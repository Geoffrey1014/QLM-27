"""Thin wrappers around the CodeQL CLI (binary: $QLM_CODEQL, default `codeql` on PATH)."""

import csv
import io
import json
import os
import subprocess
from pathlib import Path

CODEQL = os.environ.get("QLM_CODEQL", "codeql")


def _run(*args: str, cwd: Path | None = None, timeout: int = 1800) -> subprocess.CompletedProcess:
    return subprocess.run([CODEQL, *args], cwd=cwd, capture_output=True,
                          text=True, timeout=timeout)


def create_db(src_dir: Path, db: Path, build_cmds: list[str]) -> tuple[bool, str]:
    """Build a C database from `build_cmds`, run in `src_dir` through a build script."""
    src_dir, db = src_dir.resolve(), db.resolve()  # codeql runs with cwd=src_dir
    script = src_dir / "build.sh"
    script.write_text("#!/bin/bash\nset -e\n" + "\n".join(build_cmds) + "\n")
    script.chmod(0o755)
    r = _run("database", "create", str(db), "--language=cpp", f"--command={script}",
             f"--source-root={src_dir}", "--overwrite", cwd=src_dir)
    return r.returncode == 0, r.stdout[-3000:] + r.stderr[-3000:]


def run_query(ql: Path, db: Path, externals: dict[str, Path] | None = None,
              out_dir: Path | None = None) -> tuple[bool, list[list], str]:
    """Evaluate `ql` on `db`; return (ok, tuples, stderr). Entity columns decode to dicts with
    'label' and 'url' (uri/startLine/...), plain columns to strings or numbers. Results go to
    `out_dir` (default: next to `ql`); give each concurrent run its own `out_dir`."""
    bqrs = (out_dir / ql.name if out_dir else ql).with_suffix(".bqrs")
    args = ["query", "run", str(ql), f"--database={db}", f"--output={bqrs}"]
    args += [f"--external={k}={v}" for k, v in (externals or {}).items()]
    r = _run(*args)
    if r.returncode:
        return False, [], r.stderr
    d = _run("bqrs", "decode", str(bqrs), "--format=json", "--entities=url,string")
    if d.returncode:
        return False, [], d.stderr
    data = json.loads(d.stdout)
    rs = data.get("#select") or next(iter(data.values()), {"tuples": []})
    return True, rs["tuples"], r.stderr


def write_external(path: Path, rows: list[tuple]) -> Path:
    buf = io.StringIO()
    csv.writer(buf).writerows(rows)
    path.write_text(buf.getvalue())
    return path
