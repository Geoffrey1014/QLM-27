"""Thin wrappers around the CodeQL CLI."""

import csv
import io
import json
import subprocess
from pathlib import Path

from . import config


def _run(*args: str, cwd: Path | None = None, timeout: int = 1800) -> subprocess.CompletedProcess:
    return subprocess.run([config.CODEQL, *args], cwd=cwd, capture_output=True,
                          text=True, timeout=timeout)


def ensure_pack(pack_dir: Path, name: str) -> None:
    """Make `pack_dir` a query pack depending on codeql/cpp-all (needed to compile .ql there)."""
    yml = pack_dir / "qlpack.yml"
    if not yml.exists():
        pack_dir.mkdir(parents=True, exist_ok=True)
        yml.write_text(f'name: {name}\nversion: 0.0.1\ndependencies:\n  codeql/cpp-all: "*"\n')
    if not (pack_dir / "codeql-pack.lock.yml").exists():
        r = _run("pack", "install", cwd=pack_dir)
        if r.returncode:
            raise RuntimeError(f"codeql pack install failed in {pack_dir}:\n{r.stderr[-2000:]}")


def create_db(src_dir: Path, db: Path, build_cmds: list[str]) -> tuple[bool, str]:
    """Build a C database from `build_cmds`, run in `src_dir` through a build script."""
    src_dir, db = src_dir.resolve(), db.resolve()  # codeql runs with cwd=src_dir
    script = src_dir / "build.sh"
    script.write_text("#!/bin/bash\nset -e\n" + "\n".join(build_cmds) + "\n")
    script.chmod(0o755)
    r = _run("database", "create", str(db), "--language=cpp", f"--command={script}",
             f"--source-root={src_dir}", "--overwrite", cwd=src_dir)
    return r.returncode == 0, r.stdout[-3000:] + r.stderr[-3000:]


def compile_query(ql: Path) -> tuple[bool, str]:
    r = _run("query", "compile", str(ql))
    return r.returncode == 0, r.stderr


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
