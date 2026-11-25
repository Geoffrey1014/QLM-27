"""Attribute query results on the PoC database to PoC functions and check expectations."""

import re
from dataclasses import dataclass
from pathlib import Path

from . import codeql, config


def classify(fn: str) -> str:
    if re.search(r"_fp\d*$", fn):
        return "fp"
    if re.search(r"_(fixed|tn\d*)$", fn):
        return "fixed"
    if re.search(r"_(buggy|tp\d*)$", fn):
        return "buggy"
    return "other"


@dataclass
class Spans:
    rows: list[tuple[str, str, int, int]]  # (function, file basename, start, end)

    def function_at(self, uri: str, line: int) -> str | None:
        base = Path(uri.replace("file://", "")).name
        hits = [(e - s, f) for f, fb, s, e in self.rows if fb == base and s <= line <= e]
        return min(hits)[1] if hits else None


def spans(db: Path, work: Path) -> Spans:
    ok, tuples, err = codeql.run_query(config.QL_DIR / "oracle" / "functions.ql", db, out_dir=work)
    if not ok:
        raise RuntimeError(f"function-span query failed: {err[-1000:]}")
    return Spans([(t[0], t[1], int(t[2]), int(t[3])) for t in tuples])


@dataclass
class Hits:
    n_rows: int
    functions: dict[str, int]  # PoC function -> number of results located in it

    @property
    def classes(self) -> set[str]:
        return {classify(f) for f in self.functions}

    def table(self) -> str:
        if not self.functions:
            return f"{self.n_rows} rows, none located in a PoC function"
        return f"{self.n_rows} rows; " + ", ".join(f"{f}: {n}" for f, n in sorted(self.functions.items()))


def locate(tuples: list[list], sp: Spans) -> Hits:
    funcs: dict[str, int] = {}
    for t in tuples:
        cell = t[0] if t else None
        url = cell.get("url") if isinstance(cell, dict) else None
        if not url or "startLine" not in url:
            continue
        f = sp.function_at(url["uri"], url["startLine"])
        if f:
            funcs[f] = funcs.get(f, 0) + 1
    return Hits(len(tuples), funcs)


def check_expect(hits: Hits, expect: dict) -> str | None:
    """None when `expect` holds, else a one-line reason."""
    rows = expect.get("rows", "some")
    if rows == "none" and hits.n_rows:
        return f"expected no rows, got {hits.table()}"
    if rows == "some" and not hits.n_rows:
        return "expected some rows, got none"
    missing = [c for c in expect.get("must_hit", []) if c not in hits.classes]
    if missing:
        return f"expected results in {missing} functions, got {hits.table()}"
    only = expect.get("only_in") or []
    stray = sorted(hits.classes - set(only)) if only else []
    if stray:
        return f"results only allowed in {only}, also got {stray}: {hits.table()}"
    return None


def final_oracle(hits: Hits) -> tuple[bool, dict, str]:
    """Final-query acceptance: fires in a buggy function, silent in fixed and fp ones."""
    c = hits.classes
    flags = {"buggy_fires": "buggy" in c, "fixed_fires": "fixed" in c, "fp_fires": "fp" in c}
    ok = flags["buggy_fires"] and not flags["fixed_fires"] and not flags["fp_fires"]
    return ok, flags, f"expected: buggy fires, fixed and fp silent; got {hits.table()}"
