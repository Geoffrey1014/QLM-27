"""Per-pattern seed<->PoC structural fidelity check.

CodeQL (ql/features.ql) counts structural features inside the subject functions:
the seed's buggy and fixed functions (verbatim kernel code) and the PoC's `*_buggy` (and,
if present, `*_fixed`) function. This module derives the seed-specific API names from the
patch, runs the query, and turns the counts into a verdict (see judge):

  * PoC `_buggy` must keep, at least once, each pattern feature the seed's fix changes and
    the control flow the bug is written in (BUG_CF), must not already contain what the
    fix adds, and must not add control flow the seed's buggy function does not have;
  * PoC `_fixed` is not judged unless `check_fixed` is set;
  * the seed's fixed function is used only to find which features the fix changes; if it
    changes none, the check cannot see this bug and the verdict says BLIND.
"""

import re
import shutil
from dataclasses import dataclass, field
from pathlib import Path

import codeql_cli
from cfunctions import functions

QL_DIR = Path(__file__).resolve().parent / "ql"

COMMON_DIMS = ["cf.goto", "cf.return", "cf.if", "cf.loop", "cf.switch"]
# Control flow the bug itself is written in, kept for presence by judge(). "exit" is goto and
# return together: turning `goto err` into `return` keeps the same early exit.
#  * four-features / error-return: the bug sits on an error branch that leaves early, so the
#    PoC `_buggy` must keep an `if` and an exit when the seed has them;
#  * missing-check: the bug is a *missing* check, so no `if` is required in `_buggy`;
#  * delay-gfp: the bug depends on the calling context, not on a path.
BUG_CF = {
    "four-features-Lin": ["if", "exit"],
    "four-features-Lu": ["if", "exit"],
    "missing-check": [],
    "delay-gfp": [],
    "error-return-code": ["if", "exit"],
}
SHAPE_CF = ["if", "exit", "loop"]  # the PoC may drop these, never add them (judge: NO_NEW_CF)
PATTERN_DIMS = {
    "four-features-Lin": ["ff.acquire", "ff.release", "ff.leaky_exit"],
    "four-features-Lu": ["ff.acquire", "ff.release", "ff.leaky_exit"],
    "missing-check": ["mc.producer", "mc.unchecked", "mc.deref_before_check"],
    "delay-gfp": ["dg.busy_wait", "dg.sleep", "dg.gfp_atomic", "dg.gfp_kernel", "dg.atomic_ctx"],
    "error-return-code": ["er.exit_branch", "er.unset_exit"],
}
PATTERN_ALIASES = {"error-return": "error-return-code"}

# Base vocabulary for resource-lifecycle patterns, extended per seed by derive_api()
BASE_ACQUIRE = ["of_find_node_by_path", "of_find_node_opts_by_path", "of_find_matching_node",
              "of_find_compatible_node", "of_get_child_by_name", "of_get_next_child",
              "of_get_parent", "of_parse_phandle", "kzalloc", "kmalloc", "kcalloc",
              "malloc", "calloc", "realloc"]
BASE_RELEASE = ["of_node_put", "kfree", "free"]

_ACQUIRE_RE = re.compile(r"(^|_)(get|alloc|zalloc|calloc|find|parse_phandle|request|create|"
                         r"open|lookup|ioremap|map|register|acquire|hold|lock|grab)(_|$)|"
                         r"^(of|fwnode|device|bus|class)_.*(get|find)")
_RELEASE_RE = re.compile(r"(^|_)(put|free|release|destroy|unregister|close|unmap|iounmap|"
                         r"unlock|drop|disable_unprepare|remove)(_|$)|^kfree|^vfree|^kvfree")
_LOGGING_RE = re.compile(r"^(dev|pr|netdev|pci|drm|wiphy|ata|hid|bt)_(err|warn|info|dbg|notice|"
                         r"crit|alert|emerg|printk)|printk|^WARN|^BUG|_ratelimited$|^sizeof$")
_CALL_RE = re.compile(r"\b([A-Za-z_]\w*)\s*\(")
_KEYWORDS = {"if", "for", "while", "switch", "return", "sizeof", "typeof", "__typeof__"}


def _calls(text: str) -> set[str]:
    return {m.group(1) for m in _CALL_RE.finditer(text)} - _KEYWORDS


def _changed(patch: str, sign: str) -> str:
    return "\n".join(l[1:] for l in patch.splitlines()
                     if l.startswith(sign) and not l.startswith(sign * 3))


def derive_api(pattern: str, patch: str, buggy_text: str) -> list[tuple[str, str]]:
    """Seed-specific API names, derived from the fix patch and the buggy function only."""
    added, removed = _changed(patch, "+"), _changed(patch, "-")
    rows: set[tuple[str, str]] = set()
    if pattern.startswith("four-features"):
        rows |= {("acquire", n) for n in BASE_ACQUIRE}
        rows |= {("release", n) for n in BASE_RELEASE}
        rows |= {("acquire", n) for n in _calls(buggy_text) if _ACQUIRE_RE.search(n)}
        rows |= {("release", n) for n in _calls(added + removed) if _RELEASE_RE.search(n)}
        # the releases the fix is about: used by ff.leaky_exit
        rows |= {("release_patch", n) for n in _calls(added + removed) if _RELEASE_RE.search(n)}
    elif pattern == "missing-check":
        rows |= {("producer", n) for n in _calls(added + removed)
                 if not _LOGGING_RE.search(n)}
        # values the fix starts to test: `if (!x)`, `if (x < 0)`, `if (!a->b)` ...
        for cond in re.findall(r"\bif\s*\((.*)\)", added):
            for ident in re.findall(r"([A-Za-z_]\w*)(?!\s*\()", cond):
                if ident in _KEYWORDS or ident.isupper() or ident in {"NULL", "IS_ERR", "unlikely", "likely"}:
                    continue
                m = re.search(rf"\b{ident}\s*=\s*(?:\([^)]*\)\s*)?([A-Za-z_]\w*)\s*\(", buggy_text)
                if m and not _LOGGING_RE.search(m.group(1)):
                    rows.add(("producer", m.group(1)))
                elif re.search(rf"\b{ident}\b", buggy_text):
                    rows.add(("producer_var", ident))
    return sorted(rows)


@dataclass
class Verdict:
    ok: bool
    blind: bool
    rows: list[str]
    counts: dict[str, dict[str, int]] = field(default_factory=dict)
    error: bool = False  # the check itself could not run (not the PoC's fault)

    def feedback(self) -> str:
        return "\n".join(r for r in self.rows if not r.startswith("OK"))


def _poc_fn(poc_text: str, suffix: str, seed_fns: list[str]) -> str | None:
    """The PoC function mirroring the seed: `<seed fn><suffix>` if present, else the only
    function ending in `suffix`."""
    names = [f.name for f in functions(poc_text) if f.name.endswith(suffix)]
    preferred = [n for n in names if n[: -len(suffix)] in seed_fns]
    if len(preferred) == 1:
        return preferred[0]
    return names[0] if len(names) == 1 else None


def run(pattern: str, patch: str, seed_buggy_c: Path, seed_fixed_c: Path,
        buggy_fns: list[str], fixed_fns: list[str], poc_c: Path, work: Path,
        require_fixed: bool = False, check_fixed: bool = False) -> Verdict:
    """A PoC needs one `*_buggy` function; a `*_fixed` function is optional unless
    `require_fixed`. The verdict only judges `_buggy` unless `check_fixed` (see judge)."""
    pattern = PATTERN_ALIASES.get(pattern, pattern)
    poc_text = poc_c.read_text()
    pb, pf = _poc_fn(poc_text, "_buggy", buggy_fns), _poc_fn(poc_text, "_fixed", fixed_fns)
    if pb is None:
        return Verdict(False, False, ["ERROR(PoC must define exactly one `<fn>_buggy` function)"])
    if pf is None and require_fixed:
        return Verdict(False, False, ["ERROR(PoC must define exactly one `<fn>_fixed` function)"])

    if work.exists():
        shutil.rmtree(work)
    src = work / "src"
    src.mkdir(parents=True)
    for name, path in (("seed_buggy.c", seed_buggy_c), ("seed_fixed.c", seed_fixed_c), ("poc.c", poc_c)):
        shutil.copy(path, src / name)
    ok, log = codeql_cli.create_db(src, work / "db", [
        f"gcc -std=gnu11 -O0 -w -c {n} -o {n[:-2]}.o" for n in ("seed_buggy.c", "seed_fixed.c", "poc.c")])
    if not ok:
        return Verdict(False, False, ["ERROR(build failed: " + log.strip().splitlines()[-1] + ")"], error=True)

    subjects = [("seed_buggy.c", f, "seed_buggy") for f in buggy_fns] + \
               [("seed_fixed.c", f, "seed_fixed") for f in fixed_fns] + \
               [("poc.c", pb, "poc_buggy")] + ([("poc.c", pf, "poc_fixed")] if pf else [])
    buggy_text = (seed_buggy_c.read_text())
    ext = {"subject": codeql_cli.write_external(work / "subject.csv", subjects),
           "api": codeql_cli.write_external(work / "api.csv",
                                            derive_api(pattern, patch, buggy_text) or [("none", "")])}
    ok, tuples, err = codeql_cli.run_query(QL_DIR / "features.ql", work / "db", ext, out_dir=work)
    if not ok:
        return Verdict(False, False, ["ERROR(feature query failed: " + err.strip()[-500:] + ")"], error=True)

    counts: dict[str, dict[str, int]] = {}
    for role, _file, _fn, dim, n in tuples:
        counts.setdefault(role, {}).setdefault(dim, 0)
        counts[role][dim] += int(n)  # several seed functions (e.g. mc-2) add up
    return judge(pattern, counts, check_fixed)


def _sign(x: int) -> int:
    return (x > 0) - (x < 0)


def _cf(c: dict[str, int], kind: str) -> int:
    return c.get("cf.goto", 0) + c.get("cf.return", 0) if kind == "exit" else c.get("cf." + kind, 0)


def judge(pattern: str, counts: dict[str, dict[str, int]], check_fixed: bool = False) -> Verdict:
    """Buggy-side check: PoC `_buggy` must be a simplification of the seed's buggy
    function that keeps the bug's ingredients. It may drop code, not copy the seed's size.
      * KEEP_BUG: each pattern feature the fix changes (key APIs, leaky exits, unchecked
        values, ...) that the seed's buggy function has must occur at least once;
      * NO_FIX_IN_BUGGY: a pattern feature the fix adds (e.g. the release, the sleeping
        call) must not occur more often than in the seed's buggy function;
      * KEEP_CF: the pattern's bug control flow (BUG_CF) must occur at least once when the
        seed's buggy function has it;
      * NO_NEW_CF: no more if / exits (goto + return) / loops than the seed's buggy function.
    Pattern features the fix leaves alone, switches, and control flow outside BUG_CF are
    incidental to the bug and are not required.
    With `check_fixed`, PoC `_buggy` -> `_fixed` must also move the same way (up / down)
    as the seed on every pattern dimension the fix changes."""
    pattern = PATTERN_ALIASES.get(pattern, pattern)
    dims = PATTERN_DIMS[pattern]
    sb, sf = counts.get("seed_buggy", {}), counts.get("seed_fixed", {})
    pb, pf = counts.get("poc_buggy", {}), counts.get("poc_fixed", {})
    changed = [d for d in dims if sb.get(d, 0) != sf.get(d, 0)]
    rows = []
    for d in changed:
        if sb.get(d, 0) > 0 and pb.get(d, 0) == 0:
            rows.append(f"MISMATCH(buggy {d}: seed has {sb[d]}, poc has none)")
        if sf.get(d, 0) > sb.get(d, 0) and pb.get(d, 0) > sb.get(d, 0):
            rows.append(f"MISMATCH(buggy {d}: the fix adds it (seed {sb.get(d, 0)}->{sf[d]}), "
                        f"poc _buggy already has {pb[d]})")
    for k in BUG_CF[pattern]:
        if _cf(sb, k) > 0 and _cf(pb, k) == 0:
            rows.append(f"MISMATCH(buggy cf.{k}: seed has {_cf(sb, k)}, poc has none)")
    for k in SHAPE_CF:
        if _cf(pb, k) > _cf(sb, k):
            rows.append(f"MISMATCH(buggy cf.{k}: poc has {_cf(pb, k)}, more than the seed's "
                        f"{_cf(sb, k)}; simplify, do not add control flow)")
    if check_fixed and "poc_fixed" in counts:
        for d in changed:
            want, got = _sign(sf.get(d, 0) - sb.get(d, 0)), _sign(pf.get(d, 0) - pb.get(d, 0))
            if want != got:
                word = {1: "increase", -1: "decrease", 0: "stay equal"}
                rows.append(f"MISMATCH(fixed {d}: the fix should make it {word[want]} "
                            f"(seed {sb.get(d, 0)}->{sf.get(d, 0)}), poc {pb.get(d, 0)}->{pf.get(d, 0)})")
    elif check_fixed:
        rows.append("NOFIXED(PoC has no `_fixed` function; fixed side not checked)")
    blind = all(sb.get(d, 0) == sf.get(d, 0) for d in dims)
    if not rows:
        rows.append("OK(" + " ".join(f"{d}={sb.get(d, 0)}/{sf.get(d, 0)}" for d in COMMON_DIMS + dims) + ")")
    if blind:
        rows.append("BLIND(seed buggy and fixed agree on every " + pattern + " dimension)")
    return Verdict(ok=not any(r.startswith("MISMATCH") for r in rows), blind=blind, rows=rows, counts=counts)
