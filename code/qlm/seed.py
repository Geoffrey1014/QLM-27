"""Seed slices: the bug-touched function(s) copied verbatim from the kernel (buggy and fixed
versions), made compilable by an LLM-written preamble of declarations only.

The function text is never edited. The preamble is rejected if it defines any function, so
nothing outside the subject functions can contribute to fidelity-check counts."""

import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

from . import config
from .kernel import Commit, FuncSpan, bug_functions, functions
from .llm import LLM, strip_fences

SEED_STUB_SYSTEM = """\
You make extracted Linux kernel functions compile as standalone C translation units.
You write ONLY a preamble of declarations that goes in front of the given functions:
struct/union/enum definitions, typedefs, #define macros, extern function prototypes and
extern variable declarations. Never write a function definition (no function bodies).
No kernel headers; you may include <stddef.h>, <stdint.h>, <stdbool.h>.
Prefer extern prototypes for kernel APIs (kfree, mdelay, of_node_put, ...). Define macros
only where a prototype cannot work (attributes such as __init, iterator macros such as
list_for_each_entry, constants such as GFP_KERNEL or EINVAL).
Output ONLY the C preamble. No markdown fences, no commentary."""

SEED_STUB_USER = """\
File: {c_file}
The preamble must make BOTH translation units below compile with
`gcc -std=gnu11 -O0 -w -c`:
  unit 1 = preamble + the BUGGY function(s)
  unit 2 = preamble + the FIXED function(s)

--- BUGGY ---
{buggy}
--- FIXED ---
{fixed}
"""

SEED_STUB_REPAIR = """\
The preamble below does not work yet.

--- PREAMBLE ---
{preamble}
--- PROBLEM ---
{problem}

Emit the corrected complete preamble. Same rules: declarations only, no function bodies."""


@dataclass
class SeedSlices:
    buggy_c: Path
    fixed_c: Path
    buggy_fns: list[str]
    fixed_fns: list[str]
    stub_iters: int


def _gcc(path: Path) -> str:
    r = subprocess.run(["gcc", "-std=gnu11", "-O0", "-w", "-c", str(path), "-o", "/dev/null"],
                       capture_output=True, text=True)
    return "" if r.returncode == 0 else r.stderr


VERBATIM_MARK = "/* ---- verbatim kernel code ---- */\n"


def config_defines(text: str) -> str:
    """Enable every CONFIG_* option the code tests with #if/#ifdef, approximating the
    allmodconfig build the kernel databases use; otherwise guarded code would vanish."""
    opts = sorted(set(re.findall(r"(?m)^\s*#\s*(?:if|ifdef|elif)\b.*?\b(CONFIG_\w+)", text)))
    return "".join(f"#undef {o}\n#define {o} 1\n" for o in opts) + canonical_macros(text)


# Kernel iterator macros whose stubbed form decides whether the verbatim loop body is
# reachable at all; an LLM stub such as `for (child = 0; child; child = 0)` makes it dead.
_OF_ITERATORS = {
    "for_each_child_of_node": ("parent, child", "of_get_next_child",
                               "for (child = of_get_next_child(parent, 0); child != 0; "
                               "child = of_get_next_child(parent, child))"),
    "for_each_available_child_of_node": ("parent, child", "of_get_next_available_child",
                                         "for (child = of_get_next_available_child(parent, 0); child != 0; "
                                         "child = of_get_next_available_child(parent, child))"),
    "for_each_compatible_node": ("dn, type, compatible", "of_find_compatible_node",
                                 "for (dn = of_find_compatible_node(0, type, compatible); dn != 0; "
                                 "dn = of_find_compatible_node(dn, type, compatible))"),
    "for_each_node_by_name": ("dn, name", "of_find_node_by_name",
                              "for (dn = of_find_node_by_name(0, name); dn != 0; "
                              "dn = of_find_node_by_name(dn, name))"),
    "for_each_matching_node": ("dn, matches", "of_find_matching_node",
                               "for (dn = of_find_matching_node(0, matches); dn != 0; "
                               "dn = of_find_matching_node(dn, matches))"),
}


def canonical_macros(text: str) -> str:
    """Definitions that override the preamble's stubs for macros that shape control flow:
    IS_ENABLED()-style config tests are taken as enabled (like CONFIG_* above), and OF
    iterators get their real acquire/release structure."""
    out = []
    for m in ("IS_ENABLED", "IS_BUILTIN", "IS_REACHABLE", "IS_MODULE"):
        if re.search(rf"\b{m}\s*\(", text):
            out.append(f"#undef {m}\n#define {m}(x) 1\n")
    for name, (params, api, body) in _OF_ITERATORS.items():
        if re.search(rf"\b{name}\s*\(", text):
            out.append(f"struct device_node;\nstruct device_node *{api}();\n"
                       f"#undef {name}\n#define {name}({params}) {body}\n")
    return "".join(out)


def _assemble(preamble: str, spans: list[FuncSpan], commit: Commit, side: str) -> str:
    head = f"/* QLM seed slice: {commit.c_file} @ {commit.sha}{'^' if side == 'buggy' else ''} ({side}).\n" \
           f" * Function text below the preamble is verbatim from the kernel tree. */\n"
    code = "\n".join(s.text for s in spans)
    return head + preamble.rstrip() + "\n" + config_defines(code) + "\n" + VERBATIM_MARK + code


def build_seed_slices(commit: Commit, out_dir: Path, llm: LLM) -> SeedSlices:
    buggy, fixed = bug_functions(commit)
    if not buggy or not fixed:
        raise RuntimeError(f"could not locate the bug-touched function in {commit.c_file}")
    out_dir.mkdir(parents=True, exist_ok=True)
    bpath, fpath = out_dir / "seed_buggy.c", out_dir / "seed_fixed.c"
    preamble = strip_fences(llm("seed-stub", SEED_STUB_SYSTEM, SEED_STUB_USER.format(
        c_file=commit.c_file,
        buggy="\n".join(s.text for s in buggy), fixed="\n".join(s.text for s in fixed))))
    for it in range(1, config.SEED_STUB_MAX_ITERS + 1):
        defined = [f.name for f in functions(preamble)]
        if defined:
            problem = f"The preamble defines functions ({', '.join(defined)}); only declarations are allowed."
        else:
            bpath.write_text(_assemble(preamble, buggy, commit, "buggy"))
            fpath.write_text(_assemble(preamble, fixed, commit, "fixed"))
            errs = [(n, e) for n, e in (("BUGGY", _gcc(bpath)), ("FIXED", _gcc(fpath))) if e]
            if not errs:
                return SeedSlices(bpath, fpath, [s.name for s in buggy], [s.name for s in fixed], it)
            problem = "\n".join(f"gcc errors in unit {n}:\n" + "\n".join(e.splitlines()[:60])
                                for n, e in errs)
        if it == config.SEED_STUB_MAX_ITERS:
            break
        preamble = strip_fences(llm("seed-stub-repair", SEED_STUB_SYSTEM,
                                    SEED_STUB_REPAIR.format(preamble=preamble, problem=problem)))
    raise RuntimeError(f"seed slice does not compile after {config.SEED_STUB_MAX_ITERS} rounds:\n{problem}")
