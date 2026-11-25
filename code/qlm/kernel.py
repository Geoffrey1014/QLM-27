"""Kernel git access and deterministic extraction of the bug-touched function(s)."""

import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

from .config import LINUX


def git(*args: str, repo: Path = LINUX) -> str:
    return subprocess.run(["git", "-C", str(repo), *args],
                          capture_output=True, text=True, check=True).stdout


@dataclass
class Commit:
    sha: str
    c_file: str
    subject: str
    message: str
    patch: str
    buggy_src: str
    fixed_src: str


def load_commit(sha: str, c_file: str) -> Commit:
    return Commit(
        sha=sha,
        c_file=c_file,
        subject=git("show", "-s", "--format=%s", sha).strip(),
        message=git("show", "-s", "--format=%B", sha),
        patch=git("show", sha, "--", c_file),
        buggy_src=git("show", f"{sha}^:{c_file}"),
        fixed_src=git("show", f"{sha}:{c_file}"),
    )


_HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


def changed_lines(patch: str, side: str = "old") -> list[int]:
    """1-based line numbers touched by the patch on the old (buggy) or new (fixed) side.
    An insertion (deletion) is attributed on the side lacking it to the line just before
    the insertion (deletion) point."""
    out, old, new = [], 0, 0
    for line in patch.splitlines():
        m = _HUNK.match(line)
        if m:
            old, new = int(m.group(1)), int(m.group(3))
            continue
        if not old or line.startswith(("---", "+++")):
            continue
        if line.startswith("-"):
            out.append(old if side == "old" else max(new - 1, 1))
            old += 1
        elif line.startswith("+"):
            out.append(max(old - 1, 1) if side == "old" else new)
            new += 1
        elif line.startswith(" ") or line == "":
            old += 1
            new += 1
    return sorted(set(out))


def _blank_comments_and_strings(src: str) -> str:
    """Replace comments, string and char literals with spaces, keeping offsets and newlines."""
    out = list(src)
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if src.startswith("/*", i):
            j = src.find("*/", i + 2)
            j = n if j < 0 else j + 2
        elif src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
        elif c in "\"'":
            j = i + 1
            while j < n and src[j] != c:
                j += 2 if src[j] == "\\" else 1
            j = min(j + 1, n)
        else:
            i += 1
            continue
        for k in range(i, j):
            if out[k] != "\n":
                out[k] = " "
        i = j
    return "".join(out)


@dataclass
class FuncSpan:
    name: str
    start_line: int  # first line of the definition header
    end_line: int    # line of the closing brace
    text: str


_IDENT_BEFORE_PAREN = re.compile(r"([A-Za-z_]\w*)\s*$")


def functions(src: str) -> list[FuncSpan]:
    """Top-level C function definitions, found by brace matching on comment/string-free text."""
    clean = _blank_comments_and_strings(src)
    # preprocessor lines can hold unbalanced braces/parens; ignore them for scanning
    clean = re.sub(r"(?m)^[ \t]*#(?:[^\n]*\\\n)*[^\n]*", lambda m: re.sub(r"[^\n]", " ", m.group(0)), clean)
    spans, depth, stmt_start = [], 0, 0
    i = 0
    while i < len(clean):
        ch = clean[i]
        if ch == "{":
            if depth == 0:
                header = clean[stmt_start:i].rstrip()
                open_at = i
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                name = _function_name(header)
                if name:
                    hdr_off = stmt_start + (len(clean[stmt_start:open_at]) - len(clean[stmt_start:open_at].lstrip()))
                    start = src.count("\n", 0, hdr_off) + 1
                    end = src.count("\n", 0, i) + 1
                    line_start = src.rfind("\n", 0, hdr_off) + 1
                    spans.append(FuncSpan(name, start, end, src[line_start:i + 1] + "\n"))
                stmt_start = i + 1
        elif ch == ";" and depth == 0:
            stmt_start = i + 1
        i += 1
    return spans


def _function_name(header: str) -> str | None:
    h = header.strip()
    if not h.endswith(")") or "=" in h.split("(")[0]:
        return None
    depth = 0
    for k in range(len(h) - 1, -1, -1):
        if h[k] == ")":
            depth += 1
        elif h[k] == "(":
            depth -= 1
            if depth == 0:
                m = _IDENT_BEFORE_PAREN.search(h[:k])
                if not m or m.group(1) in {"if", "while", "for", "switch", "sizeof"}:
                    return None
                return m.group(1)
    return None


def touched_functions(src: str, lines: list[int]) -> list[FuncSpan]:
    spans = functions(src)
    hit = [s for s in spans if any(s.start_line <= ln <= s.end_line for ln in lines)]
    return hit


def bug_functions(commit: Commit) -> tuple[list[FuncSpan], list[FuncSpan]]:
    """(buggy-side spans, fixed-side spans) of the functions the fix touches."""
    buggy = touched_functions(commit.buggy_src, changed_lines(commit.patch, "old"))
    fixed = touched_functions(commit.fixed_src, changed_lines(commit.patch, "new"))
    return buggy, fixed
