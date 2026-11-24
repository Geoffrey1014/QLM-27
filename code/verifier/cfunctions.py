"""Top-level C function definitions, found by brace matching (no compiler needed)."""

import re
from dataclasses import dataclass


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
