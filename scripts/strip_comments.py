#!/usr/bin/env python3
"""Print a .v file's code with comments removed (nesting-aware).

Used to verify a comment-only edit: stripped(old) must equal
stripped(new). Handles Rocq's nested (* *) and string literals
(a quote inside a comment does NOT open a string; a comment opener
inside a string is text).
"""
import sys


def strip(src: str) -> str:
    out = []
    i, n = 0, len(src)
    depth = 0
    in_str = False
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if depth == 0 and not in_str and c == "(" and nxt == "*":
            depth = 1
            i += 2
            continue
        if depth > 0:
            if c == "(" and nxt == "*":
                depth += 1
                i += 2
                continue
            if c == "*" and nxt == ")":
                depth -= 1
                i += 2
                continue
            i += 1
            continue
        if c == '"':
            in_str = not in_str
        out.append(c)
        i += 1
    # normalize whitespace runs so reflowed spacing around removed
    # comments does not count as a code change
    return " ".join("".join(out).split())


if __name__ == "__main__":
    with open(sys.argv[1], encoding="utf-8") as fh:
        print(strip(fh.read()))
