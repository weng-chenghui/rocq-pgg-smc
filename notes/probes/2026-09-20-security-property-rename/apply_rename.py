#!/usr/bin/env python3
"""Applies the security-property / security-evidence rename map.

Whole-identifier-token substitution (regex [A-Za-z_][A-Za-z0-9_']*, exact
token match, never a substring) over the code and the comments of every
tracked .v file outside notes/ and legacy/.  In comments the two comment-only
tokens of the lemma family are substituted as well.  Layout is untouched: the
long lines this creates are re-broken by hand afterwards.

usage: apply_rename.py [--dry]
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = subprocess.check_output(
    ["git", "-C", HERE, "rev-parse", "--show-toplevel"]).decode().strip()
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

MAP = {}
for line in open(os.path.join(HERE, "rename_map.tsv")):
    old, new = line.rstrip("\n").split("\t")[:2]
    MAP[old] = new
COMMENT_ONLY = {"_armE": "_propertyE", "armE": "propertyE"}
BOTH = dict(MAP)
BOTH.update(COMMENT_ONLY)


def spans(text):
    """[(is_comment, chunk)] splitting text at the comment delimiters."""
    out, buf, depth, i, cur = [], [], 0, 0, False
    while i < len(text):
        if text.startswith("(*", i):
            out.append((cur, "".join(buf)))
            out.append((False, "(*"))
            buf = []
            depth += 1
            i += 2
            cur = True
        elif depth and text.startswith("*)", i):
            depth -= 1
            out.append((True, "".join(buf)))
            buf = []
            out.append((False, "*)"))
            i += 2
            cur = depth > 0
        else:
            buf.append(text[i])
            i += 1
    out.append((cur, "".join(buf)))
    return [(c, s) for c, s in out if s]


def ren(text, table):
    return IDENT.sub(lambda m: table.get(m.group(0), m.group(0)), text)


def main():
    dry = "--dry" in sys.argv
    files = subprocess.check_output(
        ["git", "-C", REPO, "ls-files", "*.v"]).decode().split("\n")
    files = [f for f in files
             if f.endswith(".v") and not f.startswith("notes/")
             and not f.startswith("legacy/")]
    total = 0
    for f in files:
        path = os.path.join(REPO, f)
        text = open(path, encoding="utf-8").read()
        before = sum(1 for w in IDENT.findall(text) if w in BOTH)
        if not before:
            continue
        out = "".join(ren(s, BOTH if c else MAP) for c, s in spans(text))
        assert "".join(s for _, s in spans(text)) == text, f
        after = sum(1 for w in IDENT.findall(out) if w in BOTH)
        longs = [n for n, l in enumerate(out.splitlines(), 1)
                 if len(l.encode()) > 80]
        print(f"{f}: {before} tokens, {after} left, "
              f"{len(longs)} lines over 80 bytes")
        total += before
        if not dry:
            open(path, "w", encoding="utf-8").write(out)
    print(f"{total} tokens substituted")


if __name__ == "__main__":
    main()
