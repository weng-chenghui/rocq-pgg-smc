#!/usr/bin/env python3
"""Applies the PublishedRow -> Published map of rename_map.tsv to the tree.

Whole-identifier-token substitution over code and comments of every tracked .v
file outside notes/ and outside legacy/.  An identifier is
[A-Za-z_][A-Za-z0-9_']* and a token is replaced only on an exact match, never
as a substring.  Three further tokens name the renamed lemma family in prose
and are replaced inside comments only.

Layout is not touched here; the lines that grow past 80 bytes are re-broken by
hand afterwards.

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
    if not line.strip():
        continue
    old, new = line.rstrip("\n").split("\t")[:2]
    MAP[old] = new
COMMENT_ONLY = {"_rowE": "_pathE", "rowE": "pathE",
                "AnalysisPathRows": "AnalysisPaths"}


def comment_mask(text):
    """A bool per character, true inside a comment (delimiters included)."""
    mask = [False] * len(text)
    depth, i = 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            mask[i] = mask[i + 1] = True
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            mask[i] = mask[i + 1] = True
            i += 2
        else:
            mask[i] = depth > 0
            i += 1
    return mask


def apply(text):
    mask = comment_mask(text)

    def sub(m):
        w = m.group(0)
        if w in MAP:
            return MAP[w]
        if mask[m.start()] and w in COMMENT_ONLY:
            return COMMENT_ONLY[w]
        return w

    return IDENT.sub(sub, text)


def main():
    dry = "--dry" in sys.argv
    files = subprocess.check_output(
        ["git", "-C", REPO, "ls-files", "*.v"]).decode().split("\n")
    files = [f for f in files if f.endswith(".v")
             and not f.startswith("notes/") and not f.startswith("legacy/")]
    total = 0
    for f in files:
        path = os.path.join(REPO, f)
        old = open(path, encoding="utf-8").read()
        new = apply(old)
        if old == new:
            continue
        n = sum(1 for w in IDENT.findall(old) if w in MAP)
        c = sum(1 for w in IDENT.findall(old) if w in COMMENT_ONLY)
        total += n
        print(f"{n:4d} map + {c:2d} prose  {f}")
        if not dry:
            open(path, "w", encoding="utf-8").write(new)
    print(f"{total} map occurrences in {len(files)} candidate files")


if __name__ == "__main__":
    main()
