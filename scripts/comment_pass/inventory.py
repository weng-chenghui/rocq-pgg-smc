#!/usr/bin/env python3
"""Every site of a word list in the comments of the tree, one row per comment
paragraph, written to a TSV for the writers and the auditors to fill.

The inflections are given explicitly on the command line: the match is by
whole word and case-insensitive, and no stemming is done.  Files under notes/
and legacy/ and the files of the frozen closure are out of the pass; --frozen
writes the frozen hits to a second TSV, which is the owner's to read.

usage: inventory.py WORDS... [--paths P...] [-o sites.tsv] [--root DIR]
                             [--frozen]
"""
import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C                                            # noqa: E402

COLUMNS = ["id", "file", "first_line", "last_line", "kind", "declaration",
           "hits", "old_text", "case", "new_text", "fact"]


def rows_of_file(tree, rel, pat, start_id):
    text = tree.read(rel)
    blocks, paras = C.paragraphs(text, rel)
    head_last = C.header_last_line(blocks, text)
    out = []
    for p in paras:
        n = len(pat.findall(p.text))
        if not n:
            continue
        out.append({
            "id": "%04d" % (start_id + len(out)),
            "file": rel,
            "first_line": p.first + 1,
            "last_line": p.last + 1,
            "kind": p.kind,
            "declaration": C.declaration_after(text, p.last, head_last),
            "hits": n,
            "old_text": p.text,
            "case": "", "new_text": "", "fact": "",
        })
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("words", nargs="+")
    ap.add_argument("--paths", nargs="*", default=None,
                    help="restrict to these files or directory prefixes")
    ap.add_argument("-o", "--out", default="sites.tsv")
    ap.add_argument("--frozen", action="store_true",
                    help="write the hits of the frozen files to OUT.frozen")
    C.add_root_arg(ap)
    a = ap.parse_args()
    tree = C.Tree(a.root)
    pat = re.compile(r"\b(?:%s)\b" % "|".join(re.escape(w) for w in a.words),
                     re.I)
    files = tree.files()
    if a.paths:
        files = [f for f in files
                 if any(f == p or f.startswith(p.rstrip("/") + "/")
                        for p in a.paths)]
    live, frozen, k = [], [], 0
    for f in files:
        rows = rows_of_file(tree, f, pat, k)
        if C.is_frozen(f):
            frozen += rows
        else:
            live += rows
            k += len(rows)
    for i, r in enumerate(live):
        r["id"] = "%04d" % i
    C.write_tsv(a.out, COLUMNS, live)
    print("%d sites in %d files -> %s"
          % (len(live), len({r["file"] for r in live}), a.out))
    by_kind = {}
    for r in live:
        by_kind[r["kind"]] = by_kind.get(r["kind"], 0) + 1
    for k in sorted(by_kind):
        print("   %-10s %4d" % (k, by_kind[k]))
    if a.frozen:
        for i, r in enumerate(frozen):
            r["id"] = "F%03d" % i
        C.write_tsv(a.out + ".frozen", COLUMNS, frozen)
        print("%d sites in the frozen closure -> %s.frozen"
              % (len(frozen), a.out))
    elif frozen:
        print("%d sites sit in the frozen closure; --frozen lists them"
              % len(frozen))


if __name__ == "__main__":
    main()
