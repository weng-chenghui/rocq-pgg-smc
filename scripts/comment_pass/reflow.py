#!/usr/bin/env python3
"""Deterministic layout of the comment paragraphs of the tree.

A boxed line is (* plus 76 bytes plus *), so exactly 80 bytes, with at least
one space before the closing delimiter.  An index entry keeps the == column
and the continuation column of its own header block, and a name too long to
sit before the == column stands alone on its line.  A banner keeps its two
star lines.  A table keeps its bars where they are.  A docstring continues at
four spaces and a plain comment at three.  No word is split, so a hyphenated
word stays whole, and a last line holding one short word is rebalanced
against the line above it.  Code is never touched.

Only a paragraph whose words differ from the base is laid out again, unless
--all is given.  The pass is idempotent and leaves the comment word stream
of the file identical.

usage: reflow.py FILE... [--all] [--base REV|DIR] [--root DIR] [--dry-run]
"""
import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C                                            # noqa: E402


def reflow_text(text, base_text=None, everything=False):
    """(new text, number of paragraphs laid out again)."""
    blocks, paras = C.paragraphs(text)
    known = set()
    if base_text is not None and not everything:
        for p in C.paragraphs(base_text)[1]:
            known.add((p.kind, tuple(p.words)))
    wanted = {}
    for p in paras:
        if p.kind == "table":
            continue
        if everything or base_text is None:
            wanted[id(p)] = None
        elif (p.kind, tuple(p.words)) not in known:
            wanted[id(p)] = None
    if not wanted:
        return text, 0
    return C.relayout(text, blocks, wanted), len(wanted)


def reflow_file(tree, rel, base_text=None, everything=False, dry=False):
    text = tree.read(rel)
    new, n = reflow_text(text, base_text, everything)
    if new != text:
        if not dry:
            tree.write(rel, new)
        return True, n
    return False, n


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+")
    ap.add_argument("--all", action="store_true",
                    help="lay out every paragraph, not only the changed ones")
    ap.add_argument("--base", default=None)
    ap.add_argument("--dry-run", action="store_true")
    C.add_root_arg(ap)
    a = ap.parse_args()
    tree = C.Tree(a.root)
    base = C.Base(a.base, tree) if a.base else None
    for f in a.files:
        rel = os.path.relpath(os.path.abspath(f), tree.root) \
            if os.path.isabs(f) or os.path.exists(f) else f
        if C.is_frozen(rel):
            C.die("refused: %s is in the frozen closure" % rel)
        bt = base.read(rel) if base else None
        changed, n = reflow_file(tree, rel, bt, a.all, a.dry_run)
        print("%s %s (%d paragraphs)"
              % ("CHANGED" if changed else "same   ", rel, n))


if __name__ == "__main__":
    main()
