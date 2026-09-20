#!/usr/bin/env python3
"""Applies an audited sheet: each row whose new_text is filled replaces the
words of one comment paragraph, which is then laid out again.

A paragraph is found by its file and by its old_text, never by its line
number, because the lines move as the earlier rows of the same file are
applied.  The rows of one file are applied from the bottom up.  A row whose
old text does not match exactly once stops the whole run: nothing is written.

usage: apply_tsv.py sites.tsv [--base REV|DIR] [--root DIR] [--dry-run]
"""
import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C                                            # noqa: E402


def matches(paras, old):
    return [p for p in paras if p.text == old]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tsv")
    ap.add_argument("--base", default=None,
                    help="refuse when a row's old text is not the base text")
    ap.add_argument("--dry-run", action="store_true")
    C.add_root_arg(ap)
    a = ap.parse_args()
    tree = C.Tree(a.root)
    base = C.Base(a.base, tree) if a.base else None
    _, rows = C.read_tsv(a.tsv)
    rows = [r for r in rows if r.get("new_text", "").strip()]
    if not rows:
        C.die("no row carries a new text")

    byfile = {}
    for r in rows:
        byfile.setdefault(r["file"], []).append(r)

    problems, plan = [], {}
    for rel, rs in sorted(byfile.items()):
        if C.is_frozen(rel):
            problems.append("FROZEN %s: the pass never writes this file" % rel)
            continue
        if not os.path.exists(os.path.join(tree.root, rel)):
            problems.append("MISSING %s" % rel)
            continue
        text = tree.read(rel)
        blocks, paras = C.paragraphs(text, rel)
        seen = {}
        for r in rs:
            hit = matches(paras, r["old_text"])
            if len(hit) != 1:
                problems.append("ROW %s %s: old text matches %d paragraphs"
                                % (r["id"], rel, len(hit)))
                continue
            p = hit[0]
            if id(p) in seen:
                problems.append("ROW %s %s: two rows claim the same paragraph"
                                % (r["id"], rel))
                continue
            if p.kind == "table":
                problems.append("ROW %s %s: a table is laid out by hand"
                                % (r["id"], rel))
                continue
            if base is not None:
                bt = base.read(rel)
                if bt is None or len(matches(
                        C.paragraphs(bt)[1], r["old_text"])) != 1:
                    problems.append(
                        "ROW %s %s: the base does not hold this paragraph "
                        "exactly once" % (r["id"], rel))
                    continue
            seen[id(p)] = r
        plan[rel] = (text, blocks, seen)

    if problems:
        for p in problems:
            print(p)
        C.die("PROBLEMS: nothing written")

    total = 0
    for rel, (text, blocks, seen) in sorted(plan.items()):
        wanted = {i: seen[i]["new_text"].split() for i in seen}
        new = C.relayout(text, blocks, wanted)
        total += len(seen)
        print("%-64s %2d paragraphs" % (rel, len(seen)))
        if not a.dry_run:
            tree.write(rel, new)
    print("%d paragraphs applied in %d files%s"
          % (total, len(plan), " (dry run)" if a.dry_run else ""))


if __name__ == "__main__":
    main()
