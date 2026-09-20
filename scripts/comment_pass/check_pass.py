#!/usr/bin/env python3
"""Checks an applied pass against the base.

For every tracked .v file that differs from the base: the comment-stripped
code tokens are identical to the base, the sequence of comment paragraphs is
the base's sequence with the rows of the sheet substituted and nothing else,
no line over 80 bytes is new, a boxed line is exactly 80 bytes with a space
before its closing delimiter, no file of the frozen closure was written, and
the words of --words are gone from the comments.  The paragraph sequences are
aligned with difflib, so a region that does not match is printed once.

usage: check_pass.py sites.tsv --base REV|DIR [--words W...] [--root DIR]
"""
import argparse
import difflib
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C                                            # noqa: E402


def expected(base_text, rows):
    """The base paragraph texts with the sheet's substitutions applied."""
    paras = C.paragraphs(base_text)[1]
    out, problems = [], []
    used = {}
    for p in paras:
        out.append(p.text)
    for r in rows:
        hits = [k for k, t in enumerate(out) if t == r["old_text"]]
        if len(hits) != 1:
            problems.append("ROW %s: the base holds this paragraph %d times"
                            % (r["id"], len(hits)))
            continue
        k = hits[0]
        if k in used:
            problems.append("ROW %s: two rows claim one paragraph" % r["id"])
            continue
        used[k] = r
        out[k] = " ".join(r["new_text"].split())
    return out, problems


def report_regions(exp, got, rel):
    sm = difflib.SequenceMatcher(None, exp, got, autojunk=False)
    bad = 0
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            continue
        bad += 1
        print("   UNEXPECTED COMMENT CHANGE %s (%s)" % (rel, tag))
        for t in exp[i1:i2]:
            print("      base : %s" % t[:160])
        for t in got[j1:j2]:
            print("      found: %s" % t[:160])
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tsv")
    ap.add_argument("--base", required=True)
    ap.add_argument("--words", nargs="*", default=[])
    C.add_root_arg(ap)
    a = ap.parse_args()
    tree = C.Tree(a.root)
    base = C.Base(a.base, tree)
    _, rows = C.read_tsv(a.tsv)
    rows = [r for r in rows if r.get("new_text", "").strip()]
    byfile = {}
    for r in rows:
        byfile.setdefault(r["file"], []).append(r)

    ok, changed = True, 0
    for rel in tree.files():
        bt = base.read(rel)
        if bt is None:
            continue
        cur = tree.read(rel)
        if bt == cur:
            if rel in byfile:
                ok = False
                print("NOT APPLIED %s: %d rows, file untouched"
                      % (rel, len(byfile[rel])))
            continue
        changed += 1
        if C.is_frozen(rel):
            ok = False
            print("FROZEN FILE CHANGED %s" % rel)
        good = True
        if C.code_tokens(bt) != C.code_tokens(cur):
            good = False
            ta, tb = C.code_tokens(bt), C.code_tokens(cur)
            print("   CODE TOKENS DIFFER %s (%d against %d)"
                  % (rel, len(ta), len(tb)))
            for k, (x, y) in enumerate(zip(ta, tb)):
                if x != y:
                    print("      first at token %d: %r against %r" % (k, x, y))
                    break
        exp, probs = expected(bt, byfile.get(rel, []))
        for p in probs:
            good = False
            print("   %s %s" % (rel, p))
        got = [p.text for p in C.paragraphs(cur)[1]]
        if exp != got:
            good = False
            report_regions(exp, got, rel)
        old_lines = set(bt.split("\n"))
        for n, line in enumerate(cur.split("\n"), 1):
            if line in old_lines:
                continue
            if C.bw(line) > C.LINE_LIMIT:
                good = False
                print("   LONG %s:%d (%d bytes)" % (rel, n, C.bw(line)))
            if (line.startswith("(*") and line.endswith("*)")
                    and not line.startswith("(**")
                    and not set(line) <= set("(*)")
                    and C.bw(line) >= C.LINE_LIMIT - 2):
                if C.bw(line) != C.LINE_LIMIT:
                    good = False
                    print("   BOX %s:%d: %d bytes, not %d"
                          % (rel, n, C.bw(line), C.LINE_LIMIT))
                if not line.endswith(" *)"):
                    good = False
                    print("   BOX %s:%d: no space before the closing "
                          "delimiter" % (rel, n))
            if C.BARRED.search(line):
                good = False
                print("   BARRED %s:%d: %s" % (rel, n, line.strip()))
        words = C.comment_words(cur)
        low = {w.strip(".,;:()[]").lower() for w in words}
        for w in a.words:
            if w.lower() in low:
                good = False
                print("   WORD LEFT %s: %s" % (rel, w))
        ok &= good
        print("%s  %s" % ("SAME " if good else "DIFF ", rel))
    print("%d files changed" % changed)
    print("ALL OK" if ok else "PROBLEMS")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
