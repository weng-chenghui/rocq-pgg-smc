#!/usr/bin/env python3
"""An identifier rename, checked before it is made and after.

The map is a TSV of old and new name, one pair per line; further columns are
ignored, so the occurrence counts a build step writes may stay in the file.

  rename.py build MAP.tsv [--modules LIB.MOD...] [--probe FILE.v]
      The map is injective, every old name occurs in the tree, and no new
      name is already an identifier of a tracked .v outside notes/.  With
      --probe a file of Locate commands over the new names is written, to be
      compiled once against the given modules before the rename is applied.

  rename.py apply MAP.tsv [--comment-only OLD=NEW...] [--move OLD NEW]
      Whole-identifier-token substitution over code and comments.  A token is
      replaced on an exact match, never as a substring.  A comment-only pair
      is substituted inside comments alone, for the prose name of a renamed
      family.  The paragraphs the substitution touched are laid out again,
      and the code lines that grew past 80 bytes are reported: a code line is
      broken by a human.

  rename.py check MAP.tsv --base REV [--move OLD NEW]
      The base text with the map applied must equal the working copy as a
      stream of code tokens and as a sequence of comment paragraphs.
"""
import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C                                            # noqa: E402
import reflow as R                                            # noqa: E402


def read_map(path):
    m = {}
    for line in open(path, encoding="utf-8"):
        if not line.strip() or line.startswith("#"):
            continue
        cells = line.rstrip("\n").split("\t")
        if len(cells) < 2 or cells[0] == "old":
            continue
        m[cells[0]] = cells[1]
    return m


def counts(tree):
    n = {}
    for f in tree.files():
        for w in C.IDENT.findall(tree.read(f)):
            n[w] = n.get(w, 0) + 1
    return n


def substitute(text, table, comment_only):
    mask = C.comment_mask(text)

    def sub(m):
        w = m.group(0)
        if w in table:
            return table[w]
        if mask[m.start()] and w in comment_only:
            return comment_only[w]
        return w

    return C.IDENT.sub(sub, text)


def cmd_build(a, tree):
    m = read_map(a.map)
    n = counts(tree)
    problems = []
    inv = {}
    for o, w in m.items():
        inv.setdefault(w, []).append(o)
    for w, os_ in sorted(inv.items()):
        if len(os_) > 1:
            problems.append("NOT INJECTIVE %s <- %s" % (w, os_))
        if w in n and w not in m:
            problems.append("NEW NAME EXISTS %s (%d uses)" % (w, n[w]))
        if w in m:
            problems.append("NEW NAME IS AN OLD NAME %s" % w)
    for o in sorted(m):
        if o not in n:
            problems.append("OLD NAME ABSENT %s" % o)
    print("%d names, %d occurrences"
          % (len(m), sum(n.get(o, 0) for o in m)))
    for p in problems:
        print(p)
    if a.probe:
        lines = ["(* Locate probe of the new names of %s.  Generated. *)"
                 % os.path.basename(a.map)]
        for mod in a.modules or []:
            lib, _, name = mod.rpartition(".")
            lines.append("From %s Require Import %s." % (lib or "pgg_smc",
                                                         name))
        lines.append("")
        for o in sorted(m):
            lines.append("Locate %s." % m[o])
        open(a.probe, "w", encoding="utf-8").write("\n".join(lines) + "\n")
        print("probe -> %s (%d Locate commands)" % (a.probe, len(m)))
    return 1 if problems else 0


def cmd_apply(a, tree):
    m = read_map(a.map)
    co = dict(p.split("=", 1) for p in (a.comment_only or []))
    total, longs = 0, []
    for f in tree.files():
        if C.is_frozen(f):
            continue
        text = tree.read(f)
        hits = sum(1 for w in C.IDENT.findall(text) if w in m or w in co)
        if not hits:
            continue
        new = substitute(text, m, co)
        new, k = R.reflow_text(new, text, False)
        total += hits
        print("%-64s %4d tokens, %2d paragraphs" % (f, hits, k))
        code = C.split(new)[0].split("\n")
        for n, line in enumerate(new.split("\n"), 1):
            if C.bw(line) > C.LINE_LIMIT and code[n - 1].strip():
                longs.append("   CODE LINE %s:%d (%d bytes) %s"
                             % (f, n, C.bw(line), line.strip()[:60]))
        if not a.dry_run:
            tree.write(f, new)
    print("%d tokens substituted%s" % (total, " (dry run)" if a.dry_run else ""))
    for l in longs:
        print(l)
    if longs:
        print("%d code lines need a human break" % len(longs))
    return 0


def cmd_check(a, tree):
    m = read_map(a.map)
    co = dict(p.split("=", 1) for p in (a.comment_only or []))
    move = dict(zip(a.move[::2], a.move[1::2])) if a.move else {}
    base = C.Base(a.base, tree)
    ok, changed, pending = True, 0, 0
    for rel in base.files():
        bt = base.read(rel)
        cur_rel = move.get(rel, rel)
        if not os.path.exists(os.path.join(tree.root, cur_rel)):
            print("MISSING %s" % cur_rel)
            ok = False
            continue
        cur = tree.read(cur_rel)
        want = substitute(bt, m, co)
        if want == cur:
            continue
        changed += 1
        good = True
        if C.code_tokens(want) != C.code_tokens(cur):
            good = False
            ta, tb = C.code_tokens(want), C.code_tokens(cur)
            print("   CODE TOKENS DIFFER %s (%d against %d)"
                  % (cur_rel, len(ta), len(tb)))
            for k, (x, y) in enumerate(zip(ta, tb)):
                if x != y:
                    print("      first at token %d: %r against %r" % (k, x, y))
                    break
        pa = [p.text for p in C.paragraphs(want)[1]]
        pb = [p.text for p in C.paragraphs(cur)[1]]
        if pa != pb:
            good = False
            import difflib
            sm = difflib.SequenceMatcher(None, pa, pb, autojunk=False)
            for tag, i1, i2, j1, j2 in sm.get_opcodes():
                if tag == "equal":
                    continue
                print("   COMMENT CHANGE %s (%s)" % (cur_rel, tag))
                for t in pa[i1:i2]:
                    print("      base : %s" % t[:150])
                for t in pb[j1:j2]:
                    print("      found: %s" % t[:150])
        old_lines = set(bt.split("\n"))
        code = C.split(cur)[0].split("\n")
        for n, line in enumerate(cur.split("\n"), 1):
            if line in old_lines:
                continue
            if C.bw(line) > C.LINE_LIMIT:
                if code[n - 1].strip():
                    pending += 1     # a code line: a human breaks it
                else:
                    good = False
                    print("   LONG COMMENT %s:%d (%d bytes)"
                          % (cur_rel, n, C.bw(line)))
            if C.BARRED.search(line):
                good = False
                print("   BARRED %s:%d: %s" % (cur_rel, n, line.strip()))
            for w in C.IDENT.findall(line):
                if w in m or w in co:
                    good = False
                    print("   LEFTOVER %s:%d: %s" % (cur_rel, n, w))
        ok &= good
        print("%s  %s" % ("SAME " if good else "DIFF ", cur_rel))
    print("%d files changed, %d code lines over 80 bytes await a human break"
          % (changed, pending))
    print("ALL OK" if ok else "PROBLEMS")
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("action", choices=["build", "apply", "check"])
    ap.add_argument("map")
    ap.add_argument("--modules", nargs="*", default=None)
    ap.add_argument("--probe", default=None)
    ap.add_argument("--comment-only", nargs="*", default=None)
    ap.add_argument("--move", nargs=2, action="extend", default=None,
                    help="a file the rename moves: its base path, its new one")
    ap.add_argument("--base", default=None)
    ap.add_argument("--dry-run", action="store_true")
    C.add_root_arg(ap)
    a = ap.parse_args()
    tree = C.Tree(a.root)
    if a.action == "check" and not a.base:
        C.die("check needs --base")
    fn = {"build": cmd_build, "apply": cmd_apply, "check": cmd_check}[a.action]
    sys.exit(fn(a, tree))


if __name__ == "__main__":
    main()
