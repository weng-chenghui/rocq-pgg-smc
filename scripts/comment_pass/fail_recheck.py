#!/usr/bin/env python3
"""Every recorded Fail command that holds one of the given identifiers,
compiled once more without the word Fail.

A batch compile prints nothing for a Fail that still fails, so a rejection
recorded in the tree says nothing about WHY the command is rejected once an
identifier in it has changed.  Each such command is compiled again in the
context its own file gives it: that file from its first line to the line
above the command, then the command without Fail.  The scratch file and its
.vo go under --out, so no production .vo is touched.

usage: fail_recheck.py (--ids MAP.tsv | --names N...) [--out DIR]
                       [--lock PATH] [--dry-run] [--root DIR]
"""
import argparse
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C                                            # noqa: E402
import compile_closure as CC                                  # noqa: E402


def commands(tree, names):
    """(file, line, command) for every Fail holding one of the names."""
    got = []
    for f in tree.files():
        text = tree.read(f)
        src = C.split(text)[0]
        for m in re.finditer(r"(?m)^[ \t]*Fail\b", src):
            end = m.start()
            while True:
                d = src.find(".", end)
                if d < 0:
                    end = len(src)
                    break
                if d + 1 >= len(src) or src[d + 1] in " \n\t":
                    end = d + 1
                    break
                end = d + 1
            cmd = text[m.start():end]
            if any(w in names for w in C.IDENT.findall(cmd)):
                got.append((f, text[:m.start()].count("\n") + 1, cmd))
    return got


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ids", default=None, help="a rename map: its new names")
    ap.add_argument("--names", nargs="*", default=None)
    ap.add_argument("--out", default="fail_recheck")
    ap.add_argument("--lock", default=None)
    ap.add_argument("--cap", type=int, default=600)
    ap.add_argument("--dry-run", action="store_true")
    C.add_root_arg(ap)
    a = ap.parse_args()
    tree = C.Tree(a.root)
    names = set(a.names or [])
    if a.ids:
        for line in open(a.ids, encoding="utf-8"):
            cells = line.rstrip("\n").split("\t")
            if len(cells) >= 2 and cells[0] != "old":
                names.add(cells[1])
    if not names:
        C.die("no identifier given")
    got = commands(tree, names)
    print("%d recorded Fail commands hold one of %d identifiers"
          % (len(got), len(names)))
    for f, line, cmd in got:
        print("%-62s %5d  %s" % (f, line, cmd.strip().split("\n")[0][:60]))
    if a.dry_run:
        for f, line, cmd in got:
            print("would compile %s without Fail, in the context of %s:1-%d"
                  % (cmd.strip().split("\n")[0][:40], f, line - 1))
        return 0
    os.makedirs(a.out, exist_ok=True)
    fl = CC.flags(tree.root)
    bad = 0
    for f, line, cmd in got:
        lines = tree.read(f).split("\n")
        slug = "%s_%d" % (os.path.basename(f)[:-2], line)
        body = re.sub(r"^(\s*)Fail\s+", r"\1", cmd, count=1)
        src = os.path.join(a.out, slug + ".v")
        open(src, "w", encoding="utf-8").write(
            "\n".join(lines[:line - 1]) + "\n" + body + "\n")
        cmd_line = ([a.lock, str(a.cap), "8000"] if a.lock else []) \
            + ["rocq", "compile"] + fl \
            + ["-o", os.path.join(a.out, slug + ".vo"), src]
        p = subprocess.run(cmd_line, cwd=tree.root, capture_output=True,
                           text=True)
        open(os.path.join(a.out, slug + ".log"), "w", encoding="utf-8").write(
            "rc=%d\n" % p.returncode + p.stdout + p.stderr)
        bad += p.returncode != 0
        print("rc=%-4d %s" % (p.returncode, slug), flush=True)
    print("%d of %d still rejected" % (bad, len(got)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
