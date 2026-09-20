#!/usr/bin/env python3
"""The reverse closure of a set of files over the Require graph, in an order
where a file comes after everything it requires.

A file of the frozen closure met on the way stops the run: the order is not
written and the exit code is 1, because the pass never compiles one.

usage: closure.py [FILES...] [--changed REV] [-o ORDER.txt] [--root DIR]
"""
import argparse
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C                                            # noqa: E402

REQUIRE = re.compile(r"^\s*(?:From\s+([\w.]+)\s+)?Require\s+"
                     r"(?:Import|Export)?\s*([^.]*)\.", re.M)
LIBS = ("pgg_smc", "pgg_reconstruct")


def graph(tree):
    files = tree.files()
    mod = {}
    for p in files:
        mod.setdefault(os.path.basename(p)[:-2], p)
    deps = {p: set() for p in files}
    for p in files:
        code = C.split(tree.read(p))[0]
        for m in REQUIRE.finditer(code):
            frm = m.group(1) or ""
            if frm and not frm.startswith(LIBS):
                continue
            for nm in m.group(2).split():
                nm = nm.split(".")[-1]
                if nm in mod and mod[nm] != p:
                    deps[p].add(mod[nm])
    rdeps = {p: set() for p in files}
    for p, ds in deps.items():
        for d in ds:
            rdeps[d].add(p)
    return files, deps, rdeps


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="*")
    ap.add_argument("--changed", default=None,
                    help="start from the files that differ from this revision")
    ap.add_argument("-o", "--out", default=None)
    C.add_root_arg(ap)
    a = ap.parse_args()
    tree = C.Tree(a.root)
    start = list(a.files)
    if a.changed:
        out = subprocess.check_output(
            ["git", "-C", tree.root, "diff", "--name-only", a.changed]
        ).decode().split()
        start += [f for f in out if f.endswith(".v")
                  and not f.startswith(C.SKIP_DIRS)]
    start = sorted(set(start))
    if not start:
        print("no file to start from")
        return 0
    files, deps, rdeps = graph(tree)
    seen, stack = set(), list(start)
    while stack:
        p = stack.pop()
        if p in seen or p not in deps:
            continue
        seen.add(p)
        stack += sorted(rdeps.get(p, ()))
    met = sorted(p for p in seen if C.is_frozen(p))
    order, mark = [], {}

    def visit(p):
        if mark.get(p) == 2:
            return
        mark[p] = 1
        for d in sorted(deps[p]):
            if d in seen:
                visit(d)
        mark[p] = 2
        order.append(p)

    for p in sorted(seen):
        visit(p)
    print("touched %d, closure %d" % (len(start), len(order)))
    if met:
        for p in met:
            print("FROZEN FILE IN THE CLOSURE %s" % p)
        print("PROBLEMS")
        return 1
    print("frozen files met: none")
    for p in order:
        print(p)
    if a.out:
        open(a.out, "w", encoding="utf-8").write("\n".join(order) + "\n")
        print("order -> %s" % a.out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
