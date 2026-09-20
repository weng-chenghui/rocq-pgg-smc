#!/usr/bin/env python3
"""Single-file compiles of an order, one at a time, through the lock.

The flags come from _CoqProject.  Every compile goes through the lock wrapper
given by --lock, so that at most one Rocq process runs on the machine.  A
file of the frozen closure stops the run before anything is started.  The cap
is 1500 seconds per file, measured in CPU time when the platform reports the
CPU time of a child, and in wall time otherwise, which the log says.  The run
stops at the first failure and is resumable from its own log.

usage: compile_closure.py ORDER.txt [--dry-run] [--resume LOG] [--lock PATH]
                                    [--log LOG] [--root DIR] [--cap 1500]
"""
import argparse
import os
import resource
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C                                            # noqa: E402


def flags(root):
    out = []
    for line in open(os.path.join(root, "_CoqProject"), encoding="utf-8"):
        w = line.split()
        if not w:
            continue
        if w[0] == "-arg":
            out += [x for x in w if x != "-arg"]
        elif w[0] in ("-R", "-Q"):
            out += w[:3]
    return out


def done_of(log):
    if not log or not os.path.exists(log):
        return set()
    out = set()
    for line in open(log, encoding="utf-8"):
        w = line.split()
        if len(w) >= 2 and w[0] == "ok":
            out.add(w[-1])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("order")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--resume", default=None)
    ap.add_argument("--lock", default=None)
    ap.add_argument("--log", default=None)
    ap.add_argument("--cap", type=int, default=1500)
    C.add_root_arg(ap)
    a = ap.parse_args()
    tree = C.Tree(a.root)
    files = [l.strip() for l in open(a.order, encoding="utf-8")
             if l.strip() and not l.startswith("#")]
    frozen = [f for f in files if C.is_frozen(f)]
    if frozen:
        for f in frozen:
            print("FROZEN FILE IN THE ORDER %s" % f)
        C.die("nothing compiled")
    done = done_of(a.resume)
    fl = flags(tree.root)
    log = open(a.log, "a", encoding="utf-8") if a.log else None
    cpu = hasattr(resource, "RUSAGE_CHILDREN")
    print("%d files, %d already done, cap %d s of %s time"
          % (len(files), len(done), a.cap, "CPU" if cpu else "wall"))
    for f in files:
        if f in done:
            print("skip  %s" % f)
            continue
        cmd = ([a.lock, str(a.cap), "14000"] if a.lock else []) \
            + ["rocq", "compile"] + fl + [f]
        if a.dry_run:
            print("would run: %s" % " ".join(cmd))
            continue
        t0 = time.time()
        c0 = resource.getrusage(resource.RUSAGE_CHILDREN) if cpu else None
        p = subprocess.run(cmd, cwd=tree.root, capture_output=True, text=True)
        dt = time.time() - t0
        if cpu:
            c1 = resource.getrusage(resource.RUSAGE_CHILDREN)
            dt = (c1.ru_utime - c0.ru_utime) + (c1.ru_stime - c0.ru_stime)
        line = "%-3s %7.1f %s" % ("ok" if not p.returncode else "FAIL", dt, f)
        print(line, flush=True)
        if log:
            log.write(line + "\n")
            log.flush()
        if p.returncode:
            print((p.stdout + p.stderr)[-3000:])
            return 1
    print("ALL OK" if not a.dry_run else "dry run")
    return 0


if __name__ == "__main__":
    sys.exit(main())
