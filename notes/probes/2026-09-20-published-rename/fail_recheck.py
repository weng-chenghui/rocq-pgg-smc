#!/usr/bin/env python3
"""Re-checks the recorded Fail commands that hold a renamed identifier.

A batch `rocq compile` prints nothing for a Fail that still fails, so each
recorded rejection is compiled once more without the word Fail, in the context
its own file gives it: the production file from its first line up to the line
above the command, then the command itself.  The scratch file goes under
fail_recheck/ and -o keeps its .vo there, so no production .vo is touched.

usage: fail_recheck.py [--gen]      (--gen writes the files and stops)
"""
import io
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = subprocess.check_output(
    ["git", "-C", HERE, "rev-parse", "--show-toplevel"]).decode().strip()
OUT = os.path.join(HERE, "fail_recheck")
LOCK = ("/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc"
        "/493d5ea4-6d9f-45fd-89c2-07339e63cb36/scratchpad/rocq1")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

NEW = {l.split("\t")[1]
       for l in open(os.path.join(HERE, "rename_map.tsv")).read().splitlines()
       if l.strip()}

FILES = ["instances/kim2025/tableau/five_card_tableau_checks.v",
         "instances/pgl27/tableau/pgl27_tableau_checks.v",
         "instances/psl211/tableau/psl211_tableau_checks.v",
         "manifest/pgg_analysis_manifest.v"]


def flags():
    out = []
    for line in open(os.path.join(ROOT, "_CoqProject")):
        w = line.split()
        if w and w[0] == "-arg":
            out += [x for x in w if x != "-arg"]
        elif w and w[0] in ("-R", "-Q"):
            out += [w[0], os.path.join(ROOT, w[1])] + w[2:]
    return out


def commands():
    """(file, line, command text) for every Fail holding a renamed name."""
    got = []
    for f in FILES:
        text = io.open(os.path.join(ROOT, f), encoding="utf-8").read()
        src = re.sub(r"\(\*.*?\*\)", lambda m: " " * len(m.group(0)), text,
                     flags=re.S)
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
            if any(w in NEW for w in IDENT.findall(cmd)):
                got.append((f, text[:m.start()].count("\n") + 1, cmd))
    return got


def generate():
    os.makedirs(OUT, exist_ok=True)
    made = []
    for f, line, cmd in commands():
        lines = io.open(os.path.join(ROOT, f),
                        encoding="utf-8").read().split("\n")
        slug = "%s_%d" % (os.path.basename(f)[:-2], line)
        body = re.sub(r"^(\s*)Fail\s+", r"\1", cmd, count=1)
        path = os.path.join(OUT, slug + ".v")
        io.open(path, "w", encoding="utf-8").write(
            "\n".join(lines[:line - 1]) + "\n" + body + "\n")
        made.append((f, line, slug, cmd.strip().split("\n")[0]))
    return made


def main():
    made = generate()
    for f, line, slug, first in made:
        print("%-62s %5d  %s" % (f, line, slug))
    if "--gen" in sys.argv:
        return
    fl = flags()
    for f, line, slug, first in made:
        src = os.path.join(OUT, slug + ".v")
        p = subprocess.run(
            [LOCK, "600", "8000", "rocq", "compile"] + fl
            + ["-o", os.path.join(OUT, slug + ".vo"), src],
            cwd=ROOT, capture_output=True, text=True)
        io.open(os.path.join(OUT, slug + ".log"), "w", encoding="utf-8").write(
            "rc=%d\n" % p.returncode + p.stdout + p.stderr)
        print("rc=%-4d %s" % (p.returncode, slug), flush=True)


if __name__ == "__main__":
    main()
