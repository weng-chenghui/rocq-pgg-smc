#!/usr/bin/env python3
"""Compile one audit scratch file through the machine-wide Rocq lock."""
import subprocess, sys, os, time, shlex

ROOT = "/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc"
PROBE = os.path.join(ROOT, "notes/probes/2026-09-19-tableau-extensions")
AUD = os.path.join(PROBE, "audit-soundness-2")
ROCQ1 = ("/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc/"
         "493d5ea4-6d9f-45fd-89c2-07339e63cb36/scratchpad/rocq1")


def flags():
    f = []
    for line in open(os.path.join(ROOT, "_CoqProject")):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = shlex.split(line)
        if parts[0] == "-arg":
            f += [tok for tok in parts if tok != "-arg"]
        elif parts[0] in ("-R", "-Q"):
            f += [parts[0], os.path.join(ROOT, parts[1]), parts[2]]
    f += ["-Q", PROBE, "tableau_ext_probe"]
    return f


def main():
    fn = sys.argv[1]
    secs = sys.argv[2] if len(sys.argv) > 2 else "200"
    path = fn if os.path.isabs(fn) else os.path.join(AUD, fn)
    cmd = [ROCQ1, secs, "12000", "rocq", "compile", "-time"] + flags() + [path]
    t0 = time.time()
    p = subprocess.run(cmd, capture_output=True, text=True)
    dt = time.time() - t0
    print("### file:", fn)
    print("### rc =", p.returncode, " wall = %.1f s" % dt)
    print("### stdout ###")
    print(p.stdout)
    print("### stderr ###")
    print(p.stderr)


main()
