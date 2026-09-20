#!/usr/bin/env python3
"""The test driver of the toolkit.

Copies four production files with git show into a scratch directory and runs
the tools on the copies, so that no file of the repository is written and no
Rocq process is started.  Four groups:

  a  reflow --all is idempotent, leaves the code tokens and the comment word
     stream identical, adds no line over 80 bytes, and reports how many lines
     it changes on production text nobody touched.
  b  inventory, a filled sheet of three paragraph kinds, apply, check; then
     one applied paragraph is corrupted by hand and check must report it.
  c  rename build, apply and check with a two-name map, one new name long
     enough to make an index entry wrap.
  d  the reverse closure of the last commit, and a dry run of the compiles.

usage: selftest.py [--dir DIR] [--repo DIR] [--only a,b,c,d]
"""
import argparse
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import common as C                                            # noqa: E402
import reflow as R                                            # noqa: E402

FILES = ["manifest/pgg_tableau.v",
         "instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v",
         "reconstruct/invariant_profiler.v",
         "manifest/pgg_analysis_manifest.v"]
DEFAULT_DIR = ("/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-"
               "rocq-pgg-smc/493d5ea4-6d9f-45fd-89c2-07339e63cb36/"
               "scratchpad/toolkit_test")


def run(args, **kw):
    p = subprocess.run([sys.executable] + args, capture_output=True,
                       text=True, **kw)
    out = p.stdout + p.stderr
    print(out.rstrip())
    return p.returncode, out


def setup(d, repo):
    base, work = os.path.join(d, "base"), os.path.join(d, "work")
    for x in (base, work):
        shutil.rmtree(x, ignore_errors=True)
    for f in FILES:
        text = subprocess.check_output(
            ["git", "-C", repo, "show", "HEAD:" + f]).decode()
        for x in (base, work):
            os.makedirs(os.path.join(x, os.path.dirname(f)), exist_ok=True)
            open(os.path.join(x, f), "w", encoding="utf-8").write(text)
    return base, work


def reset(base, work):
    shutil.rmtree(work, ignore_errors=True)
    shutil.copytree(base, work)


# ------------------------------------------------------------------ group a

def group_a(base, work):
    import difflib
    ok, tot, totreg, totlines = True, 0, 0, 0
    for f in FILES:
        p = os.path.join(work, f)
        t = open(p, encoding="utf-8").read()
        one, _ = R.reflow_text(t, None, True)
        two, _ = R.reflow_text(one, None, True)
        a, b = t.split("\n"), one.split("\n")
        sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
        rem = sum(i2 - i1 for tag, i1, i2, _, _ in sm.get_opcodes()
                  if tag != "equal")
        reg = sum(1 for tag, *_ in sm.get_opcodes() if tag != "equal")
        was = {l for l in a if C.bw(l) > 80}
        new = [l for l in b if C.bw(l) > 80 and l not in was]
        good = (one == two and C.code_tokens(t) == C.code_tokens(one)
                and C.prose_words(t) == C.prose_words(one) and not new)
        ok &= good
        tot += rem
        totreg += reg
        totlines += len(a)
        print("%-46s %s idempotent %s, code %s, words %s, new long lines %d; "
              "%d of %d lines in %d regions"
              % (os.path.basename(f), "ok " if good else "BAD",
                 one == two, C.code_tokens(t) == C.code_tokens(one),
                 C.prose_words(t) == C.prose_words(one), len(new),
                 rem, len(a), reg))
        open(p, "w", encoding="utf-8").write(one)
    print("group a: %s; %d of %d lines changed on untouched production text, "
          "in %d regions" % ("OK" if ok else "PROBLEMS", tot, totlines, totreg))
    return ok


# ------------------------------------------------------------------ group b

def group_b(d, base, work):
    reset(base, work)
    sites = os.path.join(d, "sites.tsv")
    rc, _ = run([os.path.join(HERE, "inventory.py"), "certificate",
                 "--paths", "manifest/pgg_tableau.v", "--root", work,
                 "-o", sites, "--frozen"])
    head, rows = C.read_tsv(sites)
    want, kinds = [], set()
    for r in rows:
        if r["kind"] in kinds or r["kind"] == "table":
            continue
        kinds.add(r["kind"])
        r["new_text"] = r["old_text"].replace("certificate",
                                              "attestation-of-a-bound")
        r["case"] = "a word swap that forces the paragraph to wrap again"
        r["fact"] = "the declaration is unchanged"
        want.append(r)
        if len(want) == 3:
            break
    print("filled %d rows: %s" % (len(want), ", ".join(sorted(kinds))))
    filled = os.path.join(d, "filled.tsv")
    C.write_tsv(filled, head, want)
    rc, _ = run([os.path.join(HERE, "apply_tsv.py"), filled,
                 "--root", work, "--base", base])
    ok = rc == 0
    rc, out = run([os.path.join(HERE, "check_pass.py"), filled,
                   "--base", base, "--root", work])
    ok &= rc == 0 and "ALL OK" in out
    p = os.path.join(work, "manifest/pgg_tableau.v")
    text = open(p, encoding="utf-8").read()
    para = [x for x in C.paragraphs(text)[1]
            if "attestation-of-a-bound" in x.text][0]
    lines = text.split("\n")
    lines[para.first] = lines[para.first].replace("the ", "one ", 1)
    open(p, "w", encoding="utf-8").write("\n".join(lines))
    print("--- one applied paragraph corrupted by hand at line %d"
          % (para.first + 1))
    rc, out = run([os.path.join(HERE, "check_pass.py"), filled,
                   "--base", base, "--root", work])
    caught = rc != 0 and "UNEXPECTED COMMENT CHANGE" in out
    print("group b: %s (the corruption was %sreported)"
          % ("OK" if ok and caught else "PROBLEMS",
             "" if caught else "NOT "))
    return ok and caught


# ------------------------------------------------------------------ group c

def group_c(d, base, work):
    reset(base, work)
    m = os.path.join(d, "rename_map.tsv")
    open(m, "w", encoding="utf-8").write(
        "pgl27_word_cert\tpgl27_word_input_indistinguishability_evidence\n"
        "pgl27_exact_witness\tpgl27_exact_secrecy_witness\n")
    rc, out = run([os.path.join(HERE, "rename.py"), "build", m,
                   "--root", work, "--modules", "pgg_smc.pgg_tableau",
                   "--probe", os.path.join(d, "locate_probe.v")])
    ok = rc == 0
    rc, _ = run([os.path.join(HERE, "rename.py"), "apply", m, "--root", work])
    ok &= rc == 0
    rc, out = run([os.path.join(HERE, "rename.py"), "check", m,
                   "--root", work, "--base", base])
    ok &= rc == 0 and "ALL OK" in out
    f = os.path.join(work,
                     "instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v")
    for line in open(f, encoding="utf-8"):
        if "pgl27_word_input_indistinguishability_evidence" in line \
                and line.startswith("(*"):
            print("   " + line.rstrip())
    print("group c: %s" % ("OK" if ok else "PROBLEMS"))
    return ok


# ------------------------------------------------------------------ group d

def group_d(d, repo):
    order = os.path.join(d, "order.txt")
    rc, out = run([os.path.join(HERE, "closure.py"), "--changed", "HEAD~1",
                   "--root", repo, "-o", order])
    ok = rc == 0 and "frozen files met: none" in out
    rc, out = run([os.path.join(HERE, "compile_closure.py"), order,
                   "--dry-run", "--root", repo,
                   "--lock", "/path/to/rocq1"])
    ok &= rc == 0 and "would run" in out
    print("group d: %s" % ("OK" if ok else "PROBLEMS"))
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default=DEFAULT_DIR)
    ap.add_argument("--repo", default=os.path.dirname(os.path.dirname(HERE)))
    ap.add_argument("--only", default="a,b,c,d")
    a = ap.parse_args()
    os.makedirs(a.dir, exist_ok=True)
    base, work = setup(a.dir, a.repo)
    only = a.only.split(",")
    res = {}
    if "a" in only:
        print("\n===== group a: the layout pass on four production files")
        res["a"] = group_a(base, work)
    if "b" in only:
        print("\n===== group b: inventory, apply, check, and a corruption")
        res["b"] = group_b(a.dir, base, work)
    if "c" in only:
        print("\n===== group c: a two-name rename")
        res["c"] = group_c(a.dir, base, work)
    if "d" in only:
        print("\n===== group d: the closure and a dry run of the compiles")
        res["d"] = group_d(a.dir, a.repo)
    print("\n===== %s" % ", ".join("%s %s" % (k, "OK" if v else "PROBLEMS")
                                   for k, v in sorted(res.items())))
    return 0 if all(res.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
