#!/usr/bin/env python3
"""Regenerate diffs/ for every copy of an existing production file.

Writes <name>.v.diff, the raw unified diff at two lines of context, and
<name>.v.code.diff, the same with comments stripped and blank lines dropped,
at one line of context. Prints the hunk counts.
"""
import difflib
import os

PROBE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.normpath(os.path.join(PROBE, "..", "..", ".."))
OUT = os.path.join(PROBE, "diffs")

PAIRS = {
    "five_card_analysis.v": "instances/kim2025/five_card_analysis.v",
    "pgg_analysis_manifest.v": "manifest/pgg_analysis_manifest.v",
    "pgg_analysis_client.v": "manifest/pgg_analysis_client.v",
    "pgg_tableau.v": "manifest/pgg_tableau.v",
    "pgg_tableau_syntax.v": "manifest/pgg_tableau_syntax.v",
    "s5_rows.v": "instances/s5/s5_rows.v",
    "pgl27_rows.v": "instances/pgl27/pgl27_rows.v",
    "psl211_rows.v": "instances/psl211/psl211_rows.v",
    "five_card_rows.v": "instances/kim2025/five_card_rows.v",
}


def strip_comments(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif text.startswith("*)", i) and depth:
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return [l.rstrip() for l in "".join(out).split("\n") if l.strip()]


def main():
    tot_h = tot_c = tot_imp = 0
    print("| copy | hunks | code hunks | code hunks holding a Require |")
    print("|---|---|---|---|")
    for copy, prod in sorted(PAIRS.items()):
        a = open(os.path.join(REPO, prod), encoding="utf-8").read()
        b = open(os.path.join(PROBE, copy), encoding="utf-8").read()
        raw = list(difflib.unified_diff(
            a.split("\n"), b.split("\n"),
            "production/" + prod, "probe/" + copy, n=2, lineterm=""))
        code = list(difflib.unified_diff(
            strip_comments(a), strip_comments(b),
            "prod-nocomment", "probe-nocomment", n=1, lineterm=""))
        open(os.path.join(OUT, copy + ".diff"), "w").write("\n".join(raw) + "\n")
        open(os.path.join(OUT, copy + ".code.diff"), "w").write(
            "\n".join(code) + "\n")
        h = sum(1 for l in raw if l.startswith("@@"))
        c = sum(1 for l in code if l.startswith("@@"))
        imp = 0
        cur = None
        for l in code:
            if l.startswith("@@"):
                if cur:
                    imp += 1
                cur = False
            elif cur is False and l[:1] in "+-" and "Require" in l:
                cur = True
        if cur:
            imp += 1
        print("| `%s` | %d | %d | %d |" % (copy, h, c, imp))
        tot_h += h
        tot_c += c
        tot_imp += imp
    print("TOTAL hunks %d, code hunks %d, of them with a Require %d, landing %d"
          % (tot_h, tot_c, tot_imp, tot_c - tot_imp))


main()
