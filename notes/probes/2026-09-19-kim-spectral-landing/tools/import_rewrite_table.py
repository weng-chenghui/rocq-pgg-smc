#!/usr/bin/env python3
"""Diff each landing copy's Require sentences against its production file.

For every .v file of this probe directory, print the `From ... Require ...`
sentences the production file has and the copy does not, and the sentences the
copy has and the production file does not. Sentences are comment-stripped,
whitespace-normalized, and may span several source lines. A copy with no
production counterpart is reported as new or as staying in the probe.

Run from anywhere:  python3 tools/import_rewrite_table.py
"""
import os
import re
import sys

PROBE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.normpath(os.path.join(PROBE, "..", "..", ".."))

# Where each copy's permanent file lives, or None.
TARGET = {
    "var_dist_supp.v": ("lib/var_dist_supp.v", "new"),
    "five_card_mixing.v": ("instances/kim2025/five_card_mixing.v", "new"),
    "five_card_analysis.v": ("instances/kim2025/five_card_analysis.v", None),
    "pgg_analysis_manifest.v": ("manifest/pgg_analysis_manifest.v", None),
    "pgg_analysis_client.v": ("manifest/pgg_analysis_client.v", None),
    "pgg_tableau.v": ("manifest/pgg_tableau.v", None),
    "pgg_tableau_syntax.v": ("manifest/pgg_tableau_syntax.v", None),
    "s5_rows.v": ("instances/s5/s5_rows.v", None),
    "pgl27_rows.v": ("instances/pgl27/pgl27_rows.v", None),
    "psl211_rows.v": ("instances/psl211/psl211_rows.v", None),
    "five_card_rows.v": ("instances/kim2025/five_card_rows.v", None),
    "l7_fail_messages.v": (None, "stays in the probe"),
    "kim_landing_fidelity.v": (None, "stays in the probe"),
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
    return "".join(out)


def requires(path):
    """Every Require sentence, in source order, whitespace-normalized."""
    body = strip_comments(open(path, encoding="utf-8").read())
    found = []
    for m in re.finditer(r"(?:From\s+\S+\s+)?Require\s+(?:Import|Export)[^.]*\.",
                         body):
        found.append(" ".join(m.group(0).split()))
    return found


def report(name):
    target, note = TARGET[name]
    copy = requires(os.path.join(PROBE, name))
    if target is None:
        return name, note, None, None
    prod_path = os.path.join(REPO, target)
    if not os.path.exists(prod_path):
        return name, "%s (%s)" % (target, note or "missing"), [], copy
    prod = requires(prod_path)
    removed = [s for s in prod if s not in copy]
    added = [s for s in copy if s not in prod]
    return name, target, removed, added


def main():
    names = [n for n in sorted(os.listdir(PROBE)) if n.endswith(".v")]
    unknown = [n for n in names if n not in TARGET]
    for name in names:
        if name in unknown:
            print("## %s\n  NO TARGET RECORDED\n" % name)
            continue
        n, target, removed, added = report(name)
        print("## %s -> %s" % (n, target))
        if removed is None:
            print("  no permanent file")
        elif not removed and not added:
            print("  production import block, unchanged")
        for s in (removed or []):
            print("  - production only: %s" % s)
        for s in (added or []):
            print("  + copy only:       %s" % s)
        print()
    if unknown:
        sys.exit(1)


main()
