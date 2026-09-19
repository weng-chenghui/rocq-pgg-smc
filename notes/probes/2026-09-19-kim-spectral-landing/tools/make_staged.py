#!/usr/bin/env python3
"""Build staged/ from the probe copies by rewriting Require sentences only.

Every substitution below is an exact byte-for-byte replacement of one region of
the probe copy, asserted to occur exactly once.  Nothing else of the file is
read or written, so the staged file differs from its probe copy in the printed
lines and in nothing else.

The permanent blocks are those spelled in STATUS.md, section "Import rewrite at
cp time"; for the manifest and the client they are production's own sentences,
read out of the production file rather than retyped here.
"""

import os
import sys

PROBE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.dirname(os.path.dirname(os.path.dirname(PROBE)))

# probe basename -> permanent relative path
TARGET = {
    "var_dist_supp.v": "lib/var_dist_supp.v",
    "five_card_mixing.v": "instances/kim2025/five_card_mixing.v",
    "five_card_analysis.v": "instances/kim2025/five_card_analysis.v",
    "pgg_analysis_manifest.v": "manifest/pgg_analysis_manifest.v",
    "pgg_analysis_client.v": "manifest/pgg_analysis_client.v",
    "five_card_rows.v": "instances/kim2025/five_card_rows.v",
}


def prod_lines(rel, first, last):
    """Production's physical lines first..last inclusive, 1-based, as bytes."""
    data = open(os.path.join(REPO, rel), "rb").read().split(b"\n")
    return b"\n".join(data[first - 1:last]) + b"\n"


def sub1(data, old, new, what):
    n = data.count(old)
    if n != 1:
        sys.exit("%s: expected 1 occurrence, found %d of %r" % (what, n, old))
    return data.replace(old, new)


def build(name):
    data = open(os.path.join(PROBE, name), "rb").read()

    if name == "var_dist_supp.v":
        pass

    elif name == "five_card_mixing.v":
        data = sub1(
            data,
            b"From pgg_smc Require Import perm_uniform pgg_interface"
            b" pgg_collusion_bound.\n",
            b"From pgg_smc Require Import perm_uniform var_dist_supp.\n"
            b"From pgg_smc Require Import pgg_interface pgg_collusion_bound.\n",
            name + " (perm_uniform line)",
        )
        data = sub1(
            data,
            b"From kim_landing_probe Require Import var_dist_supp.\n",
            b"",
            name + " (probe var_dist_supp line)",
        )

    elif name == "five_card_analysis.v":
        data = sub1(
            data,
            b"From kim_landing_probe Require Import five_card_mixing.\n",
            b"From pgg_smc Require Import five_card_mixing.\n",
            name,
        )

    elif name == "pgg_analysis_manifest.v":
        data = sub1(
            data,
            b"From pgg_smc Require Export pgl27_analysis s5_analysis"
            b" psl211_analysis.\n"
            b"From kim_landing_probe Require Export five_card_analysis.\n",
            prod_lines(TARGET[name], 75, 76),
            name,
        )

    elif name == "pgg_analysis_client.v":
        data = sub1(
            data,
            b"From kim_landing_probe Require Import pgg_analysis_manifest.\n",
            prod_lines(TARGET[name], 16, 16),
            name,
        )

    elif name == "five_card_rows.v":
        data = sub1(
            data,
            b"From kim_landing_probe Require Import five_card_mixing.\n"
            b"From kim_landing_probe Require Import pgg_analysis_manifest"
            b" pgg_tableau.\n"
            b"From kim_landing_probe Require Import pgg_tableau_syntax.\n",
            b"From pgg_smc Require Import five_card_mixing.\n"
            b"From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.\n"
            b"From pgg_smc Require Import pgg_tableau_syntax.\n",
            name,
        )

    else:
        sys.exit("unknown file " + name)

    out = os.path.join(PROBE, "staged", TARGET[name])
    os.makedirs(os.path.dirname(out), exist_ok=True)
    open(out, "wb").write(data)
    print("wrote", os.path.relpath(out, PROBE))


for n in TARGET:
    build(n)
