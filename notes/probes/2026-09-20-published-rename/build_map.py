#!/usr/bin/env python3
"""Builds rename_map.tsv for the PublishedRow -> Published rename (layers A-E)
and checks it: every identifier of the tree that carries the manifest's word
is either mapped or listed as unrelated; the map is injective; no new name is
already an identifier anywhere in the tree (frozen files included).

Run from the repository root.  Writes rename_map.tsv beside this script.
"""
import collections
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

# Layer A-C: the framework and the manifest record.
FRAMEWORK = {
    "PublishedRowAt": "PublishedAt",
    "PublishedRow": "Published",
    "MkPublishedRow": "MkPublished",
    "published_row": "published_path",
    "AnalysisPathRow": "AnalysisPath",
    "MkAnalysisPathRow": "MkAnalysisPath",
}

# Layer E, manifest records: <inst>_row_<model> -> <inst>_<model>_path.
RECORDS = [
    ("pgl27", "exact"), ("pgl27", "word"), ("pgl27", "prior_exact"),
    ("five_card", "uniform"), ("five_card", "biased"),
    ("five_card", "repeated"),
    ("s5", "det"), ("s5", "rand"), ("s5", "word"),
    ("psl211", "alldecks"), ("psl211", "word"),
]

# Layer E, values.  old -> new, by hand: a value's new name is
# <inst>_<model>[_<arm or variant>]_<phase>[<bound>].
VALUES = {
    # S5
    "s5_row_rand_tableau": "s5_rand_published",
    # PSL(2,11)
    "psl211_row_alldecks_tableau": "psl211_alldecks_published",
    "psl211_row_word_proximity": "psl211_word_proximity_published",
    # PGL(2,7)
    "pgl27_row_exact_tableau": "pgl27_exact_published",
    "pgl27_row_word_tableau": "pgl27_word_published",
    "pgl27_row_prior_exact_tableau": "pgl27_prior_exact_published",
    "pgl27_row_word39": "pgl27_word_published39",
    "pgl27_row_word39_bind": "pgl27_word_published39_bind",
    "pgl27_row_word_branch39": "pgl27_word_branch_published39",
    "pgl27_row_word_proximity": "pgl27_word_proximity_published",
    # five-card, Sampled values that carried the manifest's word
    "five_card_row_repeated_tableau": "five_card_repeated_sampled",
    "five_card_row_biased_tableau": "five_card_biased_sampled",
    # five-card, published values
    "five_card_row_uniform_tableau": "five_card_uniform_published",
    "five_card_row_repeated_indistinguishability_tableau":
        "five_card_repeated_indistinguishability_published",
    "five_card_row_biased_indistinguishability_tableau":
        "five_card_biased_indistinguishability_published",
    "five_card_row_biased_branch_indistinguishability":
        "five_card_biased_branch_indistinguishability_published",
    "five_card_row_biased_proximity": "five_card_biased_proximity_published",
    "five_card_row_repeated39": "five_card_repeated_published39",
    "five_card_row_biased_inv25": "five_card_biased_published_inv25",
}

# Lemmas and recorded Fail names that are NOT <value><suffix>; by hand.
SPECIAL = {
    # statements about a manifest record alone
    "five_card_row_biased_levelE": "five_card_biased_path_levelE",
    "s5_dealt_row_observedE": "s5_dealt_path_observedE",
    # statements about a model family alone
    "five_card_row_repeated_endpoint_lt": "five_card_repeated_endpoint_lt",
    "five_card_row_biased_leak_bound": "five_card_biased_leak_bound",
    # statements about a Sampled value
    "five_card_row_repeated_prefixE": "five_card_repeated_sampled_prefixE",
    "five_card_row_biased_prefixE": "five_card_biased_sampled_prefixE",
    "five_card_row_repeated_modelE": "five_card_repeated_sampled_modelE",
    "five_card_row_biased_modelE": "five_card_biased_sampled_modelE",
    # two published values compared
    "five_card_row_biased_forms_publishedE": "five_card_biased_forms_pathE",
    "five_card_row_biased_arm_neq": "five_card_biased_published_arm_neq",
    "pgl27_row_word_arm_neq": "pgl27_word_published_arm_neq",
    "pgl27_row_word_families_sampledE":
        "pgl27_word_published_families_sampledE",
    "pgl27_row_word_obs_sampledE": "pgl27_word_published_obs_sampledE",
    # recorded Fail names
    "five_card_row_biased_at_manifest_level":
        "five_card_biased_sampled_at_manifest_level",
    "five_card_row_repeated_indistinguishability_uniform_rowE":
        "five_card_repeated_indistinguishability_published_uniform_pathE",
    "five_card_row_repeated_proximity": "five_card_repeated_proximity",
    "five_card_row_repeated39_unindexed":
        "five_card_repeated_published39_unindexed",
    "five_card_row_s5_family": "five_card_s5_family_sampled",
    "pgl27_row_exact_leak7": "pgl27_exact_published_leak7",
    "pgl27_row_word39_unindexed": "pgl27_word_published39_unindexed",
    "pgl27_row_word39_unindexed_bind":
        "pgl27_word_published39_unindexed_bind",
    "pgl27_row_word41": "pgl27_word_published41",
    "psl211_row_vm_reuse": "psl211_vm_reuse_sampled",
}

# <value><suffix> lemmas: suffix map.
SUFFIX = {
    "_rowE": "_pathE",
    "_armE": "_armE",
    "_atE": "_atE",
    "_sampledE": "_sampledE",
    "_bindE": "_bindE",
    "_certE": "_certE",
    "_publishedE": "_path_fieldsE",
}

# Identifiers that carry the word for a different object (a row of a matrix,
# of a table of decks, of a trace): untouched.
UNRELATED = set("""
Q_row_sum Row Rows row rows row_ rowE _rowE ad_fiber_at_row ad_row
ad_row_asc6 ad_row_asc6' ad_row_in_hexad_blocks ad_row_in_mirror_blocks
ad_row_mem ad_row_size ad_split_over_row diff_basis_mx_row
fc_kim_row_stochastic mirror_swap_row mul_row_col
pgl27_cert_bound_row_dominant pgl27_code_view_row pgl27_code_view_row_mem
pgl27_exec_rowE pgl27_table_row_mem psl211_alldecks_row
psl211_blockline1_row_size psl211_exec_rowE psl211_leak_row psl211_map_row
psl211_perdeck_row_size rank_leq_row row_free row_free_inj row_j row_k
row_leq_rank row_mx row_of_tuple row_of_tupleK row_sub row_subP row_subPn
rows_lt12 rows_lt12_hexadT rows_lt12_mirrorT s5_cert_bound_row_dominant
tuple_of_row unif_offdiag_row_sum AnalysisPathRows
""".split())


def tree_files():
    out = subprocess.check_output(["git", "ls-files", "*.v"]).decode().split()
    return [f for f in out if not f.startswith("notes/")]


def main():
    files = tree_files()
    idents = collections.Counter()
    for f in files:
        idents.update(IDENT.findall(open(f, encoding="utf-8").read()))

    m = dict(FRAMEWORK)
    for inst, model in RECORDS:
        m[f"{inst}_row_{model}"] = f"{inst}_{model}_path"
    m.update(VALUES)
    m.update(SPECIAL)
    for w in [w for w in idents if w.startswith("apr_")]:
        m[w] = "ap_" + w[4:]

    # <value or record><suffix>
    # a lemma about a value whose name ended in _tableau was named after the
    # value's name without that ending.
    alias = {v[:-len("_tableau")]: VALUES[v] for v in VALUES
             if v.endswith("_tableau")}
    bases = sorted(set(VALUES) | set(alias)
                   | {f"{i}_row_{mo}" for i, mo in RECORDS},
                   key=len, reverse=True)
    problems = []
    for w in sorted(idents):
        if w in m or w in UNRELATED:
            continue
        if not re.search(r"(^|_)rows?(_|$|E$|\d)|Row", w):
            continue
        for b in bases:
            if w.startswith(b) and w[len(b):] in SUFFIX:
                nb = alias.get(b, m.get(b))
                m[w] = nb + SUFFIX[w[len(b):]]
                break
        else:
            problems.append(f"UNMAPPED {w} ({idents[w]})")

    inv = collections.defaultdict(list)
    for o, n in m.items():
        inv[n].append(o)
    for n, os_ in inv.items():
        if len(os_) > 1:
            problems.append(f"NOT INJECTIVE {n} <- {os_}")
        if n in idents and n not in m:
            problems.append(f"NEW NAME EXISTS {n} ({idents[n]} uses)")
        if n in m and m[n] != n:
            problems.append(f"NEW NAME IS AN OLD NAME {n}")
    for o in m:
        if o not in idents:
            problems.append(f"OLD NAME ABSENT {o}")

    with open(os.path.join(HERE, "rename_map.tsv"), "w") as fh:
        for o in sorted(m):
            if m[o] != o:
                fh.write(f"{o}\t{m[o]}\t{idents[o]}\n")
    total = sum(idents[o] for o in m if m[o] != o)
    print(f"{len([o for o in m if m[o] != o])} identifiers, {total} occurrences")
    for p in problems:
        print(p)
    sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
