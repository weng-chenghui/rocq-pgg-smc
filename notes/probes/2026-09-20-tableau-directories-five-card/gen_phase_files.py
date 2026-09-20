#!/usr/bin/env python3
"""Generate the six staged five-card phase files and the reduced proximity
file from instances/kim2025/five_card_rows.v and
instances/kim2025/five_card_proximity.v.

Every moved declaration is sliced out of production with its attached comment
blocks and emitted verbatim, so token identity and docstring identity are a
property of the generator and not of a hand edit.  New declarations are
written out here in full.  Section banners and file headers are authored here.

Two traps the PGL(2,7) generator recorded and one this instance adds:

  1. a banner's title line is a separate comment span, skipped by its
     previous line being the rule line;
  2. the file header's box lines attach to the first declaration unless the
     preamble end is subtracted;
  3. this instance has three Sections.  A declaration's slice runs to the
     next declaration, so the Section and Variable lines that open a section
     ride on the PREVIOUS declaration's chunk and the End line rides on the
     LAST declaration of the section.  That places them correctly by
     construction wherever a whole section moves together, which is the case
     for all three here; the only hand-written scaffolding is the two lines
     that open Section five_card_proximity_distance, which precede the first
     declaration of the file and so belong to no chunk.

Usage: python3 gen_phase_files.py
"""

import os
import re
import textwrap

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
PROD_ROWS = os.path.join(ROOT, "instances", "kim2025", "five_card_rows.v")
PROD_PROX = os.path.join(ROOT, "instances", "kim2025", "five_card_proximity.v")
OUT_INST = os.path.join(HERE, "staged", "instances", "kim2025")
OUT_DIR = os.path.join(OUT_INST, "tableau")

LICENCE = [
    "(* infotheo: information theory and error-correcting codes in Rocq"
    "            *)",
    "(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later"
    "            *)",
]
RULE = "(" + "*" * 78 + ")"


# ---------------------------------------------------------------- formatting

WIDTH = 74


def box(s):
    line = ("(* " + s).rstrip() if s else "(*"
    # 77, not 78: a box content line ends with a space before *), which a
    # width check does not see.
    assert len(line) <= 77, line
    return line.ljust(78) + "*)"


def para(text):
    return [box(l) for l in textwrap.wrap(" ".join(text.split()), WIDTH)]


def entry(name, desc):
    out = []
    first = "  " + name.ljust(24)
    if len(name) >= 24:
        out.append(box("  " + name))
        first = " " * 26
    body = textwrap.wrap(" ".join(desc.split()), WIDTH - 29)
    out.append(box(first + "== " + body[0]))
    for l in body[1:]:
        out.append(box(" " * 29 + l))
    return out


def header(title, paras, defs, results):
    out = list(LICENCE) + [RULE]
    out += para(title)
    for p in paras:
        out.append(box(""))
        if p.startswith("\0LOC\n"):
            # A locator table is pre-wrapped: its indentation is its meaning,
            # so it is boxed line by line and never re-flowed.
            out += [box(l) for l in p[5:].split("\n")]
        else:
            out += para(p)
    if defs:
        out.append(box(""))
        out.append(box("Definitions:"))
        for n, d in defs:
            out += entry(n, d)
    if results:
        out.append(box(""))
        out.append(box("Key results:"))
        for n, d in results:
            out += entry(n, d)
    out.append(RULE)
    return "\n".join(out) + "\n"


def banner(title):
    lines = textwrap.wrap(" ".join(title.split()), WIDTH - 4)
    out = [RULE, box("    " + lines[0])]
    for l in lines[1:]:
        out.append(box(l))
    out.append(RULE)
    return "\n".join(out)


def doc(text):
    body = textwrap.wrap(" ".join(text.split()), 72)
    out = ["(** " + body[0]]
    for l in body[1:]:
        out.append("    " + l)
    out[-1] = out[-1] + " *)"
    return "\n".join(out)


# ------------------------------------------------------------------ slicing

DECL_RE = re.compile(
    r"^(?:Fail\s+)?(?:Local\s+|Global\s+)?"
    r"(Definition|Lemma|Theorem|Corollary|Fact|Remark|Example|Check)"
    r"\s+([A-Za-z0-9_']+)", re.M)


def comment_spans(text):
    spans, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            start, depth, i = i, 1, i + 2
            while i < n and depth:
                if text.startswith("(*", i):
                    depth += 1
                    i += 2
                elif text.startswith("*)", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            spans.append((start, i))
        else:
            i += 1
    return spans


def chunks(path):
    text = open(path).read()
    spans = comment_spans(text)
    ends = {b: a for a, b in spans}
    in_comment = [False] * (len(text) + 1)
    for a, b in spans:
        for k in range(a, b):
            in_comment[k] = True
    starts = [(m.start(), m.group(2)) for m in DECL_RE.finditer(text)
              if not in_comment[m.start()]]
    head_end = max(m.end() for m in re.finditer(r"^Local Open Scope.*$",
                                                text, re.M))
    res = {}
    prev_of = {}
    for k, (off, name) in enumerate(starts):
        nxt = starts[k + 1][0] if k + 1 < len(starts) else len(text)
        p = nxt
        while True:
            q = p
            while q > off and text[q - 1] in " \t\n":
                q -= 1
            if q in ends and ends[q] >= off:
                p = ends[q]
            else:
                p = q
                break
        decl = text[off:p].rstrip()
        prev_end = head_end if k == 0 else prev_of[k - 1]
        prev_of[k] = p
        attached = []
        for a, b in spans:
            if a >= prev_end and b <= off:
                blk = text[a:b]
                if blk.startswith("(***"):
                    continue
                ls = text.rfind("\n", 0, a) + 1
                prevline = text[text.rfind("\n", 0, ls - 1) + 1:ls - 1]
                if prevline == RULE:
                    continue
                attached.append(blk)
        res[name] = "\n".join(attached + [decl])
    return res


ROWS = chunks(PROD_ROWS)
PROX = chunks(PROD_PROX)


def M(name):
    if name in ROWS and name in PROX:
        raise SystemExit("ambiguous: " + name)
    if name in ROWS:
        return ROWS[name]
    return PROX[name]


def sub(name, *edits):
    """Intended docstring edits on a moved declaration: the leading (** ... *)
    block is unwrapped, edited and rewrapped, so no edit leaves a long line."""
    t = M(name)
    m = re.match(r"\(\*\*(?!\*)(.*?)\*\)", t, re.S)
    assert m, name
    words = " ".join(m.group(1).split())
    for old, new in edits:
        assert old in words, (name, old)
        words = words.replace(old, new, 1)
    return doc(words) + t[m.end():]


def emit(path, head, preamble, sections):
    parts = [head.rstrip(), "", preamble.strip(), ""]
    for title, items in sections:
        parts.append("")
        parts.append(banner(title))
        for it in items:
            parts.append("")
            parts.append(it.rstrip())
        parts.append("")
    txt = "\n".join(parts)
    txt = re.sub(r"\n{4,}", "\n\n\n", txt).rstrip() + "\n"
    for i, l in enumerate(txt.split("\n"), 1):
        assert len(l.encode()) <= 80, "%s:%d %d bytes" % (path, i,
                                                          len(l.encode()))
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, "w").write(txt)
    print("wrote %-60s %4d lines" % (os.path.relpath(path, HERE),
                                     txt.count("\n")))


SETTINGS = """Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.
"""

# The lower three phase files.  ssrfun is on the mathcomp line because
# exact: erefl is this pattern's standard proof and erefl does not resolve
# without it; production five_card_rows.v does not carry it.
LOWER = """From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import order ssrnum ssralg reals boolp.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_observed_execution.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_exec.
"""

# The Sampled file: production five_card_rows.v's block, with ssrfun added
# and Lia, zify and pgg_trace_secrecy left out, none of whose names any
# declaration of this file uses.
SAMPLED_PRE = """From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import reals boolp lra.
From infotheo Require Import fdist proba entropy.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage five_card_exec five_card_models.
From pgg_smc Require Import kim_input_privacy.
From pgg_smc Require Import five_card_mixing.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import five_card_tableau_observed.

""" + SETTINGS + """
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.
"""

# The AnalysisBridged file: the union of the two production blocks, with
# ssrfun added.
BRIDGED_LIBS = """Require Import Lia.
From mathcomp Require Import zify.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter pgg_trace_secrecy.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import var_dist_joint_law.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage five_card_exec five_card_models.
From pgg_smc Require Import kim_input_privacy.
From pgg_smc Require Import five_card_mixing.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
"""

BRIDGED_PRE = BRIDGED_LIBS + """From pgg_smc Require Import five_card_proximity.
From pgg_smc Require Import five_card_tableau_observed.
From pgg_smc Require Import five_card_tableau_sampled.

""" + SETTINGS + """
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.
"""

CHECKS_PRE = BRIDGED_LIBS + """From pgg_smc Require Import s5_models.
From pgg_smc Require Import s5_tableau_analysis_bridged.
From pgg_smc Require Import five_card_proximity.
From pgg_smc Require Import five_card_tableau_observed.
From pgg_smc Require Import five_card_tableau_sampled.
From pgg_smc Require Import five_card_tableau_analysis_bridged.

""" + SETTINGS + """
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.
"""


# ============================================================== 1. Algebraic

emit(
    os.path.join(OUT_DIR, "five_card_tableau_algebraic.v"),
    header(
        "five_card_tableau_algebraic: the five-card instance at the "
        "Algebraic level",
        ["The Algebraic level of a row holds an algebra and nothing besides, "
         "and the proposition it carries is True. A reader shown only this "
         "file has been shown which group cuts the deck, which scheme the "
         "dealer deals and which seats read, and no claim about a coalition, "
         "a run or a probability model. All seven published rows of this "
         "instance begin at that algebra, so five_card_algebraic_start is "
         "the one point at which the uniform analysis and Kim's two "
         "analyses agree.",
         "The algebra is five_card_algebra of five_card_exec.v and is not "
         "restated here: the cyclic group generated by the rotation "
         "five_card_group.fc_sigma acts on the five card positions, den "
         "Boer's five-card scheme deals the layout of a pair of committed "
         "bits into those five cards and carries its own encoding, "
         "reconstruction and privacy obligation, and the five seats start at "
         "the five card positions in order. Two is the threshold that "
         "algebra names, so every statement above this file that quantifies "
         "over a coalition quantifies over at most one of the five seats.",
         "What this file adds is that algebra read as the first line of a "
         "program, and the ideal function beside it. The one run mode of "
         "this instance is the committed one, and the keyword rule that "
         "opens such a run begins at a Targeted and not at a PGGAlgebraic, "
         "so the two records belong together: five_card_target is the "
         "algebra paired with the conjunction of the two committed bits, and "
         "its tg_algebra field is five_card_algebra, the algebra "
         "five_card_algebraic_start names. The three probability models the "
         "instance analyses part three levels above, at Sampled, so what "
         "this file fixes is shared by every row the instance publishes."],
        [("five_card_algebraic_start",
          "the five-card algebra as a program at Algebraic"),
         ("five_card_target",
          "the algebra with the ideal function a run of it computes")],
        []),
    LOWER + """From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.

""" + SETTINGS + """
Local Open Scope ring_scope.
""",
    [("The algebra as the first line of a row", [
        doc("The five-card instance at the Algebraic level: the algebra "
            "alone, under True, the proposition that level carries. One run "
            "mode is built on this value, the committed one, and "
            "five_card_committed_executableE is where the prefix all seven "
            "published rows continue from is identified with it.")
        + "\nDefinition five_card_algebraic_start : Tableau Algebraic :="
          "\n  tableau_start five_card_algebra."]),
     ("The ideal function the run computes", [
        sub("five_card_target",
            ("The prefix above names the same one",
             "The prefix five_card_committed names the same one"),
            ("held together by five_card_realises_expected below",
             "held together by five_card_realises_expected"))])])


# ============================================================= 2. Executable

emit(
    os.path.join(OUT_DIR, "five_card_tableau_executable.v"),
    header(
        "five_card_tableau_executable: the five-card instance at the "
        "Executable level",
        ["The Executable level adjoins run-level data to the algebra: what "
         "the run argument is, who commits, what the dealer lays, what a "
         "seat observes after a cut, what value the run is meant to recover "
         "and how much interpreter fuel it is allowed. The proposition is "
         "still True, so a reader shown this file has been shown which run "
         "is about to be made, and no proof that it terminates or that it "
         "recovers the value its parameters name.",
         "The instance does not branch here. One run mode is named, the "
         "committed one: the run argument is the pair of bits two parties "
         "commit, five_card_commits are the processes that commit them, "
         "den_boer_decode reads the pair back out of the payload list, the "
         "dealer lays den_boer_layout of that pair, den_boer_assemble_valid "
         "is the sharing claim of the encoding and is checked where it is "
         "written, and the interpreter is given fuel 100. The value the run "
         "is meant to recover is read off the Targeted rather than written "
         "again, which is what keeps the function a row names and the value "
         "its run recovers one term.",
         "The line continues five_card_algebraic_start through the raw bind "
         "rather than through a keyword rule. The rules dealt and supplied "
         "begin at a PGGAlgebraic and encoded at a Targeted over one, so the "
         "keyword surface has no form that continues a named value at "
         "Algebraic, and this is the one edge of a row the surface cannot "
         "write when the two levels are two files. The record the line "
         "builds is encoded_input_params at five_card_target's own function, "
         "which is the record the encoded rule builds from that same "
         "Targeted."],
        [("five_card_committed_executable",
          "the committed run's parameters as a program")],
        [("five_card_committed_executable_paramsE",
          "the committed line builds the record five_card_params names")]),
    LOWER + """From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import five_card_tableau_algebraic.

""" + SETTINGS + """
Local Open Scope ring_scope.
""",
    [("The committed run's parameters", [
        doc("The committed mode at the Executable level: the run argument is "
            "the pair of bits two parties commit, the dealer lays den Boer's "
            "five-card layout of the decoded pair, the value the run is "
            "meant to recover is the conjunction five_card_target names, and "
            "the interpreter is given fuel 100. Naming the parameters as a "
            "program is what lets the run facts of the level above be "
            "adjoined to a value rather than to a prefix spelled out again.")
        + "\nDefinition five_card_committed_executable : Tableau Executable :="
          "\n  five_card_algebraic_start ;;; params_step"
          "\n    of (encoded_input_params five_card_algebra (bool * bool)"
          "\n          (tg_f five_card_target) den_boer_layout"
          "\n          den_boer_assemble_valid den_boer_decode"
          "\n          five_card_commits 100).",
        doc("The parameter record this line builds is the one "
            "five_card_params names. The clauses above spell the record out "
            "a second time, so the equation is what lets a statement made at "
            "five_card_params be read as a statement about this program.")
        + "\nLemma five_card_committed_executable_paramsE :"
          "\n  projT2 (tableau_at five_card_committed_executable)"
          "\n  = five_card_params."
          "\nProof. exact: erefl. Qed."])])


# =============================================================== 3. Observed

emit(
    os.path.join(OUT_DIR, "five_card_tableau_observed.v"),
    header(
        "five_card_tableau_observed: the five-card instance at the Observed "
        "level",
        ["The Observed level adjoins the three run facts to the run "
         "parameters, and it is the first level at which a row proves "
         "anything. What it carries is run correctness: the interpreter "
         "finishes within fuel 100, each of the five seats reaches an "
         "endpoint, and the endpoints decode to the conjunction of the two "
         "committed bits. Nothing about a coalition is proved at this level, "
         "at any coalition size.",
         "One run reaches this level and one value names it. "
         "five_card_committed is the prefix all seven published rows and "
         "the three named Sampled values of the instance continue from, and "
         "it names its three obligations, each an existing lemma of "
         "five_card_exec.v.",
         "The ideal functionality sits here for the same reason. "
         "five_card_F is typed over five_card_observed, the execution this "
         "level reaches, and realises_expected is an equation between the "
         "value that execution names as the one to recover and the "
         "functionality's function. Neither mentions a coalition and neither "
         "mentions a probability model. five_card_FE reads off the two "
         "values a reader of five_card_F wants, the conjunction and the "
         "tolerated coalition size of one seat, and targeted_F takes that "
         "size from the scheme rather than from the row."],
        [("five_card_committed",
          "the prefix all seven rows share"),
         ("five_card_F", "the ideal functionality the run realises"),
         ("five_card_F_ite",
          "that ideal function, in its conditional spelling")],
        [("five_card_committed_paramsE",
          "the prefix drives the run five_card_params names"),
         ("five_card_committed_executableE",
          "the prefix is its Executable value with the three run facts "
          "adjoined"),
         ("five_card_FE",
          "that functionality is the conjunction at one tolerated seat"),
         ("five_card_realises_expected",
          "the value the run is meant to recover is the functionality's")]),
    LOWER + """From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import five_card_tableau_algebraic.
From pgg_smc Require Import five_card_tableau_executable.

""" + SETTINGS + """
Local Open Scope ring_scope.
""",
    [("The prefix all seven rows share", [
        M("five_card_committed"),
        M("five_card_committed_paramsE"),
        doc("The committed program is its own Executable value with the "
            "three run facts adjoined. The program above writes the algebra, "
            "the ideal function and the run clauses in one term, the "
            "Executable file names the parameters they build, and this "
            "equation is what keeps a reader from having to decide which of "
            "the two spellings a statement below is made at.")
        + "\nLemma five_card_committed_executableE :"
          "\n  (five_card_committed_executable"
          "\n     execute terminates by five_card_terminates"
          "\n             endpoints by five_card_endpoints"
          "\n             recon by five_card_recon) = five_card_committed."
          "\nProof. exact: erefl. Qed."]),
     ("The ideal functionality",
      [M("five_card_F"), M("five_card_FE"), M("five_card_F_ite"),
       M("five_card_realises_expected")])])


# ================================================================ 4. Sampled

emit(
    os.path.join(OUT_DIR, "five_card_tableau_sampled.v"),
    header(
        "five_card_tableau_sampled: the five-card instance at the Sampled "
        "level",
        ["The Sampled level adjoins a probability model to a run, and what "
         "it adds to run correctness is the identification of the two "
         "readings of a coalition: at every real field and every index of "
         "the family, the reader built from the interpreter's own endpoints "
         "is the one computed directly from the run argument and the cut. "
         "That identification is what turns a claim about the messages a run "
         "exchanges into a claim about a group action, and it is the last "
         "thing proved before an arm is named.",
         "Three families are named here, one per model a published row "
         "continues from, and all three sit over the one committed run and "
         "are indexed by the unit type. five_card_uniform_family draws the "
         "cut uniformly from the five rotations. kim_centi_family draws it "
         "by seven repetitions of Kim's biased cut at bias one hundredth, "
         "and kim_biased_family by one such cut. The two Kim families differ "
         "from the uniform one in the law of the rotation and in nothing "
         "else: the committed pair is drawn uniformly and independently of "
         "the cut in all three.",
         "five_card_row_repeated_tableau and five_card_row_biased_tableau "
         "are names the instance already had, and they carry the "
         "published-row suffix although both are Tableau Sampled values and "
         "neither is a published row. They are existing names and they stay. "
         "five_card_uniform_sampled follows the naming scheme, and the five "
         "rows written out from the prefix are identified with these three "
         "values in five_card_tableau_analysis_bridged.v.",
         "What is proved at this level beside the three models is of two "
         "kinds, and no arm of certify takes a payload of either. "
         "five_card_row_repeated_endpoint_lt is one starting position's "
         "endpoint marginal under the repeated model's cut law, a statement "
         "about where a single position is sent and not about what any set "
         "of seats reads. five_card_row_biased_leak_bound is Kim's "
         "input-privacy bound, an upper bound on the conditional mutual "
         "information between the two committed inputs and the executed "
         "colour reading at a list of card positions, given the conjunction "
         "the run computes, under the law the one-cut model samples; it is "
         "about a reading at a list of card positions and not about a "
         "coalition of seats, and it is a bound and not a vanishing. It is "
         "the one security statement this instance makes below "
         "AnalysisBridged, and it is of this level for two reasons: its "
         "subject is the law the named Sampled model samples, and no arm of "
         "certify takes a conditional mutual information as a payload, so "
         "no program can carry it one level up.",
         "The manifest records AnalysisBridged for both Kim rows, which "
         "five_card_row_biased_levelE states for the one-cut row, and the "
         "two programs named here reach Sampled. Each of the two rows also "
         "carries a certified program that does reach AnalysisBridged, in "
         "five_card_tableau_analysis_bridged.v, and the ascription of the "
         "one-cut Sampled program at the manifest's level is refused in "
         "five_card_tableau_checks.v."],
        [("five_card_uniform_sampled",
          "the committed run under the uniform rotation, named at Sampled"),
         ("five_card_row_repeated_tableau",
          "the committed run under seven of Kim's biased cuts, named at "
          "Sampled"),
         ("five_card_row_biased_tableau",
          "the committed run under one of Kim's biased cuts, named at "
          "Sampled")],
        [("five_card_row_repeated_prefixE",
          "the repeated model carries the prefix's algebra, parameters and "
          "observed execution"),
         ("five_card_row_biased_prefixE",
          "the one-cut model carries the same three"),
         ("five_card_row_repeated_modelE",
          "the repeated program samples the model the manifest's row names"),
         ("five_card_row_biased_modelE",
          "the one-cut program samples the model the manifest's row names"),
         ("five_card_row_biased_levelE",
          "the manifest's completion level for the one-cut row is "
          "AnalysisBridged"),
         ("five_card_row_repeated_endpoint_lt",
          "one starting position's endpoint marginal under the repeated "
          "model's cut law is within 2^-40 of uniform"),
         ("kim_centi_small",
          "the smallness condition at bias one hundredth"),
         ("five_card_row_biased_leak_bound",
          "Kim's input-privacy bound at the law the one-cut model "
          "samples")]),
    SAMPLED_PRE,
    [("The uniform rotation as a branch point", [
        doc("The committed run under the uniform rotation, named at Sampled. "
            "The family is indexed by the unit type, so one member at each "
            "real field, and the cut that member draws is already the "
            "uniform one on the five rotations, so a row over this model "
            "compares no biased cut with an ideal.")
        + "\nDefinition five_card_uniform_sampled : Tableau Sampled :="
          "\n  five_card_committed"
          "\n    sample five_card_uniform_family."]),
     ("Kim's two models",
      [sub("five_card_row_repeated_tableau",
           ("the prefix above and the seven-cut model",
            "the prefix five_card_committed and the seven-cut model")),
       M("five_card_row_biased_tableau")]),
     ("What the three models share with the prefix",
      [M("five_card_row_repeated_prefixE"), M("five_card_row_biased_prefixE"),
       M("five_card_row_repeated_modelE"), M("five_card_row_biased_modelE"),
       sub("five_card_row_biased_levelE",
           ("the rejected ascription that follows",
            "the rejected ascription of five_card_tableau_checks.v"))]),
     ("What the two Kim models carry beside their programs",
      [M("five_card_row_repeated_endpoint_lt"), M("kim_centi_small"),
       M("five_card_row_biased_leak_bound")])])


# ======================================================= 5. AnalysisBridged

emit(
    os.path.join(OUT_DIR, "five_card_tableau_analysis_bridged.v"),
    header(
        "five_card_tableau_analysis_bridged: the five-card instance at the "
        "AnalysisBridged level",
        ["The AnalysisBridged level adjoins one security arm to a Sampled "
         "value, and the proposition it carries is that arm's own, on top of "
         "run correctness and of the identification of the two readings of a "
         "coalition. A publish terminal then turns the value into a "
         "PublishedRow. Every payload this instance owes an arm is here, "
         "every row it publishes is here, and every statement whose subject "
         "is a payload or a row is here. The one security statement of the "
         "instance whose subject is neither is Kim's input-privacy bound, "
         "which is in five_card_tableau_sampled.v.",
         "Three arms are used over the one committed run. The exact arm "
         "takes an ExactWitness, whose one field is independence of a "
         "coalition's reading from the conjunction of the two committed "
         "bits; under the uniform rotation this is leak_view_set, the exact "
         "mutual information of a reveal pattern, at a pattern of at most "
         "one card, where that information is zero, and the arm carries no "
         "number. The input-indistinguishability arm takes a certificate "
         "comparing the readings of two committed pairs under one model, "
         "with the uniform rotation law as the ideal cut. The proximity arm "
         "takes a certificate comparing one model with an ideal one at the "
         "same index, and the ideal it names here is the uniform model "
         "itself, whose own privacy is the exact arm's theorem.",
         "Four numbers, each carried by one certificate. kim_centi_cert "
         "carries the seven-cut bundle's marginal bound, the square root of "
         "five times the seventh power of one eightieth, and its cert_eps is "
         "that number added to itself, one for each of the two committed "
         "pairs it compares. kim_biased_cert carries the one-cut bundle's "
         "marginal bound, the square root of five over eighty, so its "
         "cert_eps is the square root of five over forty. "
         "kim_biased_cert_exact carries the exact one-cut number, one "
         "fiftieth, so its cert_eps is one twenty-fifth. "
         "kim_biased_proximity_cert carries one fiftieth and compares one "
         "law with one law, so that is also what its row publishes.",
         "Two terminals restate a certificate's number as a constant a text "
         "quotes. five_card_row_repeated39 concludes the repeated row at two "
         "to the minus thirty-ninth, and kim_centi_cert_eps_lt is strict, so "
         "the number the row publishes is strictly above the number the "
         "certificate proved. five_card_row_biased_inv25 concludes the "
         "one-cut row at one twenty-fifth, and five_card_inv50_split is an "
         "equality, so there the two numbers are the same. Each of these "
         "numbers bounds a sum of absolute differences, twice a total "
         "variation distance, so a distinguisher's advantage against a row "
         "is at most half the number that row publishes: one hundredth at "
         "the proximity row, one fiftieth at the one-cut row concluded at "
         "one twenty-fifth. five_card_biased_view_own_marginals removes the "
         "ideal from the proximity row's statement, at three fiftieths, "
         "which leaves an advantage of at most three hundredths.",
         "Two is the threshold the derived profile declares, so every "
         "statement here that quantifies over a coalition quantifies over at "
         "most one of the five seats, each seat reading the card at the cut "
         "image of its own position. No sharpness annotation is written at "
         "any row of this "
         "instance, because the closed forms of the leakage at two or more "
         "cards are proved positive nowhere.",
         "Seven rows are published, and the three the manifest carries for "
         "this instance are among them: five_card_row_uniform_rowE, "
         "five_card_row_repeated_indistinguishability_rowE and "
         "five_card_row_biased_indistinguishability_rowE discharge "
         "five_card_row_uniform, five_card_row_repeated and "
         "five_card_row_biased of pgg_analysis_manifest.v by conversion, and "
         "those three are all the AnalysisPathRows the manifest carries over "
         "the five-card instance. The manifest publishes none of the three "
         "by a route this development's programs do not take. Of the other "
         "four, three write a claim the manifest already carries a second "
         "way: the repeated row and the one-cut row concluded at the "
         "constants a text quotes, and the one-cut row continued from its "
         "named Sampled value. The fourth is the proximity row, which "
         "publishes that same AnalysisPathRow under a different arm. A "
         "published row is a program, "
         "and an AnalysisPathRow holds descriptive metadata and no Prop, so "
         "two rows publishing one AnalysisPathRow say nothing about each "
         "other's claim.",
         "\0LOC\n" + "\n".join(["Where each published row's chain is, one entry per row.", 'five_card_row_uniform_tableau, under The uniform row:', '    five_card_row_uniform_sampledE, five_card_row_uniform_rowE,', '    five_card_row_uniform_armE, and the reading', '    five_card_exact_view_secrecy.', "five_card_row_repeated_indistinguishability_tableau, under Kim's two", '    rows, certified against the uniform rotation law:', '    five_card_row_repeated_indistinguishability_sampledE, _rowE, _armE', '    and _publishedE, and no reading of its own.', 'five_card_row_biased_indistinguishability_tableau, under the same', '    banner: five_card_row_biased_indistinguishability_sampledE, _rowE,', '    _armE and _publishedE, and no reading of its own.', 'five_card_row_repeated39, under The same two rows at the constants', '    they publish: five_card_row_repeated39_sampledE,', '    five_card_row_repeated39_atE, five_card_row_repeated39_armE, no', '    _rowE of its own, and no reading of its own.', 'five_card_row_biased_inv25, under the same banner:', '    five_card_row_biased_inv25_sampledE,', '    five_card_row_biased_inv25_armE,', '    five_card_row_biased_forms_publishedE in place of a _rowE of its', '    own, and no reading of its own.', 'five_card_row_biased_branch_indistinguishability, under One model, two', '    claims, two rows: written from five_card_row_biased_tableau, so no', '    _sampledE, then _atE, _rowE and _armE, and no reading of its own.', 'five_card_row_biased_proximity, under the same banner: written from', '    five_card_row_biased_tableau, so no _sampledE,', '    five_card_row_biased_proximity_rowE, _publishedE and _armE, and the', '    readings five_card_biased_view_proximity and', '    five_card_biased_view_own_marginals.']),
         "An importer of this instance names one module per kind of name. "
         "The algebraic file declares the Algebraic value and the Targeted; "
         "the executable file the Executable value and its parameter "
         "equation; the observed file the prefix, its two equations and the "
         "ideal functionality; the sampled file the three named models, "
         "their equations against the prefix and the three statements "
         "carried beside them; this file the payloads, the rows, the row, "
         "arm and re-cut equations, the numbers and the arm theorems; and the "
         "checks file the recorded rejections and the comparison of the two "
         "one-cut rows' arms. No file of the six uses Require Export.",
         "This file requires instances/kim2025/five_card_proximity.v, which "
         "holds the laws and the distance the proximity certificate is "
         "built from: the uniform law on the pair of committed bits under "
         "either cardinality proof, the factorisation of a coalition's "
         "reading and the secret through the pair of the committed bits and "
         "the cut, that pair's joint law at a product law on the sample "
         "space, and the bound of one fiftieth on the distance between the "
         "two models' joint laws, which is the certificate's last field. "
         "The six link lemmas of the exact arm are not there but here, "
         "because no proof that stays uses them."],
        [("five_card_colour_fill",
          "a coalition's colours read back as card positions"),
         ("five_card_exact_witness",
          "the exact arm's witness at every field and index"),
         ("five_card_row_uniform_tableau",
          "the uniform row as a program"),
         ("kim_centi_cert",
          "the repeated row's certificate at its bundle's number"),
         ("kim_biased_cert",
          "the one-cut row's certificate at its bundle's number"),
         ("five_card_row_repeated_indistinguishability_tableau",
          "the repeated row as a program at the "
          "input-indistinguishability arm"),
         ("five_card_row_biased_indistinguishability_tableau",
          "the one-cut row as a program at that same arm"),
         ("five_card_reprice39",
          "the name two to the minus thirty-ninth for a bound"),
         ("five_card_row_repeated39",
          "the repeated row concluded at that number"),
         ("kim_biased_cert_exact",
          "the one-cut row's certificate at the exact number one fiftieth"),
         ("five_card_reprice_inv25",
          "the name one twenty-fifth for a bound"),
         ("five_card_row_biased_inv25",
          "the one-cut row concluded at that number"),
         ("kim_biased_proximity_cert",
          "the one-cut model's proximity certificate"),
         ("five_card_row_biased_branch_indistinguishability",
          "the one-cut row at the input-indistinguishability arm, continued "
          "from the named model"),
         ("five_card_row_biased_proximity",
          "the one-cut row as a program at the proximity arm, published at "
          "one fiftieth"),
         ("five_card_reprice_inv100",
          "the name one hundredth for a bound"),
         ("five_card_biased_proximity_at_singleton",
          "the proximity row's claim at one concrete seat")],
        [("five_card_viewS_nth",
          "a coalition's colour tuple read at one of its own seats"),
         ("five_card_static_obsE",
          "the framework's direct computation of a coalition's reading is "
          "the instance's colour reading encoded"),
         ("five_card_viewS_indep",
          "at most one revealed colour is independent of the conjunction"),
         ("five_card_exact_viewE",
          "the same identification with the committed pair and the cut left "
          "in the sample point"),
         ("five_card_static_obs_indep",
          "below the threshold of two, that is at a coalition of at most "
          "one of the five seats, the direct computation is independent of "
          "the conjunction"),
         ("five_card_row_uniform_sampledE",
          "the uniform row continues the named uniform model"),
         ("five_card_row_uniform_rowE",
          "the uniform program publishes the manifest's row"),
         ("five_card_row_uniform_armE",
          "the uniform row carries the exact arm"),
         ("five_card_exact_view_secrecy",
          "at a coalition of at most one of the five seats, the exact arm's "
          "four conjuncts at this instance"),
         ("kim_biased_epsE",
          "the one-cut bundle's marginal bound in closed form"),
         ("kim_biased_exact_le_eps",
          "the exact one-cut distance is under that bound"),
         ("five_card_row_repeated_indistinguishability_sampledE",
          "the repeated certified row continues the named repeated model"),
         ("five_card_row_biased_indistinguishability_sampledE",
          "the one-cut certified row continues the named one-cut model"),
         ("five_card_row_repeated_indistinguishability_rowE",
          "the repeated certified program publishes the manifest's row"),
         ("five_card_row_biased_indistinguishability_rowE",
          "the one-cut certified program publishes the manifest's row"),
         ("five_card_row_repeated_indistinguishability_armE",
          "the repeated certified row carries the "
          "input-indistinguishability arm"),
         ("five_card_row_biased_indistinguishability_armE",
          "the one-cut certified row carries that same arm"),
         ("five_card_row_repeated_indistinguishability_publishedE",
          "the three coordinates the repeated certified program publishes"),
         ("five_card_row_biased_indistinguishability_publishedE",
          "the three coordinates the one-cut certified program publishes"),
         ("five_card_pow2_39_split",
          "two to the minus thirty-ninth as a sum of two per-pair bounds"),
         ("kim_centi_cert_epsE",
          "the repeated row's number in closed form"),
         ("kim_centi_cert_eps_lt",
          "that number is under two to the minus thirty-ninth, strictly"),
         ("kim_biased_cert_epsE",
          "the one-cut row's number in closed form"),
         ("kim_biased_cert_eps_lt2",
          "that number is under two, the bound var_dist_le2 gives"),
         ("five_card_row_repeated39_sampledE",
          "the concluded repeated row continues the named repeated model"),
         ("five_card_row_repeated39_atE",
          "the repeated row at two to the minus thirty-ninth and at its own "
          "number carry one accumulated stack"),
         ("five_card_row_repeated39_armE",
          "the concluded repeated row carries that same arm"),
         ("five_card_inv50_split",
          "one twenty-fifth as a sum of two per-pair bounds"),
         ("five_card_row_biased_inv25_sampledE",
          "the concluded one-cut row continues the named one-cut model"),
         ("five_card_row_biased_forms_publishedE",
          "the two one-cut certified programs publish one row"),
         ("five_card_row_biased_inv25_armE",
          "the concluded one-cut row carries that same arm"),
         ("five_card_reprice_inv25_lt2",
          "one twenty-fifth is under two"),
         ("kim_biased_proximity_cert_idealE",
          "the certificate's ideal is the uniform row's model, and the port "
          "built from its witness is that row's port"),
         ("kim_biased_proximity_cert_epsE",
          "the certificate's number is one fiftieth"),
         ("kim_biased_proximity_eps_halfE",
          "the exact input-indistinguishability certificate's number is "
          "twice the proximity certificate's"),
         ("kim_biased_proximity_cert_eps_lt2",
          "that number is under two, the bound var_dist_le2 gives"),
         ("five_card_row_biased_branch_indistinguishability_atE",
          "the branch and the program written out from the prefix hold one "
          "coordinate"),
         ("five_card_row_biased_branch_indistinguishability_rowE",
          "the branch publishes the manifest's row for the one-cut path"),
         ("five_card_row_biased_proximity_rowE",
          "the proximity row publishes that same row"),
         ("five_card_row_biased_proximity_publishedE",
          "the three coordinates the proximity row publishes"),
         ("five_card_row_biased_branch_indistinguishability_armE",
          "the branch carries the input-indistinguishability arm"),
         ("five_card_row_biased_proximity_armE",
          "the proximity row carries the proximity arm"),
         ("five_card_biased_view_proximity",
          "at a coalition of at most one of the five seats, the proximity "
          "row's security statement, at one fiftieth"),
         ("five_card_biased_view_own_marginals",
          "the same at the same coalitions with the ideal removed, at three "
          "fiftieths"),
         ("kim_biased_conclude_below_false",
          "the conclude obligation at a number below the certificate's own "
          "is false"),
         ("five_card_singleton_below_threshold",
          "one seat is below the five-card privacy threshold"),
         ("five_card_biased_proximity_prop_holds",
          "the proximity arm's proposition at the number the row "
          "publishes"),
         ("five_card_biased_indistinguishability_implies_proximity",
          "the input-indistinguishability proposition implies it, its "
          "premise discarded")]),
    BRIDGED_PRE,
    [("The instance-side reading of a coalition",
      [M("five_card_colour_fill"), M("five_card_viewS_nth"),
       M("five_card_static_obsE")]),
     ("The uniform family's witness",
      [M("five_card_viewS_indep"), M("five_card_exact_viewE"),
       M("five_card_static_obs_indep"), M("five_card_exact_witness")]),
     ("The uniform row", [
         sub("five_card_row_uniform_tableau",
             ("the prefix above, the uniform rotation model",
              "the prefix five_card_committed, the uniform rotation model")),
         doc("The uniform row continues the named uniform model. The program "
             "above writes the sample statement and the certify statement in "
             "one term and the Sampled file names the value between them, so "
             "this equation is what lets a statement made at "
             "five_card_uniform_sampled be read as a statement about the "
             "row.")
         + "\nLemma five_card_row_uniform_sampledE :"
           "\n  (five_card_uniform_sampled"
           "\n     certify ExactIndependence five_card_exact_witness"
           "\n     |> publish StaticExecutedOnly BaselineClassicalOnly)"
           "\n  = five_card_row_uniform_tableau."
           "\nProof. exact: erefl. Qed.",
         M("five_card_row_uniform_rowE"), M("five_card_row_uniform_armE")]),
     ("The exact arm's four conjuncts at this instance",
      [M("five_card_exact_view_secrecy")]),
     ("Kim's two certificates",
      [M("kim_biased_epsE"), M("kim_biased_exact_le_eps"),
       M("kim_centi_cert"), M("kim_biased_cert")]),
     ("Kim's two rows, certified against the uniform rotation law", [
         M("five_card_row_repeated_indistinguishability_tableau"),
         doc("The repeated certified row continues the named repeated "
             "model, so the model a reader of the row meets and the model "
             "the Sampled file names are one name and not two spellings.")
         + "\nLemma five_card_row_repeated_indistinguishability_sampledE :"
           "\n  (five_card_row_repeated_tableau"
           "\n     certify InputIndistinguishability kim_centi_cert"
           "\n     |> publish IdealFinite BaselineClassicalOnly)"
           "\n  = five_card_row_repeated_indistinguishability_tableau."
           "\nProof. exact: erefl. Qed.",
         M("five_card_row_biased_indistinguishability_tableau"),
         doc("The same for the one-cut row and the named one-cut model.")
         + "\nLemma five_card_row_biased_indistinguishability_sampledE :"
           "\n  (five_card_row_biased_tableau"
           "\n     certify InputIndistinguishability kim_biased_cert"
           "\n     |> publish IdealFinite BaselineClassicalOnly)"
           "\n  = five_card_row_biased_indistinguishability_tableau."
           "\nProof. exact: erefl. Qed.",
         M("five_card_row_repeated_indistinguishability_rowE"),
         M("five_card_row_biased_indistinguishability_rowE"),
         M("five_card_row_repeated_indistinguishability_armE"),
         M("five_card_row_biased_indistinguishability_armE"),
         M("five_card_row_repeated_indistinguishability_publishedE"),
         M("five_card_row_biased_indistinguishability_publishedE")]),
     ("The number each certificate publishes",
      [M("five_card_pow2_39_split"), M("kim_centi_cert_epsE"),
       M("kim_centi_cert_eps_lt"), M("kim_biased_cert_epsE"),
       M("kim_biased_cert_eps_lt2")]),
     ("The same two rows at the constants they publish", [
         M("five_card_reprice39"), M("five_card_row_repeated39"),
         doc("The concluded repeated row continues the named repeated model "
             "as well, so the row at the constant a text quotes and the row "
             "at the certificate's own number read their model off one "
             "name.")
         + "\nLemma five_card_row_repeated39_sampledE :"
           "\n  (five_card_row_repeated_tableau"
           "\n     certify InputIndistinguishability kim_centi_cert"
           "\n     |> conclude five_card_reprice39"
           "\n        by (fun R idx =>"
           "\n              Order.POrderTheory.ltW (kim_centi_cert_eps_lt R idx))"
           "\n     |> publish IdealFinite BaselineClassicalOnly)"
           "\n  = five_card_row_repeated39."
           "\nProof. exact: erefl. Qed.",
         M("five_card_row_repeated39_atE"),
         M("five_card_row_repeated39_armE"),
         M("kim_biased_cert_exact"), M("five_card_inv50_split"),
         M("five_card_reprice_inv25"), M("five_card_row_biased_inv25"),
         doc("The concluded one-cut row continues the named one-cut model.")
         + "\nLemma five_card_row_biased_inv25_sampledE :"
           "\n  (five_card_row_biased_tableau"
           "\n     certify InputIndistinguishability kim_biased_cert_exact"
           "\n     |> conclude five_card_reprice_inv25"
           "\n        by (fun R _ => ssr_ext.eqW (five_card_inv50_split R))"
           "\n     |> publish IdealFinite BaselineClassicalOnly)"
           "\n  = five_card_row_biased_inv25."
           "\nProof. exact: erefl. Qed.",
         M("five_card_row_biased_forms_publishedE"),
         M("five_card_row_biased_inv25_armE"),
         M("five_card_reprice_inv25_lt2")]),
     ("The proximity certificate, and its ideal",
      [sub("kim_biased_proximity_cert",
           ("kim_biased_proximity_close of this file",
            "kim_biased_proximity_close of five_card_proximity.v")),
       M("kim_biased_proximity_cert_idealE").split("\n(***")[0].rstrip()]),
     ("The number",
      ["Section kim_biased_proximity_numbers.\nVariable R : realType.",
       M("kim_biased_proximity_cert_epsE"),
       M("kim_biased_proximity_eps_halfE"),
       M("kim_biased_proximity_cert_eps_lt2")]),
     ("One model, two claims, two rows",
      [M("five_card_row_biased_branch_indistinguishability"),
       M("five_card_row_biased_branch_indistinguishability_atE"),
       M("five_card_row_biased_branch_indistinguishability_rowE"),
       M("five_card_row_biased_proximity"),
       M("five_card_row_biased_proximity_rowE"),
       M("five_card_row_biased_proximity_publishedE"),
       M("five_card_row_biased_branch_indistinguishability_armE"),
       M("five_card_row_biased_proximity_armE")]),
     ("What the proximity row states at this instance",
      [M("five_card_biased_view_proximity"),
       M("five_card_biased_view_own_marginals")]),
     ("A number below the certificate's is refused",
      [M("five_card_reprice_inv100"), M("kim_biased_conclude_below_false")]),
     ("Every hypothesis discharged at one concrete coalition",
      [M("five_card_singleton_below_threshold"),
       M("five_card_biased_proximity_at_singleton")]),
     ("The proximity proposition at this instance, and what implies it",
      [M("five_card_biased_proximity_prop_holds"),
       M("five_card_biased_indistinguishability_implies_proximity")])])


# ================================================================= 6. Checks

emit(
    os.path.join(OUT_DIR, "five_card_tableau_checks.v"),
    header(
        "five_card_tableau_checks: the terms the kernel refuses at the "
        "five-card instance",
        ["Each entry below is one written term that the kernel rejects, "
         "recorded so that the rejection is compiled rather than described. "
         "A recorded rejection says what it says about the one term written "
         "under it and about no other term: it fixes a spelling that does "
         "not typecheck, and states no general impossibility.",
         "Seven groups of rejections, and one positive statement. The "
         "first is what a model may be sampled over: a "
         "family typed against another instance's observed execution is "
         "refused where it is written. The second is the level a program "
         "reaches against the level the manifest records for its row, which "
         "the one-cut Sampled program does not meet and its certified "
         "sibling does. The third is a row equation written for another "
         "path, the repeated certified row against the uniform row, which "
         "differ in two of their five coordinates.",
         "The fourth is the terminal's index binder: a conclude payload with "
         "the right relation but no index binder is refused, which is what "
         "keeps a row from publishing a bound that holds only at the index a "
         "reader happened to pick. The fifth is the ideal function: a "
         "different Boolean function of the same two bits is refused where "
         "it is written, so the function a row names is decided by the "
         "kernel.",
         "The sixth is the proof: the proximity arm's proposition is a "
         "bound between two laws on a real field and not a Boolean the "
         "kernel reduces, so neither conversion nor done reaches it, and "
         "both spellings are refused.",
         "The seventh is what a certificate may hold, and its four "
         "rejections have two causes. One is about the ideal, whose "
         "adapter is typed over the row's own execution parameters, so "
         "another instance's model and the witness proved about it are "
         "refused there. Three are about the sample adapter every "
         "certificate type is indexed by, which separates the two Kim "
         "models although their families carry one index type, and which "
         "refuses a certificate of either arm where the other model's is "
         "required.",
         "The one positive statement of this file is a comparison of two "
         "rows rather than a statement about one, which is what puts it "
         "here: the two rows over the one-cut model carry different arms, so "
         "the pair is two statements about one probability model and not one "
         "statement published twice."],
        [],
        [("five_card_row_biased_arm_neq",
          "the two rows over the one-cut model carry different arms")]),
    CHECKS_PRE,
    [("What a model may be sampled over",
      [sub("five_card_row_s5_family",
           ("The two models above are typed",
            "The two models named at Sampled are typed"))]),
     ("The level a program reaches",
      [M("five_card_row_biased_at_manifest_level")]),
     ("A row equation written for another path",
      [M("five_card_row_repeated_indistinguishability_uniform_rowE")]),
     ("The terminal's index binder",
      [M("five_card_row_repeated39_unindexed")]),
     ("The ideal function", [M("five_card_F_or")]),
     ("The conclusion does not hold by computation",
      [M("five_card_biased_proximity_by_computation"),
       M("five_card_biased_proximity_by_done")]),
     ("What a certificate may name as its ideal",
      [M("kim_biased_cert_s5_ideal"),
       M("kim_centi_proximity_from_biased"),
       M("five_card_row_repeated_proximity"),
       M("kim_biased_indistinguishability_from_centi")]),
     ("The arm two rows over one model carry",
      [M("five_card_row_biased_arm_neq")])])


# ============================================= 7. reduced five_card_proximity

emit(
    os.path.join(OUT_INST, "five_card_proximity.v"),
    header(
        "five_card_proximity: the laws and the distance Kim's one-cut "
        "proximity certificate is built from",
        ["Kim's one-cut model and the den Boer uniform model of the "
         "five-card instance run one execution and share one sample space, "
         "the pair of committed bits with the sampled rotation; they differ "
         "in the law that space carries. This file holds the mathematics "
         "that separates the two, with no program and no published row in "
         "it.",
         "The distance is the certificate field of the proximity arm: at "
         "every coalition, the joint law of that coalition's reading with "
         "the conjunction of the committed bits under Kim's one biased cut "
         "is within one fiftieth of the same joint law under the uniform "
         "rotation. The number is the bound kim_biased_cut_mixing_exact "
         "proves on the cut group's own distance. The bound holds at every "
         "coalition and not only below the threshold of two; the threshold "
         "enters the arm's proposition and not this distance.",
         "Every number below bounds a sum of absolute differences, which is "
         "twice the total variation distance of the literature, so a bound "
         "of one fiftieth here is a distinguishing advantage of at most one "
         "hundredth wherever it is used.",
         "Three laws carry that proof. The uniform law on the pair of "
         "committed bits is one law under either of the two cardinality "
         "proofs the tree holds for that pair, which is what gives the "
         "product step below one common left factor. The pair of a "
         "coalition's reading and the secret factors through the pair of the "
         "committed bits and the cut, which is the carrier on which the two "
         "models are compared. And at a product law on the sample space that "
         "pair's joint law is the uniform pair tensored with the model's cut "
         "law, so the distance between the two models on the cut group is "
         "the distance between their two joint laws.",
         "The certificate itself, the row it publishes and the statements "
         "about them are in instances/kim2025/tableau/, whose "
         "AnalysisBridged file requires this one. This file requires no "
         "tableau module, so the arrow between the mathematics and the "
         "tableau runs one way, upward."],
        [],
        [("five_card_uniform_pairE",
          "the uniform law on the committed pair is one law under either "
          "cardinality proof"),
         ("five_card_reading_secretE",
          "a coalition's reading and the secret factor through the pair of "
          "the committed bits and the cut"),
         ("five_card_arg_cut_prodE",
          "at a product law on the sample space, that pair's joint law is "
          "the uniform pair tensored with the model's cut law"),
         ("kim_biased_proximity_close",
          "at every coalition, the two models' joint laws of reading and "
          "secret are within one fiftieth")]),
    """From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import var_dist_joint_law.
From pgg_reconstruct Require Import algebraic_rigidity.
From pgg_smc Require Import five_card_group five_card_family.
From pgg_smc Require Import five_card_exec five_card_models.
From pgg_smc Require Import five_card_leakage five_card_kim kim_input_privacy.
From pgg_smc Require Import five_card_mixing.

""" + SETTINGS + """
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
""",
    [("The distance between the two models' joint laws",
      ["Section five_card_proximity_distance.\nVariable R : realType.",
       M("five_card_uniform_pairE"), M("five_card_reading_secretE"),
       M("five_card_arg_cut_prodE"), M("kim_biased_proximity_close")])])

print("seven files written")
