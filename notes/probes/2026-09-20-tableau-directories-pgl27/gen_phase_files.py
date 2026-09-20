#!/usr/bin/env python3
"""Generate the six staged PGL(2,7) phase files and the reduced proximity file
from instances/pgl27/pgl27_rows.v and instances/pgl27/pgl27_proximity.v.

Every moved declaration is sliced out of production with its attached comment
blocks and emitted verbatim, so token identity and docstring identity are a
property of the generator and not of a hand edit.  New declarations are
written out here in full.  Section banners and file headers are authored here.

Usage: python3 gen_phase_files.py
"""

import os
import re
import textwrap

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
PROD_ROWS = os.path.join(ROOT, "instances", "pgl27", "pgl27_rows.v")
PROD_PROX = os.path.join(ROOT, "instances", "pgl27", "pgl27_proximity.v")
OUT_INST = os.path.join(HERE, "staged", "instances", "pgl27")
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
    """A header paragraph, wrapped to the box."""
    return [box(l) for l in textwrap.wrap(" ".join(text.split()), WIDTH)]


def entry(name, desc):
    """One line of a Definitions: or Key results: table."""
    out = []
    first = "  " + name.ljust(24)
    if len(name) > 23:
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
        if isinstance(p, tuple) and p[0] == "lit":
            for l in p[1]:
                out += [box(x) for x in
                        textwrap.wrap(" ".join(l.split()), WIDTH,
                                      subsequent_indent="    ")]
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
    """A (** ... *) docstring, wrapped, with the project's 4-column indent."""
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
    """Map name -> the production text of that declaration with its attached
    non-banner comment blocks, exactly as production writes them."""
    text = open(path).read()
    spans = comment_spans(text)
    ends = {b: a for a, b in spans}
    in_comment = [False] * (len(text) + 1)
    for a, b in spans:
        for k in range(a, b):
            in_comment[k] = True
    starts = [(m.start(), m.group(2)) for m in DECL_RE.finditer(text)
              if not in_comment[m.start()]]
    # A banner is a maximal run of lines opening with (* that contains at
    # least one full-width rule line.  Keying on "the previous line is a
    # rule" misses a production banner's SECOND content line, which is then
    # emitted a second time outside the box.
    banner_at, off, run, has_rule = set(), 0, [], False
    for ln in text.split("\n"):
        if ln.startswith("(*"):
            run.append(off)
            has_rule = has_rule or ln == RULE
        else:
            if has_rule:
                banner_at |= set(run)
            run, has_rule = [], False
        off += len(ln) + 1
    if has_rule:
        banner_at |= set(run)
    # the file header and the preamble belong to no declaration
    head_end = max(m.end() for m in re.finditer(r"^Local Open Scope.*$",
                                                text, re.M))
    res = {}
    prev_of = {}
    for k, (off, name) in enumerate(starts):
        nxt = starts[k + 1][0] if k + 1 < len(starts) else len(text)
        # walk back over whitespace and whole comment blocks
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
        # the attached comment blocks are everything between the previous
        # declaration's end and off, minus the banners
        prev_end = head_end if k == 0 else prev_of[k - 1]
        prev_of[k] = p
        attached = []
        for a, b in spans:
            if a >= prev_end and b <= off:
                if a in banner_at:
                    continue
                attached.append(text[a:b])
        res[name] = ("\n".join(attached + [decl]), p)
    return {k: v[0] for k, v in res.items()}


ROWS = chunks(PROD_ROWS)
PROX = chunks(PROD_PROX)


def M(name):
    if name in ROWS and name in PROX:
        raise SystemExit("ambiguous: " + name)
    if name in ROWS:
        return ROWS[name]
    return PROX[name]


def sub(name, old, new):
    """One intended docstring edit on a moved declaration: the leading
    (** ... *) block is unwrapped, edited and rewrapped, so the edit never
    leaves an over-long line."""
    t = M(name)
    m = re.match(r"\(\*\*(?!\*)(.*?)\*\)", t, re.S)
    assert m, name
    words = " ".join(m.group(1).split())
    assert old in words, (name, old)
    return doc(words.replace(old, new, 1)) + t[m.end():]


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
    print("wrote %-58s %4d lines" % (os.path.relpath(path, HERE),
                                     txt.count("\n")))


SETTINGS = """Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.
"""

# The import block of instances/pgl27/pgl27_rows.v, with ssreflect and ssrfun
# prepended because erefl is this pattern's standard proof and the pilot
# measured a Fail passing for an unresolved erefl without them.
LOWER_MATHCOMP = """From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finset reals boolp.
From infotheo Require Import fdist.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest.
"""

FULL_MATHCOMP = """From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
"""


# ============================================================== 1. Algebraic

emit(
    os.path.join(OUT_DIR, "pgl27_tableau_algebraic.v"),
    header(
        "pgl27_tableau_algebraic: the eight-card orbit instance at the "
        "Algebraic level",
        ["The Algebraic level of a row holds an algebra and nothing besides, "
         "and the proposition it carries is True. A reader shown only this "
         "file has been shown which group shuffles the deck, which scheme "
         "the dealer shares and which seats read, and no claim about a "
         "coalition, a run or a probability model. All seven published rows "
         "of this instance begin at that algebra, so the value below is the "
         "one point at which the exact, the word and the prior-indexed "
         "exact analyses agree.",
         "The algebra is pgl27_algebra of pgl27_exec.v and is not restated "
         "here: PGL(2,7) acts on the eight card positions, the orbit scheme "
         "deals one of the two orbit classes into those eight cards and "
         "carries its own encoding, reconstruction and privacy obligation, "
         "and the eight seats start at the eight card positions in order. "
         "Four is the threshold that algebra names, so every "
         "statement above this file that quantifies over a coalition "
         "quantifies over at most three of the eight seats. What this file adds is that algebra read as the first line "
         "of a program, which is what lets each level above it be named on "
         "its own."],
        [("pgl27_algebraic_start",
          "the eight-card orbit algebra as a program at Algebraic")],
        []),
    LOWER_MATHCOMP + """From pgg_smc Require Import pgg_tableau.

""" + SETTINGS + """
Local Open Scope ring_scope.
""",
    [("The algebra as the first line of a row", [
        doc("The eight-card orbit instance at the Algebraic level: the "
            "algebra alone, under True, the proposition that level carries. "
            "One run mode is built on this value, the dealer-dealt one, "
            "and pgl27_dealt_executableE is where the prefix all seven "
            "published rows continue from is identified with that mode. The "
            "three "
            "probability models the instance analyses part three levels "
            "above, so what this file fixes is shared by every row the "
            "instance publishes.")
        + "\nDefinition pgl27_algebraic_start : Tableau Algebraic :="
          "\n  tableau_start pgl27_algebra."])])


# ============================================================= 2. Executable

emit(
    os.path.join(OUT_DIR, "pgl27_tableau_executable.v"),
    header(
        "pgl27_tableau_executable: the eight-card orbit instance at the "
        "Executable level",
        ["The Executable level adjoins run-level data to the algebra: what "
         "the run argument is, who commits, what the dealer lays, what a "
         "seat observes after a shuffle, what value the run is meant to "
         "recover and how much interpreter fuel it is allowed. The "
         "proposition is still True, so a reader shown this file has been "
         "shown which run is about to be made, and no proof that it "
         "terminates or that it recovers the value its parameters name.",
         "The instance does not branch here. One run mode is named, the "
         "dealer-dealt one: the run argument is the orbit class the dealer "
         "holds, no party commits an input, the dealer lays the orbit "
         "scheme's canonical encoding of that class into eight cards, and "
         "the interpreter is given pgl27_fuel. The line continues "
         "pgl27_algebraic_start through the raw bind rather than through a "
         "keyword rule, because the rules dealt and supplied begin at a "
         "PGGAlgebraic and encoded at a Targeted over one, so the keyword "
         "surface has no form that continues a named value at Algebraic.",
         "The two identifications of the framework's static reading of a "
         "coalition with pgl27_view are statements about this parameter "
         "record and about no program value, and they are in "
         "instances/pgl27/pgl27_proximity.v beside the distance whose proof "
         "rewrites with them, so that the mathematics requires no tableau "
         "module."],
        [("pgl27_dealt_executable",
          "the dealer-dealt run's parameters as a program")],
        [("pgl27_dealt_executable_paramsE",
          "the dealt line builds the record pgl27_dealt_params names")]),
    LOWER_MATHCOMP + """From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import pgl27_tableau_algebraic.

""" + SETTINGS + """
Local Open Scope ring_scope.
""",
    [("The dealer-dealt run's parameters", [
        doc("The dealer-dealt mode at the Executable level: the run argument "
            "is the orbit class the dealer holds, no party commits an input, "
            "the dealer lays the orbit scheme's canonical encoding of that "
            "class, and the interpreter is given pgl27_fuel. Naming the "
            "parameters as a program is what lets the run facts of the level "
            "above be adjoined to a value rather than to a prefix spelled "
            "out again.")
        + "\nDefinition pgl27_dealt_executable : Tableau Executable :="
          "\n  pgl27_algebraic_start ;;; dealt_step of pgl27_fuel.",
        doc("The parameter record this line builds is the one "
            "pgl27_dealt_params names. The line writes a fuel and leaves "
            "dealt_step to build the record, so the equation is what lets a "
            "statement made at pgl27_dealt_params be read as a statement "
            "about this program.")
        + "\nLemma pgl27_dealt_executable_paramsE :"
          "\n  projT2 (tableau_at pgl27_dealt_executable) = pgl27_dealt_params."
          "\nProof. exact: erefl. Qed."])])


# =============================================================== 3. Observed

emit(
    os.path.join(OUT_DIR, "pgl27_tableau_observed.v"),
    header(
        "pgl27_tableau_observed: the eight-card orbit instance at the "
        "Observed level",
        ["The Observed level adjoins the three run facts to the run "
         "parameters, and it is the first level at which a row proves "
         "anything. What it carries is run correctness: the interpreter "
         "finishes within pgl27_fuel, each of the eight seats reaches an "
         "endpoint, and the endpoints decode to the orbit class the run was "
         "built to recover. Nothing about a coalition is proved at this "
         "level, at any coalition size.",
         "One run parameter record reaches this level and two values name "
         "it. pgl27_dealt is "
         "the one all seven published rows of the instance continue from, "
         "and it names its termination proof. pgl27_inline_dealt writes that "
         "proof a different way, and it is here because the difference it "
         "makes is a fact about the tree and not about the mathematics: an "
         "opaque termination lemma is convertible with nothing, so a prefix "
         "that builds its own obligation reaches a second observed "
         "execution, and every value typed against the first, the instance's "
         "three model families before anything else, would have to be built "
         "again over it. The checks file records the two terms the kernel "
         "refuses that make the fork visible.",
         "The ideal functionality sits here for the same reason. pgl27_F is "
         "typed over pgl27_observed, the execution this level reaches, and "
         "realises_expected is an equation between the value that "
         "execution names as the one to recover and the functionality's "
         "function. Neither "
         "mentions a coalition and neither mentions a probability model."],
        [("pgl27_dealt", "the prefix all seven rows share"),
         ("pgl27_inline_dealt",
          "the prefix with the termination reduction written inline"),
         ("pgl27_F", "the ideal functionality the run realises")],
        [("pgl27_dealt_executableE",
          "the prefix is its Executable value with the three run facts "
          "adjoined"),
         ("pgl27_inline_paramsE", "the inline prefix builds the same run"),
         ("pgl27_FE",
          "that functionality is the identity at three"),
         ("pgl27_realises_expected",
          "the value the run is meant to recover is that functionality's "
          "function")]),
    LOWER_MATHCOMP + """From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import pgl27_tableau_executable.

""" + SETTINGS + """
Local Open Scope ring_scope.
""",
    [("The prefix all seven rows share", [
        M("pgl27_dealt"),
        doc("The dealer-dealt program is its own Executable value with the "
            "three run facts adjoined. The program above writes the algebra "
            "and the fuel in one line, the Executable file names the "
            "parameters they build, and this equation is what keeps a reader "
            "from having to decide which of the two spellings a statement "
            "below is made at.")
        + "\nLemma pgl27_dealt_executableE :"
          "\n  (pgl27_dealt_executable"
          "\n     execute terminates by pgl27_dealt_terminates"
          "\n             endpoints by pgl27_dealt_endpoints"
          "\n             recon by pgl27_dealt_recon) = pgl27_dealt."
          "\nProof. exact: erefl. Qed."]),
     ("The same prefix through the literal reduction",
      [M("pgl27_inline_dealt"), M("pgl27_inline_paramsE")]),
     ("The ideal functionality",
      [M("pgl27_F"), M("pgl27_FE"), M("pgl27_realises_expected")])])


# ================================================================ 4. Sampled

emit(
    os.path.join(OUT_DIR, "pgl27_tableau_sampled.v"),
    header(
        "pgl27_tableau_sampled: the eight-card orbit instance at the "
        "Sampled level",
        ["The Sampled level adjoins a probability model to a run, and what "
         "it adds to run correctness is the identification of the two "
         "readings of a coalition: at every real field and every index of "
         "the family, the reader built from the interpreter's own endpoints "
         "is the one computed directly from the run argument and the cut. "
         "That "
         "identification is what turns a claim about the messages a run "
         "exchanges into a claim about a group action, and it is the last "
         "thing proved before an arm is named.",
         "Three families are named here, one per model a published row "
         "continues from, and all three sit over the one dealer-dealt run. "
         "The exact family draws the cut uniformly from PGL(2,7) at the "
         "uniform secret, and its index is the unit type. The word family "
         "draws the cut by evaluating a sampled two-hundred-letter generator "
         "word, and its index is a distribution on the booleans, the law of "
         "the dealt secret. The prior-indexed exact family draws the cut "
         "uniformly at that same law of the secret. The exact family's index "
         "is "
         "the unit type and the other two carry a law of the secret, so an "
         "index type tells the exact family from the prior-indexed exact "
         "family. That is a difference of families and not of models: both "
         "draw the uniform cut, and they differ in whether the law of the "
         "secret is fixed at the uniform one or carried as an index.",
         "pgl27_word_sampled is a name the instance already had, and the "
         "two rows over the word model are written from it. The other two "
         "values are named the same way so that a row over any of the three "
         "models can be continued from a name rather than from the prefix."],
        [("pgl27_exact_sampled",
          "the dealer-dealt run under the uniform cut at the uniform secret"),
         ("pgl27_word_sampled",
          "the word model named at Sampled, before any arm is chosen"),
         ("pgl27_prior_exact_sampled",
          "the dealer-dealt run under the uniform cut at every law of the "
          "secret")],
        []),
    LOWER_MATHCOMP + """From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import pgl27_tableau_observed.

""" + SETTINGS + """
Local Open Scope ring_scope.
""",
    [("The exact shuffle at the uniform secret", [
        doc("The dealer-dealt run under the exact shuffle, named at Sampled. "
            "The family is indexed by the unit type, so one member at each "
            "real field, and that member fixes the uniform law of the dealt "
            "secret. The cut it draws is already the uniform one on "
            "PGL(2,7), so a row over this model compares no finite walk with "
            "an ideal.")
        + "\nDefinition pgl27_exact_sampled : Tableau Sampled :="
          "\n  pgl27_dealt sample pgl27_exact_family."]),
     ("The word model as a branch point", [M("pgl27_word_sampled")]),
     ("The exact shuffle at every law of the secret", [
        doc("The dealer-dealt run under the exact shuffle read at every law "
            "of the dealt secret, named at Sampled. Its family is indexed by "
            "a distribution on the booleans, the same index the word family "
            "carries, which is what lets a proximity certificate read the "
            "two models at one index.")
        + "\nDefinition pgl27_prior_exact_sampled : Tableau Sampled :="
          "\n  pgl27_dealt sample pgl27_prior_exact_family."])])


# ======================================================= 5. AnalysisBridged

BRIDGED_PRE = """From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import pgl27_tableau_observed.
From pgg_smc Require Import pgl27_tableau_sampled.
From pgg_smc Require Import pgl27_proximity.

""" + SETTINGS + """
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.
"""

emit(
    os.path.join(OUT_DIR, "pgl27_tableau_analysis_bridged.v"),
    header(
        "pgl27_tableau_analysis_bridged: the eight-card orbit instance at "
        "the AnalysisBridged level",
        ["The AnalysisBridged level adjoins one security arm to a Sampled "
         "value, and the proposition it carries is that arm's own, on top of "
         "run correctness and of the identification of the two readings of a "
         "coalition. A publish terminal then turns the value into a "
         "PublishedRow. Every payload this instance owes an arm is here, "
         "every row it publishes is here, and every statement whose subject "
         "is a payload or a row is here.",
         "Three arms are used over the one dealer-dealt run. The exact arm "
         "takes an ExactWitness, whose one field is independence of a "
         "coalition's reading from the dealt secret; at the uniform cut this "
         "is three-transitivity of PGL(2,7) on the eight points read as a "
         "privacy statement, and it is exact, with no number in it. The "
         "input-indistinguishability arm takes a certificate comparing the "
         "readings of two dealt secrets under one model. The proximity arm "
         "takes a certificate comparing one model with an ideal one at the "
         "same index.",
         "Two numbers, and both are read off the one walk bound. "
         "pgl27_word_mixing bounds the distance between the "
         "two-hundred-letter walk and the uniform cut on the group by 2^-40, "
         "and pgl27_word_marginal_bound carries that number. The "
         "input-indistinguishability certificate crosses from the walk to "
         "the ideal cut once for each of the two dealt secrets it compares, "
         "so its cert_eps is that number added to itself, 2^-39. The proximity certificate compares one law "
         "with one law and carries the number itself, 2^-40, and the "
         "proximity row concludes at 2^-39, the constant the other row over "
         "the same model publishes, so the terminal's obligation is met "
         "strictly. Each of these numbers bounds a sum of absolute "
         "differences, twice a total variation distance, so a "
         "distinguisher's advantage against a row concluded at 2^-39 is at "
         "most 2^-40. Four is the threshold the derived profile "
         "declares, so every statement here that quantifies over a "
         "coalition quantifies over at most three of the eight seats, each "
         "seat reading the card at its own position, and "
         "pgl27_exact_leak4 records that four already leak.",
         "Seven rows are published, and three of them publish the "
         "manifest's own. pgl27_row_exact_rowE, pgl27_row_word_rowE and "
         "pgl27_row_prior_exact_rowE discharge pgl27_row_exact, "
         "pgl27_row_word and pgl27_row_prior_exact of "
         "pgg_analysis_manifest.v by conversion, and those three are the "
         "AnalysisPathRows the manifest carries for this instance. The "
         "other four are the word row concluded at 2^-39 in three "
         "spellings, through the surface, through the raw bind and from the "
         "named Sampled value, and the proximity row, which publishes the "
         "same manifest row under a different arm. An AnalysisPathRow holds "
         "descriptive metadata and no Prop, so one manifest row carrying an "
         "input-indistinguishability row and a proximity row says nothing "
         "about either claim. The manifest carries no fourth row over this "
         "instance and publishes none of the three by a route this "
         "development's programs do not take.",
         ("lit", [
             "Where each published row's chain is, one entry per row.",
             "pgl27_row_exact_tableau, under The two row programs: "
             "pgl27_row_exact_sampledE, pgl27_row_exact_rowE, "
             "pgl27_row_exact_armE, and the readings "
             "pgl27_exec_exact_view_indep_restated and "
             "pgl27_exact_view_secrecy.",
             "pgl27_row_word_tableau, under the same banner: "
             "pgl27_row_word_sampledE, pgl27_row_word_rowE, "
             "pgl27_row_word_armE, and the reading "
             "pgl27_word_view_indistinguishability_restated.",
             "pgl27_row_word39, under The word row concluded at 2^-39: "
             "pgl27_row_word39_armE, and no reading of its own.",
             "pgl27_row_word39_bind, under the same banner: tied to the "
             "row above by pgl27_row_word39_bindE.",
             "pgl27_row_word_branch39, under The same row from the named "
             "word model: written from pgl27_word_sampled, so no "
             "_sampledE, and pgl27_row_word_branch39_armE.",
             "pgl27_row_prior_exact_tableau, under The ideal: the exact "
             "shuffle at every prior: pgl27_row_prior_exact_sampledE, "
             "pgl27_row_prior_exact_rowE, pgl27_row_prior_exact_armE.",
             "pgl27_row_word_proximity, under One model, two claims, two "
             "rows: written from pgl27_word_sampled, so no _sampledE, "
             "pgl27_row_word_proximity_rowE, "
             "pgl27_row_word_proximity_armE, and the reading "
             "pgl27_word_view_proximity.",
         ]),
         "An importer of this instance names one module per kind of name. "
         "The algebraic file declares the Algebraic value; the executable "
         "file the Executable value and the parameter equation; the "
         "observed file the "
         "two prefixes, the inline fork's parameter equation and the ideal "
         "functionality; the sampled file the three named models; this file "
         "the payloads, the rows, the row and arm equations, the bridges, "
         "the restated theorems and the two arm statements; and the checks "
         "file the recorded rejections and the comparison of the two word "
         "rows' arms. No file of the six uses Require Export.",
         "This file requires instances/pgl27/pgl27_proximity.v, which holds "
         "the reading and the distance mathematics the certificates are "
         "built from: the two identifications of the framework's static "
         "reading of a coalition with pgl27_view, the dealt secret on the "
         "word sample space, the distance between the two models' joint "
         "laws, and the two arithmetic facts about 2^-40 the conclude "
         "obligation is proved with."],
        [("pgl27_exact_witness",
          "the exact arm's witness at every field and index"),
         ("pgl27_word_cert",
          "the input-indistinguishability arm's certificate"),
         ("pgl27_row_exact_tableau", "the exact row as a program"),
         ("pgl27_row_word_tableau", "the word row as a program"),
         ("pgl27_reprice39", "the name 2^-39 for the word row's bound"),
         ("pgl27_row_word39", "the word row concluded at that number"),
         ("pgl27_row_word39_bind",
          "the same row written through the bind"),
         ("pgl27_row_word_branch39",
          "the continuation of the named word model concluded at 2^-39"),
         ("pgl27_reprice41", "the name 2^-41 for a bound"),
         ("pgl27_word_target", "the word row's published statement"),
         ("pgl27_exact_target", "the exact row's published statement"),
         ("pgl27_word_restated",
          "the word row through the restate terminal"),
         ("pgl27_exact_restated",
          "the exact row through the restate terminal"),
         ("pgl27_word_same_statement",
          "the published word statement and the word row's restatement "
          "inhabit one type"),
         ("pgl27_exact_same_statement",
          "the published exact statement and the exact row's restatement "
          "inhabit one type"),
         ("pgl27_prior_exact_witness",
          "the exact arm's witness at the prior-indexed exact shuffle"),
         ("pgl27_row_prior_exact_tableau",
          "that shuffle published as its own program"),
         ("pgl27_word_proximity_cert",
          "the word model's proximity certificate"),
         ("pgl27_row_word_proximity",
          "the word row as a program at the proximity arm, concluded "
          "at 2^-39")],
        [("pgl27_exact_viewE",
          "the framework's seat reader is the instance's, with the secret "
          "left in the sample point"),
         ("pgl27_exact_leak4",
          "four seats of this instance leak the secret"),
         ("pgl27_word_view_const",
          "below the four-seat threshold, two secrets give one reading of "
          "the ideal cut"),
         ("pgl27_row_exact_sampledE",
          "the exact row continues the named exact model"),
         ("pgl27_row_word_sampledE",
          "the word row continues the named word model"),
         ("pgl27_row_word_certE",
          "the five written clauses are pgl27_word_cert"),
         ("pgl27_row_exact_rowE",
          "the exact program publishes the manifest's row"),
         ("pgl27_row_word_rowE",
          "the word program publishes the manifest's row"),
         ("pgl27_row_exact_armE", "the exact row carries the exact arm"),
         ("pgl27_row_word_armE",
          "the word row carries the input-indistinguishability arm"),
         ("pgl27_row_word39_bindE",
          "the surface and the bind build one term"),
         ("pgl27_row_word39_armE",
          "the concluded row carries that same arm"),
         ("pgl27_row_word_branch39_armE",
          "the branch row carries that arm as well"),
         ("pgl27_word_reprice41_false",
          "the terminal's obligation at 2^-41 is false"),
         ("pgl27_word_bridge",
          "the word row's proposition gives its published statement"),
         ("pgl27_exact_bridge",
          "the exact row's proposition gives its published statement"),
         ("pgl27_word_view_indistinguishability_restated",
          "the word statement, from the word row alone"),
         ("pgl27_exec_exact_view_indep_restated",
          "the exact statement, from the exact row alone"),
         ("pgl27_exact_view_secrecy",
          "below the four-seat threshold, the exact arm's four conjuncts at "
          "this instance"),
         ("pgl27_prior_viewE",
          "the framework's reading of a coalition at the prior-indexed "
          "exact shuffle is the instance's own reading pgl27_view"),
         ("pgl27_row_prior_exact_sampledE",
          "the prior-indexed exact row continues the named model"),
         ("pgl27_row_prior_exact_armE",
          "the ideal row carries the exact arm"),
         ("pgl27_row_prior_exact_rowE",
          "the ideal program publishes pgl27_row_prior_exact"),
         ("pgl27_word_proximity_cert_idealE",
          "the certificate's ideal is the ideal row's model, and the port "
          "built from its witness is that row's port"),
         ("pgl27_word_proximity_cert_epsE",
          "the certificate's number is 2^-40"),
         ("pgl27_word_proximity_eps_halfE",
          "the input-indistinguishability certificate's number is twice the "
          "proximity certificate's"),
         ("pgl27_word_proximity_le39",
          "the certificate's number is at most 2^-39"),
         ("pgl27_word_proximity_cert_eps_lt2",
          "that number is below the bound two var_dist_le2 gives"),
         ("pgl27_row_word_proximity_rowE",
          "the proximity row publishes pgl27_row_word"),
         ("pgl27_row_word_proximity_armE",
          "that row carries the proximity arm"),
         ("pgl27_row_word_families_sampledE",
          "both rows over the word model read their model family off the "
          "one named Sampled value"),
         ("pgl27_row_word_obs_sampledE",
          "both rows read their observed execution off that same value"),
         ("pgl27_word_view_proximity",
          "below the four-seat threshold, the proximity row's security "
          "statement, at 2^-39")]),
    BRIDGED_PRE,
    [("The exact family's witness",
      [M("pgl27_exact_viewE"), M("pgl27_exact_witness"),
       M("pgl27_exact_leak4")]),
     ("The word family's certificate",
      [M("pgl27_word_view_const"), M("pgl27_word_cert")]),
     ("The two row programs", [
         M("pgl27_row_exact_tableau"),
         doc("The exact row continues the named exact model. The program "
             "above writes the sample step and the certify statement in one "
             "term and the Sampled file names the value between them, so "
             "this equation is what lets a statement made at "
             "pgl27_exact_sampled be read as a statement about the row.")
         + "\nLemma pgl27_row_exact_sampledE :"
           "\n  (pgl27_exact_sampled"
           "\n     certify ExactIndependence pgl27_exact_witness"
           "\n             leaks at 4 by pgl27_exact_leak4"
           "\n     |> publish StaticExecutedOnly BaselineClassicalOnly)"
           "\n  = pgl27_row_exact_tableau."
           "\nProof. exact: erefl. Qed.",
         M("pgl27_row_word_tableau"),
         doc("The word row continues the named word model, with the "
             "certificate written as one record. The five clauses of the "
             "program above and the record are one term by "
             "pgl27_row_word_certE, so this equation carries the naming of "
             "the model and nothing else.")
         + "\nLemma pgl27_row_word_sampledE :"
           "\n  (pgl27_word_sampled"
           "\n     certify InputIndistinguishability pgl27_word_cert"
           "\n     |> publish IdealFinite BaselineClassicalOnly)"
           "\n  = pgl27_row_word_tableau."
           "\nProof. exact: erefl. Qed.",
         M("pgl27_row_word_certE"), M("pgl27_row_exact_rowE"),
         M("pgl27_row_word_rowE"), M("pgl27_row_exact_armE"),
         M("pgl27_row_word_armE")]),
     ("The word row concluded at 2^-39",
      [M("pgl27_reprice39"), M("pgl27_row_word39"),
       M("pgl27_row_word39_bind"), M("pgl27_row_word39_bindE"),
       M("pgl27_row_word39_armE")]),
     ("The same row from the named word model",
      [M("pgl27_row_word_branch39"), M("pgl27_row_word_branch39_armE")]),
     ("A number below the proved one",
      [M("pgl27_reprice41"), M("pgl27_word_reprice41_false")]),
     ("The word statement, from the word row",
      [M("pgl27_word_target"), M("pgl27_word_bridge"),
       M("pgl27_word_restated"),
       M("pgl27_word_view_indistinguishability_restated")]),
     ("The exact statement, from the exact row",
      [M("pgl27_exact_target"), M("pgl27_exact_bridge"),
       M("pgl27_exact_restated"),
       M("pgl27_exec_exact_view_indep_restated")]),
     ("The exact arm's four conjuncts at this instance",
      [M("pgl27_exact_view_secrecy")]),
     ("Each published statement and its restatement are one statement",
      [M("pgl27_word_same_statement"), M("pgl27_exact_same_statement")]),
     ("The ideal: the exact shuffle at every prior", [
         M("pgl27_prior_viewE"), M("pgl27_prior_exact_witness"),
         M("pgl27_row_prior_exact_tableau"),
         doc("The prior-indexed exact row continues the named prior-indexed "
             "model, so the ideal a proximity certificate measures against "
             "and the row that publishes it are read off one name.")
         + "\nLemma pgl27_row_prior_exact_sampledE :"
           "\n  (pgl27_prior_exact_sampled"
           "\n     certify ExactIndependence pgl27_prior_exact_witness"
           "\n     |> publish StaticExecutedOnly BaselineClassicalOnly)"
           "\n  = pgl27_row_prior_exact_tableau."
           "\nProof. exact: erefl. Qed.",
         M("pgl27_row_prior_exact_armE"), M("pgl27_row_prior_exact_rowE")]),
     ("The proximity certificate, and its ideal",
      [sub("pgl27_word_proximity_cert", "and the distance above",
           "and the distance pgl27_word_proximity_close of "
           "pgl27_proximity.v"),
       M("pgl27_word_proximity_cert_idealE")]),
     ("The number",
      [M("pgl27_word_proximity_cert_epsE"),
       M("pgl27_word_proximity_eps_halfE"), M("pgl27_word_proximity_le39"),
       M("pgl27_word_proximity_cert_eps_lt2")]),
     ("One model, two claims, two rows",
      [M("pgl27_row_word_proximity"),
       sub("pgl27_row_word_proximity_rowE",
           "as pgl27_row_word_rowE of pgl27_rows.v says of the word program",
           "as pgl27_row_word_rowE says of the word program"),
       M("pgl27_row_word_proximity_armE"),
       M("pgl27_row_word_families_sampledE"),
       M("pgl27_row_word_obs_sampledE")]),
     ("What the proximity row states at this instance",
      [M("pgl27_word_view_proximity")])])


# ================================================================= 6. Checks

emit(
    os.path.join(OUT_DIR, "pgl27_tableau_checks.v"),
    header(
        "pgl27_tableau_checks: the terms the kernel refuses at the "
        "eight-card orbit instance",
        ["Each entry below is one written term that the kernel rejects, "
         "recorded so that the rejection is compiled rather than described. "
         "A recorded rejection says what it says about the one term written "
         "under it and about no other term: it fixes a spelling that does "
         "not typecheck, and states no general impossibility.",
         "Seven groups. Two are about what a clause records: the coalition "
         "size written in a leaks clause is checked against the proof it "
         "names, and the arm a row carries is the one its certify statement "
         "wrote, so recording the word row at the exact arm is refused. "
         "Beside the second sits the one positive statement of this file, "
         "that the two rows over the word model carry different arms, which "
         "is a comparison of two rows rather than a statement about one; the "
         "sixth group turns the same point the other way, refusing to read "
         "the exact arm's four conjuncts off the word row.",
         "One group is the fork the literal reduction makes: a prefix that "
         "builds its own termination obligation is not the term pgl27_dealt "
         "is, and the instance's own model family, typed against "
         "pgl27_observed, is refused over the forked execution. Two are "
         "about the terminal: a conclude payload with no index binder is "
         "refused in both spellings of the row, and the row at 2^-41 is "
         "refused where its terminal is written, the certificate's own "
         "number being twice 2^-40.",
         "The last group is what a proximity certificate may name as its "
         "ideal, and its three rejections have two causes. Two are refused "
         "at the index type, which separates the exact family indexed by "
         "the unit type from the two families indexed by a law of the dealt "
         "secret, and not the exact shuffle from the word walk. The third "
         "is well typed at its index and refused at its distance field, "
         "whose proof relates the word model at one law of the secret to "
         "the exact model at that same law and not to the exact model at "
         "the uniform one. What refutes that field, rather than refusing a "
         "written term, is pgl27_word_uniform_ideal_close_false of "
         "pgl27_proximity.v.",
         "One lemma of this file shares its name with the rejection "
         "recorded above it, and the order is what lets both compile. Rocq "
         "checks that a name is free before it elaborates a body, so a file "
         "holding the lemma first would reject the term for an occupied "
         "name and not for the arm the term asserts."],
        [],
        [("pgl27_row_word_arm_neq",
          "the two rows over the word model carry different arms")]),
    BRIDGED_PRE.replace(
        "From pgg_smc Require Import pgl27_tableau_sampled.\n", "").replace(
        "From pgg_smc Require Import pgl27_proximity.",
        "From pgg_smc Require Import pgl27_proximity.\n"
        "From pgg_smc Require Import pgl27_tableau_analysis_bridged."),
    [("The number written in a leaks clause", [M("pgl27_row_exact_leak7")]),
     ("The arm a row carries",
      [ROWS["pgl27_row_word_arm_neq"], PROX["pgl27_row_word_arm_neq"]]),
     ("The fork the literal reduction makes",
      [M("pgl27_inline_neq"), M("pgl27_inline_reuse")]),
     ("The terminal's index binder",
      [M("pgl27_row_word39_unindexed"),
       M("pgl27_row_word39_unindexed_bind")]),
     ("A number below the proved one", [M("pgl27_row_word41")]),
     ("The arms are different statements",
      [M("pgl27_word_arm_is_not_exact")]),
     ("What a certificate may name as its ideal",
      [M("pgl27_word_proximity_cert_unit_ideal")
       .split("\nSection pgl27_word_uniform_ideal.")[0].rstrip(),
       sub("pgl27_word_proximity_cert_uniform_ideal",
           "pgl27_word_uniform_ideal_close_false above, at the point-mass "
           "prior",
           "pgl27_word_uniform_ideal_close_false of pgl27_proximity.v, at "
           "the point-mass prior"),
       M("pgl27_cross_model_proximity")])])


# ================================================== 7. reduced pgl27_proximity

emit(
    os.path.join(OUT_INST, "pgl27_proximity.v"),
    header(
        "pgl27_proximity: the instance's reading of a coalition, and the "
        "distances between its two laws of the cut",
        ["The eight-card orbit instance runs one execution under two laws of "
         "the cut: the exact shuffle, which draws it uniformly from "
         "PGL(2,7), and the two-hundred-letter word walk, which draws it by "
         "evaluating a sampled generator word. This file holds the "
         "mathematics that separates the two, with no program and no "
         "published row in it.",
         "One distance is the certificate field of the proximity arm: below "
         "the four-seat threshold, the joint law of a coalition's reading "
         "with the dealt secret under the walk is within 2^-40 of the same "
         "joint law under the uniform cut at the same law of the secret. The "
         "number is the walk's single-card marginal number, and it rests on "
         "pgl27_word_mixing, the bound by that same number on the distance "
         "between the walk and the uniform cut on the group.",
         "Every number below bounds a sum of absolute differences, which is "
         "twice the total variation distance of the literature, so a bound "
         "of 2^-40 here is a distinguishing advantage of at most 2^-41 "
         "wherever it is used.",
         "The other distance runs the other way. A proximity certificate "
         "compares two models at one index, so the two have to be read at "
         "one law of the dealt secret. pgl27_prior_exact_family of "
         "pgl27_models.v carries that law as its index, where "
         "pgl27_exact_family is indexed by the unit type and its one member "
         "fixes the uniform law. An ideal taken from the unit-indexed family "
         "can therefore only be the ideal of a word model at the uniform "
         "law, and the distance of a word model at another law to it is at "
         "least the distance between the two laws of the secret, which "
         "pgl27_word_uniform_ideal_close_false exhibits at a point mass.",
         "The identification of the framework's static reading of a "
         "coalition with pgl27_view opens the file, because the distance "
         "proof rewrites with it twice and because its subject is the run "
         "parameter record and no program value. The two sides are not the "
         "same term, the framework reading seat i at tnth (pi_starts _) i "
         "and the instance at i, and they agree because this instance's "
         "seats start at the eight card positions in order.",
         "The certificate itself, the row it publishes and the statements "
         "about them are in instances/pgl27/tableau/, whose AnalysisBridged "
         "file requires this one. This file requires no tableau module, so "
         "the arrow between the mathematics and the tableau runs one way, "
         "upward."],
        [("pgl27_word_secret",
          "the dealt secret on the word sample space")],
        [("pgl27_static_obsE",
          "the framework's seat reader is the instance's"),
         ("pgl27_static_obs_funE",
          "the same with the cut left free"),
         ("pgl27_word_proximity_close",
          "below the four-seat threshold, the two models' joint laws of "
          "reading and secret are within 2^-40"),
         ("pgl27_pow2_40_ge1", "two to the fortieth is at least one"),
         ("pgl27_pow2_40_gt0", "two to the fortieth is positive"),
         ("pgl27_word_uniform_ideal_close_false",
          "the distance field is false at every coalition, with the "
          "uniform-secret exact model as the ideal of the word model at a "
          "point-mass prior")]),
    """From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.

""" + SETTINGS + """
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
""",
    [("The instance-side reading of a coalition",
      [M("pgl27_static_obsE"), M("pgl27_static_obs_funE")]),
     ("The dealt secret on the word sample space",
      [M("pgl27_word_secret")]),
     ("The distance between the two models' joint laws",
      [M("pgl27_word_proximity_close")]),
     ("The number", [M("pgl27_pow2_40_ge1"), M("pgl27_pow2_40_gt0")]),
     ("What refutes a distance bound",
      ["Section pgl27_word_uniform_ideal.\nVariable R : realType.\n\n"
       "Let P1 : R.-fdist bool := fdist1 true.",
       M("pgl27_word_uniform_ideal_close_false")])])

print("seven files written")
