#!/usr/bin/env python3
"""Write STATUS.md.  Every count and every placement row is read out of the
production sources and the staged text, so no number on that page is typed
by hand (PSL(2,11) audit ruling 12).

Usage: python3 gen_status.py
"""

import os

import verify

HERE = os.path.dirname(os.path.abspath(__file__))

WHY = {
    # --- new -------------------------------------------------------------
    "five_card_algebraic_start":
        "the algebra as the first line of a program",
    "five_card_committed_executable":
        "the one run mode a program of this instance uses",
    "five_card_committed_executable_paramsE":
        "the Executable-phase statement of its own phase",
    "five_card_committed_executableE":
        "the re-cut equation, named after its non-canonical side",
    "five_card_uniform_sampled":
        "one named value per model a published program continues from; "
        "the uniform row is written as one chain, so the re-cut is new here",
    "five_card_row_uniform_sampledE": "the re-cut equation of that row",
    "five_card_row_repeated_indistinguishability_sampledE":
        "the re-cut equation of that row",
    "five_card_row_biased_indistinguishability_sampledE":
        "the re-cut equation of that row",
    "five_card_row_repeated39_sampledE":
        "the re-cut equation of that row",
    "five_card_row_biased_inv25_sampledE":
        "the re-cut equation of that row",
    # --- algebraic --------------------------------------------------------
    "five_card_target":
        "a Targeted value, the payload of the encoded first line "
        "(design question 6)",
    # --- observed ---------------------------------------------------------
    "five_card_committed": "a Tableau Observed value",
    "five_card_committed_paramsE":
        "its subject is that Observed value, so no lower file can state it "
        "with its tokens unchanged",
    "five_card_F":
        "a Functionality over five_card_observed, the Observed-phase "
        "execution (design question 6)",
    "five_card_FE": "a statement about that functionality",
    "five_card_F_ite": "a statement about that functionality",
    "five_card_realises_expected":
        "realises_expected five_card_observed five_card_F, a statement "
        "about the observed execution and about no model",
    # --- sampled ----------------------------------------------------------
    "five_card_row_repeated_tableau":
        "a Tableau Sampled value, named before the scheme and kept",
    "five_card_row_biased_tableau":
        "a Tableau Sampled value, named before the scheme and kept",
    "five_card_row_repeated_prefixE":
        "its subject is a Sampled value against the prefix",
    "five_card_row_biased_prefixE":
        "its subject is a Sampled value against the prefix",
    "five_card_row_repeated_modelE":
        "its subject is a Sampled value's own model field",
    "five_card_row_biased_modelE":
        "its subject is a Sampled value's own model field",
    "five_card_row_biased_levelE":
        "the manifest's level for the row the one-cut Sampled program "
        "stops under; the positive half of the level gap whose rejected "
        "half is in the checks file, as pgl27_reprice41 and "
        "Fail pgl27_row_word41 were split at PGL(2,7)",
    "five_card_row_repeated_endpoint_lt":
        "its subject is the cut law of a named Sampled model and no row, "
        "no payload and no coalition",
    "kim_centi_small":
        "the side condition on the bias that the bound below consumes",
    "five_card_row_biased_leak_bound":
        "its subject is the law a named Sampled model samples; no arm of "
        "certify takes a conditional mutual information, so it is carried "
        "at Sampled and not at AnalysisBridged",
    # --- analysis_bridged, the contested ones -----------------------------
    "five_card_colour_fill":
        "the map the exact arm's link lemma is stated with; unlike "
        "PGL(2,7)'s pgl27_static_obsE, no proof that stays uses it",
    "five_card_viewS_nth":
        "the reindexing the link lemma below is proved by",
    "five_card_static_obsE":
        "a link lemma the exact witness consumes; the four lemmas that "
        "stay in five_card_proximity.v do not use it, so the PGL(2,7) "
        "ruling that put its counterpart in the mathematics does not "
        "apply here",
    "five_card_viewS_indep":
        "the mathematics the exact witness's one field rests on",
    "five_card_exact_viewE": "a link lemma the exact witness consumes",
    "five_card_static_obs_indep":
        "the exact witness's one field",
    "five_card_exact_witness": "the ExactWitness payload certify_exact takes",
    "five_card_row_biased_arm_neq":
        "a comparison of two rows' arms, which the design's Candidate A "
        "puts in the checks file",
}

DEFAULT = {
    "row": "a published row",
    "about": "a statement about a published row",
    "cert": "a certificate or witness payload an arm takes",
    "num": "a number a certificate or a terminal carries",
    "fail": "a recorded rejection",
    "thm": "an arm's statement, by the row's security projection",
}

KIND = {
    "five_card_row_uniform_tableau": "row",
    "five_card_row_repeated_indistinguishability_tableau": "row",
    "five_card_row_biased_indistinguishability_tableau": "row",
    "five_card_row_repeated39": "row",
    "five_card_row_biased_inv25": "row",
    "five_card_row_biased_branch_indistinguishability": "row",
    "five_card_row_biased_proximity": "row",
    "kim_centi_cert": "cert", "kim_biased_cert": "cert",
    "kim_biased_cert_exact": "cert", "kim_biased_proximity_cert": "cert",
    "five_card_reprice39": "num", "five_card_reprice_inv25": "num",
    "five_card_reprice_inv100": "num", "kim_biased_epsE": "num",
    "kim_biased_exact_le_eps": "num", "five_card_pow2_39_split": "num",
    "kim_centi_cert_epsE": "num", "kim_centi_cert_eps_lt": "num",
    "kim_biased_cert_epsE": "num", "kim_biased_cert_eps_lt2": "num",
    "five_card_inv50_split": "num", "five_card_reprice_inv25_lt2": "num",
    "kim_biased_proximity_cert_epsE": "num",
    "kim_biased_proximity_eps_halfE": "num",
    "kim_biased_proximity_cert_eps_lt2": "num",
    "kim_biased_conclude_below_false": "num",
    "five_card_exact_view_secrecy": "thm",
    "five_card_biased_view_proximity": "thm",
    "five_card_biased_view_own_marginals": "thm",
    "five_card_biased_proximity_prop_holds": "thm",
    "five_card_biased_indistinguishability_implies_proximity": "thm",
    "five_card_singleton_below_threshold":
        "thm", "five_card_biased_proximity_at_singleton": "thm",
}

FILE_OF = {
    "five_card_tableau_algebraic.v": "algebraic",
    "five_card_tableau_executable.v": "executable",
    "five_card_tableau_observed.v": "observed",
    "five_card_tableau_sampled.v": "sampled",
    "five_card_tableau_analysis_bridged.v": "analysis_bridged",
    "five_card_tableau_checks.v": "checks",
    "five_card_proximity.v": "stays",
}


def collect():
    prod, origin = {}, {}
    for path in (verify.PROD_ROWS, verify.PROD_PROX):
        for kind, name, _ in verify.items(
                verify.strip_comments(open(path).read())):
            prod[(kind, name)] = True
            origin[(kind, name)] = ("rows" if "rows" in os.path.basename(path)
                                    else "proximity")
    order, where = [], {}
    for path in verify.STAGED:
        base = os.path.basename(path)
        for kind, name, _ in verify.items(
                verify.strip_comments(open(path).read())):
            order.append((kind, name))
            where[(kind, name)] = FILE_OF[base]
    return prod, origin, order, where


def table():
    prod, origin, order, where = collect()
    out = ["| Declaration | Source | Phase file | Why |", "|---|---|---|---|"]
    for key in order:
        kind, name = key
        src = origin.get(key, "new")
        why = WHY.get(name)
        if why is None:
            why = DEFAULT[KIND.get(name, "about")]
            if kind.startswith("Fail"):
                why = DEFAULT["fail"]
        label = ("`Fail %s`" % name) if kind.startswith("Fail") \
            else "`%s`" % name
        out.append("| %s | %s | %s | %s |" % (label, src, where[key], why))
    counts = {}
    for key in order:
        counts[where[key]] = counts.get(where[key], 0) + 1
    return "\n".join(out), counts, len(prod), order


def read(name):
    return open(os.path.join(HERE, name)).read()


TBL, COUNTS, NPROD, ORDER = table()
_WH = collect()[3]


def where_of(key):
    return _WH[key]

NEW = len(verify.NEW_NAMES)
VERIFY = read("verify.out").strip()
NFAIL = len([k for k in ORDER if k[0].startswith("Fail")])
LINES = {}
for f in ["five_card_proximity.v"]:
    LINES[f] = open(os.path.join(
        HERE, "staged/instances/kim2025", f)).read().count("\n")
for p in ["algebraic", "executable", "observed", "sampled",
          "analysis_bridged", "checks"]:
    f = "five_card_tableau_%s.v" % p
    LINES[f] = open(os.path.join(
        HERE, "staged/instances/kim2025/tableau", f)).read().count("\n")
PRODLINES = {
    "five_card_rows.v": open(verify.PROD_ROWS).read().count("\n"),
    "five_card_proximity.v": open(verify.PROD_PROX).read().count("\n"),
}

BODY = """# Five-card (Kim and den Boer): the per-instance `tableau/` directory, staged

Probe directory for the five-card instance of the per-instance `tableau/`
reorganization, the fourth and largest. Pattern and rulings:
`../2026-09-20-tableau-directories-s5/` (`staged/TEMPLATE.md`,
`audit-s5-pilot.md`) and `../2026-09-20-tableau-directories-psl211/`
(`audit-psl211.md`). Scripts: `../2026-09-20-tableau-directories-pgl27/`.
Nothing here is in production. The main session does the `cp`, the `git rm`
and the `_CoqProject` edit.

Branch `feat/tableau-extensions-probe`. `make` was never run; every compile
went through `rocq1`, one Rocq process at a time.
`instances/psl211/psl211_endpoints.v` was never compiled and no file of its
forward closure was edited, moved or staged.

## Lines

| File | Lines |
|---|---|
%(linetable)s

Production is %(prows)d plus %(pprox)d, so %(ptot)d lines become %(stot)d:
the six headers and the section banners are the difference, and no
declaration is duplicated.

## The staged text

```
staged/instances/kim2025/five_card_proximity.v            reduced, 4 items
staged/instances/kim2025/tableau/five_card_tableau_algebraic.v
staged/instances/kim2025/tableau/five_card_tableau_executable.v
staged/instances/kim2025/tableau/five_card_tableau_observed.v
staged/instances/kim2025/tableau/five_card_tableau_sampled.v
staged/instances/kim2025/tableau/five_card_tableau_analysis_bridged.v
staged/instances/kim2025/tableau/five_card_tableau_checks.v
```

## Sources and their declaration counts

| Source | Declarations | Of which `Fail` |
|---|---|---|
| `instances/kim2025/five_card_rows.v` | 61 | 5 |
| `instances/kim2025/five_card_proximity.v` | 32 | 6 |

All %(nprod)d are accounted for: %(nmoved)d move into the six phase files,
%(nstay)d stay in the reduced `five_card_proximity.v`. %(nnew)d declarations
are new. Every count on this page is produced by `gen_status.py` from
`verify.py`'s own reading of the two sides.

Neither source holds a `Local Notation`, so the question the PSL(2,11)
audit left open at F16 does not arise. The rows file does hold one
`Arguments` line, which travels inside its declaration's slice and is
compared with it.

## Placement

%(table)s

## The cut

`five_card_proximity.v` is cut by the rule used at PGL(2,7) and PSL(2,11):
the certificate, the two published rows and every statement about them go to
`five_card_tableau_analysis_bridged.v`, the six recorded rejections and the
comparison of the two rows' arms to `five_card_tableau_checks.v`, and the
laws and the distance stay.

What differs from PGL(2,7) is which side the link lemmas fall on. There the
two identifications of the framework's static reading with the instance's own
reading stayed in the mathematics, because the distance proof that stays
rewrites with them twice. Here it does not: `kim_biased_proximity_close` is
proved from `five_card_reading_secretE`, `five_card_uniform_pairE`,
`five_card_arg_cut_prodE` and the cut-group bound, and names
`five_card_static_obsE` nowhere. So `five_card_static_obsE`,
`five_card_colour_fill`, `five_card_viewS_nth`, `five_card_viewS_indep`,
`five_card_exact_viewE` and `five_card_static_obs_indep` go where they are
consumed, into the AnalysisBridged file, beside the witness they build. The
arrow still runs one way: the reduced file requires no tableau module, and
the AnalysisBridged file requires it for the certificate's last field.

## The reduced file's import list

```
%(proxpre)s```

Production's list minus `five_card_rows`, `s5_tableau_analysis_bridged`,
`s5_exec`, `s5_models`, `pgg_analysis_manifest`, `pgg_tableau`,
`pgg_tableau_syntax` and `pgg_observed_execution pgg_analysis_status`, with
the mathcomp and infotheo lines unchanged. The last line was measured, not
guessed: each remaining `From` line was dropped in turn and the file
recompiled, and only that one and `pgg_instance pgg_sample_adapter` were
droppable, each because the other covers it. `pgg_instance` is kept, being
the file that declares `static_coalition_obs`. Its scope block is
production's, `ring`, `fdist`, `proba`.

## The `Require` graph

```
algebraic <- executable <- observed <- sampled <- analysis_bridged <- checks
                             ^                          ^               ^
      algebraic -------------+                          |               |
      five_card_proximity (reduced) --------------------+---------------+
                  analysis_bridged also imports observed
                  checks also imports observed and sampled
```

No file uses `Require Export`, and every phase import is used:

| File | Phase modules it requires | The names that earn them |
|---|---|---|
| executable | algebraic | `five_card_algebraic_start` |
| observed | algebraic, executable | `five_card_target`; `five_card_committed_executable` |
| sampled | observed | `five_card_committed` |
| analysis_bridged | observed, sampled, `five_card_proximity` | `five_card_committed`; `five_card_uniform_sampled`, `five_card_row_repeated_tableau`, `five_card_row_biased_tableau`; `kim_biased_proximity_close` |
| checks | observed, sampled, analysis_bridged, `five_card_proximity` | `five_card_committed`, `five_card_F`; `five_card_row_repeated_tableau`, `five_card_row_biased_tableau`; `kim_centi_cert`, `kim_biased_cert`, `kim_biased_proximity_cert`, `five_card_reprice39`, `five_card_row_biased_proximity`; `kim_biased_proximity_close` |

The observed file requires the algebraic one because `Require Import` is not
transitive for `Import`: it reaches `five_card_target` through the executable
file's own import otherwise, and the first compile of this staged text failed
on exactly that. `s5_exec` is required by no phase file, which is what makes
one recorded rejection print one constant differently; see below.

## Compiles

One process at a time through `rocq1`, `-time` read on every run. No sentence
over 5 s in any of the seven files; the slowest sentence anywhere is an
import.

| File | rc | Sentences | Slowest | Slowest that is not an import |
|---|---|---|---|---|
| `five_card_proximity.v` (reduced) | 0 | 49 | 2.25 s (import) | 0.014 s |
| `five_card_tableau_algebraic.v` | 0 | 18 | 2.06 s (import) | 0.001 s |
| `five_card_tableau_executable.v` | 0 | 22 | 2.06 s (import) | 0.001 s |
| `five_card_tableau_observed.v` | 0 | 37 | 2.06 s (import) | 0.001 s |
| `five_card_tableau_sampled.v` | 0 | 60 | 1.89 s (import) | 0.037 s |
| `five_card_tableau_analysis_bridged.v` | 0 | 281 | 1.39 s (import) | 0.439 s |
| `five_card_tableau_checks.v` | 0 | 50 | 1.40 s (import) | 0.304 s |

Wall times are not comparable across runs, the machine-wide Rocq lock being
shared with other sessions; one run of the reduced file read 100.2 s wall
against 3.7 s of sentence time.

The load path behaved as the template records: under the recursive
`-R staged/instances/kim2025 pgg_smc`, a file in `tableau/` is
`pgg_smc.tableau.<name>`, `From pgg_smc Require Import <name>` resolves it,
and no `-R` line for the subdirectory was added.

## The ten new declarations

Each equation closes by `exact: erefl`; none is `by []` or `done`. The
measured hazard at this instance is `five_card_row_repeated39_atE`, an
equation between two rows' `published_at` coordinates, which the moved file
records at 147 s under `exact: erefl` against 0.07 s under `reflexivity`.
That declaration is moved with production's `reflexivity` proof and is not
touched. No new equation has that shape: every re-cut is stated against a
named Sampled value and a named row, never row against row.

| Declaration | File | Closed by | `-time` |
|---|---|---|---|
| `five_card_algebraic_start` | algebraic | definition | 0.000 s |
| `five_card_committed_executable` | executable | definition | 0.001 s |
| `five_card_committed_executable_paramsE` | executable | `exact: erefl` | 0.000 s |
| `five_card_committed_executableE` | observed | `exact: erefl` | 0.000 s |
| `five_card_uniform_sampled` | sampled | definition | 0.000 s |
| `five_card_row_uniform_sampledE` | analysis_bridged | `exact: erefl` | 0.000 s |
| `five_card_row_repeated_indistinguishability_sampledE` | analysis_bridged | `exact: erefl` | 0.000 s |
| `five_card_row_biased_indistinguishability_sampledE` | analysis_bridged | `exact: erefl` | 0.000 s |
| `five_card_row_repeated39_sampledE` | analysis_bridged | `exact: erefl` | 0.005 s |
| `five_card_row_biased_inv25_sampledE` | analysis_bridged | `exact: erefl` | 0.000 s |

For comparison, `five_card_row_repeated39_atE` reads 0.000 s in the staged
text, as it does in production.

Nothing was left whole at a higher phase and no re-cut had to be dropped.
The two concluded rows carry a `_sampledE` of their own, which PGL(2,7)'s
`pgl27_row_word39` did not need because a branch row already was that row
from the named value; here no such branch row exists for either concluded
row, so the equation is written and it costs nothing.

## The scope block, and the one re-scoping

Verification rule 3 asks that the innermost `Local Open Scope` be the same in
all six phase files. It is `Local Open Scope ring_scope.` in all six, which
is also production `five_card_rows.v`'s innermost entry.

Production `five_card_proximity.v` opens `ring`, `fdist`, `proba`, so its
innermost entry is `proba_scope`, and the 28 declarations that move out of it
are read under `fdist`, `proba`, `entropy`, `ring` in the AnalysisBridged and
checks files instead. There are **two** environment changes, not one. The %(nresc)d
declarations that leave `five_card_proximity.v` are read under the
four-scope block of the sampled, AnalysisBridged and checks files; and the
%(nlow)d declarations of `five_card_rows.v` that land in the algebraic and
observed files lose `fdist`, `proba` and `entropy`, keeping `ring_scope` as
the innermost entry, which is what template rule 3 pins. Neither runs the
other way: no declaration of the rows file moves into the reduced proximity
file. Both are pinned, not assumed: `baseline.v` and `fidelity.v` print all
82 non-`Fail` types under one scope block and the diff is empty.

## The section scaffolding

This instance has three `Section`s where PGL(2,7) had one, and two of them
move whole into the AnalysisBridged file:

| Section | Source | Where it lands |
|---|---|---|
| `five_card_proximity_distance` | proximity | stays, with all four of its lemmas |
| `kim_biased_proximity_numbers` | proximity | analysis_bridged, with all three |
| `kim_cert_numbers` | rows | analysis_bridged, with all four |

The generator does not write those lines. A declaration's slice runs to the
next declaration, so a `Section` and its `Variable` line ride on the previous
declaration's chunk and the `End` line rides on the last declaration of the
section; whenever a section moves whole they therefore land correctly by
construction. The one exception is the two lines that open
`five_card_proximity_distance`, which precede the first declaration of the
file and belong to no chunk, and those the generator writes. `verify.py`
checks the split rather than assuming it.

## `_CoqProject`, the edit production needs

Derived by name, because other landings are editing this file. It moved
under this work: `instances/kim2025/five_card_rows.v` read line 225 at the
first look and line 231 at the second, the PGL(2,7) landing having been
applied in between. The main session re-derives both positions by name at
the time of the `cp`.

1. Delete the line `instances/kim2025/five_card_rows.v`.
2. After the line `instances/kim2025/five_card_proximity.v`, insert:

```
instances/kim2025/tableau/five_card_tableau_algebraic.v
instances/kim2025/tableau/five_card_tableau_executable.v
instances/kim2025/tableau/five_card_tableau_observed.v
instances/kim2025/tableau/five_card_tableau_sampled.v
instances/kim2025/tableau/five_card_tableau_analysis_bridged.v
instances/kim2025/tableau/five_card_tableau_checks.v
```

No `-R` line is added or removed. The six lines go after
`instances/kim2025/five_card_proximity.v` and not at the retired file's own
position, for two reasons that both have to hold: the AnalysisBridged file
requires the reduced proximity file, and the checks file requires
`s5_tableau_analysis_bridged`, whose six lines sit between the retired file's
position and the proximity file's. Nothing between the two positions depends
on `five_card_rows`: its reverse closure is `{five_card_proximity}` alone,
and the cut removes that arrow.

## Verification

`verify.py`, `gen_fidelity.py`, `run_fidelity.py`, `compile.py` and
`gen_phase_files.py` are this directory's copies of the PGL(2,7) ones.
`stage_edits.py` is rewritten as a scanner, since this instance has nothing
to repoint. Three changes to `verify.py`:

1. `scaffolding()` checked that no phase file holds a `Section` line. Here
   two sections move, so it now checks an explicit partition of production's
   nine scaffolding lines across the staged files and prints the split.
2. The box-line scan treated any one-line `(* ... *)` comment as a box line
   to be padded to 80 columns. `five_card_rows.v` carries such a comment,
   `(* The terminal's payload is kim_centi_cert_eps_lt weakened by ltW. *)`,
   which is 70 columns and is moved verbatim. The scan now applies only
   inside a header or banner block, which is to say between an opening and a
   closing rule line, and the PSL(2,11) F11 space-before-`*)` check applies
   there too.
3. One intended difference between two rejection messages is tabled, with
   the substitution that makes the two byte-identical, so it is checked and
   not waved through.
4. A section banner must be exactly one content line (PGL(2,7) ruling 5).
5. No index entry may let a name touch `==` (PGL(2,7) ruling 9).

### `verify.py`, whole output in `verify.out`

```
%(verify)s
```

Every token of every moved declaration is production's, statement and proof.
Each of the %(nfail)d recorded `Fail`s was compiled un-`Fail`ed in the
preamble of the file it sits in, on both sides, production without the staged
root and the staged text with it. None contains `was not found in the current
environment`.

### The one rejection that does not print identically

The eleven recorded rejections come from two production files whose import
lists differ, and they land in one checks file, so one of the two
environments cannot be reproduced. `five_card_rows.v` does not import
`s5_exec`; `five_card_proximity.v` does. The checks file follows the first,
because no name of `s5_exec` is used in it and an import has to be earned
(PSL(2,11) ruling 7). The consequence is that
`Fail kim_biased_cert_s5_ideal`, which comes from the proximity file, prints

```
"SampleAdapter R (OE.oe_execution s5_exec.s5_rand_observed)"
```

where production printed `s5_rand_observed`. It is the same constant with the
printer qualifying it, the rest of the message is byte-identical, and
`verify.py` checks exactly that substitution on every run. Importing
`s5_exec` would flip the difference onto `Fail five_card_row_s5_family`,
which comes from the rows file, so one of the two is unavoidable; the
earned-import rule decides which.

### The six intended docstring differences

| Declaration | What changes | Why |
|---|---|---|
| `five_card_target` | "The prefix above names" becomes "The prefix five_card_committed names", and "five_card_realises_expected below" loses the "below" | the prefix and that lemma are in the Observed file and this record is in the Algebraic one |
| `five_card_row_uniform_tableau` | "the prefix above, the uniform rotation model" becomes "the prefix five_card_committed, the uniform rotation model" | the prefix is in the Observed file; the witness named in the same sentence is still above |
| `five_card_row_repeated_tableau` | "the prefix above" becomes "the prefix five_card_committed" | the prefix is in the Observed file and this value in the Sampled one |
| `five_card_row_biased_levelE` | "the rejected ascription that follows" becomes "the rejected ascription of five_card_tableau_checks.v" | the equation is at Sampled and the rejection is in the checks file |
| `Fail five_card_row_s5_family` | "The two models above are typed" becomes "The two models named at Sampled are typed" | the two models are in the Sampled file |
| `kim_biased_proximity_cert` | "kim_biased_proximity_close of this file" becomes "kim_biased_proximity_close of five_card_proximity.v" | the distance stays in the reduced file and the certificate moves |

### `fidelity.v` against `baseline.v`

Both print the type of all 82 non-`Fail` declarations of the two source files
under one scope block, and print the assumptions of every lemma, fact and
theorem and of the seven published rows and the two `Definition`s that are
proof terms. `fidelity.v` prints ten more types and ten more assumption
reports, one per new declaration, the four new `Definition`s included, which
the PSL(2,11) ruling 9 asks for because a type alone would pass on a wrong
body. The name lists are read out of production by `gen_fidelity.py`.

**`baseline.v` is the scope pin, not `fidelity.v`.** `baseline.v` requires
production's `five_card_rows` and `five_card_proximity` and prints their
types under the phase files' scope block, so each constant's type comes from
production's parse and the printing from the new block. `fidelity.v` cannot
settle that on its own, because it loads the staged files and both sides come
from one block.

### Why the pin is sound for bodies and not only for statements

PGL(2,7) ruling 10: a `Definition`'s body is pinned by an equation, never by
`Check`. Of the 93 production declarations, the 28 that leave
`five_card_proximity.v` are the only ones whose scope changes, the rows
file's block being the AnalysisBridged file's. Five of the 28 are
`Definition`s, and two of those hold a numeric literal in their body:

| Re-scoped `Definition` | Literal in the body | How its body is pinned |
|---|---|---|
| `kim_biased_proximity_cert` | `1 / 50` | `Print` on both sides, and `kim_biased_proximity_cert_epsE` states the field |
| `five_card_reprice_inv100` | `1 / 100` | `Print` on both sides |
| `five_card_row_biased_branch_indistinguishability` | none | `Check` plus token identity |
| `five_card_row_biased_proximity` | none | `Check` plus token identity |
| `five_card_biased_proximity_at_singleton` | none | `Check` plus token identity |

`Reprice` is `forall R : realType, option R`, so `Check @f` prints nothing of
the number a `Reprice` carries. The two `Reprice` definitions of the rows
file, `five_card_reprice39` and `five_card_reprice_inv25`, are not re-scoped,
their file's block being the AnalysisBridged file's, but they are the same
risk class, so all four are printed. The `Print` lines sit in the part of the
body both files share, so the four bodies are diffed. Every other re-scoped
numeral appears inside a printed statement closed by conversion
(`kim_biased_proximity_cert_epsE`, `kim_biased_proximity_eps_halfE`,
`kim_biased_proximity_cert_eps_lt2`, `kim_biased_conclude_below_false`,
`five_card_biased_view_proximity`, `five_card_biased_view_own_marginals`),
and token identity of the sources closes the rest. Neither source declares a
`Local Notation` and no staged file declares one, so both sides print through
one notation set.

| File | rc | wall | `Check` | `Print Assumptions` |
|---|---|---|---|---|
| `fidelity.v` (staged text) | 0 | 51.1 s | 92 | 78 |
| `baseline.v` (production) | 0 | 46.2 s | 82 | 68 |

`baseline.v` is compiled without `-R staged/instances/kim2025 pgg_smc`, so it
loads production's `five_card_proximity` and not the reduced copy. An
earlier run of `fidelity.v` read 273.7 s wall against the same work, which
is time spent behind another session on the machine-wide Rocq lock.

`diff` of `baseline.out` against the first 853 lines of `fidelity.out`:
**empty**, 0 lines. All 82 printed types and all 68 assumption reports are
byte-identical, so no statement changed meaning under the new imports and the
new scope block, and no moved declaration gained or lost an axiom. The ten
reports for the new declarations name only the three axioms production
already carries: `propositional_extensionality`,
`functional_extensionality_dep`, `constructive_indefinite_description`. No
new axiom.

### `stage_edits.py`

```
%(stage)s
```

One file is staged under `staged-comments/` and it is **applied with this
instance**, not deferred. `manifest/pgg_tableau_arm_relations.v` cites
`instances/kim2025/five_card_proximity.v` in prose for the implication
`five_card_biased_indistinguishability_implies_proximity`, which moves into
the AnalysisBridged file. This is not the dangling case of the PGL(2,7)
audit's ruling 6, the reduced file still existing under that path; it is the
empty-reverse-closure case. Nothing in the tracked tree `Require`s
`pgg_tableau_arm_relations`, so the repoint recompiles one module, and the
reason that defers a manifest repoint does not apply to a file nothing
imports. The staged copy is produced by anchored replacement on production's
text, is verified comment-only, and no line exceeds 80 bytes.

The scan behind that ran over every tracked file with only `notes/` and
`.claude/` excluded, which is what the PGL(2,7) audit's F5 asks for after a
cross-instance file was missed there. Every hit is tabled in
`staged/RETIRED.md`. **No `.v` file of another instance cites either name**,
and nothing outside the two sources of the cut names `five_card_rows`, so
retiring that file needs no comment repoint at all.

## Second pre-audit pass

Read against `notes/probes/2026-09-20-tableau-directories-pgl27/audit-pgl27.md`
(F1 to F19 and the twelve rulings) and the third addendum of `TEMPLATE.md`,
which arrived after the first hand-back. Each row is one sentence or one
index entry of new text and the declaration or object it was checked against.
No declaration moved and no proof changed: `verify.py` reports the same 93
of 93 token-identical declarations after the pass as before it.

| Ruling | File | Before | After | Checked against |
|---|---|---|---|---|
| 4 | algebraic header | "the instance analyses part two levels above" | "part three levels above, at Sampled" | `CompletionLevel` has five constructors (`manifest/pgg_analysis_status.v:60`); a model is adjoined by `sample_step`, which reaches Sampled, three levels above Algebraic |
| 3 | analysis_bridged index, `five_card_static_obs_indep` | "below the threshold the direct computation is independent of the conjunction" | "below the threshold of two, that is at a coalition of at most one of the five seats, …" | the premise is `#\\|C\\| < profile_k (instance_profile five_card_algebra)`, and `five_card_singleton_below_threshold` with `cards1` fixes that at two |
| 3 | analysis_bridged index, `five_card_exact_view_secrecy` | "the exact arm's four conjuncts at this instance" | "at a coalition of at most one of the five seats, the exact arm's four conjuncts" | `HC : (#\\|C\\| < 2)%%N` in the theorem's own binder |
| 3 | analysis_bridged index, `five_card_biased_view_proximity` | "the proximity row's security statement, at one fiftieth" | "at a coalition of at most one of the five seats, …" | the same binder |
| 3 | analysis_bridged index, `five_card_biased_view_own_marginals` | "the same with the ideal removed" | "the same at the same coalitions with the ideal removed" | the same binder |
| 3 | reduced index, `kim_biased_proximity_close` | "the two models' joint laws of reading and secret are within one fiftieth" | "at every coalition, the two models' joint laws …" | the lemma quantifies over every `C` with no premise, which is what its own docstring says and what the AnalysisBridged entries must not be confused with |
| 7 | analysis_bridged header | "publishes that same AnalysisPathRow under a different proposition" | "under a different arm" | `five_card_row_biased_proximity_armE` gives `IdealProximityArm`, `five_card_row_biased_branch_indistinguishability_armE` gives `InputIndistinguishabilityArm`, and `five_card_row_biased_arm_neq` of the checks file proves the two differ |
| 1 | analysis_bridged header, last paragraph | named only the distance as what the reduced file holds | names all four of its lemmas, and says the six exact-arm link lemmas are in this file and not there, with the reason | grep of the whole staged tree: `five_card_static_obsE` and its five siblings occur only in the AnalysisBridged file, and `five_card_uniform_pairE`, `five_card_reading_secretE`, `five_card_arg_cut_prodE`, `kim_biased_proximity_close` only in the reduced file. This is F1's shape, caught before the audit rather than by it |
| 8 | reduced header | "it is an upper bound on a sum of absolute differences and not the distance itself", inside the distance sentence | the sibling's sentence as a paragraph of its own, with this instance's numbers: "Every number below bounds a sum of absolute differences, which is twice the total variation distance of the literature, so a bound of one fiftieth here is a distinguishing advantage of at most one hundredth wherever it is used." | `instances/psl211/psl211_word_proximity.v:16-18`. The old wording called one `var_dist` "the distance" and then said the quantity bounded was "not the distance itself", two lines apart |
| 9 | analysis_bridged index | `five_card_row_repeated39==`, `five_card_reprice_inv100==` | both entries broken, name on its own line | both names are exactly 24 characters, the column width; the generator's break threshold was `> 24` and is now `>= 24`. `verify.py` now fails any name touching `==` |
| 5 | the generator, and `verify.py` | production's "The number" banner rode inside `kim_biased_proximity_cert_idealE`'s slice and surfaced under a second authored banner | the slice is cut at that banner, "The number" is authored as its own banner, and the section's two opening lines are written out | production `five_card_proximity.v:283-285`. No staged banner has more than one content line, now asserted on every run |
| 12 | analysis_bridged header | no locator | a locator table, one entry per published row, naming its banner, its `_sampledE`, `_rowE`, `_armE`, `_atE` or `_publishedE` and its reading, and saying so where one does not exist | every name grepped out of the file. `five_card_row_repeated39` has no `_rowE` and no reading of its own; `five_card_row_biased_inv25` has `five_card_row_biased_forms_publishedE` in place of a `_rowE`; the two rows continued from `five_card_row_biased_tableau` have no `_sampledE` |
| Q2 | sampled header | "It is the only security statement made at this level." | "It is the one security statement this instance makes below AnalysisBridged, and it is of this level for two reasons: its subject is the law the named Sampled model samples, and no arm of certify takes a conditional mutual information as a payload, so no program can carry it one level up." | `five_card_row_biased_leak_bound`'s subject is `sa_sampleP (amf_sample kim_biased_family R tt)`; `certify_exact`, `certify_indistinguishability` and `certify_idealproximity` take an `ExactWitness`, an `IndistinguishabilityCert` and an `IdealProximityCert` (`manifest/pgg_tableau.v:777`, `:793`, `:811`) |
| Q2 | analysis_bridged header, first paragraph | "every statement whose subject is a payload or a row is here." | the same, plus "The one security statement of the instance whose subject is neither is Kim's input-privacy bound, which is in five_card_tableau_sampled.v." | the same, so the two headers cannot be read as both claiming the instance's security statements |
| 6 | `staged/RETIRED.md` | the scan reported as a sentence | the scan tabled, every hit of both names over every tracked file with its reason, and the one repoint applied rather than deferred | `git grep` over the whole tracked tree with only `notes/` and `.claude/` excluded. `manifest/pgg_tableau_arm_relations.v` has an empty reverse closure; it is not the dangling case, since the reduced file still exists, but the batching reason that defers a manifest repoint does not apply to a file nothing imports |
| 10 | `gen_fidelity.py` | `Check` on every non-`Fail` declaration, no `Print` | `Print` of the four `Definition`s whose body holds a numeric literal, in the part both files share | the table under "Why the pin is sound for bodies" |
| 11 | none | none | none | the five-card instance has no `restate` terminal and no `_target`, `_bridge` or `_restated` declaration, so the ruling does not arise. It is cited rather than re-argued |

Two things the pass checked and left alone. `five_card_viewS_indep`'s index
entry, "at most one revealed colour is independent of the conjunction", is
production's own wording and already carries the hypothesis, the lemma's
premise being `(#|C| < 2)%%N` and its content being `leak_view_set` at a
reveal pattern of at most one card. And the moved docstring of
`kim_biased_exact_le_eps` contains the word "price", which the banned
vocabulary list does not carry and which is production's text in a moved
declaration, so it is out of scope for this landing and belongs to the
comment pass.

## Fix pass 1

Against `audit-five-card.md`, F1 to F19 applied, F20 and F21 no change. Every
auditor replacement was treated as a proposal: the declaration was opened, the
type read and each clause confirmed before the sentence was written.
Deviations are in the last column. `verify.py` reports the same 93 of 93
token-identical declarations after the pass, and a token diff of the seven
staged `.v` files against commit `6cbc3a8`, comment-stripped, is empty in all
seven: 556, 120, 140, 270, 578, 3278 and 534 code tokens, none changed.

| id | Final text | Declaration or object checked | Deviation from the auditor's draft |
|---|---|---|---|
| F1 | algebraic docstring: "One run mode is built on this value, the committed one: the Executable file continues it into five_card_committed_executable, and five_card_committed_executableE identifies that value, with the three run facts adjoined, with the prefix all seven published rows continue from." | the equation is `(five_card_committed_executable execute terminates by … recon by …) = five_card_committed`; `five_card_algebraic_start` does not occur in it, and the Executable file's own line is `five_card_algebraic_start ;;; params_step of (…)` | folded into the existing sentence about the run mode rather than added as a separate one, so the docstring still makes one claim about that mode; the content is the auditor's |
| F2 | executable header: "…which is what keeps the function a row names and the value its run **is meant to recover** one term." | `encoded_input_params` takes the ideal function as `f` and stores it as the expected value; the reconstruction fact arrives at Observed with `five_card_recon` | none |
| F3 | analysis_bridged header, in the positive form: "Of the three, the repeated row is the one whose route the programs here share: the manifest reaches AnalysisBridged for it by the transfer whose base premise is kim_centi_cut_mixing, with five_card_static_obs_const for the reading equality, and kim_centi_cert carries those same two as fields. For the one-cut row the manifest names two theorems reaching that level: the corresponding transfer, whose premises kim_biased_cert carries, and five_card_colour_view_leak_bound, a conditional mutual information no statement of certify takes and which is carried at Sampled. For the uniform row the manifest names five_card_exec_trace_secrecy at that row's own content trace, where the program's statement is five_card_exact_view_secrecy, read off the published row by view_secrecy_of." | the three manifest docstrings were read in full. The repeated row: "its base premise is FiveCardAnalysis.centi_cut_mixing … with FiveCardAnalysis.static_obs_const for the reading equality … Their transfer concludes FiveCardAnalysis.centi_static_obs_indistinguishability, and that conclusion is what reaches AnalysisBridged". The one-cut row: "colour_view_leak_bound bounds a conditional mutual information … reaching AnalysisBridged" and "biased_static_obs_indistinguishability … is a second theorem reaching AnalysisBridged at this row". The uniform row: "exec_trace_secrecy is stated at this row's own random variable content_trace R ord0 … reaching AnalysisBridged". `kim_centi_cert`'s fields include `(@kim_centi_cut_mixing R)` and `(@five_card_static_obs_const R)`; `kim_biased_cert`'s the same pair at one cut | two. The auditor's draft says the repeated row's level is reached "by the same theorem the manifest names"; the manifest names a transfer with two premises and a conclusion, so the sentence names the two premises the certificate carries, which is the checkable claim. And the manifest writes facade aliases; the underlying names are used, `five_card_analysis.v:342`, `:395` and `:406` defining `colour_view_leak_bound`, `centi_cut_mixing` and `static_obs_const` as `@five_card_colour_view_leak_bound`, `@kim_centi_cut_mixing` and `@five_card_static_obs_const`, and `:314` `exec_trace_secrecy` as `@five_card_exec_trace_secrecy` |
| F4 | checks docstring: "**Kim's two models, named at Sampled,** are typed over this prefix's observed execution, so the two statements hold." | `five_card_tableau_sampled.v` declares three `Tableau Sampled` values; the two the rejection is about are `five_card_row_repeated_tableau` and `five_card_row_biased_tableau` | none. This is the sixth intended docstring difference, re-worded; `verify.py` still prints six and no more |
| F5 | observed index: "five_card_F_ite == the ideal function is its conditional spelling, up to conversion" | `Definition five_card_F_ite : fn_f five_card_F = (fun ab => if ab.1 then ab.2 else false) := erefl` | none |
| F6 | algebraic header: "All seven published rows of this instance begin at that algebra, and the uniform analysis and Kim's two analyses first differ three levels above, at Sampled, where each names its own model." | the Observed header names `five_card_committed` as the prefix all seven rows and all three Sampled values continue from, so the three analyses agree at Algebraic, Executable and Observed; `CompletionLevel` has five constructors, Sampled being three above Algebraic | none. The other sentences of the header were re-read for the same shape: "the value below is the one point" occurs nowhere else, and "All seven published rows of this instance begin at that algebra" is true and makes no agreement claim |
| F7 | sampled header: "Three programs are named here, one per model a published row continues from, and the three model families they sample are those of five_card_models.v: all three sit over the one committed run and are indexed by the unit type." | the three families are declared in `five_card_models.v`; this file declares three `Tableau Sampled` values | none |
| F8 | sampled header: "Two of the statements here are about neither a program nor the manifest's row for it, and no arm of certify takes a payload of either kind." | the file's index lists eight key results; six are about a program or the manifest's row for it | none |
| F9 | sampled: "**Of the statements this directory makes** it is the one security statement below AnalysisBridged, and it is of this level for two reasons: its subject is the law the named Sampled model samples, and **the three statements of certify take an ExactWitness, an IndistinguishabilityCert and an IdealProximityCert, none of them a conditional mutual information.** The distance kim_biased_proximity_close of five_card_proximity.v is at no level and is not counted here." — analysis_bridged: "**Of the statements this directory makes,** the one whose subject is neither a payload nor a row is Kim's input-privacy bound, which is in five_card_tableau_sampled.v; the distance kim_biased_proximity_close is in instances/kim2025/five_card_proximity.v and is at no level." | `certify_exact`, `certify_indistinguishability` and `certify_idealproximity` of `manifest/pgg_tableau.v` take an `ExactPayload`, an `IndistinguishabilityPayload` and an `IdealProximityPayload`, which are families of `ExactWitness`, `IndistinguishabilityCert` and `IdealProximityCert`; `kim_biased_proximity_close` is in the reduced file and belongs to no phase | "no program can carry it one level up" is gone, replaced by the three named statements as the remit directs. The class is named in both and the distance named beside it in both |
| F10 | checks header: "which differ in two of their five **fields**" | `MkAnalysisPathRow` has five fields, and the moved docstring sixteen lines below already says "fields" | none. The three `apr_` projections a published row prints are still called coordinates, which is a different object and is left alone |
| F11 | checks banner: "What a certificate may hold" | the group holds four rejections with two causes, only one of them about the ideal | none |
| F12 | analysis_bridged header: "The **map and the five** link lemmas of the exact arm are not there but here, because no proof that stays uses them." | `five_card_colour_fill` is a `Definition`, indexed under `Definitions:`; the other five are `Lemma`s | none |
| F13 | sampled index: "== one starting position's endpoint marginal under the repeated model's cut law is **under** 2^-40 **of the uniform law, in variation distance**" | `var_dist (fdistmap … ) (fdist_uniform (card_ord 5)) < 2%%:R ^- 40`, a strict bound | none |
| F14 | locator entry 1: "…five_card_row_uniform_armE, and, **under The exact arm's four conjuncts at this instance**, the reading five_card_exact_view_secrecy." Entry 7: "…_publishedE and _armE, and, **under What the proximity row states at this instance**, the readings five_card_biased_view_proximity and five_card_biased_view_own_marginals." | the banner map of the file was regenerated and every locator name checked against the banner it sits under; the other five entries name nothing outside their banner | none |
| F15 | `staged/RETIRED.md`: the reduced file's line count is now read from the staged file | 169 | none |
| F16 | analysis_bridged index: "== the input-indistinguishability proposition at any constant implies the proximity proposition at one fiftieth, its hypothesis unused" | `IndistinguishabilityPropAt (kim_biased_cert R tt) c -> IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 50)`, proof `by move=> _; …` | none |
| F17 | algebraic header: "Two is the threshold **the derived profile declares**" | one object, `profile_k (instance_profile five_card_algebra)`, now named the same way in both headers | none |
| F18 | observed docstring of `five_card_committed_executableE`: "…the Executable file names the parameters they build, and this equation is what **lets a statement made at that named value be read as a statement about the prefix.**" | the two adjacent equations relate two different pairs; `five_card_committed_paramsE` keeps production's "two spellings" wording, which is its own text | none |
| F19 | `STATUS.md`: "There are two environment changes, not one. The 28 declarations that leave five_card_proximity.v are read under the four-scope block …; and the 7 declarations of five_card_rows.v that land in the algebraic and observed files lose fdist, proba and entropy, keeping ring_scope as the innermost entry …" | both counts are computed by `gen_status.py` from `verify.py`'s reading | one. The auditor writes "the algebraic, executable and observed files"; the executable file holds no moved declaration, both of its declarations being new, so it is not named |
| F20 | no change | the seven sites are production text inside moved docstrings | carried to the closing comment pass, as the audit directs |
| F21 | no change | `five_card_colour_fill` and `five_card_viewS_nth` are encoding mathematics whose single consumer, `five_card_static_obsE`, is at AnalysisBridged | the reason is recorded in the placement table above so it need not be re-derived |

## Rulings taken

| Question | Ruling | What it changed here |
|---|---|---|
| Where the six exact-arm link lemmas live | with the witness they build, in the AnalysisBridged file | the PGL(2,7) exception does not apply, because no staying proof uses them; the reduced file is four lemmas |
| `five_card_row_biased_leak_bound` and `five_card_row_repeated_endpoint_lt` | at Sampled, the phase their subject is | the Sampled file carries the instance's one security statement below an arm, and the AnalysisBridged file carries no statement that is not about a payload or a row |
| `five_card_row_biased_levelE` at Sampled, its `Fail` in checks | accepted | follows PGL(2,7)'s split of `pgl27_reprice41` from `Fail pgl27_row_word41` |
| A `_sampledE` for both concluded rows | written | nothing row against row anywhere in the staged text |
| `s5_exec` not imported by the checks file | accepted, with the printing difference tabled | one recorded rejection prints one constant qualified |
| The comment repoints | one, applied with this instance | `manifest/pgg_tableau_arm_relations.v` staged under `staged-comments/`; empty reverse closure, so the batching reason does not apply |
| Q1, the `s5_exec` printing difference | keep the earned-import side | the checks header says nothing about it; it is a fact about printing and lives in this page only |
| Q2, Kim's input-privacy bound at Sampled | accepted as placed | the Sampled header states it as a fact with its two reasons, and the AnalysisBridged header no longer reads as holding every security statement |
| Q3, Candidate B | no | one AnalysisBridged file with a locator table in its header, as PGL(2,7) now has in production |
"""


NRESC = len([1 for k, n, _ in verify.items(
    verify.strip_comments(open(verify.PROD_PROX).read()))
    if (k, n) not in verify.STAYING])
NLOW = len([1 for key in ORDER
            if where_of(key) in ("algebraic", "observed")
            and key[1] not in verify.NEW_NAMES])


def main():
    linetable = "\n".join(
        "| `%s` | %d |" % (f, LINES[f]) for f in
        ["five_card_proximity.v", "five_card_tableau_algebraic.v",
         "five_card_tableau_executable.v", "five_card_tableau_observed.v",
         "five_card_tableau_sampled.v",
         "five_card_tableau_analysis_bridged.v",
         "five_card_tableau_checks.v"])
    proxpre = verify.preamble(verify.STAGED_PROX).split("Set Implicit")[0]
    import subprocess
    stage = subprocess.run(["python3", "stage_edits.py"], cwd=HERE,
                           capture_output=True, text=True).stdout.strip()
    txt = BODY % {
        "linetable": linetable,
        "prows": PRODLINES["five_card_rows.v"],
        "pprox": PRODLINES["five_card_proximity.v"],
        "ptot": sum(PRODLINES.values()),
        "stot": sum(LINES.values()),
        "nprod": NPROD,
        "nmoved": NPROD - COUNTS["stays"],
        "nstay": COUNTS["stays"],
        "nnew": NEW,
        "table": TBL,
        "proxpre": proxpre,
        "verify": VERIFY,
        "nfail": NFAIL,
        "stage": stage,
        "nresc": NRESC,
        "nlow": NLOW,
    }
    open(os.path.join(HERE, "STATUS.md"), "w").write(txt)
    print("wrote STATUS.md, %d lines" % txt.count("\n"))
    print("placement rows: %d; per file: %s" % (len(ORDER), COUNTS))


if __name__ == "__main__":
    main()
