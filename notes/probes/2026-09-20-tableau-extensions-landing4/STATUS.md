# Landing 4 of the Tableau extensions — staged text

Date: 2026-09-20. Branch `feat/tableau-extensions-probe`, HEAD `0c4a4ef`.

This directory holds the STAGED TEXT of landing 4 (PSL(2,11)) of
`notes/2026-09-20-000000-tableau-extensions-landing-design.md`. Nothing under
`manifest/`, `instances/`, `lib/`, `security/` or `_CoqProject` of the
repository was touched, and nothing under
`notes/probes/2026-09-20-tableau-extensions-landing1/`, `-landing2/`,
`-landing3/` or `notes/probes/2026-09-19-tableau-extensions/` was touched. The
main session does every `cp`.

Every staged file compiles, the fidelity file compiles, and every landed
declaration's assumptions are the classical trio.

## Layout

Six files are LANDED: their text is the permanent text landing 4 proposes.

| Staged path | Base | What it is |
|---|---|---|
| `staged/instances/psl211/psl211_word_model.v` | NEW; probe `p6_psl211_word_model.v` | landed |
| `staged/instances/psl211/psl211_analysis.v` | PRODUCTION plus two facade aliases | landed |
| `staged/manifest/pgg_analysis_manifest.v` | LANDING 3's staged text plus Row 11, its typed row and its pins | landed |
| `staged/manifest/pgg_analysis_client.v` | LANDING 3's staged text plus one `Check`, row count eleven | landed |
| `staged/instances/psl211/psl211_reading_constancy.v` | PRODUCTION, comment changes only | landed |
| `staged/instances/psl211/psl211_word_proximity.v` | NEW; seventeen declarations of probe `p6_psl211_word_proximity.v` and `p6_mutations.v` | landed |

Sixteen files are CHAIN-CONSISTENCY COPIES of landing 3's staged text. They
are not landed by this landing. They exist so that everything downstream of
landings 1, 2 and 3 compiles against the text the `cp` will force in
production.

| Staged path | Whose text it is |
|---|---|
| `staged/lib/var_dist_supp.v` | landing 2 |
| `staged/security/var_dist_joint_law.v` | landing 2 |
| `staged/instances/kim2025/five_card_mixing.v` | landing 2 |
| `staged/manifest/pgg_tableau_arm_relations.v` | landing 2 |
| `staged/instances/kim2025/five_card_proximity.v` | landing 2 |
| `staged/instances/kim2025/five_card_analysis.v` | production |
| `staged/manifest/pgg_tableau.v` | landing 1 |
| `staged/manifest/pgg_tableau_syntax.v` | landing 1 |
| `staged/instances/pgl27/pgl27_rows.v` | landing 1 |
| `staged/instances/kim2025/five_card_rows.v` | landing 1 |
| `staged/instances/s5/s5_rows.v` | landing 1 |
| `staged/instances/psl211/psl211_rows.v` | landing 1 |
| `staged/instances/pgl27/pgl27_exec.v` | landing 3 |
| `staged/instances/pgl27/pgl27_models.v` | landing 3 |
| `staged/instances/pgl27/pgl27_analysis.v` | landing 3 |
| `staged/instances/pgl27/pgl27_proximity.v` | landing 3 |

All sixteen are copied from **landing 3's `staged/`**, which is where landings
1, 2 and 3 all read as one text: landings 1 and 2 are in production and
landing 3's directory holds production's copies of them, and landing 3's own
six files are only there.

**Landing 3's text is not final and moved once while this landing was built.**
`restage.py` is how to redo everything:

```
python3 restage.py --check     # report which chain files differ, and whether
                               # the difference is code or comments
python3 restage.py             # copy them, regenerate the four edited files,
                               # recompile the whole chain
```

It reports each chain file as `unchanged`, `comments only` or `CODE CHANGED`
using the comment-stripped token comparison `verify.py` uses, then calls
`rebase_shared.py`, then `compile.py`, which compiles the `_CoqProject` order:
the twenty-two staged files and the fidelity file, one Rocq process at a time
through the `rocq1` lock.

### The rebase, and the one time it fired

`rebase_shared.py` GENERATES the four edited files from their bases by
anchored replacement, so none of them is ever hand-edited. Two are generated
from landing 3's staged text (`pgg_analysis_manifest.v`,
`pgg_analysis_client.v`), two from production (`psl211_analysis.v`,
`psl211_reading_constancy.v`). Every operation is one exact anchor and one
replacement; an anchor found zero or twice is an error and nothing is written.
Seven operations on the manifest, two on the client, four on the facade, four
on the constancy file.

It fired once. Landing 3's audit fix pass rewrote three of its files while
this landing was being built, and `restage.py` reported
`lib/var_dist_supp.v` CODE CHANGED, `instances/pgl27/pgl27_exec.v` comments
only and `instances/pgl27/pgl27_proximity.v` CODE CHANGED, and the manifest's
Row 10 block and the `pgl27_row_prior_exact` docstring each gained a
rewritten sentence. The rebase carried landing 4's seven manifest operations
onto that newer text with no anchor lost, and the whole chain recompiled
green. The compile table below is the run after that restage.

### The reverse closures

A Python walk over the `Require` lines gives
`instances/psl211/psl211_analysis.v` the nine reverse-dependants the design's
section 3 computes: `pgg_analysis_manifest`, `pgg_tableau`,
`pgg_tableau_syntax`, `pgl27_rows`, `five_card_rows`, `s5_rows`,
`psl211_rows`, `psl211_reading_constancy` and `pgg_analysis_client`. The new
`psl211_word_model.v` has an empty reverse closure as a file, and once the
facade aliases its family it acquires the facade's nine, which is R2's
accepted state. `psl211_word_proximity.v` and
`psl211_reading_constancy.v` have empty reverse closures.

**`psl211_analysis.v` is not in the forward closure of
`psl211_endpoints.v`.** The same walk computes that forward closure as 35
modules and the intersection with this landing's twenty-two files is empty.
`psl211_endpoints.v` was never compiled here. `psl211_analysis.v`,
`psl211_models.v` and `psl211_reading_constancy.v` load
`psl211_endpoints.vo` by digest, which is R3's recorded state: the `.vo` is
dated 2026-09-17 and the `.v` 2026-09-18, and a single-file `coqc` does not
compare timestamps.

### The load-path order

Landings 1 to 3 measured it and landing 4 reuses it: Rocq 9.0.0 resolves a
`Require` to the LAST matching `-R`/`-Q` entry, so the staged roots are the
last entries bound to `pgg_smc`, after production's AND after
`-Q . tableau_ext_landing4`. The run prints one `overriding-logical-loadpath`
warning per staged root, which is that remapping and not an error.

---

## E1 — the new `instances/psl211/psl211_word_model.v`

Seven declarations, all seven token-identical to probe
`p6_psl211_word_model.v`, and no `Fail`.

| Group | Declarations | Probe source |
|---|---|---|
| the law | `psl211_word_cutP`, `psl211_wordP` | `:76`, `:85` |
| the adapter | `psl211_word_sample`, `psl211_word_sampleP_E`, `psl211_word_cut_distE` | `:94`, `:102`, `:110` |
| the family | `psl211_word_family` | `:120` |
| the distance | `psl211_word_law_le40` (probe `psl211_word_lawE`) | `:135` |

**What the file is.** The model is the all-decks carrier with the law of the
cut coordinate alone replaced by the 584-letter word law. The header says
exactly that, in the sentence "The two models share the sample space, the deck
description and the law it is drawn from, and differ in the law of the cut
alone: this file is the all-decks carrier with that one coordinate's law
replaced, and nothing else of the instance is restated here." The clause after
the colon is the landing's; the rest is the probe's.

**The import edit.** `From tableau_ext_probe Require Import
p1_joint_law_distance` becomes `From pgg_smc Require Import
var_dist_joint_law`. The probe's file used two lemmas of
`p1_joint_law_distance.v`, `fdist_prod_snd` in `psl211_word_cut_distE` and
`var_dist_prodR` in `psl211_word_law_le40`. **Landing 2 did not put them in
`lib/var_dist_supp.v` as the design's section 2 says; it created
`security/var_dist_joint_law.v` and put all four there.** The design's
sentence "`p1_joint_law_distance` resolves to `var_dist_supp` after landing 2"
is therefore wrong about the file name and right about everything else. Both
lemmas are in `security/var_dist_joint_law.v:98,131` of landing 2's staged
text, and `var_dist_le2`, which `psl211_word_law_le2` uses, stays in
`lib/var_dist_supp.v:49`.

**The header.** Four paragraphs and the probe's `Definitions:` and
`Key results:` blocks, which index all seven declarations and no `Fail`. The
banner name and the file's opening line are the landing's, the probe's
"Probe P6, first half" being a probe word.

---

## E2 — `psl211_analysis.v` gains two aliases

Section 4 of the facade gains `word_sample := @psl211_word_sample` after
`exact_sample` and `word_family := psl211_word_family` after `exact_family`.
Both follow the file's contract: a `Definition` whose body is the landed
constant, no restated type, the `psl211_` prefix dropped. The file's own
trailing checker pins one representative per section and `exact_sample` is
section 4's, so it gains no line, as landing 3's `pgl27_analysis.v` did not.

R2 asks for the family alias only. The adapter alias is added with it so that
Row 11 names its sample in facade vocabulary, which is landing 3's ruling Q3
carried over.

Two comment changes come with them.

The header's check table gains one line, because this table does list the
sample model of this facade where `pgl27_analysis.v`'s does not:

- added: `584-letter word sample model -> word_sample, word_family`

Section 4's banner is rewritten, because it spoke of one model:

- before: "The model is followed by the equations that identify its cut and
  its coalition distributions, so that a security statement about a named
  distribution can be attached to a named executed observer."
- after: "The all-decks model is followed by the equations that identify its
  cut and its coalition distributions, so that a security statement about a
  named distribution can be attached to a named executed observer. The word
  model carries its own cut equation psl211_word_cut_distE at
  instances/psl211/psl211_word_model.v, and is aliased here for the sample and
  model slots of its own manifest row."

The import line `From pgg_smc Require Import psl211_alldecks psl211_models.`
gains `psl211_word_model`. No cycle: `psl211_word_model.v` requires no facade.

Whole-file token diff against production: **3 hunks, 14 tokens**, the import
and the two aliases. Nothing else in the file moved.

---

## E3 — `pgg_analysis_manifest.v` gains Row 11

Three code additions and three comment additions.

1. The Row 11 comment block, after Row 10's and before "Aliases carrying no
   capability yet", in the field order of Row 9's and Row 10's and with the
   same capabilities table and level justification.
2. `psl211_row_word`, after `pgl27_row_prior_exact`, with its own docstring.
3. Five `Check` pins in the rows checker, and one application of the new
   family at `tt` in the block that exercises unit-indexed families.
4. The banner "The deterministic checker: the ten typed rows" becomes "the
   eleven typed rows".
5. The file header gains one sentence about the arm (see R12 below).
6. Row 9's missing-premise cell gains one clause (see R12 below).

The typed row, verbatim:

```
Definition psl211_row_word : AnalysisPathRow :=
  @MkAnalysisPathRow PSL211Analysis.observed AnalysisBridged
    PSL211Analysis.word_family IdealFinite BaselineClassicalOnly.
```

Its five fields are the row equation's and not retyped: `landing_fidelity.v`
proves `published_row psl211_row_word_proximity = psl211_row_word` by the
landed lemma and, beside it, the probe's raw-family form of the same equation
by `exact: erefl`, so the manifest row and the program agree by conversion.

Three fields of the table need their own justification, each read off a
declaration.

**Bound or certificate: `psl211_word_proximity_cert`, at 2^-40.** The number
is `ipc_eps` of that certificate, which `psl211_word_proximity_cert_epsE`
gives in closed form, and its distance field is
`psl211_word_proximity_close`. It bounds a sum of absolute differences, twice
the total variation distance of the literature, so a distinguisher's advantage
against this row is at most 2^-41. The table and the level justification both
say so.

**Transfer status: `IdealFinite`.** The cut is drawn by evaluating a word of
584 letters where `psl211_row_alldecks` draws it uniformly from the group, so
an idealized shuffle is replaced by one a dealer performs. The row equation
`psl211_row_word_proximity_rowE` carries that constructor; it is not a choice
made in the manifest.

**Missing premise: none.** The row's certificate carries its own distance
field, so no model-transfer premise is absent. The "Absent capabilities"
block constrains `NoModelComparison` and `StaticExecutedOnly` rows and names
the S5 word row separately; this row is neither, and that block is unchanged.

Whole-file token diff against landing 3's staged text: **3 hunks, 88 tokens**,
the typed row, the five pins and the family application. The fix pass adds no
code token to this file.

---

## E4 — `pgg_analysis_client.v` reaches eleven rows

`Check PSL211Analysis.word_family.` is added after
`Check PSL211Analysis.exact_family.`, with the same
`(* 4 Models, typed family *)` trailing comment, and the header sentence "the
ten typed rows" becomes "the eleven typed rows". The file keeps its single
`Require` and every `Check` stays bare. Only the family alias is checked, not
the adapter, which is landing 3's shape for `PGL27Analysis.prior_sample`:
section 4's representative sample alias for this facade is already
`exact_sample`.

Whole-file token diff against landing 3's staged text: **1 hunk, 2 tokens**,
the `Check`.

---

## E5 — `psl211_reading_constancy.v`, comments only

Code tokens identical to production: **YES**, 0 hunks, `verify.py` check (2).
Five comment changes, 175 words, the fifth being the section banner of the
fix pass's S1. Two are the sentences landing 4 makes false
and two are sentences it makes incomplete, which the design's section 4 asks
for at this landing. Each was checked against the declarations it speaks of
and against the new word model.

### (a) The header clause the word adapter makes FALSE

- before: "Nothing here says the word row is excluded outright:
  psl211_alldecks_constancy_false_word584 reaches eps < 1/1320 - 2^-40, and no
  weighted-word sample adapter exists for this instance."
- after: "Nothing here says the word row is excluded outright:
  psl211_alldecks_constancy_false_word584 reaches eps < 1/1320 - 2^-40, and the
  row published over the weighted-word adapter psl211_word_sample in
  instances/psl211/psl211_word_proximity.v carries a proximity certificate,
  which has no constancy field to refute."

Checked against: `psl211_word_sample`
(`staged/instances/psl211/psl211_word_model.v`) is a weighted-word
`SampleAdapter` for this instance, so the old clause is false;
`psl211_row_word_proximity` is published over `psl211_word_family`, whose
adapter is that one; `IdealProximityCert` has the five fields `ipc_ideal`,
`ipc_witness`, `ipc_secret`, `ipc_eps`, `ipc_close` and no constancy field,
where `ic_const` is a field of `IndistinguishabilityCert`.

### (b) The stated reason of `psl211_alldecks_constancy_false_word584`, FALSE

- before: "It is stated on the cut law rather than on a certificate because no
  weighted-word SampleAdapter exists in this tree, so there is no adapter whose
  cut is this law and no ic_Hd through which a certificate's ideal could be
  held near it."
- after: "It is stated on the cut law rather than on a certificate because it
  quantifies over every law within eps of that cut, so it covers the ideal of
  every certificate at once and needs no adapter to name one. The weighted-word
  adapter psl211_word_sample of instances/psl211/psl211_word_model.v draws this
  cut, and the row published over it in
  instances/psl211/psl211_word_proximity.v carries a proximity certificate,
  which has no constancy field, so that row and this refutation are two
  propositions and neither bears on the other."

Checked against: the lemma's own statement, which quantifies over
`ideal : R.-fdist cutT` and `eps : R` under
`var_dist (@rho_from_words_weighted R 10 2 584 psl211_moves (psl211_Wuni R))
ideal <= eps`, so the new reason is the statement's own generality and the
lemma's scope is unchanged; `psl211_word_cutP` is that same
`rho_from_words_weighted` term, which `landing_fidelity.v` states and closes by
`exact: erefl`, so the adapter's cut and the refutation's cut are one law; and
`ic_Hd : sw_rho_dist ic_b = sa_cut_dist sa` is a field of
`IndistinguishabilityCert`, so the old consequent clauses fall with the
premise.

### (c) The header's "Not claimed" paragraph, INCOMPLETE

Added after "single-card marginal bound.": "The exclusion covers the
input-indistinguishability arm alone: a proximity certificate carries no
shuffle bound and no constancy field, and the row of
instances/psl211/psl211_word_proximity.v publishes 2^-40 over the word model
through that arm."

The design's section 4 asks for this at `:31-34`, because landing 4 gives this
instance a row at the other arm publishing 2^-40. Checked against
`psl211_alldecks_no_small_eps_cert`, which quantifies over
`cert : IndistinguishabilityCert (psl211_alldecks_sample R)` and over
`sw_bound_eps (ic_b cert)`, neither of which a proximity certificate has.

### (d) The file header, INCOMPLETE

- before: "The instance publishes its all-decks row through the exact arm, and
  this file is what the input-indistinguishability arm would cost it."
- after: "The instance publishes its all-decks row through the exact arm and
  its word row through the proximity arm, in
  instances/psl211/psl211_word_proximity.v, and this file is what the
  input-indistinguishability arm would cost it."

The design's section 4 asks for this at `:14-15`.

---

## E6 — the new `instances/psl211/psl211_word_proximity.v`

Seventeen declarations, fourteen of them statements and three recorded
`Fail`s. Sixteen are token-identical to the probe's; the one that is not is
the forced edit below.

| Group | Declarations | Probe source |
|---|---|---|
| the distance | `psl211_word_proximity_close` | `p6_word:109` |
| the certificate | `psl211_word_proximity_cert`, `psl211_word_proximity_cert_idealE` | `p6_word:146,160` |
| what it keeps secret | `psl211_word_proximity_cert_secretE`, `psl211_word_proximity_cert_secretTE` | `p6_mut:127,138` |
| the number | `psl211_word_proximity_cert_epsE`, `psl211_pow2_40_ge1`, `psl211_pow2_40_gt0`, `psl211_word_law_le2`, `psl211_word_proximity_cert_eps_lt2` | `p6_word:176,181,185`, `p6_mut:75`, `p6_word:198` |
| the row | `psl211_row_word_proximity`, `psl211_row_word_proximity_armE`, `psl211_row_word_proximity_rowE` | `p6_word:229,239,250` |
| what the row states | `psl211_word_view_proximity` | `p6_word:267` |
| recorded `Fail`s | `psl211_word_law_by_var_dist_le2` (probe `psl211_word_law_tauto`), `psl211_word_proximity_cert_pgl27_ideal`, `psl211_word_proximity_cert_ideal_self` | `p6_mut:88,107,155` |

R7 needs no rename here: the probe's `p6_psl211_word_proximity.v` already
declares the two power facts as `psl211_pow2_40_ge1` and
`psl211_pow2_40_gt0`, and landing 3 renamed the PGL(2,7) pair to match.

**Imports.** The union of the two probe files' blocks with three probe-local
edges rewritten: `pgg_tableau pgg_tableau_syntax` and `psl211_rows` become
`From pgg_smc` ones, `p1_joint_law_distance` resolves to `var_dist_joint_law`
(E1), and `p6_psl211_word_model` resolves to `psl211_word_model`.
`var_dist_supp` comes from `p6_mutations.v`'s block and carries
`var_dist_le2`; `pgl27_models` comes from the same block and carries
`pgl27_exact_family`, the subject of the cross-instance rejection.

### The one forced code edit

**`psl211_row_word_proximity_rowE` states the manifest row by name.** The
probe writes its right-hand side at the raw family names, because the manifest
held no row at this model when it was written. Landing 4 adds that row, so the
lemma states what every other `_rowE` in the tree states.

- before (`p6_psl211_word_proximity.v:250-254`):

```
Lemma psl211_row_word_proximity_rowE :
  published_row psl211_row_word_proximity
  = @MkAnalysisPathRow psl211_alldecks_observed AnalysisBridged
      psl211_word_family IdealFinite BaselineClassicalOnly.
Proof. exact: erefl. Qed.
```

- after:

```
Lemma psl211_row_word_proximity_rowE :
  published_row psl211_row_word_proximity = psl211_row_word.
Proof. exact: erefl. Qed.
```

`exact: erefl` closes it in **0.000 s** and its `Qed.` in 0.000 s, read off the
`-time` line, so `reflexivity` is not needed and `by []` is not used. This is
landing 3's ruling Q4 applied to the PSL(2,11) row.

The docstring is rewritten with the statement, and the probe's last two
sentences are dropped rather than carried:

- before: "What separates it from the manifest's all-decks row is the fourth
  coordinate, the model family an AnalysisPathRow records: psl211_row_alldecks
  carries the exact family and this row carries the word family, which the
  manifest of the tree holds no row at. The equation published_row
  psl211_row_word_proximity = psl211_row_alldecks typechecks and is not
  provable by conversion."
- after: "The manifest row the program publishes: the row of the twelve-card
  chirality instance at the 584-letter word model. Its five coordinates are the
  observed execution the program runs on, the completion level the publish
  terminal reaches, the model family the sample step named, and the two
  statuses the terminal was given, so the manifest's description of this path
  is read off the program and not written beside it. It differs from
  psl211_row_alldecks in the model family and in the transfer status, the
  all-decks row comparing no idealized model where this one replaces an
  idealized shuffle by a finite word."

Two reasons for the rewrite beyond the changed statement. The clause "which
the manifest of the tree holds no row at" is false once landing 4 lands. And
the clause naming the model family as the ONLY separating coordinate is false
in production as well as here: `psl211_row_alldecks` is `StaticExecutedOnly`
and this row is `IdealFinite`, so the two differ in two coordinates. The same
correction was applied to the manifest's typed-row docstring.

### Comment changes against the probe

Five, each with its reason. `verify.py` prints all five in full.

`psl211_word_law_le2` and the recorded guard, two words each: "ceiling"
is a metaphor noun for a bound and landings 2 and 3 removed it from their own
files.

- before: "within two of each other by the ceiling every pair of laws on one
  finite sample space meets" / "The same ceiling does not reach 2^-40"
- after: "within two of each other by the bound every pair of laws on one
  finite sample space meets" / "The same bound does not reach 2^-40"

`psl211_word_proximity_cert_eps_lt2`, twelve words, the same substitution
three times and "under two" to "below two", matching landing 3's wording of
the sibling lemma.

- before: "is under two, the ceiling var_dist_le2 of lib/var_dist_supp.v
  gives" / "What this rules out is the ceiling's own tautology" / "The number
  is 2^-41 of the ceiling."
- after: "is below two, the bound var_dist_le2 of lib/var_dist_supp.v gives" /
  "What this rules out is that bound's own tautology" / "The number is 2^-41
  of that bound."

`psl211_word_view_proximity`, two words, following landing 2's N10: "view"
stays inside identifiers and the prose says "reading".

- before: "the joint law of the executed coalition view and the chirality"
- after: "the joint law of the executed coalition reading and the chirality"

`psl211_row_word_proximity_rowE`, the whole docstring, quoted above.

One plain `(* *)` comment inside a proof loses a date, because the staged text
is permanent text. `psl211_word_proximity_cert_idealE`:

- before: "Both projections were measured at 0.000 s on 2026-09-19."
- after: "Both projections close by exact: erefl in under 0.01 s."

Measured here: the tactic at 0.000 s and its `Qed.` at 0.003 s.

### What lands unchanged, deliberately

The docstring paragraph of `psl211_row_word_proximity` that cites the three
fixed-deck refutations is the probe's audited text verbatim, including "That
every coalition below the threshold reads an ideal cut by the same law at
every run argument is false at each cut named here" and "Each is witnessed at
a coalition of three seats, and all three stay true beside this row". It names
`psl211_alldecks_constancy_false`,
`psl211_alldecks_constancy_false_word584` and `psl211_dealt_constancy_false`,
all three in `instances/psl211/psl211_reading_constancy.v`.

### Header

What the file is about, in five paragraphs: which two models are compared and
that the ideal's own privacy is a theorem the all-decks row publishes; the
word gloss of the instance; the threshold, that the row names no constant and
what the input-indistinguishability arm is and is not excluded at; and one new
paragraph saying that every number below bounds a sum of absolute differences,
twice the total variation distance, so the advantage is at most half of
2^-40. `Definitions:` indexes the two definitions and `Key results:` the
twelve remaining statements, so the two blocks index all 14 non-`Fail`
declarations and no `Fail`.

---

## The recorded `Fail`s, and why each fails

Three `Fail` guards land. Each subject resolves in the staged tree, which is
what landing 3 found one of its guards failing: `var_dist_le2` is
`lib/var_dist_supp.v:49`, `pgl27_exact_family` is `pgl27_models.v` and
`psl211_word_family` is the new model file, all three imported by this file.
Each guard was re-compiled without its `Fail`, one file per guard, in the
scratchpad and never in the repository
(`/private/tmp/.../scratchpad/unfail_l4_f1.v` … `unfail_l4_f3.v`). All three
fail, and each fails for the reason its comment states, verbatim.

| Guard | Error |
|---|---|
| `psl211_word_law_by_var_dist_le2` | `The term "var_dist_le2 ?P ?Q" has type "is_true (var_dist ?P ?Q <= 2)" while it is expected to have type "is_true (var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2 ^- 40)"` |
| `psl211_word_proximity_cert_pgl27_ideal` | `The term "amf_sample pgl27_exact_family R tt" has type "SampleAdapter R (OE.oe_execution pgl27_exec.pgl27_observed)" while it is expected to have type "SampleAdapter R (instance_exec psl211_alldecks_params)"` |
| `psl211_word_proximity_cert_ideal_self` | `The term "erefl" has type "ipc_ideal (...) = ipc_ideal (...)" while it is expected to have type "ipc_ideal (...) = amf_sample psl211_word_family R idx" (cannot unify …)` |

`rocq compile` echoes nothing for a `Fail` guard, so the guards' own compile is
evidence only that they fail, not why. The three scratch files are the record
of why.

---

## R12 — the manifest's Row 9 block and the facade table, read in full

Every sentence landing 4 makes false or incomplete, and what it now says.

| Where | Sentence | Verdict | Action |
|---|---|---|---|
| Row 9, `missing premise` | "none: the cut this model draws is the uniform distribution on the group already, so the path compares no idealized model" | INCOMPLETE: this model is now the ideal a certificate names | gained "It is the model the proximity certificate of Row 11 names as its ideal", the wording landing 3 gave Row 10 |
| header, what a row records | "Each row names its protocol instance, probability model, profile, execution, observed-execution and sample aliases, … its completion level and its assumption status." | INCOMPLETE: nothing says where the arm is read | one sentence added: "A row records no security arm. Which arm a published program carries is read off that program by security_arm_of of manifest/pgg_tableau.v, so a row at the proximity arm is told from one at the exact arm by the certificate its table names and not by a field of the record." |
| checker banner | "The deterministic checker: the ten typed rows" | FALSE | "the eleven typed rows" |
| client header | "One import reaches all four facades, the typed status vocabulary and the ten typed rows." | FALSE | "the eleven typed rows" |
| Row 9, `protocol family and model` | "the cut drawn uniformly over the 660 elements of the group" | stays true; it describes Row 9's model | none |
| Row 9, `sample alias` | "PSL211Analysis.exact_sample; the row's typed model witness is PSL211Analysis.exact_family, the family indexed by unit" | stays true | none |
| Row 9, `model transfer` | "none claimed" | stays true | none |
| Row 9, level justification | "Both privacy lines quantify over coalitions of at most five of the twelve seats, the profile's own privacy threshold being six. The independence is exact and is an average over deck descriptions and cuts; the fixed-dealer colour results … are no part of this row." | stays true | none |
| Row 9, capabilities table | the four lines at `exact_view_indep`, `static_indep`, `observed_recovers`, `secret_expectedE` | stay true | none |
| "Aliases carrying no capability yet", `PSL211Analysis` line | "seat_endpoint, coalition_endpoints, prior, cut_distE, exact_coalition_distE, content_traceE, content_trace, exact_transfer_status" | stays true AND complete: both new aliases carry a capability in Row 11, so neither belongs in this table | none |
| "Absent capabilities" | "every path whose transfer status is NoModelComparison or StaticExecutedOnly states in its missing-premise cell either the premise it lacks or why none is absent. The IdealFinite word row 8 also keeps naming the absent cut-carrier premise below" | stays true: Row 11 is `IdealFinite` and is not row 8, and rows 2 and 5 are `IdealFinite` and unnamed there already | none |

---

## Compiles

One Rocq process at a time, through the `rocq1` lock, `rocq compile` with
`-time`, never `make`. `instances/psl211/psl211_endpoints.v` was never
compiled. Nothing was written into a production directory: every `.vo` lands
beside its `.v` under `staged/`.

The table is the `python3 restage.py` run after landing 3's text moved,
captured in `restage.out`; `compile.out` holds the run before it.

| File | rc | wall | sentences over 5 s |
|---|---|---|---|
| `staged/lib/var_dist_supp.v` | 0 | 4.0 s | none |
| `staged/security/var_dist_joint_law.v` | 0 | 3.9 s | none |
| `staged/instances/pgl27/pgl27_exec.v` | 0 | 16.9 s | one, 8.8 s, production's own `by vm_compute` |
| `staged/instances/pgl27/pgl27_models.v` | 0 | 4.1 s | none |
| `staged/instances/pgl27/pgl27_analysis.v` | 0 | 3.7 s | none |
| `staged/instances/kim2025/five_card_mixing.v` | 0 | 4.3 s | none |
| `staged/instances/kim2025/five_card_analysis.v` | 0 | 3.9 s | none |
| `staged/instances/psl211/psl211_word_model.v` | 0 | 3.8 s | none |
| `staged/instances/psl211/psl211_analysis.v` | 0 | 3.8 s | none |
| `staged/manifest/pgg_analysis_manifest.v` | 0 | 6.1 s | one, 5.4 s, the `Require Export` block |
| `staged/manifest/pgg_tableau.v` | 0 | 13.2 s | none |
| `staged/manifest/pgg_tableau_syntax.v` | 0 | 4.4 s | none |
| `staged/instances/pgl27/pgl27_rows.v` | 0 | 6.4 s | none |
| `staged/instances/kim2025/five_card_rows.v` | 0 | 4.6 s | none |
| `staged/instances/s5/s5_rows.v` | 0 | 40.2 s | none; the wall includes another session's hold on the `rocq1` lock, the file measuring 4.0 s alone in the earlier run |
| `staged/instances/psl211/psl211_reading_constancy.v` | 0 | 22.1 s | two, 6.0 s and 6.1 s, both production's |
| `staged/instances/psl211/psl211_rows.v` | 0 | 5.4 s | none |
| `staged/manifest/pgg_analysis_client.v` | 0 | 3.8 s | none |
| `staged/manifest/pgg_tableau_arm_relations.v` | 0 | 3.7 s | none |
| `staged/instances/kim2025/five_card_proximity.v` | 0 | 5.7 s | none |
| `staged/instances/pgl27/pgl27_proximity.v` | 0 | 5.2 s | none |
| `staged/instances/psl211/psl211_word_proximity.v` | 0 | 4.6 s | none |
| `landing_fidelity.v` | 0 | 270.5 s | thirteen, each a `Print Assumptions` at about 20 s |

No sentence of a landed file is over 5 s. The two new files' sentences sum to
3.6 s for `psl211_word_model.v` and 4.4 s for `psl211_word_proximity.v`, the
slowest sentence outside a `Require` in either being
`exact: (view_proximity_of psl211_row_word_proximity R tt C HC)` at 0.110 s.
The 20 s `Print Assumptions` sentences are the cost the design predicts for a
declaration whose type names `psl211_alldecks_observed`; thirteen of the
twenty-four pay it.

No row-against-row data equation was added: the one row equation this landing
states names a manifest `AnalysisPathRow` and closes by `exact: erefl` in
0.000 s. No `by []` and no `done` appears on a `published_at` or
`published_row` equation anywhere in the landed text.

---

## `Print Assumptions`

24 declarations, from `landing_fidelity.out`. Every one reports exactly the
classical trio `constructive_indefinite_description`,
`functional_extensionality_dep` and `propositional_extensionality`, and no
declaration is closed under the global context. No other axiom name appears
anywhere in the run, and no `Axiom`, `Parameter`, `Admitted` or `Abort` is
introduced by any landed file.

| Group | Declarations |
|---|---|
| `psl211_word_model.v` | the seven |
| `psl211_analysis.v` | `PSL211Analysis.word_sample`, `PSL211Analysis.word_family` |
| `pgg_analysis_manifest.v` | `psl211_row_word` |
| `psl211_word_proximity.v` | the fourteen non-`Fail` declarations |

---

## `landing_fidelity.v`

Logical path `tableau_ext_landing4`. It `Require`s the staged copies through
`pgg_smc`, which the flags resolve to `staged/`. Every restatement is the
probe's statement verbatim and is closed by `exact: <staged name>`; no `by []`
and no `done` appears on a `published_at` or `published_row` equation.

| Section | Checks |
|---|---|
| provenance | `Check` on `psl211_analysis.PSL211Analysis.word_sample`, `psl211_analysis.PSL211Analysis.word_family`, `pgg_analysis_manifest.psl211_row_word`, `psl211_word_model.psl211_word_family`, `psl211_word_proximity.psl211_word_proximity_cert` |
| the word model | the four definitions ascribed at their types, the three lemmas restated, and `psl211_word_cutP R = rho_from_words_weighted …` by `exact: erefl`, which is what makes the adapter's cut and the refutation's cut one law |
| the facade | both aliases ascribed at their types and `PSL211Analysis.word_family = psl211_word_family` |
| the manifest row | the landed `published_row psl211_row_word_proximity = psl211_row_word`, closed by the landed lemma, and beside it the probe's raw-family form of the same equation, closed by `exact: erefl` |
| the certificate | the distance field at its threshold premise, the certificate ascribed, its ideal equation, and both secret equations |
| the numbers | `ipc_eps = 2^-40`, the two power facts, the bound at two and the strict inequality below two |
| the arm and the theorem | the row ascribed at `PublishedRow` and not `PublishedRowAt`, the `_armE`, and `psl211_word_view_proximity` at 2^-40 |
| assumptions | the 24 `Print Assumptions` above |

The provenance test is one-sided in both directions. `PSL211Analysis.word_sample`,
`PSL211Analysis.word_family` and `psl211_row_word` exist only in this
landing's text of the file that declares them, so if production's
`psl211_analysis.vo` or `pgg_analysis_manifest.vo` were loaded, the
corresponding `Check` would be an error; and no production load path holds a
`psl211_word_model` or a `psl211_word_proximity` at all.

**Two of the six landed files carry no provenance witness.**
`psl211_reading_constancy.v` changes in comments alone and
`pgg_analysis_client.v` adds one `Check` line and one header word, so neither
declares a name a `Check` could discriminate on. What stands for them is that
the whole chain is compiled from the staged text and that every dependant
loads its staged `.vo` by digest: `psl211_reading_constancy.v` has an empty
reverse closure, and the client's single `Require` resolves to the staged
manifest, which the provenance `Check` on `psl211_row_word` witnesses.

The three recorded `Fail` guards are not restated in the fidelity file: a
`Fail` declares nothing, so there is no statement to ascribe. Their fidelity
is the token check of `verify.py` and the three scratch compiles above.

---

## `verify.py`

Five checks, output in `verify.out`.

1. **Whole-file token diffs, each against its own base.**
   `psl211_analysis.v` against production: 1 hunk for the import and 2 for the
   aliases, 14 tokens. `psl211_reading_constancy.v` against production: 0
   hunks, 0 tokens. `pgg_analysis_manifest.v` against landing 3's staged text:
   3 hunks, 88 tokens. `pgg_analysis_client.v` against landing 3's staged
   text: 1 hunk, 2 tokens. Every hunk is an addition listed in E2 to E4;
   nothing in any of the four moved.
2. **Comments-only check.** `psl211_reading_constancy.v`'s code token stream
   is production's, reported YES, and its comment text is printed as a
   157-word unified diff in four hunks, the four changes of E5.
3. **Per-declaration token diffs against the probe.**
   `psl211_word_model.v` **6 of 7** token-identical.
   `psl211_word_proximity.v` **14 of 17** token-identical. The one that is not
   are named in the script's `EXPECTED` map, printed with their reason and
   then in full: `psl211_row_word_proximity_rowE`, 8 tokens, the right-hand
   side, and the three the fix pass's two renames touch.
4. **Comment word diffs.** Five differences, each listed with before and after
   in E6 and each classified. The largest,
   `psl211_row_word_proximity_rowE` at 126 words, is the docstring rewritten
   with its statement.
5. **Scans.** `SpectralDecay` 0, `SpectralCert` 0, `_indist\b` 0,
   `RepricePayload` 0, `idealproximity_ceiling` 0, `psl211_spectral_constancy`
   0, any abbreviation of "indistinguishability" 0, `apex` 0,
   `gate`/`gates`/`gated`/`gating` 0, `posit`/`posits`/`posited`/`positing` 0,
   `L1` 0. `ceiling`: 8 hits, all eight in the chain-consistency copy of
   `five_card_rows.v`, which is landing 1's text already in production and
   which landing 4 does not own. Lines over 80 bytes: four, all in
   chain-consistency copies (`five_card_analysis.v:336` at 81 bytes, from
   production; `pgg_tableau_syntax.v:334,372,403` at 101, 90 and 128 bytes,
   from landing 1). None is in a landed file. These are the same eight and
   four landing 3 reported.

---

## `_CoqProject` placement

Production's `_CoqProject` is not edited here. Two new lines, and the existing
lines they go after, at production's current numbering.

| New line | Inserted after | Why |
|---|---|---|
| `instances/psl211/psl211_word_model.v` | `instances/psl211/psl211_models.v` (`_CoqProject:216`), before `instances/psl211/psl211_recovery.v` | it `Require`s `psl211_models`, `psl211_alldecks`, `psl211_mixing`, `psl211_exec` and `var_dist_joint_law`, all before that line, and the facade at `:218` `Require`s it, so it must come before `:218` |
| `instances/psl211/psl211_word_proximity.v` | `instances/psl211/psl211_rows.v` (`_CoqProject:228`), before `manifest/pgg_analysis_client.v` (`:229`) | it `Require`s `psl211_rows`, `pgg_tableau`, `pgg_tableau_syntax`, `pgg_analysis_manifest`, `psl211_word_model`, `var_dist_supp`, `var_dist_joint_law` and `pgl27_models`, so it goes after all of them, and `psl211_rows.v` is the last of them |

The design's section 1 gives the same two anchors. The second file cannot join
landing 2's and landing 3's proximity files at `:226`, because it requires
`psl211_rows.v` at `:228`.

The other four files of landing 4 are already in `_CoqProject`.

---

## Questions for the owner

1. **Two of the four comment changes to `psl211_reading_constancy.v` are
   completions, not corrections.** E5 (c) and (d) are what the design's
   section 4 asks for at `:31-34` and `:14-15`; only (a) and (b) are sentences
   landing 4 makes false. If the owner wants the landing confined to the false
   sentences, dropping (c) and (d) is two operations removed from
   `rebase_shared.py`'s `CONSTANCY` list and one recompile of a file with an
   empty reverse closure.
2. **`PSL211Analysis.word_sample` is aliased and not checked in the client.**
   Landing 3's shape for `PGL27Analysis.prior_sample` is followed, so the
   client checks the family alone. The manifest's Row 11 names the adapter in
   facade vocabulary, which is why the alias exists.
3. **The probe's `psl211_row_word_proximity_rowE` docstring made a claim that
   is false in production as well as here**, that the model family is the only
   coordinate separating this row from `psl211_row_alldecks`. The transfer
   status separates them too. The correction is applied in two places, the
   lemma's docstring and the manifest's typed-row docstring, and is flagged
   because it is a correction to audited probe text and not a landing edit.

---

# Fix pass 1

Both audits of `833acaf` applied to the staged text. Only files inside this
directory were edited. The four generated files were changed through
`rebase_shared.py`'s operation lists and never by hand: `python3
rebase_shared.py` run twice in a row reproduces all four byte for byte
(`cmp` clean).

Code changes: the two renames the orchestrator ruled and the fidelity lines
they force, and nothing else. A comment-stripped token diff of the six landed
files and `landing_fidelity.v` against `833acaf` gives exactly

| File | changed tokens |
|---|---|
| `staged/instances/psl211/psl211_word_model.v` | 2: `psl211_word_lawE` to `psl211_word_law_le40` |
| `staged/instances/psl211/psl211_word_proximity.v` | 4: the `exact:` of `psl211_word_proximity_close`, and `psl211_word_law_tauto` to `psl211_word_law_by_var_dist_le2` |
| `landing_fidelity.v` | 6: `f_psl211_word_lawE` renamed and its two mentions |
| the other four landed files | 0 |

## A — the whole-file re-read of `psl211_reading_constancy.v`

All 1025 lines read. Every sentence naming an adapter, a family, a row, an
arm, a publication or a non-existence, and what it says after landing 4:

| Where | What it says | Verdict |
|---|---|---|
| `:4-16` header opening | the instance publishes its all-decks row at the exact arm and its word row at the proximity arm | true, and it is passage (d) |
| `:18-30` all-decks mode | the field asks for constancy outside the secret; `psl211_alldecks_static_indep` is what the published row carries | true |
| `:32-45` quantitative form | a certificate over the all-decks model states its distance against the group-uniform law, its identification field pinning its shuffle law to the adapter's cut | true of `psl211_alldecks_sample`, whose cut is `psl211_alldecks_cut_distE` |
| `:42-45` passage (c) | the exclusion covers one arm | true after S2 |
| `:47-56` dealt mode | "this tree carrying no dealt-mode sample adapter" | STILL TRUE: `psl211_word_sample : SampleAdapter R (instance_exec psl211_alldecks_params)` is an all-decks-mode adapter |
| `:58-77` "Not claimed" | the arm is not shown unavailable; the larger-eps range is occupied and argued, not compiled | true; `:71-75` is passage (a) |
| `:79-91` "Names" | prefixes and proof-script letters | no existence claim |
| `:93-134` index blocks | twelve entries | each checked against its declaration; `_word584`'s entry is true |
| `:188-206` `coalition_reading_constancy` | the field as a standalone Prop | true |
| `:207-216` `indistinguishability_cert_reading_constancy` | refuting the proposition at a law refutes every certificate whose ideal cut is that law | true, and it is the lemma S3 reads against |
| `:222-248` the three seats | coalition size and threshold | true |
| `:254-265` `_constancy_false` | no certificate takes the group-uniform law as its ideal cut here | true |
| `:297-510` block-line section | fibers, counts, masses | no existence claim |
| `:529-560` `_ideal_lawE` | per-deck symmetry | true |
| `:562-566` `_fiber_true0` | "which is not the law the row is about" | true of either row: both are averages over deck descriptions |
| `:575-616` `_false_supp` | support form | true |
| `:618-671` `_false_close` | eps form | true |
| `:673-688` `_cert_ideal_close` | "this adapter's cut is the uniform law on the shuffle group" | true of the all-decks adapter, which is the one the type names |
| `:690-739` `_no_small_eps_cert`, `_no_zero_eps_cert` | scoped to input-indistinguishability certificates over the all-decks model | true |
| **`:742` section banner** | "The word model, which this tree carries no sample adapter for" | **FALSE — S1** |
| `:745-764` `_false_word` | two-step form over W and ideal | true |
| `:766-795` `_word584` | passage (b) | true after S3 and S4 |
| `:801-992` dealt section | "this tree carrying no dealt-mode sample adapter through which a certificate's ideal could be pinned to it" (`:962-963`) | STILL TRUE, same reason as `:55-56` |
| `:994-1025` empty coalition | the field holds at `set0` | true |

S1 is the only sentence the word model makes false. Nothing else in the file
says that an adapter, a family or a row does not exist.

Two inherited sentences of production carry an economic metaphor and were
left, because N28's ruling confines this pass to the two new files: `:750`
("the price of replacing the exact shuffle by one a dealer can perform … pays
both") and `:770` ("the whole information-theoretic price of that
replacement"), beside the `:16` the ruling names. All three belong to a later
pass over production.

## B — the soundness findings

| id | final text | declaration checked | note |
|---|---|---|---|
| S1 | `(*     The word model, whose sample adapter is psl211_word_sample             *)` | `psl211_word_sample (R : realType) : SampleAdapter R (instance_exec psl211_alldecks_params)`, `psl211_word_model.v` | DEVIATION: the auditor's text was "whose sample adapter is psl211_word_model.v", which names a file where an adapter is meant. The declaration is named instead. 80 bytes. |
| S2 | "…and the row of instances/psl211/psl211_word_proximity.v publishes 2^-40 over the word model through the proximity arm." | `psl211_row_word_proximity_armE : security_arm_of psl211_row_word_proximity R idx = IdealProximityArm` | as proposed |
| S3+S4 | "It is stated on the cut law rather than on a certificate because it quantifies over every law within eps of that cut: a certificate whose adapter draws this cut is reached at its own shuffle bound, through ic_close read with ic_Hd, and no adapter has to be named here. The weighted-word adapter psl211_word_sample of instances/psl211/psl211_word_model.v draws this cut, and the row published over it in instances/psl211/psl211_word_proximity.v carries a proximity certificate, which has no constancy field for this refutation to touch, so this refutation rules out no proximity row." | `psl211_alldecks_constancy_false_word584`, whose two hypotheses are `var_dist (rho_from_words_weighted …) ideal <= eps` and `(2^-40 + eps) + (2^-40 + eps) < 1/#\|G\|`; `ic_close`/`ic_Hd` as used in `psl211_alldecks_cert_ideal_close`'s proof; `IdealProximityCert`'s five fields | ONE TEXT for both. S3's "covers the ideal of every certificate at once" is gone and replaced by the `ic_close`/`ic_Hd` route; S4's "neither bears on the other" is gone and replaced by the one-directional statement. The eps restriction stays where it already was, in the sentence before. |
| S5+N8 | "…is the ideal this row's certificate is measured against. The two models differ in the law of the cut alone. The two rows differ in the model family and in the transfer status, and they carry different statements, Row 9 exact independence and this row a bound on the distance to that independent model." | `psl211_row_alldecks` (`exact_family`, `StaticExecutedOnly`) against `psl211_row_word` (`word_family`, `IdealFinite`) | ONE TEXT for both. S5's model clause is kept because it is true and is what the file's own header says; N8's "a bound on the distance" is used, not S5's "a distance", per N20. |
| S6 | "The propositions refuted in instances/psl211/psl211_reading_constancy.v are instances of coalition_reading_constancy, which indistinguishability_cert_reading_constancy reads as ic_const, the fifth field of an input-indistinguishability certificate and a field a proximity certificate has no counterpart of. Those refutations stay true beside this row." | `coalition_reading_constancy` is a standalone `Definition`; `indistinguishability_cert_reading_constancy … : coalition_reading_constancy E (ic_ideal cert)` proved by `exact: ic_const cert` | DEVIATION: the auditor wrote "The three refutations"; the cell does not name three and the file carries more than three refutations, so no count is given. |
| S7 | "…so every security statement below is about a static coalition of at most five of the twelve seats…" | `profile_k_psl211_algebra : profile_k (instance_profile psl211_algebra) = 6`, `psl211_exec.v:132` | as proposed |
| S8+N10 | "So the bound var_dist_le2 gives for an arbitrary pair of laws does not reach this number: the term that proves the distance at two is rejected at 2^-40. What carries the number psl211_word_law_le40 proves is psl211_word_mixing." | the quoted rejection, which is about `var_dist_le2 ?P ?Q` alone | ONE TEXT for both. No universal claim over a class of facts is left. |
| S9 | "The certificate's ideal is not convertible with the word model it is about." | the `Fail` is on `erefl` at that equation | as proposed |
| S10 | added: "The bit is not a constant either: psl211_alldecks_secret_expectedE of instances/psl211/psl211_models.v reads it as the value the run recovers at every sample point." | `psl211_alldecks_secret_expectedE (R) (u) : psl211_alldecks_secret R u = ex_expected psl211_alldecks_params ((psl211_alldecks_sample R).(sa_arg) u)`, `psl211_models.v:449` | as proposed |
| S11 | added to the cell: "…; the row's reading is the framework's own sa_coalition_view at word_sample, which the adapter's projections make the all-decks reading, so no facade-level reading bridge is named" | `psl211_word_sample` and `psl211_alldecks_sample` are both `@MkSampleAdapter … (… : finType) … fst snd`; `psl211_word_view_proximity` is stated at `sa_coalition_view … (amf_sample psl211_word_family R tt)` | as proposed |
| S12+N11 | `(* eleven typed rows. The file has EXACTLY ONE Require of any kind, and       *)` | — | 80 bytes, checked. Both reports proposed the same line. |
| S13 | recorded below | — | |
| S14 | recorded below | — | |

### S13 — the reverse closure count

STATUS.md's "The reverse closures" reports nine reverse-dependants of
`instances/psl211/psl211_analysis.v`. The `Require` walk over the tree at
`833acaf` with the landing's staged text gives twelve: the nine of the
design's section 3, plus `five_card_proximity` and
`pgg_tableau_arm_relations` from landings 2 and 3 and `psl211_word_proximity`
from this one. All twelve are among the twenty-two staged files, so the
conclusion the number supports is unaffected.

### S14 — `psl211_endpoints.vo`

The landing never recompiles `instances/psl211/psl211_endpoints.v`. Its `.vo`
is dated 2026-09-17 16:32 and its `.v` 2026-09-18 16:10, at commit `c9634fd`,
whose whole diff to that file adds `Optimize Proof` and `Optimize Heap` lines
inside the proof of `psl211_profile_endpoints` and changes neither the
statement nor the proof term. So nothing this landing measured moves, and the
limit of the evidence is that the compiles and the assumption reports are not
reproducible from the committed sources until that `.vo` is rebuilt.

## C, D, E — the naming findings

| id | disposition |
|---|---|
| N1 | applied; the docstring now carries the fixed sibling's "The manifest writes those coordinates in the facade's vocabulary and the program in this file's, and conversion decides the equation, so the manifest's row for this path is a claim this equation discharges rather than a table maintained beside the program", followed by the two-coordinate difference |
| N2 | applied; the "paper's table" sentence deleted, leaving the fixed sibling's docstring verbatim |
| N3 | applied; header entry now "== the certificate's ideal is the all-decks row's model, and the port built from its witness is that row's port". Checked against the second conjunct `ExactIndependence (ipc_witness …) = ab_port (published_at psl211_row_alldecks_tableau) R idx` |
| N4 | applied; the docstring now says "the port built from the witness the certificate carries is that row's port" |
| N5 | applied; "== the proximity row's security statement, at 2^-40". Checked against the theorem's conclusion `… <= 2%:R^-40` |
| N6 | applied; header "== the certificate's number is 2^-40", docstring "The certificate's number is the 584-letter walk's number, 2^-40." Decimal dropped under N27 |
| N7 | applied; "== below the six-seat threshold, the two models' joint laws of a coalition's reading and the chirality are within 2^-40". Checked against `(#\|C\| < profile_k (instance_profile psl211_algebra))%N ->` and `profile_k … = 6` |
| N9 | applied; `psl211_word_law_tauto` renamed `psl211_word_law_by_var_dist_le2` |
| N12 | applied; `(*   584-letter word sample model             -> word_sample, word_family     *)`, 80 bytes with `->` at column 46, the column of the other thirteen rows |
| N13 | applied; `psl211_word_lawE` renamed `psl211_word_law_le40` at all six mentions: the declaration, the model file's header entry, the `exact:` in `psl211_word_proximity_close`, the comment of the recorded guard, Row 11's model-transfer cell (through `rebase_shared.py`), and `landing_fidelity.v`'s restatement and `Print Assumptions`. `verify.py` gained a `RENAMED` map so the two declarations are still compared against the probe under the probe's name, and three `EXPECTED` entries |
| N14 | applied; both "idealised" are now "idealized" |
| N15 | applied; "the twelve-card chirality instance is the third to publish through that arm" |
| N16 | applied; the duplicated header paragraph deleted. The "one random variable for the two models" clause stays where it already was, in the `psl211_word_sample` docstring |
| N17 | applied; the header paragraph is now "That both laws are written as products is a premise about how the shuffle is performed and not a theorem about the execution: it says the dealer draws the word without seeing the deck", and the repeated clause is dropped from `psl211_wordP`'s docstring, leaving "the two independent by construction" |
| N18 | dissolved by N27: the decimal the "which" attached to is gone, so the sentence is "The two models' laws are within 2^-40 of each other in the sum of absolute differences." |
| N19 | applied; "The ideal, its witness and the secret are terms the all-decks row publishes, and the number is this certificate's own." |
| N20 | applied; "and psl211_word_proximity_close as the distance field, which bounds by that number the distance between the two models' joint laws of a coalition's reading with the chirality" |
| N21 | applied; the timing sentence deleted |
| N22 | applied; the comment moved inside `Proof.` |
| N23 | applied; the two entries now name the number two and `var_dist_le2` inside themselves |
| N24 | applied; "for a sum of absolute differences" |
| N25 | applied; "so which arm a path carries is told from the certificate its table names and not from a field of the record" |
| N26 | applied; "It is the distance field of this instance's proximity certificate" |
| N27 | applied; both decimal literals dropped, `2^-40` throughout |
| N28 | applied in the two new files: `:77` is now "and psl211_word_mixing bounds the distance between the two cut laws by 2^-40", `:110` "the distance the proximity arm bounds". DEVIATION from the note's own suggestion "the whole distance between the two models": 2^-40 is a bound on that distance and not the distance, per N20. `psl211_reading_constancy.v:16` left, per the ruling |
| N29, N30, N31, N32, N35, N37 | clean in the report; nothing to apply |
| N33 | applied; "Its transfer status is IdealFinite: the cut is a shuffle of 584 letters where psl211_row_alldecks draws it uniformly from the group." This also removes one "idealised" |
| N34 | applied; "2^-41" in all three places |
| N36 | applied; the "Word gloss" paragraph is in `psl211_word_model.v` only, and `psl211_word_proximity.v` now opens that paragraph's place with "The word gloss of this instance is in instances/psl211/psl211_word_model.v." |

Nothing was declined.

What the audits asked a fix pass not to lose is all still there:
`psl211_word_law_le2`'s "A proximity certificate carrying two would be a
certificate about nothing", `_cert_secretTE`'s one-point-carrier sentence,
`psl211_word_law_le40`'s "The bound is unconditional and
information-theoretic: it counts the 3^584 words and assumes nothing about an
adversary's resources", and `psl211_row_word_proximity`'s "once twice the sum
of eps and 2^-40 stays below 1/660".

## Chain state at hand-back

`python3 restage.py --check` reports two chain-consistency copies as
**comments only** drift, `staged/lib/var_dist_supp.v` and
`staged/instances/pgl27/pgl27_proximity.v`. Landing 3's fix pass rewrote them
at 04:12 and 04:24, after landing 4's last restage at 03:50. Neither was
copied here, because landing 3 is not yet in production and the main session
reruns `restage.py` after it is. The drift is comments only, so the code every
compile below loaded is the chain's; the fixed `pgl27_proximity.v` text is
nonetheless the text this fix pass diffed the PGL(2,7) roles against, so the
wording adopted for N1 to N7 is landing 3's current wording and not its older
one. The two files landing 4 rebases onto, `pgg_analysis_manifest.v` and
`pgg_analysis_client.v`, are regenerated from landing 3's current text, so
they carry no drift.

## Fix pass 1 — verification

`python3 rebase_shared.py` run twice: the four generated files are byte
identical across the two runs (`cmp` clean on all four), 7, 2, 4 and 5
operations applied, every anchor found exactly once, 0 lines over 80 bytes.

Compiles after the fix pass, one Rocq process at a time through the `rocq1`
lock, `rocq compile -time`, never `make`, and
`instances/psl211/psl211_endpoints.v` never compiled. The seven chain files
before `psl211_word_model.v` in the `_CoqProject` order were not recompiled:
nothing this pass touched is in their forward closure. Wall times include
other sessions' holds on the lock, so the "slow" column is read off the
`-time` lines.

| File | rc | wall | sentences over 5 s |
|---|---|---|---|
| `staged/instances/psl211/psl211_word_model.v` | 0 | 3.8 s | none |
| `staged/instances/psl211/psl211_analysis.v` | 0 | 3.7 s | none |
| `staged/manifest/pgg_analysis_manifest.v` | 0 | 5.9 s | one, 5.218 s, the `Require Export` block |
| `staged/manifest/pgg_tableau.v` | 0 | 13.1 s | none |
| `staged/manifest/pgg_tableau_syntax.v` | 0 | 4.4 s | none |
| `staged/instances/pgl27/pgl27_rows.v` | 0 | 6.4 s | none |
| `staged/instances/kim2025/five_card_rows.v` | 0 | 4.6 s | none |
| `staged/instances/s5/s5_rows.v` | 0 | 4.0 s | none |
| `staged/instances/psl211/psl211_reading_constancy.v` | 0 | 22.7 s | three, 5.186 s, 6.200 s and 6.219 s, all three production's |
| `staged/instances/psl211/psl211_rows.v` | 0 | 5.5 s | none |
| `staged/manifest/pgg_analysis_client.v` | 0 | 3.8 s | none |
| `staged/manifest/pgg_tableau_arm_relations.v` | 0 | 3.7 s | none |
| `staged/instances/kim2025/five_card_proximity.v` | 0 | 5.7 s | none |
| `staged/instances/pgl27/pgl27_proximity.v` | 0 | 5.2 s | none |
| `staged/instances/psl211/psl211_word_proximity.v` | 0 | 4.6 s | none |
| `landing_fidelity.v` | 0 | 269.3 s | thirteen, each a `Print Assumptions` at about 20 s |

The last two rows are a second run of those two files: one header paragraph
of `psl211_word_proximity.v` was rewrapped after the first, so the fidelity
file was recompiled against the final text.

No sentence of a landed file is over 5 s.

`Print Assumptions`, recaptured in `landing_fidelity.out`: 24 `Axioms:`
blocks, each exactly `propositional_extensionality`,
`functional_extensionality_dep` and `constructive_indefinite_description`,
24 occurrences of each name and of no other, no declaration closed under the
global context, and no `Error`, `Axiom`, `Admitted` or `Abort` anywhere in
the run. `psl211_word_law_le40` appears twice, in the restatement and in the
`Print Assumptions` line; `psl211_word_lawE` appears nowhere.

`python3 verify.py`, in `verify.out`:

1. Whole-file token diffs unchanged: `psl211_analysis.v` 3 hunks 14 tokens
   against production, `psl211_reading_constancy.v` 0 hunks,
   `pgg_analysis_manifest.v` 3 hunks 88 tokens and `pgg_analysis_client.v`
   1 hunk 2 tokens against landing 3.
2. `psl211_reading_constancy.v` code tokens identical to production, YES; its
   comment diff is now 5 hunks, 175 words.
3. `psl211_word_model.v` 6 of 7 and `psl211_word_proximity.v` 14 of 17
   token-identical to the probe. The four that differ are all in `EXPECTED`:
   `psl211_row_word_proximity_rowE` as before, and the three the two renames
   touch, compared against the probe under the probe's names through the new
   `RENAMED` map.
4. Comment word diffs: one per rewritten docstring, each mapping to a finding
   of this pass.
5. Scans unchanged from landing 4's own report: every retired and barred
   pattern 0, `indistinguishability` never abbreviated, `ceiling` 8 hits all
   in the chain copy of `five_card_rows.v`, and 4 lines over 80 bytes all in
   chain copies. No landed file has a line over 80 bytes and every box line
   of the six landed files closes at column 80.

Code-token diff of the landed files and `landing_fidelity.v` against
`833acaf`: 2, 0, 0, 0, 0, 4 and 6 tokens, all of them one of the two renames
or a mention of a renamed lemma. No other code token moved.
