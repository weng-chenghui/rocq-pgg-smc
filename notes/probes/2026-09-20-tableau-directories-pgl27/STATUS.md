# PGL(2,7): the per-instance `tableau/` directory, staged

Probe directory for the PGL(2,7) instance of the per-instance `tableau/`
reorganization. Pattern and rulings: `../2026-09-20-tableau-directories-s5/`
(`staged/TEMPLATE.md`, `audit-s5-pilot.md`). Scripts and the two-source cut:
`../2026-09-20-tableau-directories-psl211/`. Nothing here is in production.
The main session does the `cp`, the `git rm`, the `_CoqProject` edit and the
comment repoints.

Branch `feat/tableau-extensions-probe`. `make` was never run; every compile
went through `rocq1`, one Rocq process at a time.
`instances/psl211/psl211_endpoints.v` was never compiled and no file of its
forward closure was edited, moved or staged.

## Lines

| File | Lines |
|---|---|
| `pgl27_tableau_algebraic.v` | 61 |
| `pgl27_tableau_executable.v` | 79 |
| `pgl27_tableau_observed.v` | 148 |
| `pgl27_tableau_sampled.v` | 98 |
| `pgl27_tableau_analysis_bridged.v` | 950 |
| `pgl27_tableau_checks.v` | 260 |
| `pgl27_proximity.v` (reduced) | 286 |

Production is 751 plus 624, so 1375 lines become 1882: the six headers and
the section banners are the difference, and no declaration is duplicated.

## The staged text

```
staged/instances/pgl27/pgl27_proximity.v                 reduced, 7 items, 286 lines
staged/instances/pgl27/tableau/pgl27_tableau_algebraic.v
staged/instances/pgl27/tableau/pgl27_tableau_executable.v
staged/instances/pgl27/tableau/pgl27_tableau_observed.v
staged/instances/pgl27/tableau/pgl27_tableau_sampled.v
staged/instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v
staged/instances/pgl27/tableau/pgl27_tableau_checks.v
```

## Sources and their declaration counts

| Source | Declarations | Of which `Fail` |
|---|---|---|
| `instances/pgl27/pgl27_rows.v` | 49 | 8 |
| `instances/pgl27/pgl27_proximity.v` | 26 | 3 |

All 75 are accounted for: 68 move into the six phase files, 7 stay in the
reduced `pgl27_proximity.v`. Nine declarations are new. Every count on
this page is `verify.py`'s, pasted from `verify.out`.

Neither source file holds a `Local Notation`, so the question the
PSL(2,11) audit left open at F16 does not arise here. The rule the next
instance needs is the one production's rows files followed: a
`Local Notation` is not indexed in a header table.

## Placement

| Declaration | Source | Phase file | Why |
|---|---|---|---|
| `pgl27_algebraic_start` | new | algebraic | the algebra as the first line of a program |
| `pgl27_dealt_executable` | new | executable | the one run mode a program of this instance uses |
| `pgl27_dealt_executable_paramsE` | new | executable | the Executable-phase statement of its own phase (audit ruling 8) |
| `pgl27_static_obsE` | rows | stays | its subject is `static_coalition_obs` at `pgl27_dealt_params` and no Tableau value, no run fact and no model appears in it; the distance proof that stays rewrites with it twice |
| `pgl27_static_obs_funE` | rows | stays | the same subject with the cut left free |
| `pgl27_dealt` | rows | observed | a `Tableau Observed` value |
| `pgl27_dealt_executableE` | new | observed | the re-cut equation, named after its non-canonical side |
| `pgl27_inline_dealt` | rows | observed | a `Tableau Observed` value |
| `pgl27_inline_paramsE` | rows | observed | its subject is an Observed value, so no lower file can state it with its tokens unchanged |
| `pgl27_F` | rows | observed | a `Functionality` over `pgl27_observed`, the Observed-phase execution (design question 6) |
| `pgl27_FE` | rows | observed | a statement about that functionality |
| `pgl27_realises_expected` | rows | observed | `realises_expected pgl27_observed pgl27_F`, a statement about the observed execution and about no model |
| `pgl27_exact_sampled` | new | sampled | one named value per model a published program continues from |
| `pgl27_word_sampled` | rows | sampled | a `Tableau Sampled` value, named before the scheme and kept |
| `pgl27_prior_exact_sampled` | new | sampled | the third model, the prior-indexed exact shuffle |
| `pgl27_exact_viewE` | rows | analysis_bridged | a link lemma the exact witness consumes |
| `pgl27_exact_witness` | rows | analysis_bridged | the `ExactWitness` payload `certify_exact` takes |
| `pgl27_exact_leak4` | rows | analysis_bridged | the `leaks at` payload of the exact row |
| `pgl27_word_view_const` | rows | analysis_bridged | the constancy field of the input-indistinguishability certificate |
| `pgl27_word_cert` | rows | analysis_bridged | an `IndistinguishabilityCert` payload |
| `pgl27_row_exact_tableau` | rows | analysis_bridged | a published row |
| `pgl27_row_exact_sampledE` | new | analysis_bridged | the re-cut equation of that row |
| `pgl27_row_word_tableau` | rows | analysis_bridged | a published row |
| `pgl27_row_word_sampledE` | new | analysis_bridged | the re-cut equation of that row |
| `pgl27_row_word_certE` | rows | analysis_bridged | a statement about that row |
| `pgl27_row_exact_rowE` | rows | analysis_bridged | a statement about that row |
| `pgl27_row_word_rowE` | rows | analysis_bridged | a statement about that row |
| `pgl27_row_exact_armE` | rows | analysis_bridged | a statement about that row |
| `pgl27_row_word_armE` | rows | analysis_bridged | a statement about that row |
| `pgl27_reprice39` | rows | analysis_bridged | a `conclude` payload, with the row that uses it (design question 7) |
| `pgl27_row_word39` | rows | analysis_bridged | a published row |
| `pgl27_row_word39_bind` | rows | analysis_bridged | the same row through the raw bind |
| `pgl27_row_word39_bindE` | rows | analysis_bridged | a statement about those two rows |
| `pgl27_row_word39_armE` | rows | analysis_bridged | a statement about that row |
| `pgl27_row_word_branch39` | rows | analysis_bridged | a published row, already written from the named Sampled value |
| `pgl27_row_word_branch39_armE` | rows | analysis_bridged | a statement about that row |
| `pgl27_reprice41` | rows | analysis_bridged | a `conclude` payload, with the statement that refutes its obligation |
| `pgl27_word_reprice41_false` | rows | analysis_bridged | a statement about `pgl27_word_cert`'s number |
| `pgl27_word_target` | rows | analysis_bridged | the proposition the word row is restated as |
| `pgl27_word_bridge` | rows | analysis_bridged | the `restate` payload |
| `pgl27_word_restated` | rows | analysis_bridged | a restated row |
| `pgl27_word_view_indistinguishability_restated` | rows | analysis_bridged | read off that row's theorem field |
| `pgl27_exact_target` | rows | analysis_bridged | the proposition the exact row is restated as |
| `pgl27_exact_bridge` | rows | analysis_bridged | the `restate` payload |
| `pgl27_exact_restated` | rows | analysis_bridged | a restated row |
| `pgl27_exec_exact_view_indep_restated` | rows | analysis_bridged | read off that row's theorem field |
| `pgl27_exact_view_secrecy` | rows | analysis_bridged | the exact arm's four conjuncts, by the row's security projection |
| `pgl27_word_same_statement` | rows | analysis_bridged | a pair type over a published statement and a row's restatement |
| `pgl27_exact_same_statement` | rows | analysis_bridged | the same for the exact row |
| `pgl27_prior_viewE` | proximity | analysis_bridged | a link lemma whose one consumer is `pgl27_prior_exact_witness`; the same object as `pgl27_exact_viewE`, which names a model family |
| `pgl27_prior_exact_witness` | proximity | analysis_bridged | an `ExactWitness` payload |
| `pgl27_row_prior_exact_tableau` | proximity | analysis_bridged | a published row |
| `pgl27_row_prior_exact_sampledE` | new | analysis_bridged | the re-cut equation of that row |
| `pgl27_row_prior_exact_armE` | proximity | analysis_bridged | a statement about that row |
| `pgl27_row_prior_exact_rowE` | proximity | analysis_bridged | a statement about that row |
| `pgl27_word_proximity_cert` | proximity | analysis_bridged | an `IdealProximityCert` payload |
| `pgl27_word_proximity_cert_idealE` | proximity | analysis_bridged | a statement about the certificate and about the prior-indexed row |
| `pgl27_word_proximity_cert_epsE` | proximity | analysis_bridged | a statement about the certificate |
| `pgl27_word_proximity_eps_halfE` | proximity | analysis_bridged | a statement about two certificates |
| `pgl27_word_proximity_le39` | proximity | analysis_bridged | the `conclude` obligation of the proximity row |
| `pgl27_word_proximity_cert_eps_lt2` | proximity | analysis_bridged | a statement about the certificate |
| `pgl27_row_word_proximity` | proximity | analysis_bridged | a published row, already written from the named Sampled value |
| `pgl27_row_word_proximity_rowE` | proximity | analysis_bridged | a statement about that row |
| `pgl27_row_word_proximity_armE` | proximity | analysis_bridged | a statement about that row |
| `pgl27_row_word_families_sampledE` | proximity | analysis_bridged | both rows against the named Sampled value |
| `pgl27_row_word_obs_sampledE` | proximity | analysis_bridged | both rows against the named Sampled value |
| `pgl27_word_view_proximity` | proximity | analysis_bridged | the proximity arm's statement, by the row's security projection |
| `Fail pgl27_row_exact_leak7` | rows | checks | a recorded rejection |
| `Fail pgl27_row_word_arm_neq` | rows | checks | a recorded rejection |
| `pgl27_row_word_arm_neq` | proximity | checks | a comparison of two rows' arms, which the design's Candidate A puts in the checks file; and the `Fail` of the same name must not have it in scope, see "The name that is written twice" |
| `Fail pgl27_inline_neq` | rows | checks | a recorded rejection |
| `Fail pgl27_inline_reuse` | rows | checks | a recorded rejection |
| `Fail pgl27_row_word39_unindexed` | rows | checks | a recorded rejection |
| `Fail pgl27_row_word39_unindexed_bind` | rows | checks | a recorded rejection |
| `Fail pgl27_row_word41` | rows | checks | a recorded rejection |
| `Fail pgl27_word_arm_is_not_exact` | rows | checks | a recorded rejection |
| `Fail pgl27_word_proximity_cert_unit_ideal` | proximity | checks | a recorded rejection about a certificate |
| `Fail pgl27_word_proximity_cert_uniform_ideal` | proximity | checks | a recorded rejection about a certificate |
| `Fail pgl27_cross_model_proximity` | proximity | checks | a recorded rejection about a certificate |
| `pgl27_word_secret` | proximity | stays | the dealt secret as a random variable on the word sample space, used by the certificate above and by the refutation below |
| `pgl27_word_proximity_close` | proximity | stays | a distance between two models' joint laws |
| `pgl27_pow2_40_ge1` | proximity | stays | arithmetic of the number |
| `pgl27_pow2_40_gt0` | proximity | stays | arithmetic of the number |
| `pgl27_word_uniform_ideal_close_false` | proximity | stays | a refutation of a distance bound, inside its own section |

## The two lemmas the mathematics keeps

`pgl27_word_proximity_close` stays, and its proof rewrites with
`pgl27_static_obsE` twice (`instances/pgl27/pgl27_proximity.v:258`, `:268`),
while `pgl27_word_proximity_cert` in the AnalysisBridged file consumes that
distance back. The two identifications of the framework's static reading of a
coalition with `pgl27_view` therefore go into the reduced
`instances/pgl27/pgl27_proximity.v`, at the head of the file, rather than into
a phase file. They are the only declarations of `pgl27_rows.v` that do not
land in `instances/pgl27/tableau/`.

The placement is right on its own terms, not only as a way out of a cycle.
`pgl27_static_obsE` states `@static_coalition_obs pgl27_algebra
pgl27_dealt_params C s g = pgl27_view R C (s, g)`: the only instance objects
in it are the algebra and the run parameter record, and no `Tableau` value, no
run fact and no probability model appears. It is mathematics about the run
parameters, and it now sits beside the distance whose proof uses it.

What this buys is the direction of the arrow. The reduced
`pgl27_proximity.v` requires no tableau module at all, so the mathematics is a
leaf and the tableau directory reads from it. Dropping the two lemmas'
dependency also let the file drop `pgg_tableau`, `pgg_tableau_syntax` and
`pgg_analysis_manifest` from its import list: `static_coalition_obs` is
declared in `protocol/pgg_instance.v`, which the file already required.

## The reduced file's import list

```
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
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
```

Production's list minus `pgl27_rows`, `pgg_tableau`, `pgg_tableau_syntax` and
`pgg_analysis_manifest`, with the mathcomp lines unchanged. Its scope block is
production's, `ring`, `fdist`, `proba`.

## The name that is written twice

`pgl27_rows.v:371` records `Fail Definition pgl27_row_word_arm_neq` and
`pgl27_proximity.v:450` declares `Lemma pgl27_row_word_arm_neq`. In
production the `Fail` is compiled first, in a file where the name is free.
Measured at this toolchain, Rocq checks name freedom before it elaborates the
body:

```
Lemma foo : True. Proof. exact I. Qed.
Definition foo : nat = bool := erefl.
  ->  Error: foo already exists.
```

So a checks file that imported the lemma would record a rejection for the
wrong reason. The lemma is therefore in the checks file too, below its
namesake, which is where the design's Candidate A puts a comparison of two
rows in any case.

## The `Require` graph

```
algebraic <- executable <- observed <- sampled <- analysis_bridged <- checks
                                                       ^                ^
pgl27_proximity (reduced) -----------------------------+                |
                              analysis_bridged also imports observed     |
                              checks also imports observed --------------+
```

No file uses `Require Export`, and every phase import is used:

| File | Phase modules it requires | The names that earn them |
|---|---|---|
| executable | algebraic | `pgl27_algebraic_start` |
| observed | executable | `pgl27_dealt_executable` |
| sampled | observed | `pgl27_dealt` |
| analysis_bridged | observed, sampled | `pgl27_dealt`; `pgl27_exact_sampled`, `pgl27_word_sampled`, `pgl27_prior_exact_sampled` |
| checks | observed, analysis_bridged | `pgl27_dealt`, `pgl27_inline_dealt`; `pgl27_word_proximity_cert`, `pgl27_row_word_proximity`, `pgl27_row_word_branch39`, `pgl27_row_word_tableau` |

`pgl27_tableau_executable` is not required by the AnalysisBridged file and
`pgl27_tableau_sampled` is not required by the checks file, because neither
uses a name those files declare. Both `Fail` checks were re-run after the
imports were trimmed, since a rejection's message is a function of the import
list.

## Compiles

One process at a time through `rocq1`, `-time` read on every run. No sentence
over 5 s in any of the seven files; the slowest sentence anywhere is an
import.

| File | rc | wall | Sentences | Slowest | Slowest that is not an import |
|---|---|---|---|---|---|
| `pgl27_proximity.v` (reduced) | 0 | 4.2 s | 72 | 2.28 s (import) | 0.099 s |
| `pgl27_tableau_algebraic.v` | 0 | 3.8 s | 16 | 1.83 s (import) | 0.001 s |
| `pgl27_tableau_executable.v` | 0 | 3.8 s | 28 | 1.84 s (import) | 0.027 s |
| `pgl27_tableau_observed.v` | 0 | 4.0 s | 36 | 1.86 s (import) | 0.194 s |
| `pgl27_tableau_sampled.v` | 0 | 3.8 s | 20 | 1.88 s (import) | 0.001 s |
| `pgl27_tableau_analysis_bridged.v` | 0 | 7.1 s | 198 | 2.29 s (import) | 0.724 s |
| `pgl27_tableau_checks.v` | 0 | 4.6 s | 45 | 2.33 s (import) | 0.127 s |

The wall time of the reduced file's own run in the last full rebuild reads
263 s, which is time spent waiting on the machine-wide Rocq lock behind
another session; `-time` reports no sentence over 5 s in it.

The load path behaved as the template records: under the existing recursive
`-R staged/instances/pgl27 pgg_smc`, a file in `tableau/` is
`pgg_smc.tableau.<name>`, `From pgg_smc Require Import <name>` resolves it,
and no `-R` line for the subdirectory was added.

## The nine new declarations

Each equation closes by `exact: erefl`; none is `by []` or `done`. The
measured hazard at this instance did not materialise, because every re-cut is
stated against a named value and never row against row: the four equations
cost 0.000 s each, read from `-time`.

| Declaration | File | Closed by | `-time` |
|---|---|---|---|
| `pgl27_algebraic_start` | algebraic | definition | 0.001 s |
| `pgl27_dealt_executable` | executable | definition | 0.002 s |
| `pgl27_dealt_executable_paramsE` | executable | `exact: erefl` | 0.000 s |
| `pgl27_dealt_executableE` | observed | `exact: erefl` | 0.000 s |
| `pgl27_exact_sampled` | sampled | definition | 0.000 s |
| `pgl27_prior_exact_sampled` | sampled | definition | 0.000 s |
| `pgl27_row_exact_sampledE` | analysis_bridged | `exact: erefl` | 0.000 s |
| `pgl27_row_word_sampledE` | analysis_bridged | `exact: erefl` | 0.000 s |
| `pgl27_row_prior_exact_sampledE` | analysis_bridged | `exact: erefl` | 0.000 s |

No re-cut had to be dropped and no prefix had to be left whole at a higher
phase.

`pgl27_row_word39` is the one published row with no `_sampledE` of its own,
and it needs none: `pgl27_row_word_branch39` already is that row written from
`pgl27_word_sampled`, and an equation between the two would be row against
row, the form measured at 48 to 96 s.

## The scope block, and the one re-scoping

Verification rule 3 asks that the innermost `Local Open Scope` be the same in
all six phase files. It is `Local Open Scope ring_scope.` in all six, which is
also production `pgl27_rows.v`'s innermost entry.

Production `pgl27_proximity.v` opens `ring`, `fdist`, `proba`, so its
innermost entry is `proba_scope`, and the 21 declarations that move out of it
are read under `fdist`, `proba`, `entropy`, `ring` in the AnalysisBridged and
checks files instead. That is the one environment change any moved
declaration undergoes. It is pinned, not assumed: `fidelity.v` and
`baseline.v` print the type of every one of them under one scope block and
the two outputs are diffed, so a numeral or a notation that resolved
differently would print differently. `verify.py` prints the re-scoping on
every run.

## The `_CoqProject` edit production needs

Replace line 224, `instances/pgl27/pgl27_rows.v`, with the seven lines below,
and delete line 233, `instances/pgl27/pgl27_proximity.v`, which those seven
lines carry.

```
manifest/pgg_tableau_arm_relations.v
instances/pgl27/pgl27_proximity.v
instances/pgl27/tableau/pgl27_tableau_algebraic.v
instances/pgl27/tableau/pgl27_tableau_executable.v
instances/pgl27/tableau/pgl27_tableau_observed.v
instances/pgl27/tableau/pgl27_tableau_sampled.v
instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v
instances/pgl27/tableau/pgl27_tableau_checks.v
instances/kim2025/five_card_rows.v
```

**The line numbers move.** `224` and `233` are this file's numbers at HEAD
`154c742`. The PSL(2,11) landing is in flight and has already edited
`_CoqProject`, so the main session re-derives both numbers by name at the
time of the `cp` rather than trusting these. Nothing else about the edit
depends on them.

The reduced proximity file moves up from line 233 to sit ahead of all six,
which its one arrow allows and the AnalysisBridged file's `Require` of it
demands. Nothing between its old and its new position depends on it: its
reverse closure is empty, and its own imports name no five-card, S5 or
PSL(2,11) module. No `-R` line is added or removed.

## Verification

`verify.py`, `gen_fidelity.py`, `run_fidelity.py`, `compile.py` and
`stage_edits.py` are this directory's copies of the PSL(2,11) ones.
`gen_phase_files.py` is new: it slices every moved declaration out of
production with its attached comment blocks and emits the seven files, so
token identity and docstring identity are a property of the generator rather
than of a hand edit.

Three additions to `verify.py`, the first two from what this instance has
and PSL(2,11) did not, the third from the PSL(2,11) audit's ruling 8:

1. A declaration's slice runs to the next declaration, so it absorbs any
   `Section`, `Variable`, `Let` or `End` line written between the two. Those
   lines are now compared separately, by `scaffolding()`, which asserts that
   the reduced proximity file's four are production's four and that no phase
   file holds any. Without it two declarations would have shown a token
   difference for scaffolding that did not move.
2. The un-`Fail`ed bodies are read out of the production sources rather than
   transcribed, so that table cannot drift from them.
3. A box content line must end with a space before `*)`. A width check does
   not see a line that is exactly 80 bytes with its text abutting the close,
   which is what the PSL(2,11) audit found twice at F11. The generator
   enforces the same bound by wrapping to 74 columns and asserting 77.

### `verify.py`, whole output in `verify.out`

```
production items: 75 (49 + 26)
moved or stayed 75, new 9, lost 0
token identity: 75 of 75 declarations identical, 0 intended difference(s)
docstrings: 70 of 73 word-identical, 3 intended difference(s)
the cut: 7 declarations stay in pgl27_proximity.v, 68 move
section scaffolding of pgl27_proximity.v: 4 line(s), unchanged
innermost scope, all six phase files: Local Open Scope ring_scope.
innermost scope, production pgl27_rows.v: Local Open Scope ring_scope.
innermost scope, production pgl27_proximity.v: Local Open Scope proba_scope.
RE-SCOPED BY DESIGN: ...
RE-SCOPED THE OTHER WAY BY DESIGN: ...
scans done
Fail pgl27_cross_model_proximity: same rejection
Fail pgl27_inline_neq: same rejection
Fail pgl27_inline_reuse: same rejection
Fail pgl27_row_exact_leak7: same rejection
Fail pgl27_row_word39_unindexed: same rejection
Fail pgl27_row_word39_unindexed_bind: same rejection
Fail pgl27_row_word41: same rejection
Fail pgl27_row_word_arm_neq: same rejection
Fail pgl27_word_arm_is_not_exact: same rejection
Fail pgl27_word_proximity_cert_uniform_ideal: same rejection
Fail pgl27_word_proximity_cert_unit_ideal: same rejection
ALL CHECKS PASSED
```

Every token of every moved declaration is production's, statement and proof.
Each of the eleven recorded `Fail`s was compiled un-`Fail`ed in the preamble
of the file it sits in, on both sides, production without the staged root and
the staged text with it. The eleven rejections are byte-identical across the
two sides, and none contains `was not found in the current environment`.

The three intended docstring differences, each printed on every run:

| Declaration | What changes | Why |
|---|---|---|
| `pgl27_word_proximity_cert` | "and the distance above" becomes "and the distance pgl27_word_proximity_close of pgl27_proximity.v" | the distance is no longer above the certificate but in the file this one requires |
| `pgl27_row_word_proximity_rowE` | "as pgl27_row_word_rowE of pgl27_rows.v says" becomes "as pgl27_row_word_rowE says" | the retired file name is gone and the lemma now sits beside the one it cites |
| `Fail pgl27_word_proximity_cert_uniform_ideal` | "pgl27_word_uniform_ideal_close_false above" becomes "pgl27_word_uniform_ideal_close_false of pgl27_proximity.v" | the refutation stays in the reduced file and this rejection moves to the checks file |

### `fidelity.v` against `baseline.v`

Both print the type of all 64 non-`Fail` declarations of the two source files
under one scope block, and print the assumptions of the seven published rows
and of all 40 lemmas, facts and theorems. `fidelity.v` prints nine more types
and nine more assumption reports, one per new declaration, including the four
new `Definition`s, which the PSL(2,11) audit's ruling 9 asks for because a
type alone would pass on a wrong body. The name lists are read out of
production by `gen_fidelity.py`, so nothing is ascribed by hand and nothing
can be left out by hand.

**`baseline.v` is the scope pin, not `fidelity.v`.** `baseline.v` requires
production's `pgl27_rows` and `pgl27_proximity` and prints their types under
the phase files' scope block, so each constant's type comes from production's
parse and the printing from the new block; a notation that resolved
differently would print differently there. `fidelity.v` cannot settle that
question on its own, because it loads the staged files and both sides come
from one block. The two are needed together, and it is the pairing that makes
the diff mean anything.

| File | rc | wall | `Check` | `Print Assumptions` |
|---|---|---|---|---|
| `fidelity.v` (staged text) | 0 | 121.4 s | 73 | 56 |
| `baseline.v` (production) | 0 | 51.0 s | 64 | 47 |

`baseline.v` is compiled without `-R staged/instances/pgl27 pgg_smc`, so it
loads production's `pgl27_proximity` and not the reduced copy; a `Require`
resolves to the last matching `-R`.

`diff` of `baseline.out` against the first 614 lines of `fidelity.out`:
**empty**. All 64 printed types and all 47 assumption reports are
byte-identical, so no statement changed meaning under the new imports and the
new scope block, and no moved declaration gained or lost an axiom. The nine
reports for the new declarations carry the same three:
`propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description`. No new axiom.

The re-scoping runs both ways at this instance and the diff covers both.
Twenty-one declarations move out of `pgl27_proximity.v`, whose innermost
scope is `proba_scope`, into the phase files, whose innermost is
`ring_scope`; and `pgl27_static_obsE` and `pgl27_static_obs_funE` move the
other way, out of `pgl27_rows.v` into `pgl27_proximity.v`. `verify.py` prints
both directions on every run.

### `stage_edits.py`, DEFERRED

```
instances/pgl27/pgl27_encoding_r5.v              1 edit(s)  comment-only=True  over-80=none
manifest/pgg_analysis_manifest.v                 2 edit(s)  comment-only=True  over-80=none
```

Both staged under `staged-comments/`, never under `staged/`, which is an
`-R` root. **Neither is applied with this instance.** Both wait for one pass
after all four instances have landed, so the manifest is recompiled once
rather than four times. `staged/RETIRED.md` lists both reverse closures: four
modules for the first and seventeen for the second, twenty-two after the
move.

## Rulings taken

| Question | Ruling | What it changed here |
|---|---|---|
| Where `pgl27_static_obsE` and `pgl27_static_obs_funE` live | the mathematics imports no tableau file | both lemmas are in the reduced `pgl27_proximity.v`, which now requires no tableau module and drops `pgg_tableau`, `pgg_tableau_syntax` and `pgg_analysis_manifest`; the `_CoqProject` order puts it ahead of all six phase files |
| `Lemma pgl27_row_word_arm_neq` in the checks file | accepted | the checks header states the fact and the reason the order matters |
| The two comment repoints | deferred to one pass after all four instances | marked deferred here and in `staged/RETIRED.md`; the staged copies are unchanged |
| No `_sampledE` for `pgl27_row_word39` | accepted | nothing row against row anywhere in the staged text |

## Pre-audit pass

Read against `notes/probes/2026-09-20-tableau-directories-psl211/audit-psl211.md`
(F1 to F18 and the twelve rulings) and the second addendum of `TEMPLATE.md`.
Each row is one sentence of new text and the declaration or object it was
checked against.

| Ruling | File | Before | After | Checked against |
|---|---|---|---|---|
| 1 | observed header | "realises_expected is an equation between that execution's recovered value and the functionality's function" | "…between the value that execution names as the one to recover and the functionality's function" | `realises_expected` relates `oe_expected` to the functionality's function; recovery is the third conjunct of `oe_correct_prop` and is a separate fact |
| F1 | algebraic docstring | "One run mode continues from this value, the dealer-dealt run" | "One run mode is built on this value, the dealer-dealt one, and pgl27_dealt_executableE is where the prefix all seven published rows continue from is identified with it" | `pgl27_dealt` is written through the keyword surface from `pgl27_algebra` and reaches the named Algebraic value only through that equation |
| F1 | algebraic header | "All seven published rows of this instance begin here" | "All seven published rows of this instance begin at that algebra" | the same |
| 5 | algebraic header | "every coalition statement above this file is about at most three of the eight seats" | "every statement above this file that quantifies over a coalition quantifies over at most three of the eight seats" | most declarations above quantify over no coalition |
| 5 | analysis_bridged header | "Four is the threshold, so every coalition statement here is about at most three of the eight seats" | "Four is the threshold the derived profile declares, so every statement here that quantifies over a coalition quantifies over at most three of the eight seats, each seat reading the card at its own position" | of the 53 declarations in that file, only `pgl27_exact_leak4`, `pgl27_word_view_const`, `pgl27_word_target`, `pgl27_exact_target`, the two restated theorems, `pgl27_exact_view_secrecy`, `pgl27_word_view_proximity` and the two `_same_statement` pairs quantify over a coalition |
| 4 | sampled header | "the reader … is the one computed directly from the layout and the cut" | "…from the run argument and the cut" | `static_coalition_obs` takes `x : ex_inputT E` and `g`; the layout is a field of the parameter record |
| 10 | analysis_bridged index | `pgl27_row_word_proximity == the proximity claim, concluded at 2^-39` | `== the word row as a program at the proximity arm, concluded at 2^-39` | its type is `PublishedRowAt pgl27_reprice39`; the claim is `pgl27_word_view_proximity`, indexed separately |
| 3 | checks header | "Two of its three rejections turn on the index type … What refutes the distance field itself, rather than refusing a spelling of it, is …" | "…its three rejections have two causes. Two are refused at the index type … The third is well typed at its index and refused at its distance field, whose proof relates the word model at one law of the secret to the exact model at that same law and not to the exact model at the uniform one." | `pgl27_word_proximity_cert_unit_ideal` and `pgl27_cross_model_proximity` are index-type refusals; `pgl27_word_proximity_cert_uniform_ideal` is refused at the distance field, as its own moved docstring says |
| 2 | checks header | new sentence | "One lemma of this file shares its name with the rejection recorded above it, and the order is what lets both compile. Rocq checks that a name is free before it elaborates a body…" | measured: `Lemma foo : True.` then `Definition foo : nat = bool := erefl.` gives `Error: foo already exists.` |
| 7 | analysis_bridged, checks preambles | both required a phase file whose names they do not use | `pgl27_tableau_executable` dropped from the AnalysisBridged file, `pgl27_tableau_sampled` from the checks file | name-set check per file; all eleven `Fail` rejections re-run and still byte-identical |
| 8 | the generator | box content wrapped to 75 columns, so a line could abut `*)` | wrapped to 74, asserted at 77, and `verify.py` now fails a box content line that does not end in a space | audit F11 |
| 9 | `gen_fidelity.py` | `Print Assumptions` for the five new equations only | all nine new declarations, the four new `Definition`s included | audit F12 |
| 11 | this file | the scope pin credited to `fidelity.v` | credited to `baseline.v`, with the reason the pairing matters | audit F18 |
| 12 | this file | counts written by hand | every count is `verify.py`'s, pasted | audit F17 |
| Q1 | executable header, reduced header | the Executable file claimed the two reader lemmas | the Executable header names where they are and why; the reduced header says the file requires no tableau module | the ruling |

Two things the pass checked and left alone. `pgl27_exact_leak4`'s moved
docstring says "four seats of this instance leak the secret", which is
production's text and is true of the one coalition the lemma exhibits, as its
own next sentence says. The reduced file's second paragraph opens "The other
distance runs the other way", and the object it names, the refutation, is a
statement about a distance bounded below rather than above, so the noun is
right.

## What no phase header claims

The manifest carries exactly three `AnalysisPathRow`s over this instance,
`pgl27_row_exact` (`manifest/pgg_analysis_manifest.v:962`), `pgl27_row_word`
(`:973`) and `pgl27_row_prior_exact` (`:1085`), and a program of this
development publishes each of them, discharged by `pgl27_row_exact_rowE`,
`pgl27_row_word_rowE` and `pgl27_row_prior_exact_rowE`. So no header has to
name a row the manifest publishes by another route, which is the case S5's F1
and F2 and PSL(2,11)'s F2 were about, and none claims that a row does not
exist because a program does not.

The instance has exactly three analysis model families, and all three are
named in the Sampled file, so no header says a model is unnamed.
