# PSL(2,11): the per-instance `tableau/` directory, staged

Probe directory for the PSL(2,11) instance of the per-instance `tableau/`
reorganization. Pattern and rulings: `../2026-09-20-tableau-directories-s5/`
(`staged/TEMPLATE.md`, `audit-s5-pilot.md`, `STATUS.md`). Nothing here is in
production. The main session does the `cp`, the `git rm`, the `_CoqProject`
edit and the comment repoints.

Branch `feat/tableau-extensions-probe`. `make` was never run; every compile
went through `rocq1`, one Rocq process at a time.
`instances/psl211/psl211_endpoints.v` was never compiled and no file of its
forward closure was edited, moved or staged.

## The staged text

```
staged/instances/psl211/psl211_word_proximity.v          reduced, 4 + 1 items
staged/instances/psl211/tableau/psl211_tableau_algebraic.v
staged/instances/psl211/tableau/psl211_tableau_executable.v
staged/instances/psl211/tableau/psl211_tableau_observed.v
staged/instances/psl211/tableau/psl211_tableau_sampled.v
staged/instances/psl211/tableau/psl211_tableau_analysis_bridged.v
staged/instances/psl211/tableau/psl211_tableau_checks.v
```

## Sources and their declaration counts

| Source | Declarations | Of which `Fail` |
|---|---|---|
| `instances/psl211/psl211_rows.v` | 12 | 2 |
| `instances/psl211/psl211_word_proximity.v` | 16 | 3 |

All 28 are accounted for: 23 move into the six phase files, 5 stay in the
reduced `psl211_word_proximity.v`.

## Placement

| Declaration | Source | Phase file | Why |
|---|---|---|---|
| `psl211_algebraic_start` | new | algebraic | the algebra as the first line of a program |
| `psl211_alldecks_executable` | new | executable | the one run mode a program of this instance uses |
| `psl211_alldecks_executable_paramsE` | new | executable | the Executable-phase statement of its own phase (audit ruling 8) |
| `psl211_alldecks_prefix` | rows | observed | a `Tableau Observed` value |
| `psl211_alldecks_executableE` | new | observed | the re-cut equation, named after its non-canonical side |
| `psl211_alldecks_prefix_vm` | rows | observed | a `Tableau Observed` value |
| `psl211_alldecks_prefix_vm_paramsE` | rows | observed | its subject is an Observed value, so no lower file can state it with its tokens unchanged |
| `psl211_alldecks_prefix_lit` | rows | observed | a `Tableau Observed` value |
| `psl211_alldecks_prefix_lit_paramsE` | rows | observed | same reason |
| `psl211_exact_sampled` | new | sampled | one named value per model a program continues from |
| `psl211_word_sampled` | new | sampled | the second model, where the instance branches |
| `psl211_exact_witness` | rows | analysis_bridged | the `ExactWitness` payload `certify_exact` takes |
| `psl211_row_alldecks_tableau` | rows | analysis_bridged | a published row |
| `psl211_row_alldecks_rowE` | rows | analysis_bridged | a statement about that row |
| `psl211_row_alldecks_armE` | rows | analysis_bridged | a statement about that row |
| `psl211_row_alldecks_sampledE` | new | analysis_bridged | the re-cut equation of that row |
| `psl211_alldecks_view_secrecy` | rows | analysis_bridged | the arm's conjuncts, proved by the row's security projection |
| `psl211_word_proximity_cert` | word_proximity | analysis_bridged | a certificate record value |
| `psl211_word_proximity_cert_idealE` | word_proximity | analysis_bridged | a statement about the certificate and about the all-decks row |
| `psl211_word_proximity_cert_secretE` | word_proximity | analysis_bridged | a statement about the certificate |
| `psl211_word_proximity_cert_secretTE` | word_proximity | analysis_bridged | a statement about the certificate |
| `psl211_word_proximity_cert_epsE` | word_proximity | analysis_bridged | a statement about the certificate |
| `psl211_word_proximity_cert_eps_lt2` | word_proximity | analysis_bridged | a statement about the certificate |
| `psl211_row_word_proximity` | word_proximity | analysis_bridged | a published row |
| `psl211_row_word_proximity_armE` | word_proximity | analysis_bridged | a statement about that row |
| `psl211_row_word_proximity_rowE` | word_proximity | analysis_bridged | a statement about that row |
| `psl211_row_word_proximity_sampledE` | new | analysis_bridged | the re-cut equation of that row |
| `psl211_word_view_proximity` | word_proximity | analysis_bridged | the arm's statement, proved by the row's security projection |
| `Fail psl211_alldecks_prefix_vm_neq` | rows | checks | a recorded rejection |
| `Fail psl211_row_vm_reuse` | rows | checks | a recorded rejection |
| `Fail psl211_word_proximity_cert_pgl27_ideal` | word_proximity | checks | a recorded rejection about the certificate |
| `Fail psl211_word_proximity_cert_ideal_self` | word_proximity | checks | a recorded rejection about the certificate |
| `psl211_word_proximity_close` | word_proximity | stays | a distance between two laws |
| `psl211_pow2_40_ge1` | word_proximity | stays | arithmetic of the number |
| `psl211_pow2_40_gt0` | word_proximity | stays | arithmetic of the number |
| `psl211_word_law_le2` | word_proximity | stays | a distance between two laws |
| `Fail psl211_word_law_by_var_dist_le2` | word_proximity | stays | its subject is a distance between two laws and names no certificate |

## The `Require` graph

```
psl211_word_proximity  (reduced, production directory)
        ^
        |
algebraic <- executable <- observed <- sampled <- analysis_bridged <- checks
                                          ^            ^                ^
                                          |            |                |
                          analysis_bridged also imports observed        |
                          checks also imports observed and sampled -----+
```

No file uses `Require Export`. `psl211_tableau_analysis_bridged.v` requires
`psl211_word_proximity` for `psl211_word_proximity_close` and the two `pow2`
facts, so the arrow between the two runs upward from the mathematics into the
tableau. The reduced `psl211_word_proximity.v` requires no tableau module and
no longer requires `psl211_rows`, which is the import the design predicted
would dissolve.

## Compiles

One process at a time through `rocq1`, `-time` read on every run. No sentence
over 5 s in any of the seven files.

| File | rc | wall |
|---|---|---|
| `psl211_word_proximity.v` (reduced) | 0 | 4.6 s |
| `psl211_tableau_algebraic.v` | 0 | 4.4 s |
| `psl211_tableau_executable.v` | 0 | 3.9 s |
| `psl211_tableau_observed.v` | 0 | 4.9 s |
| `psl211_tableau_sampled.v` | 0 | 4.2 s |
| `psl211_tableau_analysis_bridged.v` | 0 | 5.9 s |
| `psl211_tableau_checks.v` | 0 | 4.8 s |

The load path behaved as the template records: under the existing recursive
`-R staged/instances/psl211 pgg_smc`, a file in `tableau/` is
`pgg_smc.tableau.<name>`, `From pgg_smc Require Import <name>` resolves it,
and no `-R` line for the subdirectory was added.

## The four new equations

Each closes by `exact: erefl`; none is `by []` or `done`. The known hazard at
this instance, that a term naming `psl211_alldecks_observed` is large, did not
materialise. Read from `-time`, per file, the slowest sentence of all seven
files is a `From mathcomp Require Import` line at about 1.5 s, and the slowest
sentence that is not an import is 0.988 s, the `vm_compute` prefix definition
in the Observed file.

| File | Sentences | Slowest | Slowest that is not an import |
|---|---|---|---|
| `psl211_word_proximity.v` | 43 | 1.507 s (import) | 0.010 s `exact: var_dist_le2.` |
| `psl211_tableau_algebraic.v` | 16 | 1.502 s (import) | 0.000 s `Definition psl211_algebraic_start` |
| `psl211_tableau_executable.v` | 21 | 1.502 s (import) | 0.002 s `Definition psl211_alldecks_executable` |
| `psl211_tableau_observed.v` | 35 | 1.519 s (import) | 0.988 s `Definition psl211_alldecks_prefix_vm` |
| `psl211_tableau_sampled.v` | 22 | 1.415 s (import) | 0.000 s `Definition psl211_word_sampled` |
| `psl211_tableau_analysis_bridged.v` | 86 | 1.422 s (import) | 0.112 s `exact: (view_secrecy_of …)` |
| `psl211_tableau_checks.v` | 33 | 1.434 s (import) | 0.001 s `Fail Definition …` |

| Equation | File | Closed by |
|---|---|---|
| `psl211_alldecks_executable_paramsE` | executable | `exact: erefl` |
| `psl211_alldecks_executableE` | observed | `exact: erefl` |
| `psl211_row_alldecks_sampledE` | analysis_bridged | `exact: erefl` |
| `psl211_row_word_proximity_sampledE` | analysis_bridged | `exact: erefl` |

No `exact: erefl` in the staged text costs more than 0.112 s, so no prefix had
to be left whole and no conversion lemma was dropped.

## The scope block, and the one re-scoping

Verification rule 3 asks that the innermost `Local Open Scope` be the same in
all six phase files. It is `Local Open Scope ring_scope.` in all six, which is
also production `psl211_rows.v`'s innermost entry.

Production `psl211_word_proximity.v` opens `ring`, `fdist`, `proba`, so its
innermost entry is `proba_scope`, and the twelve declarations that move out of
it are read under `fdist`, `proba`, `entropy`, `ring` in the AnalysisBridged
file instead. That is the one environment change any moved declaration
undergoes. It is pinned, not assumed: `fidelity.v` ascribes each of those
twelve at the statement production gives it, under the AnalysisBridged block,
so a numeral or a notation that resolved differently would be a type error.
`verify.py` prints the re-scoping on every run.

## The `_CoqProject` edit production needs

Replace line 235, `instances/psl211/psl211_rows.v`, with nothing, and insert
the six phase files after line 236, `instances/psl211/psl211_word_proximity.v`,
in phase order. The reduced proximity file must precede the phase files,
because `psl211_tableau_analysis_bridged.v` requires it.

```
instances/psl211/psl211_reading_constancy.v
instances/psl211/psl211_word_proximity.v
instances/psl211/tableau/psl211_tableau_algebraic.v
instances/psl211/tableau/psl211_tableau_executable.v
instances/psl211/tableau/psl211_tableau_observed.v
instances/psl211/tableau/psl211_tableau_sampled.v
instances/psl211/tableau/psl211_tableau_analysis_bridged.v
instances/psl211/tableau/psl211_tableau_checks.v
```

No `-R` line is added or removed.

## Verification

`verify.py`, `gen_fidelity.py` and `run_fidelity.py` are this directory's
copies of the pilot's, adapted to two source files. `stage_edits.py`
generates the three comment repoints under `staged-comments/`.

### `verify.py`, whole output in `verify.out`

```
production items: 29 (12 + 17)
moved or stayed 29, new 8, lost 0
token identity: 29 of 29 declarations identical, 0 intended difference(s)
docstring differs BY DESIGN: psl211_word_proximity_cert_idealE
docstrings: 28 of 29 word-identical, 1 intended difference(s)
the cut: 5 declarations stay in psl211_word_proximity.v, 24 move
innermost scope, all six phase files: Local Open Scope ring_scope.
innermost scope, production psl211_rows.v: Local Open Scope ring_scope.
innermost scope, production psl211_word_proximity.v: Local Open Scope proba_scope.
RE-SCOPED BY DESIGN: ...
scans done
Fail psl211_alldecks_prefix_vm_neq: same rejection
Fail psl211_row_vm_reuse: same rejection
Fail psl211_word_law_by_var_dist_le2: same rejection
Fail psl211_word_proximity_cert_ideal_self: same rejection
Fail psl211_word_proximity_cert_pgl27_ideal: same rejection
ALL CHECKS PASSED
```

Every token of every moved declaration is production's, statement and proof.
The one docstring difference is in `psl211_word_proximity_cert_idealE`, whose
sentence "the ideal a word row is measured against is the model
psl211_rows.v publishes" becomes "... the model the all-decks row publishes":
the retired file name is gone, and the lemma now sits in the same file as
that row, so the citation would otherwise point at the reader's own file.
The script prints the difference on every run.

Each of the five recorded `Fail`s was compiled un-`Fail`ed in the preamble of
the file it sits in, on both sides, production without the staged root and
the staged text with it. The five rejections are byte-identical across the
two sides, and none contains `was not found in the current environment`.

### `fidelity.v` against `baseline.v`

Both ascribe all 24 non-`Fail` declarations of the two source files at their
production statements, and print the assumptions of the two published rows
and of all 17 lemmas, facts and theorems.

| File | rc | wall | `Print Assumptions` blocks |
|---|---|---|---|
| `fidelity.v` (staged text) | 0 | 390.8 s | 19 + 5 for the new declarations |
| `baseline.v` (production) | 0 | 309.3 s | 19 |

`baseline.v` is compiled without `-R staged/instances/psl211 pgg_smc`, so it
loads production's `psl211_word_proximity` and not the reduced copy; a
`Require` resolves to the last matching `-R`.

`diff` of `baseline.out` against the first 322 lines of `fidelity.out`: empty.
The 19 shared assumption reports are byte-identical. The five new reports
carry the same three: `propositional_extensionality`,
`functional_extensionality_dep`, `constructive_indefinite_description`. No
new axiom.

### `stage_edits.py`

```
instances/psl211/psl211_models.v                 1 edit(s)  comment-only=True  over-80=none
instances/psl211/psl211_reading_constancy.v      4 edit(s)  comment-only=True  over-80=none
manifest/pgg_analysis_manifest.v                 2 edit(s)  comment-only=True  over-80=none
```

## Open questions for the main session

1. **Does the reduced `psl211_word_proximity.v` still have a reason to
   exist?** It holds four declarations and one recorded `Fail`, 140 lines
   with its header. Its four declarations are the distance between the two
   models' joint laws, two arithmetic facts about 2^-40, and the tautological
   bound two. `instances/psl211/psl211_word_model.v` is 135 lines and holds
   the word law, its adapter and `psl211_word_law_le40`, which is the fact
   `psl211_word_proximity_close` consumes. Folding the four into that file
   would leave the instance with one file for the word model and its
   distances, and would remove one module from `_CoqProject`. It is not done
   here: the brief asks for the reduced file to be staged and the question
   raised. Nothing else changes either way, because
   `psl211_tableau_analysis_bridged.v` would then require `psl211_word_model`
   for those names, which it already requires.
2. **The two large comment repoints.** `instances/psl211/psl211_models.v` and
   `manifest/pgg_analysis_manifest.v` cost 20 and 17 module recompiles for a
   comment. `staged/RETIRED.md` lists both closures. They can go in a commit
   of their own.
3. **The brief's premise about manifest row 8.** Row 8 is the five-seat
   instance's finite generator word, not a PSL(2,11) row. The manifest's
   PSL(2,11) rows are Row 9, `psl211_row_alldecks`, and Row 11,
   `psl211_row_word`, and both are over the all-decks run. The dealer-dealt
   parameters of `psl211_exec.v` carry no manifest row and no program; what
   is stated at them is `psl211_dealt_constancy_false`. The Executable file's
   header says so and names no value for that mode.
