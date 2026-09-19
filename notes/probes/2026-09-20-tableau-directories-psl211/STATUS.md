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
| `instances/psl211/psl211_word_proximity.v` | 17 | 3 |

All 29 are accounted for: 24 move into the six phase files, 5 stay in the
reduced `psl211_word_proximity.v`.

These three numbers are `verify.py`'s, not hand counts: the script prints
`production items: 29 (12 + 17)` and `the cut: 5 declarations stay in
psl211_word_proximity.v, 24 move`, and the whole output is in `verify.out`.

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
                          checks also imports observed -----------------+
```

The checks file imports `observed` and `analysis_bridged` and not `sampled`:
it uses no name declared at Sampled. Its four rejections reach
`psl211_alldecks_prefix` and `psl211_alldecks_prefix_vm` at Observed,
`psl211_exact_family` and `psl211_word_family` from the model files,
`psl211_exact_witness` and `psl211_word_proximity_cert` at AnalysisBridged,
`psl211_word_proximity_close` from the reduced file, and `pgl27_exact_family`.
At S5 the Sampled import was earned by a bare `Check` of `s5_rand_sampled`;
this instance has no such `Check`, so the import is not taken.

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

Rebuilt in phase order after fix pass 1, all `rc=0`: the reduced proximity
file, then algebraic 3.8 s, executable 3.8 s, observed 4.8 s, sampled 3.9 s,
analysis_bridged 4.7 s, checks 4.4 s. No sentence over 5 s in any of them.

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
and checks files instead. That is the one environment change any moved
declaration undergoes. The other ten moved declarations come from
`psl211_rows.v`, whose block is already the phase files', so they are under no
scope change at all.

**`baseline.v` is the pin, and `fidelity.v` cannot be.** `baseline.v`
`Require`s **production**'s `psl211_rows` and `psl211_word_proximity` and
ascribes their 24 statements under the **phase files'** scope block. Each
constant's type was fixed when production parsed it under production's block;
each ascription text is re-elaborated under the new block; if any notation in
those statements resolved differently under the new stack, the ascription
would be a type error. It compiles, so none does. `fidelity.v` settles a
different question and could not settle this one: it loads the staged phase
files, so the constant's type and the ascription text come from the same
block and the ascription holds whatever that block does. `fidelity.v` pins
that the staged text carries production's statements; `baseline.v` pins that
production's statements mean the same thing under the new block. Both are
needed and both were run. `verify.py` prints the re-scoping on every run.

The rule for the next instance: the baseline file must `Require` the
production modules and open the phase files' scope block, and it is the
baseline file, not the fidelity file, that decides the scope question.

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
and of all 17 lemmas, facts and theorems. `fidelity.v` ascribes the 8 new
declarations as well and, after F12, prints the assumptions of all 8: the 4
new definitions and the 4 new equations. 32 `Check`s and 27 `Print
Assumptions` against baseline's 24 and 19.

| File | rc | wall | `Print Assumptions` blocks |
|---|---|---|---|
| `fidelity.v` (staged text) | 0 | 627.7 s | 27 = 19 + 8 for the new declarations |
| `baseline.v` (production) | 0 | 308.9 s | 19 |

`baseline.v` is compiled without `-R staged/instances/psl211 pgg_smc`, so it
loads production's `psl211_word_proximity` and not the reduced copy; a
`Require` resolves to the last matching `-R`.

`diff` of `baseline.out` against the first 322 lines of `fidelity.out`: empty.
The 19 shared assumption reports are byte-identical. The eight new reports
carry the same three: `propositional_extensionality`,
`functional_extensionality_dep`, `constructive_indefinite_description`. No
report in either file is closed under the global context, and no new axiom
appears.

Three comment re-wraps were made after that compile, in the Executable,
Observed, Sampled and AnalysisBridged headers, to remove short continuation
lines the fix-pass edits left behind. They changed no code: the token diff
against `154c742` is the same after them as before, one dropped import in
the checks file and nothing else, so the chain the fidelity and baseline
compile ran against has the same code tokens as the chain on disk. The chain
was rebuilt in phase order after them, all `rc=0`, and `verify.py` re-run
with byte-identical output.

### `stage_edits.py`

```
instances/psl211/psl211_models.v                 1 edit(s)  comment-only=True  over-80=none
instances/psl211/psl211_reading_constancy.v      4 edit(s)  comment-only=True  over-80=none
manifest/pgg_analysis_manifest.v                 2 edit(s)  comment-only=True  over-80=none
```

## Questions, as ruled

1. **Does the reduced `psl211_word_proximity.v` still have a reason to
   exist? Ruled: yes, and it is not folded into
   `instances/psl211/psl211_word_model.v`.** Folding would be free in module
   terms, since `var_dist_supp` is already in that file's load closure
   through `security/var_dist_joint_law.v`, so the module count is not the
   argument either way. The reason is where the proofs would then sit.
   `psl211_word_proximity.v` is a leaf and gains exactly one importer after
   this batch. `psl211_word_model.v` sits below the facade
   `psl211_analysis.v` and hence below `manifest/pgg_analysis_manifest.v`, a
   reverse closure of about twenty modules; folding moves a coalition-level
   distance and a recorded rejection onto that path, and a recorded rejection
   is the last thing a reader of a model file expects. It would also falsify
   that file's own scope sentence, which says nothing else of the instance is
   restated there. The same ruling carries to PGL(2,7) and five-card: the
   reduced mathematics file stays a file of its own and the tableau directory
   imports it.
2. **The two large comment repoints. Ruled: deferred.** Only the
   `instances/psl211/psl211_reading_constancy.v` repoint goes with this move,
   at a cost of zero recompiles. `instances/psl211/psl211_models.v` and
   `manifest/pgg_analysis_manifest.v` cost 20 and 17 module recompiles for a
   comment and will need the same treatment again at the other two
   instances, so they are deferred to one pass after all four. Their staged
   copies stay in `staged-comments/` and are marked deferred there and in
   `staged/RETIRED.md`.
3. **The brief's premise about manifest row 8.** Row 8 is the five-seat
   instance's finite generator word, not a PSL(2,11) row. The manifest's
   PSL(2,11) rows are Row 9, `psl211_row_alldecks`, and Row 11,
   `psl211_row_word`, and both are over the all-decks run. The dealer-dealt
   parameters of `psl211_exec.v` carry no manifest row and no program. They
   do carry that record's own reconstruction and termination facts, and the
   only security statement made at them is
   `psl211_dealt_constancy_false`. The Executable file's header says exactly
   that and names no value for that mode.

## Notes for whoever does PGL(2,7)

**The two `Local Notation`s are not in any header index.** `seatT` and
`cardT` in `psl211_tableau_analysis_bridged.v`, and `seatT` in the reduced
proximity file, are left out of the `Definitions:` and `Key results:` lists.
The template says to index every non-`Fail` declaration; a `Local Notation`
is not one, and production `psl211_rows.v` and `psl211_word_proximity.v` did
not index theirs either, so this follows the files being moved. S5 had no
`Local Notation` to test the rule against. PGL(2,7) and five-card both have
`Local Notation` blocks: follow this, or settle the rule in the template
once, but do not settle it twice differently.

**The `overriding-logical-loadpath` warnings in `fidelity.err` and
`baseline.err` are an artifact of this probe's `_CoqProject`, not the
template's trap.** The probe binds the staged tree twice, under
`-Q . tableau_dirs_psl211` and then `-R staged/instances/psl211 pgg_smc`. The
remap lands on `pgg_smc.tableau.<name>`, which is the binding production's
existing recursive `-R instances/psl211 pgg_smc` gives, so the resolution
the compile evidence was gathered under is production's. Production has no
second binding and will not emit the warning. This is not the template's rule
about adding an `-R` line for the subdirectory: no such line was added.

**One two-word continuation line in the staged
`psl211_reading_constancy.v`.** The repoint leaves `… carries a` /
`proximity certificate,` inside an 80-column box. It is legal and
comment-only. Re-flowing the surrounding paragraph would make a larger diff
on a file whose reverse closure is empty, so it is left as it is rather than
being an oversight.

## Fix pass 1

After `audit-psl211.md`. Every replacement the auditor proposed was checked
against the declaration it speaks of before it was written; deviations are
recorded per finding. Code tokens of the seven staged `.v` files against
commit `154c742`: identical in six of seven, and in the seventh the only
difference is F10's dropped import, `psl211_tableau_observed
psl211_tableau_sampled.` becoming `psl211_tableau_observed.` (290 tokens to
289).

### F1, MUST, `psl211_tableau_algebraic.v`, docstring of `psl211_algebraic_start`

Checked: `psl211_dealt_params := dealt_secret_params psl211_algebra
psl211_fuel` (`psl211_exec.v:112-113`) takes the algebra, not a `Tableau`
value, so nothing binds it to `psl211_algebraic_start`. Final text:

```
(** The twelve-card chirality instance at the Algebraic level: the algebra
    alone, under True, the proposition that level carries. One run mode is
    built on this value, the all-decks one, and psl211_alldecks_executableE
    is where the prefix both published rows continue from is identified with
    it. The dealer-dealt parameters of psl211_exec.v are built from the same
    algebra and from no program. What separates the run modes is the level
    above and not this one. *)
```

Deviation: the auditor's backticks around identifiers are dropped, because no
comment in the seven files or in production's rows files uses them.

### F2, MUST, `psl211_tableau_executable.v`, header

Checked: `psl211_dealt_recon : instance_recon_stmt psl211_dealt_params`
(`psl211_exec.v:117`) and `psl211_dealt_terminates :
instance_terminates_stmt psl211_dealt_params` (`:123`) are stated at that
record, and `psl211_reading_constancy.v` states eight more. Of those, the one
that is a security statement is `psl211_dealt_constancy_false`; the others
are the reading, fibre and mass computations it is proved from. Final text:

```
(* psl211_exec.v carries a second parameter record, psl211_dealt_params, in   *)
(* the dealer-dealt mode, where the run argument is the secret itself. It     *)
(* carries that record's own reconstruction and termination facts. No         *)
(* program of this development continues from it and the manifest carries no  *)
(* row over it, and the only security statement made at it is the refutation  *)
(* psl211_dealt_constancy_false of psl211_reading_constancy.v. It is named    *)
(* here and not built into a value.                                           *)
```

No deviation.

### F3, MUST, `psl211_tableau_executable.v`, docstring of `psl211_alldecks_executable`

Checked: `StackProp Executable = fun _ => True` (`manifest/pgg_tableau.v:557`),
and the reconstruction fact is the third conjunct of `oe_correct_prop`, which
arrives at Observed. The file's own header already wrote "meant to recover".
Final text, first and second clauses:

```
    the value the run is meant to recover is the chirality bit of its
    argument, and the interpreter is given the instance's budget of 220
    steps. No party commits an input, so the run carries no commit process,
    and the value it names is a reading of the run's own argument rather than
    an ideal function of anyone's input.
```

No deviation.

### F4, MUST, `psl211_tableau_checks.v`, header

Checked both rejections by compiling them un-`Fail`ed. The first is a type
refusal, `SampleAdapter R (OE.oe_execution pgl27_exec.pgl27_observed)`
against `SampleAdapter R (instance_exec psl211_alldecks_params)`. The second
is a conversion failure on an equation about the certificate this file
already has. Final text:

```
(* which ideal the proximity arm admits. A certificate's ideal is a sample    *)
(* adapter over the row's own execution, so the eight-card orbit instance's   *)
(* model is refused at its type and no distance is reached. Beside it, the    *)
(* ideal of the certificate this instance builds is refused as the word model *)
(* the certificate is about; a certificate whose ideal were its own model     *)
(* would hold its distance field at zero, the two sides of that field being   *)
(* one term.                                                                  *)
```

Deviation: the auditor's "Beside it, the ideal of the certificate this
instance builds is refused as the word model the certificate is about" is
kept verbatim; only the line wrap differs.

### F5 to F9, F11, SHOULD

| id | file | what changed | checked against |
|---|---|---|---|
| F5 | sampled header | "computed directly from the layout and the cut" becomes "from the run argument and the cut" | `sampled_viewE_prop` (`pgg_tableau.v:410-420`) and `static_coalition_obs` (`pgg_instance.v:481-490`), which take `x : ex_inputT E` and `g`; the layout is a field of the parameter record |
| F6 | sampled header | "a distance between two members of this level" becomes "a distance between the models that two values of this level carry" | `StackAt Sampled` (`pgg_tableau.v:284-291`) is an algebra with parameters, three run facts and a family, not a law |
| F7 | analysis_bridged header | "every statement here is about a coalition" becomes "every statement here that quantifies over a coalition quantifies over at most five of the twelve seats" | counted: 2 of 17 declarations quantify over a coalition in their statement, 2 more only in a body, 13 name none |
| F8 | checks header | "what that fork costs, that the model" becomes "what that fork rules out: the model" | metaphor noun for a refusal |
| F9 | analysis_bridged index | "the proximity claim, published at 2^-40" becomes "the word row as a program, published at 2^-40" | `psl211_row_word_proximity : PublishedRow`; the claim is `psl211_word_view_proximity`, indexed separately |
| F11 | analysis_bridged `:49`, observed `:13` | both re-wrapped so the right edge reads `… *)` | both were exactly 80 bytes with the text touching `*)` |

No deviations. The F9 re-wrap introduced a 79-column continuation line, which
the width check caught on the next run and which was padded to 80.

### F10, SHOULD, the checks file's Sampled import

Dropped. Confirmed first that the file names neither `psl211_exact_sampled`
nor `psl211_word_sampled`, and that its four rejections reach only Observed,
AnalysisBridged, the model files, the reduced proximity file and
`pgl27_exact_family`.

Verification rule 2 was then re-run, because a `Fail`'s message is a function
of its import list. `verify.out` after the drop is **byte-identical** to the
run before it: all five rejections still match production's exactly, and none
contains `was not found in the current environment`. The three that sit in
the checks file still reject for their recorded reasons, which the file's
docstrings quote:

```
psl211_alldecks_prefix_vm_neq   cannot unify "psl211_alldecks_prefix_vm" and
                                "psl211_alldecks_prefix"
psl211_row_vm_reuse             "psl211_exact_family" has type
                                "AnalysisModelFamily psl211_alldecks_observed"
                                while expected "FamPayload (tableau_at
                                psl211_alldecks_prefix_vm)"
psl211_word_proximity_cert_ideal_self
                                cannot unify "ipc_ideal (…_cert R idx)" and
                                "amf_sample psl211_word_family R idx"
```

### F11 and ruling 8, the right-edge check in `verify.py`

Added beside the width check: a box content line must not end with its last
character touching `*)`, so the two bytes before the closing `*)` are one of
space, `*`, `)`. Both offenders were fixed and the check now passes on all
seven files.

### F12, SHOULD, `Print Assumptions` for the three unprinted definitions

`gen_fidelity.py` now prints the assumptions of `psl211_alldecks_executable`,
`psl211_exact_sampled` and `psl211_word_sampled` as well, so all four new
definitions and all four new equations are printed rather than three of them
resting on the pinning argument alone.

Deviation: the audit says "five new definitions". There are four,
`psl211_algebraic_start`, `psl211_alldecks_executable`,
`psl211_exact_sampled` and `psl211_word_sampled`, of which the first was
already printed and the three the audit names were not. The finding's
substance is unaffected and all four are printed now.

### F13, SHOULD, `staged/RETIRED.md`

`instances/psl211/psl211_word_proximity.v:173` added to the comment table,
marked as already carried by the one intended docstring difference on
`psl211_word_proximity_cert_idealE`. A line added saying `.Makefile.rocq.d`
names `psl211_rows` and is generated by the build.

### F14, F15, F16, NOTE

F14: no change, as ruled. F15 and F16 are recorded above under "Notes for
whoever does PGL(2,7)".

### F17 and F18, SHOULD, this file

F17: the count table now reads 17 and 3 for `psl211_word_proximity.v`, the
total sentence reads 29 and 24, and the paragraph says the numbers are the
script's rather than hand counts. F18: the scope-pin paragraph is rewritten
around `baseline.v`, with why `fidelity.v` cannot settle that question and
the one-line rule for the next instance.

## As built (2026-09-20)

Fix pass 1 was audited by the main session: `verify.py` green (29 of 29
declarations token-identical, 28 of 29 docstrings word-identical with the one
intended difference, five recorded rejections equal to production's), the
final texts of F1 to F4 read against the declarations they cite, and the
staged repoint of `instances/psl211/psl211_reading_constancy.v` confirmed
comment-only by script.

The six staged files were copied with `cp` to `instances/psl211/tableau/`
(`cmp`: byte-identical), `instances/psl211/psl211_word_proximity.v` was
replaced by its reduced text (140 lines), `psl211_reading_constancy.v` received
its comment repoint, and `_CoqProject` lists the six files after
`instances/psl211/psl211_word_proximity.v` in place of
`instances/psl211/psl211_rows.v`, with no `-R` line. The eight files compiled
single-file, all rc=0. `instances/psl211/psl211_rows.v` was then removed with
`git rm` together with its build outputs, and `fidelity.v`, unchanged, was
compiled from a scratch directory against production's load path alone: rc=0,
27 `Axioms:` blocks, each the three classical axioms, none closed, as in the
staged run. `instances/psl211/psl211_endpoints.v` was not compiled.

Deferred to one pass after the four instances: the comment repoints of
`manifest/pgg_analysis_manifest.v` and `instances/psl211/psl211_models.v`,
which still cite `instances/psl211/psl211_rows.v`.
