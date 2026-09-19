# S5 pilot of the per-instance `tableau/` directory: staged text

Date 2026-09-20. Repository `rocq-pgg-smc`, branch `feat/tableau-extensions-probe`,
HEAD `6f3612e`. Nothing in `manifest/`, `instances/`, `lib/`, `security/` or
`_CoqProject` was edited. Everything is under this directory.

Source of the plan: `notes/2026-09-20-060000-instance-tableau-directory-design.md`,
Candidate A, and its last section "Orchestrator's decisions", which supersedes
the rest.

## Step 0: the load path of a `tableau/` subdirectory

Production maps `-R instances/s5 pgg_smc`, and `-R` is recursive. The probe put
`s5_tableau_algebraic.v` in `staged/instances/s5/tableau/` under a mirrored
`-R staged/instances/s5 pgg_smc`, compiled it, and compiled a second file
`step0.v` that requires it by its short name.

(a) **Logical name.** `pgg_smc.tableau.s5_tableau_algebraic`. The directory
component is inserted, exactly as design question 1 predicted. Evidence:
`Print Libraries` in `step0.v` prints

```
  pgg_smc.tableau.s5_tableau_algebraic
```

(b) **Short `Require` resolves it.** `From pgg_smc Require Import
s5_tableau_algebraic.` compiles with `rc=0` and loads that module. A `Require`
matches a prefix of the root and a suffix of the name, and `pgg_smc` +
`s5_tableau_algebraic` is such a pair for `pgg_smc.tableau.s5_tableau_algebraic`.
No source anywhere writes a fully qualified `pgg_smc.<module>.<ident>`, so no
cited name changes.

(c) **Warnings.** In the production shape — one `-R` on the instance directory,
no other root over the same files — the compile emits **no warning at all**.
The command run, verbatim:

```
<rocq1 lock> 300 4000 rocq compile \
  -w -projection-no-head-constant -w -redundant-canonical-projection \
  -w -notation-overridden -w -ambiguous-paths -w -notation-incompatible-format \
  -R staged/instances/s5 pgg_smc step0.v
```

Production's `-arg -w -arg -ambiguous-paths` line (`_CoqProject:4`) is therefore
**not** what makes the subdirectory work; nothing needs silencing. The warnings
this probe does show are `overriding-logical-loadpath`, a different warning,
and they come from this probe's own `-Q . tableau_dirs_s5` line, which binds
`staged/` under the probe root before the staged `-R` lines rebind it. That
ordering is required (landing 1 of the extensions measured it) and the warning
is a probe artifact with `rc=0`; `Print Libraries` confirms the staged module is
the one loaded.

(d) **An extra `-R instances/s5/tableau pgg_smc` line is harmful.** Adding it
remaps the directory and warns:

```
Warning: .../staged/instances/s5/tableau
was previously bound to pgg_smc.tableau; it is remapped to pgg_smc
[overriding-logical-loadpath,filesystem,default]
```

and against a `.vo` built without the line the compile then fails outright:

```
Error: .../s5_tableau_algebraic.vo contains library
pgg_smc.tableau.s5_tableau_algebraic and not library
pgg_smc.s5_tableau_algebraic.
```

**Decision: add no `-R` line.** The subdirectory works cleanly under the
existing recursive root. Design question 1 takes its stated default and the
flat-file fallback is not needed.

(e) **zsh trap, for whoever repeats this.** `$FLAGS` is not word-split by zsh;
`rocq compile $FLAGS f.v` reports `Unknown option -w -projection-...` as if the
whole string were one flag. Write `${=FLAGS}`, or use `compile.py`, which passes
a list.

## The `_CoqProject` edit production needs

Lines to add, at the end of the file list, in this order (each phase file after
the one it imports), replacing the single line `instances/s5/s5_rows.v`:

```
instances/s5/tableau/s5_tableau_algebraic.v
instances/s5/tableau/s5_tableau_executable.v
instances/s5/tableau/s5_tableau_observed.v
instances/s5/tableau/s5_tableau_sampled.v
instances/s5/tableau/s5_tableau_analysis_bridged.v
instances/s5/tableau/s5_tableau_checks.v
```

Line to remove: `instances/s5/s5_rows.v` (production `_CoqProject:226` at this
HEAD; it sits between `instances/kim2025/five_card_rows.v` and
`instances/kim2025/five_card_proximity.v`).

`-R` lines: **none added, none removed**, per step 0(d).

Ordering constraint: `instances/kim2025/five_card_proximity.v` requires the S5
material, so the six lines go before it. Placing them where
`instances/s5/s5_rows.v` stands satisfies that.

## Files staged, and what is in each

The names and counts in this section and in the three that follow are the
first pass's. Fix pass 1, at the end of this file, renames four
declarations, adds two more and supersedes them.

| File | Items | New | Moved | Names |
|---|---|---|---|---|
| `s5_tableau_algebraic.v` | 1 | 1 | 0 | new `s5_algebraic` |
| `s5_tableau_executable.v` | 2 | 2 | 0 | new `s5_dealt_executable`, `s5_supplied_executable` |
| `s5_tableau_observed.v` | 13 | 2 | 11 | moved `s5_dealt`, `s5_dealt_row_observedE`, `s5_supplied`, `s5_supplied_paramsE`, `s5_F`, `s5_FE`, `s5_F_thresholdE`, `s5_realises_expected`, `s5_rand_F`, `s5_rand_FE`, `s5_rand_realises_expected`; new `s5_dealt_splitE`, `s5_supplied_splitE` |
| `s5_tableau_sampled.v` | 1 | 1 | 0 | new `s5_rand_sampled` |
| `s5_tableau_analysis_bridged.v` | 8 | 1 | 7 | moved `s5_rand_static_obsE`, `s5_rand_static_obs_indep`, `s5_rand_exact_witness`, `s5_row_rand_tableau`, `s5_row_rand_rowE`, `s5_row_rand_armE`, `s5_rand_view_secrecy`; new `s5_row_rand_splitE` |
| `s5_tableau_checks.v` | 3 | 0 | 3 | moved: the bare `Check`, `Fail s5_dealt_rand`, `Fail s5_F_k5` |
| `staged/instances/kim2025/five_card_proximity.v` | — | — | — | production's text, one `Require` repointed |

`s5_rows.v` has 21 items: 18 declarations, two recorded `Fail`s and one bare
`Check`. 11 + 7 + 3 = 21, so every item lands in exactly one file, and 7 new
declarations are added.

`Require` graph, each file importing the one before it:

```
s5_tableau_algebraic
  <- s5_tableau_executable
       <- s5_tableau_observed
            <- s5_tableau_sampled
                 <- s5_tableau_analysis_bridged
                      <- s5_tableau_checks
                      <- (production) instances/kim2025/five_card_proximity.v
```

A `Require Import` is not transitive for `Import`, so a file that needs a name
from a phase two levels down names that phase too:
`s5_tableau_analysis_bridged.v` imports `s5_tableau_observed` as well as
`s5_tableau_sampled` (it states `s5_row_rand_tableau` from `s5_supplied`), and
`s5_tableau_checks.v` imports all three of observed, sampled and
analysis_bridged. Leaving that out is a compile error, not a silent miss.

## Compile

One Rocq process at a time, through the `rocq1` lock, `rocq compile` directly.
`make` was never run. Nothing was written into a production directory.

| File | rc | wall | sentences over 5 s |
|---|---|---|---|
| `s5_tableau_algebraic.v` | 0 | 3.3 s | none |
| `s5_tableau_executable.v` | 0 | 3.3 s | none |
| `s5_tableau_observed.v` | 0 | 3.8 s | none |
| `s5_tableau_sampled.v` | 0 | 3.4 s | none |
| `s5_tableau_analysis_bridged.v` | 0 | 3.9 s | none |
| `s5_tableau_checks.v` | 0 | 3.4 s | none |
| `staged/…/five_card_proximity.v` | 0 | 5.7 s | none |
| `fidelity.v` | 0 | — | none |
| `baseline.v` | 0 | — | none |

One warning is emitted, `notation-incompatible-prefix` on `_ <| _ |> _` against
`_ <| _`. It is emitted identically by `baseline.v`, which requires production's
`s5_rows` and no staged file, so it is a property of the import set and is not
introduced here.

## The three conversion lemmas

All three close by `exact: erefl`, and `-time` puts each at 0.000 s, so none is
near the 5 s reading threshold or the 30 s abandon threshold. `by []` and
`done` were not used anywhere: a `by []` over a `published_at` equation has been
measured at 683 s against 0.13 s for `exact: erefl`.

| Lemma | File | Statement | Time |
|---|---|---|---|
| `s5_dealt_splitE` | observed | `s5_dealt_executable execute … = s5_dealt` | 0.000 s |
| `s5_supplied_splitE` | observed | `s5_supplied_executable execute … = s5_supplied` | 0.000 s |
| `s5_row_rand_splitE` | analysis_bridged | `s5_rand_sampled certify … \|> publish … = s5_row_rand_tableau` | 0.000 s |

Nothing was abandoned and no prefix was left whole for want of a conversion.
The Algebraic-to-Executable edge is written with the raw bind `;;;`, because
the keyword rules `dealt`, `encoded` and `supplied` each begin at a
`PGGAlgebraic` and none of them continues a named `Tableau Algebraic` value.
The elaboration works: `s5_algebraic ;;; dealt_step of 150` and
`s5_algebraic ;;; params_step of (supplied_input_params …)` both typecheck, and
`params_step` passes its stack slot correctly under this file's
`Unset Strict Implicit` because `pgg_tableau_syntax.v` carries
`Arguments params_step : clear implicits`.

## verify.py

`python3 verify.py` exits 0. What it reports:

```
production items: 21
moved 21, new 7, lost 0
token identity: 21 of 21 moved declarations identical
docstrings: 18 of 18 word-identical
scans done
Fail s5_F_k5: same rejection
Fail s5_dealt_rand: same rejection
ALL CHECKS PASSED
```

Checks it makes: name sets equal with nothing lost and nothing duplicated
across the six files; comment-stripped token-stream identity per declaration,
statement and proof; docstring word identity; per-file scans for lines over 80
bytes, box lines away from column 80, the banned vocabulary and abbreviations
of "indistinguishability"; and, for each recorded `Fail`, an un-`Fail`ed copy
compiled from production and from the staged text with the two rejections
compared.

The `Fail` check compiles each un-`Fail`ed term in the preamble of the file the
`Fail` actually sits in, not in a preamble of the script's own choosing. That
distinction caught a real defect, below.

Rejections, identical on both sides:

```
s5_F_k5      Error: The term "erefl" has type "s5_F = s5_F" while it is
                    expected to have type "s5_F = {| fn_f := id;
                    fn_threshold := 5 |}"
s5_dealt_rand Error: The term "s5_rand_family" has type
                    "AnalysisModelFamily s5_rand_observed" while it is
                    expected to have type "FamPayload (tableau_at s5_dealt)"
```

### Three defects the verification caught

1. **A `Fail` that passed for the wrong reason.** The checks file's first
   import line did not bring `ssrfun` in, so `erefl` did not resolve and
   `Fail Definition s5_F_k5 … := erefl` was rejected with
   `The reference erefl was not found in the current environment` instead of
   the coalition-size mismatch it records. Production's `s5_rows.v` gets
   `erefl` through the longer import list it needs for the security material.
   Fixed by adding `ssrfun` to `s5_tableau_checks.v`. This is item 10 of the
   extensions' as-built note reproduced exactly: a `Fail` whose subject no
   longer resolves passes silently and proves nothing.
2. **Two box lines at 79 columns** rather than 80, in the observed and
   analysis_bridged headers. Fixed.
3. **A stale `.vo` in the middle of the chain.** Rebuilding
   `s5_tableau_observed.v` after `s5_tableau_sampled.vo` already existed gave
   `makes inconsistent assumptions over library pgg_smc.tableau.…`. The chain
   must be rebuilt in phase order.
4. **A box-column repair that a length check cannot see.** The first attempt
   at defect 2 stripped one character and appended `*)`, leaving `**)` at the
   end of two header lines. The line was then exactly 80 columns, so the
   column check passed and the defect survived a green compile and a green
   `verify.py`. It was found by eye, in a `grep` for `**)`. `verify.py` now
   also rejects a non-banner box line ending in a stray asterisk. A width
   check is not a shape check.

## fidelity.v and the Print Assumptions diff

`fidelity.v` and `baseline.v` are generated by `gen_fidelity.py` from one
shared body, so their only difference is the `Require` line: `fidelity.v`
takes the six staged phase files, `baseline.v` takes production's `s5_rows`.
Both ascribe all 18 declarations at production's statements, so a lost or
altered declaration is a compile error, and both `Print Assumptions` the
published row and every lemma and theorem.

Both compile with `rc=0`. The 94 lines of assumption output are **byte
identical** between the two. Every one of the 14 names rests on

```
Axioms:
rigidity_s5_instance.s5_group_order_eq :
  #|pgg_G (Gen_PGGTypes (pgg_raag_path.path_gen_tuple 3))| = 120
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep : …
constructive_indefinite_description : …
```

except `s5_F_thresholdE`, which is `Closed under the global context`, and
`s5_realises_expected`, `s5_rand_FE`, `s5_rand_realises_expected` and
`s5_FE`, which carry `s5_group_order_eq` alone. The three boolp axioms are the
fdist-record section floor and the group-order axiom is the S5 row's own, as
the manifest's `AcceptsAxioms [:: AxS5GroupOrder]` records.

`fidelity.v` additionally ascribes the seven new declarations and prints the
assumptions of the three conversion lemmas. Each carries the same four axioms
as the row they relate, and no axiom the staged text introduces.

## Decisions taken, and why

1. **`s5_supplied_paramsE` is in the Observed file, not the Executable file.**
   The design's table of what each phase can hold puts it at Executable. Its
   statement is `projT1 (projT2 (tableau_at s5_supplied)) = s5_supplied_params`
   and it names `s5_supplied`, which is an Observed value, so placing it in the
   Executable file would either invert the import order or change its
   statement. The pure-move rule governs: it moved with its tokens unchanged
   into the first file that can state it.
2. **The word model is not named at Sampled.** No row of the instance
   continues from `s5_word_family`, and the instance's own record says two of
   the five parts of an input-indistinguishability certificate over it are out
   of reach. Naming a value nothing continues from would put an object in the
   phase list that the phase does not reach. The reasoning moved into the
   header of `s5_tableau_sampled.v`, which is where a reader looking for the
   second model now finds why it is absent.
3. **Scope and settings blocks are not uniform across the six files.** Every
   file carries `Set Implicit Arguments`, `Unset Strict Implicit`,
   `Import Prenex Implicits` and `Import GRing.Theory Num.Theory`, because
   `Unset Strict Implicit` changes how the binds elaborate and the moved text
   was written under it. The four `Local Open Scope` lines of `s5_rows.v` are
   kept whole only where distributions appear, in the analysis_bridged and
   checks files; the lower four open `ring_scope` alone, which is the innermost
   of the four and therefore the one that decides a numeral. Those four files
   add `ssralg ssrnum` to the mathcomp import line, which `s5_rows.v` did not
   need because infotheo's `fdist` pulled `GRing` in for it.
4. **No `-R` line is added**, per step 0(d).

## Open questions for the owner

1. **The bare `Check` is now redundant.** `Check (s5_supplied sample
   s5_rand_family : Tableau Sampled)` in the checks file has exactly the body
   of `s5_rand_sampled` in the sampled file. It was kept, as the default says,
   because it is a pure move and because it is the positive half of the pair
   whose negative is `Fail s5_dealt_rand` directly beneath it. Dropping it
   would leave the `Fail` without the contrast it was written against.
   Alternative: replace the `Check` with `Check (s5_rand_sampled : Tableau
   Sampled)`, which is a token change and so outside the pure-move rule.
2. **Naming.** The new values are `s5_algebraic`, `s5_dealt_executable`,
   `s5_supplied_executable` and `s5_rand_sampled`, following the tree's one
   precedent for a named phase value, `pgl27_word_sampled` in
   `instances/pgl27/pgl27_rows.v:485`, which is `<instance>_<mode>_<phase>`.
   `s5_algebraic` sits one letter from `s5_algebra`, the object it names.
3. **The conversion lemma names** are `_splitE`, which is the spelling the
   design note used. The tree has no `_splitE` yet.
4. **`instances/kim2025/five_card_rows.v:59`** cites the retired file in a
   comment and needs a one-line edit the main session makes; see
   `staged/RETIRED.md`. No staged copy of that file is in this directory.

# Fix pass 1, after `audit-s5-pilot.md`

This section supersedes the counts and names above. The pattern as ruled is
written out separately in `staged/TEMPLATE.md`, for the next instance.

## Final counts

| File | Items | New | Moved |
|---|---|---|---|
| `s5_tableau_algebraic.v` | 1 | `s5_algebraic_start` | — |
| `s5_tableau_executable.v` | 4 | `s5_dealt_executable`, `s5_supplied_executable`, `s5_dealt_executable_paramsE`, `s5_supplied_executable_paramsE` | — |
| `s5_tableau_observed.v` | 13 | `s5_dealt_executableE`, `s5_supplied_executableE` | 11 |
| `s5_tableau_sampled.v` | 1 | `s5_rand_sampled` | — |
| `s5_tableau_analysis_bridged.v` | 8 | `s5_row_rand_sampledE` | 7 |
| `s5_tableau_checks.v` | 3 | — | 3 |

21 moved items, 9 new declarations.

## Renames

| Before | After | Why |
|---|---|---|
| `s5_algebraic` | `s5_algebraic_start` | one letter from `s5_algebra` in the same file; `_start` names `tableau_start`, the statement that builds it, and the phase is still carried by the file name |
| `s5_dealt_splitE` | `s5_dealt_executableE` | "split" names the edit, not the relation; the tree names such an equation after its non-canonical side (`pgl27_inline_paramsE`, `pgl27_row_word39_bindE`, `s5_supplied_paramsE`) |
| `s5_supplied_splitE` | `s5_supplied_executableE` | same |
| `s5_row_rand_splitE` | `s5_row_rand_sampledE` | same |

## F17: one Executable-phase statement per run mode

Both close by `exact: erefl`. Read from `-time`:

```
Chars 4765 - 4861 [Lemma~s5_dealt_executable_para...] 0.   secs
Chars 4869 - 4882 [exact~:~erefl~.]                     0.001 secs
Chars 5992 - 6097 [Lemma~s5_supplied_executable_p...] 0.   secs
Chars 6105 - 6118 [exact~:~erefl~.]                     0.   secs
```

```coq
Lemma s5_dealt_executable_paramsE :
  projT2 (tableau_at s5_dealt_executable) = s5_dealt_params.
Proof. exact: erefl. Qed.

Lemma s5_supplied_executable_paramsE :
  projT2 (tableau_at s5_supplied_executable) = s5_supplied_params.
Proof. exact: erefl. Qed.
```

The dealt analogue does typecheck: `dealt_step` builds
`dealt_secret_params x fuel` and `s5_dealt_params` is
`dealt_secret_params s5_algebra 150` (`instances/s5/s5_exec.v:366`), so the two
are one term. `projT2` is the right projection because
`StackAt Executable = {A : PGGAlgebraic & ExecutionParams A}`
(`manifest/pgg_tableau.v:281`).

## Per finding

| id | declaration or header checked | final text, and deviations |
|---|---|---|
| F1 | `manifest/pgg_analysis_manifest.v:1034` `s5_row_det` = `@MkAnalysisPathRow S5Analysis.observed Observed None NoModelComparison …`, and `:1056` `s5_row_word` = `@MkAnalysisPathRow S5Analysis.observed AnalysisBridged S5Analysis.word_family IdealFinite …`, pinned `apr_completion = AnalysisBridged` at `:2168`. Both are over the dealer-dealt observed execution. | Applied as proposed: "The dealer-dealt run's program stops here: the manifest row s5_row_det it answers carries no model and no security payload, because the canonical encoding it deals puts the whole secret on one card, so the single seat the cut sends that card to reads the secret, as does every coalition containing that seat. The manifest carries a second row over this run, s5_row_word, under a finite-word model; the Sampled file records why no program of this instance continues from that model." Checked "second": over the dealer-dealt run the manifest carries exactly `s5_row_det` and `s5_row_word`. No deviation. |
| F2 | `instances/s5/s5_models.v:455`, `s5_word_family : AnalysisModelFamily s5_observed`, so it is a model of the dealer-dealt run and could not be adjoined to `s5_supplied` in any case. The manifest's own docstring for `s5_row_word` says `exec_endpoint_bound` is a mixing theorem resting on the Rayleigh certificate of `s5_mixing.v`. | Applied as proposed: "The instance's other model, the finite word over the four adjacent transpositions, is not named at this level. It is a model of the dealer-dealt run, and the manifest's row over it, s5_row_word, is published from a mixing theorem rather than from a program: two of the five parts of an input-indistinguishability certificate over that model are out of reach." No deviation. |
| F3 | `manifest/pgg_tableau.v:196-200`: `ic_const : forall C : {set …}, (#\|C\| < profile_k (instance_profile A))%N -> forall x x', fdistmap (static_coalition_obs C x) ic_ideal = fdistmap (static_coalition_obs C x') ic_ideal`. Quantified over every coalition below the threshold, so every singleton is one of them. | Restored from `instances/s5/s5_rows.v:66-72`: "…is the constancy of a coalition's reading of the ideal cut in the secret, which the certificate's constancy field asks for at every coalition below the threshold and so at every singleton: … and no choice of ideal avoids it, the seat in question varying with the cut while the ideal is fixed before any coalition is named." Deviation from production's wording: "the field" is written out as "the certificate's constancy field", because in a file that no longer sits beside the certificate the bare word reads as the research field. |
| F4 | `protocol/pgg_instance.v:281-306`, the six fields of `ExecutionParams`; `ex_expected` is commented "the value the run is meant to recover". | "The proposition is still True, so a reader shown this file has been shown which run is about to be made, and no proof that it terminates or that it recovers the value its parameters name." No deviation. |
| F5 | The two proofs in `s5_tableau_analysis_bridged.v` use `s5_sample_coalition_viewE`, `s5_supplied_endpoints` and `profile_k_s5_algebra` besides `s5_exec_coalition_secrecy`. None of those three is a statement about what a coalition learns. | "No other security statement of the instance enters the row." No deviation. |
| F6 | Same evidence as F4; `s5_supplied_recon` is adjoined one level up. | "the value the run is meant to recover is the tape's secret coordinate carried through the codec". No deviation. |
| F7 | `s5_supplied_paramsE`'s own docstring already uses "spellings" for this concept. | `s5_dealt_executableE`: "which of the two spellings a statement below is made at". `s5_supplied_executableE`: "adjoined, in the same sense as the dealer-dealt case". No deviation. |
| F8 | All six `ExecutionParams` fields. | "what the run argument is, who commits, what the dealer lays, what a seat observes after a shuffle, what value the run is meant to recover and how much interpreter fuel it is allowed". No deviation. |
| F9 | `StackProp Algebraic = fun _ => True` (`manifest/pgg_tableau.v:555`). | "under True, the proposition that level carries". No deviation. |
| F10 | The paragraph is about `s5_realises_expected` and `s5_rand_realises_expected`. | "Each realisation lemma is therefore a statement of this level, and neither depends on a probability model." No deviation. |
| F11 | The index entry for `s5_rand_static_obsE`. | Deviation: the proposed "the additive sharing's own" fills the 80-column field with no space before `*)`. Reworded over three lines instead, which supplies the missing head noun outright: "the framework's direct computation of a / coalition's reading is the one the additive / sharing makes". |
| F12 | `Fail Definition s5_F_k5 : s5_F = MkFunctionality id 5 := erefl` rejects with a unification failure on `erefl`; `s5_F := algebra_functionality s5_algebra`. | "The second is that the tolerated coalition size of s5_F is read off the algebra: the equation asserting it is five, where the sum-mod scheme tolerates four, is refused." The section banner above the `Fail` was also changed from "The tolerated coalition size is not a free choice", the same universal, to "The tolerated coalition size is read off the algebra". Deviation: the banner change is not in the finding, and is the same defect one line away. |
| F13 | New header text only; the moved comment below keeps production's wording under the pure-move rule. | "and no statement made at one run's model is a statement about the other's". No deviation. |
| F14 | No second row over `s5_rand_family` exists at this instance. | Kept on `s5_rand_sampled`, restated: "The value is what s5_row_rand_sampledE continues, so the row and the model are named apart." On `s5_row_rand_sampledE` the forward-looking clause is replaced by "so this equation is what keeps the two spellings of the row's prefix from parting", which is the same relation `s5_supplied_paramsE` states. Deviation: the auditor said only "drop the clause"; a replacement clause was needed or the docstring would end mid-thought. |
| F15 | `s5_tableau_algebraic.v` was the only file writing "sum-mod-5". | Fixed to "sum-mod". "view" left untouched in the moved docstrings and in `s5_rand_view_secrecy`, per the instruction. |
| F16 | `s5_rand_sampled`'s body is character for character the checked term, and the checks file imports that module. | `Check (s5_rand_sampled : Tableau Sampled).` Recorded in `verify.py` as `INTENDED_TOKEN_DIFF`, printed on every run with its reason and both texts, so the one difference from production's 21 items cannot become invisible. |
| F18 | `_CoqProject:226`. | Corrected; `STATUS.md` and `staged/RETIRED.md` now agree. |
| F19 | The four new `Definition`s were ascribed at their type only. | `gen_fidelity.py` now prints the assumptions of all nine new declarations and carries one comment saying that what pins the four bodies is the five equations, each holding by conversion. |
| F24 | `manifest/pgg_tableau_syntax.v:294` `dealt` and `:351` `supplied` both start `tableau_start A`; `:334` `encoded` starts `tableau_start (tg_algebra t)`. | "The rules dealt and supplied begin at a PGGAlgebraic and encoded at a Targeted over one, so the keyword surface has no form that continues a named value at Algebraic." No deviation. |

## Pattern rulings applied

- **Ruling 3, no `Require Export`.** The header of `s5_tableau_analysis_bridged.v`
  now states, as a fact about the files: "The phase files are required and
  imported one by one and export nothing of each other, so a file outside this
  directory names the phase that declares the name it wants: this file for a
  payload, a published row or a row equation, s5_tableau_sampled for a named
  model, s5_tableau_observed for a run or a specification, and
  s5_tableau_executable for a parameter record. An importer that wants only
  s5_rand_exact_witness names this file alone."
- **Ruling 4, the scope line.** `verify.py` now asserts that the last
  `Local Open Scope` line of all six phase files is the same. It already was:
  `Local Open Scope ring_scope.`, printed on every run.
- **Ruling 5, the `Fail` check.** Unchanged, and now stated as a rule of the
  template: every recorded `Fail` is compiled un-`Fail`ed in the preamble of
  the file it sits in, on both sides, and neither message may contain
  `was not found in the current environment`. The pass proved the rule again:
  `s5_tableau_executable.v` could not compile `exact: erefl` at all until
  `ssrfun` was added, which is the same missing import that had made
  `Fail s5_F_k5` pass for the wrong reason in the checks file. `ssrfun` is now
  on the first mathcomp line of all six files.

## Rebuild, verify and fidelity after the fix pass

Chain rebuilt in phase order through the lock; `make` not run.

| File | rc | wall |
|---|---|---|
| `s5_tableau_algebraic.v` | 0 | 4.3 s |
| `s5_tableau_executable.v` | 0 | 3.8 s |
| `s5_tableau_observed.v` | 0 | 5.0 s |
| `s5_tableau_sampled.v` | 0 | 3.9 s |
| `s5_tableau_analysis_bridged.v` | 0 | 4.6 s |
| `s5_tableau_checks.v` | 0 | 4.1 s |
| `staged/…/five_card_proximity.v` | 0 | 6.3 s |

No sentence over 5 s anywhere.

```
production items: 21
moved 21, new 9, lost 0
token stream differs BY DESIGN: Check <anonymous Check> (in s5_tableau_checks.v)
      F16: the bare Check now checks the named Sampled value s5_rand_sampled
           instead of restating its body (s5_supplied sample s5_rand_family)
      production: Check (s5_supplied sample s5_rand_family : Tableau Sampled).
      staged    : Check (s5_rand_sampled : Tableau Sampled).
token identity: 20 of 21 moved declarations identical, 1 intended difference(s)
docstrings: 18 of 18 word-identical
innermost scope, all six files: Local Open Scope ring_scope.
scans done
Fail s5_F_k5: same rejection
Fail s5_dealt_rand: same rejection
ALL CHECKS PASSED
```

`fidelity.v` and `baseline.v` both `rc=0`. The 94 assumption lines of the
moved names are **byte-identical**; the staged side carries 9 further blocks,
one per new declaration. The set of axiom identifiers in the two outputs is
equal: `rigidity_s5_instance.s5_group_order_eq`,
`propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description`. No new axiom, and `Closed under the
global context` appears once on each side, for `s5_F_thresholdE`.

Scans: no line over 80 bytes, every non-banner box line exactly 80 columns and
none ending in a stray asterisk, no banned vocabulary, no abbreviation of
"indistinguishability".
