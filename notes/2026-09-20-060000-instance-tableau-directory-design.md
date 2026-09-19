# One directory per instance for the Tableau phases: design and plan

Date: 2026-09-20. Repository `rocq-pgg-smc`, branch `feat/tableau-extensions-probe`,
HEAD `67e67f4`, which is identical to `main` (`git diff --name-only main...HEAD`
is empty). Read-only survey; nothing in the tree was edited or compiled for it.
Every claim below cites the file and line it was read from. Line numbers are
`grep -n` numbers, checked against a byte-offset count of the newlines before
each declaration, because a line-oriented reading of two of these files
disagreed with both by one. Where a claim can
only be settled by running the compiler, it says "needs a compile".

Successor to `notes/2026-09-19-124500-instance-tableau-directory-proposal.md`,
which states the owner's request and the first assessment. Two sentences of that
note do not describe the tree at this HEAD and are corrected in the section
"Corrections to the proposal note".

## The flow, as a program

The structure being designed is the reading order of one instance. The
accumulated value on each line is the proposition a reader has been shown by
the end of that file, which is the value the framework itself accumulates
(`manifest/pgg_tableau.v:553`, `StackProp`).

```
tableau/pgl27_tableau_algebraic.v        names pgl27_algebra          // proved: True
tableau/pgl27_tableau_executable.v       deals at pgl27_fuel          // proved: True
tableau/pgl27_tableau_observed.v         adjoins the three run facts  // proved: run correctness
tableau/pgl27_tableau_sampled.v          adjoins one family per model // proved: + executed reader is the static one
tableau/pgl27_tableau_analysis_bridged.v adjoins one arm per row      // proved: + that arm's proposition
tableau/pgl27_tableau_checks.v           recorded failures, examples  // proved: nothing further
```

Roles. Objects: the five named `Tableau` values, one per phase. Step
justifications: the three run facts at Observed, the family at Sampled, the
witness or certificate at AnalysisBridged. Terminals: `conclude` and `publish`,
which stay on the last line of a row and are not a phase
(`manifest/pgg_tableau.v:884`, `:937`). Outside the flow: the instance
mathematics that produces a payload, which enters through one named lemma per
payload and stays in the file it is in today.

The migration itself is a second program, with the count of production files
whose text changes as the accumulated value.

```
probe the loadpath with one empty phase file        // files changed: 1  (_CoqProject)
move Algebraic and Executable material              // files changed: 2
move the Observed prefix and its equations          // files changed: 2
move the Sampled names                              // files changed: 2
move the AnalysisBridged payloads, rows, equations  // files changed: 3
move the recorded failures; retire the rows file    // files changed: 4  (+1 importer)
fidelity compile and Print Assumptions diff         // files changed: 4
```

Monad verdict. `tableau_bind` (`manifest/pgg_tableau.v:590`) is a parameterised
monad indexed by pre- and post-`CompletionLevel`, with `tableau_start` as unit
(`:607`) and the left unit law holding by conversion
(`tableau_left_unit`, `:614`, `Proof. exact: erefl. Qed.`). The reorganization
does not add or change a law; it cuts the existing chain at the indices the
monad already has. That is why the phase directory is a faithful presentation
and not a new abstraction: the index of the monad is the file name.

DSL. A DSL already exists (`manifest/pgg_tableau_syntax.v`). This work exposes
one expressiveness limit in it, recorded as Question 4 below: the first
statement of a row starts from a `PGGAlgebraic` and not from a named
`Tableau Algebraic` value (`manifest/pgg_tableau_syntax.v:294`), so the
Algebraic-to-Executable edge is the one edge that cannot be written in the
keyword surface when the two phases sit in two files.

## Scope and the hard constraints

1. `instances/psl211/psl211_endpoints.v` is never compiled (its own header,
   `:6-17`: 568 s of `vm_compute`, 324 s of `Qed`, 898 s wall, 17 GB budget).
   No file in its forward closure may be edited or moved.
2. The forward closure was recomputed from the `Require` lines of every file in
   a `-R` directory of `_CoqProject`, transitively. It has 35 modules and is
   exactly the list in the brief: algebraic_rigidity, card_exchange_pismc,
   cover_tradeoff, covering_scheme, graded_resource, input_encoding,
   perm_exchange, perm_uniform, pgg_algebra_syntax, pgg_collusion_bound,
   pgg_execution_plug, pgg_input_commitment, pgg_instance, pgg_interface,
   pgg_monodromy_profile, pgg_observed_execution, pgg_raag, pgg_run,
   pgg_security_solver, pgg_session_types, pgg_sharing_framework, pgg_sum_mod,
   pgl_bound, pismc, psl211_blocks, psl211_closure, psl211_endpoints,
   psl211_exec, psl211_group, psl211_orbit, psl211_profile, psl211_scheme,
   smc_interpreter, smc_session_types, transitivity_privacy. Confirmed.
3. Exactly three files `Require` `psl211_endpoints`: `psl211_analysis.v`,
   `psl211_models.v` and `psl211_reading_constancy.v`. Moving one of them is
   safe for the digest. A `Require` resolves the logical name of the *required*
   module, and moving the *requiring* file changes neither
   `pgg_smc.psl211_endpoints` nor its `.vo`. What invalidates the `.vo` is a
   rebuild of anything below it, byte-identical or not
   (`psl211_endpoints.v:19-23`).
4. `instances/psl211/psl211_endpoints.vo` is older than its source
   (`notes/2026-09-20-054425-tableau-extensions-as-built.md`, last section).
   `make` would therefore rebuild it. The `Makefile` regenerates
   `Makefile.rocq` whenever `_CoqProject` changes (`Makefile:7-8`), and this
   plan changes `_CoqProject`. No task in this plan may run `make`, including
   `make <file>.vo`. Compile single files with the compiler directly, one Rocq
   process at a time.
5. No file outside `instances/` defines a `Tableau` program or a
   `PublishedRow`. Checked over `manifest/`, `security/`, `protocol/`,
   `reconstruct/`, `lib/`, `smc/`, `groups/`: every hit is a framework
   declaration in `manifest/pgg_tableau.v` or `manifest/pgg_tableau_syntax.v`.

## What the framework gives each phase

`CompletionLevel` has the five constructors the manifest records
(`manifest/pgg_analysis_status.v:60`), and `StackAt`
(`manifest/pgg_tableau.v:278-300`) says what data each level holds:

| Phase | Data the level holds | Statement that reaches it | Continues from |
|---|---|---|---|
| Algebraic | a `PGGAlgebraic` | `tableau_start` (`pgg_tableau.v:607`) | an algebra |
| Executable | + `ExecutionParams` | `dealt_step` (`:627`), or `params_step` under `encoded`/`supplied` | an algebra, not a named value |
| Observed | + the three run facts | `execute_step` (`:644`) | a named `Tableau Executable` |
| Sampled | + an `AnalysisModelFamily` | `sample_step` (`:664`) | a named `Tableau Observed` |
| AnalysisBridged | + a `SecurityPort` per field and index | `certify_exact` (`:777`), `certify_indistinguishability` (`:793`), `certify_idealproximity` (`:811`) | a named `Tableau Sampled` |

Three arms exist in production and no more: `ExactIndependence`,
`InputIndistinguishability`, `IdealProximity` (`pgg_tableau.v:239-243`). There
is no `SpectralCert` and no spectral arm anywhere in the compiled tree; the only
occurrences of that name are in an agent worktree under `.claude/`.

The keyword surface (`manifest/pgg_tableau_syntax.v`) continues from a named
value at `execute` (`:367`), `sample` (`:377`), every `certify` (`:380-403`),
`|> conclude` (`:416`) and `|> publish` (`:422`). The three first-line rules
`dealt` (`:294`), `encoded` (`:334`) and `supplied` (`:351`) take the algebra
itself. The raw bind `s ;;; f 'of' p` (`pgg_tableau.v:601`) continues from any
named value at any level, so a named `Tableau Algebraic` can be continued by
`;;; dealt_step of n`; that this elaborates needs a compile.

## Inventory

### What is named today, by phase

No file in the tree names a `Tableau Algebraic` or a `Tableau Executable`
value. This is the direct answer to the owner's question. A reader who opens the
tree today finds:

- Algebraic and Executable: not named anywhere. They exist as the first two
  lines inside a prefix program.
- Observed: named, once or twice per instance, as the prefix.
- Sampled: named at PGL(2,7) (`pgl27_word_sampled`) and at five-card (two
  values); not named at S5 or PSL(2,11).
- AnalysisBridged: never named on its own. Every row runs from its `certify`
  line straight into a terminal.

### PGL(2,7)

| Phase | Object | File:line | What else that file holds |
|---|---|---|---|
| Algebraic | `pgl27_algebra` | `instances/pgl27/pgl27_exec.v:337` | 643 lines: the parameters, the three run facts, the observed execution and three sample adapters |
| Executable | `pgl27_dealt_params` | `pgl27_exec.v:354` | same file |
| Observed | `pgl27_dealt_terminates` `:377`, `pgl27_dealt_endpoints` `:394`, `pgl27_dealt_recon` `:403`, `pgl27_observed` `:417` | `pgl27_exec.v` | same file; the facade alias is `PGL27Analysis.observed`, `pgl27_analysis.v:153` |
| Sampled | adapters `pgl27_sample` `:441`, `pgl27_word_sample` `:550`, `pgl27_prior_sample` `:639` | `pgl27_exec.v` | same file |
| Sampled | `pgl27_fixed_sample` `:121`, `pgl27_fixed_word_sample` `:129`, families `pgl27_exact_family` `:417`, `pgl27_word_family` `:424`, `pgl27_prior_exact_family` `:432` | `instances/pgl27/pgl27_models.v` | 434 lines, also the model mathematics |
| Tableau at Observed | `pgl27_dealt` `:141`, `pgl27_inline_dealt` `:388` | `instances/pgl27/pgl27_rows.v` | 751 lines, 49 declarations |
| Tableau at Sampled | `pgl27_word_sampled` `:485` | `pgl27_rows.v` | |
| AnalysisBridged | `pgl27_exact_witness` `:204`, `pgl27_word_cert` `:267` | `pgl27_rows.v` | with the link lemmas `pgl27_static_obsE` `:159`, `pgl27_static_obs_funE` `:173`, `pgl27_exact_viewE` `:186`, `pgl27_word_view_const` `:242` |
| Published rows | `pgl27_row_exact_tableau` `:289`, `pgl27_row_word_tableau` `:314`, `pgl27_row_word39` `:426`, `pgl27_row_word39_bind` `:435`, `pgl27_row_word_branch39` `:493` | `pgl27_rows.v` | plus `_rowE` `:338`, `:345`, `_armE` `:354`, `:363`, `:451`, `:502`, the bridges `:557`, `:616`, the restatements `:574`, `:635`, the theorems `:588`, `:647`, `:666`, the functionality `pgl27_F` `:735` and `pgl27_realises_expected` `:750` |
| Recorded failures | `:300`, `:371`, `:396`, `:408`, `:460`, `:469`, `:529`, `:721` | `pgl27_rows.v` | eight |
| AnalysisBridged | `pgl27_prior_exact_witness` `:157`, `pgl27_word_proximity_cert` `:292`, rows `:175`, `:392` | `instances/pgl27/pgl27_proximity.v` | 624 lines, 25 declarations, of which the distance mathematics `:141`, `:226`, `:307-367` and a section `:520-588` |
| Recorded failures | `:509`, `:601`, `:622` | `pgl27_proximity.v` | three |

### Five-card (Kim and den Boer)

| Phase | Object | File:line | What else that file holds |
|---|---|---|---|
| Algebraic | `five_card_algebra` | `instances/kim2025/five_card_exec.v:424` | 992 lines |
| Algebraic | `five_card_target` (the algebra with its ideal function) | `instances/kim2025/five_card_rows.v:958` | |
| Executable | `five_card_params` | `five_card_exec.v:468` | |
| Observed | `five_card_terminates` `:485`, `five_card_endpoints` `:511`, `five_card_recon` `:520`, `five_card_observed` `:583`, `den_boer_observed` `:589` | `five_card_exec.v` | the facade alias is `FiveCardAnalysis.observed` |
| Sampled | `five_card_sample` `:624` | `five_card_exec.v` | |
| Sampled | `kim_single_sample` `:139`, `kim_repeated_sample` `:161`, `five_card_uniform_family` `:426`, `kim_biased_family` `:435`, `kim_centi_family` `:443` | `instances/kim2025/five_card_models.v` | 445 lines |
| Tableau at Observed | `five_card_committed` `:236` | `instances/kim2025/five_card_rows.v` | 998 lines, 59 declarations |
| Tableau at Sampled | `five_card_row_repeated_tableau` `:463`, `five_card_row_biased_tableau` `:475` | `five_card_rows.v` | |
| AnalysisBridged | `five_card_exact_witness` `:382`, `kim_centi_cert` `:586`, `kim_biased_cert` `:601`, `kim_biased_cert_exact` `:832` | `five_card_rows.v` | with the link lemmas `:277`, `:295`, `:331`, `:347`, `:360` and the number lemmas `:554`, `:564`, `:723-769`, `:890-956` |
| Published rows | `:399`, `:617`, `:627`, `:786`, `:859` | `five_card_rows.v` | plus `_rowE`, `_armE`, `_atE`, `_publishedE` at `:408`, `:417`, `:638`, `:644`, `:655`, `:666`, `:685`, `:698`, `:816`, `:825`, `:873`, `:882` |
| Observed, again | `five_card_F` `:966`, `five_card_FE` `:974`, `five_card_realises_expected` `:995` | `five_card_rows.v` | statements about `five_card_observed` |
| Recorded failures | `:483`, `:543`, `:679`, `:798`, `:987` | `five_card_rows.v` | five |
| AnalysisBridged | `kim_biased_proximity_cert` `:261`, rows `:331`, `:361` | `instances/kim2025/five_card_proximity.v` | 593 lines, 31 declarations, of which two sections of distance mathematics `:161-244`, `:287-320` |
| Recorded failures | `:515`, `:523`, `:536`, `:551`, `:557`, `:567` | `five_card_proximity.v` | six, two of which name S5 objects |

### S5

| Phase | Object | File:line | Notes |
|---|---|---|---|
| Algebraic | `s5_algebra` | `instances/s5/s5_exec.v:334` | 983 lines, two whole run modes |
| Executable | `s5_dealt_params` `:366`, `s5_supplied_params` `:912` | `s5_exec.v` | two modes |
| Observed | `s5_dealt_terminates` `:383`, `s5_dealt_endpoints` `:399`, `s5_dealt_recon` `:408`, `s5_observed` `:432`; `s5_supplied_terminates` `:929`, `s5_supplied_endpoints` `:938`, `s5_supplied_recon` `:948`, `s5_rand_observed` `:966` | `s5_exec.v` | |
| Sampled | `s5_rand_sample` `:113`, `s5_word_sample` `:253`, `s5_rand_family` `:447`, `s5_word_family` `:455` | `instances/s5/s5_models.v` | 458 lines; two recorded failures `:345`, `:432` |
| Tableau at Observed | `s5_dealt` `:142`, `s5_supplied` `:168` | `instances/s5/s5_rows.v` | 394 lines, 21 declarations |
| AnalysisBridged | `s5_rand_exact_witness` `:257`, row `s5_row_rand_tableau` `:277` | `s5_rows.v` | with link lemmas `:209`, `:228`, `_rowE` `:286`, `_armE` `:294`, theorem `:311`, functionality `:341-392` |
| Recorded failures | `:194`, `:359` | `s5_rows.v` | two; `:193` is a bare `Check` |

### PSL(2,11)

| Phase | Object | File:line | Untouchable |
|---|---|---|---|
| Algebraic | `psl211_algebra` | `instances/psl211/psl211_exec.v:81` | yes, in the forward closure |
| Executable | `psl211_dealt_params` `:112`, `psl211_dealt_recon` `:117`, `psl211_dealt_terminates` `:123` | `psl211_exec.v` | yes |
| Executable | `psl211_alldecks_params` | `instances/psl211/psl211_alldecks.v:158` | no |
| Observed | `psl211_alldecks_terminates` `:571`, `psl211_alldecks_recon` `:580` | `psl211_alldecks.v` | no; 1407 lines |
| Observed | `psl211_profile_endpoints` | `instances/psl211/psl211_endpoints.v:50` | yes, and never recompiled |
| Observed | `psl211_alldecks_endpoints` `:340`, `psl211_alldecks_observed` `:349` | `instances/psl211/psl211_models.v` | no, but this file `Require`s `psl211_endpoints` |
| Sampled | `psl211_alldecks_sample` `:220`, `psl211_exact_family` `:514` | `psl211_models.v` | 1224 lines, mixes Observed and Sampled |
| Sampled | `psl211_word_sample` `:89`, `psl211_word_family` `:115` | `instances/psl211/psl211_word_model.v` | 135 lines |
| Tableau at Observed | `psl211_alldecks_prefix` `:147`, `psl211_alldecks_prefix_vm` `:266`, `psl211_alldecks_prefix_lit` `:299` | `instances/psl211/psl211_rows.v` | 324 lines, 12 declarations |
| AnalysisBridged | `psl211_exact_witness` `:172`, row `:196` | `psl211_rows.v` | `_rowE` `:205`, `_armE` `:213`, theorem `:230`; failures `:285`, `:323` |
| AnalysisBridged | `psl211_word_proximity_cert` `:160`, row `:290` | `instances/psl211/psl211_word_proximity.v` | 387 lines; failures `:245`, `:360`, `:384` |
| Refutation | `coalition_reading_constancy` `:200`, `indistinguishability_cert_reading_constancy` `:213`, `psl211_alldecks_no_small_eps_cert` `:711` | `instances/psl211/psl211_reading_constancy.v` | 1028 lines, 46 declarations, no program and no published row; `Require`s `psl211_endpoints` |

### Which files mix phases

- `pgl27_exec.v`, `five_card_exec.v`, `s5_exec.v`: Algebraic, Executable,
  Observed and the first Sampled adapters, in one file each.
- `psl211_models.v`: Observed and Sampled, in one file, above an untouchable
  `.vo`.
- `psl211_exec.v`: Algebraic and Executable, and untouchable.
- Every rows file: a named Observed value, sometimes named Sampled values, all
  the AnalysisBridged payloads and rows, the bridges to the paper-facing
  theorems, the functionality examples and the recorded failures.

### Phase objects that cannot move

PSL(2,11)'s Algebraic and Executable objects for the dealer-dealt mode
(`psl211_algebra`, `psl211_dealt_params`, `psl211_dealt_terminates`,
`psl211_dealt_recon`) are in `psl211_exec.v`, which is in the forward closure.
`psl211_profile_endpoints` is in `psl211_endpoints.v` itself. A phase file for
PSL(2,11) can therefore only name and re-state them. That is not a limitation of
the plan but of the tree: the same holds, for a different reason, at every other
instance, because moving `pgl27_exec.v` or `five_card_exec.v` would recompile
the analysis facade and through it `pgg_analysis_manifest.v` and every rows
file. The phase directories present the phases; the mathematics stays where it
is.

### Dependency facts the plan turns on

- `pgg_analysis_manifest.v` depends on the four `*_analysis.v` facades and on
  nothing above them. No manifest row cites a `Tableau` program; the citation
  runs the other way, through the `_rowE` lemmas in the rows files. So no
  candidate here touches the manifest or its pins.
- Reverse dependencies of the files this plan moves: `pgl27_rows` is imported
  only by `pgl27_proximity`; `five_card_rows` only by `five_card_proximity`;
  `psl211_rows` only by `psl211_word_proximity`; `s5_rows` only by
  `five_card_proximity`, which is a cross-instance import. The four proximity
  and constancy files have no importer at all.
- No source anywhere writes a fully qualified `pgg_smc.<module>.<ident>`. Every
  reference is a short identifier after a `From pgg_smc Require Import
  <module>`. Moving a declaration between modules under one logical root
  therefore changes no cited name; only `Require` lines change.
- Module base names are unique across every `-R` directory today, legacy
  included (checked by script).

## Candidate structures

All three keep the instance prefix in every file name, because `_CoqProject`
maps every instance directory to the one logical root `pgg_smc`.

### Candidate A: one file per phase

```
instances/pgl27/
  pgl27_group.v  pgl27_orbit.v  pgl27_scheme.v  ...        (unchanged)
  pgl27_exec.v        the algebra, the parameters, the run facts, the observed
                      execution, the three adapters              (unchanged)
  pgl27_models.v      the families and their mathematics         (unchanged)
  pgl27_analysis.v    the facade the manifest cites              (unchanged)
  pgl27_proximity.v   the proximity distance mathematics only    (reduced)
  tableau/
    pgl27_tableau_algebraic.v          Algebraic: pgl27_algebra named as a
                                       Tableau Algebraic value
    pgl27_tableau_executable.v         Executable: the dealt line at pgl27_fuel,
                                       and the equation that it is the run
                                       pgl27_dealt_params names
    pgl27_tableau_observed.v           Observed: pgl27_dealt, the inline variant,
                                       the functionality pgl27_F and
                                       pgl27_realises_expected
    pgl27_tableau_sampled.v            Sampled: pgl27_word_sampled and one named
                                       value per further model
    pgl27_tableau_analysis_bridged.v   AnalysisBridged: the witnesses and
                                       certificates, the seven published rows,
                                       five from the rows file and two from the
                                       proximity file, the row and arm equations,
                                       the conclude terminals, the bridges and
                                       the restated theorems
    pgl27_tableau_checks.v             the recorded failures, the cross-row
                                       comparisons, the number refutations
```

Sketched for the others: the same six files, with `five_card_*`, `s5_*` and
`psl211_*` in place of `pgl27_*`. At S5 the Executable and Observed files each
hold two named values, one per run mode. At PSL(2,11) the Algebraic and
Executable files name objects that live in untouchable files and add nothing of
their own beyond the `Tableau` values.

What moves: from `<inst>_rows.v` and `<inst>_proximity.v`, every program, every
payload record, every row equation, every recorded failure and the functionality
examples. What stays: the distance mathematics of the proximity files, the link
lemmas that are theorems about the instance rather than about a row, the whole
of `psl211_reading_constancy.v`.

Module names: `pgl27_tableau_algebraic`, `pgl27_tableau_executable`,
`pgl27_tableau_observed`, `pgl27_tableau_sampled`,
`pgl27_tableau_analysis_bridged`, `pgl27_tableau_checks`, and the same with the
other three prefixes. Twenty-four names, all unique under `pgg_smc`.

Import graph: each phase file imports the one before it; `_checks` imports
`_analysis_bridged`; `_analysis_bridged` also imports the instance mathematics it
needs, which is what the rows file imports today. Rows of different models
branch inside `_sampled` and `_analysis_bridged`, not across files.

`<inst>_rows.v` is retired, not kept as a re-export facade. The tree has no
precedent for a facade at this layer: the only `Require Export` files are the
four analysis facades, which exist to give the manifest one import point. The
three importers are edited in the same commit.

The manifest cites nothing here. The paper-facing names are the theorems at the
bottom of the rows files (`pgl27_exact_view_secrecy`,
`pgl27_word_view_indistinguishability_restated`, and their siblings); they move
into `_analysis_bridged` and keep their identifiers.

### Candidate B: Candidate A, with one file per row at the last phase

The first four phase files are Candidate A's. The fifth becomes a directory:

```
    tableau/analysis_bridged/
      pgl27_bridged_exact.v            witness, program, row and arm equation,
                                       bridge, restated theorem
      pgl27_bridged_word.v             certificate, program, the two concluded
                                       rows, the branch row, their equations
      pgl27_bridged_prior_exact.v      the prior-indexed exact row
      pgl27_bridged_word_proximity.v   the proximity certificate and its row
```

One security claim with its whole chain per file, which is the second half of the
owner's rule taken literally. Costs: the directory listing stops being the phase
list at the last level, which is the objection the owner raised to the first
structure in the proposal note; the cross-row failures
(`pgl27_row_word_arm_neq`, `pgl27_proximity.v:450`) and the arm comparisons need
a file that sees two rows, so `_checks` becomes mandatory rather than optional;
and each row file re-imports the same heavy instance mathematics, so the instance
build grows by three or five import loads. At five-card the split is four to six
files; at S5 it is one file, so the four instances no longer have the same roles.

### Candidate C: one file per instance, one section per phase

```
instances/pgl27/pgl27_tableau.v        five section banners, in phase order
```

Cheapest by far: four new files, four retired, no directory, no loadpath
question, no import graph between phase files. It fails the owner's question as
asked. A reader who lists the directory sees one file; the phases are visible
only after opening it. At PGL(2,7) the file is about 1100 lines after the
mathematics is left behind, at five-card about 1200.

### What all three do the same way

The rows files are retired rather than kept as re-export facades; the three
importers are edited in the same commit. The proximity files keep their distance
mathematics and their sections and lose their certificates, programs, row
equations and recorded failures to the AnalysisBridged material, wherever that
material lands. `psl211_reading_constancy.v` moves nowhere: it holds no program
and no published row, and the AnalysisBridged material cites it. The manifest
cites none of this in any candidate, because `pgg_analysis_manifest.v` depends
on the four `*_analysis.v` facades and nothing above them. The paper-facing
theorems keep their identifiers and change file only.

## Recommendation

Candidate A, with the AnalysisBridged phase left as one file per instance.

Against the owner's design rule, which is that the Tableau presents what is
proved and is organized by what each phase means:

1. A phase is a property of the instance, not of a row. The three lower phases
   have exactly one value per run mode, shared by every row of the instance:
   all seven published rows of PGL(2,7) rest on `pgl27_dealt`, two of them
   through `pgl27_word_sampled` (`pgl27_proximity.v:176`, `:393`). Splitting
   them per row would duplicate a shared object; splitting them per phase names
   it once, where its meaning is stated.
2. The split by phase dissolves an import that exists only because of the
   present file boundary. `pgl27_proximity.v` imports `pgl27_rows.v` for two
   names, the Observed prefix and the Sampled value, and the same holds at
   five-card and PSL(2,11). Once those two names are in the phase files, the
   proximity rows sit beside the rows they branch from and the import is gone.
3. The branch structure of the argument is one algebra, one run, one observed
   execution, several models, several rows. Candidate A puts the branch at the
   two levels where the tree actually branches, which is what the framework's
   own index says (`StackAt`, `pgg_tableau.v:278`). Candidate B branches one
   level further than the mathematics does, and pays for it with a nested
   directory whose listing is no longer the phase list.
4. One claim with its whole chain per row survives inside the file: each row is
   its own program, its own `_rowE`, its own `_armE`, its own bridge and its own
   theorem, in that order, under one banner per row. Nothing of the chain is
   shared between two rows except the prefix, which by then has its own file.
5. Candidate C answers the owner's question only after the file is opened, and
   the question was asked about the directory.

The recommendation is not final for five-card, where the AnalysisBridged file
would hold six rows and about 700 lines. If it reads badly once landed, the
split to Candidate B is a per-instance decision that costs one commit and no
statement change, because each row's chain is already contiguous.

## Costs

Counts are per instance unless stated. Compile times are unmeasured: needs a
compile.

| Cost | Candidate A | Candidate B | Candidate C |
|---|---|---|---|
| Files created | 6 per instance, 24 total | 9 to 11 at five-card and PGL(2,7), 6 at S5 and PSL(2,11), 32 total | 1 per instance, 4 total |
| Production files retired | `<inst>_rows.v`, 4 total | 4 | 4 |
| Production files reduced | 3 proximity files | 3 | 3 |
| Importer edits | 4 `Require` entries in 3 files, one of them cross-instance (`five_card_proximity` imports both `five_card_rows` and `s5_rows`) | 4 | 4 |
| `_CoqProject` lines | 24 added to the file list, 0 or 4 `-R` lines (Question 1) | 32 added, 0 or 8 `-R` | 4 added, 0 `-R` |
| Identifiers whose qualified name changes | none that any source cites: no file writes `pgg_smc.<module>.<ident>` | same | same |
| Modules recompiled | the 24 new files, the 3 reduced proximity files, and `five_card_proximity` once more after S5 lands | 32 + 3 + 1 | 4 + 3 + 1 |
| Files below that recompile | none. The exec, models and analysis files and `pgg_analysis_manifest.v` are untouched | none | none |
| Touches the forward closure | no | no | no |
| Risk of a rebuild of `psl211_endpoints.vo` | only through `make`, which no task runs | same | same |

Reverse closures, computed from the `Require` graph, for the files this plan
edits: `pgl27_rows` to `{pgl27_proximity}`; `five_card_rows` to
`{five_card_proximity}`; `s5_rows` to `{five_card_proximity}`; `psl211_rows` to
`{psl211_word_proximity}`; each proximity file and `psl211_reading_constancy` to
the empty set. The union is four files. Nothing reaches `pgg_analysis_manifest`,
because the manifest sits below the rows and not above them.

What the phases can hold, given the objects that cannot move:

| Instance | Algebraic file holds | Executable file holds | Observed file holds |
|---|---|---|---|
| PGL(2,7) | the `Tableau Algebraic` value over `pgl27_algebra` | the dealt line, and `pgl27_inline_paramsE`-style equations naming `pgl27_dealt_params` | `pgl27_dealt`, the inline prefix, the fork failure, `pgl27_F`, `pgl27_realises_expected` |
| five-card | the value, and `five_card_target` moved from the rows file | the encoded line at fuel 100, and `five_card_committed_paramsE` | `five_card_committed`, `five_card_F`, `five_card_FE`, `five_card_F_ite`, `five_card_realises_expected` |
| S5 | the value | two values, dealt and supplied, and `s5_supplied_paramsE` | `s5_dealt`, `s5_supplied`, `s5_dealt_row_observedE`, `s5_F`, `s5_rand_F` and the two `realises_expected` |
| PSL(2,11) | a value over `psl211_algebra`, which stays in an untouchable file | a value over `psl211_alldecks_params`; the dealer-dealt parameters stay untouchable | the three prefixes and their `paramsE` equations |

The Algebraic file of every instance holds one or two declarations. That is the
intended outcome, not a defect: the directory listing is the phase list, and a
short file is what an unbranched phase looks like.

## Pure moves, and how to verify them

The reorganization should be pure moves at declaration granularity, with two
named exceptions.

Pure, and checkable by script: every payload record, every published row, every
`_rowE`, `_armE`, `_atE` and `_publishedE`, every bridge, every restated
theorem, every recorded failure, every functionality example. These move as
written, with their comments, and nothing about their text changes except the
file they are in.

Not pure, and each needs one conversion lemma:

1. Naming a `Tableau Algebraic` and a `Tableau Executable` value re-cuts the
   prefix. `pgl27_dealt` written as `pgl27_tableau_executable execute ...`
   expands to `execute_step (tableau_at pgl27_tableau_executable) ...`, which is
   convertible with the present term by delta and iota but not token-identical.
   The check is `Lemma pgl27_dealt_splitE : <new> = <old> := erefl`, which
   `tableau_left_unit` says should close (`pgg_tableau.v:614-618`). Needs a
   compile. If it fails, the fallback is Question 4's default reversed: leave
   the prefix whole in the Observed file and let the two lower files name only
   the instance objects.
2. The proximity files are split rather than moved, so their `Require` lists
   must be recomputed for both halves.

Verification, in this order:

1. Token identity. For each moved declaration, `scripts/strip_comments.py` on
   the old and the new file, then compare the declaration's token stream. The
   script is nesting-aware and already exists for exactly this check (its
   docstring, `scripts/strip_comments.py:3-5`). A wrapper that slices a
   declaration by name is the only new code, and it is a script, not a proof.
2. A fidelity file under `notes/probes/2026-09-20-tableau-dirs/`, never imported
   by production, that `Require`s the new modules and `Check`s every moved name
   at the statement it had before, with `Timeout 60 Check (erefl : ...)` for the
   row equations. Compile once per instance.
3. `Print Assumptions` for every published row and every paper-facing theorem,
   before and after, compared as text. The project's scan convention allows the
   dots.
4. The recorded failures must still fail, and for their recorded reason. A
   `Fail` that becomes an unknown-reference failure passes silently and proves
   nothing; landing 4 of the extensions hit exactly this
   (`notes/2026-09-20-054425-tableau-extensions-as-built.md`, item 10). Capture
   the message of each `Fail` before the move and compare after.
5. The manifest's pins compile unchanged. They will, because the manifest does
   not import any file this plan touches; the check is that the `_rowE` lemmas,
   which do cite manifest rows, still close by conversion in their new file.
6. Any newly written equation uses `exact: erefl` and never `by []`. A `by []`
   over a `published_at` equation has been measured at 683 s against 0.13 s.

## Task list

One atomic task per commit. The tree compiles after every commit. Single-file
compiles only, one Rocq process at a time, never `make`. Every `.v` edit is
executed by a rocq-prover agent, comment edits included. Time estimates exclude
compile time, which is unmeasured.

Order of instances: S5 first, because it is the smallest and because retiring
`s5_rows.v` forces the one cross-instance import edit that everything else would
otherwise trip over; then PSL(2,11), then PGL(2,7), then five-card.

| # | Task | Instance | Mechanical or prover | Estimate |
|---|---|---|---|---|
| 1 | Add `instances/s5/tableau/` with one phase file holding a single `Check`, add its `_CoqProject` entry, compile it. Settles Question 1 before anything moves. | S5 | prover | 30 min |
| 2 | Move the Algebraic and Executable material; add the two `Tableau` values and their conversion lemma. | S5 | prover | 1 h |
| 3 | Move `s5_dealt`, `s5_supplied`, their equations and the functionality examples into the Observed file. | S5 | script, then prover for the headers | 1 h |
| 4 | Create the Sampled file naming one value per family. | S5 | prover | 45 min |
| 5 | Move the witness, the row, the equations and the theorem into the AnalysisBridged file. | S5 | script | 45 min |
| 6 | Move the two recorded failures and the bare `Check` into the checks file; retire `s5_rows.v`; repoint `five_card_proximity.v`'s import; compile both. | S5 | prover | 1 h |
| 7 | Fidelity compile, `Print Assumptions` diff, failure-message diff. | S5 | script | 45 min |
| 8-14 | The same seven tasks at PSL(2,11). Task 9 names values over objects in untouchable files and adds nothing else. Task 13 repoints `psl211_word_proximity.v`. | PSL(2,11) | as above | 5 h |
| 15-21 | The same seven at PGL(2,7). Task 19 also splits `pgl27_proximity.v`, leaving the distance mathematics behind. | PGL(2,7) | as above | 6 h |
| 22-28 | The same seven at five-card. Task 26 also splits `five_card_proximity.v`. The AnalysisBridged file is the largest in the batch. | five-card | as above | 7 h |
| 29 | Update the header of `manifest/pgg_analysis_manifest.v` and any note or paper path that cites a retired file name. | all | prover | 1 h |

Tasks that a script can do end to end: 3, 5, and their analogues, plus every
step of task 7. Tasks that need a prover: every task that writes a new
declaration (2, 4 and analogues), every header, and every task that changes a
`Require` list.

## Corrections to the proposal note

`notes/2026-09-19-124500-instance-tableau-directory-proposal.md:65-66` says
`psl211_spectral_constancy.v` names `SpectralCert` and should move into the
PSL(2,11) tableau directory. At this HEAD there is no file of that name and no
`SpectralCert` in the compiled tree; the only occurrences are in an agent
worktree under `.claude/`. The production file is
`instances/psl211/psl211_reading_constancy.v`, it names `IndistinguishabilityCert`
through `indistinguishability_cert_reading_constancy` (`:213`), and it holds no
program and no published row. It should stay where it is.

The same note's cost paragraph (`:91-92`) says the four rows files have no
importer. Three of them now do, as the as-built note records: `pgl27_proximity`,
`five_card_proximity` and `psl211_word_proximity` import them, and
`five_card_proximity` imports `s5_rows` across instances.

## Open questions, with the default that lets work proceed

1. **Loadpath.** `-R` is recursive, so `instances/pgl27/tableau/x.v` under the
   existing `-R instances/pgl27 pgg_smc` gets the logical name
   `pgg_smc.tableau.x`. Adding `-R instances/pgl27/tableau pgg_smc` would make
   the name flat but binds the same files under two logical names, which is what
   `-w -ambiguous-paths` in `_CoqProject:4` silences. Default: add no `-R` line,
   let the names carry the `tableau` component, and keep writing
   `From pgg_smc Require Import pgl27_tableau_sampled`, which should resolve
   because the prefix and the suffix both match. Needs a compile, and task 1
   exists to run it. Fallback if it does not resolve: no directory, flat files
   named `<inst>_tableau_<phase>.v` in the instance directory.
2. **One file per row at AnalysisBridged.** Default: no, one file per instance,
   revisited at five-card after it lands.
3. **Retiring the rows files.** Default: retire, and edit the three importers.
   No re-export facade, because the tree uses that idiom only for the four
   analysis facades the manifest imports.
4. **Named `Tableau Algebraic` and `Tableau Executable` values.** Default: name
   them, through the raw bind where the keyword surface cannot continue from a
   name, and prove one conversion lemma per re-cut. If the conversion does not
   close, fall back to phase files that name only the instance objects and leave
   the prefix whole at Observed.
5. **A notation for the first line.** If the default of Question 4 stands, the
   surface has one edge it cannot write. Default: do not add a notation in this
   batch; record it as the first ledger row of any follow-up, as the proposal
   note already does.
6. **Where the functionality material goes.** `Targeted` values are the payload
   of an `encoded` or `supplied` first line, and `realises_expected` is a
   statement about the observed execution. Default: `Targeted` to the Algebraic
   file, the functionality and its equations to the Observed file.
7. **Where the `Reprice` constants go.** They are payloads of the `conclude`
   terminal. Default: with the row that uses them, in the AnalysisBridged file.
   The open naming question about `Reprice` itself, recorded in the as-built
   note, is untouched by this batch.

## Orchestrator's decisions (2026-09-20)

The draft above is by an Opus agent that compiled nothing. The main session
read the recommendation, the S5 and PSL(2,11) inventories, the costs and the
task list, and decided as follows. These supersede the text above where they
differ.

1. Candidate A: one directory `instances/<inst>/tableau/` per instance, one
   file per phase (`<inst>_tableau_algebraic.v`, `_executable.v`,
   `_observed.v`, `_sampled.v`, `_analysis_bridged.v`) and one
   `<inst>_tableau_checks.v`. It is the structure the owner described ("a
   directory in each instance to contain Tableau phase files, each phase one
   file") and it answers the owner's question of which file holds which phase
   by the file's name.
2. The seven open questions take their stated defaults. Question 1 (the load
   path of a subdirectory under a recursive `-R`) is settled by a compile
   before anything moves; the fallback is flat files named the same way.
3. S5 is the pilot. It is built as a staged text in a probe directory, with a
   fidelity file and a declaration-level token check, audited, and copied with
   `cp`, as the landings of the extensions were. The other three instances
   follow the same way, and the pilot's as-built structure is shown to the
   owner before they start.
4. The mathematics does not move. `<inst>_exec.v`, `<inst>_models.v`, the
   analysis facades and the manifest are unchanged, so nothing below the rows
   is recompiled and no file in the forward closure of `psl211_endpoints.v` is
   touched. A phase file names the object its phase means and states what the
   program prefix up to that phase has shown.
5. A retired `<inst>_rows.v` is removed with `git rm` by the main session at
   the `cp`, after its three importers are repointed. No paper file is edited:
   the file names the paper sources cite are listed in a dated note for the
   owner, as the renamed identifiers were.
6. `make` is never run, and `_CoqProject` edits are made by the main session at
   the `cp`.
