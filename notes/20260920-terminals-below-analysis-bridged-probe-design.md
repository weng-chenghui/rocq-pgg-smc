# Terminals below AnalysisBridged: spec for a probe (2026-09-20)

Tracker step 4.3. Parent: `notes/20260919-tableau-three-extensions-probe-design.md`,
section "What this batch leaves, by phase", third group.

## The problem

A Tableau program can be handed over as a value that carries its manifest path
and its theorem only at the top level: `publish` takes a `StackAt
AnalysisBridged` and returns `PublishedAt c`. The manifest has a path that
honestly stops lower: `s5_det_path` is at `Observed` (`NoModelComparison`, the
dealer-dealt deterministic run). Its program `s5_dealt : Tableau Observed`
exists (`instances/s5/tableau/s5_tableau_observed.v`), and one lemma equates the
program's observed execution with the path's
(`s5_dealt_path_observedE`), but no value ties the path to the proposition the
program proved. Any program that honestly stops at `Sampled` (a model is named,
its link lemma is proved, no security evidence exists) is in the same position;
the refutations of tracker step 4.2, which end in `NegativeTransfer` without
security evidence, will be.

Why it matters: the manifest says of every path which level its theorems reach.
At `AnalysisBridged` that sentence is a term (`published_path p = the path`, by
conversion). Below, it is prose. A reader cannot tell a path whose program
stops at `Observed` from a path nobody wrote a program for.

## What each phase means (the placement rule of this development)

`StackProp Observed q` is run correctness of the observed execution;
`StackProp Sampled q` adds the link lemma of the named model family
(`sampled_viewE_prop`). A terminal at a level hands over exactly that
proposition and nothing above it: no security property is certified below
`AnalysisBridged`, so no reader of a security property may apply to such a
value, and its path's transfer status cannot claim a comparison with an ideal
that no evidence supports.

## Design

One record family indexed by the level, beside `PublishedAt` and not replacing
it (the seventeen published values and their readers keep their types):

```coq
Record PublishedAtLevel (l : CompletionLevel) := MkPublishedAtLevel {
  published_level_at   : StackAt l ;
  published_level_path : AnalysisPath ;
  published_level_thm  : StackProp l published_level_at }.
Notation PublishedObserved := (PublishedAtLevel Observed).
Notation PublishedSampled  := (PublishedAtLevel Sampled).
```

Two terminals, each building the path from the program's own data:

- `publish_observed (a : AssumptionStatus) : Tableau Observed -> PublishedObserved`,
  path `MkAnalysisPath (ob_obs q) Observed <empty slot> NoModelComparison a`. The
  transfer status is FIXED: a program with no model compares nothing.
- `publish_sampled (a : AssumptionStatus) (t : TransferStatus) :
  Tableau Sampled -> PublishedSampled`, path
  `MkAnalysisPath (sp_obs q) Sampled (sp_f q) t a`. The status is a payload
  because step 4.2's refutations publish `NegativeTransfer` from `Sampled`;
  whether `IdealFinite` must be refused at this level (it names a transfer
  theorem no `Sampled` program holds) is ledger row T6.

No terminal at `Algebraic` or `Executable`: their `StackProp` is `True`, and the
manifest has no path there.

Names: the owner's scheme names a finished program by its phase
(`Published`). `PublishedObserved`, `PublishedSampled` say the phase the program
stopped at. The instance value is `s5_det_published : PublishedObserved`, its
equation `s5_det_published_pathE`.

Rejected: generalising `PublishedAt` over the level (changes the type of every
published value and of `security_property_of`, for one path); a terminal that
takes an arbitrary path as payload (the path would no longer be the program's
own description, which is the point of the value).

## Pinned carrier

The framework's own: `CompletionLevel`, `StackAt l`, `StackProp l`,
`TableauAt`, `AnalysisPath`, `AnalysisModelSlot` (`manifest/pgg_analysis_status.v`),
at no instance. Vacuity rows instantiate at S_5 and PGL(2,7).

## Claim ledger

| id | Claim | Passing means |
|---|---|---|
| T1 | `PublishedAtLevel` typechecks as written; `AnalysisModelSlot obs Observed` has an empty inhabitant and `AnalysisModelSlot obs Sampled` is the family | `Definition`s compiled; the two slot types printed |
| T2 | `publish_observed`, `publish_sampled` typecheck; `ap_completion (published_level_path (publish_observed a p)) = Observed` and the Sampled twin, by conversion | `Qed` by `erefl`/`reflexivity` (never `by []` on these: known hang shape) |
| T3 | At S_5: `s5_det_published := publish_observed (AcceptsAxioms [:: AxS5GroupOrder]) s5_dealt`, and `published_level_path s5_det_published = s5_det_path` | closed by conversion; compile time recorded; mutation: with `BaselineClassicalOnly` the equation must fail |
| T4 | Readers: `run_correct_of_level` at both levels, `view_identification_of_sampled` at `Sampled`; at S_5 the first gives the run-correctness statement a downstream file cites today | `Definition`s; one `Check` against the existing S_5 statement |
| T5 | No security reader applies: `view_secrecy_of`, `security_property_of` on a `PublishedObserved` are type errors; `publish_observed` on a `Tableau Executable` is a type error; a `PublishedObserved` is not a `Published` | four recorded `Fail`s, each compiled once without `Fail` and the message read and quoted: a type mismatch, not an unknown reference |
| T6 | Which transfer statuses `publish_sampled` should admit. Compile `publish_sampled a IdealFinite` on `pgl27_word_sampled`: it typechecks (a status is data). Decide from `manifest/pgg_analysis_status.v`'s own docstring of `TransferStatus` whether the framework should refuse it, and if so by which means (a payload type `SampledTransfer` with two constructors `NoModelComparison`, `NegativeTransfer`, mapped into `TransferStatus`) | the variant compiled both ways; a recommendation with the docstring quoted |
| T7 | A `Sampled` instance: `publish_sampled` on `pgl27_word_sampled`; its path is NOT the manifest's `pgl27_word_path` (that one is `AnalysisBridged`) | the value compiled; `Fail` of the equation, message read |
| T8 | Keyword surface: notations `|> publish observed a` / `|> publish sampled a t` (or whatever the measured keyword rule of `manifest/pgg_tableau_syntax.v` allows without reserving a new global keyword); the existing `|> publish t a` still parses | a program written in the surface; the nineteen existing keywords unchanged; `Print Grammar constr` not required, but a file that imports only ssreflect plus the syntax file must still parse `observed` and `sampled` as identifiers if they become keywords: measured, as the syntax file's header demands |
| T9 | Decomposition: nothing above uses an axiom | `Print Assumptions` of T3's value and equation: the S_5 axiom `s5_group_order_eq` and the three classical ones, as `s5_dealt` today |

## Soundness invariants

- No new axiom. No change to any existing declaration (`PublishedAt`,
  `publish`, the readers, the seventeen values).
- A value of `PublishedAtLevel l` asserts `StackProp l` and nothing else; the
  statement comments say that no coalition, privacy or security statement
  follows from one.
- Out of scope and said so: `restate` below the top level; a place for
  `realises_expected` in the accumulated proposition (a recorded choice of the
  framework).

## Procedure

Probe directory `notes/probes/2026-09-20-terminals-below-analysis-bridged/`:
`t_framework.v` (T1, T2, T4, T5 framework part, T6), `t_s5.v` (T3, T4, T5, T9),
`t_pgl27.v` (T7), `t_syntax.v` (T8), `LEDGER.md`. Production load path, the
probe directory's `-Q` FIRST. Two audits (soundness, naming) before a landing
plan. Landing homes, if GO: `manifest/pgg_tableau.v` (record, terminals,
readers), `manifest/pgg_tableau_syntax.v` (notations),
`instances/s5/tableau/s5_tableau_observed.v` (the value and its equation).

## Results of the probe and of the two audits, and the landing plan (2026-09-20)

Probe: `notes/probes/2026-09-20-terminals-below-analysis-bridged/` (`LEDGER.md`),
nine rows compiled, the four main files recompiled from source by the main
session. Audits: `audit-soundness.md` (GO for a plan; Y6, Y7, Y8 must be carried;
its own recommendation on T6) and `audit-naming.md` (NO-GO under the probe's
names; Z1 to Z13). The owner is away; the decisions below are the main
session's. Every finding of both audits is ACCEPTED unless a decision below
says otherwise.

### Decisions

1. **Two records, not a family indexed by the level.** `PublishedObserved` and
   `PublishedSampled` are two `Record`s, each with its own constructor and three
   fields (`published_observed_at`, `published_observed_path`,
   `published_observed_thm`; the Sampled three likewise). Reason: the family
   `PublishedAtLevel l` is inhabited at `Algebraic` with a trivial proposition
   (Y2) and at `AnalysisBridged` with the content of `Published` under a second
   type (Y3), and its name collides in a reader's mind with `PublishedAt c`,
   which is indexed by a bound (Z14); two records have none of the three
   problems and rename nothing the owner named. `RunCorrectProp` and the
   dependent reader disappear: readers are `run_correct_of_observed`,
   `run_correct_of_sampled`, `view_identification_of_sampled`. The probe
   compiled the family; the landing first compiles the two-record shape in the
   probe directory (`t_framework_two_records.v`, with the six path equations and
   the readers) and lands only what compiled there.
2. **T6: the Sampled terminal admits only the two statuses that name an absent
   premise** (the soundness audit's recommendation). `TransferStatus`'s docstring
   divides its four constructors into two that name a theorem and two that name
   an absent premise; `StackProp Sampled` contains no ideal, distance or
   obstruction, so a program that stopped there holds no theorem a status could
   name, and the manifest's duty to state the missing premise is written for
   exactly the two admitted statuses. Type `TransferStatusWithoutTheorem` with
   constructors `SampledNoModelComparison`, `SampledStaticExecutedOnly` and the
   map into `TransferStatus` (name decided at the landing, checked free). The
   restricted terminal is THE terminal, `publish_sampled` (Z17). Consequence
   for tracker step 4.2: a refutation publishes `NegativeTransfer` only from a
   level whose proposition contains the obstruction; step 4.2 designs that
   statement.
3. **One shape for the three terminals** (Z8): both new terminals take
   `(q) (pf)` and their payload as `publish` does, so the surface rules expand
   through the bind; the `_step` variants do not land.
4. **Surface** (Z4, Z16, Y6, Y7): `s |> publish Observed a` and
   `s |> publish Sampled t a`, the framework's own constructor names after the
   literal verb, transfer status before assumption status as in all thirty-one
   existing uses. The keyword measurement is re-run at these spellings, and the
   syntax header gains the measured fact that inside the publish position the
   two tokens are taken by the new rules.
5. **Names** (Z1 to Z3): `<inst>_<discriminator>_<phase>_published`, the phase
   written at Observed and Sampled and elided at the top level:
   `s5_dealt_observed_published`, `s5_dealt_observed_published_pathE`,
   `s5_dealt_observed_published_recovers`.
6. **What lands where** (Z20, Z21, Y13): framework in `manifest/pgg_tableau.v`
   (one new section with its banner, header paragraph and index entries, one
   `Arguments` line per declaration as the neighbours have), the two rules in
   `manifest/pgg_tableau_syntax.v` (header facts corrected, Z12), the S_5 value
   and its two lemmas in `instances/s5/tableau/s5_tableau_observed.v`
   (docstrings in that file's `(**` style, Z11), four recorded rejections in
   `instances/s5/tableau/s5_tableau_checks.v`, each compiled once without `Fail`
   and its message kept in the probe directory (Y8). NOT landed: the PGL(2,7)
   Sampled value (the manifest holds no path at `Sampled` for it), the
   whole-program surface values, the unchosen T6 variants.
7. **Honesty sentences that must be in the landed comments** (Y1, Y3, Y4, Y5,
   Y15): the record's three fields are independent and the terminals are what
   tie the path to the data, as at the top level; nothing ties an assumption
   status to `Print Assumptions` at any level, the status is the author's
   statement and the manifest's prose defines when it is true; the new content
   of the S_5 value is the bundling of the program's theorem beside its path,
   the path equation being four coordinates fixed by the terminal and one
   conversion the tree already had; the four rejections of security readers
   rest on these records being distinct inductive types.

### Order of work

1. Probe directory: `t_framework_two_records.v` and the restricted terminal;
   `t_s5_two_records.v`; the keyword re-measurement; message files for every
   `Fail` that lands.
2. `manifest/pgg_tableau.v`, compile; `manifest/pgg_tableau_syntax.v`, compile.
3. `instances/s5/tableau/s5_tableau_observed.v`, `s5_tableau_checks.v`, compile.
4. `landing_fidelity.v` in the probe directory (every landed declaration
   ascribed at its full statement, `Print Assumptions` of the S_5 value and its
   two lemmas: `s5_group_order_eq` and the three classical axioms).
5. Main session: reverse closure of `manifest/pgg_tableau.v` recompiled
   single-file, fidelity recompiled, two audits, fix pass, commit.
