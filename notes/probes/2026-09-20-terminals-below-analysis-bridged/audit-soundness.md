# Adversarial soundness audit: terminals below AnalysisBridged (2026-09-20)

Audited: the spec `notes/20260920-terminals-below-analysis-bridged-probe-design.md`
and the probe `notes/probes/2026-09-20-terminals-below-analysis-bridged/`
(`LEDGER.md`, `t_framework.v`, `t_s5.v`, `t_pgl27.v`, `t_syntax.v`,
`t6_alt_split.v`, `t_keyword_check.v`, seven one-rejection files), against
`manifest/pgg_tableau.v`, `manifest/pgg_analysis_status.v`,
`manifest/pgg_analysis_manifest.v`, `manifest/pgg_tableau_syntax.v` and
`instances/s5/tableau/s5_tableau_observed.v`.

## Verdict

**GO** for writing a landing plan. No claim of the ledger is false, no row is
vacuous in a way that defeats its purpose, and no new assumption enters. Three
findings must be carried into the plan before any file is edited (Y6, Y7, Y8),
and the T6 decision differs from the prover's recommendation.

Three compiles were run for this audit, through the single-Rocq lock wrapper
on the production load path with the probe directory bound first. They are
scratch files outside the repository; their results are quoted below.

## What was compiled for this audit

| scratch file | what it settles | result |
|---|---|---|
| `amb.v` | a `TransferStatus` bound as `observed`, written in the existing terminal's status slot | the NEW rule fires: `The term "{| tableau_at := qb; tableau_thm := pfb |}" has type "Tableau AnalysisBridged" while it is expected to have type "Tableau Observed".` |
| `amb2.v` | the same at `sampled` | `Syntax error: [term level 0] expected after [term level 0] (in [term]).` |
| `free.v` | the record's three fields are independent; the family is inhabited at `Algebraic`; the one T6 rejection whose message was never read | all four `Check`s printed; final rejection `The term "StaticExecutedOnly" has type "TransferStatus" while it is expected to have type "SampledTransfer".` |

## Findings

| id | class | row | file:line | finding | what to change |
|---|---|---|---|---|---|
| Y1 | NOTE | T1 | `notes/probes/2026-09-20-terminals-below-analysis-bridged/t_framework.v:29-32` | The record's three fields are independent, so a value can hold a path that misdescribes its own data. Compiled: `Definition audit_misdescribed : PublishedObserved := @MkPublishedAtLevel Observed (tableau_at s5_dealt) s5_rand_path (tableau_thm s5_dealt).` accepts `s5_rand_path`, whose completion is `AnalysisBridged` and whose transfer is `StaticExecutedOnly`; both `Check (erefl : ap_completion (published_level_path audit_misdescribed) = AnalysisBridged)` and the `StaticExecutedOnly` twin print. The identical freedom exists today: `@MkPublished no_concluded_bound q s5_rand_path pf : Published` also compiled. `manifest/pgg_tableau.v:952-955` has the same three independent fields and `publish` is the only builder by convention, not by construction. This is a convention, not a soundness defect: no false proposition becomes provable, and it is not a regression. | The statement comment on the record must say the tie is made by the terminals and not by the record. The probe's current wording, `A program's data at one completion level, the manifest path describing it, and the proposition that level's StackProp carries about the data`, asserts a description the field does not carry. |
| Y2 | SHOULD | T1 | `t_framework.v:29`; spec lines 62-63 | The spec says `No terminal at Algebraic or Executable: their StackProp is True, and the manifest has no path there.` That is true of the terminals and false of the type. `PublishedAtLevel Algebraic` is inhabited: `Definition audit_published_algebraic : PublishedAtLevel Algebraic := @MkPublishedAtLevel Algebraic s5_algebra s5_rand_path I.` compiled, a value carrying a bridged path, an `IdealFinite`-free but `AnalysisBridged`-level path, and no content. `run_correct_of_level audit_published_algebraic : level_run_correct Algebraic (...)`, that is `True`, also printed. | Either restrict the family's index, or state in the record's comment that the family is inhabited at the two bottom levels with a trivial proposition and that no terminal builds such a value. A landing that says nothing leaves a type whose name reads as a published result and whose content is `I`. |
| Y3 | SHOULD | T1 | `t_framework.v:29` against `manifest/pgg_tableau.v:952-960` | `StackProp AnalysisBridged q` is `BridgedProp no_concluded_bound q` (`manifest/pgg_tableau.v:584`), so `PublishedAtLevel AnalysisBridged` holds exactly the content of `Published` under a second type, and `run_correct_of_level` at that level is `proj1 (proj1 (published_level_thm u))`, the same projection as `run_correct_of`. The spec's `beside PublishedAt and not replacing it` accepts the coexistence but never says which an author must use at the top. | The landing plan must state the rule: at `AnalysisBridged` a program is published with `publish` into `PublishedAt`, and `PublishedAtLevel AnalysisBridged` is not written. Put the rule in the record's comment, where a later author will read it. |
| Y4 | MUST | T3, T9 | `t_s5.v:39-47`; `manifest/pgg_analysis_manifest.v:55-58` | Nothing ties an assumption status to `Print Assumptions`, at this level or at the top level. The manifest states the discipline in prose: `A path is BaselineClassicalOnly when Print Assumptions reports the trio and nothing else, and AcceptsAxioms when it reports named repository assumptions beyond it`, and adds `a status covers the public results of the path, not only the values the path stores`. The only mechanical checks in the tree are `Timeout 60 Check (erefl : ap_assumptions s5_det_path = AcceptsAxioms [:: AxS5GroupOrder])` at `manifest/pgg_analysis_manifest.v:2163-2164`, which checks the path against itself. The T3 mutation is therefore rejected because one hand-written payload differs from one hand-written manifest field, not because the framework checked an assumption. The ledger's T9 output is read by eye. | Say this in the landing note in one sentence, and keep a `Print Assumptions` of the landed value and its equation in a checks file, so the eye-read evidence is recompiled rather than described. Do not let the landing prose read as though the terminal validates the status. |
| Y5 | SHOULD | T3 | `t_s5.v:45-47`; `instances/s5/tableau/s5_tableau_observed.v:95-97` | `published_level_path s5_det_published = s5_det_path` ties five coordinates, of which two are forced by the terminal's type (`Observed`, the empty slot), one by the terminal's body (`NoModelComparison`), one is a hand-written payload matched against a hand-written manifest field (`AcceptsAxioms [:: AxS5GroupOrder]`, see Y4), and one is the genuine conversion, `ap_observed s5_det_path = ob_obs (tableau_at s5_dealt)`, which `s5_dealt_path_observedE` already proves today. The new content of the value is therefore not the equation but the bundling: `published_level_thm` carries the proof beside the path, which is what the spec's problem statement asks for. | Write the landing note this way. The spec sentence `no value ties the path to the proposition the program proved` is accurate and the ledger's framing of T3 is not: state that T3's equation restates one existing lemma plus three type-forced coordinates plus one unchecked payload, and that the gain is the bundled theorem. |
| Y6 | MUST | T8 | `t_syntax.v:42-47` against `manifest/pgg_tableau_syntax.v:418-422` | The two payloads of the new `Sampled` rule are written in the opposite order from the existing terminal, and the comment on the new rule claims the opposite of what the rule does. The existing rule and its comment: `The two statuses are written transfer first, against the argument order of publish itself, so that a program's last statement reads in the order the manifest column headings run.` / `Notation "s |> 'publish' t a" := (s ;;; publish a of t)`. The new rule's comment: `Two payloads, written transfer first, in the order the manifest column headings run and against the argument order of the terminal itself, as the existing publish rule is.` / `Notation "s |> 'publish' 'sampled' a t" := (publish_sampled a t s)`, used at `t_syntax.v:69` as `|> publish sampled BaselineClassicalOnly NoModelComparison`. That is assumption first, transfer second, matching the terminal's argument order, which is what the comment denies. All 31 existing uses of `|> publish` in the tree write transfer first. | Swap the rule to `"s |> 'publish' 'sampled' t a"` so the two terminals read alike, and rewrite the comment to state what the rule does. If the owner prefers the terminal's own order, then the existing rule's comment is the one that must change, and the change touches an existing declaration, which the spec's invariants forbid in this batch. |
| Y7 | MUST | T8 | `t_syntax.v:39-47`; `t_keyword_check.v`; LEDGER section T8 | The ledger's T8 claim is true about the global lexer and false about the terminal position, and it is stated in a way a reader will take as the second. `t_keyword_check.v` measures only that `observed` and `sampled` remain bindable identifiers, which they do. Measured here: inside `|> publish _ …` the two tokens are captured by the new rules. With `Variable observed : TransferStatus`, the term `… |> publish observed a` elaborates as `publish_observed a s` and reports `The term "{| tableau_at := qb; tableau_thm := pfb |}" has type "Tableau AnalysisBridged" while it is expected to have type "Tableau Observed".` With `Variable sampled : TransferStatus`, `… |> publish sampled a` is a hard `Syntax error: [term level 0] expected after [term level 0] (in [term]).` — the parser commits to the two-payload rule and does not back out. A control in the same file, `amb_ok_fresh (t : TransferStatus)`, compiles. Cost today: none, because all 31 existing uses write a constructor name in that slot and no `TransferStatus` in the tree is named `observed` or `sampled`. | State the measured fact in the syntax file's header paragraph, beside the nineteen-keyword sentence: the two tokens are not global keywords, and inside the publish position they are not available as status names. The ledger's T8 wording must be corrected before the landing plan cites it. |
| Y8 | MUST | T5, T6, T7 | `t_s5.v:93,96,99`; `t_pgl27.v:69-70,87,88`; `t6_alt_split.v:48-51,56-57` | Nine `Fail`s in the probe have no message file, so nine rejections are recorded without evidence of what they reject. `Fail` succeeds on any error, including an unknown reference, so an unread `Fail` is weak evidence by the spec's own rule (T5: `each compiled once without Fail and the message read and quoted`). Four of the nine are the framework's, covered. The load-bearing one is `t6_alt_split.v:56-57`, `Fail Check (fun (a : AssumptionStatus) (s : Tableau Sampled) => publish_sampled_restricted a StaticExecutedOnly s).`, on which the T6 recommendation's second bullet rests. Compiled here without `Fail`: `The term "StaticExecutedOnly" has type "TransferStatus" while it is expected to have type "SampledTransfer".` A real type mismatch. The other eight are unverified. | Either add message files, or say in the ledger which `Fail`s are message-verified and which are not. The four message-verified ones are all of the form `The term X has type Y while it is expected to have type Z`, and `PublishedAtLevel` and `PublishedAt` are distinct inductives with no coercion, so all nine survive a rename. |
| Y9 | NOTE | T4 | `t_s5.v:60-64`; `manifest/pgg_analysis_manifest.v:472-474,486-489` | The probe's comment says `It is the statement the manifest pins for this path's correctness theorem`, singular. The manifest's correctness row for this path names three aliases, `S5Analysis.exec_correct, S5Analysis.exec_recovers, S5Analysis.observed_recovers`, and only the capability table pins one, `observed_recovers`. The type check itself is sound: both `Check (s5_det_published_recovers : …)` and `Check (S5Analysis.observed_recovers : …)` pass at the same written type, so the reader reaches the same fact the alias names. | Name `observed_recovers` in the comment rather than writing `the statement the manifest pins`, and say that the other two conjuncts of the same `And3` are reachable through the same reader. |
| Y10 | NOTE | T4 | `t_framework.v:154-176` | `level_run_correct` is `True` at `Algebraic` and `Executable` and `run_correct_of_level` returns `I` there. Harmless in the kernel: `StackProp` is `True` at those levels too, so the reader cannot overstate. The hazard is in the name: a downstream statement quantified over `l` reads as a run-correctness claim and is vacuous at two of five levels. The probe's comment already says so, `Below Observed a program has proved nothing about a run, which is what True records`. Note also that run correctness at `Observed` is read off the execution record's own field, `observed_correct (oe) := @OE.oe_run_correct oe` (`manifest/pgg_tableau.v:422-423`), so the terminal bundles a proof the instance discharged earlier and proves nothing new. | Keep the comment. If Y2 restricts the family, the two dead branches go with it. |
| Y11 | SHOULD | T1, T2, T4 | `t_framework.v:29,68,78,167,182` | No `Arguments` line for `PublishedAtLevel`, `MkPublishedAtLevel`, the three projections, `publish_observed`, `publish_sampled`, `run_correct_of_level` or `view_identification_of_sampled`. The production neighbours all carry them: `Arguments PublishedAt : clear implicits.`, `Arguments publish a {c} q pf t.`, `Arguments run_correct_of {c} r.`, `Arguments view_identification_of {c} r.`, `Arguments security_property_of {c} r R idx.` (`manifest/pgg_tableau.v:956,970,976,983,1016`). Under `Set Implicit Arguments` the probe happens to elaborate as written, but the landed file must not rely on that. | Add the mirroring directives in the landing edit and check each call site still elaborates. |
| Y12 | SHOULD | all | `manifest/pgg_tableau.v:80-146`; `manifest/pgg_tableau_syntax.v:64-88`; `instances/s5/tableau/s5_tableau_observed.v:29-51` | Three file headers carry `Definitions:` and `Key results:` blocks that the landing must extend, and the syntax header carries the keyword paragraph Y7 corrects. Nothing in the probe drafts them. | Draft the six new header entries (`PublishedAtLevel`, `publish_observed`, `publish_sampled`, `level_run_correct`, `run_correct_of_level`, `view_identification_of_sampled`), the two at the instance (`s5_det_published`, `s5_det_published_pathE`), and the corrected keyword paragraph, as named tasks of the landing plan. |
| Y13 | SHOULD | T5 | `instances/s5/tableau/s5_tableau_checks.v` | The instance already has the right home for a recorded rejection, described in its own header as `the terms the kernel refuses at the five-seat instance … recorded so that the rejection is compiled rather than described`, and the spec's landing homes do not name it. The three instance-level `Fail`s of `t_s5.v` belong there. | Add to the landing plan: record `Fail Check (view_secrecy_of s5_det_published).`, `Fail Check (security_property_of s5_det_published).` and `Fail Check (s5_det_published : Published).` in `s5_tableau_checks.v`, with the file's existing comment style. |
| Y14 | NOTE | T3 | `instances/s5/tableau/s5_tableau_observed.v:95-97` | After landing, `s5_dealt_path_observedE` is the observed-execution coordinate of `s5_det_published_pathE` (Y5). The batch's invariant forbids changing an existing declaration, so it stays. | Say in the landing note why both stay: the older lemma states the data coordinate alone and is cited as such, the newer one states the whole path. |
| Y15 | NOTE | T5 | spec lines 71-73 | The four T5 rejections depend on `PublishedAt` staying a separate inductive. The spec already rejects `generalising PublishedAt over the level`; that rejection is now load-bearing evidence and not only a design preference, because a later simplification that makes `PublishedAt` a notation for `PublishedAtLevel AnalysisBridged` silently turns all four rejections into acceptances. | Record the constraint in the landing plan as a condition on future work, not only as a rejected alternative. |
| Y16 | NOTE | T8 | `t_keyword_check.v:7-8` | The ledger says the file's `only imports are ssreflect and the probe syntax file`. True of its `Require` lines; the probe syntax file transitively pulls in the whole manifest, so the measurement is made in the full environment and does not isolate the new rules from the surface's existing nineteen keywords. It is still valid for the question asked, because a lexer keyword is global. | Phrase it as measured in the full environment. |
| Y17 | NOTE | T7 | `t_pgl27.v:31-33` | `The transfer status is the refusal to compare` is narrative wording for a constructor. The repository's rule is to write the relation. | `The transfer status is NoModelComparison: the program names a model and claims no relation between it and an idealized one.` |

## T6: which transfer statuses `publish_sampled` should admit

The prover recommends leaving `TransferStatus` unrestricted. I recommend
restricting to the pair the docstring itself separates, `NoModelComparison`
and `StaticExecutedOnly`, that is the shape already compiled in
`t6_alt_split.v`, with two changes to it.

### What the docstring and the manifest say

`manifest/pgg_analysis_status.v:63-71`, in full:

```
(* Relation an analysis path establishes between its executed model and an
   idealized one. IdealFinite is a public model-transfer theorem, and the
   path's prose names the ideal and the carrier of the transfer: the
   constructor covers both a cut-carrier transfer whose base premise is
   discharged and an observer-level transfer to a named ideal at the
   endpoint carrier. NegativeTransfer is a theorem transporting an
   obstruction to the path's observer. StaticExecutedOnly and
   NoModelComparison carry no such theorem, and a path with such a status
   names the absent premise instead. *)
```

The manifest header adds an obligation that runs the other way
(`manifest/pgg_analysis_manifest.v:894-896`): `every path whose transfer
status is NoModelComparison or StaticExecutedOnly states in its
missing-premise cell either the premise it lacks or why none is absent`.

So the four statuses split two and two. Two assert a theorem. Two assert no
theorem and take on a disclosure duty in exchange.

`StackProp Sampled q` is `oe_correct_prop (sp_obs q) /\ sampled_viewE_prop
(sp_f q)` (`manifest/pgg_tableau.v:582-583`): run correctness, and the
identification of the executed coalition reader with the static computation.
The second conjunct is exactly what the manifest calls the static-to-executed
travel that `StaticExecutedOnly` names. Neither conjunct mentions an
idealized model, a distance, or an obstruction.

### What a reader of a `PublishedSampled` at `IdealFinite` would wrongly conclude

Two things. First, that the program proved a public model-transfer theorem
naming an ideal and a carrier. It proved no statement in which an ideal
occurs. Second, and worse, the reader would not look for a missing-premise
cell, because the manifest's disclosure duty is written for the other two
statuses only. An `IdealFinite` at `Sampled` therefore claims a theorem that
does not exist and is exempted from the one paragraph that would have exposed
the gap. The probe compiled such a value:
`pgl27_word_published_idealfinite` (`t_pgl27.v:65-66`).

### Where I differ from the prover

Its first two reasons are correct as facts. Its first, that the spec's pair
does not respect the docstring's division of the four statuses, is decisive
against the spec's proposal and I adopt it. Its second, that no level stores a theorem for its status and
that `publish` at the top takes any `TransferStatus`, is verified
(`manifest/pgg_tableau.v:965-970`). But it argues from a known laxity to a new
one. The top level's laxity is bounded by the fact that a program there does
carry security evidence, so a wrong status there misstates the kind of a
theorem the program has. At `Sampled` a wrong status invents a theorem from
nothing. Those are not the same size of error, and copying the larger
permission down is not symmetry.

Its third reason, that step 4.2's refutations need `NegativeTransfer` from
`Sampled`, is not a reason to leave the payload open; it is a reason not to
settle the shape of a refutation here. The prover says as much itself, that
such a program `needs a statement that carries the obstruction theorem into
the program`. Under the restriction, step 4.2 is pushed to add that statement
and publish at the level whose proposition then contains the obstruction. That
is the placement rule this development already follows, and the pressure is
the right one.

The honest counter to my own recommendation is that the restriction buys a
convention and not a guarantee, because the path field is free (Y1): a hand-
written `@MkPublishedAtLevel Sampled q p pf` can carry any path at all. That
is true, and it is the reason the restriction is worth having anyway. The
terminal's payload type is the only place in this design where the convention
can be written as a type rather than as prose, and it costs nothing today:
both admissible statuses remain available, and no program in the tree wants a
third.

### The two changes to `t6_alt_split.v`'s shape

1. Rename. `SampledNoTransferTheorem` with constructors
   `NoTheoremNoModelComparison` and `NoTheoremStaticExecutedOnly` names the
   absence twice. Name the type for what it is and the constructors for what
   they claim: `TransferStatusWithoutTheorem`, with `SampledNoModelComparison`
   and `SampledStaticExecutedOnly`, mapped by `transfer_of_sampled`.
2. Say in the statement comment that the restriction is on the terminal and
   not on the record, and that a value built by hand can still carry any path.

If the owner prefers the prover's recommendation, the landing must at least
carry the disclosure duty into the statement comment of `publish_sampled`: a
program at this level has proved no statement about an idealized model, and a
path it builds at `IdealFinite` or `NegativeTransfer` is not supported by the
value's own proposition. The choice is the owner's; the two options must not
be landed without one of these two sentences.

## What is missing for a landing, beyond the table

- `_propertyE`-style equations do not apply: no security property exists below
  `AnalysisBridged`, and `publish_propertyE` has no analogue. The applicable
  analogue is the per-coordinate path equation, and the probe has all six
  (`publish_observed_completionE`, `_transferE`, `_modelE`, and the `Sampled`
  twins) plus the instance equation `s5_det_published_pathE`. Nothing further
  is owed here.
- `Arguments` lines: Y11.
- A recorded rejection at the instance: Y13.
- Header blocks and the syntax keyword paragraph: Y12, Y7.
- The rule for `PublishedAtLevel AnalysisBridged`: Y3.
- A recompiled `Print Assumptions` rather than an eye-read one: Y4.

## Invariants

- No existing declaration changed. `git status --porcelain manifest/
  instances/s5/` reports only `manifest/pgg_tableau_security_property_relations.v`,
  modified by an earlier campaign and untouched by this probe. The five
  production files the probe reads are clean.
- No new assumption. The main session recompiled the four main probe files
  from source at rc 0, and the S_5 values rest on `s5_group_order_eq` plus the
  three classical assumptions, as `s5_dealt` does today.
- Nothing at `Algebraic` or `Executable` is built by a terminal. The type
  family is nonetheless inhabited there: Y2.
- Statement comments: no probe comment claims that a value below
  `AnalysisBridged` certifies a security property, and `t_framework.v:26-28`
  states the opposite explicitly. The over-claims found are Y1 (`the manifest
  path describing it`), Y9 (`the statement the manifest pins`) and Y17
  (`the refusal to compare`). All three are wording, none is a claim about
  what is proved.
