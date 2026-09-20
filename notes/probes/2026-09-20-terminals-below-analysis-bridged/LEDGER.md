# Terminals below AnalysisBridged: probe ledger (2026-09-20)

Spec: `notes/20260920-terminals-below-analysis-bridged-probe-design.md`.
No production file was read-modified; every file below is in this directory.
Load path: this directory bound to `belowprobe` first, then `_CoqProject`'s
`-R` lines and its five warning flags. Every compile ran through the
single-Rocq lock wrapper, capped at 900 s. Rocq 9.0.0.

Verdict: **T1-T9 all GO.** Zero `Admitted`, zero `Abort`, zero `Axiom` in the
probe files; every equation closes by `exact: erefl`.

## The flow

```
s5_algebra                                  // Algebraic,  proposition: True
  dealt fuel 150                            // Executable, proposition: True
  execute terminates by s5_dealt_terminates
          endpoints  by s5_dealt_endpoints
          recon      by s5_dealt_recon      // Observed, proposition: run correctness
  |> publish observed (AcceptsAxioms [:: AxS5GroupOrder])
                                            // PublishedObserved: run correctness
                                            // + MkAnalysisPath (ob_obs q) Observed
                                            //     None NoModelComparison a
                                            //   = s5_det_path, by conversion
```

Each existing definition and the interface it enters through:

| component | role | interface |
|---|---|---|
| `s5_algebra` (`instances/s5/pgg_raag_s5.v`) | first object | `tableau_start`, through the `dealt` rule |
| `dealt_step` (`manifest/pgg_tableau.v`) | step, payload the fuel | `A dealt fuel n` |
| `s5_dealt_terminates`, `s5_dealt_endpoints`, `s5_dealt_recon` (`instances/s5/s5_exec.v`) | step justification | `obs_payload` (`manifest/pgg_tableau_syntax.v`), through the `execute` rule |
| `execute_step` (`manifest/pgg_tableau.v`) | step establishing run correctness | `observed_correct` reads `OE.oe_run_correct` |
| `ob_obs` (`manifest/pgg_tableau.v`) | observation change, at no cost | read by the new terminal |
| `MkAnalysisPath` (`manifest/pgg_analysis_manifest.v`), `AnalysisModelSlot`, `NoModelComparison` (`manifest/pgg_analysis_status.v`) | packaging into a record | the new terminal `publish_observed` |
| `run_correct_of_level` (new) | terminal evaluation | reads `published_level_thm` back at the level |

Outside the flow: the assumption status, which no level's proposition
determines and which the terminal therefore takes as a payload; and the
manifest's own prose table, which the status is checked against by eye.

Monad verdict: `TableauAt` is a parameterised monad indexed by pre- and
post-`CompletionLevel`, with `tableau_start` the unit, `tableau_bind` the bind
and left unit definitional (`tableau_left_unit`, `exact: erefl`); it is not
graded, because the accumulated value is a proposition and not a monoid. The
two new terminals are the level-indexed terminal morphism out of that
structure, not steps, and add no monadic structure of their own.

## Ledger

| id | verdict | evidence |
|---|---|---|
| T1 | GO | `t_framework.v`, `PublishedAtLevel`, `PublishedObserved`, `PublishedSampled`, and the three slot `Check`s |
| T2 | GO | `t_framework.v`, six equations, all `exact: erefl` |
| T3 | GO | `t_s5.v`, `s5_det_published`, `s5_det_published_pathE`; mutation rejected, `t3_msg_mutation.v` |
| T4 | GO | `t_framework.v`, `run_correct_of_level`, `view_identification_of_sampled`; `t_s5.v`, `s5_det_published_recovers` and two `Check`s |
| T5 | GO | four rejections, each a type mismatch, messages quoted below |
| T6 | GO (decision open, recommendation below) | three variants compiled: `publish_sampled` unrestricted, `publish_sampled_restricted`, `publish_sampled_no_theorem` |
| T7 | GO | `t_pgl27.v`, `pgl27_word_published_sampled`; path inequality, `t7_msg_path.v` |
| T8 | GO | `t_syntax.v` two rules, three terminals parse side by side, a whole program in the surface; `t_keyword_check.v` measures no reservation |
| T9 | GO | `t_s5.v`, four `Print Assumptions`, all four identical to `s5_dealt`'s |

## Timings

One pass, 23:00:50 to 23:02:08.

| file | rc | elapsed |
|---|---|---|
| `t_framework.v` | 0 | 30 s (first of the pass, pays the `.vo` load) |
| `t_s5.v` | 0 | 5 s |
| `t_pgl27.v` | 0 | 5 s |
| `t6_alt_split.v` | 0 | 4 s |
| `t_syntax.v` | 0 | 4 s |
| `t_keyword_check.v` | 0 | 3 s |
| the seven message files | 1, as intended | 3-4 s each |

The only warning any probe file emits is `notation-incompatible-prefix` about
infotheo's `_ <| _ |> _` against mathcomp-analysis's `_ <| _`. It is raised at
the `Require Import pgg_analysis_manifest` line of each file, so it predates
this probe; `t_keyword_check.v`, which requires no manifest of its own, emits
nothing, and the two new notations emit nothing.

## T1, the record and the two slot types

```coq
Record PublishedAtLevel (l : CompletionLevel) := MkPublishedAtLevel {
  published_level_at   : StackAt l ;
  published_level_path : AnalysisPath ;
  published_level_thm  : StackProp l published_level_at }.
Notation PublishedObserved := (PublishedAtLevel Observed).
Notation PublishedSampled := (PublishedAtLevel Sampled).
```

Typechecks as the spec writes it. The printed slot types, at a variable
observed execution `obs`:

```
erefl : AnalysisModelSlot obs Observed = option (AnalysisModelFamily obs)
None : AnalysisModelSlot obs Observed
erefl : AnalysisModelSlot obs Sampled = AnalysisModelFamily obs
```

## T2, the two terminals

```coq
Definition publish_observed (a : AssumptionStatus) (s : Tableau Observed)
    : PublishedObserved :=
  @MkPublishedAtLevel Observed (tableau_at s)
    (@MkAnalysisPath (ob_obs (tableau_at s)) Observed None NoModelComparison a)
    (tableau_thm s).

Definition publish_sampled (a : AssumptionStatus) (t : TransferStatus)
    (s : Tableau Sampled) : PublishedSampled :=
  @MkPublishedAtLevel Sampled (tableau_at s)
    (@MkAnalysisPath (sp_obs (tableau_at s)) Sampled (sp_f (tableau_at s)) t a)
    (tableau_thm s).
```

Six equations, each `Proof. exact: erefl. Qed.`:

```coq
Lemma publish_observed_completionE (a : AssumptionStatus)
    (s : Tableau Observed) :
  ap_completion (published_level_path (publish_observed a s)) = Observed.

Lemma publish_observed_transferE (a : AssumptionStatus) (s : Tableau Observed) :
  ap_transfer (published_level_path (publish_observed a s))
  = NoModelComparison.

Lemma publish_observed_modelE (a : AssumptionStatus) (s : Tableau Observed) :
  ap_model (published_level_path (publish_observed a s)) = None.

Lemma publish_sampled_completionE (a : AssumptionStatus) (t : TransferStatus)
    (s : Tableau Sampled) :
  ap_completion (published_level_path (publish_sampled a t s)) = Sampled.

Lemma publish_sampled_transferE (a : AssumptionStatus) (t : TransferStatus)
    (s : Tableau Sampled) :
  ap_transfer (published_level_path (publish_sampled a t s)) = t.

Lemma publish_sampled_modelE (a : AssumptionStatus) (t : TransferStatus)
    (s : Tableau Sampled) :
  ap_model (published_level_path (publish_sampled a t s))
  = sp_f (tableau_at s).
```

The bind-shaped spelling of the Sampled terminal also compiles, and the two
are one term:

```coq
Definition publish_sampled_step (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (t : TransferStatus) : PublishedSampled :=
  @MkPublishedAtLevel Sampled q
    (@MkAnalysisPath (sp_obs q) Sampled (sp_f q) t a) pf.

Lemma publish_sampled_stepE (a : AssumptionStatus) (t : TransferStatus)
    (s : Tableau Sampled) :
  (s ;;; publish_sampled_step a of t) = publish_sampled a t s.
```

The Observed terminal has no bind-shaped spelling: `tableau_bind` passes a
payload, and that terminal has none. A landing that wants both terminals to
be binds has to give the Observed one a unit payload, which buys nothing.

## T3, the five-seat value and its path

```coq
Definition s5_det_published : PublishedObserved :=
  publish_observed (AcceptsAxioms [:: AxS5GroupOrder]) s5_dealt.

Lemma s5_det_published_pathE :
  published_level_path s5_det_published = s5_det_path.
Proof. exact: erefl. Qed.
```

Closed by conversion. The whole file is 5 s, so the conversion is not a cost
worth managing; no `reflexivity` fallback was needed and no `by []` was used
on an equation crossing the terminal.

Mutation, in `t3_msg_mutation.v`, compiled without `Fail`:

```
File ".../t3_msg_mutation.v", line 16, characters 19-24:
Error:
The term "erefl" has type
 "published_level_path (publish_observed BaselineClassicalOnly s5_dealt) =
  published_level_path (publish_observed BaselineClassicalOnly s5_dealt)"
while it is expected to have type
 "published_level_path (publish_observed BaselineClassicalOnly s5_dealt) =
  s5_det_path"
(cannot unify "published_level_path
                 (publish_observed BaselineClassicalOnly s5_dealt)"
and "s5_det_path").
```

The mutation is written as a `Fail Definition ... := erefl` and not as a
failing `Lemma`, because a `Fail Lemma` whose statement is merely false does
not fail: the statement typechecks.

## T4, the readers

```coq
Definition level_run_correct (l : CompletionLevel) : StackAt l -> Prop :=
  match l with
  | Algebraic | Executable => fun _ => True
  | Observed => fun q => oe_correct_prop (ob_obs q)
  | Sampled => fun q => oe_correct_prop (sp_obs q)
  | AnalysisBridged => fun q => oe_correct_prop (ab_obs q)
  end.
Arguments level_run_correct : clear implicits.

Definition run_correct_of_level (l : CompletionLevel) (r : PublishedAtLevel l)
    : level_run_correct l (published_level_at r) :=
  match l return forall u : PublishedAtLevel l,
                   level_run_correct l (published_level_at u) with
  | Algebraic => fun _ => I
  | Executable => fun _ => I
  | Observed => fun u => published_level_thm u
  | Sampled => fun u => proj1 (published_level_thm u)
  | AnalysisBridged => fun u => proj1 (proj1 (published_level_thm u))
  end r.

Definition view_identification_of_sampled (r : PublishedSampled)
    : sampled_viewE_prop (sp_f (published_level_at r)) :=
  proj2 (published_level_thm r).
```

One reader serves every level; the dependent match needs the explicit
`return` clause and nothing else. At S_5:

```coq
Definition s5_det_published_recovers
    (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile))
    (Gw0 : w0 \in pgg_G (mp_M S5Analysis.profile)) :
  exec_decode S5Analysis.exec_plug
    (OE.oe_endpoints_size S5Analysis.observed s w0) = s :=
  match run_correct_of_level s5_det_published s w0 Gw0 with
  | And3 _ _ H => H
  end.
```

Its type and the type `manifest/pgg_analysis_manifest.v` pins for
`S5Analysis.observed_recovers` print identically:

```
forall (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
w0 \in pgg_G (mp_M S5Analysis.profile) ->
exec_decode S5Analysis.exec_plug
  (OE.oe_endpoints_size S5Analysis.observed s w0) = s
```

## T5, the four rejections

Each was compiled once without `Fail`, in its own file, and each is a type
mismatch and not an unknown reference.

`t5_msg_view_secrecy.v`:

```
Error:
In environment
r : PublishedObserved
The term "r" has type "PublishedObserved" while it is expected to have type
 "PublishedAt ?c".
```

`t5_msg_security_property.v`: the same message, at `security_property_of r`.

`t5_msg_not_published.v`:

```
Error:
In environment
r : PublishedObserved
The term "r" has type "PublishedObserved" while it is expected to have type
 "Published".
```

`t5_msg_executable.v`:

```
Error:
In environment
a : AssumptionStatus
s : Tableau Executable
The term "s" has type "Tableau Executable" while it is expected to have type
 "Tableau Observed".
```

## T6, which transfer statuses a Sampled program may carry

The docstring of `TransferStatus` in `manifest/pgg_analysis_status.v`, in
full:

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

Three variants compiled.

1. Unrestricted, `t_framework.v` and `t_pgl27.v`. A status is data, so
   `publish_sampled BaselineClassicalOnly IdealFinite pgl27_word_sampled`
   typechecks and is the value `pgl27_word_published_idealfinite`.
2. The spec's pair, `t_framework.v`: `SampledTransfer` with
   `SampledNoModelComparison` and `SampledNegativeTransfer`, mapped by
   `transfer_of_sampled`. It refuses `IdealFinite`
   (`t6_msg_restricted.v`):

```
Error:
In environment
a : AssumptionStatus
s : Tableau Sampled
The term "IdealFinite" has type "TransferStatus"
while it is expected to have type "SampledTransfer".
```

3. The docstring's own split, `t6_alt_split.v`: `SampledNoTransferTheorem`
   with `NoTheoremNoModelComparison` and `NoTheoremStaticExecutedOnly`. It
   refuses both `IdealFinite` and `NegativeTransfer`, and the spec's pair in
   turn refuses `StaticExecutedOnly`.

Recommendation: **keep `TransferStatus` unrestricted as the payload of
`publish_sampled`, and do not land `SampledTransfer`.** Three reasons, the
first two of which are what the docstring says rather than what the spec
assumed.

- The docstring separates `{IdealFinite, NegativeTransfer}`, each of which
  names a theorem, from `{StaticExecutedOnly, NoModelComparison}`, each of
  which names an absent premise. The spec's pair cuts across that line: it
  admits `NegativeTransfer`, whose obstruction theorem a `PublishedSampled`
  does not hold, and refuses `StaticExecutedOnly`, whose static-to-executed
  bridge is exactly the second conjunct of `StackProp Sampled`. So the
  spec's pair is not the restriction the docstring licenses.
- No level stores a theorem for its status. At `AnalysisBridged` the
  transfer theorem is a facade alias pinned by the manifest's prose table and
  its `erefl` status checks, and `publish` takes any `TransferStatus`.
  Restricting only at `Sampled` would make the framework strict at the level
  whose claim is smallest and lax at the level whose claim is largest.
- The refutations of tracker step 4.2 need `NegativeTransfer` from `Sampled`
  and have no certify statement to hand their obstruction theorem to, so any
  restriction that excludes `NegativeTransfer` blocks them, and any that
  includes it is not the docstring's split.

If the owner prefers a restriction anyway, the honest one is variant 3, and
it forces a prior decision: step 4.2's refutations then need a statement that
carries the obstruction theorem into the program, which is that batch's
question and not this one's.

## T7, the word model published at Sampled

```coq
Definition pgl27_word_published_sampled : PublishedSampled :=
  publish_sampled BaselineClassicalOnly NoModelComparison pgl27_word_sampled.

Lemma pgl27_word_published_completionE :
  ap_completion (published_level_path pgl27_word_published_sampled) = Sampled.

Lemma pgl27_word_path_completionE :
  ap_completion pgl27_word_path = AnalysisBridged.

Lemma pgl27_word_published_modelE :
  ap_model (published_level_path pgl27_word_published_sampled)
  = sp_f (tableau_at pgl27_word_sampled).
```

The path is not the manifest's word path. `t7_msg_path.v`, without `Fail`:

```
Error:
The term "erefl" has type
 "published_level_path pgl27_word_published_sampled =
  published_level_path pgl27_word_published_sampled"
while it is expected to have type
 "published_level_path pgl27_word_published_sampled = pgl27_word_path"
(cannot unify "published_level_path pgl27_word_published_sampled" and
"pgl27_word_path").
```

`Print Assumptions pgl27_word_published_sampled` reports the classical trio
and nothing else.

## T8, the keyword surface

```coq
Notation "s |> 'publish' 'observed' a" := (publish_observed a s)
  (at level 90, left associativity, a at level 0).

Notation "s |> 'publish' 'sampled' a t" := (publish_sampled a t s)
  (at level 90, left associativity, a at level 0, t at level 0).
```

Both tokens sit immediately after the literal `publish`, and every slot of
both rules comes last, so no token of either rule follows a slot. That is the
condition the header of `manifest/pgg_tableau_syntax.v` states for a token to
stay an identifier, and the measurement confirms it. `t_keyword_check.v`,
whose only imports are `ssreflect` and the probe syntax file, compiles clean
and prints:

```
fun observed : nat => observed
     : nat -> nat
fun sampled : nat => sampled
     : nat -> nat
observed
     : nat
sampled
     : nat
```

Binder use and a top-level `Definition observed : nat := 0.` both succeed, so
neither token is reserved and the nineteen existing keywords are untouched.
Independently: of the twenty-one files in the tree that require the statement
surface, none writes `observed` or `sampled` outside a comment, so even a
reservation would break nothing today. One layer below, `AnalysisModelFamily`
and `AnalysisModelSlot` bind `observed` and `Arguments amf_sample {observed}`
names it, which is what a reservation would have cost later.

The existing terminal still parses beside the two new rules, at a bare
identifier in the slot where the new rules put a literal:

```coq
Definition probe_bridged_terminal : Published :=
  @MkTableau AnalysisBridged (StackProp AnalysisBridged) qb pfb
  |> publish IdealFinite BaselineClassicalOnly.
```

A whole program of the five-seat instance in the surface, and its two
equations, both `exact: erefl`:

```coq
Definition s5_det_published_program : PublishedObserved :=
  s5_algebra
    dealt   fuel 150
    execute terminates by s5_dealt_terminates
            endpoints by s5_dealt_endpoints
            recon by s5_dealt_recon
  |> publish observed (AcceptsAxioms [:: AxS5GroupOrder]).

Lemma s5_det_published_programE :
  s5_det_published_program = s5_det_published.

Lemma s5_det_published_program_pathE :
  published_level_path s5_det_published_program = s5_det_path.
```

`s5_det_published_programE` is what shows the new rule fired rather than the
existing one parsing `observed` as a term: its right side is
`publish_observed` applied by hand.

## T9, the assumptions

`Print Assumptions` of `s5_dealt`, of `s5_det_published`, of
`s5_det_published_pathE` and of `s5_det_published_recovers` return the same
four lines:

```
Axioms:
rigidity_s5_instance.s5_group_order_eq :
  #|pgg_G (Gen_PGGTypes (pgg_raag_path.path_gen_tuple 3))| = 120%R
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

The record, the terminals and the readers add nothing: the published value's
assumptions are the program's own.

## Departures from the spec

1. T6's instance half is in `t_pgl27.v`, not `t_framework.v`. The spec files
   T6 under the framework file, but the compile it asks for names
   `pgl27_word_sampled`. The framework half, the restricted payload type, is
   where the spec puts it.
2. `t6_alt_split.v` is a file the spec does not list. It exists because the
   spec's proposed pair is not the pair the `TransferStatus` docstring
   separates, and the recommendation needs the alternative compiled rather
   than argued.
3. Seven message files and `t_keyword_check.v` are not in the spec's file
   list, but its own evidence rules require them: `rocq compile` prints
   nothing for a passing `Fail`, and compilation stops at the first error, so
   one rejection needs one file.
4. The two terminals take the whole `Tableau`, as the spec's Design section
   writes their signatures, not the `(q, pf, payload)` shape `publish` has.
   `publish_sampled_step` is compiled in that shape as well and
   `publish_sampled_stepE` shows the two are one term.
5. T7's value is published at `NoModelComparison`. The spec does not fix a
   status for it; `IdealFinite` is compiled separately under T6.
6. T3's mutation is a `Fail Definition ... := erefl`, not a failing `Lemma`.

## What misled me, for the record

- The concurrent production rebuild is not one transient error but a front
  that climbs the tree: over twenty minutes it moved from
  `pgg_analysis_manifest` to `pgg_tableau` to `pgg_tableau_syntax`, and each
  step also invalidated the probe `.vo` files an earlier attempt had already
  built. A per-file retry loop cannot converge under that, because it never
  rebuilds the probe file below the one it is retrying. The whole ordered
  pass has to restart from the top on any inconsistent-assumptions failure.
  With that change the entire chain landed in one 78-second pass.
- `Require Import` is not transitive. `t_s5.v` first required `s5_exec`,
  which uses `exec_decode` and `OE` throughout, and neither name was in
  scope; `pgg_monodromy_profile`, `pgg_execution_plug` and
  `pgg_observed_execution` had to be required by name.

## What is left

- The spec's two audits, soundness and naming, before a landing plan. Neither
  was run here.
- The owner's decision on T6.
- Out of scope and untouched, as the spec says: `restate` below the top
  level, and a place for `realises_expected` in the accumulated proposition.
- Landing homes unchanged from the spec: `manifest/pgg_tableau.v` for the
  record, the terminals and the readers, `manifest/pgg_tableau_syntax.v` for
  the two notations, `instances/s5/tableau/s5_tableau_observed.v` for the
  value and its equation.
