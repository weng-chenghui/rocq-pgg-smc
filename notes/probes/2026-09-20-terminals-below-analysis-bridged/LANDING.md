# Terminals below AnalysisBridged: the landing (2026-09-21)

Spec and plan: `notes/20260920-terminals-below-analysis-bridged-probe-design.md`,
last section. Probe: this directory. Branch `feat/tableau-extensions-probe`.
Four production files edited, all additions except the header prose and index
blocks the plan names (Z12, Z13, Y7). Zero `Admitted`, `Abort`, `Axiom`. Every
equation closes by `exact: erefl`. No `make`, no git write, nothing deleted.

## The flow

```
s5_algebra                                      // Algebraic;  proposition: True
  dealt fuel 150                                // Executable; proposition: True
  execute terminates by s5_dealt_terminates
          endpoints  by s5_dealt_endpoints
          recon      by s5_dealt_recon          // Observed;  + run correctness
  |> publish Observed (AcceptsAxioms [:: AxS5GroupOrder])
                                                // PublishedObserved. Accumulated:
                                                //   run correctness, carried not
                                                //     re-proved
                                                // + MkAnalysisPath (ob_obs q)
                                                //     Observed None
                                                //     NoModelComparison a
                                                //   = s5_det_path, by conversion
                                                // + 0 security properties

<program> sample f                              // Sampled;   + the link lemma
  |> publish Sampled SampledNoModelComparison a
                                                // PublishedSampled. Accumulated:
                                                //   run correctness /\ link lemma
                                                // + path at Sampled, model slot
                                                //     sp_f q, transfer status
                                                //     transfer_of_sampled t
                                                // + 0 security properties, and
                                                //   the two statuses that name a
                                                //   transfer theorem are not
                                                //   writable in that slot
```

Outside the program: the assumption status, which no level's proposition
determines and which each terminal therefore takes as a payload; and the
manifest's prose table, against which that status is read by eye.

Monad verdict: `TableauAt` is a parameterised monad indexed by pre- and
post-`CompletionLevel`, with `tableau_start` the unit, `tableau_bind` the bind
and the left unit definitional (`tableau_left_unit`, `exact: erefl`). It is not
graded, because the accumulated value is a proposition and not a monoid
element. The two new terminals are morphisms out of that structure at two fixed
indices and add no structure of their own.

Each existing definition and the interface it enters through:

| component | role | interface |
|---|---|---|
| `s5_algebra` (`instances/s5/pgg_raag_s5.v`) | first object | `tableau_start`, through the `dealt` rule |
| `dealt_step`, `execute_step` (`manifest/pgg_tableau.v`) | steps | `A dealt fuel n`, `s execute terminates by ...` |
| `s5_dealt_terminates`, `s5_dealt_endpoints`, `s5_dealt_recon` (`instances/s5/s5_exec.v`) | step justification | `obs_payload`, through the `execute` rule |
| `tableau_bind` (`manifest/pgg_tableau.v`) | sequencing | `s ;;; f 'of' p`, to which both new rules expand |
| `ob_obs`, `sp_obs`, `sp_f` (`manifest/pgg_tableau.v`) | the coordinates a path is built from | read by the terminals off `StackAt` |
| `StackProp` (`manifest/pgg_tableau.v`) | the carried proposition | the third field of each record |
| `MkAnalysisPath`, `AnalysisModelSlot` (`manifest/pgg_analysis_manifest.v`), `TransferStatus`, `AssumptionStatus` (`manifest/pgg_analysis_status.v`) | packaging | the two terminals |
| `s5_dealt`, `s5_det_path` | the instance argument and the path answered | `publish_observed` and its path equation |

## What landed, per file

### `manifest/pgg_tableau.v`, one new section at lines 1066-1219

Banner `Handing a program over below AnalysisBridged`, between
`security_property_of` and the banner `Where a program's security property is
decided`. Header paragraph added after the "Two things stay outside the
program" paragraph. Index entries added to `Definitions:` and `Key results:`
at the file's own columns (name at 5, `==` at 28, description at 31).

```coq
Record PublishedObserved := MkPublishedObserved {
  published_observed_at   : StackAt Observed ;
  published_observed_path : AnalysisPath ;
  published_observed_thm  : StackProp Observed published_observed_at }.
Arguments published_observed_thm : clear implicits.

Record PublishedSampled := MkPublishedSampled {
  published_sampled_at   : StackAt Sampled ;
  published_sampled_path : AnalysisPath ;
  published_sampled_thm  : StackProp Sampled published_sampled_at }.

Variant TransferStatusWithoutTheorem :=
  SampledNoModelComparison | SampledStaticExecutedOnly.

Definition transfer_of_sampled (t : TransferStatusWithoutTheorem)
    : TransferStatus :=
  match t with
  | SampledNoModelComparison => NoModelComparison
  | SampledStaticExecutedOnly => StaticExecutedOnly
  end.

Definition publish_observed (q : StackAt Observed) (pf : StackProp Observed q)
    (a : AssumptionStatus) : PublishedObserved :=
  @MkPublishedObserved q
    (@MkAnalysisPath (ob_obs q) Observed None NoModelComparison a) pf.
Arguments publish_observed : clear implicits.

Definition publish_sampled (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (t : TransferStatusWithoutTheorem)
    : PublishedSampled :=
  @MkPublishedSampled q
    (@MkAnalysisPath (sp_obs q) Sampled (sp_f q) (transfer_of_sampled t) a) pf.
Arguments publish_sampled : clear implicits.

Lemma publish_observed_completionE (q : StackAt Observed)
    (pf : StackProp Observed q) (a : AssumptionStatus) :
  ap_completion (published_observed_path (publish_observed q pf a)) = Observed.
Proof. exact: erefl. Qed.

Lemma publish_observed_transferE (q : StackAt Observed)
    (pf : StackProp Observed q) (a : AssumptionStatus) :
  ap_transfer (published_observed_path (publish_observed q pf a))
  = NoModelComparison.
Proof. exact: erefl. Qed.

Lemma publish_observed_modelE (q : StackAt Observed)
    (pf : StackProp Observed q) (a : AssumptionStatus) :
  ap_model (published_observed_path (publish_observed q pf a)) = None.
Proof. exact: erefl. Qed.

Lemma publish_sampled_completionE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (t : TransferStatusWithoutTheorem) :
  ap_completion (published_sampled_path (publish_sampled a q pf t)) = Sampled.
Proof. exact: erefl. Qed.

Lemma publish_sampled_transferE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (t : TransferStatusWithoutTheorem) :
  ap_transfer (published_sampled_path (publish_sampled a q pf t))
  = transfer_of_sampled t.
Proof. exact: erefl. Qed.

Lemma publish_sampled_modelE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (t : TransferStatusWithoutTheorem) :
  ap_model (published_sampled_path (publish_sampled a q pf t)) = sp_f q.
Proof. exact: erefl. Qed.

Definition run_correct_of_observed (r : PublishedObserved)
  : oe_correct_prop (ob_obs (published_observed_at r)) :=
  published_observed_thm r.
Arguments run_correct_of_observed : clear implicits.

Definition run_correct_of_sampled (r : PublishedSampled)
  : oe_correct_prop (sp_obs (published_sampled_at r)) :=
  proj1 (published_sampled_thm r).
Arguments run_correct_of_sampled : clear implicits.

Definition view_identification_of_sampled (r : PublishedSampled)
  : sampled_viewE_prop (sp_f (published_sampled_at r)) :=
  proj2 (published_sampled_thm r).
Arguments view_identification_of_sampled : clear implicits.
```

### `manifest/pgg_tableau_syntax.v`, two rules at the end, two header facts

```coq
Notation "s |> 'publish' 'Observed' a" := (s ;;; publish_observed of a)
  (at level 90, left associativity, a at level 0).

Notation "s |> 'publish' 'Sampled' t a" := (s ;;; publish_sampled a of t)
  (at level 90, left associativity, t at level 0, a at level 0).
```

Header, line 40 (Z12): "The separator of the two terminal rules is |>" becomes
"The separator of the terminal rules is |>"; the measurement sentence after it
is unchanged. Keyword paragraph (Y7, Z13): a sentence appended inside it,
dated 2026-09-21, saying that each of `Observed` and `Sampled` follows the
literal `publish` in one of the two new rules and stays both a binder name and
the `CompletionLevel` constructor it names, and that inside the publish
position the two tokens are taken by those rules.

### `instances/s5/tableau/s5_tableau_observed.v`

Imports gained `pgg_monodromy_profile pgg_execution_plug` and
`pgg_observed_execution`. Header second paragraph gained one sentence. Two
`Definitions:` entries and one `Key results:` entry, at that file's columns
(name at 5, `==` at 26, description and continuation at 29). Docstrings in
that file's `(** ` style with 4-space continuation.

```coq
Definition s5_dealt_observed_published : PublishedObserved :=
  s5_dealt |> publish Observed (AcceptsAxioms [:: AxS5GroupOrder]).

Lemma s5_dealt_observed_published_pathE :
  published_observed_path s5_dealt_observed_published = s5_det_path.
Proof. exact: erefl. Qed.

Definition s5_dealt_observed_published_recovers
    (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile))
    (Gw0 : w0 \in pgg_G (mp_M S5Analysis.profile)) :
  exec_decode S5Analysis.exec_plug
    (OE.oe_endpoints_size S5Analysis.observed s w0) = s :=
  match run_correct_of_observed s5_dealt_observed_published s w0 Gw0 with
  | And3 _ _ H => H
  end.
```

### `instances/s5/tableau/s5_tableau_checks.v`

Header: "Two boundaries are recorded" becomes "Three", the paragraph rewrapped
word for word otherwise, and one sentence appended naming the third boundary.
New section `No security reader applies to a program published at Observed`
with four recorded rejections, each under a comment about the one term written
below it:

```coq
Fail Check (view_secrecy_of s5_dealt_observed_published).
Fail Check (security_property_of s5_dealt_observed_published).
Fail Check (s5_dealt_observed_published : Published).
Fail Definition s5_dealt_baseline_pathE :
  published_observed_path (s5_dealt |> publish Observed BaselineClassicalOnly)
  = s5_det_path := erefl.
```

## The rejection messages, each compiled once without `Fail`

Files `t2_msg_view_secrecy.v`, `t2_msg_security_property.v`,
`t2_msg_not_published.v`, `t2_msg_baseline_path.v`, `t2_msg_idealfinite.v`;
full output in `t2_msg_outputs.txt`. Every one is a type mismatch, none an
unknown reference and none a syntax error.

```
The term "s5_dealt_observed_published" has type "PublishedObserved"
while it is expected to have type "PublishedAt ?c".
```
(the same message at `view_secrecy_of` and at `security_property_of`)

```
The term "s5_dealt_observed_published" has type "PublishedObserved"
while it is expected to have type "Published".
```

```
The term "erefl" has type
 "published_observed_path
    (s5_dealt |> publish Observed BaselineClassicalOnly) =
  published_observed_path
    (s5_dealt |> publish Observed BaselineClassicalOnly)"
while it is expected to have type
 "published_observed_path
    (s5_dealt |> publish Observed BaselineClassicalOnly) =
  s5_det_path"
(cannot unify "published_observed_path
                 (s5_dealt |> publish Observed BaselineClassicalOnly)"
and "s5_det_path").
```

The fifth message is decision 2's own evidence. It is not a landed `Fail`: the
restriction lands as the payload type of `publish_sampled` and not as a
recorded rejection.

```
The term "IdealFinite" has type "TransferStatus"
while it is expected to have type "TransferStatusWithoutTheorem".
```

## `Print Assumptions`

`landing_fidelity.out`, from production imports alone. All three of
`s5_dealt_observed_published`, `s5_dealt_observed_published_pathE` and
`s5_dealt_observed_published_recovers` report the same four lines, which are
`s5_dealt`'s own:

```
Axioms:
rigidity_s5_instance.s5_group_order_eq :
  #|pgg_G (Gen_PGGTypes (pgg_raag_path.path_gen_tuple 3))| = 120
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

## The keyword measurement, re-run at the capitalised tokens

`t_keyword_check_two_records.v`, whose Require lines are `ssreflect` and the
probe syntax file, compiles clean and prints `fun Observed : nat => Observed`,
the `Sampled` twin, and both tokens rebound by a top-level `Definition`.
`t_syntax_two_records.v` prints `StackAt Observed`, `StackAt Sampled`,
`Tableau Observed`, `Tableau Sampled`, and `Observed : CompletionLevel`,
`Sampled : CompletionLevel`, after both rules are declared. Neither token is
reserved and the header's count of nineteen is unchanged.

The existing rule was measured against the landed rules, not only the probe
ones: `landing_fidelity.v` writes `|> publish t a` at all four transfer
statuses and each is a `Published`. Independently, the thirty-one uses in the
tree write `IdealFinite` twenty times and `StaticExecutedOnly` eleven, and
none writes `Observed` or `Sampled`, so no existing use is captured.

## Compiles, in order, one Rocq process at a time

| file | rc | elapsed |
|---|---|---|
| `t_framework_two_records.v` (probe) | 0 | 4 s |
| `t_syntax_two_records.v` (probe) | 0 | 4 s |
| `t_keyword_check_two_records.v` (probe) | 0 | 3 s |
| `t_s5_two_records.v` (probe) | 0 | 5 s |
| five `t2_msg_*.v` (probe, rc 1 as intended) | 1 | 3-5 s each |
| `manifest/pgg_tableau.v` | 0 | 14 s |
| `manifest/pgg_tableau_syntax.v` | 0 | 5 s |
| `instances/s5/tableau/s5_tableau_algebraic.v` (unedited) | 0 | 4 s |
| `instances/s5/tableau/s5_tableau_executable.v` (unedited) | 0 | 4 s |
| `instances/s5/tableau/s5_tableau_observed.v` | 0 | 3 s |
| `instances/s5/tableau/s5_tableau_sampled.v` (unedited) | 0 | 4 s |
| `instances/s5/tableau/s5_tableau_analysis_bridged.v` (unedited) | 0 | 4 s |
| `instances/s5/tableau/s5_tableau_checks.v` | 0 | 4 s |
| `landing_fidelity.v` (probe) | 0 | 5 s |

Unedited production files recompiled, in topological order, because the edited
framework invalidated them and the later compiles needed them:
`s5_tableau_algebraic.v`, `s5_tableau_executable.v`, `s5_tableau_sampled.v`,
`s5_tableau_analysis_bridged.v`. Everything else in the reverse closure of
`manifest/pgg_tableau.v` is left to the main session.

No line of any edited file exceeds 80 bytes. The three over-80 lines of
`manifest/pgg_tableau_syntax.v` are its pre-existing notation headers, at the
same three line contents as at HEAD.

## Departures from the plan, and why

1. **Extra `Arguments` directives, and a different form from the plan's.**
   Y11 asked for directives mirroring the neighbours' `Arguments publish a {c}
   q pf t.`. Measured: a directive that only lists names changes no implicit
   status and warns `arguments-assert`, and `Set Implicit Arguments` does make
   the data argument implicit here, because `StackProp Observed q` unfolds to a
   statement quantified over a run argument and `q` occurs in that argument's
   type. The landed form is therefore `: clear implicits`, which is the idiom
   the file already uses eleven times. Two directives the plan did not foresee
   were needed for the same reason: `published_observed_thm` and the three
   readers, whose return types are quantified statements. Without them
   `published_observed_thm r` elaborates `r` into the run-argument slot.
2. **`publish_sampled_transferE` reads `= transfer_of_sampled t`, not `= t`.**
   Forced by decision 2: the payload is no longer a `TransferStatus`.
3. **Two probe files the plan's step 1 does not list.**
   `t_syntax_two_records.v`, because the surface rules cannot be measured
   without a file that declares them, and `t_keyword_check_two_records.v`,
   because the lexer question needs a file whose Require lines are ssreflect
   and the rule file alone.
4. **A fifth message file.** The plan names four landing rejections;
   `t2_msg_idealfinite.v` records the message behind decision 2, which lands as
   a type rather than as a `Fail` and would otherwise rest on an unread `Fail`.
5. **Index entries re-drafted.** The naming audit drafted them for the family
   shape, with `RunCorrectProp` and `run_correct_of_level`. Decision 1 deletes
   both, so the entries landed are `PublishedObserved`, `PublishedSampled`,
   `TransferStatusWithoutTheorem`, `transfer_of_sampled`, `publish_observed`,
   `publish_sampled`, `run_correct_of_observed`, `run_correct_of_sampled`,
   `view_identification_of_sampled`, and the six path equations.
6. **The keyword paragraph gained a sentence rather than a rewritten one.**
   Z13 asked for the two tokens inside the sentence that lists tokens following
   a literal. That sentence is dated 2026-09-14 and folding a 2026-09-21
   measurement into it would re-date a measurement that was not re-run. The two
   tokens are named in the same paragraph, in their own sentence, under their
   own date, and Y7's measured fact follows there.
7. **`s5_tableau_checks.v`'s header count.** "Two boundaries are recorded"
   became "Three", which forced the paragraph to be rewrapped. A word-level
   diff of the preserved text shows only that word changed and one sentence
   appended.

Nothing else departs. Decision 1 (two records) and decision 3 (bind shape)
both compiled as planned, so the stopping rule was not reached: no declaration
needed a second attempt beyond the two `Arguments` corrections above, which
were compiler-reported and fixed at the first retry.

## Names

Every name introduced was checked free twice: by grep over the 225 tracked
`.v` files outside `notes/`, legacy included, and by a `Locate` block compiled
under the home file's own imports at the head of `t_framework_two_records.v`,
which printed `No object of basename` for all twenty-five.

## What this landing does not do

The PGL(2,7) `Sampled` value does not land (Z20, Q4: the manifest holds no
path at `Sampled` over that model). The whole-program surface values and the
identifier checks stay in the probe. Neither unchosen T6 variant lands, and
`publish_sampled_step` and its equation do not. `restate` below the top level
and a place for `realises_expected` in the accumulated proposition remain out
of scope, as the spec says.

## Fix pass

Applied 2026-09-21 over the uncommitted landing, under `landing_rulings.md`.
Nothing was compiled and no Rocq process was started. Line and column numbers
below are the post-pass ones.

### The two renames

**B7, `transfer_of_sampled` -> `transfer_of_without_theorem`.** Free in the
tracked tree before the pass (grep over all `.v`, `.md`, `.tex`: only the two
audit notes and this file mentioned it). Five sites:

| file:line | site |
|---|---|
| `manifest/pgg_tableau.v:147` | index entry, B12's two-line form |
| `manifest/pgg_tableau.v:1112` | the definition |
| `manifest/pgg_tableau.v:1149` | `publish_sampled`'s body |
| `manifest/pgg_tableau.v:1190` | `publish_sampled_transferE`'s statement |
| `landing_fidelity.v:61,63,65,103` | the four probe uses |

The body at 1148-1149 no longer fits one line at the longer name, so the
`MkAnalysisPath` application is split after `(sp_f q)`; the token stream is
unchanged. `landing_fidelity.v:61` was likewise split after the head.

**B8, `s5_dealt_baseline_pathE` ->
`s5_dealt_observed_published_baseline_pathE`.** Free before the pass. Two
sites: `instances/s5/tableau/s5_tableau_checks.v:98` (inside the `Fail
Definition`) and `t2_msg_baseline_path.v:16` (the message file source,
regenerated, not compiled).

After the pass, `grep` for either old name over the four landed files,
`landing_fidelity.v` and `t2_msg_baseline_path.v` returns zero hits.

### Comment findings, old line then new line

**A5 + A3/B21, `manifest/pgg_tableau.v:80-95`, file header.**
Old: "A program that stops at Observed hands over run correctness with the
manifest path its own data builds, and one that stops at Sampled hands over
run correctness and the link lemma of the model family it named." and "so a
later reading of PublishedAt as one of them would turn each recorded
rejection into an acceptance."
New: "A program that stops at Observed hands over run correctness with a
manifest path whose observed execution is the program's own, whose level,
model slot and transfer status the terminal fixes, and whose assumption
status is the payload the line writes. One that stops at Sampled hands over
run correctness and the link lemma of the model family it named." and "so a
coercion added later out of either record into PublishedAt would turn each
recorded rejection into an acceptance."

**A9 + B12 + B13, `manifest/pgg_tableau.v:144-151`, index entries.**
Old: `== the transfer statuses asserting no theorem`;
`transfer_of_sampled    == the manifest status such a payload stands for`;
`publish_observed       == the terminal of a program that stops at run` /
`correctness`; `publish_sampled        == the terminal of a program that
stops at its` / `named model`.
New: `== the transfer statuses carrying no theorem`; the three-line entry
`transfer_of_without_theorem` / `== the manifest transfer status a payload of
the` / `Sampled terminal stands for`;
`publish_observed       == the terminal of a program stopped at Observed`;
`publish_sampled        == the terminal of a program stopped at Sampled`.
Measured columns of this block: name at 5, `==` at 28, description and
continuation at 31, every line exactly 80 bytes.

**A4, `manifest/pgg_tableau.v:1073-1080` and `:1091-1095`.**
Old: "The three fields are independent, as the three of PublishedAt are: the
terminal below builds the path from the program's own data, and the record
does not force a path written by hand to describe the data beside it." and
"The three fields are independent in the same sense."
New: "The path field is constrained by neither of the other two, as
PublishedAt's is not: the terminal below builds it from the program's own
data, and the record accepts any path written by hand beside any data. The
proposition field is typed at the data field, as PublishedAt's third field
is." and "The path field stands in the same relation to the other two."
Checked against `PublishedAt` at 1001-1004: `published_thm : BridgedProp c
published_at` is typed at the first field, as
`published_observed_thm : StackProp Observed published_observed_at` is.

**A9 + B11, `manifest/pgg_tableau.v:1101-1105`, the `Variant`.**
Old: "The two transfer statuses that assert no theorem about an idealized
model." and the closing "The restriction is on the terminal below and not on
the record: a value written by hand still carries any path."
New: "The two transfer statuses that carry no theorem about an idealized
model."; the closing sentence is deleted here and lands on `publish_sampled`.

**B14, `manifest/pgg_tableau.v:1109-1111`.**
Old: "The manifest's own status such a payload stands for."
New: "The manifest transfer status a restricted payload stands for. It is the
coordinate a reader of such a path finds, so the two statuses naming a
transfer theorem never appear on a path the Sampled terminal built."

**B4, `manifest/pgg_tableau.v:1119-1126`.**
Old: "The path is built from the program's own data: the observed execution
the program reached, the level Observed, the empty model slot, and
NoModelComparison, which is not a payload because ..."
New: "The path takes the observed execution from the program's own data and
the terminal writes the other three coordinates: the level Observed, the
empty model slot, and NoModelComparison, which is not a payload because a
program naming no model compares its execution with nothing."

**B11, `manifest/pgg_tableau.v:1137-1143`, on `publish_sampled`.**
New sentence, placed after the clause about the restricted payload type:
"The restriction is carried by this terminal and not by the record, whose
path field accepts any path."

**B19, `manifest/pgg_tableau.v:1151`.**
Old: "Explicit for the reason publish_observed's directive gives."
New: "The data occurs in the type of the proof here too."

**B17, `manifest/pgg_tableau.v:1154-1156`.**
Old: "so the manifest's sentence about how far a path's theorems reach is a
term at this level and not prose."
New: "so a reader of the value learns the level its program stopped at
without consulting the manifest."

**A11, `manifest/pgg_tableau.v:1201-1206`.**
Old: "It is the whole content of such a value, and the proof is the observed
execution's own field, so the terminal hands back what the instance
discharged and the reader adds nothing to it."
New: "It is the whole of what such a value proves, and the reader is the
third field itself, so a value the execute rule built hands back the
instance's own run-correctness field and the reader adds nothing to it."

**B15, `manifest/pgg_tableau.v:1212-1214`.** Appended: "A reader of such a
value learns that the run finished and that its endpoints decode, and nothing
about a coalition."

**B16, `manifest/pgg_tableau.v:1220-1223`.**
Old: "and the fact a security statement about this model would be made along
were one proved."
New: "and the hypothesis along which a security statement about this model
would be transported, were one proved."

**A2 + B1 + B24, `manifest/pgg_tableau_syntax.v:80-90`.**
Old: "Observed and Sampled belong to that first list too, measured on
2026-09-21: each follows the literal publish in one of the two terminal rules
below AnalysisBridged, and each is still a binder name and still the
CompletionLevel constructor it names, in a file whose Require lines are
ssreflect and this one."
New: "Observed and Sampled follow a literal too, measured on 2026-09-21: each
follows the literal publish in one of the two terminal rules below
AnalysisBridged, each stays a binder name in a file whose Require lines are
ssreflect and this one, and each stays the CompletionLevel constructor it
names, as Tableau Observed in s5_tableau_observed.v and Tableau Sampled in
s5_tableau_sampled.v write it. The count of nineteen is unchanged."
The binder half keeps the probe file's measurement, the constructor half
takes the production citation B24 asks for: `Tableau Observed` at
`s5_tableau_observed.v:100`, `Tableau Sampled` at `s5_tableau_sampled.v:71`,
both verified by grep. No new probe file.

**B2 + A10, `manifest/pgg_tableau_syntax.v:87-90`.**
Old: "so a transfer status spelled Observed or Sampled could not be written
where the other thirty-one uses write theirs."
New: "so the transfer-status slot of the three-payload rule cannot be filled
by a bare token spelled Observed or Sampled, though a parenthesised one
reaches the slot." A10's narrowing is the one clause "bare" plus the closing
clause; the census is gone, as B2 asks.

**B3, `manifest/pgg_tableau_syntax.v:434-437`.**
Old: "One payload, the assumption status: the level, the model slot and the
transfer status of the path are all read off the program's own data."
New: "One payload, the assumption status. The terminal takes the observed
execution from the program's own data and writes the other three coordinates
itself: the level, the empty model slot and NoModelComparison."

**B18, `manifest/pgg_tableau_syntax.v:441-444`.**
Old: "the order the existing publish rule writes them"
New: "the order the three-payload publish rule writes them"

**A12 + B23, `instances/s5/tableau/s5_tableau_observed.v:22-26`, header.**
Old: "The dealt program is handed over at this level with the path it
answers." and "the assumption status written into its path is a statement of
the author".
New: "The dealt program is handed over at this level with the manifest path
it builds." and "the assumption status written into its path is the author's
statement".

**A8, `instances/s5/tableau/s5_tableau_observed.v:62-64`.** The entry
`s5_dealt_observed_published_recovers == the endpoints of that run decode to
the dealt position, read off the published value` moves out of `Definitions:`
and into `Key results:`, last, which is its file order (the declaration is at
154, after `s5_dealt_observed_published_pathE` at 146). Wording unchanged;
columns of that block are name at 5, `==` at 26, description at 29.

**A12, `instances/s5/tableau/s5_tableau_observed.v:127`.**
Old: "The dealer-dealt run handed over with the manifest path it answers."
New: "The dealer-dealt run handed over with the manifest path it builds."

**A1 + B5 + B6, `instances/s5/tableau/s5_tableau_observed.v:138-145`.**
Old: "Four of its five coordinates are fixed by the terminal and the fifth is
the observed execution s5_dealt_path_observedE already identifies, so what
the equation adds is that the theorem now travels beside the path rather than
the path being a description a reader matches by eye."
New: "Three of its five coordinates are fixed by the terminal, the assumption
status is the payload this file writes, and the fifth is the observed
execution s5_dealt_path_observedE already identifies. A reader of the value
therefore holds the manifest's path for this program and the proof of run
correctness in one term. The equation holds only for the assumption status
the program was published under, as the recorded rejection in
s5_tableau_checks.v shows."
This is the rulings' merged wording, with the manifest's record named as a
path. Checked against `publish_observed`
(`@MkAnalysisPath (ob_obs q) Observed None NoModelComparison a`): three
constants, one coordinate off the data, one payload.

**B20, `instances/s5/tableau/s5_tableau_observed.v:150-153`.**
Old: "the two other conjuncts of the same And3 come off the same reader."
New: "the two other conjuncts come off the same reader."

**B22, `instances/s5/tableau/s5_tableau_checks.v:22`, header.**
Old: "the path that value builds records the assumption status it was
published under"
New: "the path built for that value records the assumption status it was
published under"

**A13 + B9, `instances/s5/tableau/s5_tableau_checks.v:73`, banner.**
Old: `(*     No security reader applies to a program published at Observed
*)`
New: `(*     Terms refused at the dealer-dealt program published at Observed
*)`, measured at exactly 80 bytes with a space before the closing delimiter.

**A6, `instances/s5/tableau/s5_tableau_checks.v:86-88`.**
Old: "Nor is that value a Published. The two are distinct inductive types
with no coercion between them, so the ascription written here is refused."
New: "Nor is that value a Published, which is PublishedAt at the empty bound.
PublishedObserved and PublishedAt are distinct inductive types with no
coercion between them, so the ascription written here is refused."
Checked against `Notation Published := (PublishedAt no_concluded_bound).` at
`manifest/pgg_tableau.v:1009`.

**A7, `instances/s5/tableau/s5_tableau_checks.v:91-97`.** Appended: "Both
sides of that disagreement are written by hand, the payload here and the
manifest's field there, so what the kernel decides is whether two authors'
statements agree and not which axioms the program uses."

### Findings not applied as written

**B10** is subsumed by **A11**, which rewrites the same span
(`run_correct_of_observed`'s docstring) and removes the defect B10 names: the
new sentence no longer gives the act two subjects, and the terminal is no
longer its subject. Writing both would have produced two versions of one
clause. A11's text is what landed.

### A12 at the two sites the finding did not name

Ruled to be in scope: A12 covers every occurrence of the phrase in
`instances/s5/tableau/s5_tableau_observed.v`, so the two the auditor did not
cite are fixed too, and no occurrence of "answers" is left in the file. At the
header site the subject of "it" is the dealer-dealt run's program, which does
not build the path (the terminal builds it for the published value), so "it
builds" would be false there and the true form names the value: line 15 reads
"the manifest path s5_det_path its published value builds carries no model and
no security payload", which the equation `s5_dealt_observed_published_pathE`
supports. The index entry at line 41 reads "the dealer-dealt program handed
over with the / manifest path it builds", re-padded to exactly 80 bytes with a
space before the closing delimiter. The header paragraph was re-wrapped from
line 14 to line 26; the token comparison of the file was rerun and reports no
code-token difference at all against the pre-pass copy (462 tokens either
way), with no changed line over 80 bytes and no barred word.

### Finishing checks

1. **Comment-stripped token comparison** against the pre-pass copies of the
   four files (nested comments and string literals handled; tokens are
   identifiers, qualified names, string literals and single symbols). Token
   counts are equal in all four files, and the only differences reported are
   four single-token replacements: three `transfer_of_sampled` ->
   `transfer_of_without_theorem` in `manifest/pgg_tableau.v` (the index entry
   is inside a comment and so not a code token) and one
   `s5_dealt_baseline_pathE` -> `s5_dealt_observed_published_baseline_pathE`
   in `s5_tableau_checks.v`. No other code token changed in any of the four
   files.
2. **Width.** No changed line in the four files exceeds 80 bytes. The three
   pre-existing over-80 lines of `manifest/pgg_tableau_syntax.v` (343, 381,
   412, all `Notation` lines) are untouched. Both banners and every index
   line touched are exactly 80 bytes with a space before ` *)`.
3. **Vocabulary.** A scan of every changed line for the owner's barred list,
   the two barred nouns of the prose sheet, `L`-plus-digit tokens, and the
   status words "now", "still", "existing", "new" returns nothing. The
   manifest's record is written "path" everywhere in the new text, including
   in the merged A1/B5/B6 docstring where one auditor's replacement had used
   the removed word.
4. **Nothing was compiled**, no Rocq process was started, no git command that
   writes was run, and nothing under `notes/probes/` was deleted.
