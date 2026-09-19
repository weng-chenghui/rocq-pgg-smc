# Stage D — the PSL(2,11) word model and its row through the proximity arm

Spec ledger row P6, with its share of P3, P7, K1, G1, D1 and D2.
Repository `rocq-pgg-smc` at HEAD `ceb2317`, branch `feat/tableau-extensions-probe`.
Probe `notes/probes/2026-09-19-tableau-extensions`, logical path `tableau_ext_probe`.

## Verdict per item

| Item | Verdict | Where |
|---|---|---|
| 1. The word model, its family, its cut-law lemma | GO | `p6_psl211_word_model.v` |
| 2. The certificate and the row | GO, published at the certificate's own number | `p6_psl211_word_proximity.v` |
| 3. P3, `_armE`, the average sentence | GO | `p6_psl211_word_proximity.v` |
| 4. P7: the number against the ceiling, two recorded `Fail`s, the tautology probe | GO | `p6_psl211_word_proximity.v`, `p6_mutations.v` |
| 5. G1: no stage A, B or C `.v` file edited, `_CoqProject` gained four lines | GO | `history/_CoqProject.11-before-stageD` |
| 6. D1/D2: permanent homes and closures | GO, a new file is the only safe home | below |
| 7. Assumptions | GO, the three boolp constants only, the production row's own | `assumptions_report_stageD.v` |

No `Admitted`, `Abort`, `Axiom` or `Parameter` is written anywhere in stage D.
Nothing outside the probe directory was touched. Nothing under `notes/probes/`
was deleted. No production file was compiled and `psl211_endpoints.v` was never
touched, so its 900 s rebuild was never triggered.

## The numbers

- The certificate's number, `ipc_eps (psl211_word_proximity_cert R idx)`, is
  `2%:R^-40`. Exactly `1/1099511627776`, as a decimal
  `9.094947017729282379150390625e-13`.
- The published number is the same, `2^-40 = 9.094947017729282379150390625e-13`.
  The row carries no `conclude`, so it publishes the number its certificate
  proves.
- `var_dist` is the sum of absolute differences, which is twice the total
  variation distance of the literature, so a distinguisher's advantage against
  this row is at most `2^-41 = 4.5474735088646411895751953125e-13`.
- The ceiling every variation distance meets is two, so the certificate stands
  at about `4.5e-13` of the ceiling.

## Why the row does not conclude at a named constant

The brief allows a `conclude` at a named constant when there is a reason. There
is none here. The eight-card orbit instance concluded its word row at `2^-39`
because a spectral row over the same model publishes that constant and the two
are read in one column. The twelve-card instance has no spectral row: the
constancy field a spectral certificate needs is refuted at this model in both
run modes, `psl211_alldecks_constancy_false` and `psl211_dealt_constancy_false`
of `instances/psl211/psl211_spectral_constancy.v`, and
`psl211_alldecks_no_small_eps_cert` excludes every shuffle bound strictly below
`1/1320`. There is therefore no column to line up with and no constant a paper
cites for this model, so the row publishes plainly. The payload of a `conclude`
would have had to be a `<=`; none is written.

## The word model

The sample space is the one the all-decks adapter already uses,
`psl211_inputT * pgg_gT psl211_M`, with the law of the cut coordinate replaced.
That is a real difference from the eight-card orbit instance, whose word model
lives on `bool * 200.-tuple 'I_5` and therefore needed a second reading of the
secret. Here `psl211_alldecks_secret` is the secret of both models as one term,
and the certificate's `ipc_secret` field is that term with no retyping.

Key statements, verbatim.

```coq
Definition psl211_word_cutP (R : realType) : R.-fdist (pgg_gT psl211_M) :=
  @rho_from_words_weighted R 10 2 584 psl211_moves (psl211_Wuni R).

Definition psl211_wordP (R : realType)
  : R.-fdist (psl211_inputT * pgg_gT psl211_M)%type :=
  (`U psl211_alldecks_gt0) `x (psl211_word_cutP R).

Definition psl211_word_sample (R : realType)
  : SampleAdapter R (instance_exec psl211_alldecks_params) :=
  @MkSampleAdapter R (instance_profile psl211_algebra)
    (instance_exec psl211_alldecks_params)
    ((psl211_inputT * pgg_gT psl211_M)%type : finType)
    (psl211_wordP R) fst snd.

Definition psl211_word_family : AnalysisModelFamily psl211_alldecks_observed :=
  @MkAnalysisModelFamily psl211_alldecks_observed (fun _ => unit)
    (fun R _ => psl211_word_sample R).

Lemma psl211_word_cut_distE (R : realType) :
  @sa_cut_dist R (instance_profile psl211_algebra)
    (instance_exec psl211_alldecks_params) (psl211_word_sample R)
  = psl211_word_cutP R.
Proof. exact: fdist_prod_snd. Qed.

Lemma psl211_word_lawE (R : realType) :
  var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2%:R^-40.
Proof.
rewrite /psl211_wordP /psl211_alldecksP /psl211_word_cutP var_dist_prodR.
exact: psl211_word_mixing.
Qed.
```

The parameters `10 2 584 psl211_moves (psl211_Wuni R)` are taken from
`psl211_word_mixing`'s own statement, `instances/psl211/psl211_mixing.v:545`,
and not from the brief. `psl211_Wuni` and `psl211_word_mixing` both discharge
their section variable `R` as an explicit first argument, confirmed by `About`.

`psl211_word_cut_distE` needed no `fdist_ext` script: `sa_cut_dist` at this
adapter is `fdistmap snd` of a product, which is P1's `fdist_prod_snd`
directly. The production twin `psl211_alldecks_cut_distE` runs a four-line
bigop script for the same fact.

## The certificate, the distance and the row

```coq
Lemma psl211_word_proximity_close (R : realType) (C : {set seatT}) :
  (#|C| < profile_k (instance_profile psl211_algebra))%N ->
  var_dist
    (fdistmap (fun u => (@static_coalition_obs psl211_algebra
                           psl211_alldecks_params C
                           ((psl211_word_sample R).(sa_arg) u)
                           ((psl211_word_sample R).(sa_cut) u),
                         psl211_alldecks_secret R u))
       (sa_sampleP (psl211_word_sample R)))
    (fdistmap (fun u => (@static_coalition_obs psl211_algebra
                           psl211_alldecks_params C
                           ((psl211_alldecks_sample R).(sa_arg) u)
                           ((psl211_alldecks_sample R).(sa_cut) u),
                         psl211_alldecks_secret R u))
       (sa_sampleP (psl211_alldecks_sample R)))
  <= 2%:R^-40.
Proof.
move=> _.
apply: var_dist_fdistmap_pair.
rewrite psl211_word_sampleP_E psl211_alldecks_sampleP_E.
exact: psl211_word_lawE.
Qed.

Definition psl211_word_proximity_cert (R : realType) (idx : unit)
  : IdealProximityCert (amf_sample psl211_word_family R idx) :=
  @MkIdealProximityCert R psl211_algebra psl211_alldecks_params
    (amf_sample psl211_word_family R idx)
    (amf_sample psl211_exact_family R idx)
    (psl211_exact_witness R idx)
    (psl211_alldecks_secret R)
    (2%:R^-40)
    (fun C HC => @psl211_word_proximity_close R C HC).

Definition psl211_row_word_proximity : PublishedRow :=
  psl211_alldecks_prefix
    sample  psl211_word_family
    certify IdealProximity psl211_word_proximity_cert
    |> publish IdealFinite BaselineClassicalOnly.
```

Three things about the distance proof are worth recording.

The threshold hypothesis is discarded by `move=> _`. The bound is a fact about
the two laws and holds at every coalition; the threshold enters
`IdealProximityPropAt` and not this field. The hypothesis is kept in the
statement because `ipc_close`'s type demands it.

Both `fdistmap`s are applied to one function. The two adapters read a sample
point by `fst` and `snd`, so `apply: var_dist_fdistmap_pair` unifies the
readers on both sides with no `boolp.funext` step. The eight-card orbit
instance needed two `funext` steps here, its two models living on different
sample spaces.

`profile_k (instance_profile psl211_algebra)` is decided against `6` and
`(#|C| <= 5)%N` by conversion, so `psl211_word_view_proximity` states its
hypothesis as `(#|C| <= 5)%N` and `view_proximity_of` accepts it.

## P3 and the arm

```coq
Lemma psl211_word_proximity_cert_idealE (R : realType) (idx : unit) :
  ipc_ideal (psl211_word_proximity_cert R idx)
  = amf_sample (ab_f (published_at psl211_row_alldecks_tableau)) R idx
  /\ ExactIndependence (ipc_witness (psl211_word_proximity_cert R idx))
     = ab_port (published_at psl211_row_alldecks_tableau) R idx.
Proof. split; exact: erefl. Qed.

Lemma psl211_row_word_proximity_armE (R : realType)
    (idx : amf_index (ab_f (published_at psl211_row_word_proximity)) R) :
  security_arm_of psl211_row_word_proximity R idx = IdealProximityArm.
Proof. exact: erefl. Qed.

Lemma psl211_row_word_proximity_publishedE :
  apr_completion (published_row psl211_row_word_proximity) = AnalysisBridged
  /\ apr_transfer (published_row psl211_row_word_proximity) = IdealFinite
  /\ apr_assumptions (published_row psl211_row_word_proximity)
     = BaselineClassicalOnly.
Proof. split; [exact: erefl | split; exact: erefl]. Qed.
```

Cost of the row and data equations, from the `-time` lines, all far under the
five-second rule, so no cheaper projection had to be substituted and no
statement was weakened:

| sentence | seconds |
|---|---|
| `split; exact: erefl` of `psl211_word_proximity_cert_idealE` | 0.000 |
| its `Qed` | 0.003 |
| `exact: erefl` of `psl211_row_word_proximity_armE` | 0.000 |
| `split; [exact: erefl \| split; exact: erefl]` of `..._publishedE` | 0.000 |
| `exact: (view_proximity_of ...)` of `psl211_word_view_proximity` | 0.118 |

`by []` and `done` were not used on any of them, following the hang shape
recorded in `STATUS.md`. `reflexivity` was not needed, no `exact: erefl` having
come near five seconds.

## Soundness invariant 3: the average sentence

Carried in the statement comment of `psl211_row_word_proximity` and in the
statement comment of `psl211_word_proximity_close`. The claim is an average
over the deck description and the cut. It is not a statement at a fixed deck
description: the reading of a coalition below the threshold is not constant in
the run argument, which `psl211_alldecks_constancy_false` and
`psl211_dealt_constancy_false` of
`instances/psl211/psl211_spectral_constancy.v` refute in the two run modes.
Those refutations stay true beside this row and are cited by name in the row's
comment.

Word gloss, used in every comment of the two files. A deck description is the
whole run argument, a chirality bit together with a deal. A deal is the block
line, the labelling of the heart codes and the labelling of the club codes, the
three coordinates other than the secret. The secret is the chirality bit.

## Recorded rejections

Both are written with `Fail` in `p6_mutations.v`. The decisive error line of
each was obtained by compiling the same term without `Fail` in the scratchpad,
since `rocq compile` echoes nothing for a `Fail` guard. Each rejection is of
one written term and is no proof that no term exists.

**The tautology probe on the distance lemma.** `var_dist_le2` of
`lib/var_dist_supp.v` proves the distance lemma at two with no fact about the
instance and no fact about the walk, and is rejected at `2^-40`:

```
The term "var_dist_le2 ?P ?Q" has type "is_true (var_dist ?P ?Q <= 2)"
while it is expected to have type
 "is_true (var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2 ^- 40)".
```

The pair places the whole content of `psl211_word_lawE` in
`psl211_word_mixing`. The accepted half is kept as
`psl211_word_law_le2`, the only declaration `p6_mutations.v` adds.

**A certificate naming another instance's exact family.** `pgl27_exact_family`
as `ipc_ideal` of a twelve-card certificate:

```
The term "amf_sample pgl27_exact_family R tt" has type
 "SampleAdapter R (OE.oe_execution pgl27_exec.pgl27_observed)"
while it is expected to have type
 "SampleAdapter R (instance_exec psl211_alldecks_params)".
```

The field is rejected at its type, before any distance is looked at.

## Compile table

Every file compiled `rc=0` from the probe directory with the production flags
and `-Q <probe dir> tableau_ext_probe` last, under
`rocq1 900 8000 rocq compile -time`. Wall times include the shared Rocq lock's
own wait; the `-time` sums are the real cost. The four files had no `.vo`
before these runs and were compiled in `_CoqProject` order, so each was built
from its own source and none of them read a `.vo` of another stage D file that
predated this stage; the dependencies below them are the probe's `.vo` files,
built and current at HEAD. The last three were compiled a second time after a
comment-only edit to `p6_psl211_word_proximity.v`, with the same result.

| file | rc | wall | sum of `-time` | sentences | slowest non-import sentence |
|---|---|---|---|---|---|
| `p6_psl211_word_model.v` | 0 | 4.2 s | 4.102 s | 38 | 0.066 s |
| `p6_psl211_word_proximity.v` | 0 | 5.0 s | 4.825 s | 67 | 0.118 s |
| `p6_mutations.v` | 0 | 4.2 s | 4.111 s | 29 | 0.056 s |
| `assumptions_report_stageD.v` | 0 | 244.1 s | 244.00 s | 31 | 23.93 s |

The three source files are dominated by their `Require` lines, the three
largest of which are the mathcomp algebra block, the infotheo block and
`boolp reals`, at about 1.5 s, 1.4 s and 0.8 s each. No sentence outside a
`Require` reaches 0.12 s in them.

The assumptions report is the only file with sentences above five seconds, and
every one of them is a `Print Assumptions`, which the brief exempts. Eleven of
the 21 prints exceed five seconds, between about 21 s and 23.93 s; the other
ten are between 0.01 s and 0.06 s. The split follows what the declaration
mentions. A print on a bare real field, such as `psl211_pow2_40_gt0`, costs
0.01 s; a print on anything that mentions the twelve-card probability model
traverses the instance's interpreter tables and costs about 22 s. The cost is
not something stage D introduces: the production `psl211_row_alldecks_tableau`
print is in the same band.

## Assumptions

Twenty-one `Print Assumptions`, one per declaration stage D writes plus the two
production declarations printed for comparison. Every one of the twenty-one
prints an `Axioms:` block, and every block is the same three constants:

```
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

The whole log was scanned for constant names with `[\w.]+`, which catches a
module-qualified `Axiom` that a `\w+` scan would miss. The names found are the
three above and nothing else. No declaration printed `Closed under the global
context`, which is expected: every one of them mentions an fdist record, and an
fdist record carries the three boolp constants through its own section context.

Stage D therefore rests on exactly what the production all-decks row rests on.
That row was printed here for the comparison: `psl211_row_alldecks_tableau` and
`psl211_alldecks_view_secrecy` each print the same three constants and nothing
more. The twelve-card material adds no constant beyond the eight-card
material's, the extra interpreter tables it passes through being definitions
rather than assumptions.

## D1 and D2: where each declaration would live permanently

The closures below were computed with Python over the `Require` lines of every
`.v` file named by a `-R` or `-Q` entry of the production `_CoqProject`, with
comments stripped, resolving each required name to its file by basename.

**The forbidden set.** `psl211_endpoints` transitively requires 34 files:

```
algebraic_rigidity card_exchange_pismc cover_tradeoff covering_scheme
graded_resource input_encoding perm_exchange perm_uniform pgg_algebra_syntax
pgg_collusion_bound pgg_execution_plug pgg_input_commitment pgg_instance
pgg_interface pgg_monodromy_profile pgg_observed_execution pgg_raag pgg_run
pgg_security_solver pgg_session_types pgg_sharing_framework pgg_sum_mod
pgl_bound pismc psl211_blocks psl211_closure psl211_exec psl211_group
psl211_orbit psl211_profile psl211_scheme smc_interpreter smc_session_types
transitivity_privacy
```

Editing any of those, or `psl211_endpoints.v` itself, forces the 900 s and
17 GB rebuild. None of them is proposed as a home.

**`psl211_mixing.v`** is not in that set. Its reverse closure has one member.
It already holds `psl211_word_mixing`, `psl211_Wuni` and `psl211_moves`'s
consumers, so the word cut law `psl211_word_cutP` could live there at the cost
of one rebuilt file. It is not proposed, because the adapter and the family
need `psl211_models`, which `psl211_mixing.v` does not require.

**`psl211_models.v`** is not in the forbidden set either, so editing it would
not rebuild `psl211_endpoints`. Its reverse closure has ten members:

```
five_card_rows pgg_analysis_client pgg_analysis_manifest pgg_tableau
pgg_tableau_syntax pgl27_rows psl211_analysis psl211_rows
psl211_spectral_constancy s5_rows
```

So a landing that put the word adapter in `psl211_models.v` would rebuild the
manifest layer and every instance's rows file. That is the cost the note calls
the models-witness cycle.

**The recommendation.** A new file, as the PSL(2,11) landing already did once
with `instances/psl211/psl211_spectral_constancy.v`, whose reverse closure is
empty. Proposed as `instances/psl211/psl211_word_model.v`, requiring
`psl211_mixing` and `psl211_models` and nothing from the manifest layer; it
would hold `psl211_word_cutP`, `psl211_wordP`, `psl211_word_sample`,
`psl211_word_sampleP_E`, `psl211_word_cut_distE`, `psl211_word_family` and
`psl211_word_lawE`. Its own reverse closure at landing time is empty, so
nothing already compiled is rebuilt by adding it.

The certificate, the row and their lemmas would go beside
`psl211_exact_witness` in the instance's rows file, whose reverse closure is
empty as well, for the reason that file's header already gives: `ExactWitness`
and `IdealProximityCert` are records of the manifest layer, and an instance
file importing that layer closes a cycle through the analysis manifest.

Two P1 lemmas the landing needs are probe-local today.
`var_dist_prodR` is `Local` in both `instances/pgl27/pgl27_mixing.v` and
`instances/psl211/psl211_mixing.v`; `fdist_prod_snd` has no infotheo
counterpart, `fdist_prod1` covering the first marginal only. A landing would
make one copy of each global beside `var_dist_le2` in `lib/var_dist_supp.v`,
whose reverse closure has eleven members and does not contain
`psl211_endpoints`. That is the one edit to an existing file the landing needs.

**What a landing changes.** One new instance file and one new row group; two
lemmas promoted out of `Local` into `lib/var_dist_supp.v`; one manifest row for
the word path, which does not exist today, since an `AnalysisPathRow` records
the model family and this family is new. The manifest edit is what makes the
landing cost the ten-file reverse closure of `psl211_models`, not the model
file itself.

## G1: stage A, B and C untouched

No file of stage A, B or C was edited by stage D. The only existing file
stage D changed is the probe's `_CoqProject`, which gained four lines at the
end after being snapshotted as `history/_CoqProject.11-before-stageD`. The four
stage D files are new. The framework copy `pgg_tableau.v` did not have to
change: the proximity arm accepted a third carrier as written.

A concurrent stage C fix pass edited `p5_pgl27_prior_ideal.v`,
`p5_pgl27_word_proximity.v`, `p5_mutations.v`, `assumptions_report_stageC.v`
and `STATUS-stageC.md` while stage D was being written, and snapshotted them
under `history/*.12-before-fixC1`. Those are that pass's edits, not stage D's.
No stage D file imports a `p5_*` file, so the two passes do not interact; the
`p5_*` files were not recompiled here and their `.vo` may be stale against
that pass's sources.

## What in the brief or the spec turned out wrong

1. **The brief asks for "a lemma saying its cut law IS the word law" among the
   word model's obligations, and for the secret as a separate object.** The
   second is not needed at this instance. The two models share the sample
   space, so `psl211_alldecks_secret` serves as `ipc_secret` unchanged. No
   `psl211_word_secret` is defined, and the brief's own parenthesis, "or the
   carrier the existing all-decks adapter uses, with the cut coordinate's law
   replaced", is what made that possible.

2. **The brief says to derive `ipc_close` "through the P1 product lemma and
   data processing".** Both are used, but in the opposite order to the
   eight-card orbit instance's script: data processing is applied first, to the
   whole certificate field, and the product lemma then closes a goal about the
   two laws alone. The eight-card script had to rewrite each reader pointwise
   first, because its two models live on different sample spaces.

3. **The brief warns that `psl211_joint_mixing` is stated at a Boolean prior
   and does not apply to this carrier.** Correct, and `psl211_word_mixing` was
   used instead. The warning understates the reason: the obstruction is not the
   prior but the left factor, which is the uniform law on 136857600 deck
   descriptions here and a law on `bool` there. P1's `var_dist_prodR` is
   general in that factor, which is why it is the lemma the step needs.

4. **The brief offers a `conclude` at a named constant as an option.** There is
   no constant to conclude at, for the reason given above. The row publishes
   plainly and no `conclude` payload is written.
