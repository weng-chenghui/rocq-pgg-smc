# Stage C: the PGL(2,7) word row through the ideal-proximity arm

Spec ledger row P5, with its share of P3, P7, K1, G1, D1, D2. Probe directory
`notes/probes/2026-09-19-tableau-extensions/`, logical path
`tableau_ext_probe`, base commit `8ea05d5`.

Stage C adds four files and edits nothing that stage A or stage B produced.
The `_CoqProject` snapshot before this stage is
`history/_CoqProject.9-before-stageC`; the four new entries are appended after
`assumptions_report_stageB.v` in dependency order.

## Verdict per item

| item | verdict |
|---|---|
| 1. the prior-indexed ideal | GO |
| 2. the certificate and the row | GO |
| 3. P3, the two `_armE`, the shared `Sampled` data, `_arm_neq` | GO, with one weakening |
| 4. P7: the ceiling, the recorded rejections | GO; the wrong-prior refutation is recorded as a rejection and argued |
| 5. G1 | GO |
| 6. D1/D2 | reported below |

The one weakening in item 3: the equation saying the two arms' rows over the
word model share their `Sampled` data is stated on the model family and not on
the whole observed execution. An equation between the two rows' `ab_obs` is
decided by conversion, but takes 48.1 s by `reflexivity` and 96.0 s by
`exact: erefl`, both far above the 5 s bound, so it is not in the file. The
family equation, which is what a continuation of a named `Sampled` value
actually reads off the name, takes 0.004 s.

## The two numbers

| quantity | exact | decimal |
|---|---|---|
| `ipc_eps (pgl27_word_proximity_cert secretP)` | `2^-40` | 0.00000000000090949470177292824 |
| what `pgl27_row_word_proximity` publishes | `2^-39` | 0.0000000000018189894035458565 |
| what `pgl27_row_word39` publishes, spectral arm | `2^-39` | 0.0000000000018189894035458565 |
| `cert_eps (pgl27_word_cert secretP)`, spectral, accumulated | `2^-40 + 2^-40` | 0.0000000000018189894035458565 |

The proximity row and the spectral row publish the same number. The proximity
certificate proves half of what the spectral certificate accumulates: the
spectral arm crosses from the word walk to the uniform cut and back, spending
`pgl27_word_mixing` once for each of the two dealt secrets it compares, and
the proximity arm compares one joint law with one product law and spends it
once. `pgl27_word_proximity_eps_halfE` is that identity, closed by conversion.
The certificate's number is `2^-40` against the ceiling `2` that
`var_dist_le2` gives for a variation distance, so at about
0.00000000000045 of the ceiling the separation is a cryptographic one.

## Key statements, verbatim

The ideal, in `p5_pgl27_prior_ideal.v`:

```
Definition pgl27_prior_sample (R : realType) (secretP : R.-fdist bool)
  : SampleAdapter R pgl27_exec_plug :=
  @MkSampleAdapter R pgl27_profile pgl27_exec_plug
    [the finType of (bool * pgg_gT pgl27_M)%type]
    (pgl27P_gen secretP) fst snd.

Definition pgl27_prior_exact_family : AnalysisModelFamily pgl27_observed :=
  @MkAnalysisModelFamily pgl27_observed (fun R => R.-fdist bool)
    (fun R p => @pgl27_prior_sample R p).

Definition pgl27_prior_exact_witness (R : realType) (secretP : R.-fdist bool)
  : ExactWitness (amf_sample pgl27_prior_exact_family R secretP) :=
  @MkExactWitness R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_prior_exact_family R secretP) bool (pgl27_secret R)
    (fun C HC =>
       let H3 : (#|C| <= 3)%N := HC in
       (eq_ind_r
          (fun v => pgl27P_gen secretP |= v _|_ pgl27_secret R)
          (pgl27_view_indep_gen secretP H3)
          (pgl27_prior_viewE secretP C))).

Definition pgl27_row_prior_exact_tableau : PublishedRow :=
  pgl27_dealt
    sample  pgl27_prior_exact_family
    certify ExactIndependence pgl27_prior_exact_witness
    |> publish StaticExecutedOnly BaselineClassicalOnly.
```

The certificate and the row, in `p5_pgl27_word_proximity.v`:

```
Lemma pgl27_word_proximity_close (R : realType) (secretP : R.-fdist bool)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  (#|C| < profile_k (instance_profile pgl27_algebra))%N ->
  var_dist
    (fdistmap (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params
                           C ((pgl27_word_sample secretP).(sa_arg) u)
                           ((pgl27_word_sample secretP).(sa_cut) u),
                         pgl27_word_secret secretP u))
       (sa_sampleP (pgl27_word_sample secretP)))
    (fdistmap (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params
                           C ((pgl27_prior_sample secretP).(sa_arg) u)
                           ((pgl27_prior_sample secretP).(sa_cut) u),
                         pgl27_secret R u))
       (sa_sampleP (pgl27_prior_sample secretP)))
  <= 2%:R^-40.

Definition pgl27_word_proximity_cert (R : realType) (secretP : R.-fdist bool)
  : IdealProximityCert (amf_sample pgl27_word_family R secretP) :=
  @MkIdealProximityCert R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP)
    (amf_sample pgl27_prior_exact_family R secretP)
    (pgl27_prior_exact_witness secretP)
    (pgl27_word_secret secretP)
    (sw_bound_eps (pgl27_word_marginal_bound R))
    (fun C HC => pgl27_word_proximity_close secretP HC).

Definition pgl27_row_word_proximity : PublishedRowAt pgl27_reprice39 :=
  pgl27_word_sampled
    certify IdealProximity pgl27_word_proximity_cert
    |> conclude pgl27_reprice39 by (fun R idx => pgl27_word_proximity_le39 idx)
    |> publish IdealFinite BaselineClassicalOnly.

Theorem pgl27_word_view_proximity (R : realType) (secretP : R.-fdist bool)
    (C : {set 'I_8}) (HC : (#|C| <= 3)%N) :
  var_dist
    (fdistmap (fun u => (@sa_coalition_view R pgl27_profile pgl27_exec_plug
                           (amf_sample pgl27_word_family R secretP) 0 C u,
                         pgl27_word_secret secretP u))
       (sa_sampleP (amf_sample pgl27_word_family R secretP)))
    ((fdistmap (@sa_coalition_view R pgl27_profile pgl27_exec_plug
                  (pgl27_prior_sample secretP) 0 C) (pgl27P_gen secretP))
     `x (fdistmap (pgl27_secret R) (pgl27P_gen secretP)))
  <= 2%:R^-39.
```

The P3 equation and the two rows over the word model:

```
Lemma pgl27_word_proximity_cert_idealE (R : realType)
    (secretP : R.-fdist bool) :
  ipc_ideal (pgl27_word_proximity_cert secretP)
  = amf_sample (ab_f (published_at pgl27_row_prior_exact_tableau)) R secretP
  /\ ExactIndependence (ipc_witness (pgl27_word_proximity_cert secretP))
     = ab_port (published_at pgl27_row_prior_exact_tableau) R secretP.

Lemma pgl27_row_word_arms_sampledE :
  ab_f (published_at pgl27_row_word_proximity)
  = sp_f (tableau_at pgl27_word_sampled)
  /\ ab_f (published_at pgl27_row_word_branch39)
     = sp_f (tableau_at pgl27_word_sampled).

Lemma pgl27_row_word_arm_neq (R : realType) (secretP : R.-fdist bool) :
  security_arm_of pgl27_row_word_proximity R secretP
  <> security_arm_of pgl27_row_word_branch39 R secretP.
```

## Item 1: how far the ideal's independence was from the tree

It was one lemma away and the lemma is already in the tree.
`pgl27_view_indep_gen` in `instances/pgl27/pgl27_word_privacy.v` states
independence of a coalition's view from the dealt secret under
`pgl27P_gen secretP`, at every Boolean prior, and it is three-transitivity of
PGL(2,7) on the eight points read as a privacy statement. Nothing had to be
proved for the witness beyond carrying it along `pgl27_prior_viewE`, which is
`pgl27_exact_viewE` of `pgl27_rows.v` restated at the prior-indexed family.
No lemma is missing.

## Item 2: how far `ipc_close` is from `pgl27_view_mixing`

One step, plus carrier bookkeeping that costs nothing.

The step is `inde_dist_of_RV2 (pgl27_view_indep_gen secretP H3)`. It is needed
because `pgl27_view_mixing` states its right-hand side as the product of the
ideal's two marginals, while `ipc_close` asks for the ideal's joint law; the
ideal witness's own independence is exactly what turns one into the other.
This is the same step `pgl27_view_mixing`'s own proof takes in the other
direction, so the arm asks for the joint form and the instance already
carries the product form.

The bookkeeping is three rewrites, each an identity of readers and none of
them a probabilistic fact:

- `pgl27_static_obsE`, the framework's `static_coalition_obs` against the
  instance's `pgl27_view`, on both models;
- `fdistmap_comp` with `pgl27_word_sample_joint_distE`, which carries the word
  sample space, the pair of the secret and the sampled generator word, forward
  to `pgl27P_word_gen secretP`, the pair of the secret and the evaluated cut
  that `pgl27_view_mixing` is stated on;
- the ideal side needs no transport, because `pgl27_prior_sample` was built
  with `pgl27P_gen secretP` as its sample law.

No carrier mismatch, no `static_coalition_obs` against a different view, and
no joint-versus-product mismatch survives.

## Compile table

Per-sentence times from `rocq compile -time`, under the shared lock. Wall
times include waiting for the lock and are not attributed.

From the fresh recompile of the whole probe from source in `_CoqProject`
order, in a directory holding no `.vo` this stage produced:

| file | rc | wall | sentences above 5 s |
|---|---|---|---|
| `p5_pgl27_prior_ideal.v` | 0 | 4.5 s | none |
| `p5_pgl27_word_proximity.v` | 0 | 5.0 s | none |
| `p5_mutations.v` | 0 | 4.3 s | none |
| `assumptions_report_stageC.v` | 0 | 26.7 s | none |

All sixteen files of stages A and B compile rc=0 in that same run, with no
sentence above 5 s outside `assumptions_report.v`, where one
`Print Assumptions` takes 20.6 s as it did before this stage.

Sentences that were measured and then removed or rewritten:

| sentence | `exact: erefl` | `reflexivity` | outcome |
|---|---|---|---|
| `ab_obs` of the proximity row against `ab_obs` of the branch row | 96.0 s | 48.1 s | removed; the family equation replaces it |
| `ab_f` of either row against `sp_f (tableau_at pgl27_word_sampled)` | 0.000 s | 0.004 s | kept, with `exact: erefl` |
| `pgl27_row_word_arm_neq` with the prior bound as an index of the proximity row | statement alone 78.7 s | - | rewritten |
| `pgl27_row_word_arm_neq` proved by rewriting with the two `_armE` lemmas applied to the prior | 24.3 s | - | rewritten |
| the same with the two equations restated locally and both rewritten in the inequation | 24.1 s | - | rewritten |
| `pgl27_row_word_arm_neq` as it stands, the arm equation assumed first | under 5 s | - | kept |

The pattern behind the last three rows is the one recorded in `MEMORY.md` as
the cross-class rewrite conversion bomb: a rewrite scans the other side of the
goal, so rewriting one row's arm in a goal that also mentions the other row
converts the two rows against each other. Assuming the equation between the
two arms first leaves each rewrite on a goal that mentions one row.

Every row equation in the two program files closes by `exact: erefl` and never
by `by []`, `done` or `by split`, following the hang shape recorded in
`STATUS.md`.

## Assumptions

`assumptions_report_stageC.v` prints `Print Assumptions` for all 24
declarations stage C writes. Scanning the output with `[\w.]+` before a colon
gives exactly three constant names and no fourth:

- `propositional_extensionality`
- `functional_extensionality_dep`
- `constructive_indefinite_description`

All 24 blocks are `Axioms:` blocks carrying those three and nothing else; none
is `Closed under the global context`. The three come from `boolp`, through the
section context of the `fdist` record, which is the floor every statement
about a PGL(2,7) probability model sits on. No new axiom, assumed constant,
`Admitted`, `Abort`, `Axiom` or `Parameter` is written anywhere in stage C.

## Recorded rejections

All three are in `p5_mutations.v` under `Fail`. The decisive error line of
each was obtained by compiling the same definition without `Fail` in a scratch
file.

**1. The ideal at the unit-indexed `pgl27_exact_family`.** The index types
differ.

```
The term "secretP" has type "{fdist bool}" while it is expected to have type
 "amf_index pgl27_exact_family R".
```

**2. The ideal at the wrong prior, the uniform one.** Supplying `tt` makes the
unit-indexed family's one member a well-typed ideal, and what the kernel then
rejects is the distance field.

```
The term "pgl27_word_proximity_close secretP HC" has type
 "is_true (var_dist ... (fdistmap ... (sa_sampleP (pgl27_prior_sample secretP)))
   <= 2 ^- 40)"
while it is expected to have type
 "is_true (var_dist ... (fdistmap (fun u : sa_sampleT (amf_sample
    pgl27_exact_family R tt) => ...) (sa_sampleP (amf_sample
    pgl27_exact_family R tt))) <= sw_bound_eps (pgl27_word_marginal_bound R))".
```

The semantic half of this rejection is argued and not compiled, and is marked
as argued here. Pushing both joint laws forward along the secret coordinate
leaves the word model's prior on one side and the uniform law on the other,
and `var_dist_fdistmap` says that the distance between the two joint laws is
at least the distance between those two pushforwards. At a point-mass prior
that distance is one, which is above `2^-40` by a factor of about
1.1e12, so no proof of the distance field could exist at a
non-uniform prior. Compiling that argument needs a lower bound on `var_dist`
by one of its terms and an evaluation of `var_dist (fdist1 true)
(fdist_uniform card_bool)`, neither of which the tree carries; it was judged
not cheap against the turn budget and left as an argument.

**3. The word model's proximity certificate over the exact model's branch
point.** The cross-arm rejection, the proximity counterpart of the two
rejections `t0_sampled_branch_pgl27.v` already records.

```
The term "pgl27_word_proximity_cert" has type
 "forall (R : realType) (secretP : {fdist bool}),
  IdealProximityCert (amf_sample pgl27_word_family R secretP)"
while it is expected to have type
 "IdealProximityPayload (tableau_at pgl27_exact_sampled)"
(cannot unify "amf_index (sp_f (tableau_at pgl27_exact_sampled)) R" and
"{fdist bool}").
```

## G1

Stage C edits no file that stage A or stage B produced. `pgg_tableau.v`,
`pgg_tableau_syntax.v`, `pgl27_rows.v`, `t0_sampled_branch_pgl27.v`, the
five-card and S5 and PSL(2,11) row files, and both earlier assumptions
reports are byte-identical to their state at the start of this stage. The
three existing PGL(2,7) programs and every recorded `Fail` in `pgl27_rows.v`
and `t0_sampled_branch_pgl27.v` compile unchanged in the fresh recompile of
the whole probe in `_CoqProject` order.

## D1: where each new declaration would live permanently

The reverse closure of each candidate home was computed with Python over the
`Require` lines of every `.v` file under `lib`, `protocol`, `groups`,
`security`, `smc`, `reconstruct`, `manifest`, `instances/*` and `legacy/*`.
`psl211_endpoints` is in none of them.

| declaration | permanent home | dependents of that home | holds `psl211_endpoints` |
|---|---|---|---|
| `pgl27_prior_sample` | `instances/pgl27/pgl27_exec.v`, beside `pgl27_sample` and `pgl27_word_sample`, inside the section that already binds `secretP` | 11 | no |
| `pgl27_prior_exact_family` | `instances/pgl27/pgl27_models.v`, beside `pgl27_exact_family` | 10 | no |
| `pgl27_prior_viewE`, `pgl27_prior_exact_witness`, `pgl27_word_secret`, `pgl27_word_proximity_close`, `pgl27_word_proximity_cert`, both rows and all their lemmas | `instances/pgl27/pgl27_rows.v`, beside `pgl27_exact_witness` and `pgl27_word_cert` | 0 | no |

The dependents of `pgl27_models.v` are `five_card_rows`,
`pgg_analysis_client`, `pgg_analysis_manifest`, `pgg_tableau`,
`pgg_tableau_syntax`, `pgl27_analysis`, `pgl27_rows`, `psl211_rows`,
`psl211_spectral_constancy` and `s5_rows`; `pgl27_exec.v` adds `pgl27_models`
to that set.

`pgl27_word_proximity_close` was considered for
`instances/pgl27/pgl27_word_privacy.v`, which is where `pgl27_view_mixing`
lives. It is rejected: the statement mentions `static_coalition_obs`,
`sa_arg`, `sa_cut` and `sa_sampleP`, framework vocabulary that
`pgl27_word_privacy.v` does not import and should not start importing to
carry one lemma.

## D2: what a landing would change

Searched, not assumed.

1. **The manifest gains a row, or the ideal program cannot publish one.** An
   `AnalysisPathRow` records the analysis model family, so a row over
   `pgl27_prior_exact_family` is not `pgl27_row_exact`. The statement
   `published_row pgl27_row_prior_exact_tableau = pgl27_row_exact` does not
   typecheck by conversion and was withdrawn; what the file states instead is
   `pgl27_row_prior_exact_publishedE`, the three coordinates the ideal row
   publishes. A landing has to add one manifest row for the prior-indexed
   exact model at `AnalysisBridged`, `StaticExecutedOnly`,
   `BaselineClassicalOnly`, in `manifest/pgg_analysis_manifest.v`.

2. **The word row needs no manifest change.**
   `pgl27_row_word_proximity_rowE` closes by conversion against
   `pgl27_row_word`, so the proximity row publishes the manifest row the
   spectral row already publishes. An `AnalysisPathRow` holds descriptive
   metadata and no `Prop`, so one manifest row carrying a spectral row and a
   proximity row says nothing about either claim; the arm is read by
   `security_arm_of` and by nothing in the manifest.

3. **Ten files recompile for the family, eleven for the adapter.** Those are
   the dependent sets in the D1 table. `psl211_spectral_constancy` is in both
   and is the heaviest of them; `psl211_endpoints` is in neither.

4. **The framework has to land first.** Both program files rest on the stage B
   additions to the probe's copy of `pgg_tableau.v`, so nothing here can land
   before `IdealProximityCert`, `IdealProximity`, `IdealProximityPropAt`,
   `idealproximity_tail`, `certify_idealproximity`, `IdealProximityArm`,
   `view_proximity_of` and the `certify IdealProximity` keyword notation do.

## What in the brief or the spec turned out wrong

1. **The ideal program does not publish `pgl27_row_exact`.** The brief asks
   for the prior-indexed ideal to be published as its own program from the
   shared observed prefix, which it is; what it cannot do is reuse the
   manifest's exact row, because an `AnalysisPathRow` carries the model
   family. The file states the row's three coordinates instead of an equality
   with a manifest row, and D2 records the manifest row a landing owes.

2. **The equation on the two rows' `Sampled` data cannot be stated on the
   observed execution.** Item 3 asks for "the equation saying the two arms'
   rows over the word model share their `Sampled` data". At PGL(2,7) the
   `ab_obs` half of that costs 48.1 s by `reflexivity` and 96.0 s by
   `exact: erefl`, so the file states the `ab_f` half, against the named
   `Sampled` value itself rather than against the sibling row. That is the
   half a continuation reads off the name, and it costs 0.004 s.

3. **`_arm_neq` at this instance is not p4's one-liner.** At the five-card
   instance the family index is `unit` and `by []` closes the inequation. At
   PGL(2,7) the index is a distribution on the booleans and binding it as one
   row's index makes the other row's index type reachable only by converting
   the two rows' observed executions: 78.7 s in the statement alone. The
   working form binds the prior at its own type, assumes the equation between
   the two arms, and rewrites each row's arm on a goal that mentions one row.

4. **Nothing in the spec's "Pinned carriers" section for PGL(2,7) was wrong.**
   `pgl27P_gen` is the law the ideal is built on, `pgl27_view_mixing` is the
   distance, and both are where the spec says they are.
