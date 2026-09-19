# Independent soundness audit of stage B

Date: 2026-09-19. Auditor: an Opus session with no part in writing stage B.
Object: the frozen export of `notes/probes/2026-09-19-tableau-extensions/` at
commit 8ea05d5, read at
`<scratchpad>/extB_frozen/notes/probes/2026-09-19-tableau-extensions/`.
Spec: `notes/20260919-tableau-three-extensions-probe-design.md`.
Nothing in the repository was edited except this file.
`instances/psl211/psl211_endpoints.v` was never opened and never compiled, and
no `make` was run.

## What I compiled

Everything below was compiled from the frozen source in a fresh scratch
directory `<scratchpad>/extB_sound/work`, through the machine-wide lock, with
the production `_CoqProject` flags and `-Q <work> tableau_ext_probe` last. No
`.vo` written by the prover was read. Wall times include queueing behind two
other agents, so only the `-time` per-sentence figures are attributable.

| file | rc | attributable sentence time | slowest sentence |
|---|---|---|---|
| `p1_joint_law_distance.v` | 0 | 3.7 s | 1.72 s, a `From mathcomp Require` |
| `pgg_tableau.v` | 0 | 13.0 s | 4.01 s, `Definition ab_port` |
| `pgg_tableau_syntax.v` | 0 | 4.4 s | 1.45 s, a `From mathcomp Require` |
| `five_card_rows.v` | 0 | 4.5 s | 1.40 s, a `From mathcomp Require` |
| `s5_rows.v` | 0 | 4.0 s | 1.83 s, a `From mathcomp Require` |
| `p4_kim_biased_proximity.v` | 0 | 11.1 s | 3.25 s, the `by []` of `five_card_row_biased_arm_neq` |
| `p8_spectral_relation.v` | 0 | 3.7 s | 2.11 s, a `From mathcomp Require` |
| `p9_actual_marginals.v` | 0 | 3.8 s | 3.8 s total, no sentence above 2.3 s |
| `p7_mutations.v` | 0 | 3.7 s | 2.32 s, a `From mathcomp Require` |
| `assumptions_report_stageB.v` | 0 | 22.9 s | 1.43 s, a `Print Assumptions` |

Beside those I compiled two experiment files of my own, the nine new recorded
failures of stage B each recompiled once with its `Fail` removed, and one
failure of my own.

`<scratchpad>/extB_sound/work/exp1.v`, rc=0, 4.1 s attributable:

- `aud_five_card_proximity_prop_holds : IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 25)`,
  by `exact: (view_proximity_of five_card_row_biased_proximity R tt)`.
- `aud_spectral_implies_proximity_five_card : SpectralPropAt (kim_biased_cert R tt) c -> IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 25)`.
- `aud_spectral_implies_proximity_at_one`, the same at the spec's constant 1.
- `aud_five_card_secret_sameE : ew_secret (five_card_exact_witness R tt) = five_card_leakage.Secret R`, by `erefl`.

`<scratchpad>/extB_sound/work/exp2.v`, rc=0, 4.1 s attributable:

- `aud_kim_biased_proximity_close_1_50`: the certificate field of P4 holds at
  the exact number `1 / 50`, by the probe's own chain with the last step taken
  to `kim_biased_cut_mixing_exact` instead of `kim_biased_cut_mixing`.
- `aud_kim_biased_proximity_cert_exact`: a proximity certificate at `1 / 50`.
- `aud_row_biased_proximity_inv50 : PublishedRowAt aud_reprice_inv50`: the
  one-cut row through the proximity arm published at `1 / 50`.
- `aud_conclude_below_false`: the `conclude` obligation at `1 / 100` is false.
- `Fail` on the same row at `1 / 100`; its error, read from `exp2b.v`, is the
  `ConcludePayload` mismatch, with the `IdealProximity` branch printed.

## Findings

| ID | Severity | File:line | Claim | Evidence | Checked replacement |
|---|---|---|---|---|---|
| B1 | BLOCKING | `STATUS-stageB.md:22`, `:411-420`; `p8_spectral_relation.v:56-60` | "the spec's implication is refuted by compile"; "A proposition that does not mention any ideal cannot imply a bound on the distance to one, at any instance and at any constant" | `exp1.v` compiles `aud_spectral_implies_proximity_five_card` and `aud_spectral_implies_proximity_at_one`. At the five-card instance the proximity proposition at 1/25 is a theorem outright (`five_card_biased_view_proximity`), so anything implies it, the spectral proposition included, at 1/25 and at 1. `spectral_prop_cert_free` refutes the implication read as a schema uniform in the proximity certificate, which is not the reading the spec's P8 row has ("at PGL(2,7) and at the five-card instance"). | below, R1 |
| S1 | SHOULD | `p4_kim_biased_proximity.v:205-213`; `STATUS-stageB.md:110-118` | "The spectral arm's number at this model is twice the proximity arm's"; the published 1/25 is presented as the number both arms are read at | `exp2.v` compiles a proximity certificate over the same model and the same ideal at `1 / 50`, and a row that publishes `1 / 50`. `kim_biased_cut_mixing_exact` (`instances/kim2025/five_card_mixing.v:548`) and `kim_biased_cert_exact` (`instances/kim2025/five_card_rows.v:770`) are already in the tree, and `five_card_row_biased_inv25` reaches 1/25 as `1/50 + 1/50`. So the halving relation holds between the two chosen certificates, not between the two arms, and the proximity arm at this model supports 1/50, half of what the spectral arm can publish. | below, R2 |
| S2 | SHOULD | `pgg_tableau.v:446` (in the `IdealProximityPropAt` comment); `p9_actual_marginals.v:9-15` | "c is the whole advantage a coalition below the threshold has over an observer who sees the two quantities drawn apart"; "an advantage of at most three times the published number" | `var_dist` is the sum of the absolute differences (infotheo `probability/variation_dist.v:33`), and `lib/var_dist_supp.v:49-50` records in the repository's own words that "the total variation distance of the literature is half of this quantity". A distinguisher's advantage is therefore at most `c / 2`, and at most `3 * c / 2` in P9. | below, R3 |
| S3 | SHOULD | `pgg_tableau.v:180` | "the number is the whole of what the actual model loses against an execution that leaks nothing" | `ipc_eps` is a free field and `ipc_close` only bounds the distance by it. `exp2.v` builds two certificates over the same model and the same ideal at two different numbers, `sw_bound_eps (kim_biased_marginal_bound R)` and `1 / 50`, both accepted. The number is an upper bound the instance chooses, not a quantity the record determines. | below, R4 |
| S4 | SHOULD | `p8_spectral_relation.v:65-68` | "the recorded failure beside it says that replacing the certificate does not leave it the same" | Recompiling `idealproximity_prop_cert_free` without `Fail` gives `Error: No applicable tactic.` A failure of `done` on an equality is not a proof that the two sides differ. | below, R5 |
| N1 | NOTE | `p1_joint_law_distance.v:122` | `fdist_uniform_prod` | Used by no proof in the probe; the only other occurrence is its own `Print Assumptions`. `STATUS-stageB.md:461-464` says so, and says a landing may drop it. | none needed |
| N2 | NOTE | `pgg_tableau.v:187` | `ipc_secret` is unconstrained | Nothing ties it to `ew_secret (ipc_witness cert)` or to the protocol's own secret, so a certificate may name a degenerate secret and satisfy `ipc_close` cheaply. This is the same freedom `ew_secret` has in `ExactWitness` (`pgg_tableau.v:145`), so it is a property the arm inherits and not one it introduces. At the five-card instance the two are the same random variable: `exp1.v` compiles `ew_secret (five_card_exact_witness R tt) = five_card_leakage.Secret R` by `erefl`. | none needed |
| N3 | NOTE | `p7_mutations.v:92-93` | "The coalition is not empty, so the reading it bounds is not the constant finfun and the statement is about a seat that sees a card" | Asserted in a comment and compiled nowhere. The probe establishes that the claim is not closed by conversion and not closed by `done`; it establishes nothing about the distance being positive. | none needed |
| N4 | NOTE | `STATUS-stageB.md:158`, `:166-170` | "The slowest stage B sentence is the `by []` closing `five_card_row_biased_arm_neq`" | My run attributes 3.25 s to that `by []` and a further 3.13 s to the `Lemma` sentence that states it, so the declaration costs about 6.4 s over two sentences. The claim that no sentence outside a `Print Assumptions` reaches 5 s survives. | none needed |
| N5 | NOTE | `history/five_card_rows.v.6-before-fix3` | `five_card_row_repeated_at_manifest_level` is absent from the current `five_card_rows.v` | The deletion is between `.6-before-fix3` and `.8-before-fix4`, so it belongs to stage A's fix pass 3 and not to stage B. Stage B changed no line of code in `five_card_rows.v`: the comment-stripped diff against `.8-before-fix4` is empty. | none needed |

### R1, the replacement for the P8 account

The compiled facts are: `spectral_prop_cert_free`, and the two lemmas of
`exp1.v`. A truthful account of them, for `STATUS-stageB.md`'s "What in the
brief or the spec turned out wrong" and for the header of
`p8_spectral_relation.v`:

> The spectral arm's published proposition does not mention its certificate:
> `spectral_prop_cert_free` proves `SpectralPropAt cert c = SpectralPropAt
> cert' c` by conversion, so the ideal cut and the constancy field are spent
> inside `spectral_tail` and have left the claim. That refutes the implication
> read as a schema uniform in the proximity certificate, because the two sides
> would then vary independently. It does not refute the spec's P8 row, which is
> read at one instance: at the five-card instance the proximity proposition at
> one twenty-fifth is a theorem outright, so the spectral proposition implies
> it there, and at the constant one as well. The separation between the two
> arms is therefore a statement about the schema and not about any one row, and
> the schematic half is argued and not compiled, since a countermodel needs a
> model whose reading law is the same at every run argument and far from the
> ideal's.

The two lemmas backing the middle sentence, compiled in this audit, are worth
adding to `p8_spectral_relation.v` verbatim:

```coq
Lemma five_card_proximity_prop_holds (R : realType) :
  IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 25).
Proof. exact: (view_proximity_of five_card_row_biased_proximity R tt). Qed.

Lemma spectral_implies_proximity_five_card (R : realType) (c : R) :
  SpectralPropAt (kim_biased_cert R tt) c ->
  IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 25).
Proof. by move=> _; exact: five_card_proximity_prop_holds. Qed.
```

They need `p4_kim_biased_proximity` and `five_card_rows` in the file's
requires, which `p8_spectral_relation.v` does not have today; either that, or
they go at the end of `p4_kim_biased_proximity.v`, where both are already
available.

### R2, the replacement for the halving sentence

For the docstring of `kim_biased_proximity_eps_halfE`:

> The number `kim_biased_cert` carries at this model is twice the number
> `kim_biased_proximity_cert` carries. Both are read off `kim_biased_cut_mixing`,
> the one distance on the cut group; the spectral arm spends it once for each of
> the two committed pairs it compares and the proximity arm compares one law
> with one law. The relation is between these two certificates and not between
> the two arms: `kim_biased_cert_exact` carries one fiftieth for the spectral
> arm over the same model, and the same distance on the cut group gives the
> proximity arm one fiftieth as well.

And for the `STATUS-stageB.md` section "The published number", after the
sentence naming the closed form, a sentence that the current text lacks:

> One fiftieth, the number `kim_biased_cut_mixing_exact` proves on the cut
> group, is sharper than the certificate's own sqrt 5 over eighty and is what
> the proximity arm can publish at this model. The row is concluded at one
> twenty-fifth so that the two arms are read in one column, which costs the
> proximity row a factor of two against the number it could publish.

### R3, the replacement for the advantage sentences

In `pgg_tableau.v`'s `IdealProximityPropAt` comment, for the sentence
beginning "The right side is a product":

> The right side is a product because the ideal's witness makes those two
> independent there, so a distinguisher below the threshold separates the
> coalition's reading with the secret from an independent pair with advantage
> at most half of c, this being the sum of the absolute differences and not the
> total variation distance of the literature.

In `p9_actual_marginals.v`'s header, for the sentence beginning "so a
coalition below the threshold has":

> so a coalition below the threshold has, under the actual model by itself, an
> advantage of at most one and a half times the published number in telling its
> reading and the secret apart from two quantities drawn independently, the
> published number being the sum of the absolute differences and the advantage
> half of the bound on it.

### R4, the replacement for the certificate comment

For the last clause of the `IdealProximityCert` comment:

> and the number is an upper bound the instance chooses on what the actual
> model loses against an execution that leaks nothing, not a quantity the
> record determines: any number at which `ipc_close` is provable is a legal
> field, so a certificate says exactly as much as its number is small.

### R5, the replacement for the cert-freeness contrast

For the comment above `idealproximity_prop_cert_free`:

> The proximity arm's proposition mentions its certificate, through the ideal
> adapter, that ideal's witness and the actual model's secret, so the two are
> not two readings of one object. The recorded failure beside it says only that
> the equality between the proposition at two certificates is not closed by
> conversion.

## The questions, answered

**1. Does the arm say what the domain wants?** Yes, and it says it at the
executed reader. `IdealProximityPropAt` (`pgg_tableau.v:452-466`) is stated at
`sa_coalition_view` on both sides, which `security/pgg_sample_adapter.v:157` defines as
the layer-two reader built from `exec_coalition_endpoints`, so the claim is
about the interpreter's endpoints and not about the static observation the
spectral arm's claim stops at. The laws are pushforwards of `sa_sampleP`, so
the claim is an average over the run argument. The right side is the ideal's
own reading marginal times the ideal's own secret marginal, which is exactly
the shape of `pgl27_view_mixing` (`instances/pgl27/pgl27_word_privacy.v:233`),
down to the proof step `rewrite -(inde_dist_of_RV2 ...)` the arm's tail uses.
Comparing with the ideal's secret marginal and not the actual's is what the
spec asks for and what the repository's existing theorem does; the statement
remains meaningful when the two secret laws differ, since closeness to any
product law is a statement that no distinguisher separates the pair from an
independent pair, and `p9_actual_marginals.v` converts it to the actual model's
own marginals at three times the number. At the five-card instance the two
models share the secret random variable outright (exp1, by `erefl`).

The tail consumes a link lemma for both models: `idealproximity_tail`
(`pgg_tableau.v:710`) takes `Hview` and `Hideal`, both of the shape
`sa_coalition_view ... = fun u => static_coalition_obs C (sa_arg u) (sa_cut u)`,
and rewrites with each. The prover's claim about the ideal's link is right.
`sampled_viewE_prop` (`pgg_tableau.v:377`) quantifies over
`amf_sample f R idx`, members of the row's own family, and `ipc_ideal` is an
arbitrary adapter over the same execution, so the ideal's link is not an
instance of it; `certify_idealproximity` (`pgg_tableau.v:766`) builds it
from `sa_coalition_viewE` with `endpoint_eq := fun u => sp_He x _ _`, the row's
own endpoint statement, which is exactly the lemma and the hypothesis
`sample_step` (`pgg_tableau.v:623`) uses. That is what typing `ipc_ideal`
over `instance_exec E` buys, and it is why the ideal may not be an arbitrary
adapter.

No field is decorative. `ipc_ideal` occurs in the proposition twice and in the
tail; `ipc_witness` types `ipc_secret` through `ew_secretT`, supplies
`ew_secret` to the proposition and `ew_indep` to the tail; `ipc_secret` occurs
in the proposition and in `ipc_close`; `ipc_eps` occurs in `ipc_close`, in the
tail's conclusion and in `ConcludePayload`; `ipc_close` is what the tail
applies. The one field whose use could have been cosmetic, the witness's
independence, is the subject of the mutation `idealproximity_tail_without_independence`,
which I recompiled without `Fail`: `Error: Cannot apply lemma (ipc_close cert HC)`,
the final application, which is where the independence was spent.
`Print Assumptions` over all 35 stage B declarations shows no axiom beyond the
three boolp constants (see invariant 1).

**2. `ipc_eps` as a fifth field.** Sound. Anyone may pick the number, and
`ipc_close` has to hold at it, so a certificate cannot claim less than it
proves. Monotonicity is proved for the arm: `port_conclude`
(`pgg_tableau.v:813`) gained a third case closed by `le_trans`, and
`ConcludePayload` (`pgg_tableau.v:797`) asks
`ipc_eps cert <= odflt (ipc_eps cert) (c R)`. A number below the certificate's
is refutable and not merely unprovable: `exp2.v` proves
`~ (ipc_eps (kim_biased_proximity_cert R idx) <= 1 / 100)` from
`kim_biased_proximity_cert_epsE` and `2 <= sqrt 5`, and the row written at
`1 / 100` is rejected at the `conclude` payload with the `IdealProximity`
branch visible in the printed `match`. The one consequence worth recording is
S3: because the number is free and not computed from a marginal bound as the
spectral arm's is, the published number of a proximity row is not a canonical
quantity of the model, which is what makes S1 possible.

**3. Vacuity and triviality, P7.** The five-card number is not vacuous, and the
status file understates how much room is left. The certificate's number is
`sw_bound_eps (kim_biased_marginal_bound R) = sqrt 5 * (1 / 80)`, about
0.02795; the published number is 1/25 = 0.04; the ceiling `var_dist_le2`
(`lib/var_dist_supp.v:51`) is 2. So the published number is 2 per cent of the
ceiling. The tree also proves the sharper 1/50 = 0.02 on the same cut group
(`kim_biased_cut_mixing_exact`), which is below the certificate's own number,
and my `exp2.v` shows the proximity arm reaches it: the certificate's distance
is above the exact number the tree has, the published number is twice it, and
`STATUS-stageB.md` says neither. That is finding S1.

Every recorded `Fail` of stage B fails for the stated reason and for no other.
I recompiled all nine new ones with the `Fail` removed; the decisive lines
match `STATUS-stageB.md:200-210` word for word, including
`Error: No applicable tactic.` twice,
`Error: Cannot apply lemma (ipc_close cert HC)`, and the four type mismatches.
The "independence removed" mutation does remove what it says: it deletes the
only use of `ew_indep` in the proof and keeps everything else, and the failure
lands on the final application. The cross-instance rejection lands where the
status says, on the ideal adapter field, with
`SampleAdapter R (OE.oe_execution s5_rand_observed)` against
`SampleAdapter R (instance_exec five_card_params)`. The mutation between two
adapters of one instance sharing the index type `unit` is rejected on the
certificate's own index, in both arms and in both directions, and the status's
account of it is honest; the p7 comment's added claim that the two adapters
"differ in their sample space as well as in their law" is true, since
`kim_single_sample` carries `five_card_leakage.Omega`
(`instances/kim2025/five_card_models.v:139`) and `kim_centi_repeated_sample`
carries `kim_repeated_sampleT` (`:146`).

The tautology probes: `five_card_biased_proximity_by_computation` and
`_by_done` are the two the probe records, and both fail as stated. I did not
find a further tautology: `kim_biased_proximity_close` is stated at a number
0.028 against a ceiling of 2, so it is not the ceiling in disguise, and its
proof spends `kim_biased_cut_mixing`, a real distance on the cut group. What
the probe does not establish, and what I list under "what I did not check", is
that the distance is positive at any coalition, so "not trivially true" is
established as "not closed by conversion and not closed by `done`" and no more.
The vacuity probe over hypotheses passes: `five_card_biased_proximity_at_singleton`
(`p7_mutations.v:94-96`) instantiates the coalition at `[set i]` and discharges
the threshold hypothesis by `five_card_singleton_below_threshold`, whose
`Print Assumptions` block is the one that reports `Closed under the global
context`, as the status says.

**4. P8.** `spectral_prop_cert_free` is correct and it compiles: the body of
`SpectralPropAt` does not mention its certificate argument, so the equality
holds by `erefl`. The inference the comments draw from it is not valid as
written, and B1 is that finding. Certificate-freeness refutes an implication
uniform in the proximity certificate, and even that half needs the observation
that the two sides would vary independently, which in turn needs a model with a
distant ideal to be a theorem rather than an argument. It does not refute the
spec's P8 row, which is read at two named instances; at the five-card instance
the implication is true and I compiled it, at 1/25 and at 1. The distinction
the question asks for: the published proposition of the spectral arm does not
imply the proximity proposition for a reason internal to the proposition, but
the certificate's data does give it at this instance, because `sc_close` is
`kim_biased_cut_mixing`, the same distance on the cut group that
`kim_biased_proximity_close` spends. What the certificate's data does not
supply is the ideal as a model: `sc_ideal` (`pgg_tableau.v:163`) is a law on
the cut group with no sample space, no secret and no witness, so
`sc_close` and `sc_const` alone cannot produce an `IdealProximityCert`; the
ideal model and its `ExactWitness` have to come from outside the spectral
certificate. That is the honest statement of the relation, and it is neither
the status file's nor the spec's. `idealproximity_reading_le`
(`p8_spectral_relation.v:89-118`) is correct: it projects the joint bound along
`fst` by `var_dist_fdistmap`, and identifies the ideal product's first marginal
with the ideal reading by `fdist_prod1`; both steps are sound and the lemma is
the sharpest carrier-level comparison available without a model of one arm
being a model of the other.

**5. P9.** The statement is right and 3 is what the proof gives.
`var_dist_own_marginals` (`p9_actual_marginals.v:61-82`) bounds
`var_dist J (fst J `x snd J)` by `d + (d + d)`, spending `d` once on
`J` against `Mr `x Ms` and once on each factor replacement through
`var_dist_prodR` and `var_dist_prodL`, each of the two factor distances being
`d` by data processing. The corollary
`five_card_biased_view_own_marginals` names only `kim_biased_family` and the
two marginals of its own joint law; the den Boer uniform model does not occur
in its statement. The only correction is S2, on what "advantage" means at this
normalization.

**6. P3 and P4.** `kim_biased_cert_idealE` (`p4_kim_biased_proximity.v:185-190`)
equates two things and claims two: `ipc_ideal cert` with
`amf_sample (ab_f (published_at five_card_row_uniform_tableau)) R idx`, the
adapter, and `ExactIndependence (ipc_witness cert)` with
`ab_port (published_at five_card_row_uniform_tableau) R idx`, the port, whence
the witness by injectivity of the constructor. It does not equate the whole
`ab` data, and the comment does not say it does. Since the certificate holds
nothing about the ideal beyond those two, P3 is fully met. P4:
`five_card_row_biased_tableau` is a `Tableau Sampled`
(`five_card_rows.v:472`), the spectral sibling
`five_card_row_biased_spectral_tableau` (`:622`) is written out from the prefix
and is unchanged by stage B (comment-stripped diff against `.8-before-fix4` is
empty for the whole file), and the two stage B programs both continue from the
named value through different arms, with `five_card_row_biased_arm_neq`
(`p4_kim_biased_proximity.v:332-336`) separating them and
`five_card_row_biased_branch_spectral_atE` showing the branch and the
written-out program hold one coordinate. Finding S1 is against the number the
proximity row publishes, not against its structure.

**7. P1.** The five lemmas are general, and named by what they say.
`var_dist_prodR` duplicates the two `Local Lemma`s at
`instances/pgl27/pgl27_mixing.v:1077` and
`instances/psl211/psl211_mixing.v:577`, which the status admits and which a
landing would replace. `var_dist_prodL`, `fdist_prod_snd`,
`var_dist_fdistmap_pair` and `fdist_uniform_prod` have no counterpart under any
name in `lib/`, `security/pgg_collusion_bound.v` or the instances, and
`fdist_prod_snd` has none in infotheo either: `fdist_prod1`
(`probability/fdist.v:1040`) is the first marginal, and `fdistX_prod2` (`:1133`) is a statement about a channel product, so the file's own reason for
stating it is accurate. The spec's claim that `var_dist_le2` exists only in the
Kim probe is stale, as `STATUS-stageB.md:352` says: it is at
`lib/var_dist_supp.v:51`. N1 stands against `fdist_uniform_prod`, which no
proof in the probe uses.

**8. G1.** Comment-stripped diffs against the correct stage A baselines,
`.7-before-stageB` where it exists and `.6-before-fix3` otherwise, show
`pgl27_rows.v`, `psl211_rows.v`, `s5_rows.v` and `t0_sampled_branch_pgl27.v`
untouched; `pgg_tableau.v` at minus four lines and plus ninety-four, the four
deletions being the last constructor line of `SecurityPort`, the `SecurityArm`
variant line and the two lines of `port_conclude`'s old proof, all three
rewritten and none removed in meaning; `pgg_tableau_syntax.v` and
`g2_keyword_measure.v` additions only. Every recorded `Fail` of stage A is
still present, by name: 5 in `five_card_rows.v`, 8 in `pgl27_rows.v`, 2 each in
`psl211_rows.v`, `s5_rows.v`, `t0_sampled_branch.v` and
`t0_sampled_branch_pgl27.v`, none missing and none added. The `match` sites on
a port in `pgg_tableau.v` are exactly four, at `:224` (`port_arm`), `:482`
(`PortProp`), `:797` (`ConcludePayload`) and `:813` (`port_conclude`), which is
the claim. N5 records that the one deletion of a declaration in
`five_card_rows.v` belongs to stage A.

**9. The soundness invariants.**

1. No new axiom, assumed constant, `Admitted` or `Abort`. **Met.** I compiled
   `assumptions_report_stageB.v` myself: 34 `Axioms:` blocks and one
   `Closed under the global context`, 35 in all; the scan `^([\w.]+)\s*:` over
   the output returns `Axioms`, `constructive_indefinite_description`,
   `functional_extensionality_dep`, `propositional_extensionality` and two
   tokens of my own harness. No source file of the probe contains `Admitted`,
   `Abort` or a top-level `Axiom`.
2. Every distance is a variation distance between exact laws, no computational
   assumption. **Met.** Every bound in stage B is `var_dist` between two
   `fdist`s, and no security parameter, adversary class or negligible function
   occurs anywhere.
3. The claim is an average over the run argument, not a statement at a fixed
   deck, and the refutations at a fixed deck stay true and are cited beside it.
   **Met on the substantive half**, vacuously on the citation half: the
   proposition's laws are pushforwards of `sa_sampleP`, and the five-card
   instance has no fixed-deck refutation to cite. Stage D will owe the citation.
4. The ideal in a certificate is a model with a witness, never a bare law.
   **Met.** `ipc_ideal : SampleAdapter R (instance_exec E)` with
   `ipc_witness : ExactWitness ipc_ideal`, and the type of `ipc_ideal` rejects
   another instance's model, as the recompiled `kim_biased_cert_s5_ideal` shows.
5. One claim per row; two claims about one model are two programs from one
   named `Tableau Sampled` value. **Met.** `five_card_row_biased_tableau` is
   the named value, two programs continue from it, and
   `five_card_row_biased_arm_neq` compiles.
6. No row publishes a number below the one it proved. **Met and refutable.**
   `ConcludePayload`'s proximity branch is an inequality, `port_conclude`
   proves the monotonicity, and `exp2.v` shows the obligation at a smaller
   number is false, not merely unproved.
7. Nothing is removed from the Tableau. **Met**; the four deletions in the diff
   are rewritten lines of a variant and of one proof.
8. No permanent file edited; probe files never imported by a permanent file;
   `psl211_endpoints` never compiled. **Met.** `git status` shows one tracked
   modification in the working tree, `notes/probes/2026-09-19-tableau-extensions/_CoqProject`,
   which is the probe's own file; no `.v` under `manifest/`, `instances/`,
   `lib/`, `security/`, `protocol/`, `smc/`, `reconstruct/`, `groups/` or
   `legacy/` is modified, none of them mentions `tableau_ext_probe`, and the
   production `_CoqProject` names neither the probe directory nor its logical
   path.

**10. Domain position of the statement comments.** A cryptographer reading only
the comments would get the attack model right and the normalization wrong. The
`IdealProximityCert` and `IdealProximityPropAt` comments both name the static
coalition below the threshold, both say the claim is an average over the run
argument and not a statement at a fixed one, both name the ideal as a model
whose own privacy is proved rather than assumed, and no comment mentions a
computational assumption, which is correct. The comment on
`certify_idealproximity` states why the ideal's link lemma is available, which
is the load-bearing design fact. Three comments state more than the lemma
proves, and they are S2, S3 and B1: the number is called "the whole advantage"
and "the whole of what the actual model loses" when it is an upper bound on a
sum of absolute differences, twice the quantity a distinguisher's advantage is
measured by; and the p8 comment draws an impossibility from certificate
freedom that a compiled lemma contradicts. The p4 comments are accurate
throughout except the halving sentence of S1, including the docstring of
`five_card_row_biased_proximity`, which correctly says what a coalition of
fewer than two seats is shown and against which ideal.

## Verdicts by ledger row

| Row | Verdict |
|---|---|
| P1 | GO |
| P2 | GO |
| P3 | GO |
| P4 | GO, with S1 against the published number |
| P7 | GO, with S1 against the account of the number |
| P8 | NO-GO, B1 |
| P9 | GO, with S2 against the reading of the constant |
| G1 | GO |

## Overall

**GO, conditional on B1.** The Rocq content of the arm is sound as it stands:
the certificate, the proposition and the composition law say what the attack
model wants, at the executed reader, on average over the run argument, with no
axiom beyond the three the tree already carries, with every field load-bearing,
with the ideal forced to be a model with a witness over the row's own
execution, and with a terminal that cannot publish below what the row proved.
Stages C and D may build on it now. What may not be folded into the spec as it
stands is the P8 account: `STATUS-stageB.md`'s sentence that a
certificate-free proposition "cannot imply a bound on the distance to one, at
any instance and at any constant" is false at the very instance stage B
carries, and I compiled the counter-lemma. Correct that account, apply R1, and
the fold is clean. S1 to S4 should be applied at the same time; none of them
touches a proof.

## What I did not check

- Stage A's own content: the fidelity of the copies to production, T0, the
  `conclude` change C1 to C3, the arm reader K1, and the surface syntax beyond
  the two rules stage B touches.
- `pgl27_rows.v`, `psl211_rows.v`, `t0_sampled_branch.v`,
  `t0_sampled_branch_pgl27.v` and `assumptions_report.v` were not compiled by
  me; the G1 verdict for them rests on the comment-stripped diffs and the
  `Fail` inventory, not on a fresh compile.
- Whether the proximity distance is positive at any coalition of the five-card
  instance. The probe shows the claim is not closed by conversion and not
  closed by `done`; nothing here or in the probe shows the two joint laws
  actually differ, so "non-trivial" is established in the weaker sense only.
- Whether the constant 3 of `var_dist_own_marginals` is optimal.
- The line numbers of the D2 list beyond the four claims I checked by grep:
  that production has no `SecurityArm`, `port_arm`, `ab_arm` or
  `security_arm_of`; that `manifest/pgg_tableau.v` is the only production file
  that matches on a `SecurityPort`; that `var_dist_le2` is in
  `lib/var_dist_supp.v`; and that `var_dist_prodR` is `Local` in the two mixing
  files.
- The naming audit, which is a separate auditor's.
- Anything about PGL(2,7) or PSL(2,11), which are stages C and D.
