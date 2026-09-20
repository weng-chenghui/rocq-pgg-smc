# P8 arm relations: adversarial soundness audit (2026-09-20)

Spec `notes/20260920-p8-arm-relations-probe-design.md`. Probe
`notes/probes/2026-09-20-p8-arm-relations/`. No repository file other than this
one was written. Auditor scratch directory:

```
/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc/493d5ea4-6d9f-45fd-89c2-07339e63cb36/scratchpad/p8_audit/
```

Four scratch files were compiled through the single-Rocq lock wrapper with the
production load path. All four produced a `.vo` with no error:
`u_extra2.v` (A1 to A4 re-checked from source plus checks U1, U3, U4, U6, U7),
`u_numbers.v` (U5, U8), `u_threshold.v` (the threshold fact behind U2),
`u_final.v` (U2's unconditional restatement and U9). `Print Assumptions` inside
`u_extra2.v` prints the three classical axioms of `boolp` and nothing else, in
agreement with the probe's own record.

## Verdict

**NO-GO for landing first.**

No compiled statement of the probe is false, no assumed constant appears, and
the axiom set is the tree's. The block is in the probe's own record and in the
statement comments, not in the kernel:

- `p8b_instances.v`'s header asserts that the two numbers agree at both
  models, which the same file refutes at the five-card model (U5a).
- Departure 6 concludes that the spec's numeric expectation was wrong and that
  the generic construction is the looser one at the five-card model. The tree
  carries a second input-indistinguishability certificate at that same model,
  `kim_biased_cert_exact`, whose epsilon is exactly `1/50` and whose ideal cut
  law is the same. Fed that certificate, the generic construction carries the
  hand-built number. The conclusion is an artifact of the certificate the probe
  picked (U5b), and the spec's expectation was right.
- A4's and A5's threshold premise is a theorem of the framework, so both
  statements are unconditional and the premise makes them read as restricted
  when they are not (U2).
- A5 is a restatement of A4 with an eliminable parameter (U1).
- Four statement or header sentences over-claim: an implication from any
  premise whatever, an impossibility read off one `Fail`, a comparison between
  numbers attached to two different propositions, and a comment attached to the
  wrong step (U10, U11, U12, U13).

Each item is cheap to fix and none requires a new proof beyond the one-liners
already compiled in the scratch directory.

## Findings

| id | class | ledger row | file:line | finding, with the statement or proof step quoted, and the machine-checked evidence | what to change |
|---|---|---|---|---|---|
| U1 | MUST | A5 | `notes/probes/2026-09-20-p8-arm-relations/p8a_degenerate_certificate.v:180` | `proximity_below2_uniform_in_cert_false (Hk) (Q : Prop) (c : R) : Q -> c < 2%:R -> ~ (Q -> forall cert, IdealProximityPropAt cert c)` is logically equal to the parameter-free `~ (forall cert, IdealProximityPropAt cert c)`, because `Q -> X` with a proof of `Q` in hand is `X`. Machine-checked both ways in `u_extra2.v`: `qfree_proximity_below2_forall_cert_false` states the parameter-free form and A5 follows from it in one step (`a5_from_qfree`), and in the earlier `u_extra.v` draft the converse direction was written as `apply: (proximity_below2_uniform_in_cert_false Hk (Q := True) Hc I)`. The parameter-free form is in turn one application of A4 to `degenerate_proximity_cert`. So A5 adds no proposition to A4. | Land the parameter-free statement `~ (forall cert : IdealProximityCert sa, IdealProximityPropAt cert c)` and drop `Q`, or keep A5 and say in its comment that `Q` is eliminable and that the corollary exists to name the reading, not to add strength. |
| U2 | MUST | A4, A5 | `p8a_degenerate_certificate.v:151`, `:181`, `:196` | The premise `(0 < profile_k (instance_profile A))%N` holds at every `PGGAlgebraic`. `profile_k mp = ts_k (rp_scheme ...)` (`protocol/pgg_monodromy_profile.v:101`) and `ts_k ts = (ts_k' ts).+1` (`reconstruct/pgg_sharing_framework.v:92`). `u_threshold.v` compiles `profile_k_gt0 (A : PGGAlgebraic) : (0 < profile_k (instance_profile A))%N` by `by rewrite /profile_k /ts_k`, and `u_final.v` compiles A4 with no premise at all: `degenerate_proximity_prop_below2_false_unconditional (c : R) : c < 2%:R -> ~ IdealProximityPropAt degenerate_proximity_cert c`. The premise is therefore not a restriction on the algebra. It is load-bearing only over a hypothetical profile of threshold zero, where `u_extra2.v`'s `proximity_prop_vacuous_at_threshold0` shows every proximity proposition holds at every number, and that profile is unreachable in this framework. | Drop `Hk` from A4, A5 and the corollary, and discharge it inside with `profile_k_gt0`, which should land beside `profile_k` or in the tableau file. If the premise is kept for readability, the comment must say it is a theorem of the framework and not a side condition. |
| U3 | SHOULD | A4 | `p8a_degenerate_certificate.v:150` | The bound two is attained, not merely approached: `u_extra2.v` compiles `degenerate_proximity_prop_at2 : IdealProximityPropAt degenerate_proximity_cert 2%:R` by `move=> C _; exact: var_dist_le2`, with no hypothesis. A4 is therefore exact at the endpoint and the probe did not record this. | Add the endpoint statement beside A4, so that the pair reads "false strictly below two, true at two", which is what makes "below two" the right threshold rather than an arbitrary one. |
| U4 | SHOULD | B2, B4 | `p8b_proximity_from_indistinguishability.v:158` | The section hypothesis `Hconst` has the shape of `ic_const` at `rho0`, and the ledger's B4 row says the witness comes "from `ic_const`", but the probe never derives one from the other, so after section discharge `proximity_cert_of_indistinguishability` demands `Hconst` as a separate argument although the caller already holds `ic`. `u_extra2.v` compiles the derivation: `hconst_of_ic_const (ic) (rho0) (Hic : ic_ideal ic = rho0) : forall C, (#\|C\| < profile_k ...)%N -> forall x x', fdistmap (static_coalition_obs C x) rho0 = fdistmap (static_coalition_obs C x') rho0`, by `rewrite -Hic; exact: (@ic_const _ _ _ _ ic C HC x x')`. | Land that one-liner and let the certificate construction take `ic` and `Hic` only, so that the landed statement matches the ledger's own description of B4. |
| U5a | MUST | B6 | `p8b_instances.v:7` | The file header ends "The hypothesis of B1 therefore holds at both, and the number the generic certificate would carry is the number the hand-built certificate carries." The same file refutes the second clause at the five-card model: `kim_biased_proximity_epsE` gives `1 / 50` and `kim_biased_indistinguishability_epsE` gives `Num.sqrt 5%:R * (1 / 80)`. `u_numbers.v` compiles the strict separation `kim_biased_eps_lt : ipc_eps (kim_biased_proximity_cert R idx) < sw_bound_eps (ic_b (kim_biased_cert R idx))`, so the two are not equal and the probe's own `kim_biased_proximity_eps_generic_le` records only `<=`. | Rewrite the header to state what the file proves: the hypothesis of B1 holds at both models, the two numbers agree at the word model, and at the five-card model they agree or differ according to which of the two input-indistinguishability certificates the construction is fed (see U5b). |
| U5b | MUST | B6, departure 6 | `notes/probes/2026-09-20-p8-arm-relations/LEDGER.md:365`, `p8b_instances.v:110` | Departure 6 says the spec's expectation of one fiftieth against the certificate's own epsilon was wrong, and `p8b_instances.v:110` says "The generic construction is the looser of the two at this model." Both rest on choosing `kim_biased_cert`. The tree carries `kim_biased_cert_exact` (`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:880`) over the same model, built on `kim_biased_marginal_bound_exact` whose epsilon is `1 / 50` (`instances/kim2025/five_card_mixing.v:524`). `u_numbers.v` compiles `kim_biased_cert_exact_epsE : sw_bound_eps (ic_b (kim_biased_cert_exact R idx)) = 1 / 50`, `kim_biased_proximity_eps_exact_certE : ipc_eps (kim_biased_proximity_cert R idx) = sw_bound_eps (ic_b (kim_biased_cert_exact R idx))` and `kim_biased_cert_exact_idealE : ic_ideal (kim_biased_cert_exact R idx) = ic_ideal (kim_biased_cert R idx)`, all by `erefl`. Fed `kim_biased_cert_exact`, the generic construction carries the hand-built number exactly, and the ideal cut law it needs is unchanged. | Withdraw departure 6 as a departure. Record instead that the number the generic construction carries is whichever epsilon the chosen input-indistinguishability certificate carries, that the five-card model has two such certificates, and that at the one built on the exact one-cut distance the generic number equals the hand-built one. The spec's expectation was met. |
| U6 | SHOULD | B1, B5 | `p8b_proximity_from_indistinguishability.v:131`, `:294` | Vacuity of `Hprod` alone: taking `argT := unit` makes `Hprod` a statement about a one-point first factor. What blocks it in general is `Harg`, which forces `sa_arg` to factor through `arg_read`. `u_extra2.v` compiles the boundary: under `Hcstarg : forall u, sa_arg u = x0`, both `unit_Harg` and ``unit_Hprod : fdistmap (fun u => (tt, sa_cut u)) (sa_sampleP sa) = (fdist1 tt) `x (sa_cut_dist sa)`` hold, so at a model whose run argument is constant the whole of arm B applies with `ipc_secret` the constant map. B5 is then true and honest, and says only that the coalition's reading law under the model is within the number of the ideal's, with a one-point second coordinate carried along. It asserts nothing about hiding anything, because there is nothing to hide. | Say in B1's and B5's comments that the strength of the conclusion is the fineness of `arg_read`, that `Harg` is what makes `arg_read` determine the run argument, and that at a model with one run argument the statement is true and empty. |
| U7 | SHOULD | B2, B5 | `p8b_proximity_from_indistinguishability.v:229`, `:290` | The record ties `ipc_secret` to the ideal's `ew_secret` only by their common carrier `argT`. What makes the two sides speak of one secret and not of one type is that they have one law, and the probe never states it. `u_final.v` compiles the missing fact from `Hprod` alone: `arg_read_distE : fdistmap arg_read (sa_sampleP sa) = Parg`, and `Parg` is by construction the law the ideal adapter's first coordinate carries. | Land `arg_read_distE` beside B1 and cite it in B5's comment as the reason the comparison is between one secret's two joint laws. |
| U8 | NOTE | B6 | `p8b_instances.v:46`, `:79` | Both instance rows are existential: ``exists (Parg) (rho), fdistmap (fun u => (sa_arg u, sa_cut u)) (sa_sampleP ...) = Parg `x rho``, proved by `do 2 eexists; exact: fdistmap_prodr`. The witnesses are never named, so the rows do not say that `Parg` is the instance's own prior, which is what the ideal adapter then draws its run argument from. `pgl27_word_arg_readE` and `kim_biased_arg_readE` check `sa_arg` against `u.1` and against `five_card_sample_arg`, and `five_card_sample_arg u = u.1` (`instances/kim2025/five_card_exec.v:611`), so `arg_decode` is the identity at both, but neither `Harg` nor the identification of `Parg` with the prior is stated. | State the rows with the witnesses named, and add the two `Harg` instances, so that B6 says the hypotheses of B1 hold at the two models rather than that some pair of laws exists. |
| U9 | NOTE | B4 | `p8b_proximity_from_indistinguishability.v:268`, `:279` | `proximity_close_of_indistinguishability` carries the premise `(#\|C\| < profile_k (instance_profile A))%N` and discards it at once: the proof opens `move=> _.`. The distance holds at every coalition, as `kim_biased_proximity_close` does at the five-card instance, where the premise is absent and the record field is supplied as `fun C _ => ...`. | Drop the premise from the lemma and supply the record field as `fun C _ => ...`, which also records that the bound is not a threshold statement. |
| U10 | MUST | A4, A5 | `p8a_degenerate_certificate.v:9` | The header reads "Any premise whatever, an input-indistinguishability proposition among them, therefore fails to give the proximity proposition at any number below two once the conclusion is quantified over certificates." A premise that is false gives every conclusion, so the sentence is false as written. A5's statement is correct precisely because it takes a proof of `Q` (see U1), and the corollary discharges its premise with `indistinguishability_tail ic`. | Replace with a sentence quantified the way the statement is: "No proposition the model satisfies gives the proximity proposition at a number below two when the conclusion is quantified over certificates." Checked against `proximity_below2_uniform_in_cert_false`, whose hypotheses are `Q`, `c < 2%:R`. |
| U11 | MUST | A5 | `p8a_degenerate_certificate.v:177` | The comment reads "The premise is discharged by the degenerate certificate alone, so the strength of the premise plays no part." In `proximity_below2_uniform_in_cert_false` the premise is not discharged at all: it is the hypothesis `HQ` the caller supplies. What the degenerate certificate refutes is the conclusion. In the corollary below, the premise is discharged, and by `indistinguishability_tail ic`, not by the certificate. | Replace with: "The conclusion is refuted by the degenerate certificate alone, so no property of the premise enters." Checked against the proof step `exact: (degenerate_proximity_prop_below2_false Hk Hc (Himp HQ degenerate_proximity_cert))`, where `HQ` is consumed unexamined and the certificate supplies the refuting instance. |
| U12 | MUST | B7 | `p8b_proximity_from_indistinguishability.v:318` | The comment reads "The proposition B5 states is not closed by conversion". A recorded `Fail` rejects the one term written after `:=`, here `ltac:(by [])`, and shows no impossibility. The tree already holds itself to this: `instances/pgl27/tableau/pgl27_tableau_checks.v:229` writes "The Fail rejects the one term written here, on that mismatch of types, and rules out no other term." | Replace with: "The closing tactic `by []` does not prove the proposition B5 states, and the recorded error is `No applicable tactic`, the ssreflect closing tactic failing on the inequality rather than a missing name. The guard rejects this one term and rules out no other." Checked against the `Fail Definition ... := ltac:(by [])` at lines 322 to 326 and the error quoted in `LEDGER.md:294`. |
| U13 | MUST | B5 | `p8b_proximity_from_indistinguishability.v:303`, `:328` | "so the proximity reading of one certificate is the sharper of the two numbers by a factor of two" and "the proximity arm reads it once, the input-indistinguishability arm twice". `sw_bound_eps (ic_b ic)` bounds the distance between two joint laws of a coalition's reading and the secret, one per model. `cert_eps ic` bounds the distance between two readings of the cut under one model at two run arguments (`manifest/pgg_tableau.v:461` and `:496`). The two numbers bound different quantities, so neither is the smaller of two bounds on one quantity. `proximity_eps_halves_cert_epsE` itself is an equation between two reals proved by `erefl`, nothing more. | Replace with a type-honest sentence: "The number this certificate carries into the proximity arm is `sw_bound_eps (ic_b ic)`, and the number the same certificate carries into the input-indistinguishability arm is that value added to itself. The two bound different quantities, so the equation relates the two numbers and not the two propositions." Checked against `proximity_eps_halves_cert_epsE`, whose statement is `cert_eps ic = ipc_eps (...) + ipc_eps (...)`. |
| U14 | NOTE | A1 to A5 | `p8a_degenerate_certificate.v:40` | A bare `Search "dist_of_RV".` sits in the body of the probe file, above A1. | Remove before landing. |
| U15 | NOTE | decomposition | `notes/probes/2026-09-20-p8-arm-relations/p8_decomposition.v:101` | `headline_proximity_prop_at_cert_eps : IdealProximityPropAt cert (ipc_eps cert)` is proved by `exact: (idealproximity_tail cert model_coalition_viewE ideal_coalition_viewE)` from two `Admitted` link statements. That is `idealproximity_tail` itself, a production lemma, restated with its two hypotheses assumed. The file therefore decomposes the framework's tail and not the probe's B5, whose content is the construction of the certificate and the identification of its number. The file header's "nothing beyond what the supports assert is needed to reach either headline" is true and, for headline B, says only what `idealproximity_tail`'s own statement says. | Say so in the header, or decompose B5 by assuming `proximity_close_of_indistinguishability` and the two link statements, which is the shape B5 actually has. |
| U16 | NOTE | B3 mutation | `notes/probes/2026-09-20-p8-arm-relations/p8b_mut_product_needed.v:88` | `joint_le_cut_without_product_false` drops the product hypothesis but adds `fdistmap snd P = fdistmap snd Q`, so the right side of the refuted inequality is zero and the witness pair has one pair of marginals. It shows that two marginals do not determine a joint law. It does not exercise B3's own shape, which pushes both joints forward along `static_coalition_obs` and compares at a positive `var_dist rho rho0`. | Keep it, and add a mutation at B3's own shape: two joint laws with the same first marginal and second marginals at a positive distance, whose pushforwards along one reading are further apart than that distance. Or say in the comment that the check is on the generic fact behind B3 and not on B3. |
| U17 | NOTE | A1 mutation | `p8a_mut_disjointness_needed.v:23` | `var_dist_eq2_unconditional_false : ~ (forall A P Q, var_dist P Q = 2%:R)` refutes A1 with the hypothesis deleted, which is stronger than the spec's "the proof must fail". It does not test whether a weaker hypothesis would do. | Optional: add `~ (forall A P Q, (exists a, P a = 0) -> var_dist P Q = 2%:R)`, which separates disjointness everywhere from a single vanishing point. |
| U18 | NOTE | B1 to B5 | `p8b_proximity_from_indistinguishability.v:131` to `:157` | After section discharge, `proximity_cert_of_indistinguishability` and `proximity_prop_of_indistinguishability` take `argT`, `arg_decode`, `arg_read`, `Harg`, `Parg`, `rho`, `Hprod`, `rho0`, `Hconst` in front of `ic` and `Hic`, and none of the first nine is determined by the result type `IdealProximityCert sa`. Under `Set Implicit Arguments` with `Unset Strict Implicit` the ledger already reports one elaboration failure of exactly this kind at `fdistmap_pair_arg_prodE`. | Land explicit `Arguments` directives for both, so that a caller inside a Tableau program is not left to guess which of the nine the elaborator will ask for. |
| U19 | NOTE | B1 | `p8b_proximity_from_indistinguishability.v:127` | The source comment opens "The finite reading of the model's run argument", and `arg_read : sa_sampleT sa -> argT` reads the sample point, not the run argument. The same comment gets it right three lines later ("a finite reading of the sample point that determines it"). | Use the second phrasing in both places. One word per concept. |

## Answers to the eight questions

**1. A4 and A5.**

(a) `degenerate_proximity_cert` is a legitimate inhabitant. Every field has the
type and the meaning `IdealProximityCert` asks for: `ipc_ideal := sa` is a
sample adapter over `instance_exec E`, `ipc_witness` is an `ExactWitness` whose
`ew_indep` field is discharged by A2 at a constant secret, `ipc_secret` is a
random variable into `ew_secretT ipc_witness`, and `ipc_close` is `var_dist_le2`
at `ipc_eps := 2`. What it uses that the two landed certificates do not is the
record's silence on three points. The record does not ask the ideal to be a
different model from the actual one, and both landed certificates name a
separately published ideal (`amf_sample pgl27_prior_exact_family R secretP` at
`instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:829`,
`amf_sample five_card_uniform_family R idx` at
`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:975`). The
record does not ask the ideal's secret to be non-constant, and both landed
witnesses prove independence of a secret the execution computes. Above all the
record relates `ipc_secret` to `ew_secret ipc_witness` by their common carrier
only, never by their law, so a pair of disagreeing constants is legal. And
`ipc_eps` has no upper constraint, so the largest value of the scale is a legal
field. Nothing in the landed certificates rules the degenerate one out. They
simply choose better fields.

(b) What A4 shows: for every model over every algebra of this framework there
is a proximity certificate whose proximity proposition is false at every number
strictly below two, so no statement of the form "premise implies the proximity
proposition at `c` for every certificate" holds for `c < 2`. What A4 does not
show, (i) about the implication from the input-indistinguishability proposition
to the proximity proposition: nothing that contradicts B5, which proves exactly
such an implication at `sw_bound_eps (ic_b ic)` for the certificate the
construction builds, so A4 refutes the implication only when the certificate is
universally quantified in the conclusion. (ii) About a given meaningful
certificate: nothing whatever, since A4 speaks of one certificate all of whose
secret-side fields are constants, and it constrains no other certificate.

A5 is a restatement. See U1: `Q` together with a proof of `Q` reduces
`~ (Q -> X)` to `~ X`, both directions were compiled, and the parameter-free
statement is one application of A4. A5 should not land as if it added a
quantification over premises.

(c) The premise `0 < profile_k` is not needed. See U2:
`ts_k ts = (ts_k' ts).+1` makes it a theorem at every algebra, `profile_k_gt0`
compiles, and A4 compiles with no premise at all
(`degenerate_proximity_prop_below2_false_unconditional`). The counter-statement
the question asks for does compile in the abstract, as
`proximity_prop_vacuous_at_threshold0` under the assumption
`profile_k (instance_profile A) = 0`, but that assumption is unreachable here,
so it refutes nothing this framework can reach.

**2. B1 as reformulated.** Satisfiable at both production models, and not
degenerately, with one gap in the evidence. `arg_decode` is the identity at
both: at the word model `sa_arg u = u.1` by `erefl`, and at the five-card model
`sa_arg u = five_card_sample_arg u` by `erefl` with
`five_card_sample_arg u = u.1` by definition
(`instances/kim2025/five_card_exec.v:611`). `Parg` is not pinned to the
instance's prior, because both rows are existential and the witnesses come from
`eexists` (U8), so "is `Parg` the instance's actual prior" is not machine-checked
by the probe. `Hprod` alone can be satisfied with `argT := unit`, and what
blocks that in general is `Harg`, which forces `sa_arg` to factor through
`arg_read`. At a model whose `sa_arg` is constant nothing blocks it, and U6
compiles both `Harg` and `Hprod` there. B5 then says: the joint law of a
coalition's reading with a one-point secret under the model is within
`sw_bound_eps (ic_b ic)` of the product of the ideal's reading law with that
one-point law, which is the statement that the two readings are close, with a
constant carried along. That is true and honest, and it hides nothing, because
a model with one run argument has nothing to hide. The strength of B5 is
exactly the fineness of `arg_read`.

**3. B2.** The independence `ideal_product_reading_indep` is derived from the
constancy hypothesis `Hconst` and the product form of the ideal adapter's law,
through `fdistmap_pair_arg_prodE`, and from nothing else. `Hconst` has the shape
of `ic_const` at `rho0` and is in fact `ic_const ic` transported along
`ic_ideal ic = rho0`, which U4 compiles but the probe does not. The secret's
type is the right one, and more than the type holds: by U7 the actual model's
secret `arg_read` has law `Parg`, the same law the ideal's first coordinate
carries, so the two sides compare one secret's two joint laws and not two
unrelated random variables that happen to share a carrier.

At the five-card instance the landed certificate's secret is
`five_card_leakage.Secret R u`, which `five_card_reading_secretE`
(`instances/kim2025/five_card_proximity.v:103`) shows is `u.1.1 && u.1.2`, one
bit computed from the run argument pair. The generic construction's secret is
the whole pair. Comparing the two statements at equal numbers, the generic one
is the stronger: the landed law is the pushforward of the generic one along
`(v, p) |-> (v, p.1 && p.2)`, `var_dist` does not increase under a common
pushforward, and a product pushes forward componentwise, so the generic
statement at `eps` implies the landed shape at `eps`. This last step is an
argument and was not compiled. At the numbers as they stand the two are
incomparable, because the generic construction fed `kim_biased_cert` carries
`Num.sqrt 5%:R * (1 / 80)`, strictly above `1 / 50` by U5a, while the landed one
carries `1 / 50` about a coarser secret. Fed `kim_biased_cert_exact` the generic
construction carries `1 / 50` as well (U5b), and there it is strictly stronger
than the landed statement.

**4. B5's premise `instance_endpoints_stmt E`.** It is a component every
published program already carries. `StackAt Sampled` contains
`{He : instance_endpoints_stmt E ...}` (`manifest/pgg_tableau.v:289` and the
accessor `sp_He` at `:332`), and `certify_idealproximity` builds the ideal
model's link hypothesis from `sp_He x` by `sa_coalition_viewE`
(`manifest/pgg_tableau.v:832`), which is exactly what B5 does with `Hendp`.
`certify_idealproximity` takes the actual model's link from the Sampled
proposition, `proj2 q R idx`, rather than rebuilding it, which is the same
proposition. B5 is therefore usable inside a Tableau program with no new
obligation.

**5. B6's numbers.** Verified independently in `u_numbers.v`. At the five-card
one-cut model `ipc_eps (kim_biased_proximity_cert R idx) = 1 / 50` and
`sw_bound_eps (ic_b (kim_biased_cert R idx)) = Num.sqrt 5%:R * (1 / 80)`, and
the separation is strict: `kim_biased_eps_lt` compiles
`ipc_eps (kim_biased_proximity_cert R idx) < sw_bound_eps (ic_b (kim_biased_cert R idx))`
from `2%:R < Num.sqrt 5%:R`. The probe records only `<=`, which does not support
the word "sharper" in its own comment. At PGL(2,7) the two are equal by
conversion, and the common value is `2%:R^-40`
(`pgl27_word_eps_valueE`, compiled).

The explanation offered is right as far as it goes and incomplete where it
matters. `kim_biased_proximity_close`
(`instances/kim2025/five_card_proximity.v:144`) ends `exact:
kim_biased_cut_mixing_exact`, the exact one-cut distance, and `kim_biased_cert`
(`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:628`) carries
`kim_biased_marginal_bound R`, the spectral bound, so the two numbers have
different origins. What the explanation omits is that the difference is not a
loss of the generic construction. The generic chain's own inequality, B3, gives
`var_dist rho rho0`, which at this model is the exact one-cut distance the
hand-built certificate uses. The slack sits entirely in the certificate's
`ic_close` field, and the tree carries a second certificate at the same model,
`kim_biased_cert_exact`, whose `ic_close` is the exact bound and whose epsilon is
`1 / 50`. See U5b.

**6. Type honesty of the docstrings and headers.** Four sentences must change,
U10 (a universal over premises that a false premise refutes), U11 (a comment
attached to the wrong step), U12 (an impossibility read off one `Fail`, against
the tree's own standard), U13 (two numbers attached to two propositions compared
as if they bounded one quantity). Two more should change, U5a (a header sentence
the file refutes) and U19 (a reading of the sample point called a reading of the
run argument). The scale sentence is present and correct in
`p8a_degenerate_certificate.v:9` and `p8b_proximity_from_indistinguishability.v:11`.
It is absent from `p8b_instances.v`, which is the file that prints the numbers,
and should be added there. The average-case and single-run scope is stated at
`p8b_proximity_from_indistinguishability.v:10` and matches the record's own
wording at `manifest/pgg_tableau.v:214`. No place calls a `<=` bound "the
distance".

**7. Mutations.** All three are real, each negates the right thing, and none
would have compiled as a proof of the mutated statement, because each is a
refutation of the mutated statement rather than an attempted proof. The A1
mutation refutes the hypothesis-free equation, the A4 mutation refutes A4's
conclusion for a certificate whose two secrets are one constant, and the B3
mutation refutes the inequality for two joint laws with one pair of marginals.
Two carry caveats, U16 (the B3 mutation is on the generic fact behind B3, at
zero right side, not at B3's shape) and U17 (the A1 mutation does not test
weaker hypotheses).

Four mutations the probe did not try, all compiled here except where noted:

- A4, threshold: `proximity_prop_vacuous_at_threshold0` and
  `a4_conclusion_false_at_threshold0` in `u_extra2.v`. The conclusion is false at
  threshold zero, and `profile_k_gt0` in `u_threshold.v` then shows the case is
  unreachable, so the premise can go (U2).
- A4, endpoint: `degenerate_proximity_prop_at2` in `u_extra2.v`. The proposition
  holds at two with no hypothesis, so "below two" is exact (U3).
- A5, eliminability: `a5_from_qfree` in `u_extra2.v` and the converse direction
  written in `u_extra.v` (U1).
- B5, the unit degeneracy: `unit_Harg` and `unit_Hprod` in `u_extra2.v` (U6).

Not compiled, proposed for the landing: the B3 mutation at B3's own shape (U16)
and the A1 mutation at a weaker hypothesis (U17).

**8. Other observations.** The `Set Implicit Arguments` discharge trap the
probe reports will reach the landing, because nine of the eleven arguments of
the two B-side definitions are not determined by the result type (U18). One
lemma is trivial by convertibility on purpose:
`same_secret_proximity_cert`'s `ipc_close` field is `var_dist_self_le0 _`, and
the two laws it compares are the same term, which is what the mutation is for.
One hypothesis is introduced and immediately discarded, `move=> _` at
`p8b_proximity_from_indistinguishability.v:279` (U9), and one is unused and
already recorded by departure 5. Nothing is made opaque or transparent against
the tree's habit: the two `Definition`s that produce records are plain
definitions, as the landed certificates are. A bare `Search` is left in the
source (U14). The `p8_decomposition.v` headline B restates `idealproximity_tail`
rather than B5 (U15).

## Machine-checked evidence, by file

| scratch file | what it compiles | result |
|---|---|---|
| `u_extra2.v` | A1, A2, A3, A4 re-checked from source, plus `qfree_proximity_below2_forall_cert_false`, `a5_from_qfree`, `degenerate_proximity_prop_at2`, `proximity_prop_vacuous_at_threshold0`, `a4_conclusion_false_at_threshold0`, `hconst_of_ic_const`, `unit_Harg`, `unit_Hprod` | `.vo` produced, no error, three `Print Assumptions` print the three classical axioms only |
| `u_numbers.v` | `kim_biased_cert_exact_epsE`, `kim_biased_proximity_eps_exact_certE`, `kim_biased_cert_exact_idealE`, `kim_biased_eps_lt`, `pgl27_word_eps_valueE` | `.vo` produced, no error |
| `u_threshold.v` | `profile_k_gt0`, `set0_below_threshold` | `.vo` produced, no error |
| `u_final.v` | `degenerate_proximity_prop_below2_false_unconditional`, `arg_read_distE` | `.vo` produced, no error |

One earlier attempt, `u_extra.v`, failed with "Compiled library
`p8probe.p8a_degenerate_certificate` makes inconsistent assumptions over library
`pgg_smc.pgg_tableau`", the transient stale-object condition the task predicted.
The response was to make the scratch files self-contained rather than to require
the probe's modules, which also re-checks A1 to A4 from source.
