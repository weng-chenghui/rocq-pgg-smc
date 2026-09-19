# Can Kim's five-card rows be certified by the spectral arm?

Date: 2026-09-19

Status: probe complete, 2026-09-19. Both claims hold. Kim's two five-card rows
can be certified by the existing `SpectralDecay` arm, with no change to
`manifest/pgg_tableau.v`. Five soundness audits found every compiled statement
true. Five naming audits ended with no blocking finding in the five `.v`
files. The record is `notes/probes/2026-09-19-kim-spectral-arm/STATUS.md`. No
permanent file was edited. A landing is a separate batch and needs the user's
decision. The companion probe `notes/probes/2026-09-19-psl211-sc-const/`
shows the same arm cannot serve PSL(2,11).

Follows [[20260919-kim-tableau-sampled-design]] and
[[2026-09-19-062455-third-certify-arm-for-the-biased-row]].

## Problem

The story the paper tells about every instance is the same. There is an ideal
model, in which the cut is uniform, and an actual model, in which it is not.
The ideal model is private. The actual model is close to the ideal one, so it
is private up to a small distance. PGL(2,7) tells this story in the Tableau:
`pgl27_row_exact_tableau` is the ideal row, and `pgl27_row_word_tableau` is the
actual one, certified by `SpectralDecay`.

For the five-card instance the ideal row is den Boer's uniform cut and the
actual rows are Kim's biased cut and Kim's seven biased cuts. Since 2026-09-19
both Kim programs stop at `Sampled`. The reason recorded then was that no
existing theorem supplies either arm of `certify`. That is true, and it left
the wrong impression that the rows cannot be certified. The note on a third
arm then looked at a new arm for the mutual information bound. That was the
wrong question. The arm the story needs already exists. `SpectralDecay` is
exactly "close to an ideal cut under which a coalition's reading does not
depend on the input".

So the right question is whether the two missing fields of a `SpectralCert` can
be proved for the five-card instance. If both can, Kim's rows reach
`AnalysisBridged` through the existing arm, the five-card instance reads like
PGL(2,7), and nothing under `manifest/pgg_tableau.v` changes. If either cannot,
the present state is the final one and the reason becomes a compiled fact.

The S5 instance is the warning. `instances/s5/s5_rows.v` records that for
`s5_row_word` the first field has nothing behind it and the second is false for
a reason no proof can remove. The claim here is that den Boer's encoding
differs from S5 on the second point, and that has to be shown and not assumed.

## The two claims

A `SpectralCert sa` has five fields (`manifest/pgg_tableau.v:131`). Three were
compiled one by one for the biased member in
`notes/probes/2026-09-19-kim-tableau-sampled/kim_biased_arms_probe.v`: `sc_b`,
`sc_Hd` and `sc_ideal`, the ideal being the uniform rotation law
`sa_cut_dist (five_card_sample R)`.

**Claim A, `sc_close`.** The variation distance on the cut group between the
bundle's law and the uniform rotation law is at most the bundle's own bound:

```coq
var_dist (sw_rho_dist sc_b) sc_ideal <= sw_bound_eps sc_b
```

What the tree has is a bound on one position's endpoint marginal, a distance
between two laws on `'I_5` (`sw_bound`, `kim_deal_centi_lt`,
`kim_one_cut_centiE`). The conjecture is that the two distances are the same
number. The cuts are powers of one 5-cycle. That group acts regularly on the
five positions, so a rotation is determined by the image of any one position.
Both laws are supported on the rotations. A pushforward along a map that is
injective on the union of two supports preserves variation distance.

**Claim B, `sc_const`.** Under the uniform rotation law, the reading of a
coalition below the threshold has the same law at every run argument:

```coq
forall C, (#|C| < profile_k (instance_profile five_card_algebra))%N ->
forall x x' : ex_inputT _,
  fdistmap (static_coalition_obs C x) ideal
  = fdistmap (static_coalition_obs C x') ideal
```

The threshold is 2 (`profile_k_denboer`), so `C` is empty or one seat. The
conjecture is that the law of one seat's colour under a uniform rotation does
not depend on the two input bits, because den Boer's encoding puts the same
number of cards of each colour on the table at every input. The precedent of
the same shape is `pgl27_word_view_const` (`instances/pgl27/pgl27_rows.v:224`),
proved there from three-transitivity. Here the reason would be the fixed colour
count, which is a different argument and may need a lemma about the encoding.

## Flow

The running value is the number of fields supplied, then the bound.

```
flow five_card_spectral_cert(row), row in {repeated, biased}            // fields 0/5
object   sa := amf_sample kim_<row>_family R tt                          // 0/5
field    sc_b     := scb_bound of the Kim bundle at bias 1/100, length L // 1/5  compiled earlier
field    sc_Hd    by kim_centi_cut_distE | kim_single_cut_distE          // 2/5  compiled earlier
field    sc_ideal := sa_cut_dist (five_card_sample R)                    // 3/5  compiled earlier
field    sc_close by regular action of the rotations, then sw_bound      // 4/5  claim A
field    sc_const by the fixed colour count of den Boer's encoding       // 5/5  claim B
terminal certify SpectralDecay ... |> publish                            // cert_eps = 2 * sw_bound_eps
outside  the endpoint lemma and the mutual information bound stay beside the programs
outside  the manifest row five_card_row_repeated moving to AnalysisBridged is a landing matter
```

Roles. Object: the sample adapter. Step justifications: the five fields.
Interfaces for the external components: `kim_centi_cut_distE` and
`kim_single_cut_distE` for the cut law, `sw_bound` for the number, and
`var_dist_fdistmap_transfer` inside the framework's `spectral_tail`, which
turns the five fields into the arm's proposition. Assumptions invoked: none.

Structure. No change to the Tableau. The work supplies a payload to the
existing step `certify_spectral`.

## Pinned carrier

`sa := amf_sample kim_centi_family R tt` and
`amf_sample kim_biased_family R tt`, both of type
`SampleAdapter R (instance_exec five_card_params)` over an abstract
`R : realType`. The cut group type is `pgg_gT FiveCardKim_M`, convertible to
`{perm 'I_5}`. The run argument type is `ex_inputT` of the five-card
parameters, the pair of committed bits.

## Claim ledger

| ID | Checkable claim | Passing evidence |
|---|---|---|
| S1 | A pushforward along a map injective on the union of two supports preserves variation distance. | A generic lemma over finite types ending in `Qed`, or an existing lemma found in infotheo or `lib/`. A mutation with a non-injective map must fail to prove the equality. |
| S2 | The rotations act regularly: a power of `fc_sigma` is determined by the image of one position, and both cut laws are supported on the powers of `fc_sigma`. | Two lemmas ending in `Qed`. The support statements are for the uniform rotation law, the single biased cut law and the seven-cut law. |
| S3 | Claim A for the repeated row. | `sc_close` at `sc_b := scb_bound kim_security_bundle_centi` ends in `Qed`, from S1, S2 and `sw_bound`. |
| S4 | Claim A for the biased row. | The same at the bundle of word length 1. The bound is then `sw_bound_eps` of that bundle, and the probe reports its value and how it compares with the exact distance `1 / 50` of `kim_one_cut_centiE`. |
| S5 | Claim B. | `sc_const` at the uniform rotation law, for every coalition of size below 2 and every two run arguments, ends in `Qed`. If it is false, the smallest counter-probe: a seat and two inputs at which the two laws differ, compiled. |
| S6 | The five fields assemble. | `MkSpectralCert` applied to the five fields typechecks for each row, and `certify SpectralDecay` followed by `publish` elaborates to a `PublishedRow` in a probe file. |
| S7 | What the certified row states, in numbers. | `cert_eps` of each certificate as a closed expression, and a lemma bounding it: below `2%:R ^- 39` for the repeated row if the bundle's bound is below `2%:R ^- 40`, and the exact value for the biased row. The bound is compared with the trivial ceiling 1 of a variation distance, so that a vacuous number is reported as vacuous. |
| S8 | The published rows and the manifest. | `publish IdealFinite BaselineClassicalOnly` is compared with the manifest rows. `five_card_row_biased` is recorded as `StaticExecutedOnly`, and `five_card_row_repeated` as `Sampled` with `NoModelComparison`. The probe reports, by `erefl` or by a recorded `Fail`, which `rowE` equations hold today and which manifest fields a landing would have to change. |
| S9 | Nothing already proved is contradicted. | The exact arm stays false in expectation under a biased cut, and the probe does not claim otherwise. `SpectralPropAt` is about two run arguments and a coalition below the threshold, and is not a statement about the full reveal. The landed mutual information bound covers that and stays. |
| S10 | Names and homes for a landing. | Each new lemma has a proposed permanent name and file. Generic lemmas do not go into a file below `psl211_endpoints`. The reverse-dependency closure of each proposed home is computed from `.Makefile.rocq.d`. |

## Cited objects

| Object | File | Required statement shape |
|---|---|---|
| `SpectralCert`, `cert_eps`, `SpectralPropAt`, `spectral_tail`, `mk_spectral` | `manifest/pgg_tableau.v:131`, `:345`, `:331`, `:561` | The five fields, the bound as twice `sw_bound_eps`, the arm's proposition, and the lemma that derives it. |
| `sw_bound`, `sw_bound_eps`, `sw_rho_dist`, `scb_bound` | the shuffle certificate layer | One position's endpoint marginal is within `sw_bound_eps` of uniform. |
| `kim_security_bundle_centi`, `kim_deal_centi_lt`, `kim_one_cut_centiE`, `kim_var_dist_exact` | `instances/kim2025/five_card_kim.v:640`, `:646`, `:661`, `:463` | The seven-cut bundle, its bound below `2^-40`, the exact one-cut distance `1 / 50`, and the exact distance at length `L`. |
| `kim_centi_cut_distE`, `kim_single_cut_distE` | `instances/kim2025/five_card_models.v:402`, `:188` | The cut law of each model is the weighted word shuffle. |
| `five_card_sample`, `five_card_sample_cut_distE` | `instances/kim2025/five_card_models.v` | The uniform rotation model and its cut law. |
| `fc_sigma`, `fc_kim_gensE` | `instances/kim2025/five_card_group.v`, `five_card_kim.v:125` | The 5-cycle and the generators as its powers. |
| `static_coalition_obs`, `five_card_static_obsE` | the framework, `instances/kim2025/five_card_rows.v:234` | The direct computation of a coalition's reading, and its identification with the colour reading. |
| `profile_k_denboer` | `instances/denboer1989/den_boer_profile.v:90` | The threshold is 2. |
| `pgl27_word_mixing`, `pgl27_word_view_const` | `instances/pgl27/pgl27_mixing.v:1048`, `pgl27_rows.v:224` | The precedents for the two fields. |
| `s5_word_base_premise` and the header of `s5_rows.v` | `instances/s5/s5_models.v`, `s5_rows.v:52-72` | The instance where the first field is unproved and the second is false. |
| `var_dist`, `fdistmap`, `fdist_uniform_supp_notin` | infotheo | Variation distance and pushforward. |

## Soundness invariants

1. No new axiom, assumed constant, `Admitted` or `Abort`, apart from the one
   decomposition probe the method allows, which stays in the probe.
2. Every distance is a variation distance between exact laws. No computational
   assumption appears.
3. Claim B is a statement about a coalition of at most one seat. Nothing in the
   probe or its comments extends it to two seats or to the full reveal.
4. The certified statement is about two run arguments. It is not independence
   from the secret, and the probe does not present it as such.
5. If claim B is false, the probe says so with a compiled counterexample and
   does not weaken the statement until something compiles.
6. The number is reported honestly. A bound of order `1 / 25` for the single
   biased cut is a weak statement and is reported as weak.
7. No permanent file is edited. Probe files are kept and never imported by a
   permanent file.

## Probe artifacts

Directory `notes/probes/2026-09-19-kim-spectral-arm/`, logical path
`kim_spectral_arm_probe`: `var_dist_injective_probe.v` for S1,
`five_card_rotation_probe.v` for S2, `kim_sc_close_probe.v` for S3 and S4,
`five_card_sc_const_probe.v` for S5, `kim_spectral_rows_probe.v` for S6 to S8,
`_CoqProject`, `STATUS.md`, and the two audit reports.

## Acceptance condition

S1 to S10 each end in GO or in NO-GO with an isolating counter-probe. An
independent soundness audit and an independent naming audit end in a verdict.
The batch then reports to the user what a landing would change. It edits no
permanent file.

## Results, folded back on 2026-09-19

| ID | Verdict | What was compiled |
|---|---|---|
| S1 | GO | `var_dist_fdistmap_supp_inj`: a pushforward along a map injective on the union of two supports preserves variation distance. infotheo has no lemma relating `var_dist` and `fdistmap`. The tree's `var_dist_fdistmap` is data processing and runs the wrong way for this use, so the equality was needed. A constant reader is the compiled mutation. |
| S2 | GO | `fc_sigma_pow_point_inj`, and one support lemma at every word length and weighting, `fc_kim_rho_supp_pow`, from which the two Kim cut laws follow in one line each. |
| S3, S4 | GO | `kim_centi_cut_mixing` and `kim_biased_cut_mixing`, at the exact type of the certificate's fourth field, with no added hypothesis. |
| S5 | GO | `five_card_static_obs_const`, at the exact type of the fifth field. The reason is the colour census of den Boer's layout: three hearts and two clubs at each of the four inputs. The layout at both inputs true is not a rotation of the other three, so the rotation orbit alone does not give it. `five_card_viewS_indep` does not imply it: independence equates averages, and the field equates laws at two fixed inputs. |
| S6 | GO | Four certificates and four published programs. |
| S7 | GO | Repeated row: the certificate's own number is `2 * sqrt 5 * (1/80)^7`, about `2.13e-13`, below `2^-39`; written as a constant it is `2^-40 + 2^-40`, repriced to `2^-39`, about eight and a half times weaker. One-cut row: `sqrt 5 / 40`, about `0.056`, or the exact `1/50 + 1/50 = 1/25`, which is the stronger of the two. Every number is compared with the ceiling 2, proved as `var_dist_le2`. |
| S8 | GO | Both manifest rows change at a landing. `five_card_row_repeated` moves to `AnalysisBridged` and `IdealFinite`. `five_card_row_biased` moves from `StaticExecutedOnly` to `IdealFinite`, because a row whose certificate is a comparison with an ideal cut is `IdealFinite` by the manifest's own definitions. A row equation compares row metadata and carries no theorem. |
| S9 | done | At every real field, for every coalition of at most one seat and every two committed pairs, the variation distance between the two static endpoint readings under the row's own cut law is at most the published number. It is not independence from the secret, not a statement about two seats, and not a statement about the full reveal. |
| S10 | done | Generic lemmas to a new `lib/var_dist_supp.v`, which needs one line in `_CoqProject`. The instance theorems either in `five_card_rows.v`, 10 files to recompile, or in a new `five_card_mixing.v` below the analysis facade, 11 files, which is the tree's convention and lets the manifest name the base premise. `psl211_endpoints` is in neither set. |

What this spec had wrong, as the probe and the audits showed.

1. The ceiling of infotheo's `var_dist` is 2 and not 1, since it is the sum of
   absolute differences and not half of it.
2. S1 suggested an inequality might do. The equality is required.
3. S2 asked for three support statements. One covers all three cut laws.
4. S8 expected the biased row to need no manifest change. It needs one.
5. The spec did not ask what a landing breaks. Finding that took three audit
   rounds, because the tree states the same facts in pins, in facade aliases
   and in sentences that carry no row name. The record now holds a seed list
   and the method for rebuilding it.

What the audits found about the arm itself, which the next batch takes up
([[20260919-tableau-three-extensions-probe-design]]): `spectral_tail` does not
consume the link lemma of `Sampled`, so the claim a spectral row publishes is
about static readings on both sides and never reaches the executed reader; and
the ideal in a certificate is a bare law on the cut group that never passed
through the phases.

## Out of scope

Any edit under `manifest/` or `instances/`. A third `certify` arm. The paper.
A statement about coalitions of two or more seats. The `s5_row_word` program.
