# Landing the three Tableau extensions

Date: 2026-09-20

Status: DESIGN AND PLAN. Nothing is landed. This note plans the landing of
`notes/probes/2026-09-19-tableau-extensions/` into the permanent tree. The
probe's verdicts, its eleven changes to the spec and its landing order are in
`notes/20260919-tableau-three-extensions-probe-design.md:285-429`. The
procedure imitated is the Kim spectral landing
(`docs/superpowers/plans/2026-09-19-kim-spectral-landing.md`,
`notes/20260919-kim-spectral-landing-design.md`) and the PSL(2,11)
reading-constancy landing
(`notes/20260919-psl211-spectral-nogo-landing-design.md`).

No file was compiled while this note was written. Every statement about a
compile cost or a compile outcome below is either quoted from the probe's
records or marked "needs a compile".

`var_dist` is the sum of absolute differences of two laws, twice the total
variation distance of the literature, as `lib/var_dist_supp.v` states. A
published number is an upper bound on that sum, not a distance, and a
distinguisher's advantage is at most half of it.

---

## Flow

The connecting operation of the whole landing is: put one audited file into
the tree, then compile it alone, in dependency order. The running value is
the number of production files whose text is final.

```
flow landing(probe)                                                      // 0
object  staged/  : the permanent-form text of every file that lands      // 0
step    land1 framework   cp manifest/pgg_tableau.v                      // 1
step    land1 framework   cp manifest/pgg_tableau_syntax.v               // 2
step    land1 rows        cp instances/pgl27/pgl27_rows.v                // 3
step    land1 rows        cp instances/kim2025/five_card_rows.v          // 4
step    land1 rows        cp instances/s5/s5_rows.v                      // 5
step    land1 rows        cp instances/psl211/psl211_rows.v              // 6
step    land1 re-read     instances/psl211/psl211_reading_constancy.v    // 7
step    land2 library     cp lib/var_dist_supp.v                         // 8
step    land2 instance    cp instances/kim2025/five_card_mixing.v        // 9
step    land2 rows        new instances/kim2025/five_card_proximity.v    // 10
step    land3 exec        edit instances/pgl27/pgl27_exec.v              // 11
step    land3 models      edit instances/pgl27/pgl27_models.v            // 12
step    land3 facade      edit instances/pgl27/pgl27_analysis.v          // 13
step    land3 manifest    edit manifest/pgg_analysis_manifest.v (row 10) // 14
step    land3 rows        new instances/pgl27/pgl27_proximity.v          // 15
step    land4 model       new instances/psl211/psl211_word_model.v       // 16
step    land4 facade      edit instances/psl211/psl211_analysis.v        // 17
step    land4 manifest    edit manifest/pgg_analysis_manifest.v (row 11) // 18
step    land4 client      edit manifest/pgg_analysis_client.v            // 19
step    land4 rows        new instances/psl211/psl211_word_proximity.v   // 20
beside  landing_fidelity.v against the staged text                       // 20
beside  asbuilt_fidelity.v against production after each cp              // 20
outside the paper, notes/probes/, psl211_endpoints.v
```

External components and the interface each enters through: `pgl27_view_mixing`
enters as the argument of `inde_dist_of_RV2` inside the PGL(2,7) distance
field; `psl211_word_mixing` enters through `psl211_word_cut_distE` as the
distance field of the PSL(2,11) certificate; `kim_biased_cut_mixing_exact`
enters through `var_dist_fdistmap_pair` as the five-card distance field;
`var_dist_le2` of `lib/var_dist_supp.v` enters as the ceiling every published
number is compared against.

`Monad:` no monadic structure at the landing level. This is a linear order of
copies and compiles, each depending on the `.vo` files written before it, as
the Kim landing plan also recorded for itself
(`docs/superpowers/plans/2026-09-19-kim-spectral-landing.md:14`). The Tableau
itself is the graded structure; the landing is not.

`DSL:` none is needed. The Tableau is the DSL and the landing adds one arm,
one relaxed terminal obligation and one reader to it.

---

## 1. The four landings, file by file

### Landing 1 — the framework, and the four rows files

D2 fixes that `manifest/pgg_tableau.v` and `manifest/pgg_tableau_syntax.v`
land once, carrying stage A and stage B together. The probe's text of those
two files is one audited text and holds both.

| Production file | Text from | What changes |
|---|---|---|
| `manifest/pgg_tableau.v` | probe `pgg_tableau.v` | whole file; 37 hunks, 427 changed lines against production (measured by `diff`) |
| `manifest/pgg_tableau_syntax.v` | probe `pgg_tableau_syntax.v` | whole file; 7 hunks, 73 changed lines |
| `instances/pgl27/pgl27_rows.v` | probe `pgl27_rows.v` | whole file; 19 hunks, 188 changed lines |
| `instances/kim2025/five_card_rows.v` | probe `five_card_rows.v` | whole file; 26 hunks, 180 changed lines |
| `instances/s5/s5_rows.v` | probe `s5_rows.v` | whole file; 3 hunks, 15 changed lines |
| `instances/psl211/psl211_rows.v` | probe `psl211_rows.v` | whole file; 3 hunks, 12 changed lines |

The only edit the landing forces on those six texts is the `Require` block:
the probe's `From tableau_ext_probe Require Import pgg_tableau
pgg_tableau_syntax` becomes `From pgg_smc Require Import pgg_tableau
pgg_tableau_syntax`. The probe-local edges are exactly
`pgg_tableau_syntax -> pgg_tableau` and `<rows> -> {pgg_tableau,
pgg_tableau_syntax}` and nothing else, so no other line moves.

What lands in landing 1, by content: the `<=` obligation of `conclude`
(`ConcludePayload`, `port_conclude`), the `SecurityArm` reader (`port_arm`,
`ab_arm`, `security_arm_of`, the five general `_armE` lemmas), the `conclude`
keyword notation, the `IdealProximity` arm with its certificate, proposition,
composition law, builder, reader and notation, the per-program `_armE` pins in
the four rows files, `pgl27_rows.v`'s payload wrapped in `eqW`, and the
repeated five-card row on the `ltW` route.

D3: the withdrawal splits across two landings, because the four declarations
live in two files.

| Declaration | Defined at | Withdrawn in |
|---|---|---|
| `kim_centi_cert40` | `instances/kim2025/five_card_rows.v:737` | landing 1 |
| `kim_centi_cert40_epsE` | `instances/kim2025/five_card_rows.v:749` | landing 1 |
| `kim_centi_marginal_bound40` | `instances/kim2025/five_card_mixing.v:507` | landing 2 |
| `kim_centi_cut_mixing40` | `instances/kim2025/five_card_mixing.v:517` | landing 2 |

The consumption chain, read off the two files:
`kim_centi_marginal_bound40` is the `sc_b` field of `kim_centi_cert40`
(`five_card_rows.v:741`) and the subject of `kim_centi_cut_mixing40`
(`five_card_mixing.v:518,520`); `kim_centi_cut_mixing40` is the `sc_close`
field of `kim_centi_cert40` (`five_card_rows.v:744`); and `kim_centi_cert40`
is consumed today by `kim_centi_cert40_epsE` (`five_card_rows.v:749`) and by
the real `five_card_row_repeated39` (`five_card_rows.v:765`). So landing 1's
copy of `five_card_rows.v`, which reroutes the repeated row to
`kim_centi_cert` by `ltW (kim_centi_cert_eps_lt R idx)`
(probe `five_card_rows.v:781-783`), leaves the two mixing-file declarations
with no consumer, and landing 2 removes them from `five_card_mixing.v`, which
it edits for D5 in any case. Putting them in landing 1 instead would add
`five_card_mixing.v` and its ten-file reverse closure to that landing for no
gain.

Note that the probe's own `five_card_rows.v` still *defines* `kim_centi_cert40`
at its `:752` and `kim_centi_cert40_epsE` at its `:764`; the probe rerouted the
row and did not remove the certificate. Landing 1 removes both, along with the
index-comment lines that name them (probe `five_card_rows.v:98,154`). This is
the one place where the staged text is not the probe's text with only a
`Require` rewrite, and D1's "after only the edits a landing forces" covers it,
because D3 is an owner decision.

Citation scan for D3: no hit for any of the four names in `paper/`,
`paper-wadt2026/` or `paper-wadt2026-baseline-application/`. Outside
`notes/probes/` the names appear only in the two files above and in six notes
(`notes/20260919-kim-spectral-landing-design.md:42,176`,
`notes/2026-09-19-214329-tableau-campaign-tracker.md:45`,
`notes/20260919-tableau-three-extensions-probe-design.md:306,410`,
`notes/2026-09-19-112500-spectral-arm-at-kim-and-psl211-summary.md:187`,
`notes/2026-09-19-230000-audit-rename-input-indistinguishability-arm.md:28,63`).
Those notes are records of the campaign and are not rewritten; the landing
adds a line to the tracker saying the four are withdrawn.

### Landing 2 — the generic lemmas, the library move, the five-card row

| Production file | Text from | What changes |
|---|---|---|
| `lib/var_dist_supp.v` | probe `p1_joint_law_distance.v` | `var_dist_fdistmap_pair`, `var_dist_prodR`, `fdist_prod_snd`, `var_dist_own_marginals` added; `card_tnth_count` removed from `:166` |
| `instances/kim2025/five_card_mixing.v` | production plus the moved lemma | `card_tnth_count` added; `kim_centi_marginal_bound40` (`:507`) and `kim_centi_cut_mixing40` (`:517`) removed per D3 |
| `instances/kim2025/five_card_proximity.v` (new) | probe `p4_kim_biased_proximity.v`, `p9_actual_marginals.v`, `p7_mutations.v`, `p8_spectral_relation.v` | new file |

D5 puts `var_dist_prodR` and `fdist_prod_snd` into `lib/var_dist_supp.v` and
moves `card_tnth_count` out of it into its only user. `var_dist_fdistmap_pair`
is the third generic lemma of `p1_joint_law_distance.v`; it is generic in the
same sense and belongs with them. See the risk list for `var_dist_prodL` and
`fdist_uniform_prod`, which the probe also proves.

### Landing 3 — PGL(2,7)

| Production file | Text from | What changes |
|---|---|---|
| `instances/pgl27/pgl27_exec.v` | probe `p5_pgl27_prior_ideal.v:78-85` | `pgl27_prior_sample` added |
| `instances/pgl27/pgl27_models.v` | probe `p5_pgl27_prior_ideal.v:87-132` | `pgl27_prior_exact_family`, `pgl27_prior_viewE`, `pgl27_prior_exact_witness` added |
| `instances/pgl27/pgl27_analysis.v` | new alias | `prior_exact_family` added to `PGL27Analysis` |
| `manifest/pgg_analysis_manifest.v` | probe `p5_pgl27_prior_ideal.v:157-160` | one new `AnalysisPathRow`, its table block, its three pins |
| `instances/pgl27/pgl27_proximity.v` (new) | probe `p5_pgl27_prior_ideal.v` (programs), `p5_pgl27_word_proximity.v`, `p5_mutations.v` | new file |

### Landing 4 — PSL(2,11)

| Production file | Text from | What changes |
|---|---|---|
| `instances/psl211/psl211_word_model.v` (new) | probe `p6_psl211_word_model.v` | new file |
| `instances/psl211/psl211_analysis.v` | new alias | `word_family` added to `PSL211Analysis` |
| `manifest/pgg_analysis_manifest.v` | probe `p6_psl211_word_proximity.v:250-256` | one new `AnalysisPathRow`, its table block, its three pins |
| `manifest/pgg_analysis_client.v` | new `Check` lines | the row count and the two new family aliases |
| `instances/psl211/psl211_reading_constancy.v` | comment only | the sentences the word adapter makes false |
| `instances/psl211/psl211_word_proximity.v` (new) | probe `p6_psl211_word_proximity.v`, `p6_mutations.v` | new file |

`_CoqProject` gains four lines. The existing block around
`_CoqProject:215-226` fixes the anchors:

| New line | Inserted after |
|---|---|
| `instances/psl211/psl211_word_model.v` | `instances/psl211/psl211_models.v` (`_CoqProject:215`), before `psl211_recovery.v` |
| `instances/pgl27/pgl27_proximity.v` | `instances/pgl27/pgl27_rows.v` (`_CoqProject:221`) |
| `instances/kim2025/five_card_proximity.v` | `instances/kim2025/five_card_rows.v` (`_CoqProject:222`) |
| `instances/psl211/psl211_word_proximity.v` | `instances/psl211/psl211_rows.v` (`_CoqProject:225`) |

---

## 2. Declaration by declaration (D6)

D6: a declaration of the probe becomes permanent only if the paper or a note
claims it, or later work needs it as a premise. The probe copy is the record
of the rest.

### `p1_joint_law_distance.v`

| Declaration | Lands in | Reason |
|---|---|---|
| `var_dist_fdistmap_pair` (:61) | `lib/var_dist_supp.v` | premise of every proximity distance field; it is the data-processing step P1 names |
| `var_dist_prodR` (:84) | `lib/var_dist_supp.v` | D5; premise of the PSL(2,11) distance field |
| `var_dist_prodL` (:100) | stays in the probe | used by no landing declaration. See risk R6 |
| `fdist_prod_snd` (:115) | `lib/var_dist_supp.v` | D5 |
| `fdist_uniform_prod` (:122) | stays in the probe | used by no landing declaration. See risk R6 |

### `p4_kim_biased_proximity.v`

| Declaration | Lands in | Reason |
|---|---|---|
| `five_card_uniform_pairE` (:86) | `five_card_proximity.v` | premise of `kim_biased_proximity_close` |
| `five_card_reading_secretE` (:95) | `five_card_proximity.v` | premise of the same |
| `five_card_arg_cut_prodE` (:116) | `five_card_proximity.v` | premise of the same |
| `kim_biased_proximity_close` (:136) | `five_card_proximity.v` | the distance field of the certificate |
| `kim_biased_proximity_cert` (:176) | `five_card_proximity.v` | the certificate the row certifies |
| `kim_biased_proximity_cert_idealE` (:190) | `five_card_proximity.v` | P3, the certificate's ideal is the published ideal row |
| `kim_biased_proximity_cert_epsE` (:207) | `five_card_proximity.v` | states which number the row publishes |
| `kim_biased_proximity_eps_halfE` (:220) | `five_card_proximity.v` | the advantage reading of the published number; the spec's change 4 makes this the honest form |
| `kim_biased_proximity_cert_eps_lt2` (:230) | `five_card_proximity.v` | P7, the number is below the `var_dist_le2` ceiling, so the claim is not vacuous |
| `five_card_row_biased_branch_indistinguishability` (:245) | `five_card_proximity.v` | the sibling program that makes the two-claims-one-model shape real |
| `five_card_row_biased_branch_indistinguishability_atE` (:255) | `five_card_proximity.v` | pins the branch against the named `Tableau Sampled` value |
| `five_card_row_biased_branch_indistinguishability_rowE` (:261) | `five_card_proximity.v` | the manifest row the sibling publishes, already held |
| `five_card_row_biased_proximity` (:275) | `five_card_proximity.v` | the new program |
| `five_card_row_biased_proximity_rowE` (:285) | `five_card_proximity.v` | the manifest row it publishes, already held by `five_card_row_biased` |
| `five_card_row_biased_proximity_publishedE` (:290) | `five_card_proximity.v` | the published number, one fiftieth |
| the two `_armE` lemmas (:300, :313) | `five_card_proximity.v` | K1, the arm pin each program owes |
| `five_card_row_biased_arm_neq` (:321) | `five_card_proximity.v` | the two siblings carry different arms; this is what the reader was added for |
| `five_card_biased_view_proximity` (:337) | `five_card_proximity.v` | the theorem a paper cites |

### `p5_pgl27_prior_ideal.v`

| Declaration | Lands in | Reason |
|---|---|---|
| `pgl27_prior_sample` (:78) | `instances/pgl27/pgl27_exec.v` | the spec's landing order; sample adapters live in `pgl27_exec.v` |
| `pgl27_prior_exact_family` (:87) | `instances/pgl27/pgl27_models.v` | the spec's landing order; families live in `pgl27_models.v` |
| `pgl27_prior_viewE` (:96) | `instances/pgl27/pgl27_models.v` | the link the witness needs; it is about the family, so it goes with it |
| `pgl27_prior_exact_witness` (:112) | `instances/pgl27/pgl27_models.v` | the witness of that family |
| `pgl27_row_prior_exact_tableau` (:134) | `instances/pgl27/pgl27_proximity.v` | the ideal program; a program is a row, and rows live beside rows |
| `pgl27_row_prior_exact_armE` (:144) | `instances/pgl27/pgl27_proximity.v` | K1 |
| `pgl27_row_prior_exact_rowE` (:157) | `instances/pgl27/pgl27_proximity.v` | the manifest row; it is the text landing 3 adds to the manifest |

### `p5_pgl27_word_proximity.v`

| Declaration | Lands in | Reason |
|---|---|---|
| `pgl27_word_secret` (:111) | `pgl27_proximity.v` | the secret field of the certificate |
| `pgl27_word_proximity_close` (:128) | `pgl27_proximity.v` | the distance field, one step from `pgl27_view_mixing` |
| `pgl27_word_proximity_cert` (:191) | `pgl27_proximity.v` | the certificate |
| `pgl27_word_proximity_cert_idealE` (:206) | `pgl27_proximity.v` | P3 |
| `pgl27_word_proximity_cert_epsE` (:220) | `pgl27_proximity.v` | the certificate's number, `2^-40` |
| `pgl27_word_proximity_eps_halfE` (:234) | `pgl27_proximity.v` | the advantage reading |
| `pow2_40_ge1` (:241), `pow2_40_gt0` (:245) | `pgl27_proximity.v` | premises of `pgl27_word_proximity_le39`. Rename needed, see risk R7 |
| `pgl27_word_proximity_le39` (:251) | `pgl27_proximity.v` | the `conclude` payload: `2^-40 <= 2^-39` |
| `pgl27_word_proximity_cert_eps_lt2` (:263) | `pgl27_proximity.v` | P7 ceiling |
| `pgl27_row_word_proximity` (:285) | `pgl27_proximity.v` | the new program |
| `pgl27_row_word_proximity_rowE` (:299) | `pgl27_proximity.v` | the manifest row, already held by `pgl27_row_word` |
| `pgl27_row_word_proximity_armE` (:307) | `pgl27_proximity.v` | K1 |
| `pgl27_row_word_branch39_armE` (:314) | `pgl27_proximity.v` only if its subject lands | its subject `pgl27_row_word_branch39` is defined in `t0_sampled_branch_pgl27.v`. See risk R1 |
| `pgl27_row_word_arms_sampledE` (:323), `pgl27_row_word_obs_sampledE` (:335) | same condition | they are stated at `pgl27_word_sampled`. See risk R1 |
| `pgl27_row_word_arm_neq` (:350) | same condition | the two siblings carry different arms |
| `pgl27_word_view_proximity` (:382) | `pgl27_proximity.v` | the theorem a paper cites |

### `p5_mutations.v`

| Declaration | Lands in | Reason |
|---|---|---|
| `pgl27_word_proximity_cert_unit_ideal` (`Fail`, :68) | `pgl27_proximity.v` | a recorded `Fail` lands beside the row it guards, as the rows files already do |
| `var_dist_fdist1_uniform` (:88) | `pgl27_proximity.v` | premise of `pgl27_word_uniform_ideal_not_close`. Its `first [...]` list is a header obligation, see section 5 |
| `pgl27_word_uniform_ideal_not_close` (:120) | `pgl27_proximity.v` | the spec's change 8: the refutation that fixes what is not claimed near the uniform prior |
| `pgl27_word_proximity_cert_uniform_ideal` (`Fail`, :187) | `pgl27_proximity.v` | recorded `Fail` |
| `pgl27_cross_model_proximity` (`Fail`, :205) | `pgl27_proximity.v` | recorded `Fail`, the cross-model rejection |

### `p6_psl211_word_model.v`

| Declaration | Lands in | Reason |
|---|---|---|
| `psl211_word_cutP` (:76) | `instances/psl211/psl211_word_model.v` | the cut law of the word model |
| `psl211_wordP` (:85) | same | the sample law |
| `psl211_word_sample` (:94) | same | the adapter |
| `psl211_word_sampleP_E` (:102) | same | the adapter's law, a premise of the distance field |
| `psl211_word_cut_distE` (:110) | same | the cut law is the word law; the premise that carries `psl211_word_mixing` in |
| `psl211_word_family` (:120) | same | the family the manifest row records |
| `psl211_word_lawE` (:135) | same | the family's law at the one index |

### `p6_psl211_word_proximity.v`

| Declaration | Lands in | Reason |
|---|---|---|
| `psl211_word_proximity_close` (:109) | `instances/psl211/psl211_word_proximity.v` | the distance field |
| `psl211_word_proximity_cert` (:146) | same | the certificate |
| `psl211_word_proximity_cert_idealE` (:160) | same | P3 |
| `psl211_word_proximity_cert_epsE` (:176) | same | the number, `2^-40` |
| `psl211_pow2_40_ge1` (:181), `psl211_pow2_40_gt0` (:185) | same | premises. See risk R7 |
| `psl211_word_proximity_cert_eps_lt2` (:198) | same | P7 ceiling |
| `psl211_row_word_proximity` (:229) | same | the new program |
| `psl211_row_word_proximity_armE` (:239) | same | K1 |
| `psl211_row_word_proximity_rowE` (:250) | same | the manifest row landing 4 adds |
| `psl211_word_view_proximity` (:267) | same | the theorem a paper cites |

### `p6_mutations.v`

| Declaration | Lands in | Reason |
|---|---|---|
| `psl211_word_law_le2` (:75) | `psl211_word_proximity.v` | P7 ceiling at the law itself |
| `psl211_word_law_tauto` (`Fail`, :88) | same | recorded `Fail` |
| `psl211_word_proximity_cert_pgl27_ideal` (`Fail`, :107) | same | recorded `Fail`, cross-instance rejection |
| `psl211_word_proximity_cert_secretE` (:127) | same | the spec's change 5: the certificate's secret is the real chirality bit, not a unit |
| `psl211_word_proximity_cert_secretTE` (:138) | same | the same at the type |
| `psl211_word_proximity_cert_ideal_self` (`Fail`, :155) | same | recorded `Fail`, the self-ideal rejection |

### `p7_mutations.v`

| Declaration | Lands in | Reason |
|---|---|---|
| `idealproximity_ceiling` (:87) | `five_card_proximity.v` | framework-level: stated for any algebra and any execution parameters. It sits at the instance because D2 freezes `manifest/pgg_tableau.v`'s text at the probe's, and the tree has the precedent: `instances/psl211/psl211_reading_constancy.v:73-74` says its own first two declarations are framework-level and sit at the instance |
| `five_card_reprice_inv100` (:99) | `five_card_proximity.v` | the subject of the next `Fail` |
| `kim_biased_conclude_below_false` (:107) | `five_card_proximity.v` | C2, the refutation that a number below the proved one is not merely unprovable |
| `five_card_singleton_below_threshold` (:118) | `five_card_proximity.v` | premise of the instantiation |
| `five_card_biased_proximity_at_singleton` (:127) | `five_card_proximity.v` | the proposition at one seat; the `Check` at :131 lands with it |
| the five `Fail` definitions (:141, :149, :164, :187, :202, :208, :218) | `five_card_proximity.v` | recorded `Fail`s beside the row they guard |

The `Fail` at :164, `idealproximity_tail_without_independence`, is the one
that shows the arm's mathematics is used: with the ideal witness's
independence removed, the tail does not close. It belongs beside the arm in
`manifest/pgg_tableau.v`. It cannot go there for two reasons: it is stated at
a five-card certificate, which the framework file is below, and D2 freezes
that file's text. It stays at the instance and the framework header names it.
See risk R8.

### `p8_spectral_relation.v`

| Declaration | Lands in | Reason |
|---|---|---|
| `indistinguishability_prop_cert_free` (:100) | `five_card_proximity.v` | a fact about the framework: `IndistinguishabilityPropAt cert c` does not mention `cert`, so a certificate is spent inside the tail. The spec's change 3 makes this the finding of P8 |
| `idealproximity_prop_cert_free` (`Fail`, :111) | `five_card_proximity.v` | the contrast: the proximity proposition does mention its certificate |
| `indistinguishability_cert_in_proximity_prop` (`Fail`, :120) | `five_card_proximity.v` | the same contrast from the other side |
| `idealproximity_reading_le` (:133) | `five_card_proximity.v` | framework-level: what the proximity proposition gives about readings |
| `five_card_biased_proximity_prop_holds` (:173) | `five_card_proximity.v` | instance-level |
| `five_card_biased_indistinguishability_implies_proximity` (:184) | `five_card_proximity.v` | P8's compiled half at the five-card instance |

The first four are stated inside `Section
proximity_against_indistinguishability` over `Variable R : realType`,
`Variable A : PGGAlgebraic`, `Variable E : ExecutionParams A`,
`Variable sa : SampleAdapter R (instance_exec E)`
(`p8_spectral_relation.v:83-87`), so they name no instance. Their natural home
is `manifest/pgg_tableau.v`, beside the two propositions they compare, and D2
forbids it: that file's text is the probe's audited text and lands once. They
therefore go to `five_card_proximity.v` with the section intact, and the
framework header names the file. A later batch may move them; the move is one
`cp` and one recompile of six files.

P8 is partial by the probe's own verdict. What is argued and not compiled
stays argued; the landing copies the argument into the comment of
`five_card_biased_indistinguishability_implies_proximity` and claims nothing
more, following `psl211_reading_constancy.v:697-704`, which marks its own
argued step that way.

### `p9_actual_marginals.v`

| Declaration | Lands in | Reason |
|---|---|---|
| `var_dist_own_marginals` (:65) | `lib/var_dist_supp.v` | generic in two finite types and a real field; it names no instance |
| `five_card_biased_view_own_marginals` (:98) | `five_card_proximity.v` | P9's corollary at the instance, the constant three |

### Probe instruments that do not land

`assumptions_report.v`, `assumptions_report_stageB.v`,
`assumptions_report_stageC.v`, `assumptions_report_stageD.v` are
`Print Assumptions` rolls. They are replaced by the landing's two fidelity
files (section 6), which is what the Kim landing did.

`g2_keyword_measure.v` is the G2 keyword measurement of the syntax file's
header. Its result is a sentence in the header of
`manifest/pgg_tableau_syntax.v`, which the probe's copy already carries, so
the measuring file has no further use.

`t0_sampled_branch.v` and `t0_sampled_branch_pgl27.v` are T0's evidence. I
partly disagree with D6 here: `t0_sampled_branch_pgl27.v:135` defines
`pgl27_word_sampled`, which `p5_pgl27_word_proximity.v` uses six times,
including in the definition of the landing program `pgl27_row_word_proximity`
(`p5_pgl27_word_proximity.v:285-289`). Something has to land. Risk R1 states
the three ways out.

---

## 3. Reverse closures and the compile order

Computed from the `Require` lines of every `.v` file outside `notes/`,
`_build` and `.git`, by a Python walk. The forward closure of
`instances/psl211/psl211_endpoints.v` computed the same way has 34 modules
and, with `psl211_endpoints` itself, is exactly the 35-module list of D7, so
the computation agrees with the constraint it has to respect.

| Changed file | Reverse closure among production files | In D7's forbidden list |
|---|---|---|
| `manifest/pgg_tableau.v` | `pgg_tableau_syntax`, `pgl27_rows`, `five_card_rows`, `s5_rows`, `psl211_rows`, `psl211_reading_constancy` | no |
| `manifest/pgg_tableau_syntax.v` | `pgl27_rows`, `five_card_rows`, `s5_rows`, `psl211_rows` | no |
| `instances/pgl27/pgl27_rows.v` | empty | no |
| `instances/kim2025/five_card_rows.v` | empty | no |
| `instances/s5/s5_rows.v` | empty | no |
| `instances/psl211/psl211_rows.v` | empty | no |
| `instances/psl211/psl211_reading_constancy.v` | empty | no |
| `lib/var_dist_supp.v` | `five_card_mixing`, `five_card_analysis`, `pgg_analysis_manifest`, `pgg_tableau`, `pgg_tableau_syntax`, `pgl27_rows`, `five_card_rows`, `s5_rows`, `psl211_rows`, `psl211_reading_constancy`, `pgg_analysis_client` (eleven) | no |
| `instances/kim2025/five_card_mixing.v` | `five_card_analysis`, `pgg_analysis_manifest`, `pgg_tableau`, `pgg_tableau_syntax`, `pgl27_rows`, `five_card_rows`, `s5_rows`, `psl211_rows`, `psl211_reading_constancy`, `pgg_analysis_client` (ten) | no |
| `instances/pgl27/pgl27_exec.v` | `pgl27_models`, `pgl27_analysis`, `pgg_analysis_manifest`, `pgg_tableau`, `pgg_tableau_syntax`, `pgl27_rows`, `five_card_rows`, `s5_rows`, `psl211_rows`, `psl211_reading_constancy`, `pgg_analysis_client` (eleven) | no |
| `instances/pgl27/pgl27_models.v` | the same eleven minus `pgl27_models` itself: `pgl27_analysis`, `pgg_analysis_manifest`, `pgg_tableau`, `pgg_tableau_syntax`, `pgl27_rows`, `five_card_rows`, `s5_rows`, `psl211_rows`, `psl211_reading_constancy`, `pgg_analysis_client` (ten) | no |
| `instances/pgl27/pgl27_analysis.v` | `pgg_analysis_manifest`, `pgg_tableau`, `pgg_tableau_syntax`, `pgl27_rows`, `five_card_rows`, `s5_rows`, `psl211_rows`, `psl211_reading_constancy`, `pgg_analysis_client` (nine) | no |
| `instances/psl211/psl211_analysis.v` | the same nine | no |
| `manifest/pgg_analysis_manifest.v` | `pgg_tableau`, `pgg_tableau_syntax`, `pgl27_rows`, `five_card_rows`, `s5_rows`, `psl211_rows`, `psl211_reading_constancy`, `pgg_analysis_client` (eight) | no |
| `manifest/pgg_analysis_client.v` | empty | no |
| `instances/psl211/psl211_word_model.v` (new) | empty as a file, not empty once the facade aliases its family. See risk R2 | no |
| `instances/kim2025/five_card_proximity.v` (new) | empty | no |
| `instances/pgl27/pgl27_proximity.v` (new) | empty | no |
| `instances/psl211/psl211_word_proximity.v` (new) | empty | no |

None of the files the landing edits is in the forward closure of
`psl211_endpoints`. `psl211_endpoints.v` is never compiled. Two of the files
the landing edits are *upstream* of it in the other direction and none is
downstream in the sense D7 forbids: `psl211_analysis.v` and
`psl211_reading_constancy.v` both `Require psl211_endpoints`
(`instances/psl211/psl211_analysis.v:76`), so compiling either one loads
`psl211_endpoints.vo` without rebuilding it. Risk R3 records what this costs.

### Single-file compile order

Landing 1, after `cp` of each file:

1. `manifest/pgg_tableau.v`
2. `manifest/pgg_tableau_syntax.v`
3. `instances/pgl27/pgl27_rows.v`
4. `instances/kim2025/five_card_rows.v`
5. `instances/s5/s5_rows.v`
6. `instances/psl211/psl211_rows.v`
7. `instances/psl211/psl211_reading_constancy.v` (recompiled, its text changed only in comments)

Landing 2:

1. `lib/var_dist_supp.v`
2. `instances/kim2025/five_card_mixing.v`
3. `instances/kim2025/five_card_analysis.v` (recompiled only)
4. `manifest/pgg_analysis_manifest.v` (recompiled only)
5. `manifest/pgg_tableau.v` (recompiled only)
6. `manifest/pgg_tableau_syntax.v` (recompiled only)
7. `manifest/pgg_analysis_client.v` (recompiled only)
8. `instances/pgl27/pgl27_rows.v`, `instances/kim2025/five_card_rows.v`, `instances/s5/s5_rows.v`, `instances/psl211/psl211_reading_constancy.v`, `instances/psl211/psl211_rows.v` (recompiled only)
9. `instances/kim2025/five_card_proximity.v` (new)

Landing 3:

1. `instances/pgl27/pgl27_exec.v`
2. `instances/pgl27/pgl27_models.v`
3. `instances/pgl27/pgl27_analysis.v`
4. `manifest/pgg_analysis_manifest.v`
5. `manifest/pgg_tableau.v`, `manifest/pgg_tableau_syntax.v`, `manifest/pgg_analysis_client.v` (recompiled only)
6. the five rows and constancy files (recompiled only)
7. `instances/pgl27/pgl27_proximity.v` (new)

Landing 4:

1. `instances/psl211/psl211_word_model.v` (new)
2. `instances/psl211/psl211_analysis.v`
3. `manifest/pgg_analysis_manifest.v`
4. `manifest/pgg_tableau.v`, `manifest/pgg_tableau_syntax.v` (recompiled only)
5. the five rows and constancy files (recompiled only)
6. `manifest/pgg_analysis_client.v`
7. `instances/psl211/psl211_word_proximity.v` (new)

### The four new files' import blocks

Each probe-local `Require` becomes a `pgg_smc` one; everything else in the
block is unchanged, because the probe files already import production modules
directly.

| New file | Probe-local edges to rewrite | Notable production imports it keeps |
|---|---|---|
| `instances/kim2025/five_card_proximity.v` | `pgg_tableau`, `pgg_tableau_syntax`, `p1_joint_law_distance`, `five_card_rows`, `s5_rows` | `five_card_mixing` (`p4_kim_biased_proximity.v:61`) for `kim_biased_cut_mixing_exact`, `pgg_analysis_manifest` (`:62`), `pgg_collusion_bound` (`:56`) |
| `instances/pgl27/pgl27_proximity.v` | `pgg_tableau`, `pgg_tableau_syntax`, `pgl27_rows`, `t0_sampled_branch_pgl27`, `p5_pgl27_prior_ideal` | the PGL(2,7) cone the rows file already brings |
| `instances/psl211/psl211_word_model.v` | `p1_joint_law_distance` only | `psl211_mixing` for `psl211_word_mixing`, `psl211_alldecks` for the carrier |
| `instances/psl211/psl211_word_proximity.v` | `pgg_tableau`, `pgg_tableau_syntax`, `psl211_rows`, `p1_joint_law_distance`, `p6_psl211_word_model` | the PSL(2,11) cone the rows file already brings |

`p1_joint_law_distance` resolves to `var_dist_supp` after landing 2, for the
three lemmas that land there. `t0_sampled_branch_pgl27` resolves to
`pgl27_rows` under R1's option (a), which is why that option keeps the import
block shortest.

The `s5_rows` edge of `p7_mutations.v:64` exists only for the cross-instance
rejection `kim_biased_cert_s5_ideal` (`p7_mutations.v:187`). It makes
`five_card_proximity.v` import `s5_rows.v`, which is a leaf today. Keeping the
rejection is worth the edge: it is the compiled evidence that a certificate
naming another instance's exact family is rejected by the types, which is half
of ledger row P7.

### The two PGL(2,7) edits, precisely

`instances/pgl27/pgl27_exec.v` gains one definition, `pgl27_prior_sample`,
the text of `p5_pgl27_prior_ideal.v:78-85`. It is a `SampleAdapter` over the
PGL(2,7) execution whose law is `pgl27P_gen secretP`. The file already holds
the instance's sample adapters and already `Require`s `pgg_sample_adapter`
and `pgl27_word_privacy` (both in its direct `Require` list), so the addition
needs no new import. Placement: beside the file's existing adapters, at the
end of the adapter section. Needs a compile to confirm no import is missing.

`instances/pgl27/pgl27_models.v` gains three declarations, the text of
`p5_pgl27_prior_ideal.v:87-132`: `pgl27_prior_exact_family` (an
`AnalysisModelFamily pgl27_observed` indexed by `R.-fdist bool`),
`pgl27_prior_viewE` and `pgl27_prior_exact_witness`. The file already holds
`pgl27_exact_family` at `:410` and `pgl27_word_family` at `:417` by the spec's
"Cited objects" table, so the three go after `:417`, in the same section.
`pgl27_models.v` already `Require`s `pgl27_exec`, which is where
`pgl27_prior_sample` will live.

---

## 4. Files re-read because the framework changes under them

These files are not copies of probe files. They are read sentence by sentence
because landing 1 changes the meaning of `conclude` under them.

### `instances/psl211/psl211_reading_constancy.v`

Production's `conclude` obligation is an equality today. Landing 1 makes it
`<=`. Every sentence in this file that reasons from the obligation has to be
re-read. The file has 1018 lines and its reverse closure is empty, so the
change costs one recompile and no further file.

| Line | Sentence | Verdict after the `<=` change |
|---|---|---|
| `:35-38` | "The obligation of conclude bounds the published number below by cert_eps cert, which is that epsilon twice, so every row over this model that publishes its certificate's own number publishes at least 1/660." | Stays true. `<=` bounds the published number below by `cert_eps cert` exactly as the equality did. The word "bounds below" was already written for the weaker obligation |
| `:688-693` | "A row publishes odflt (cert_eps cert) (c R) at its own reprice coordinate c, and cert_eps cert is the shuffle bound epsilon twice, so a row over this model that publishes its certificate's own number publishes at least 1/660. The obligation of conclude bounds the published number below by cert_eps cert, so no row over this model publishes less." | Stays true, and the word "reprice" is now the wrong name. `RepricePayload` and `port_reprice` become `ConcludePayload` and `port_conclude` in landing 1 (the spec's change 11), so "its own reprice coordinate c" must become "its own conclude coordinate c" |
| `:697-701` | "Argued and not compiled: the proposition a row carries is IndistinguishabilityPropAt cert c, a variation distance bounded above by c, so an obligation weakened from an equality to cert_eps cert <= odflt (cert_eps cert) (c R) could only let a row publish a number no smaller than cert_eps." | Becomes stale as a hypothetical. The weakening it anticipates is exactly what landing 1 performs, so the block is rewritten from "Argued and not compiled: an obligation weakened from …" to a statement of the obligation as it now is. The mathematics is unchanged |
| `:54-55` | "The input-indistinguishability arm is not shown unavailable at this instance." | Stays true |
| `:67-69` | "Nothing here says the word row is excluded outright: psl211_alldecks_constancy_false_word584 reaches eps < 1/1320 - 2^-40, and no weighted-word sample adapter exists for this instance." | The final clause becomes FALSE at landing 4. `psl211_word_sample` is a weighted-word sample adapter for this instance |
| `:768-771` | "It is stated on the cut law rather than on a certificate because no weighted-word SampleAdapter exists in this tree, so there is no adapter whose cut is this law and no ic_Hd through which a certificate's ideal could be held near it." | This is the comment of `psl211_alldecks_constancy_false_word584` (`instances/psl211/psl211_reading_constancy.v:772`). Its stated reason becomes false at landing 4. See section 5 |
| `:31-34` | "The quantitative form fixes what an input-indistinguishability row would have to publish. A certificate over the all-decks model states its distance against the group-uniform law, its identification field pinning its shuffle law to the adapter's cut, so no certificate carries a shuffle bound epsilon strictly below 1/1320." | Stays true. It is about `IndistinguishabilityCert` and says nothing about `IdealProximityCert`. A sentence should be added saying the exclusion covers one arm only, because landing 4 gives this instance a row at the other arm publishing `2^-40` |
| `:14-15` | "publishes its all-decks row through the exact arm, and this file is what the input-indistinguishability arm would cost it." | Stays true, and a reader now needs the third arm named. The header gains a sentence pointing at `psl211_word_proximity.v` |
| `:202`, `:208`, `:674`, `:706`, `:725` | statements at `IndistinguishabilityCert` | unchanged by the `<=` weakening; they quantify over certificates, not over rows |
| `:560` | "at this fixed deal, which is not the law the row is about" | stays true |

### Production-only passages of the four rows files

Landing 1 replaces all four files wholesale with the probe's copies, so every
sentence of production that the `<=` obligation makes false is already
rewritten in text the probe's audits read. The list below is the evidence that
no such sentence was missed. It is every line of the four production rows
files that mentions the obligation, the reprice or an identity, and that does
not occur in the probe's copy of the same file.

| Production line | What it says that the `<=` obligation makes false or stale |
|---|---|
| `pgl27_rows.v:55` | index entry, "the word row republished at that name". "Republished" is the old vocabulary for a terminal that now publishes an upper bound |
| `pgl27_rows.v:376-379` | "The word row with its bound republished as the single constant 2^-39. The accumulated bound is 2^-40 twice, and the identity that adds the two copies… the republished row asserts exactly what the row above asserts, at the number a…". "Exactly what the row above asserts" is the equality obligation speaking. Under `<=` the republished row asserts a weaker statement whenever the payload is a strict inequality; here it is not, so the row's own content is unchanged and only the sentence is |
| `pgl27_rows.v:385` | the payload `(fun R _ => pow2_split R)`, an identity. Under `<=` it is wrapped in `eqW`, which is the spec's landing-order item for this file |
| `pgl27_rows.v:388-390` | "The reprice obligation is one identity per real field and per index of the family, and pow2_split alone is an identity at one field. Supplying it bare is rejected, which is what keeps a row from republishing a bound that holds…". The first clause is false: the obligation is one inequality. The recorded `Fail` at `:392-396` still fails, for the arity reason and not the identity reason, so the comment must say arity |
| `pgl27_rows.v:153` | "as an equality of functions". Unrelated to the terminal; stays |
| `five_card_rows.v:42,102,108,158,160` | index and header entries using "reprice" and "republish" |
| `five_card_rows.v:671,684` | "identity is what names that sum by a single constant", "before any reprice names it by a constant" |
| `five_card_rows.v:757-758` | "The repriced row republished at that constant. The reprice supplies the identity five_card_pow2_39_split and changes nothing else" |
| `five_card_rows.v:766` | the payload, an identity; the probe's route is `ltW (kim_centi_cert_eps_lt R idx)` instead, and the number published is unchanged at `2^-39` |
| `five_card_rows.v:769-771` | "The reprice obligation is one identity per real field and per index"; false under `<=`, and the recorded `Fail` at `:772-778` now fails for arity |
| `five_card_rows.v:800,809,823` | the one-cut row at one twenty-fifth, the same vocabulary |
| `s5_rows.v` | no such line. The S5 rows carry no terminal that moves a number |
| `psl211_rows.v` | no such line |

Every one of these is inside a file landing 1 replaces, and the probe's copies
do not contain them, which is how the list was built. What must still be
checked at the landing, and what the landing-fidelity file checks, is that no
sentence of the probe's copy is stale against production the other way round:
the probe's copies were refreshed to production's new names on 2026-09-19
(commits `bf42b4d`, `7bae082`, `dc1321e`, `819461d`) and are uncommitted in
the working tree. The diff counts in section 1 are against production as it
stands at `819461d`.

### `manifest/pgg_analysis_client.v`

`manifest/pgg_analysis_client.v:7` says the file reaches "the nine typed
rows". Landing 3 and landing 4 add one row each, so that count becomes eleven
and the sentence is false in between. The file has exactly one `Require`
(`:16`) and its reverse closure is empty, so the fix is local.

What the client gains: `Check PGL27Analysis.prior_exact_family.` beside
`:27-28`, and `Check PSL211Analysis.word_family.` beside `:79`. Both are bare
`Check`s on aliases, which is the rule the file's own header states at `:8-10`.
The client is compiled last in landings 3 and 4, as
`docs/superpowers/plans/2026-09-19-kim-spectral-landing.md` put it in its
twelve-file order.

---

## 5. Header-text obligations

### `manifest/pgg_tableau.v`: the counts

The probe's copy already carries the rewritten header. The sentences that
change, by production line:

| Production | Probe replacement |
|---|---|
| `:17` "There are five statements." | "There are six statements." |
| `:22-31` "certify_exact and certify_indistinguishability adjoin a security witness of one of the two arms. Both arms speak only of a coalition below the privacy threshold, and they are not comparable statements…" | "certify_exact, certify_indistinguishability and certify_idealproximity adjoin a security witness of one arm. Each arm speaks only of a coalition below the privacy threshold, and the arms are not comparable statements…", with the proximity arm's conclusion spelled out and `security_arm_of` named |
| `:33-40` "Each arm has one composition law, and the two laws are where the mathematics of the row sits." | "Each arm has one composition law, and those laws are where the mathematics of the row sits.", plus the sentence for `idealproximity_tail` |
| `:41-48` "The mathematics of a particular instance never appears as a line: it enters only as the witness or the certificate a certify statement takes… it leaves the data and the arms untouched and moves only the real the input-indistinguishability arm's proposition mentions." | "…it enters as the witness or the certificate a certify statement takes, and once more as the payload of conclude, which for an input-indistinguishability or a proximity port is an inequality between the number the row's own certificate proved and the number the row publishes and for an exact port is nothing… and moves the real an arm's proposition mentions to any upper bound of it." |
| the `Definitions:` block at `:50` onward | gains `IdealProximityCert`, `SecurityArm`, `port_arm`, `certify_idealproximity`, and `conclude`'s entry is rewritten to "the terminal publishing an upper bound of the accumulated bound" |

One sentence the probe's header does not carry and the spec's change 5
requires: a certificate is as meaningful as its ideal and its secret. An ideal
that is the actual model with a unit secret makes the proposition true at zero
and says nothing. `SpectralCert`'s `sc_ideal` and `ExactWitness`'s secret have
the same freedom in production today, so the new arm adds none. A search of
the probe's `pgg_tableau.v` for that content finds nothing, so the landing
writes it. See risk R15.

The rename that comes with the `<=` obligation is not confined to the
framework file. `RepricePayload` (`manifest/pgg_tableau.v:633`, `Arguments` at
`:640`) becomes `ConcludePayload`, and `port_reprice` (`:646`, `Arguments` at
`:657`) becomes `port_conclude`. Both are read by `conclude` itself
(`:663-668`). `conclude` is an existing terminal, used at
`instances/pgl27/pgl27_rows.v:385,396` and
`instances/kim2025/five_card_rows.v:766,777,809`, so landing 1 weakens an
obligation and does not add a terminal. The type `Reprice` keeps its name in
the probe. See risk R13.

### `instances/psl211/psl211_reading_constancy.v:768-771`

The current comment of `psl211_alldecks_constancy_false_word584`
(`instances/psl211/psl211_reading_constancy.v:772`) reads, verbatim:

> It is stated on the cut law rather than on a certificate because no
> weighted-word SampleAdapter exists in this tree, so there is no adapter
> whose cut is this law and no ic_Hd through which a certificate's ideal
> could be held near it.

What is false in it after landing 4: the clause "no weighted-word
SampleAdapter exists in this tree". `psl211_word_sample`
(`notes/probes/2026-09-19-tableau-extensions/p6_psl211_word_model.v:94`) is
one, its cut law is exactly this law by `psl211_word_cut_distE` (`:110`), and
`psl211_word_family` (`:120`) is built over it. The consequent clauses
"there is no adapter whose cut is this law" and "no ic_Hd through which a
certificate's ideal could be held near it" become false with it.

The replacement has to keep the lemma's actual scope, which the landing does
not change. The lemma is stated on a cut law and quantifies over an `ideal`
and an `eps`. The honest new reason is that the statement is about any law
within `eps` of the word cut, so it covers every certificate's ideal at once
and does not need an adapter to name one. And the refutation and the new row
do not contradict each other: the refutation is about the constancy field of
`IndistinguishabilityCert`, the new row publishes a proximity bound, and those
are two propositions.

`:67-69` of the same file carries the same false clause and is rewritten with
it.

### `var_dist_fdist1_uniform`'s `first [...]` list

`notes/probes/2026-09-19-tableau-extensions/p5_mutations.v:98-100`:

```
have Hf : (fdist1 true : R.-fdist bool) false = 0.
  by first [by rewrite fdist1E | by rewrite fdist1E /= mul0rn
           | by rewrite fdist1E mul0rn | by rewrite fdist1E /=].
```

A `first [...]` of four spellings of one rewrite is a prover hedging against
an unknown reduction. Exactly one branch fires. Before the lemma lands in
`instances/pgl27/pgl27_proximity.v`, the landing determines which one and
replaces the list with it. That is a one-line edit and one compile. Needs a
compile: I cannot tell from the source which branch fires.

### `manifest/pgg_tableau_syntax.v`

The probe's copy carries the G2 keyword measurement for the two new words,
`conclude` and `IdealProximity`, which the spec records as costing no keyword.
That sentence lands with the file.

---

## 6. The two fidelity instruments

Imitating `notes/probes/2026-09-19-kim-spectral-landing/kim_landing_fidelity.v`
and `kim_asbuilt_fidelity.v`, in a new landing probe directory
`notes/probes/2026-09-20-tableau-extensions-landing/` with logical path
`tableau_ext_landing`.

### `landing_fidelity.v` — the staged text against the probe's statements

`Require`s the staged copies through `tableau_ext_landing`, not through
`pgg_smc`. It checks, for each landing:

1. **Row equations.** `published_row pgl27_row_prior_exact_tableau` and
   `published_row psl211_row_word_proximity` restated and proved by the
   staged files' own `_rowE` lemmas, so the manifest rows drafted in section 7
   are checked against the programs rather than typed twice.
2. **Arm pins.** One restatement of `security_arm_of <row> = <arm>` per
   program the landing adds, proved by the staged `_armE` lemma. This is what
   makes the arm reader's answer part of the landing's evidence.
3. **Published numbers.** One restatement per row of the number it publishes
   (one fiftieth at five-card, `2^-39` at PGL(2,7), `2^-40` at PSL(2,11)) and
   one restatement of each `_eps_lt2` ceiling lemma, so that no row publishes a
   number a pair of laws cannot exceed.
4. **The withdrawal.** A `Fail`-guarded mention of `kim_centi_cert40` proving
   that the name is gone from the staged tree, and a restatement of
   `five_card_row_repeated39`'s published number showing it is still `2^-39`
   on the `ltW` route.
5. **The library move.** A restatement of `card_tnth_count` proved from
   `five_card_mixing`, and of `var_dist_prodR` and `fdist_prod_snd` proved
   from `var_dist_supp`, so the move and the promotion are both witnessed at
   their new homes.
6. **`Print Assumptions`** on every declaration the landing adds or moves,
   grouped under one banner per source file, as the Kim file does. The pass
   criterion is the three `boolp` axioms or closed, except the S5 row, which
   rests on the production `Axiom s5_group_order_eq` as it did before.

### `asbuilt_fidelity.v` — production after the `cp`

The same targets, `Require`d through `pgg_smc` only, compiled with the
production `_CoqProject` flags and with the landing probe mapped to no logical
root on that command line, so no staged copy is reachable by any `Require`. It
adds `Locate` sentences on `idealproximity_tail`, `security_arm_of`,
`var_dist_prodR`, `card_tnth_count`, `pgl27_prior_exact_family` and
`psl211_word_family`, which print the full names the constants carry under
`pgg_smc`. `Locate Library` does not witness which file a `Require` picked and
is not used, which is the trap the Kim landing's record names.

One `asbuilt_fidelity.v` per landing, or one file grown at each landing. One
grown file is better: it makes landing 4's run re-check landing 1's targets.

---

## 7. The two manifest rows

`manifest/pgg_analysis_manifest.v:776` declares
`Record AnalysisPathRow := MkAnalysisPathRow { ... }`. Existing rows are
stated in the facade vocabulary, for instance `:803-805`:

```
Definition pgl27_row_exact : AnalysisPathRow :=
  @MkAnalysisPathRow PGL27Analysis.observed AnalysisBridged
    PGL27Analysis.exact_family StaticExecutedOnly BaselineClassicalOnly.
```

and `:911-913`:

```
Definition psl211_row_alldecks : AnalysisPathRow :=
  @MkAnalysisPathRow PSL211Analysis.observed AnalysisBridged
    PSL211Analysis.exact_family StaticExecutedOnly BaselineClassicalOnly.
```

The probe states the two new rows at the raw family names. Verbatim, from
`notes/probes/2026-09-19-tableau-extensions/p5_pgl27_prior_ideal.v:157-160`:

```
Lemma pgl27_row_prior_exact_rowE :
  published_row pgl27_row_prior_exact_tableau
  = @MkAnalysisPathRow pgl27_observed AnalysisBridged
      pgl27_prior_exact_family StaticExecutedOnly BaselineClassicalOnly.
Proof. exact: erefl. Qed.
```

and from
`notes/probes/2026-09-19-tableau-extensions/p6_psl211_word_proximity.v:250-256`:

```
Lemma psl211_row_word_proximity_rowE :
  published_row psl211_row_word_proximity
  = @MkAnalysisPathRow psl211_alldecks_observed AnalysisBridged
      psl211_word_family IdealFinite BaselineClassicalOnly.
Proof. exact: erefl. Qed.
```

So the two manifest rows, in the manifest's own vocabulary:

```
Definition pgl27_row_prior_exact : AnalysisPathRow :=
  @MkAnalysisPathRow PGL27Analysis.observed AnalysisBridged
    PGL27Analysis.prior_exact_family StaticExecutedOnly BaselineClassicalOnly.

Definition psl211_row_word : AnalysisPathRow :=
  @MkAnalysisPathRow PSL211Analysis.observed AnalysisBridged
    PSL211Analysis.word_family IdealFinite BaselineClassicalOnly.
```

Fields, read off the two row equations and nothing else:

| Field | PGL(2,7) prior-indexed exact row | PSL(2,11) word row |
|---|---|---|
| observed | `PGL27Analysis.observed` (`= pgl27_observed`, `instances/pgl27/pgl27_analysis.v:153`) | `PSL211Analysis.observed` (`= psl211_alldecks_observed`, `instances/psl211/psl211_analysis.v:116`) |
| completion level | `AnalysisBridged` | `AnalysisBridged` |
| model family | `PGL27Analysis.prior_exact_family`, new alias of `pgl27_prior_exact_family` | `PSL211Analysis.word_family`, new alias of `psl211_word_family` |
| transfer status | `StaticExecutedOnly` | `IdealFinite` |
| assumption status | `BaselineClassicalOnly` | `BaselineClassicalOnly` |

The two transfer statuses are the row equations', not a choice. The PGL(2,7)
ideal row is `StaticExecutedOnly` because it compares no model with another:
its comment at `p5_pgl27_prior_ideal.v:130-133` says the row carries
independence of the dealt secret at every real field and prior, with no
numeric bound anywhere in it. The PSL(2,11) word row is `IdealFinite` because
an idealised shuffle is replaced by one of 584 letters
(`p6_psl211_word_proximity.v:225-228`).

### The two comment blocks

The manifest carries nine numbered row tables, Row 1 at `:89` through Row 9 at
`:629`. The two new rows are Row 10 (PGL(2,7), prior-indexed exact) and Row 11
(PSL(2,11), word). Each table has the fields of Row 9's
(`manifest/pgg_analysis_manifest.v:631-669`): protocol family and model,
profile alias, execution alias, observed alias, sample alias, observers with
their carriers, distribution-to-observer bridges, bound or certificate, final
bridge theorem, correctness theorem, model transfer, missing premise,
completion level, transfer status, assumption status, typed row; followed by
the capabilities table, one line per theorem with its distribution, its
observer and its notion.

Two fields need care, because they are where the new arm shows in the
manifest.

**Row 10, model transfer.** "none claimed", and the missing-premise field
says why: the row is the ideal of a comparison and compares nothing itself.
Its final bridge theorem is the exact arm's, at `pgl27_prior_exact_witness`.
Its sample alias is `PGL27Analysis.prior_sample`, if the facade aliases the
adapter too, otherwise the field names `pgl27_prior_sample` by file.

**Row 11, model transfer and bound.** The transfer is an idealised shuffle
replaced by one of 584 letters and the bound is `2^-40`, in the sum of
absolute differences, which is the field `psl211_word_proximity_close` proves.
The missing-premise field is "none": the row's certificate carries its own
distance. The final bridge theorem is `psl211_word_view_proximity`. The
capabilities line reads: theorem `psl211_word_view_proximity`, distribution
the law of `psl211_word_sample`, observer `sa_coalition_view` at a coalition
of at most five of the twelve seats, notion proximity to a private ideal
model. This is the manifest's first row at the new arm, so the file header's
description of what a row records (`:9-16`) gains the arm as a field a reader
reads off the program and not off the row, which is the design's own decision
(`notes/20260919-tableau-three-extensions-probe-design.md:99-103`).

Both rows also need three `Check` pins each, in the style of `:1917-1923`:
one `Check (<row> : AnalysisPathRow)`, one
`Check (erefl : apr_transfer <row> = <status>)`, one
`Check (erefl : apr_assumptions <row> = BaselineClassicalOnly)`.

Assumptions: both rows are `BaselineClassicalOnly`, which the manifest's
convention at `:49` ties to `Print Assumptions` reporting the classical trio.
The fidelity files' `Print Assumptions` run is what establishes it. Needs a
compile.

---

## 8. Risks

**R1. `pgl27_word_sampled` is in a probe instrument that D6 does not land.**
`p5_pgl27_word_proximity.v:285-289` defines the landing program
`pgl27_row_word_proximity` as a continuation of `pgl27_word_sampled`, and
`pgl27_word_sampled` is defined at
`notes/probes/2026-09-19-tableau-extensions/t0_sampled_branch_pgl27.v:135-136`
as `pgl27_dealt sample pgl27_word_family`. Four further declarations of
`p5_pgl27_word_proximity.v` (`:314`, `:323`, `:335`, `:350`) are stated at
`pgl27_word_sampled` or at `pgl27_row_word_branch39`, which is also
`t0_sampled_branch_pgl27.v`'s (`:148`). Three ways out. (a) Land
`pgl27_word_sampled` and `pgl27_row_word_branch39` into
`instances/pgl27/pgl27_rows.v` in landing 1, which is where `pgl27_dealt` is
(18 occurrences in the rows file) and which is also the natural home of a
named `Tableau Sampled` value. (b) Land them into
`instances/pgl27/pgl27_proximity.v` in landing 3. (c) Inline the sample step
in `pgl27_row_word_proximity` and drop the four sibling lemmas. (a) is best:
the probe's own proof-engineering note says each row stated against the named
`Tableau Sampled` value costs under 0.01 s where row-against-row equations
cost 48 to 96 s, so the named value is worth having in the rows file for every
later row. (c) loses `pgl27_row_word_arm_neq`, the lemma that shows two claims
about one model are two rows, which is the design's own point.
`five_card_rows.v` has the same shape: `five_card_uniform_sampled` is at
`t0_sampled_branch.v:73`, but `p4_kim_biased_proximity.v` does not import
`t0_sampled_branch.v`, so the five-card side is clear.

**R2. `instances/psl211/psl211_word_model.v` does not have an empty reverse
closure once the manifest row lands.** The spec's landing order says "a new
`instances/psl211/psl211_word_model.v` with an empty reverse closure"
(`notes/20260919-tableau-three-extensions-probe-design.md:419-420`). That
holds for the file alone. But `manifest/pgg_analysis_manifest.v` `Require`s
only the four `*_analysis` facades, and `instances/psl211/psl211_analysis.v`
brings `psl211_models` in with `Require Import`, not `Require Export`
(`:77`), so the manifest cannot see `psl211_word_family` unqualified. For the
manifest row of section 7 to exist, `psl211_analysis.v` must `Require` the new
file and alias its family, and the reverse closure of `psl211_word_model.v`
then becomes the nine files of `psl211_analysis.v`'s. The same holds at
PGL(2,7) for `pgl27_prior_exact_family`, which is why landing 3's table has a
`pgl27_analysis.v` row the spec does not list. Alternative: state the manifest
rows at a qualified name, `psl211_word_model.psl211_word_family`. That breaks
the manifest's convention that every row is in facade vocabulary and the
client's convention that every alias is reachable by one import, so the facade
route is the right one. Either way the spec's sentence is wrong and the note
supersedes it.

**R3. `psl211_endpoints.vo` is older than `psl211_endpoints.v`, and three
files the landing compiles load it.** Measured on disk:
`instances/psl211/psl211_endpoints.v` has mtime 2026-09-18 16:10:53 and
`instances/psl211/psl211_endpoints.vo` has mtime 2026-09-17 16:32:24. The
compiled object predates the source by a day. Three production files `Require`
it: `instances/psl211/psl211_analysis.v:76`,
`instances/psl211/psl211_models.v:154`,
`instances/psl211/psl211_reading_constancy.v:148`. All three are compiled by
this landing: the analysis facade at landing 4, the constancy file at landings
1 and 2, and `psl211_models.v` at every landing that recompiles the manifest's
reverse closure.

This does not violate D7 by itself. `coqc` loads a `.vo` by its dependency
digest and not by its timestamp, so a single-file compile of a dependant loads
the stale object and does not rebuild `psl211_endpoints.v`. The Kim landing
recorded the same situation and the same outcome. What it forbids absolutely
is `make`: `coq_makefile` compares timestamps, so any `make` touching this
subtree rebuilds `psl211_endpoints.v`, which D7 bans. D7 already requires
single-file compiles; this measurement is why.

Two further consequences. The `.vo` in the tree may not be the compilation of
the `.v` in the tree, so a declaration this landing reads from
`psl211_endpoints` through `psl211_models.v` or `psl211_analysis.v` is the
older one. The landing names no such declaration, so nothing here depends on
which. And the state is pre-existing, not created by this landing: it was
already so at the Kim landing on 2026-09-19. The landing records it and does
not fix it.

**R4. `manifest/pgg_analysis_manifest.v` is edited twice, in landing 3 and
landing 4.** Each edit recompiles the manifest and rewrites its `.vo`, and
everything in its eight-file reverse closure has to be recompiled after each.
The Kim landing's plan step 0 makes waiting for the Rocq lock an explicit
step for this reason. Landing 3 and landing 4 must not run at the same time as
any other session compiling against the manifest.

**R5. Two `Local` copies of `var_dist_prodR`, and retiring them is expensive.**
The spec's landing order says "two `Local` copies of `var_dist_prodR` stay or
are retired" (`notes/20260919-tableau-three-extensions-probe-design.md:415-416`).
They are `instances/pgl27/pgl27_mixing.v:1077-1088` and
`instances/psl211/psl211_mixing.v:577-588`, identical in statement, proof and
preceding comment, and identical to the probe's `p1_joint_law_distance.v:84`
up to the section variable `R`. Each has exactly one use:
`pgl27_mixing.v:1100` and `psl211_mixing.v:601`, both inside the file's own
`*_joint_mixing`.

Retiring the PGL(2,7) copy means editing `instances/pgl27/pgl27_mixing.v`,
whose reverse closure among production files is twenty-one files, including
the whole PGL(2,7) encoding and leakage subtree. That is a larger recompile
than the rest of landing 2 put together. The PSL(2,11) copy's reverse closure
is one file, `psl211_reading_constancy.v`.

Decision: leave both. They are `Local`, so they are invisible outside their
files, no note or paper claims them, and the permanence rule does not reach
them. The landing records in `lib/var_dist_supp.v`'s comment on
`var_dist_prodR` that two section-local proofs of the same statement predate
it, so a later reader does not take the duplication for an oversight. Retiring
them is its own batch with its own reverse closure.

**R6. `var_dist_prodL` and `fdist_uniform_prod` have no user in the landing.**
`p1_joint_law_distance.v:100` and `:122`. D6 keeps them in the probe. If a
later batch needs them, the plan is to redefine them in their permanent home,
not to import the probe, which is the rule scratch files carry everywhere.
Flagging them because the spec's ledger row P1 names only three lemmas
(`var_dist_fdistmap_pair`, `var_dist_prodR`, `fdist_prod_snd`) and the file
holds five, so a reader of the spec would not expect a choice here.

**R7. `pow2_40_ge1` and `pow2_40_gt0` are declared twice in the probe under
two naming schemes.** `p5_pgl27_word_proximity.v:241,245` declares them
unqualified and global, in no section;
`p6_psl211_word_proximity.v:181,185` declares the same two facts as
`psl211_pow2_40_ge1` and `psl211_pow2_40_gt0`. A whole-tree scan finds neither
pair in production, so there is no collision with existing code; the collision
is between the two landings. If both land as written, the tree holds two
proofs of one statement about the real field, one of them under a name that
claims a PSL(2,11) instance for a fact about powers of two.

The fix: promote one pair, at `(1:R) <= 2%:R^+40` and `(0:R) < 2%:R^+40`, into
`lib/var_dist_supp.v` in landing 2, and have landings 3 and 4 both use it. The
alternative, prefixing the PGL(2,7) pair `pgl27_`, keeps the landings
independent but leaves the duplication. Promotion is right here, because
neither statement mentions an instance and the naming rule puts the carrier
qualifier last only when there is a carrier to name.

Related, and not a collision: `pow2_split` does exist in production, at
`instances/pgl27/pgl27_word_privacy.v:181` and used at
`instances/pgl27/pgl27_rows.v:378,385,389,396,428` and
`instances/pgl27/pgl27_models.v:400`. The probe's
`pgl27_row_word_branch39` uses it through `ssr_ext.eqW (pow2_split R)`
(`t0_sampled_branch_pgl27.v:151`), so R1's option (a) needs no new lemma.

**R8. Six framework-level declarations end up at an instance, because D2
freezes the framework file's text.** `p7_mutations.v:87`
(`idealproximity_ceiling`) and the four declarations of
`p8_spectral_relation.v:100-133` are stated over `Variable A : PGGAlgebraic`,
`Variable E : ExecutionParams A`, `Variable sa : SampleAdapter R (instance_exec
E)` and name no instance. Their home is `manifest/pgg_tableau.v`. D1 says the
permanent text is the probe's audited text and D2 says the framework files
land once carrying it, so adding them means writing text into that file that
no audit read, or a second landing of it. Both are worse than the placement,
so they go to `instances/kim2025/five_card_proximity.v` with their sections
intact and the framework header names the file.
`p7_mutations.v:164` (`idealproximity_tail_without_independence`) is the sixth
and has a second reason to sit there: it is stated at a five-card certificate,
which `pgg_tableau.v` is below.

The cost is that a reader of `manifest/pgg_tableau.v` who wants to know
whether the arm's independence premise is load-bearing has to follow a pointer
into an instance file. The tree already accepts this shape at
`instances/psl211/psl211_reading_constancy.v:73-74`, which says its own first
two declarations are framework-level and sit at the instance. A later batch
that reopens `pgg_tableau.v` should move all six.

**R9. The probe's rows-file copies are uncommitted working-tree text.** `git
status` at the start of this session lists all fifteen of the probe's `.v`
files as modified. The refresh to production's new names (`bf42b4d` through
`819461d`) was applied to the probe copies but not committed. A landing that
reads the working tree reads text no commit holds. Commit the probe refresh
before landing 1, so that the `git archive` export the audits read is
reproducible.

**R10. `five_card_proximity.v` must `Require` `five_card_rows.v`.**
`p4_kim_biased_proximity.v` imports the probe's `five_card_rows`. In
production that becomes `From pgg_smc Require Import five_card_rows`.
`five_card_rows.v`'s reverse closure is empty today, so the new file becomes
its first reverse-dependant and the rows file stops being a leaf. The same
holds for `pgl27_proximity.v` against `pgl27_rows.v` and
`psl211_word_proximity.v` against `psl211_rows.v`. No cycle: the rows files
`Require` no instance-level proximity file. But D4 says the new rows files
have "empty reverse closures", which is true of them and not of the files they
import, and a later batch reorganizing rows into per-instance `tableau/`
directories has to know that the rows files are no longer leaves.

**R11. `card_tnth_count`'s move is clean.** It is `lib/var_dist_supp.v:166`.
`instances/kim2025/five_card_mixing.v:279` is its only call site anywhere in
the tree, which a whole-repository scan confirms. `five_card_mixing.v`
`Require`s `var_dist_supp` directly, so the import edge already points the
right way and the move creates no cycle and no unresolved name. Recorded as a
risk only because D5 asserts the sole-user claim and it is now measured rather
than assumed.

**R12. The manifest's own PSL(2,11) comment block may contradict landing 4.**
`manifest/pgg_analysis_manifest.v` holds a PSL(2,11) row table whose text I
have not read in full. The PSL(2,11) reading-constancy landing's own record
says a hit in the manifest was reported and not edited, because the Kim
landing owned that file that week. Landing 4 owns it, so the manifest's
PSL(2,11) block has to be read in full at that landing and any sentence saying
this instance has one model or one row corrected.

**R13. The `RepricePayload` rename touches a live `conclude` and its two
existing call sites.** Production has `RepricePayload` at
`manifest/pgg_tableau.v:633` with `Arguments` at `:640`, `port_reprice` at
`:646` with `Arguments` at `:657`, and `conclude` at `:663`, whose payload
parameter is typed `RepricePayload c q` (`:664`) and whose body calls
`port_reprice` (`:668`). `conclude` itself is not a new name: it exists and is
used at `instances/pgl27/pgl27_rows.v:385,396` and
`instances/kim2025/five_card_rows.v:766,777,809`. So landing 1 is not adding a
terminal; it is weakening an existing terminal's obligation and renaming the
two declarations that carry it. Two file-crossing consequences. The comments
of `instances/psl211/psl211_reading_constancy.v:689` and `:692` speak of "its
own reprice coordinate" and of "the obligation of conclude", so the rename
reaches that file as well as the ones the probe copies. And `Reprice` itself,
the type of the coordinate, is not renamed by the probe, so after landing 1
the tree holds `ConcludePayload`, `port_conclude` and `Reprice` together. That
is a synonym drift within one concept. Either `Reprice` is renamed too, which
widens landing 1, or the framework header says in one sentence why the type
keeps the older name. The probe chose neither; the landing must choose.

**R14. A stale git worktree under `.claude/worktrees/` duplicates production
files and will pollute any scan or export.**
`.claude/worktrees/agent-aa400558bc3410a7b/` is an untracked worktree at
commit `b7f39a4`, an ancestor of the current `819461d`. It holds its own
`manifest/pgg_view_lift.v`, the pre-rename name of `pgg_tableau.v`, and its
own `pgl27_mixing.v`, `pgl27_rows.v` and others, which duplicate hits for
`var_dist_prodR`, `RepricePayload`, `port_reprice`, `conclude` and
`pgl27_row_word39`. Every scan in this note excluded it. Two things follow.
The `git archive` export the landing audits read must be taken from the commit
and not from the working tree, so the worktree cannot reach an auditor. And
the worktree should be removed before the landing, because a scan that
silently includes it reports a name as present in production when it is
present only in a month-old checkout. It appears in `git status` as the
untracked `.claude/worktrees/` entry.

---

**R15. One header sentence the landing must write itself, which no audit
read.** The spec's change 5 requires the framework header to say that a
certificate is as meaningful as its ideal and its secret, that an ideal which
is the actual model with a unit secret makes the proposition true at zero and
says nothing, and that `SpectralCert`'s `sc_ideal` and `ExactWitness`'s secret
have the same freedom in production today so the new arm adds none. A search
of the probe's `pgg_tableau.v` for that content finds nothing. Every other
header change of landing 1 is text an audit read; this sentence is not. It has
to be written at the landing and it is the one piece of landing-1 prose the
soundness audit reads for the first time. The compiled evidence behind it is
`psl211_word_proximity_cert_secretE` and `psl211_word_proximity_cert_secretTE`
(`p6_mutations.v:127,138`), which the header should cite by name rather than
restate.

## 9. Tasks, one per commit

Every task compiles before the next starts. Single-file `coqc` throughout,
never `make`, one Rocq process at a time.

### Landing 1 — framework and rows (estimate 2.5 to 3.5 hours)

| # | Task | Compiles | Est. |
|---|---|---|---|
| 1.0 | Commit the probe's working-tree refresh, so the export the audits read is reproducible (R9) | nothing | 5 min |
| 1.1 | Build `staged/` for the six files: `cp` from the probe, rewrite the `Require` block, resolve R1 | nothing | 30 min |
| 1.2 | Check the staged text against the probe's: comment-stripped and `Require`-stripped line-for-line match, and `tableau_ext_probe` occurs nowhere | nothing | 15 min |
| 1.3 | `cp` and compile `manifest/pgg_tableau.v` alone | itself | 15 min |
| 1.4 | `cp` and compile `manifest/pgg_tableau_syntax.v` alone | itself | 5 min |
| 1.5 | `cp` and compile the four rows files, in the order of section 3 | four files | 30 min |
| 1.6 | Rewrite `instances/psl211/psl211_reading_constancy.v`'s `:688-701` per section 4, compile it | itself | 20 min |
| 1.7 | `landing_fidelity.v` for landing 1: arm pins, the withdrawal `Fail`, the `<=` obligation, `Print Assumptions` | itself | 30 min |
| 1.8 | Commit. `asbuilt_fidelity.v` against production | itself | 20 min |

### Landing 2 — library and the five-card row (estimate 2 to 3 hours)

| # | Task | Compiles | Est. |
|---|---|---|---|
| 2.1 | Check `instances/psl211/psl211_endpoints.vo`'s date (R3) | nothing | 2 min |
| 2.2 | `lib/var_dist_supp.v`: add `var_dist_fdistmap_pair`, `var_dist_prodR`, `fdist_prod_snd`, `var_dist_own_marginals`; remove `card_tnth_count`. Compile alone | itself | 20 min |
| 2.3 | `instances/kim2025/five_card_mixing.v`: add `card_tnth_count`. Compile alone | itself | 10 min |
| 2.4 | Recompile the nine remaining files of `var_dist_supp.v`'s reverse closure, in order | nine files | 30 min |
| 2.5 | Decide R5 and apply it | up to two files | 20 min |
| 2.6 | New `instances/kim2025/five_card_proximity.v` from p4, p7, p8, p9; `_CoqProject` line; compile | itself | 40 min |
| 2.7 | Extend `landing_fidelity.v` and `asbuilt_fidelity.v`; commit | two files | 25 min |

### Landing 3 — PGL(2,7) (estimate 2.5 to 3.5 hours)

| # | Task | Compiles | Est. |
|---|---|---|---|
| 3.1 | `instances/pgl27/pgl27_exec.v`: add `pgl27_prior_sample`. Compile alone | itself | 15 min |
| 3.2 | `instances/pgl27/pgl27_models.v`: add the family, its view equation and its witness. Compile alone | itself | 20 min |
| 3.3 | `instances/pgl27/pgl27_analysis.v`: add the `prior_exact_family` alias (R2). Compile alone | itself | 10 min |
| 3.4 | `manifest/pgg_analysis_manifest.v`: the row, its table block, its three pins. Compile alone | itself | 30 min |
| 3.5 | Recompile the manifest's eight-file reverse closure (R4) | eight files | 30 min |
| 3.6 | New `instances/pgl27/pgl27_proximity.v` from p5 and p5_mutations; resolve the `first [...]` list; `_CoqProject` line; compile | itself | 45 min |
| 3.7 | Extend both fidelity files; commit | two files | 25 min |

### Landing 4 — PSL(2,11) (estimate 2.5 to 3.5 hours)

| # | Task | Compiles | Est. |
|---|---|---|---|
| 4.1 | New `instances/psl211/psl211_word_model.v` from p6; `_CoqProject` line; compile alone | itself | 25 min |
| 4.2 | `instances/psl211/psl211_analysis.v`: add the `word_family` alias (R2). Compile alone | itself | 15 min |
| 4.3 | `manifest/pgg_analysis_manifest.v`: the row, its block, its pins; read the PSL(2,11) block in full (R12). Compile alone | itself | 35 min |
| 4.4 | Rewrite `instances/psl211/psl211_reading_constancy.v`'s `:67-69` and `:768-771` per section 5; compile | itself | 25 min |
| 4.5 | `manifest/pgg_analysis_client.v`: the row count and the two `Check` lines; compile last | itself | 10 min |
| 4.6 | Recompile the manifest's reverse closure | eight files | 30 min |
| 4.7 | New `instances/psl211/psl211_word_proximity.v` from p6 and p6_mutations; `_CoqProject` line; compile | itself | 40 min |
| 4.8 | Extend both fidelity files; commit | two files | 25 min |

Compile-cost warnings carried from the probe's proof-engineering section:
`by []`, `done` and `by split` do not return on an equation between
`published_at` of a concluded row and an unconcluded one, 683 s measured.
Every such proof is `exact: erefl`, with `reflexivity` as the fallback when
the `-time` line is slow. `Print Assumptions` on a declaration whose type
names `psl211_alldecks_observed` costs about 20 s, which is what landing 4's
fidelity run pays.

---

## 10. Audit plan

Two independent Opus audits per landing, one for soundness and one for naming
and style, both reading a frozen `git archive` export of the branch at the
moment the landing's last commit is written, so neither reads a working tree
that moves under it.

The probe's audits covered the mathematics: five stages, ten audit reports in
`notes/probes/2026-09-19-tableau-extensions/`. The landing audits do not
repeat them. What each landing audit checks that is new:

### Soundness audit, per landing

| Landing | New to check |
|---|---|
| 1 | The `Require` rewrite is the only forced edit: staged text equals probe text once comments and `Require` blocks are stripped. The withdrawal of D3 removes four declarations and no row's published number changes: `five_card_row_repeated39` still publishes `2^-39`. The `<=` obligation makes no existing published number move. `psl211_reading_constancy.v:688-701` is true sentence by sentence after the rewrite |
| 2 | The move of `card_tnth_count` and the promotion of `var_dist_prodR` and `fdist_prod_snd` change no statement; the moved and promoted lemmas are the same propositions in their new homes. The eleven recompiled files' `Print Assumptions` is unchanged against the pre-landing run. R5's decision is applied consistently |
| 3 | The manifest row's five fields are the row equation's, checked against `pgl27_row_prior_exact_rowE` and not retyped. The facade alias resolves to the same family term. The `first [...]` resolution changed the proof and not the statement. The additions to `pgl27_exec.v` and `pgl27_models.v` are additions and nothing in those files moved |
| 4 | The manifest row's fields against `psl211_row_word_proximity_rowE`. The two rewritten comments of `psl211_reading_constancy.v` are true of the tree as it now stands, and the refutation's scope is unchanged. `psl211_endpoints.vo` was loaded and not rebuilt, with its date before the landing. The client's row count is eleven |

Every landing's soundness audit also checks: no new `Axiom`, `Parameter`,
`Admitted` or `Abort`; every published number below the `var_dist_le2`
ceiling; every distance a variation distance between exact laws with no
computational assumption; and that the file the audit reads is the file the
commit holds.

### Naming and style audit, per landing

| Landing | New to check |
|---|---|
| 1 | The `ConcludePayload`/`port_conclude` rename is complete at all seven sites and no `reprice` survives outside a comment that means the old name. The `_armE` names follow the tree's `<row>_armE` pattern. The header's counts and the `Definitions:` block match the file's contents |
| 2 | `var_dist_supp.v`'s section structure after the move and the promotion; the three promoted lemmas' comments state their position in the argument and not their types. No project-local abbreviation |
| 3 | `pgl27_prior_*` reads as the tree's other `pgl27_*` names; `pow2_40_*` is resolved per R7; the new file's header states what the file is for without restating the Tableau's |
| 4 | `psl211_word_*` against the tree's `psl211_alldecks_*` and `psl211_exact_*`; "indistinguishability" never abbreviated; the new file's header |

Every landing's naming audit also checks: none of the three barred words of
`~/.claude/CLAUDE.md`, in any of their forms; "the sum of absolute
differences" and never the two-letter name; one word per concept file-wide;
and every statement comment
carrying both its mathematical fact and its position in the argument the file
is making.

The auditors' replacement sentences were false about a dozen times in the
probe batch. Every audit brief repeats the rule that a replacement sentence is
checked against the declaration before it is pasted.

## 11. Orchestrator's decisions on the risk list (2026-09-19)

These supersede the text above wherever they differ. The draft of sections 1
to 10 is by an Opus agent that compiled nothing; its bulk scans ran on two
Sonnet agents whose claims it re-read in the files. The main session read the
risk list and section 1 and decided as follows.

| Risk | Decision |
|---|---|
| R1 | Way (a). `pgl27_word_sampled` and `pgl27_row_word_branch39`, with the lemmas of `t0_sampled_branch_pgl27.v` that the landing rows are stated against, move into the staged `instances/pgl27/pgl27_rows.v` in landing 1, beside `pgl27_dealt`. The text is the probe's, moved and not rewritten. |
| R2 | Accepted. Landings 3 and 4 include the facades `pgl27_analysis.v` and `psl211_analysis.v`, which `Require` the file of the new family and alias it. The spec's "empty reverse closure" holds for the new file alone. |
| R3 | No action. Single-file compiles load `psl211_endpoints.vo` by digest. The mismatch of dates predates this campaign and is reported to the owner. |
| R4 | Accepted. One session, one Rocq process, so the two manifest edits cannot overlap. |
| R5 | Both `Local` copies of `var_dist_prodR` stay. The comment of the promoted lemma in `lib/var_dist_supp.v` names the two files. |
| R6 | `var_dist_prodL` and `fdist_uniform_prod` stay in the probe. |
| R7 | No promotion into `lib/`. The PGL(2,7) pair lands as `pgl27_pow2_40_ge1` and `pgl27_pow2_40_gt0`, matching the PSL(2,11) pair's prefix. A forced edit of landing 3. |
| R8 | The declarations that name no instance do not go to an instance file. They land in a new file `manifest/pgg_tableau_arm_relations.v` in landing 2 (empty reverse closure apart from `five_card_proximity.v` if it uses one of them). The five-card statements go to `five_card_proximity.v`. |
| R9 | Done: the probe's renamed text is commit 2679c1f. |
| R10 | Accepted and recorded for the `tableau/` batch. |
| R12 | Landing 4 reads rows 9 and the facade table of the manifest in full before it edits. |
| R13 | Landing 1 lands the probe's text, which keeps the type name `Reprice` and the constants `*_reprice39`. Whether `Reprice` is renamed now that `conclude` no longer restates a number at equality is the owner's naming decision. It is a mechanical pass that can follow any landing. |
| R14 | The worktree under `.claude/worktrees/` is left alone. Every export comes from a commit and every scan excludes `.claude/`. |
| R15 | Landing 1 writes that one header sentence. The soundness audit of landing 1 reads it against `psl211_word_proximity_cert_secretE` and `psl211_word_proximity_cert_secretTE` of the probe. |
| D3 split | Accepted: `kim_centi_cert40` and `kim_centi_cert40_epsE` leave in landing 1, the two declarations of `five_card_mixing.v` in landing 2. |
