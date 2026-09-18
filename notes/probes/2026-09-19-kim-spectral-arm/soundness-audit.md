# Soundness audit: can Kim's five-card rows be certified by the spectral arm?

Independent adversarial audit of `notes/20260919-kim-spectral-arm-probe-design.md`
and `notes/probes/2026-09-19-kim-spectral-arm/`. 2026-09-19.

**VERDICT: NO-GO** for folding the spec and reporting it to the user as it
stands. One claim in `STATUS.md` is false under the repository's own
definitions: S8's conclusion that the biased row needs no manifest change. The
mathematics is sound. Every compiled statement I checked is true, the two new
fields have exactly the record's field types, and nothing is vacuous. The
remedy is narrow: rewrite two sentences of S8 and add one field to the
landing's change list. With that done the answer flips to GO.

I recompiled all five probe files from source in my own directory
(`scratchpad/b3_audit/`, rc=0 for each) and wrote two audit files of my own,
`audit_checks.v` and `audit_concrete.v`, both rc=0. No repository file was
edited; `git status --short` over `lib protocol groups security smc reconstruct
instances manifest _CoqProject` is empty.

## Findings

| ID | Severity | Claim audited | Evidence | Recommended change |
|---|---|---|---|---|
| F1 | BLOCKING | `STATUS.md` S8: "the **biased row needs no manifest change at all**", and the S8 table row `five_card_row_biased ... unchanged ... none`. | `manifest/pgg_analysis_status.v:63-73` defines `IdealFinite` as covering "a cut-carrier transfer whose base premise is discharged", and says `StaticExecutedOnly` "carr[ies] no such theorem". `manifest/pgg_analysis_manifest.v:744-747` says `word_mixing` supplying "the base-distribution bound the generic transfer inequality needs on the cut carrier itself ... is what makes the transfer status `IdealFinite` rather than merely `StaticExecutedOnly`". `kim_biased_sc_close` is that bound, on that carrier, against a named ideal. The probe itself publishes the *repeated* row at `IdealFinite` on the identical certificate shape (`kim_spectral_rows_probe.v:91-95` against `:105-109`). | Record the honest status as `IdealFinite` for both rows. State that a landing must change `apr_transfer` of `five_card_row_biased` from `StaticExecutedOnly` to `IdealFinite` and rewrite its docstring at `pgg_analysis_manifest.v:760-768`, which currently names only `colour_view_leak_bound`. Delete the sentence that the biased row needs no manifest change. |
| F2 | SHOULD-FIX | The `rowE` equations are presented as the thing that settles the manifest question. | `AnalysisPathRow` (`pgg_analysis_manifest.v:707-725`) has five fields and none is a `Prop`; the record "stores no theorem" (`:702`). My `A5_row_insensitive` proves `published_row kim_row_biased_spectral_static = published_row kim_row_biased25`, so two different certificates and two different published numbers give the same row. My `A5_same_data` and `A5_same_thm` prove that `kim_row_biased_spectral` and `kim_row_biased_spectral_static` have the *same data and the same theorem*, differing only in the label (`A5_labels`). | Say plainly in S8 that a `rowE` equation compares descriptive metadata and carries no security content, so it cannot decide which transfer status is honest. |
| F3 | SHOULD-FIX | S8's list of what a landing changes: `apr_completion` and `apr_transfer` of `five_card_row_repeated`, nothing else. | Incomplete. See the Q8 paragraph for the full list. In particular `five_card_row_repeated_at_manifest_level` (`five_card_rows.v:456-458`) ascribes the `Sampled` program at `Tableau (apr_completion five_card_row_repeated)`; moving that row to `AnalysisBridged` makes the ascription fail to typecheck. | Extend the S8 change list with the seven items in the Q8 paragraph, and flag the ascription as a compile breakage rather than a prose edit. |
| F4 | SHOULD-FIX | "far below the ceiling 2", used four times in S7 to argue non-vacuity. | infotheo's `variation_dist.v` contains four lemmas and none of them bounds `var_dist` above; the repository proves no such bound either. The ceiling is asserted in prose only. I proved it: `A4_var_dist_le2 : var_dist P Q <= 2%:R`, six lines. | If a paper cites the ceiling, land the one-lemma proof beside the rows. Otherwise say the ceiling is elementary and uncited. |
| F5 | NOTE | `kim_sc_close_probe.v:118`: "it overstates the distance it certifies by the factor the file header records". | That file has no header recording a factor. The number is `sqrt 5 / 80 = 0.02795` against the exact `1/50 = 0.02`, a factor of about 1.4. | Write the factor, or drop the reference. |
| F6 | NOTE | `five_card_rotation_probe.v:35-36`: `fc_sigma_pow5`'s comment says the fact makes "the cut group ... have exactly the five elements the deck has positions". | `fc_sigma ^+ 5 = 1` gives order dividing five. That the group has exactly five elements is proved elsewhere (`den_boer_encoding.v:64-71`, `pgg_G FiveCardKim_M = <[fc_sigma]>`), not by this lemma. | Restate the comment as "order dividing five", or cite the group identity. |
| F7 | NOTE | S1's mutation covers only a reader that separates nothing. | The mutation shows the hypothesis cannot be dropped altogether. It does not show the *union* of the two supports is needed rather than the support of one law. | Optional second mutation: a reader injective on `supp P` but merging two points of `supp Q`. |
| F8 | NOTE | `kim_centi_bound40` declares `sw_L := 7` and `kim_biased_bound50` declares `sw_L := 1`. | Both are correct, but `sw_L` enters neither `cert_eps` nor `SpectralPropAt`, so a wrong value would pass unnoticed. | No change. Worth knowing that this field is undefended. |
| F9 | NOTE | `SpectralPropAt` fixes the run argument and pushes the *cut marginal* `sa_cut_dist sa`. | For this to read as "the conditional law of the executed view given input x", the adapter's argument and cut must be independent. They are: `kim_input_dist` is a product (`kim_input_privacy.v:58-60`). This is a property of these two adapters, not of the arm. | State the product structure when the statement is described in words. |

Nothing I found is a kernel-level unsoundness. No `Admitted`, `Axiom`, `admit`,
`Abort`, `Parameter`, `Hypothesis` or `Conjecture` occurs in any of the five
probe files; the only section binder anywhere is `Variable R : realType`.

## Q1 Field fidelity

Exact, and the kernel is the witness. `SpectralCert`
(`manifest/pgg_tableau.v:131-142`) is a dependent record: `sc_close`'s type
mentions `sc_b` and `sc_ideal`, and `sc_const`'s type mentions `sc_ideal`. A
term in one of those slots must have the field type up to conversion, so the
fact that `MkSpectralCert` elaborates for all four certificates
(`kim_centi_cert`, `kim_biased_cert`, `kim_centi_cert40`, `kim_biased_cert50`)
already rules out an added hypothesis, a weakened quantifier or a changed
ideal. I confirmed the slots hold the named terms and not variants of them:
`A1_close`, `A1_const`, `A1b_close`, `A1b_const` close by `erefl`, so the
fields *are* `kim_centi_sc_close R`, `five_card_sc_const R`,
`kim_biased_sc_close R` and `five_card_sc_const R`. On the ideal: there is one
`sc_ideal` field, and `A1_ideal`, `A1b_ideal`, `A1c40_ideal` and `A1c50_ideal`
each close by `erefl` at `sa_cut_dist (five_card_sample R)`, so the ideal used
by `sc_close` and the ideal used by `sc_const` are the same term in all four
certificates. My `A1_wrong_ideal` is a rejected `MkSpectralCert` that measures
the distance against the row's own biased cut instead of the uniform one,
confirming the two slots are tied together and not independently choosable.
`kim_centi40_sc_close` and `kim_biased50_sc_close` likewise carry no hypothesis
and are stated at the record's field type.

## Q2 S1, the transport lemma

Stated correctly. `var_dist_fdistmap_supp_inj`
(`var_dist_injective_probe.v:44-48`) asks that `f` separate any two points at
least one of which carries mass under `P` or under `Q`, which is injectivity on
the union of the two supports, and concludes an equality of variation
distances. The equality is what `sc_close` needs, and the direction matters:
`var_dist_fdistmap` (`security/pgg_collusion_bound.v:126`) is the data
processing inequality `var_dist (fdistmap f P) (fdistmap f Q) <= var_dist P Q`,
which runs from the group to the reading and is useless here, and
`var_dist_fdistmap_inj` (`:73`) needs `f` injective on the whole domain, which
`g |-> g s` on `{perm 'I_5}` is not (it is twenty-four to one). So the new
lemma is genuinely needed and is a strict generalization of the existing
equality case; its proof is the same script with the hypothesis weakened. The
mutation is real: `var_dist_const_reader_false` proves the equality *false* at
a constant reader, where the left side is zero and the right side is two, and
the recorded `Fail` shows the lemma's own script cannot discharge the
hypothesis there. infotheo's `variation_dist.v` is confirmed to be the L1 sum
`\sum_a |P a - Q a|` with no lemma about `fdistmap` at all, so the ceiling is 2
and the spec's "ceiling 1" was wrong, as `STATUS.md` says.

## Q3 S2, S3, S4, the rotations and the two word lengths

The argument holds and the coverage is complete. `fc_word_eval_pow` evaluates
any word over `fc_kim_gens` to a power of `fc_sigma`, so
`rho_words_rot_supp` covers every word length and every letter weighting in one
statement; that is why one support lemma serves three cut laws.
`fc_rot_pow_faithful` is regularity: a rotation is fixed by the image of one
position. Both are used where they should be. On coverage of the certificate's
own `sc_b`: `kim_centi_rot_supp` is stated at
`sw_rho_dist (scb_bound (kim_security_bundle_centi R))` and closes by `exact:
rho_words_rot_supp`, which forces the kernel to unfold that to
`rho_from_words_weighted` at length 7; `kim_single_rot_supp` does the same at
length 1 for `five_card_biased_sc_b`; `kim_biased50_sc_close` applies
`rho_words_rot_supp` directly at `kim_biased_bound50`, and `kim_centi40_sc_close`
applies `kim_centi_rot_supp` at `kim_centi_bound40`. So all four bounds are
covered at both word lengths. `sc_Hd` ties each bound's law to the adapter's
cut: the repeated row uses `esym (kim_centi_cut_distE R)`
(`five_card_models.v:402`), the one-cut row uses `five_card_biased_sc_Hd`,
built from `rho_from_words_weighted1`, `kim_single_cut_distE`
(`five_card_models.v:188`) and `fc_kim_gensE`. Both typecheck in the `sc_Hd`
slot, which is where the identification is kernel-checked. The claim that the
group distance *equals* the endpoint-marginal distance is proved, not assumed:
`five_card_sc_close_of_rot_supp` rewrites with the transport equality and then
applies `sw_bound b ord0`. It reads position `ord0` only, which is harmless
because `sw_bound` holds at every position and regularity makes the choice
immaterial.

## Q4 S5, the domain question

A seat reads a colour, not a card identity, and I proved it rather than
inferring it. `encode_bool : bool -> 'I_5` is `if x then inord 1 else inord 0`
(`five_card_program.v:142`), and `den_boer_layout` is `map_tuple encode_bool
(fc_arrange_tup ...)` (`den_boer_encoding.v:24-25`), so my `A3_colour_only`
proves that every entry of `static_coalition_obs C x g` is `encode_bool b` for
some boolean, and `A3_two_valued` that it lies in a two-element list. The five
card positions are therefore distinguishable only by colour, which is den
Boer's own modelling assumption and faithful to the protocol. I checked the
census by hand from the sources: `fc_arrange a b = rev (fc_encode a) ++ [true]
++ fc_encode b` gives `(F,F) -> TFTFT`, `(F,T) -> TFTTF`, `(T,F) -> FTTFT`,
`(T,T) -> FTTTF`, three hearts and two clubs in every row, exactly the table in
`STATUS.md`. `(T,T)` is the only row with three consecutive hearts and is not a
cyclic rotation of the other three, so `den_boer_orbit` (`:42`) really does not
reach across the two values of the conjunction; the census does, and
`STATUS.md`'s English is the real reason. The probe's claim that
`five_card_viewS_indep` does not already imply `sc_const` is right:
independence from the conjunction under the joint uniform sample equates two
*averages*, the average over the three inputs with conjunction false against
the single input with conjunction true, and permits those three to differ from
one another; `sc_const` equates the laws at two *fixed* inputs. As a side
observation the identity-versus-colour distinction would not by itself break
`sc_const` at one seat, because a layout of five distinct cards read at a
uniform position also gives an input-free law; it is at two or more seats that
identities would matter, and the threshold keeps the statement at one.

## Q5 Threshold and the certified proposition

`profile_k (instance_profile five_card_algebra)` is 2 (`profile_k_denboer`,
`den_boer_profile.v:90`), and the probe's `have HC2 : (#|C| < 2)%N := HC`
typechecks, so the reduction is definitional. The coalition is therefore empty
or a single seat, and the empty case is trivial. In one sentence, what
`spectral_tail` (`pgg_tableau.v:561-571`) produces is: *at every real field and
every index of the model family, for every coalition of at most one seat and
every two committed pairs, the sum of absolute differences between the law of
that coalition's static endpoint reading at the first pair and its law at the
second pair, both taken under the row's own cut law, is at most the row's
published number.* `STATUS.md`'s S9 sentence says exactly this and I found no
discrepancy. I searched the five probe files and `STATUS.md` for any sentence
extending the result to two seats, to the full reveal, or to independence from
the secret, and found none; S9 denies all three explicitly, and the comment on
`five_card_sc_const` states the one-seat restriction in the body. Two things
are worth writing down beside the sentence. First, the two run arguments range
over all four committed pairs, so the statement does cover pairs with different
conjunction values, which is the domain-meaningful reading. Second, `sa_cut_dist
sa` is the cut *marginal* with the input pinned outside it, so the statement
reads as a conditional law only because `kim_input_dist` is a product
(`kim_input_privacy.v:58-60`); that is a property of these adapters, not of the
arm (F9).

## Q6 Numbers and vacuity

The ceiling is 2 and I proved it (`A4_var_dist_le2`), so a published number is
non-vacuous exactly when it is below 2. All four are, and I checked each.
Repeated row form 1: `cert_eps = 2 * sqrt 5 * (1/80)^7`, about `2.13e-13`,
about `1.2e-13` of the ceiling; strong. `kim_centi_cert_eps_lt` puts it below
`2^-39` and I verified `2^-39 < 2` (`A4_pow2_39_lt2`) and hence
`cert_eps < 2` (`A4_repeated_form1_lt2`). Repeated row form 2: `2^-40 + 2^-40`,
repriced to `2^-39`, about `1.8e-12`; strong, but about eight and a half times
weaker than what form 1 proves, which I checked directly
(`A4_form2_weaker : cert_eps (kim_centi_cert R idx) < cert_eps (kim_centi_cert40
R idx)`). Biased row form 1: `sqrt 5 / 40`, about `0.0559`, under three percent
of the ceiling; weak but not vacuous. Biased row form 2: exactly `1/25 = 0.04`;
weak, not vacuous, and stronger than form 1, which I checked
(`A4_biased_form2_stronger`). Both form-2 records are honest. `kim_centi_bound40`
declares `2^-40` and supplies `fun s => ltW (kim_deal_centi_lt R s)`, which is a
proof at that same distribution and at that same number, not an inheritance;
`kim_biased_bound50` declares `1/50` and supplies `kim_one_cut_le`, derived from
the exact equality `kim_one_cut_centiE`. That the epsilon is not free I
confirmed by two rejected records: `A2_eps41` tries the same proof at `2^-41`
and `A2_eps100` tries the one-cut proof at `1/100`, and both are rejected. One
honest remark about the biased numbers: `1/25` is what the triangle inequality
through the ideal gives from a per-position distance of `1/50`, so it is tight
for this argument but is an upper bound on a quantity that a direct computation
might show to be much smaller.

## Q7 Transfer status honesty

The honest status is `IdealFinite`, for both rows, and the `erefl` is an
accident of metadata. The status vocabulary decides it. `IdealFinite` is
defined at `pgg_analysis_status.v:63-73` as "a public model-transfer theorem"
covering "a cut-carrier transfer whose base premise is discharged", while
`StaticExecutedOnly` and `NoModelComparison` "carry no such theorem, and the
manifest row of such a path names the absent premise instead". A `SpectralCert`
is precisely a cut-carrier transfer with its base premise discharged: `sc_ideal`
names the ideal, `sc_close` is the distance on the cut carrier, and
`sc_const` is what makes the ideal usable. The manifest states the criterion
again in its own words for the precedent: `pgl27_row_word` is `IdealFinite`
because `word_mixing` "supplies the base-distribution bound the generic
transfer inequality needs on the cut carrier itself, which is what makes the
transfer status `IdealFinite` rather than merely `StaticExecutedOnly`"
(`pgg_analysis_manifest.v:744-747`). The probe's own treatment is internally
inconsistent: the repeated row is published at `IdealFinite` and the biased row,
carrying a certificate of identical shape over the same ideal with the same
`sc_const` field, is published at `StaticExecutedOnly`. The only reason given
is that the second choice makes an `erefl` close. That `erefl` carries nothing:
`AnalysisPathRow` stores no theorem (`pgg_analysis_manifest.v:702`, and the
record at `:707-725` has no `Prop` field), the data and the theorem of the two
biased programs are the same term (`A5_same_data`, `A5_same_thm`) and only the
label differs (`A5_labels`), and two different certificates with two different
published numbers publish the same row (`A5_row_insensitive`). So a landing must
change the manifest's biased row too: `apr_transfer` from `StaticExecutedOnly`
to `IdealFinite`, and the docstring at `:760-768`, which currently explains the
row's level by `colour_view_leak_bound` and names no ideal. Nothing in any
`rowE` equation carries security content; they are equalities of descriptive
metadata and should be described that way.

## Q8 What a landing would make false or obsolete

Certifying through `SpectralDecay` contradicts nothing that landed today. Every
statement in `instances/kim2025/five_card_rows.v` that is a theorem stays true:
`five_card_row_repeated_endpoint_lt`, `kim_centi_small`,
`five_card_row_biased_leak_bound`, `five_card_row_uniform_tableau` and its
`rowE`, `five_card_exact_view_secrecy`, the three `prefixE` and two `modelE`
lemmas, `five_card_row_biased_levelE`, `five_card_committed_paramsE`, and the
recorded `Fail five_card_row_s5_family`. The exact arm stays false in
expectation under a biased cut and the probe asserts nothing to the contrary.
What a landing makes false or obsolete is prose and one ascription, and the
list is longer than S8's. (1) The header sentence at `:39-42`, "the spectral arm
asks for a variation distance to an ideal cut on the shuffle group together
with the constancy of a coalition's reading of that ideal, and neither of those
is proved at this instance", becomes false; both are now proved. (2) The header
paragraph at `:42-50`, which explains `AnalysisBridged` as "one constructor
with two admission criteria" and calls the biased row's gap "the manifest's
criterion met by a theorem no arm takes ... the situation
`instances/s5/s5_rows.v` already records for `s5_row_word`", becomes obsolete
for the biased row; the S5 comparison no longer applies there, though it stays
correct for S5 itself, where `sc_const` is false for a reason no proof removes
(`s5_rows.v:60-72`). (3) The header sentence at `:29-33` that both Kim rows stop
at `Sampled` becomes obsolete. (4) The docstring of
`five_card_row_repeated_tableau` (`:383-389`), ending "so no security payload
follows it", becomes false. (5) The docstring of `five_card_row_biased_tableau`
(`:396-400`), which says neither arm takes a bound of the kind the row has,
becomes false. (6) The docstrings of `five_card_row_biased_levelE` (`:460-464`)
and of the recorded `Fail five_card_row_biased_at_manifest_level` (`:469-475`)
describe a level gap that closes; the `Fail` itself stays true as a statement
about the `Sampled` program, but its prose is then misleading. (7)
`five_card_row_repeated_at_manifest_level` (`:456-458`) ascribes the `Sampled`
program at `Tableau (apr_completion five_card_row_repeated)`; if the manifest's
repeated row moves to `AnalysisBridged` this stops typechecking, so it is a
compile breakage and not a comment edit. On the manifest side, both five-card
docstrings (`:760-768` and `:770-778`) explain their statuses by theorems that
are no longer the reason.

## Q9 Tautology and vacuity

Nothing headline is hidden behind reflexivity in a way that conceals emptiness,
and three conversion proofs are worth naming for what they do and do not do.
`kim_centi_cert40_epsE` closes by `[]` because `cert_eps` is a projection sum
and `sw_bound_eps (kim_centi_bound40 R)` is literally `2%:R ^- 40`
(`A1_eps40`); it reports the record's declared number and proves no arithmetic,
which `STATUS.md` says. The mathematics sits in that record's `sw_bound` field,
which is `kim_deal_centi_lt` weakened. `kim_row_biased_static_rowE` and
`kim_row_biased25_rowE` close by `[]` over a record with no `Prop` field, so
they compare descriptive metadata; this is the one place where a definitional
equality is doing rhetorical work it cannot support (F1, F2).
`kim_row_repeated_published_fields` reads off three enumeration constructors.
On satisfiability: every certificate is a closed term over an abstract
`R : realType`, and the only section binder anywhere is that variable, so the
hypothesis sets are trivially jointly satisfiable provided `realType` is
inhabited. I checked that it is, rather than assuming it:
`audit_concrete.v` instantiates the repeated row's certificate at
`Rdefinitions.R` through mathcomp's `Rstruct` and builds
`spectral_tail` at that concrete field, adding only the classical Dedekind-real
axioms of the instance and no axiom from the probe. The quantifiers inside the
statements are also non-empty: `amf_index` is `unit` for both families, the
coalition quantifier ranges over a set that can be empty or a singleton and the
singleton case does the work, and the run arguments range over four committed
pairs. The generic lemma `five_card_sc_close_of_rot_supp` carries one
hypothesis, discharged at all four bounds by compiled support lemmas, so it is
never applied vacuously.

## Q10 S10, the home for the generic lemmas

A new file is the right call, and the dependency arithmetic checks out. I
recomputed the closures from `.Makefile.rocq.d` independently and reproduce
`STATUS.md`'s table exactly: `security/pgg_collusion_bound.v` has 105 reverse
dependants with `psl211_endpoints` among them, `lib/perm_uniform.v` has 107,
also with it, and `instances/kim2025/five_card_rows.v` has none. So editing the
subject-matter home would force the long rebuild, and a new leaf file has an
empty reverse closure by construction and costs only its own compile plus
`five_card_rows.v`. Four remarks. First, the permanent file should not require
`pgg_collusion_bound.v`; the probe does so only for two `Check` lines, and
dropping that keeps the new file at mathcomp plus infotheo and makes it
importable from anywhere later. Second, the split home is a real hazard:
`var_dist_fdistmap_supp_inj` strictly generalizes `var_dist_fdistmap_inj`
(`:73`) and shares its proof script, so a reader looking for variation-distance
transport lemmas will find two shelves. Put a comment in the new file naming
`pgg_collusion_bound.v` as the eventual home and merge them the next time that
file is edited for another reason. Third, `security/` is a shelf for security
statements and these are generic probability facts; `lib/` would read better
and has the same empty reverse closure for a new file, so either is acceptable
and the choice is cosmetic. Fourth, `card_tnth_count` has no probability
content at all and is a mathcomp tuple-counting fact; it would sit more
naturally in `lib/` or be inlined. None of this affects soundness. I spot
checked ten of the fifty-one proposed names against the repository and against
the installed infotheo and mathcomp trees and found no collisions, consistent
with `STATUS.md`.

## What a paper may and may not say

- May say: under Kim's seven biased cuts, a coalition of at most one of the
  five seats reads laws at any two committed pairs that differ by at most
  `2^-39` in L1, and under one biased cut by at most `1/25`, both proved in
  the kernel from the certificate's own fields with no assumption beyond the
  repository's classical baseline.
- May say: both bounds are unconditional. Nothing in them is conditional on a
  computational assumption, and the only inexact quantity in the repeated row
  is the bundle's spectral number; the two facts about the ideal cut are exact.
- May say: the five-card instance now reads like PGL(2,7) because the same arm
  certifies it, and the reason the ideal constancy holds is that den Boer's
  encoding deals three hearts and two clubs at every committed pair while only
  the arrangement moves.
- May not say: that the reading is independent of the secret. That is the
  exact arm's claim, it holds for the uniform model, and Kim's biased models do
  not inherit it.
- May not say: anything about two or more seats, or about the full reveal. The
  bound is conditional on the coalition having fewer than two seats, and the
  full reveal is covered only by the conditional mutual information bound that
  stays beside the programs.
- May not say: that the biased row's status is unchanged. Under the
  repository's own definition of `IdealFinite` the biased row's status becomes
  `IdealFinite`, and a paper reproducing the manifest table must show the new
  value.
- Take care: `1/25` is about two percent of the ceiling 2 of infotheo's
  variation distance, which is the sum of absolute differences and not the
  total variation distance. Halve it before comparing with a total-variation
  number in the literature, and note that no lemma in the tree proves the
  ceiling.
- Take care: `2^-39` is the repriced constant and is about eight and a half
  times weaker than the spectral expression `2 * sqrt 5 * (1/80)^7` the same
  development proves. Cite whichever is wanted, but not both as the same
  number.
