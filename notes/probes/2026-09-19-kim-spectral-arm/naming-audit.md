# NO-GO

Verdict on "these names, homes and comments may be carried into a landing plan
as they are": **NO-GO**.

The mathematics is not in question. This audit is about names, homes and
statement comments only. Six findings block a landing plan that copies the
probe text verbatim. Two of them are corrections to the mathematics a name
asserts, one is a declaration that already exists in the tree under another
name, one is a whole family of identifiers built from record field
abbreviations where the sibling instance already has domain words for the same
five fields, one is a row-naming scheme that contradicts the landed file it
would land into, and one is a landed declaration that stops compiling once the
manifest row changes.

Independent checks run for this audit: a whole-word scan of every new
identifier over 133 production files, 62 legacy files, 1153 installed library
files and 345 earlier probe files, and a reverse-dependency computation over
`.Makefile.rocq.d`. Both confirm the numbers in `STATUS.md`. No Rocq compiler
was run and no existing file was edited.

Audited text: `notes/20260919-kim-spectral-arm-probe-design.md`, and in
`notes/probes/2026-09-19-kim-spectral-arm/`: `var_dist_injective_probe.v`,
`five_card_rotation_probe.v`, `kim_sc_close_probe.v`,
`five_card_sc_const_probe.v`, `kim_spectral_rows_probe.v`, `STATUS.md`.

---

## 1. Findings

### Blocking

| ID | Severity | Location | What is wrong | Replacement |
|---|---|---|---|---|
| N1 | BLOCKING | `five_card_rotation_probe.v:47` | `fc_rot_pow_faithful` names a property the statement does not prove. MathComp's `faithful A S to` is `A :&: astab S to \subset [1]`, a trivial kernel on a whole set, defined at `mathcomp/fingroup/action.v:210`. The statement is that the stabiliser of ONE card position in the rotation group is trivial, which is freeness of the action at a point. A reader of the name alone would conclude the file proves only that the rotation group embeds in `Sym(5)`, which is a strictly weaker fact and not the one `sc_close` consumes. The comment on line 46 adds a third word, "regularity", for the same property. Regularity is freeness plus transitivity, and only the free half is proved here. | Rename to `fc_sigma_pow_point_inj`. Replacement comment below in section 4, item C2. |
| N2 | BLOCKING | `five_card_rotation_probe.v:100-103` | `five_card_ideal_distE` is `instances/kim2025/five_card_exec.v:756` `five_card_sample_cut_distE` after unfolding `five_card_sample_cut_dist`, which is defined at `five_card_exec.v:661` as `sa_cut_dist five_card_sample`. Its proof is `exact: five_card_sample_cut_distE`. `STATUS.md:488` proposes landing it as `five_card_ideal_cut_distE` into `five_card_exec.v`, which is the file that already holds the original. That would put two names for one equation in one file. | Delete the declaration. Use `five_card_sample_cut_distE` at every call site. If a five-card reader needs the `sa_cut_dist` spelling, add the one-line unfolding remark to the existing lemma's comment instead of a second lemma. |
| N3 | BLOCKING | `kim_sc_close_probe.v:47,77,91,99`; `five_card_sc_const_probe.v:88`; `kim_spectral_rows_probe.v:46,206,276` | Eight identifiers are built from `SpectralCert` field abbreviations: `_sc_close`, `_sc_b`, `_sc_Hd`, `_sc_const`. `sc_Hd` in particular is a project-local abbreviation no reader can expand without opening `manifest/pgg_tableau.v:131`. The sibling instance that fills the same five fields does not do this. `instances/pgl27/pgl27_rows.v:248-258` fills them with `pgl27_word_marginal_bound`, `pgl27_word_cut_distE`, `pgl27_word_mixing` and `pgl27_word_view_const`, and the Tableau surface's own clause words at `pgl27_rows.v:301-306` are `tied by`, `ideal`, `mixing by` and `invariant by`. The tree also already has `den_boer_marginal_bound` and `den_boer_sample_cut_witnessE` at `five_card_exec.v:989-993` for exactly these two shapes at this instance. | Rename all eight to the domain words. Full table in section 2. |
| N4 | BLOCKING | `kim_spectral_rows_probe.v:91,98,105,237,304` | The five row programs are named `kim_row_*`. The file they would land into names its three row programs `five_card_row_uniform_tableau`, `five_card_row_repeated_tableau` and `five_card_row_biased_tableau`, at `five_card_rows.v:338,390,401`, and the sibling instance names its two `pgl27_row_exact_tableau` and `pgl27_row_word_tableau` at `pgl27_rows.v:270,295`. After the landing the same file would hold `five_card_row_repeated_tableau` and `kim_row_repeated_spectral` for the same manifest path at two certification levels, under two prefixes and with the `_tableau` suffix on one of them only. | Rename to `five_card_row_*_tableau`. Full table in section 2. |
| N5 | BLOCKING | `kim_spectral_rows_probe.v:171,177` | The `_bad` suffix on `kim_row_biased_rowE_bad` and `kim_row_repeated_rowE_bad` is a status marker. The tree's convention for a recorded `Fail` is to name it after what is attempted and never to mark it as wrong: `five_card_rows.v:409,473,571` give `five_card_row_s5_family`, `five_card_row_biased_at_manifest_level` and `five_card_F_or`, and `pgl27_rows.v:281,350,362,389,580` give `pgl27_row_exact_leak7`, `pgl27_inline_neq`, `pgl27_inline_reuse`, `pgl27_row_word39_bare` and `pgl27_word_arm_is_not_exact`. The probe's own `kim_row_repeated39_bare` follows the convention correctly, which makes the two `_bad` names inconsistent inside one file. | `kim_row_biased_rowE_bad` becomes `five_card_row_biased_ideal_rowE`. `kim_row_repeated_rowE_bad` becomes `five_card_row_repeated_spectral_rowE`. Both stay recorded `Fail`s. |
| N6 | BLOCKING | `instances/kim2025/five_card_rows.v:456-458`, and header lines 29-50, and comments at 383-400 and 469-475 | The landing contradicts landed text and breaks a landed declaration. `five_card_row_repeated_at_manifest_level : Tableau (apr_completion five_card_row_repeated)` is an ascription of a `Tableau Sampled` term. `STATUS.md:420` says a landing changes `apr_completion five_card_row_repeated` from `Sampled` to `AnalysisBridged`. That ascription then fails to typecheck, and `STATUS.md`'s table of fields to change does not mention it. Separately, three pieces of landed prose become false: the header at lines 39-42 says the spectral arm "asks for a variation distance to an ideal cut on the shuffle group together with the constancy of a coalition's reading of that ideal, and neither of those is proved at this instance"; the comment at 394-400 gives the same reason for the biased row stopping at `Sampled`; and the comment at 469-475 on the recorded `Fail` reads as a statement about the biased path rather than about one particular program. | The landing plan must list, as work items: rewrite the file header lines 29-50, rewrite the comments at 383-400 and 469-475, and either delete `five_card_row_repeated_at_manifest_level` or restate it against the new manifest row. None of this is optional once `apr_completion` changes. |

### Should fix

| ID | Severity | Location | What is wrong | Replacement |
|---|---|---|---|---|
| N7 | SHOULD-FIX | `kim_spectral_rows_probe.v:199,232,237,268,296,300,304` | The numeral suffix slot carries two different readings. In `kim_centi_bound40`, `kim_reprice39` and `kim_row_repeated39` the numeral is the exponent of a power of two, which is the reading `pgl27_reprice39` and `pgl27_row_word39` establish at `pgl27_rows.v:371,378`. In `kim_biased_bound50`, `kim_reprice25`, `kim_row_biased25` and `fifty_split` the numeral is a denominator. A reader cannot tell `2^-40` from `1/50` by the name. | Spell the reciprocals: `kim_biased_bound50` becomes `kim_biased_marginal_bound_exact`, since `1/50` is the exact distance of `kim_one_cut_centiE` and not a chosen constant. `kim_reprice25` becomes `five_card_reprice_inv25`. `kim_row_biased25` becomes `five_card_row_biased_inv25`. `fifty_split` becomes `inv50_split`. |
| N8 | SHOULD-FIX | `five_card_rotation_probe.v:47,59,89,106`; `kim_sc_close_probe.v:47`; `kim_spectral_rows_probe.v:281` | `rot` is a second word for a concept the tree already names. `instances/denboer1989/five_card_scheme_I5.v:210` calls `fc_sigma ^+ k` a `fc_sigma_pow`, and `instances/kim2025/five_card_kim.v:109` defines `fc_sigma_pow`. Meanwhile `rot` is MathComp's sequence rotation and is used in that sense in this very development at `five_card_scheme_I5.v:230` and `den_boer_encoding.v:44`. Two meanings for `rot` in one instance. | Use `pow` for the group elements. `rho_words_rot_supp` becomes `fc_kim_rho_supp_pow`, `five_card_ideal_rot_supp` becomes `five_card_ideal_supp_pow`, `kim_single_rot_supp` becomes `kim_single_cut_supp_pow`, `kim_centi_rot_supp` becomes `kim_centi_cut_supp_pow`, `fc_rot_point_inj` becomes `fc_sigma_pow_ord_inj`. |
| N9 | SHOULD-FIX | `five_card_sc_const_probe.v:52` | `den_boer_layout_law` names a distribution, not the proposition. The statement is that the distribution is the SAME at two committed pairs. The tree's word for that is `_const`, at `pgl27_word_privacy.v:168` `pgl27_view_law_const`, `pgl27_rows.v:224` `pgl27_word_view_const` and `reconstruct/transitivity_privacy.v:216` `fdistmap_prod_const`. | Rename to `den_boer_layout_law_const`. |
| N10 | SHOULD-FIX | `var_dist_injective_probe.v:129` | `fdistmap_supp` overclaims. infotheo defines `fdist_supp d := [set a | d a != 0]` at `infotheo/probability/fdist.v:188`, so a reader expects `fdist_supp (fdistmap f P) = f @: fdist_supp P`. The statement is the weaker one-way fact that mass at `b` puts `b` in the image of `f`. It also sits beside infotheo's `fdistmap_eq0` and `fdistmap_neq0` at `fdist.v:404,412`, which are the converse direction, so the family reading matters. | Rename to `fdistmap_neq0_codom`. Consider stating the conclusion as `b \in codom f` so that `codomP` applies directly. |
| N11 | SHOULD-FIX | `STATUS.md:477-481`, proposed home `security/pgg_var_dist_supp.v` | Wrong directory and a file name the contents do not match. Every file in `security/` is named `pgg_*` and holds PGG-specific security layers. `lib/` is where this tree puts extensions to the underlying libraries, and its files carry no `pgg_` prefix: `perm_uniform.v`, `perm_exchange.v`, `proba_entropy_ext.v`, `support_posterior.v`, `mutual_info_recoding.v`. All five proposed inhabitants are library-level facts with no PGG content. The rule about `psl211_endpoints` does not decide between the two directories, because a NEW file has an empty reverse closure wherever it is put, which I confirmed by construction. Separately, `card_tnth_count` is a tuple and fintype fact with no distribution in it and cannot honestly live in a file named after `var_dist`. | Put the four distribution lemmas in `lib/var_dist_supp.v`. Put `card_tnth_count` in `lib/` too, under a file whose name covers it, or keep it local to `den_boer_encoding.v` where its only consumer is. Both directories are covered by a `-R` line on the directory in `_CoqProject`, so no `_CoqProject` edit is needed either way. |
| N12 | SHOULD-FIX | `five_card_rotation_probe.v:34-36` | The comment claims more than the statement. `fc_sigma ^+ 5 = 1` gives that the order divides five. The comment concludes that "the cut group of the five-card instance has exactly the five elements the deck has positions", which needs the extra fact that the five-cycle is not the identity. Nothing in the file proves it. | Replacement comment in section 4, item C1. |
| N13 | SHOULD-FIX | `kim_sc_close_probe.v:116-118` | The comment on `five_card_biased_exact_le_eps` says the certificate's number "overstates the distance it certifies by the factor the file header records". `kim_sc_close_probe.v` has no header beyond the three-line probe banner and records no factor. The sentence points at text that does not exist, and a pointer of the "see X" kind does not belong in a statement comment in any case. | Replacement comment in section 4, item C7. |
| N14 | SHOULD-FIX | `five_card_rotation_probe.v:46,58,114`; `kim_sc_close_probe.v:44`; `var_dist_injective_probe.v:111` | Seat and card position are used for the same object. In all five sentences the object is `s : 'I_5` in the `sw_bound` field, which is a card position. A seat is an index into `pi_starts`, and the landed file keeps the two apart deliberately at `five_card_rows.v:227-233`, "the framework reads the dealt layout at the cut image of seat i's start". The two carriers coincide numerically at this instance only because `pi_starts` is the identity, which the probe itself proves as `Hst` at `five_card_sc_const_probe.v:99-101`. Writing "seat" where the statement quantifies over positions makes the comment say something the statement does not. | Write "card position" in all five sentences. The corrected texts are in section 4. |
| N15 | SHOULD-FIX | `var_dist_injective_probe.v:97-98` | The statement comment narrates a proof script: "The script of `var_dist_fdistmap_supp_inj` leaves the support hypothesis open at that reader, and no fact about the reader discharges it." Proof strategy belongs inside the proof. | Replacement comment in section 4, item C5. |
| N16 | SHOULD-FIX | `five_card_rotation_probe.v:86-88` | "so the support fact below is stated once" is roadmap, and "below" is a positional pointer that a landing reorders. | Replacement comment in section 4, item C3. |
| N17 | SHOULD-FIX | `five_card_sc_const_probe.v:99` | The only line over 80 columns in the five files, at 81. | Break after `have Hst :` and indent the quantifier by four: `have Hst :` on one line, then `    forall i : 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1,` which is 77 columns. |
| N18 | SHOULD-FIX | `five_card_rotation_probe.v:75`, `:89` | Wrong instance prefix. `fc_word_eval_pow` and `rho_words_rot_supp` are statements about `fc_kim_gens`, and the tree reserves `fc_` for den Boer's five-card objects and `fc_kim_` for Kim's, at `five_card_kim.v:115,125` `fc_kim_gens` and `fc_kim_gensE`. `rho_words_rot_supp` also carries no instance prefix at all in a file full of them. | `fc_word_eval_pow` becomes `fc_kim_word_eval_powE`, which is also `STATUS.md`'s own proposal, and the `E` is right because the statement is a rewriting equation. `rho_words_rot_supp` becomes `fc_kim_rho_supp_pow`, per N8. |
| N19 | SHOULD-FIX | `kim_sc_close_probe.v:91,112,119` | `five_card_biased_*` and `kim_biased_*` are both used for objects of the one-cut Kim model, inside one file: `five_card_biased_sc_b` and `five_card_biased_epsE` beside `kim_biased_sc_close`. The tree's split is clear. `kim_` is for objects typed over Kim's construction, such as `kim_biased_family` and `kim_security_bundle_centi`, and `five_card_` is for rows and instance-level statements, such as `five_card_row_biased_leak_bound`. The bound, its epsilon and its distance statement are all Kim objects. | Use `kim_biased_*` for all three. See the rename table. |
| N20 | SHOULD-FIX | `kim_spectral_rows_probe.v:296`, and the `pow2_split` reuse at `:130,241` | `fifty_split` is a bare unprefixed name that would land in a file where every other name carries an instance prefix. It is modelled on `pow2_split` at `pgl27_word_privacy.v:180`, which is bare for the same reason and is also mis-homed. Reusing `pow2_split` from `five_card_rows.v` would create the first dependency from `instances/kim2025` or `instances/denboer1989` on `instances/pgl27` in the whole tree. I checked: today there is none. | Two acceptable routes. Either reprove the one-line identity locally, which costs one `lra` line and keeps the instance directories independent, or reuse `pow2_split` and say in the landing plan that a new cross-instance edge is being added deliberately. The build cost of the edge is zero, because the 33 files `pgl27_word_privacy.v` depends on are already inside the 98 that `five_card_rows.v` depends on. The cost is architectural only. |

### Notes

| ID | Severity | Location | Observation |
|---|---|---|---|
| N21 | NOTE | `var_dist_injective_probe.v:113` | `fdistmap_inj_uniform_id` sits one token away from the tree's `fdistmap_inj_uniform` at `security/pgg_collusion_bound.v:572`, whose statement is `fdistmap f (fdist_uniform Hcard_A) = fdist_uniform_supp (f @: setT)`. The probe's lemma is the endomap corollary of it, since `f @: setT = setT` for an injective endomap of a finite type. The two are not duplicates, and the probe's six-line direct proof is cheaper than the derivation. Keep the name. The statement comment should say in one clause how it differs from its neighbour, so a reader who finds both knows which to use. |
| N22 | NOTE | `five_card_rotation_probe.v:75` | A strictly more general fact exists at `legacy/instances/abelian/abelian_word_collapse.v:177`, `abelian_word_eval`, which evaluates a word in an abelian generated group as a product of generator powers. `fc_kim_word_eval_powE` is derivable from it. Do not route through it. The source is under `legacy/`, and an eight-line direct proof is the right trade. |
| N23 | NOTE | `kim_sc_close_probe.v:122-124`; `kim_spectral_rows_probe.v:148-150` | The numeric goal selector `2:` appears four times. The tree uses it in exactly two places, `five_card_kim.v:626-627`, in the same `ler_pXn2r` side-condition shape. The probe follows the only precedent there is, so this is consistent rather than deviant, but it is a rare idiom and a reviewer may ask. |
| N24 | NOTE | all five probe files | Statement comments use `(* ... *)`. The landing target `five_card_rows.v` uses `(** ... *)` throughout, and `five_card_scheme_I5.v` and `five_card_exec.v` use `(** name — statement. *)` with the identifier repeated first. Match the target file's shape when landing. |
| N25 | NOTE | `STATUS.md:475-500` | The S10 home table spreads thirteen instance-specific declarations across six files whose reverse-dependency counts are 24, 20, 20, 16, 10 and 9, and then closes with "a landing that keeps everything instance-specific there recompiles one file", which is true of `five_card_rows.v` alone. The two statements are in tension. My measurements, in section 3, confirm every count in that table and add `den_boer_encoding.v` at 16, which the table omits. Either land everything instance-specific in `five_card_rows.v`, which has zero reverse-dependants, or state the real recompile cost in the plan. |
| N26 | NOTE | `kim_spectral_rows_probe.v:9`, `kim_sc_close_probe.v:6-7` | Import audit for the landing. `Require Import Lia` and `From mathcomp Require Import zify` appear in exactly one production file, `instances/kim2025/five_card_kim.v:74-75`, and the probe's ordering matches it exactly. `lra` appears in eleven production files including `instances/kim2025/kim_input_privacy.v` and `instances/denboer1989/five_card_leakage.v`. `five_card_rows.v` imports none of the three today. Landing `kim_biased_exact_le_eps`, `inv50_split` and `five_card_reprice_inv25_lt2` into it adds all three. Nothing new enters the tree. |
| N27 | NOTE | all five probe files, and the spec | No hits for the banned words in the seven audited files. See section 5. |

---

## 2. Rename table

Old names are as written in the probe. Where `STATUS.md`'s S10 table already
proposes a name, the column says so.

### Library-level lemmas, proposed home `lib/var_dist_supp.v`

| Old | New | Reason |
|---|---|---|
| `var_dist_fdistmap_supp_inj` | unchanged | Correct as it stands. `supp_inj` for "injective on the support" is already the tree's reading at `pgg_collusion_bound.v:725` `fdistmap_uniform_supp_inj`, whose hypothesis is `{in C &, injective f}`. The name also sits correctly beside `var_dist_fdistmap_inj` at `:73`. |
| `var_dist_const_reader_false` | `var_dist_fdistmap_const_neq` | `_false` is a status word. `_neq` is MathComp's suffix for a disequality. This is `STATUS.md`'s own proposal and it is right. |
| `fdistmap_supp` | `fdistmap_neq0_codom` | N10. The current name promises a support equality and delivers a one-way membership. |
| `fdistmap_inj_uniform_id` | unchanged | N21. |
| `card_tnth_count` | unchanged | Head symbol `card`, both operands named, no project-local abbreviation. |
| `var_dist_const_reader_mutation` | does not land | Probe-only. "mutation" is probe idiom and the declaration is a recorded `Fail` whose job ends with the probe. |

### The five-cycle, proposed home `instances/denboer1989/five_card_scheme_I5.v`

| Old | New | Reason |
|---|---|---|
| `fc_sigma_pow5` | `fc_sigma_pow5_eq1` | The bare `fc_sigma_pow5` reads as a fact about `fc_sigma_pow` at index five, and `fc_sigma_pow` is a landed definition of type `'I_5 -> {perm 'I_5}` at `five_card_kim.v:109`, where there is no index five. The `_eq1` states the conclusion. `STATUS.md` proposes `fc_sigma_expg5`, which also avoids the misreading, but `pow` is this file's word for `^+`, established by `fc_sigma_pow_val` at `five_card_scheme_I5.v:210`. |
| `fc_rot_pow_faithful` | `fc_sigma_pow_point_inj` | N1. The statement is injectivity of evaluation at a point, restricted to the powers. |
| `fc_rot_point_inj` | `fc_sigma_pow_ord_inj` | N8. Distinguished from the previous one by the carrier of the thing that varies, which is the ordinal exponent here and the permutation there. Carrier qualifier last. |

### Kim's word shuffle, proposed home `instances/kim2025/five_card_kim.v`

| Old | New | Reason |
|---|---|---|
| `fc_word_eval_pow` | `fc_kim_word_eval_powE` | N18. Kim's generators take the `fc_kim_` prefix, and the statement is a rewriting equation. Same as `STATUS.md`. |
| `rho_words_rot_supp` | `fc_kim_rho_supp_pow` | N8 and N18. No bare names in an instance file, and `pow` rather than `rot`. |

### The ideal cut, proposed home `instances/kim2025/five_card_exec.v`

| Old | New | Reason |
|---|---|---|
| `five_card_ideal_distE` | deleted | N2. It is `five_card_sample_cut_distE`. |
| `five_card_ideal_rot_supp` | `five_card_ideal_supp_pow` | N8. |
| `five_card_ideal_point_uniform` | unchanged | States the proposition, names both carriers, no abbreviation. |

### The Kim cut laws, proposed home `instances/kim2025/five_card_models.v`

| Old | New | Reason |
|---|---|---|
| `kim_single_rot_supp` | `kim_single_cut_supp_pow` | N8. `cut` names what is supported, matching `kim_single_cut_distE` in the same file. |
| `kim_centi_rot_supp` | `kim_centi_cut_supp_pow` | Same. |

### The encoding, proposed homes in `instances/denboer1989/`

| Old | New | Reason |
|---|---|---|
| `fc_arrange_count` | `fc_arrange_countE` | A rewriting equation between two `count` expressions. The `E` is the tree's marker for one. Home `five_card_program.v` is right, next to `fc_arrange_size` at `:73`. |
| `den_boer_layout_law` | `den_boer_layout_law_const` | N9. Home `den_boer_encoding.v` is right. |

### The certificate fields and the certificates, proposed home `instances/kim2025/five_card_rows.v`

| Old | New | Reason |
|---|---|---|
| `five_card_sc_close_of_rot_supp` | `five_card_cut_mixing_of_supp_pow` | N3 and N8. `mixing` is the tree's word for a variation distance to an ideal cut, used in `pgl27_word_mixing`, `pgl27_mixing.v`, `s5_mixing.v` and `psl211_mixing.v`, and it is the Tableau surface's own clause word at `pgl27_rows.v:305`. The `_of_` shape is precedented at `security/pgg_mixing.v:939` and `security/pgg_leakage_witness.v:42`. |
| `kim_centi_sc_close` | `kim_centi_cut_mixing` | N3. `cut` distinguishes the group-level distance from the per-position one that `five_card_row_repeated_endpoint_lt` already carries at `five_card_rows.v:488`. |
| `kim_biased_sc_close` | `kim_biased_cut_mixing` | Same. |
| `kim_centi40_sc_close` | `kim_centi_cut_mixing40` | Same, at the constant bound. |
| `kim_biased50_sc_close` | `kim_biased_cut_mixing_exact` | N3 and N7. The number is the exact distance, not a chosen constant. |
| `five_card_biased_sc_b` | `kim_biased_marginal_bound` | N3 and N19. `marginal_bound` is the tree's word for a `ShuffleMarginalBound`, at `pgl27_word_privacy.v:89` and `five_card_exec.v:991`. |
| `kim_centi_bound40` | `kim_centi_marginal_bound40` | Same, numeral kept because 40 is an exponent. |
| `kim_biased_bound50` | `kim_biased_marginal_bound_exact` | N3 and N7. |
| `five_card_biased_sc_Hd` | `kim_biased_sample_cut_witnessE` | N3. `Hd` expands to nothing. The tree's name for this exact shape at this instance is `den_boer_sample_cut_witnessE` at `five_card_exec.v:989`. |
| `five_card_sc_const` | `five_card_static_obs_const` | N3. The carrier is `static_coalition_obs`, and the landed file already names statements about it `five_card_static_obsE` and `five_card_static_obs_indep` at `:234,299`. The exact arm gives `indep` and the spectral arm gives `const` on the same carrier, which is the pairing a reader wants. The cross-instance sibling is `pgl27_word_view_const`, so the two instances would use different heads. That divergence is deliberate here, because `view` at this instance already means `ViewS`, the leakage space's colour tuple, as in `five_card_viewS_indep`. Flagging it for the user's decision. |
| `kim_centi_cert` | unchanged | Matches `pgl27_word_cert`, and `centi` is the family word, matching `kim_centi_family`. |
| `kim_biased_cert` | unchanged | Same. |
| `kim_centi_cert40` | unchanged | Same, at the constant bound. |
| `kim_biased_cert50` | `kim_biased_cert_exact` | N7. |
| `five_card_biased_epsE` | `kim_biased_epsE` | N19. |
| `five_card_biased_exact_le_eps` | `kim_biased_exact_le_eps` | N19. |
| `kim_one_cut_le` | `kim_one_cut_centi_le` | It is `kim_one_cut_centiE` weakened from an equality to an inequality, and the name should say which equation it weakens. |

### The rows and their numbers, proposed home `instances/kim2025/five_card_rows.v`

| Old | New | Reason |
|---|---|---|
| `kim_row_repeated_spectral` | `five_card_row_repeated_spectral_tableau` | N4. |
| `kim_row_biased_spectral` | `five_card_row_biased_ideal_tableau` | N4. `ideal` names the transfer status `IdealFinite` that distinguishes it from the next one. |
| `kim_row_biased_spectral_static` | `five_card_row_biased_spectral_tableau` | N4. This is the one that publishes the manifest's own row, so it takes the plain name. |
| `kim_row_repeated39` | `five_card_row_repeated39` | N4. Matches `pgl27_row_word39`. |
| `kim_row_biased25` | `five_card_row_biased_inv25` | N4 and N7. |
| `kim_reprice39` | `five_card_reprice39` | N4. Matches `pgl27_reprice39`. |
| `kim_reprice25` | `five_card_reprice_inv25` | N7. |
| `fifty_split` | `inv50_split` | N7 and N20. |
| `kim_row_biased_static_rowE` | `five_card_row_biased_spectral_rowE` | Follows the row it is about. |
| `kim_row_biased25_rowE` | `five_card_row_biased_inv25_rowE` | Same. |
| `kim_row_biased_rowE_bad` | `five_card_row_biased_ideal_rowE`, still a `Fail` | N5. |
| `kim_row_repeated_rowE_bad` | `five_card_row_repeated_spectral_rowE`, still a `Fail` | N5. |
| `kim_row_repeated39_bare` | `five_card_row_repeated39_bare` | Prefix only. The `_bare` suffix is correct and matches `pgl27_row_word39_bare`. |
| `kim_row_repeated_published_fields` | `five_card_row_repeated_spectral_publishedE` | Prefix, and the statement is three equations, so `E`. |
| `kim_centi_cert_epsE` | unchanged | Good shape. |
| `kim_centi_cert_eps_lt` | unchanged | Good shape. |
| `kim_biased_cert_epsE` | unchanged | Good shape. |
| `kim_biased_cert_eps_lt2` | unchanged | `lt2` states the number it is below. |
| `kim_centi_cert40_epsE` | unchanged | Good shape. |
| `kim_reprice25_lt2` | `five_card_reprice_inv25_lt2` | N7. |

### Answer to the two questions the remit asks by name

**Is "faithful" right for "a rotation is determined by one image"?** No. See
N1. The action is free at every point, and free plus transitive makes it
regular. Faithful is a different and weaker property, and MathComp uses the
word for that weaker property at `mathcomp/fingroup/action.v:210`.

**Are names built from record field names acceptable?** Not here. See N3. The
one sibling file that fills the same five fields uses domain words for all
four payloads, and the Tableau surface itself uses domain words in its clause
keywords. Field abbreviations also fail the "no project-local abbreviations"
test outright in the case of `sc_Hd`.

---

## 3. Collision and duplication results

### Collision scan

Whole-word Python `\b` scan of all 55 declaration names taken from the five
probe files. `grep -E '[[:<:]]'` was not used, per the remit.

```python
import re, os, json
ROOT='/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc'
PROBE=os.path.join(ROOT,'notes/probes/2026-09-19-kim-spectral-arm')
files=['var_dist_injective_probe.v','five_card_rotation_probe.v',
       'kim_sc_close_probe.v','five_card_sc_const_probe.v',
       'kim_spectral_rows_probe.v']
decl=re.compile(r"^\s*(?:Fail\s+)?(Lemma|Theorem|Definition|Fact|Corollary"
                r"|Remark|Record|Inductive|Notation|Example|Instance)"
                r"\s+([A-Za-z_][A-Za-z0-9_']*)")
names=set()
for f in files:
    for l in open(os.path.join(PROBE,f)):
        m=decl.match(l)
        if m: names.add(m.group(2))

prod=['lib','protocol','groups','security','smc','reconstruct',
      'instances/denboer1989','instances/kim2025','instances/s5',
      'instances/pgl27','instances/psl211','manifest']
def vfiles(dirs, base):
    out=[]
    for d in dirs:
        for r,_,fs in os.walk(os.path.join(base,d)):
            out += [os.path.join(r,f) for f in fs if f.endswith('.v')]
    return out
LIB='/Users/cheng-huiweng/Projects/coq/_opam/lib/coq/user-contrib'
groups_of_files = {
  'production' : vfiles(prod, ROOT),
  'legacy'     : vfiles(['legacy'], ROOT),
  'installed'  : vfiles(['.'], LIB),
  'earlier probes': [p for p in vfiles(['notes/probes'], ROOT)
                     if '2026-09-19-kim-spectral-arm' not in p],
}
pats={n:re.compile(r'\b'+re.escape(n)+r'\b') for n in names}
for label, fs in groups_of_files.items():
    hits={}
    for p in fs:
        txt=open(p,encoding='utf-8',errors='replace').read()
        for n,pat in pats.items():
            for m in pat.finditer(txt):
                hits.setdefault(n,[]).append((p, txt[:m.start()].count('\n')+1))
    print(label, len(fs), 'files ->', hits if hits else 'no hits')
```

Result:

| corpus | files scanned | hits |
|---|---|---|
| production, the twelve `_CoqProject` directories | 133 | none |
| `legacy/` | 62 | none |
| installed, all of `~/Projects/coq/_opam/lib/coq/user-contrib` | 1153 | none |
| earlier probe directories | 345 | `five_card_biased_sc_b` 9 times and `five_card_biased_sc_Hd` twice, all in `notes/probes/2026-09-19-kim-tableau-sampled/kim_biased_arms_probe.v` |

The installed corpus here is wider than the 388 files `STATUS.md` reports,
because I scanned every `.v` under `user-contrib` rather than infotheo and
mathcomp alone. The verdict is the same. The two earlier-probe hits are the
ones `STATUS.md:505-508` already records, and both names are being renamed by
N3 and N19 anyway.

`_opam` sits at `~/Projects/coq/_opam`, one level above the repository. The
switch `~/.opam/infotheo` does not contain infotheo.

### Duplication against the tree and the installed libraries

| new lemma | nearest existing thing | verdict |
|---|---|---|
| `var_dist_fdistmap_supp_inj` | `var_dist_fdistmap_inj` at `security/pgg_collusion_bound.v:73`, and `var_dist_fdistmap` at `:126` | Not a duplicate. The first assumes global injectivity and the second runs the inequality the other way. infotheo's `variation_dist.v` holds only `symmetric_var_dist`, `pos_var_dist`, `def_var_dist` and `leq_var_dist`, and no `fdistmap` lemma at all. |
| `fdistmap_supp` | `fdistmap_eq0` and `fdistmap_neq0` at `infotheo/probability/fdist.v:404,412` | Not a duplicate. Those two are the converse direction, from a preimage to the image. See N10 on the name. |
| `fdistmap_inj_uniform_id` | `fdistmap_inj_uniform` at `security/pgg_collusion_bound.v:572` | Not a duplicate. The existing one concludes `fdist_uniform_supp (f @: setT)` for a map between two types. The new one is its endomap corollary with the conclusion simplified back to `fdist_uniform`. See N21. |
| `card_tnth_count` | nothing | No lemma in mathcomp or infotheo relates `count` on a tuple to the cardinality of the ordinal predicate. Searched `count.*tnth`, `tnth.*count` across `mathcomp/` and `= count ` in `tuple.v`, `fintype.v` and `bigop.v`. |
| `fc_word_eval_pow` | `abelian_word_eval` at `legacy/instances/abelian/abelian_word_collapse.v:177`, `cyclic_word_eval` at `legacy/instances/abelian/pgg_abelian.v:183` | Both are in `legacy/`. The abelian one is strictly more general. See N22. |
| `fc_sigma_pow5` | nothing | No `fc_sigma ^+ 5`, no `#[fc_sigma]` and no order fact for the five-cycle anywhere in the tree. |
| `five_card_ideal_distE` | `five_card_sample_cut_distE` at `instances/kim2025/five_card_exec.v:756` | **Duplicate.** See N2. |
| `five_card_sc_const` | `five_card_viewS_indep` at `five_card_rows.v:270` and `leak_view_set` | Not a duplicate, and `STATUS.md:215-221` gets the reason right. Independence from the conjunction under the joint uniform law does not give equality of two laws at two fixed inputs. |
| `kim_one_cut_le` | `kim_one_cut_centiE` at `five_card_kim.v:661` | A weakening of an existing equality, not a duplicate. See the rename. |

### Reverse-dependency check on the proposed homes

Computed from `.Makefile.rocq.d` by transitive closure over the reverse of the
`.vo` dependency edges.

```python
import re, collections
txt = re.sub(r'\\\n', ' ', open('.Makefile.rocq.d').read())
deps = collections.defaultdict(set)
for line in txt.splitlines():
    if ':' not in line: continue
    lhs, rhs = line.split(':', 1)
    for t in lhs.split():
        if t.endswith('.vo'):
            deps[t] |= {d for d in rhs.split() if d.endswith('.vo') and d != t}
rev = collections.defaultdict(set)
for a, bs in deps.items():
    for b in bs: rev[b].add(a)
def closure(x, g):
    seen, stack = set(), [x]
    while stack:
        for z in g.get(stack.pop(), ()):
            if z not in seen: seen.add(z); stack.append(z)
    return seen
```

| home | reverse-dependants | `psl211_endpoints` in the closure | matches `STATUS.md` |
|---|---|---|---|
| `instances/kim2025/five_card_rows.v` | 0 | no | yes |
| `security/pgg_collusion_bound.v` | 105 | YES | yes |
| `lib/perm_uniform.v` | 107 | YES | yes |
| `instances/denboer1989/five_card_program.v` | 24 | no | yes |
| `instances/denboer1989/five_card_scheme_I5.v` | 20 | no | yes |
| `instances/kim2025/five_card_kim.v` | 20 | no | yes |
| `instances/denboer1989/den_boer_encoding.v` | 16 | no | not listed |
| `instances/kim2025/five_card_exec.v` | 10 | no | yes |
| `instances/kim2025/five_card_models.v` | 9 | no | yes |
| `instances/pgl27/pgl27_word_privacy.v` | 11 | no | not listed |

`five_card_rows.v` has no importer, so `STATUS.md`'s claim about it is
confirmed. `psl211_endpoints` is in the closure of `pgg_collusion_bound.v` and
`perm_uniform.v` only, among the proposed homes, and neither would be edited.
A new file in `lib/` and a new file in `security/` both have an empty closure,
so the `psl211_endpoints` rule does not choose between them. N11 chooses on
other grounds.

Cross-instance dependency check for the `pow2_split` reuse: no file under
`instances/kim2025` or `instances/denboer1989` currently requires any file
under `instances/pgl27`, `instances/psl211` or `instances/s5`. The reuse would
create the first such edge. It pulls in no new file, because all 33 files in
`pgl27_word_privacy.v`'s dependency cone are already inside the 98 in
`five_card_rows.v`'s.

---

## 4. Statement comments: replacement texts

Every replacement is at most 80 columns. Each carries the mathematical fact
first and its place in the five-card argument second, in the domain's own
frame: what a coalition of at most one seat can tell about the two committed
bits, under which cut law, against which ideal.

**C1.** `five_card_rotation_probe.v:34-36`, on `fc_sigma_pow5_eq1`. Fixes N12.

```
(* The fifth power of the five-cycle is the identity, so the order of the
   rotation group divides five. It is what makes the exponent of a cut a
   residue modulo five, and so what lets the exponent be read back from the
   image of a single card position. *)
```

**C2.** `five_card_rotation_probe.v:44-46`, on `fc_sigma_pow_point_inj`. Fixes
N1 and N14.

```
(* Two powers of the five-cycle that agree at one card position are equal:
   the stabiliser of a position in the rotation group is trivial. This is
   the step that carries a statement about the law of one card position
   back to the law of the cut that produced it, which is what the spectral
   arm needs and a per-position marginal bound does not supply. *)
```

**C3.** `five_card_rotation_probe.v:56-58`, on `fc_sigma_pow_ord_inj`. Fixes
N14.

```
(* The five rotation amounts send one card position to five distinct
   positions. It is the injectivity the uniform law on rotation amounts is
   pushed forward along, so one card position read under the ideal cut
   carries the uniform law on positions. *)
```

**C4.** `five_card_rotation_probe.v:85-88`, on `fc_kim_rho_supp_pow`. Fixes
N16.

```
(* Every cut the weighted word shuffle gives mass to is a power of the
   five-cycle, at every word length and every letter weighting. Kim's
   alphabet is the five powers of one five-cycle, so no word shuffle leaves
   the rotation group however long the word is, and every Kim cut law is
   comparable with the uniform rotation law on that group. *)
```

**C5.** `var_dist_injective_probe.v:86-98`. The `false` witness keeps its
comment with one sentence rewritten, and the recorded `Fail` loses its
script narration. Fixes N15.

```
(* At a constant reader the transported distance is not the original one,
   and it fails by the whole distance: two distinct point masses coincide
   on the image. This fixes the boundary the support hypothesis draws. *)
```

For the recorded `Fail`, which stays in the probe and does not land:

```
(* The support hypothesis is not discharged at a constant reader, so the
   transport lemma does not apply there. *)
```

**C6.** `kim_sc_close_probe.v:41-46`, on `five_card_cut_mixing_of_supp_pow`.
Fixes N14.

```
(* A cut law carried by the powers of the five-cycle is within its own
   per-position bound of the uniform rotation law, as a distance on the cut
   group itself. The stabiliser of a card position in the rotation group is
   trivial, so reading one position loses nothing between two laws both
   carried by the rotations, and the number a shuffle certificate states
   about one position is already the group-level number the spectral arm
   asks for. *)
```

**C7.** `kim_sc_close_probe.v:116-118`, on `kim_biased_exact_le_eps`. Fixes
N13.

```
(* The exact one-cut distance of kim_one_cut_centiE, one fiftieth, is below
   the spectral bound the certificate publishes, sqrt 5 over eighty. The
   certificate's number is therefore an overestimate of the distance it
   certifies, and the row is honest rather than tight. *)
```

**C8.** `var_dist_injective_probe.v:109-112`, on `fdistmap_inj_uniform_id`.
Fixes N14 and adds the clause N21 asks for.

```
(* An injective endomap of a finite type leaves the uniform law fixed. It
   is the endomap case of fdistmap_inj_uniform, whose conclusion is uniform
   on the image and which does not simplify back to the uniform law when
   the two types differ. The ideal cut of the five-card instance is uniform
   on the rotations, and one card position of it is read by such an
   endomap, so the ideal cut read at a position is the uniform law a
   marginal bound is stated against. *)
```

**C9.** `five_card_sc_const_probe.v:82-87`, on `five_card_static_obs_const`.

```
(* The privacy threshold is two, so a coalition below it is empty or holds
   one seat. At every such coalition the static endpoint reading of the
   uniform rotation law has the same law at both committed pairs. One seat
   reads one card of a deck whose colour census den Boer's encoding fixes
   at three hearts and two clubs, so the reading cannot separate the pairs.
   This is the invariance field of the spectral certificate, and it is
   exact. It spends no mixing bound. *)
```

**C10.** `five_card_sc_const_probe.v:48-51`, on `den_boer_layout_law_const`.

```
(* The card at a uniformly chosen position has the same law at every
   committed pair. The arrangement moves with the two bits and the colour
   census does not, and this is that census read as a distribution on card
   positions. It is the level at which the spectral arm's two run arguments
   become indistinguishable to a single seat. *)
```

**C11.** `kim_sc_close_probe.v:74-76`, on `kim_centi_cut_mixing`.

```
(* The seven-cut law of Kim's repeated row is within the bundle's own
   spectral number of the uniform rotation law, in variation distance on
   the cut group. This is the mixing field of the spectral certificate for
   that row. The number is the bundle's and no new one is introduced, so
   the row's only inexact quantity is that spectral number. *)
```

### Probe-only sentences, marked

Every line below is acceptable in a probe file and must not travel into a
permanent file.

| location | text |
|---|---|
| `var_dist_injective_probe.v:1-3` | the `PROBE` banner and the `Ledger row S1` line |
| `var_dist_injective_probe.v:19-21` | the banner "What the tree already carries" |
| `var_dist_injective_probe.v:28-29` | the two `Check` commands |
| `var_dist_injective_probe.v:83` | the banner "Mutation: the same equality at a reader that separates nothing" |
| `var_dist_injective_probe.v:97-98` | the script narration, see C5 |
| `var_dist_injective_probe.v:99` | the identifier `var_dist_const_reader_mutation` |
| `var_dist_injective_probe.v:154-157` | the four `Print Assumptions` |
| `five_card_rotation_probe.v:1-3` | banner and `Ledger row S2` |
| `five_card_rotation_probe.v:20` | `From kim_spectral_arm_probe Require Import ...` |
| `five_card_rotation_probe.v:86-88` | "so the support fact below is stated once", see C4 |
| `five_card_rotation_probe.v:148-151` | the four `Print Assumptions` |
| `kim_sc_close_probe.v:1-3` | banner and `Ledger rows S3 and S4` |
| `kim_sc_close_probe.v:23-24` | the two probe `Require Import` lines |
| `kim_sc_close_probe.v:71,86` | the banners "S3: ..." and "S4: ..." |
| `kim_sc_close_probe.v:135-137` | the three `Print Assumptions` |
| `five_card_sc_const_probe.v:1-3` | banner and `Ledger row S5` |
| `five_card_sc_const_probe.v:20-21` | the two probe `Require Import` lines |
| `five_card_sc_const_probe.v:79` | the banner "S5: ..." |
| `five_card_sc_const_probe.v:127-128` | the two `Print Assumptions` |
| `kim_spectral_rows_probe.v:1-3` | banner and `Ledger rows S6, S7 and S8` |
| `kim_spectral_rows_probe.v:26-29` | the four probe `Require Import` lines |
| `kim_spectral_rows_probe.v:42` | "The tying field, restated so this probe stands alone" |
| `kim_spectral_rows_probe.v:54,86,112,158,190,254` | the six banners carrying "S6", "S7", "S8", "form 1" and "form 2" |
| `kim_spectral_rows_probe.v:320-323` | the four `Print Assumptions` |

### Word drift found

| concept | words used in the probe | what the tree uses | ruling |
|---|---|---|---|
| a coordinate in `'I_5` naming a card | "position", "card position", and "seat" in five sentences | `five_card_rows.v` keeps "seat" for a profile index and "card position" for a deck coordinate | N14. Use "card position". |
| a power of `fc_sigma` | "rotation" in prose, "rot" in five identifiers, "pow" in one | `fc_sigma_pow`, `fc_sigma_pow_val`, and "rotation" in prose | N8. Use "rotation" in prose and `pow` in identifiers. Never `rot`, which is MathComp's sequence rotation and is used in that sense in this instance. |
| the group-level distance to the ideal | "close", "sc_close", "distance" | "mixing", in four instance files and in the Tableau surface keyword | N3. Use "mixing". |
| what a coalition computes | "reading" throughout | "reading" in `five_card_rows.v`, `pgl27_rows.v`, `five_card_models.v` | Consistent. No action. |
| the map pushed forward along | "reader" | "reader" in `pgg_collusion_bound.v` and `pgl27_rows.v` | Consistent. No action. |
| the model of the repeated row | "centi" in identifiers, "repeated" in row names | the tree does the same split, family word versus manifest row word | Consistent once N4 is applied. Not consistent as written, because `kim_row_repeated_spectral` and `kim_centi_cert` sit under one prefix. |

### Type honesty

No comment in the five files calls an inequality between reals "privacy". The
closest is `five_card_sc_const_probe.v:82`, which says "Below the privacy
threshold", naming the threshold and not the conclusion, and that is correct.
The strongest sentence in the batch, `kim_spectral_rows_probe.v:140-142`, says
a variation distance here is "the sum of the absolute differences, twice the
total variation distance, so its ceiling is two", which corrects the spec and
is right. `STATUS.md:426-446` separates what the certified statement is from
what it is not, at the right level of care.

---

## 5. Banned vocabulary

Scanned the five `.v` files, `STATUS.md` and
`notes/20260919-kim-spectral-arm-probe-design.md` for `apex`, for `gate`,
`gates`, `gated` and `gating`, and for `posit`, `posits`, `posited` and
`positing`, as whole words with `re` and `\b`, case-insensitive, so that
`negate`, `position`, `propagate`, `composite` and `deposit` do not match.

**Zero hits in all seven files.**

```python
pats={'apex':r'\bapex\w*\b','gate':r'\bgat(e|es|ed|ing)\b',
      'posit':r'\bposit(s|ed|ing)?\b'}
```

---

## 6. SSReflect style

| item | finding |
|---|---|
| bare `auto`, `intuition`, `tauto`, `omega` | none in any of the five files |
| line length | one line over 80 columns, `five_card_sc_const_probe.v:99` at 81. See N17. |
| `by` closing | every proof closes with `by`, `exact:` or `Qed` after a `by` line. No dangling `Focus` or `admit`. |
| generated names | no `rewrite` chain depends on a generated hypothesis name. Every `have` is named, every `case` introduces with an explicit pattern. |
| bullets | none used. The files use `last`, `last first` and the numeric selector `2:` instead. `five_card_rows.v` and `pgl27_rows.v` use no bullets either, so this matches. |
| numeric goal selectors | four uses. Two precedents exist in the tree, `five_card_kim.v:626-627`, in the same proof shape. See N23. |
| `Require Import` ordering | `From HB`, then `Require Import Lia`, then `From mathcomp Require Import zify`, then mathcomp, then infotheo, then `pgg_smc`, then `pgg_reconstruct`. This is `five_card_kim.v:73-85` exactly. `five_card_rows.v:140-153` uses the same order without the first three. Consistent. |
| new imports a landing adds | `Lia`, `zify` and `lra` into `five_card_rows.v`, which has none today. All three are already in the tree. See N26. |
| `Set Implicit Arguments` block | identical in all five files and identical to the tree's. |
| section structure | `Section`/`End` pairs balanced, `Variable R : realType` at the section head, matching `pgg_collusion_bound.v:65` and `five_card_models.v`. |

---

## 7. What a landing plan must carry

1. The renames in section 2, applied before any file is written, because five
   of the names are cited in `STATUS.md`'s own S10 table and in the spec.
2. The comment replacements in section 4, and the removal of every line in the
   probe-only table.
3. A decision on N11, `lib/` against `security/`, and on N20, reuse against
   reproof of `pow2_split`.
4. A decision on N3's last row: `five_card_static_obs_const` here against
   `pgl27_word_view_const` there, which leaves the two instances naming one
   certificate field differently.
5. The N6 work items: the header of `five_card_rows.v` lines 29-50, the
   comments at 383-400 and 469-475, and the fate of
   `five_card_row_repeated_at_manifest_level`.
6. A recompile estimate. Everything instance-specific in `five_card_rows.v`
   costs one file. The S10 spread across six files costs the closures in
   section 3.
