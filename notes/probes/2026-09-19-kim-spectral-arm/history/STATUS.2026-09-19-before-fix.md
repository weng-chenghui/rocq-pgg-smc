# Can Kim's five-card rows be certified by the existing spectral arm?

Probe of `notes/20260919-kim-spectral-arm-probe-design.md`, 2026-09-19.

Verdict: **both claims hold**. `sc_close` and `sc_const` are proved for the
five-card instance, both Kim rows assemble a `SpectralCert`, and both
`certify SpectralDecay ... |> publish ...` programs elaborate to a
`PublishedRow`. Nothing under `manifest/` needs a new arm.

No file under `lib/ protocol/ groups/ security/ smc/ reconstruct/ instances/
manifest/` or the production `_CoqProject` was touched. No `make` was run.
`git status --short` over those paths is empty.

## Ledger

| ID | Verdict | Evidence |
|---|---|---|
| S1 | GO | `var_dist_fdistmap_supp_inj` ends in `Qed`. infotheo carries no `var_dist` lemma about `fdistmap` at all; the repo carries the data processing inequality `var_dist_fdistmap` and its globally injective equality case `var_dist_fdistmap_inj`, both in `security/pgg_collusion_bound.v`. The mutation `var_dist_const_reader_false` proves the equality FALSE at a constant reader, and the recorded `Fail` shows the lemma's own script leaves the support hypothesis open there. |
| S2 | GO | `fc_sigma_pow5`, `fc_rot_pow_faithful`, `fc_rot_point_inj`, `fc_word_eval_pow`, `rho_words_rot_supp`, `five_card_ideal_rot_supp`, `kim_single_rot_supp`, `kim_centi_rot_supp`, `five_card_ideal_point_uniform`, all `Qed`. One support lemma covers all three cut laws, because all three are the same weighted word shuffle over `fc_kim_gens`. |
| S3 | GO | `kim_centi_sc_close` ends in `Qed`, with exactly the `sc_close` field type at `sc_b := scb_bound (kim_security_bundle_centi R)`. |
| S4 | GO | `kim_biased_sc_close` ends in `Qed` at the word-length-one bundle. `five_card_biased_epsE` gives the number in closed form and `five_card_biased_exact_le_eps` compares it with the exact `1 / 50`. |
| S5 | GO | `five_card_sc_const` ends in `Qed`, with exactly the `sc_const` field type and no added hypothesis. The reason is the colour census below. |
| S6 | GO | `kim_centi_cert` and `kim_biased_cert` are `MkSpectralCert` applications that typecheck; the three row programs elaborate to `PublishedRow`. |
| S7 | GO | Two forms per row, below. `kim_centi_cert_epsE`, `kim_centi_cert_eps_lt`, `kim_biased_cert_epsE`, `kim_biased_cert_eps_lt2`, `kim_centi_cert40_epsE`, `kim_reprice25_lt2`. |
| S8 | GO | One `erefl` equation holds, two are recorded `Fail`s with their errors. The manifest fields a landing changes are listed below. |
| S9 | done | Below. |
| S10 | done | Below. Whole-word scan of 51 new names over 133 production `.v` files and 388 installed infotheo and mathcomp `.v` files: zero hits. |

## Compile table

`ps -axo comm= | grep -E 'rocqworker$'` was empty before and after every
compile. Every compile ran under the perl time and RSS wrapper at an 8000 MB
cap, which never fired. The table is a from-scratch run in dependency order
after deleting the probe's `.vo`.

| file | wall | peak RSS |
|---|---|---|
| `var_dist_injective_probe.v` | 4.38 s | 1.61 GB |
| `five_card_rotation_probe.v` | 4.20 s | 1.66 GB |
| `kim_sc_close_probe.v` | 6.15 s | 1.79 GB |
| `five_card_sc_const_probe.v` | 4.26 s | 1.65 GB |
| `kim_spectral_rows_probe.v` | 7.72 s | 1.82 GB |

About 3 s of every figure is the library `Require` lines. No sentence
approaches the 20 s bug threshold. The two conversion decisions
(`kim_row_biased_static_rowE` and `kim_row_biased25_rowE`, each `by []` over
a published row that contains the executed run) are inside the 7.72 s figure.

## S1: the generic lemmas

```coq
Lemma var_dist_fdistmap_supp_inj (A B : finType) (f : A -> B)
    (P Q : R.-fdist A) :
  (forall a b : A, (P a != 0) || (Q a != 0) ->
     (P b != 0) || (Q b != 0) -> f a = f b -> a = b) ->
  var_dist (fdistmap f P) (fdistmap f Q) = var_dist P Q.

Lemma var_dist_const_reader_false (R : realType) :
  var_dist (fdistmap (fun _ : bool => tt) (fdist1 true : R.-fdist bool))
           (fdistmap (fun _ : bool => tt) (fdist1 false))
  <> var_dist (fdist1 true : R.-fdist bool) (fdist1 false).

Lemma fdistmap_supp (R : realType) (A B : finType) (f : A -> B)
    (P : R.-fdist A) (b : B) :
  fdistmap f P b != 0 -> exists a : A, f a = b.

Lemma fdistmap_inj_uniform_id (R : realType) (A : finType) (n : nat)
    (cA : #|A| = n.+1) (f : A -> A) :
  injective f ->
  fdistmap f (fdist_uniform cA) = fdist_uniform cA :> R.-fdist A.

Lemma card_tnth_count (n : nat) (T : Type) (t : n.-tuple T) (p : pred T) :
  #|[pred k : 'I_n | p (tnth t k)]| = count p t.
```

The equality is what `sc_close` needs. The data processing inequality runs
from the group to the reading, and a shuffle certificate states its number on
the reading and owes it on the group; only the equality crosses back.

## S2: the rotations

```coq
Lemma fc_sigma_pow5 : (fc_sigma ^+ 5 = 1)%g.

Lemma fc_rot_pow_faithful (s : 'I_5) (j k : nat) :
  (fc_sigma ^+ j)%g s = (fc_sigma ^+ k)%g s ->
  (fc_sigma ^+ j = fc_sigma ^+ k)%g.

Lemma fc_rot_point_inj (s : 'I_5) :
  injective (fun k : 'I_5 => (fc_sigma ^+ k)%g s).

Lemma fc_word_eval_pow (L : nat) (w : L.-tuple 'I_5) :
  @word_eval (Gen_PGGTypes fc_kim_gens) L w
  = (fc_sigma ^+ (\sum_(i < L) \val (tnth w i)))%g.

Lemma rho_words_rot_supp (R : realType) (L : nat) (W : R.-fdist 'I_5)
    (g : {perm 'I_5}) :
  @rho_from_words_weighted R 3 4 L fc_kim_gens W g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.

Lemma five_card_ideal_distE (R : realType) :
  sa_cut_dist (five_card_sample R)
  = fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g) (fdist_uniform (card_ord 5)).

Lemma five_card_ideal_rot_supp (R : realType) (g : {perm 'I_5}) :
  sa_cut_dist (five_card_sample R) g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.

Lemma five_card_ideal_point_uniform (R : realType) (s : 'I_5) :
  fdistmap (fun g : {perm 'I_5} => g s) (sa_cut_dist (five_card_sample R))
  = fdist_uniform (card_ord 5).

Lemma kim_single_rot_supp (g : {perm 'I_5}) :
  sw_rho_dist (scb_bound (@fc_kim_security_bundle R (1 / 100)
    (kim_centi_lt R) (kim_centi_gt R) (kim_centi_spec R) 1)) g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.

Lemma kim_centi_rot_supp (g : {perm 'I_5}) :
  sw_rho_dist (scb_bound (kim_security_bundle_centi R)) g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.
```

`fc_word_eval_pow` is why one support lemma serves every word length: Kim's
alphabet is the five powers of one five-cycle, so a word of any length
evaluates inside the cyclic group.

## S3 and S4: the distance on the cut group

```coq
Lemma five_card_sc_close_of_rot_supp
    (b : ShuffleMarginalBound R (instance_M five_card_algebra)) :
  (forall g : {perm 'I_5}, sw_rho_dist b g != 0 ->
     exists k : nat, g = (fc_sigma ^+ k)%g) ->
  var_dist (sw_rho_dist b) (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps b.

Lemma kim_centi_sc_close :
  var_dist (sw_rho_dist (scb_bound (kim_security_bundle_centi R)))
           (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps (scb_bound (kim_security_bundle_centi R)).

Definition five_card_biased_sc_b
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  scb_bound (@fc_kim_security_bundle R (1 / 100)
               (kim_centi_lt R) (kim_centi_gt R) (kim_centi_spec R) 1).

Lemma kim_biased_sc_close :
  var_dist (sw_rho_dist five_card_biased_sc_b)
           (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps five_card_biased_sc_b.

Lemma five_card_biased_epsE :
  sw_bound_eps five_card_biased_sc_b = Num.sqrt 5%:R * (1 / 80).

Lemma five_card_biased_exact_le_eps :
  1 / 50 <= sw_bound_eps five_card_biased_sc_b :> R.
```

The per-row lemmas carry no hypothesis, so they have exactly the `sc_close`
field type. The generic lemma's hypothesis is discharged by S2 before the
field is filled.

## S5: the colour census and the constancy field

Sources, quoted.

- `instances/denboer1989/five_card_program.v:53-54`
  `Definition fc_encode (b : bool) : seq bool := if b then [:: true; false] else [:: false; true].`
- `instances/denboer1989/five_card_program.v:57`
  `Definition fc_negate (cs : seq bool) : seq bool := rev cs.`
- `instances/denboer1989/five_card_program.v:65-66`
  `Definition fc_arrange (a b : bool) : seq bool := fc_negate (fc_encode a) ++ [:: true] ++ fc_encode b.`
- `instances/denboer1989/den_boer_encoding.v:24-25`
  `Definition den_boer_layout (ab : bool * bool) : 5.-tuple 'I_5 := map_tuple encode_bool (fc_arrange_tup ab.1 ab.2).`

The four rows, with `true` = heart:

| committed pair | dealt row | hearts | clubs |
|---|---|---|---|
| `(false, false)` | `[true; false; true; false; true]` | 3 | 2 |
| `(false, true)` | `[true; false; true; true; false]` | 3 | 2 |
| `(true, false)` | `[false; true; true; false; true]` | 3 | 2 |
| `(true, true)` | `[false; true; true; true; false]` | 3 | 2 |

The census is the same at every input and only the arrangement moves.
`(true, true)` is NOT a cyclic rotation of the other three, so
`den_boer_orbit` (`den_boer_encoding.v:42`) does not reach across the two
values of the conjunction; the census does.

```coq
Lemma fc_arrange_count (a b : bool) (p : pred bool) :
  count p (fc_arrange a b) = count p [:: true; true; true; false; false].

Lemma den_boer_layout_law (x x' : bool * bool) :
  fdistmap (tnth (den_boer_layout x)) (fdist_uniform (card_ord 5))
  = fdistmap (tnth (den_boer_layout x')) (fdist_uniform (card_ord 5))
  :> R.-fdist 'I_5.

Lemma five_card_sc_const
    (C : {set 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1}) :
  (#|C| < profile_k (instance_profile five_card_algebra))%N ->
  forall x x' : ex_inputT five_card_params,
    fdistmap (@static_coalition_obs five_card_algebra five_card_params C x)
             (sa_cut_dist (five_card_sample R))
    = fdistmap (@static_coalition_obs five_card_algebra five_card_params C x')
               (sa_cut_dist (five_card_sample R)).
```

The threshold is 2, so the coalition is empty, where the reading is constant
in the cut and the input, or one seat, where the reading factors as
`fill \o tnth (den_boer_layout y) \o (fun g => g i0)`; the last factor carries
the uniform rotation law to the uniform law on card positions and
`den_boer_layout_law` closes it.

**`five_card_viewS_indep` and `leak_view_set` do not already imply this.**
They state independence of the coalition's reading from the conjunction
`a && b` under the joint uniform sample, one distribution over inputs and
rotations together. `sc_const` compares two laws at two FIXED inputs, with the
input no longer random. Independence from the conjunction would still permit
the three inputs with `a && b = false` to give three different readings.
`den_boer_layout_law` is exactly the missing content.

## S6: the certificates and the programs

```coq
Definition kim_centi_cert (R : realType) (idx : unit)
  : SpectralCert (amf_sample kim_centi_family R idx) :=
  @MkSpectralCert R five_card_algebra five_card_params
    (amf_sample kim_centi_family R idx)
    (scb_bound (kim_security_bundle_centi R))
    (esym (kim_centi_cut_distE R))
    (sa_cut_dist (five_card_sample R))
    (@kim_centi_sc_close R)
    (@five_card_sc_const R).

Definition kim_row_repeated_spectral : PublishedRow :=
  five_card_committed
    sample kim_centi_family
    certify SpectralDecay kim_centi_cert
    |> publish IdealFinite BaselineClassicalOnly.

Definition kim_row_biased_spectral_static : PublishedRow :=
  five_card_committed
    sample kim_biased_family
    certify SpectralDecay kim_biased_cert
    |> publish StaticExecutedOnly BaselineClassicalOnly.
```

`kim_biased_cert` is the same shape at `five_card_biased_sc_b`,
`five_card_biased_sc_Hd` and `kim_biased_sc_close`.

## S7: the numbers, in two forms per row

A variation distance here is infotheo's `var_dist`, the sum of the absolute
differences, which is twice the total variation distance. Its ceiling is
**2**, not 1. The spec's "trivial ceiling 1" is wrong and the numbers below
are compared with 2.

### Repeated row, form 1: the bundle's own number

```coq
Lemma kim_centi_cert_epsE (idx : unit) :
  cert_eps (kim_centi_cert R idx)
  = Num.sqrt 5%:R * (1 / 80) ^+ 7 + Num.sqrt 5%:R * (1 / 80) ^+ 7.

Lemma kim_centi_cert_eps_lt (idx : unit) :
  cert_eps (kim_centi_cert R idx) < 2%:R ^- 39.
```

What a reader of this row sees as its bound is the spectral expression
`2 * sqrt 5 * (1/80)^7`, about `1.6e-13`, far below the ceiling 2. To write
"2^-39" a paper would have to cite `kim_centi_cert_eps_lt` beside the row,
because the row's own published number is the expression and not the
constant.

### Repeated row, form 2: the number written as a constant

```coq
Definition kim_centi_bound40 (R : realType)
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  @MkShuffleMarginalBound R FiveCardKim_M 7 (2%:R ^- 40)
    (sw_rho_dist (scb_bound (kim_security_bundle_centi R)))
    (fun s => Order.POrderTheory.ltW (kim_deal_centi_lt R s)).

Lemma kim_centi_cert40_epsE (R : realType) (idx : unit) :
  cert_eps (kim_centi_cert40 R idx) = 2%:R ^- 40 + 2%:R ^- 40 :> R.
Proof. by []. Qed.

Definition kim_reprice39 : Reprice := fun R => Some (2%:R ^- 39 : R).

Definition kim_row_repeated39 : PublishedRowAt kim_reprice39 :=
  five_card_committed
    ;;; sample_step of kim_centi_family
    ;;; certify_spectral of kim_centi_cert40
    ;;; conclude kim_reprice39 of (fun R _ => pow2_split R)
    ;;; publish BaselineClassicalOnly of IdealFinite.
```

This is the PGL(2,7) shape. The epsilon is SET to `2%:R^-40`, the per-position
field is the tree's own `kim_deal_centi_lt` weakened by `ltW`, `cert_eps` is
two copies of `2^-40` by conversion with no arithmetic, and the row republishes
at `2^-39` through the tree's own `pow2_split`
(`instances/pgl27/pgl27_word_privacy.v:180`), reused and not reproved. What a
reader of this row sees as its bound is `2^-39` itself, and the paper cites no
lemma outside the program. The mutation `pgl27_rows.v` records carries over:
`conclude kim_reprice39 of pow2_split` without the `fun R _ =>` is a recorded
`Fail`, with the error "The term `pow2_split` has type `forall R : realType,
2 ^- 40 + 2 ^- 40 = 2 ^- 39` while it is expected to have type
`RepricePayload kim_reprice39 (...)`".

The price of form 2 is that the row no longer displays the spectral mechanism:
`sqrt 5 * (1/80)^7` is where the bound comes from, and the record that carries
`2^-40` states only the conclusion.

### One-cut row, form 1: the bundle's own number

```coq
Lemma kim_biased_cert_epsE (idx : unit) :
  cert_eps (kim_biased_cert R idx)
  = Num.sqrt 5%:R * (1 / 80) + Num.sqrt 5%:R * (1 / 80).

Lemma kim_biased_cert_eps_lt2 (idx : unit) :
  cert_eps (kim_biased_cert R idx) < 2%:R.
```

`sqrt 5 / 40`, about `0.0559`, against the ceiling 2. Weak but not vacuous.

### One-cut row, form 2: the exact number

`kim_one_cut_centiE` is an EQUALITY, so the marginal bound record can carry
the exact one-cut distance rather than the spectral one.

```coq
Lemma kim_one_cut_le (R : realType) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
              (@rho_from_words_weighted R 3 4 1 fc_kim_gens
                 (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R))))
           (fdist_uniform (card_ord 5)) <= 1 / 50 :> R.

Definition kim_biased_bound50 (R : realType)
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  @MkShuffleMarginalBound R FiveCardKim_M 1 (1 / 50)
    (@rho_from_words_weighted R 3 4 1 fc_kim_gens
       (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R)))
    (fun s => kim_one_cut_le R s).

Fact fifty_split (R : realType) : (1 / 50 : R) + 1 / 50 = 1 / 25.
Proof. by lra. Qed.

Definition kim_reprice25 : Reprice := fun R => Some (1 / 25 : R).

Definition kim_row_biased25 : PublishedRowAt kim_reprice25 :=
  five_card_committed
    ;;; sample_step of kim_biased_family
    ;;; certify_spectral of kim_biased_cert50
    ;;; conclude kim_reprice25 of (fun R _ => fifty_split R)
    ;;; publish BaselineClassicalOnly of StaticExecutedOnly.

Lemma kim_reprice25_lt2 (R : realType) : (1 / 25 : R) < 2%:R.
```

The reprice to `1 / 25` goes through, and the identity is as cheap as
`pow2_split`: one `lra` line. `cert_eps` is `1/50 + 1/50` by conversion. What
a reader of this row sees as its bound is `1 / 25 = 0.04`, against the ceiling
2, and the paper cites nothing outside the program. `lra` is already used in
the tree (`instances/kim2025/kim_input_privacy.v:29`,
`instances/denboer1989/five_card_leakage.v:29`), so form 2 adds no new
dependency.

Form 2 is strictly better for the one-cut row: the number is the exact
distance rather than a spectral overestimate `sqrt 5 / 80 = 0.02795`, and
`five_card_biased_exact_le_eps` records that the overestimate is the larger of
the two.

## S8: the rows against the manifest

Holds today, by conversion:

```coq
Lemma kim_row_biased_static_rowE :
  published_row kim_row_biased_spectral_static = five_card_row_biased.
Proof. by []. Qed.

Lemma kim_row_biased25_rowE :
  published_row kim_row_biased25 = five_card_row_biased.
Proof. by []. Qed.
```

So the **biased row needs no manifest change at all**: the manifest already
records `AnalysisBridged` and `StaticExecutedOnly` for it
(`manifest/pgg_analysis_manifest.v:766-768`), and the spectral program at
`StaticExecutedOnly` publishes that exact row, repriced or not.

Recorded `Fail`s, with the first line of each error:

- `kim_row_biased_rowE_bad`, the same program published at `IdealFinite`:
  "The term `erefl` has type `published_row kim_row_biased_spectral =
  published_row kim_row_biased_spectral` while it is expected to have type
  `published_row kim_row_biased_spectral = five_card_row_biased`". Only the
  transfer status differs.
- `kim_row_repeated_rowE_bad`: "The term `erefl` has type `published_row
  kim_row_repeated_spectral = published_row kim_row_repeated_spectral` while
  it is expected to have type `published_row kim_row_repeated_spectral =
  five_card_row_repeated`".

The fields a landing would have to change, read off the program:

```coq
Lemma kim_row_repeated_published_fields :
  apr_completion (published_row kim_row_repeated_spectral) = AnalysisBridged
  /\ apr_transfer (published_row kim_row_repeated_spectral) = IdealFinite
  /\ apr_assumptions (published_row kim_row_repeated_spectral)
     = BaselineClassicalOnly.
Proof. by []. Qed.
```

| row | manifest today | after a spectral landing | fields to change |
|---|---|---|---|
| `five_card_row_biased` | `AnalysisBridged`, `StaticExecutedOnly`, `BaselineClassicalOnly` | unchanged | none |
| `five_card_row_repeated` | `Sampled`, `NoModelComparison`, `BaselineClassicalOnly` | `AnalysisBridged`, `IdealFinite`, `BaselineClassicalOnly` | `apr_completion` and `apr_transfer` |

`publish` always builds a row at `AnalysisBridged`
(`manifest/pgg_tableau.v:691`), so no choice of transfer status makes a
published row equal `five_card_row_repeated` while that row records `Sampled`.

## S9: what the certified statement is, and what it is not

It IS: for each real field, for every coalition `C` of at most one seat, and
for every two committed pairs `x` and `x'`, the variation distance between the
law of `C`'s static endpoint reading under the row's own cut law at `x` and
the same law at `x'` is at most the row's published number
(`SpectralPropAt`, `manifest/pgg_tableau.v:331`).

It is NOT:

- not independence of the reading from the secret. The exact arm states that
  and the spectral arm does not. `five_card_row_uniform_tableau` keeps the
  independence statement for the uniform model, and Kim's biased models do not
  inherit it.
- not a statement about two or more seats. The bound is conditional on
  `#|C| < 2`.
- not a statement about the full reveal. The landed conditional mutual
  information bound `five_card_colour_view_leak_bound` covers the executed
  colour view and stays where it is; nothing here replaces or weakens it.
- not a claim that the exact arm holds under a biased cut. It does not, and
  the probe asserts nothing of the kind.

## S10: proposed names and homes

Reverse-dependency closures computed from `.Makefile.rocq.d` in Python
(number of `.vo` files that transitively depend on the home; and whether
`instances/psl211/psl211_endpoints.vo` is among them).

| home | reverse-dependants | `psl211_endpoints` in the closure |
|---|---|---|
| `security/pgg_collusion_bound.v` | 105 | **YES** |
| `lib/perm_uniform.v` | 107 | **YES** |
| `reconstruct/algebraic_rigidity.v` | 102 | **YES** |
| `reconstruct/transitivity_privacy.v` | 41 | **YES** |
| `security/pgg_weighted_words.v` | 39 | no |
| `instances/denboer1989/five_card_program.v` | 24 | no |
| `instances/denboer1989/five_card_scheme_I5.v` | 20 | no |
| `instances/kim2025/five_card_kim.v` | 20 | no |
| `instances/kim2025/five_card_exec.v` | 10 | no |
| `instances/kim2025/five_card_models.v` | 9 | no |
| `instances/kim2025/five_card_rows.v` | 0 | no |
| `manifest/pgg_analysis_manifest.v` | 5 | no |

The subject-matter home of the three generic distribution lemmas is
`security/pgg_collusion_bound.v`, which already holds `var_dist_fdistmap` and
`var_dist_fdistmap_inj`. That file is below `psl211_endpoints`, so the rule
forbids it. The proposal is a NEW file that nothing else requires, whose
reverse closure is empty by construction.

| lemma | proposed permanent name | proposed home |
|---|---|---|
| support-injective transport | `var_dist_fdistmap_supp_inj` | new `security/pgg_var_dist_supp.v` |
| its mutation witness | `var_dist_fdistmap_const_neq` | same |
| pushforward support | `fdistmap_supp` | same |
| uniform fixed by an injective endomap | `fdistmap_inj_uniform_id` | same |
| tuple positions counted | `card_tnth_count` | same |
| `fc_sigma ^+ 5 = 1` | `fc_sigma_expg5` | `instances/denboer1989/five_card_scheme_I5.v` |
| a rotation fixed by one image | `fc_sigma_pow_faithful` | same |
| the exponent reader is injective | `fc_sigma_pow_point_inj` | same |
| the deck census | `fc_arrange_count` | `instances/denboer1989/five_card_program.v` |
| word evaluates to a power | `fc_kim_word_eval_powE` | `instances/kim2025/five_card_kim.v` |
| the word law's support | `fc_kim_rho_rot_supp` | same |
| the ideal law as a pushforward | `five_card_ideal_cut_distE` | `instances/kim2025/five_card_exec.v` |
| the ideal law's support | `five_card_ideal_rot_supp` | same |
| one seat of the ideal law is uniform | `five_card_ideal_point_uniform` | same |
| the two Kim supports | `kim_single_rot_supp`, `kim_centi_rot_supp` | `instances/kim2025/five_card_models.v` |
| one-position card law is input-free | `den_boer_layout_law` | `instances/denboer1989/den_boer_encoding.v` |
| the generic distance transfer | `five_card_sc_close_of_rot_supp` | `instances/kim2025/five_card_rows.v` |
| the two `sc_close` fields | `kim_centi_sc_close`, `kim_biased_sc_close` | same |
| the `sc_const` field | `five_card_sc_const` | same |
| the bounds and the certificates | `five_card_biased_sc_b`, `five_card_biased_sc_Hd`, `kim_centi_bound40`, `kim_biased_bound50`, `kim_centi_cert`, `kim_biased_cert`, `kim_centi_cert40`, `kim_biased_cert50` | same |
| the rows and the numbers | `kim_row_repeated_spectral`, `kim_row_biased_spectral_static`, `kim_row_repeated39`, `kim_row_biased25`, and their `epsE`, `eps_lt` and `rowE` lemmas | same |

`instances/kim2025/five_card_rows.v` has no reverse-dependants, so a landing
that keeps everything instance-specific there recompiles one file.

Collision scan: whole-word Python `\b` search of the 51 new names over the
133 `.v` files of `lib protocol groups security smc reconstruct instances
manifest` and the 388 installed infotheo and mathcomp `.v` files under
`_opam/lib/coq/user-contrib`. Zero hits. Two names,
`five_card_biased_sc_b` and `five_card_biased_sc_Hd`, already appear in the
earlier probe `notes/probes/2026-09-19-kim-tableau-sampled/`; no permanent
file uses them.

## What the spec got wrong

1. "the trivial ceiling 1 of a variation distance". infotheo's `var_dist` is
   the L1 sum, twice the total variation distance, so the ceiling is 2.
2. S1 asks for an on-support equality and suggests that a one-directional
   `<=` might suffice. The tree's `<=` is the data processing inequality and
   runs the wrong way for `sc_close`; the equality is needed, not a bound.
3. S2 suggests separate support statements for the three cut laws. One
   statement at arbitrary word length and arbitrary letter weights covers all
   three, because all three are `rho_from_words_weighted` over `fc_kim_gens`.
4. S8 expects both rows to need manifest changes. The biased row needs none:
   the spectral program at `StaticExecutedOnly` publishes the manifest's own
   `five_card_row_biased` by conversion.
5. The decomposition probe the method allows was not needed. Every lemma ends
   in `Qed`; no `Admitted`, `Abort`, `Axiom` or `admit` occurs in any of the
   five files.

## Assumptions

`Print Assumptions` on `var_dist_fdistmap_supp_inj`,
`fdistmap_inj_uniform_id`, `var_dist_const_reader_false`,
`fc_rot_pow_faithful`, `rho_words_rot_supp`, `five_card_ideal_point_uniform`,
`kim_centi_rot_supp`, `kim_centi_sc_close`, `kim_biased_sc_close`,
`five_card_biased_exact_le_eps`, `den_boer_layout_law`, `five_card_sc_const`,
`kim_row_repeated_spectral`, `kim_row_biased_spectral_static`,
`kim_row_repeated39` and `kim_row_biased25` reports the three boolp axioms and
nothing else:

    propositional_extensionality
    functional_extensionality_dep
    constructive_indefinite_description

`fc_rot_pow_faithful` and `card_tnth_count` are closed under the global
context.
