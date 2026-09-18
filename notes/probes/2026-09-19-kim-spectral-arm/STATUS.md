# Can Kim's five-card rows be certified by the existing spectral arm?

Probe of `notes/20260919-kim-spectral-arm-probe-design.md`, 2026-09-19.

Verdict: **both claims hold**. The mixing and invariance fields are proved
for the five-card instance, both Kim rows assemble a `SpectralCert`, and both
`certify SpectralDecay ... |> publish ...` programs elaborate to a
`PublishedRow`. Nothing under `manifest/` needs a new arm. Both manifest rows
do change: under the repository's own definition of `IdealFinite` a
cut-carrier comparison with its base premise discharged is `IdealFinite`, so
the repeated row moves from `Sampled`/`NoModelComparison` and the biased row
from `StaticExecutedOnly`.

This file was rewritten on 2026-09-19 after two independent round-1 audits
returned NO-GO on surface matters. See "Round 1 audits and what changed".

No file under `lib/ protocol/ groups/ security/ smc/ reconstruct/ instances/
manifest/` or the production `_CoqProject` was touched. No `make` was run.
`git status --short` over those paths is empty.

## Ledger

| ID | Verdict | Evidence |
|---|---|---|
| S1 | GO | `var_dist_fdistmap_supp_inj` ends in `Qed`. infotheo carries no `var_dist` lemma about `fdistmap` at all; the repo carries the data processing inequality `var_dist_fdistmap` and its globally injective equality case `var_dist_fdistmap_inj`, both in `security/pgg_collusion_bound.v`. The mutation `var_dist_fdistmap_const_neq` proves the equality FALSE at a constant reader, and the recorded `Fail` shows the lemma's own script leaves the support hypothesis open there. |
| S2 | GO | `fc_sigma_pow5_eq1`, `fc_sigma_pow_point_inj`, `fc_sigma_pow_ord_inj`, `fc_kim_word_eval_powE`, `fc_kim_rho_supp_pow`, `five_card_ideal_supp_pow`, `kim_single_cut_supp_pow`, `kim_centi_cut_supp_pow`, `five_card_ideal_point_uniform`, all `Qed`. One support lemma covers all three cut laws, because all three are the same weighted word shuffle over `fc_kim_gens`. |
| S3 | GO | `kim_centi_cut_mixing` ends in `Qed`, with exactly the `sc_close` field type at `sc_b := scb_bound (kim_security_bundle_centi R)`. |
| S4 | GO | `kim_biased_cut_mixing` ends in `Qed` at the word-length-one bundle. `kim_biased_epsE` gives the number in closed form and `kim_biased_exact_le_eps` compares it with the exact `1 / 50`. |
| S5 | GO | `five_card_static_obs_const` ends in `Qed`, with exactly the `sc_const` field type and no added hypothesis. The reason is the colour census below. |
| S6 | GO | `kim_centi_cert` and `kim_biased_cert` are `MkSpectralCert` applications that typecheck; both row programs elaborate to `PublishedRow`. |
| S7 | GO | Two forms per row, below. `kim_centi_cert_epsE`, `kim_centi_cert_eps_lt`, `kim_biased_cert_epsE`, `kim_biased_cert_eps_lt2`, `kim_centi_cert40_epsE`, `five_card_reprice_inv25_lt2`. |
| S8 | GO | Three recorded `Fail`s, two lemmas reading off the published fields, and one equation between two published rows. The manifest fields a landing changes are listed below, for both rows. |
| S9 | done | Below. |
| S10 | done | Below. Whole-word scan of the 56 declaration names of round 2 over 133 production, 62 legacy and 1153 installed `.v` files: zero hits. |

## Compile table

`ps -axo comm= | grep -E 'rocqworker$'` was empty before and after every
compile. Every compile ran under the perl time and RSS wrapper at an 8000 MB
cap, which never fired. The table is a from-scratch run in dependency order
after deleting the probe's `.vo`.

| file | wall | peak RSS |
|---|---|---|
| `var_dist_injective_probe.v` | 4.26 s | 1.58 GB |
| `five_card_rotation_probe.v` | 4.25 s | 1.62 GB |
| `kim_sc_close_probe.v` | 6.16 s | 1.75 GB |
| `five_card_sc_const_probe.v` | 4.29 s | 1.61 GB |
| `kim_spectral_rows_probe.v` | 11.01 s | 1.77 GB |

About 3 s of every figure is the library `Require` lines. No sentence
approaches the 20 s bug threshold. One sentence takes over 3 s:
`five_card_row_biased_forms_publishedE`, 3.15 s, a `by []` between two
published rows that each contain the executed run. The round-1 figure for
`kim_spectral_rows_probe.v` was 7.72 s; the 3.3 s added are that new
comparison and the two `Fail`s, each of which elaborates a published row
before the kernel rejects the `erefl`.

## S1: the generic lemmas

```coq
Lemma var_dist_le2 (R : realType) (A : finType) (P Q : R.-fdist A) :
  var_dist P Q <= 2%:R.

Lemma var_dist_fdistmap_supp_inj (A B : finType) (f : A -> B)
    (P Q : R.-fdist A) :
  (forall a b : A, (P a != 0) || (Q a != 0) ->
     (P b != 0) || (Q b != 0) -> f a = f b -> a = b) ->
  var_dist (fdistmap f P) (fdistmap f Q) = var_dist P Q.

Lemma var_dist_fdistmap_const_neq (R : realType) :
  var_dist (fdistmap (fun _ : bool => tt) (fdist1 true : R.-fdist bool))
           (fdistmap (fun _ : bool => tt) (fdist1 false))
  <> var_dist (fdist1 true : R.-fdist bool) (fdist1 false).

Lemma fdistmap_neq0_codom (R : realType) (A B : finType) (f : A -> B)
    (P : R.-fdist A) (b : B) :
  fdistmap f P b != 0 -> exists a : A, f a = b.

Lemma fdistmap_inj_uniform_id (R : realType) (A : finType) (n : nat)
    (cA : #|A| = n.+1) (f : A -> A) :
  injective f ->
  fdistmap f (fdist_uniform cA) = fdist_uniform cA :> R.-fdist A.

Lemma card_tnth_count (n : nat) (T : Type) (t : n.-tuple T) (p : pred T) :
  #|[pred k : 'I_n | p (tnth t k)]| = count p t.
```

`var_dist_le2` is the ceiling every number in S7 is compared with. infotheo's
`variation_dist.v` carries four lemmas and none of them bounds `var_dist`
above, so before this probe the ceiling was asserted in prose only; the proof
is six lines and is adapted from the soundness auditor's `A4_var_dist_le2`.

The equality is what the mixing field needs. The data processing inequality runs
from the group to the reading, and a shuffle certificate states its number on
the reading and owes it on the group; only the equality crosses back.

## S2: the rotations

```coq
Lemma fc_sigma_pow5_eq1 : (fc_sigma ^+ 5 = 1)%g.

Lemma fc_sigma_pow_point_inj (s : 'I_5) (j k : nat) :
  (fc_sigma ^+ j)%g s = (fc_sigma ^+ k)%g s ->
  (fc_sigma ^+ j = fc_sigma ^+ k)%g.

Lemma fc_sigma_pow_ord_inj (s : 'I_5) :
  injective (fun k : 'I_5 => (fc_sigma ^+ k)%g s).

Lemma fc_kim_word_eval_powE (L : nat) (w : L.-tuple 'I_5) :
  @word_eval (Gen_PGGTypes fc_kim_gens) L w
  = (fc_sigma ^+ (\sum_(i < L) \val (tnth w i)))%g.

Lemma fc_kim_rho_supp_pow (R : realType) (L : nat) (W : R.-fdist 'I_5)
    (g : {perm 'I_5}) :
  @rho_from_words_weighted R 3 4 L fc_kim_gens W g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.

Lemma five_card_ideal_supp_pow (R : realType) (g : {perm 'I_5}) :
  sa_cut_dist (five_card_sample R) g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.

Lemma five_card_ideal_point_uniform (R : realType) (s : 'I_5) :
  fdistmap (fun g : {perm 'I_5} => g s) (sa_cut_dist (five_card_sample R))
  = fdist_uniform (card_ord 5).

Lemma kim_single_cut_supp_pow (g : {perm 'I_5}) :
  sw_rho_dist (scb_bound (@fc_kim_security_bundle R (1 / 100)
    (kim_centi_lt R) (kim_centi_gt R) (kim_centi_spec R) 1)) g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.

Lemma kim_centi_cut_supp_pow (g : {perm 'I_5}) :
  sw_rho_dist (scb_bound (kim_security_bundle_centi R)) g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.
```

`fc_kim_word_eval_powE` is why one support lemma serves every word length:
Kim's alphabet is the five powers of one five-cycle, so a word of any length
evaluates inside the rotation group. The ideal cut's own support statement
uses `five_card_sample_cut_distE` (`instances/kim2025/five_card_exec.v:756`)
directly; the probe no longer restates that equation under a second name.

## S3 and S4: the distance on the cut group

```coq
Lemma five_card_cut_mixing_of_supp_pow
    (b : ShuffleMarginalBound R (instance_M five_card_algebra)) :
  (forall g : {perm 'I_5}, sw_rho_dist b g != 0 ->
     exists k : nat, g = (fc_sigma ^+ k)%g) ->
  var_dist (sw_rho_dist b) (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps b.

Lemma kim_centi_cut_mixing :
  var_dist (sw_rho_dist (scb_bound (kim_security_bundle_centi R)))
           (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps (scb_bound (kim_security_bundle_centi R)).

Definition kim_biased_marginal_bound
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  scb_bound (@fc_kim_security_bundle R (1 / 100)
               (kim_centi_lt R) (kim_centi_gt R) (kim_centi_spec R) 1).

Lemma kim_biased_cut_mixing :
  var_dist (sw_rho_dist kim_biased_marginal_bound)
           (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps kim_biased_marginal_bound.

Lemma kim_biased_epsE :
  sw_bound_eps kim_biased_marginal_bound = Num.sqrt 5%:R * (1 / 80).

Lemma kim_biased_exact_le_eps :
  1 / 50 <= sw_bound_eps kim_biased_marginal_bound :> R.
```

The per-row lemmas carry no hypothesis, so they have exactly the `sc_close`
field type. The generic lemma's hypothesis is discharged by S2 before the
field is filled.

## S5: the colour census and the invariance field

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
Lemma fc_arrange_countE (a b : bool) (p : pred bool) :
  count p (fc_arrange a b) = count p [:: true; true; true; false; false].

Lemma den_boer_layout_law_const (x x' : bool * bool) :
  fdistmap (tnth (den_boer_layout x)) (fdist_uniform (card_ord 5))
  = fdistmap (tnth (den_boer_layout x')) (fdist_uniform (card_ord 5))
  :> R.-fdist 'I_5.

Lemma five_card_static_obs_const
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
`den_boer_layout_law_const` closes it.

**`five_card_viewS_indep` and `leak_view_set` do not already imply this.**
They state independence of the coalition's reading from the conjunction
`a && b` under the joint uniform sample, one distribution over inputs and
rotations together. `sc_const` compares two laws at two FIXED inputs, with the
input no longer random. Independence from the conjunction would still permit
the three inputs with `a && b = false` to give three different readings.
`den_boer_layout_law_const` is exactly the missing content.

## S6: the certificates and the programs

```coq
Definition kim_centi_cert (R : realType) (idx : unit)
  : SpectralCert (amf_sample kim_centi_family R idx) :=
  @MkSpectralCert R five_card_algebra five_card_params
    (amf_sample kim_centi_family R idx)
    (scb_bound (kim_security_bundle_centi R))
    (esym (kim_centi_cut_distE R))
    (sa_cut_dist (five_card_sample R))
    (@kim_centi_cut_mixing R)
    (@five_card_static_obs_const R).

Definition five_card_row_repeated_spectral_tableau : PublishedRow :=
  five_card_committed
    sample kim_centi_family
    certify SpectralDecay kim_centi_cert
    |> publish IdealFinite BaselineClassicalOnly.

Definition five_card_row_biased_ideal_tableau : PublishedRow :=
  five_card_committed
    sample kim_biased_family
    certify SpectralDecay kim_biased_cert
    |> publish IdealFinite BaselineClassicalOnly.
```

`kim_biased_cert` is the same shape at `kim_biased_marginal_bound`,
`kim_biased_sample_cut_witnessE` and `kim_biased_cut_mixing`.

## S7: the numbers, in two forms per row

A variation distance here is infotheo's `var_dist`, the sum of the absolute
differences, which is twice the total variation distance. Its ceiling is
**2**, not 1, and `var_dist_le2` proves it. The spec's "trivial ceiling 1" is
wrong and every number below is compared with 2 on the strength of that
lemma.

### Repeated row, form 1: the bundle's own number

```coq
Lemma kim_centi_cert_epsE (idx : unit) :
  cert_eps (kim_centi_cert R idx)
  = Num.sqrt 5%:R * (1 / 80) ^+ 7 + Num.sqrt 5%:R * (1 / 80) ^+ 7.

Lemma kim_centi_cert_eps_lt (idx : unit) :
  cert_eps (kim_centi_cert R idx) < 2%:R ^- 39.
```

What a reader of this row sees as its bound is the spectral expression
`2 * sqrt 5 * (1/80)^7`, about `1.6e-13`, far below the ceiling `var_dist_le2`
gives. To write
"2^-39" a paper would have to cite `kim_centi_cert_eps_lt` beside the row,
because the row's own published number is the expression and not the
constant.

### Repeated row, form 2: the number written as a constant

```coq
Definition kim_centi_marginal_bound40 (R : realType)
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  @MkShuffleMarginalBound R FiveCardKim_M 7 (2%:R ^- 40)
    (sw_rho_dist (scb_bound (kim_security_bundle_centi R)))
    (fun s => Order.POrderTheory.ltW (kim_deal_centi_lt R s)).

Lemma kim_centi_cert40_epsE (R : realType) (idx : unit) :
  cert_eps (kim_centi_cert40 R idx) = 2%:R ^- 40 + 2%:R ^- 40 :> R.
Proof. by []. Qed.

Definition five_card_reprice39 : Reprice := fun R => Some (2%:R ^- 39 : R).

Definition five_card_row_repeated39 : PublishedRowAt five_card_reprice39 :=
  five_card_committed
    ;;; sample_step of kim_centi_family
    ;;; certify_spectral of kim_centi_cert40
    ;;; conclude five_card_reprice39 of (fun R _ => five_card_pow2_39_split R)
    ;;; publish BaselineClassicalOnly of IdealFinite.
```

This is the PGL(2,7) shape. The epsilon is SET to `2%:R^-40`, the
per-card-position field is the tree's own `kim_deal_centi_lt` weakened by
`ltW`, `cert_eps` is two copies of `2^-40` by conversion with no arithmetic,
and the row republishes at `2^-39` through `five_card_pow2_39_split`, a local
one-line `Fact` proved by `rewrite [RHS]splitr exprSr invfM`. That identity is
`pow2_split` of `instances/pgl27/pgl27_word_privacy.v:180`, reproved here
rather than imported: importing it would create the first dependency from
`instances/kim2025` on `instances/pgl27` in the tree, and the coordinator
chose to keep the two instance directories independent. Reusing `pow2_split`
remains open to the user; the build cost of the edge is zero, because the 33
files in `pgl27_word_privacy.v`'s cone are already inside the 98 in
`five_card_rows.v`'s, and the cost is architectural only.

What a reader of this row sees as its bound is `2^-39` itself, and the paper
cites no lemma outside the program. The mutation `pgl27_rows.v` records
carries over: `conclude five_card_reprice39 of five_card_pow2_39_split`
without the `fun R _ =>` is a recorded `Fail`.

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

`sqrt 5 / 40`, about `0.0559`, against the ceiling 2 of `var_dist_le2`. Weak
but not vacuous.

### One-cut row, form 2: the exact number

`kim_one_cut_centiE` is an EQUALITY, so the marginal bound record can carry
the exact one-cut distance rather than the spectral one.

```coq
Lemma kim_one_cut_centi_le (R : realType) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
              (@rho_from_words_weighted R 3 4 1 fc_kim_gens
                 (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R))))
           (fdist_uniform (card_ord 5)) <= 1 / 50 :> R.

Definition kim_biased_marginal_bound_exact (R : realType)
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  @MkShuffleMarginalBound R FiveCardKim_M 1 (1 / 50)
    (@rho_from_words_weighted R 3 4 1 fc_kim_gens
       (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R)))
    (fun s => kim_one_cut_centi_le R s).

Fact five_card_inv50_split (R : realType) : (1 / 50 : R) + 1 / 50 = 1 / 25.
Proof. by lra. Qed.

Definition five_card_reprice_inv25 : Reprice := fun R => Some (1 / 25 : R).

Definition five_card_row_biased_inv25 : PublishedRowAt five_card_reprice_inv25 :=
  five_card_committed
    ;;; sample_step of kim_biased_family
    ;;; certify_spectral of kim_biased_cert_exact
    ;;; conclude five_card_reprice_inv25 of (fun R _ => five_card_inv50_split R)
    ;;; publish BaselineClassicalOnly of IdealFinite.

Lemma five_card_reprice_inv25_lt2 (R : realType) : (1 / 25 : R) < 2%:R.
```

The reprice to `1 / 25` goes through, and the identity is as cheap as
`five_card_pow2_39_split`: one `lra` line. `cert_eps` is `1/50 + 1/50` by
conversion. What a reader of this row sees as its bound is `1 / 25 = 0.04`,
against the ceiling 2 of `var_dist_le2`, and the paper cites nothing outside
the program. `lra` is already used in the tree
(`instances/kim2025/kim_input_privacy.v:29`,
`instances/denboer1989/five_card_leakage.v:29`), so form 2 adds no new
dependency.

Form 2 is strictly better for the one-cut row: the number is the exact
distance rather than a spectral overestimate `sqrt 5 / 80 = 0.02795`, and
`kim_biased_exact_le_eps` records that the overestimate is the larger of
the two.

## S8: the rows against the manifest

No spectral program publishes a manifest row as the manifest stands, and that
is the honest outcome for both rows.

The status vocabulary decides it. `manifest/pgg_analysis_status.v:63-73`
defines `IdealFinite` as a public model-transfer theorem covering "a
cut-carrier transfer whose base premise is discharged", and says
`StaticExecutedOnly` and `NoModelComparison` "carry no such theorem, and the
manifest row of such a path names the absent premise instead".
`manifest/pgg_analysis_manifest.v:741-744` states the same criterion in the
manifest's own words for the `pgl27_row_word` precedent: `word_mixing`
"supplies the base-distribution bound the generic transfer inequality needs on
the cut carrier itself, which is what makes the transfer status `IdealFinite`
rather than merely `StaticExecutedOnly`". A `SpectralCert` is exactly that:
`sc_ideal` names the ideal, the mixing field is the distance on the cut
carrier, and the invariance field is what makes the ideal usable. Both Kim
rows carry one, so both are published at `IdealFinite`.

Recorded `Fail`s:

- `five_card_row_biased_ideal_rowE`: the one-cut row at `IdealFinite` against
  the manifest's `five_card_row_biased`, which records `StaticExecutedOnly`.
- `five_card_row_biased_inv25_rowE`: the repriced one-cut row, same reason.
- `five_card_row_repeated_spectral_rowE`: the repeated row, whose manifest row
  records `Sampled` with `NoModelComparison` beside it.

What the two programs publish:

```coq
Lemma five_card_row_repeated_spectral_publishedE :
  apr_completion (published_row five_card_row_repeated_spectral_tableau)
    = AnalysisBridged
  /\ apr_transfer (published_row five_card_row_repeated_spectral_tableau)
     = IdealFinite
  /\ apr_assumptions (published_row five_card_row_repeated_spectral_tableau)
     = BaselineClassicalOnly.

Lemma five_card_row_biased_ideal_publishedE :
  apr_completion (published_row five_card_row_biased_ideal_tableau)
    = AnalysisBridged
  /\ apr_transfer (published_row five_card_row_biased_ideal_tableau)
     = IdealFinite
  /\ apr_assumptions (published_row five_card_row_biased_ideal_tableau)
     = BaselineClassicalOnly.
```

`publish` always builds a row at `AnalysisBridged`
(`manifest/pgg_tableau.v:691`), so no choice of transfer status makes a
published row equal `five_card_row_repeated` while that row records `Sampled`.

### A row equation carries no security content

`AnalysisPathRow` (`manifest/pgg_analysis_manifest.v:707-725`) has five fields
and none is a `Prop`; the record "stores no theorem" (`:702`). The probe
records the consequence directly:

```coq
Lemma five_card_row_biased_forms_publishedE :
  published_row five_card_row_biased_ideal_tableau
  = published_row five_card_row_biased_inv25.
Proof. by []. Qed.
```

Two certificates carrying two different published numbers, `sqrt 5 / 40` and
`1 / 25`, publish one row. An `erefl` between a program's row and a manifest
row therefore compares descriptive metadata and settles nothing about either
certificate, and in particular cannot decide which transfer status is honest.

Round 1 of this probe carried a third biased program published at
`StaticExecutedOnly`, and used the `erefl` that program made close to
conclude that the biased row needed no manifest change. That conclusion was
false under the repository's own definition of `IdealFinite`. The program and
its `rowE` are deleted, and `five_card_row_biased_forms_publishedE` is the one
declaration kept in their place, for the fact it does establish.

### What a landing changes

Manifest rows, in `manifest/pgg_analysis_manifest.v`:

| row | manifest today | after a spectral landing | fields to change |
|---|---|---|---|
| `five_card_row_biased` (`:766-768`) | `AnalysisBridged`, `StaticExecutedOnly`, `BaselineClassicalOnly` | `AnalysisBridged`, `IdealFinite`, `BaselineClassicalOnly` | `apr_transfer`, and the docstring at `:760-765`, which explains the row's level by `colour_view_leak_bound` and names no ideal |
| `five_card_row_repeated` (`:776-778`) | `Sampled`, `NoModelComparison`, `BaselineClassicalOnly` | `AnalysisBridged`, `IdealFinite`, `BaselineClassicalOnly` | `apr_completion`, `apr_transfer`, and the docstring at `:770-775`, which explains the level by `endpoint_bound` and `deal_centi_lt` |

Declarations and prose in `instances/kim2025/five_card_rows.v` that a landing
breaks or makes false. The first is a compile breakage; the rest are prose.

1. `five_card_row_repeated_at_manifest_level` (`:456-458`) ascribes the
   `Sampled` program at `Tableau (apr_completion five_card_row_repeated)`.
   Moving that manifest row to `AnalysisBridged` makes the ascription fail to
   typecheck. It must be deleted or restated against the new row.
2. The header sentence at `:29-33`, that both Kim rows stop at `Sampled`,
   becomes obsolete.
3. The header sentence at `:39-42`, that the spectral arm "asks for a
   variation distance to an ideal cut on the shuffle group together with the
   constancy of a coalition's reading of that ideal, and neither of those is
   proved at this instance", becomes false. Both are now proved.
4. The header paragraph at `:42-50`, which explains the biased row's gap as
   "the manifest's criterion met by a theorem no arm takes" and compares it
   with `s5_row_word`, becomes obsolete for the biased row. It stays correct
   for S5 itself, where the invariance field is false for a reason no proof
   removes (`instances/s5/s5_rows.v:60-72`).
5. The docstring of `five_card_row_repeated_tableau` (`:383-389`), ending "so
   no security payload follows it", becomes false.
6. The docstring of `five_card_row_biased_tableau` (`:396-400`), which says
   neither arm takes a bound of the kind the row has, becomes false.
7. `five_card_row_biased_levelE` (`:460-464`) stays true, since only the
   biased row's transfer status changes and its completion level is already
   `AnalysisBridged`; its docstring describes a level gap and stays accurate
   for the `Sampled` program, but should say that the gap it describes is
   about the program and not about the manifest's transfer status.
8. The recorded `Fail five_card_row_biased_at_manifest_level` (`:469-475`)
   stays a `Fail`, because `five_card_row_biased_tableau` still reaches only
   `Sampled`. Its prose reads as a statement about the biased path rather
   than about one program and becomes misleading.

Every other theorem in that file stays true:
`five_card_row_repeated_endpoint_lt`, `kim_centi_small`,
`five_card_row_biased_leak_bound`, `five_card_row_uniform_tableau` and its
`rowE`, `five_card_exact_view_secrecy`, the three `prefixE` and two `modelE`
lemmas, `five_card_committed_paramsE`, and the recorded
`Fail five_card_row_s5_family`.

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

Two remarks belong beside that sentence. The two run arguments range over all
four committed pairs, so the statement does cover pairs with different values
of the conjunction. And `sa_cut_dist sa` is the cut marginal with the input
pinned outside it, so the statement reads as a conditional law given the input
only because `kim_input_dist` is a product
(`instances/kim2025/kim_input_privacy.v:58-60`); that is a property of these
two adapters and not of the arm.

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

The subject-matter home of the generic distribution lemmas is
`security/pgg_collusion_bound.v`, which already holds `var_dist_fdistmap` and
`var_dist_fdistmap_inj`. That file is below `psl211_endpoints`, so the rule
forbids it. The proposal is a NEW file that nothing else requires, whose
reverse closure is empty by construction.

That new file goes in `lib/`, not `security/`. Every file in `security/` is
named `pgg_*` and holds a PGG-specific security layer; `lib/` is where the
tree puts extensions to the underlying libraries, and its files carry no
prefix (`perm_uniform.v`, `perm_exchange.v`, `proba_entropy_ext.v`,
`support_posterior.v`, `mutual_info_recoding.v`). All the inhabitants below
are library-level facts with no PGG content. A new file has an empty reverse
closure wherever it is put, so the `psl211_endpoints` rule does not choose
between the two directories; both directories are covered by a `-R` line in
`_CoqProject`, so no `_CoqProject` edit is needed either way. The permanent
file should not require `pgg_collusion_bound.v`: the probe does so only for
two `Check` lines, and dropping that keeps the new file at mathcomp plus
infotheo. `card_tnth_count` is a tuple and fintype fact with no distribution
in it and cannot honestly live in a file named after `var_dist`, so it goes
either in a `lib/` file whose name covers it or local to
`den_boer_encoding.v`, where its only consumer is.

Two homes, and nothing else. The generic lemmas go in one new `lib/` file;
everything instance-specific goes in `instances/kim2025/five_card_rows.v`.

| lemma | proposed permanent name | proposed home |
|---|---|---|
| the ceiling of a variation distance | `var_dist_le2` | new `lib/var_dist_supp.v` |
| support-injective transport | `var_dist_fdistmap_supp_inj` | same |
| its mutation witness | `var_dist_fdistmap_const_neq` | same |
| pushforward support | `fdistmap_neq0_codom` | same |
| uniform fixed by an injective endomap | `fdistmap_inj_uniform_id` | same |
| tuple positions counted | `card_tnth_count` | `lib/`, in a file whose name covers it, or local to `den_boer_encoding.v` |
| `fc_sigma ^+ 5 = 1` | `fc_sigma_pow5_eq1` | `instances/kim2025/five_card_rows.v` |
| two powers agreeing at one card position are equal | `fc_sigma_pow_point_inj` | same |
| the exponent reader is injective | `fc_sigma_pow_ord_inj` | same |
| the deck census | `fc_arrange_countE` | same |
| word evaluates to a power | `fc_kim_word_eval_powE` | same |
| the word law's support | `fc_kim_rho_supp_pow` | same |
| the ideal law's support | `five_card_ideal_supp_pow` | same |
| one card position of the ideal law is uniform | `five_card_ideal_point_uniform` | same |
| the two Kim supports | `kim_single_cut_supp_pow`, `kim_centi_cut_supp_pow` | same |
| one-position card law is input-free | `den_boer_layout_law_const` | same |
| the generic distance transfer | `five_card_cut_mixing_of_supp_pow` | same |
| the two mixing fields | `kim_centi_cut_mixing`, `kim_biased_cut_mixing` | same |
| the invariance field | `five_card_static_obs_const` | same |
| the two reprice identities | `five_card_pow2_39_split`, `five_card_inv50_split` | same |
| the bounds and the certificates | `kim_biased_marginal_bound`, `kim_biased_sample_cut_witnessE`, `kim_centi_marginal_bound40`, `kim_biased_marginal_bound_exact`, `kim_centi_cert`, `kim_biased_cert`, `kim_centi_cert40`, `kim_biased_cert_exact` | same |
| the rows and the numbers | `five_card_row_repeated_spectral_tableau`, `five_card_row_biased_ideal_tableau`, `five_card_row_repeated39`, `five_card_row_biased_inv25`, and their `epsE`, `eps_lt`, `publishedE` and `rowE` declarations | same |

The lemmas the round-1 table sent to `five_card_program.v`, `five_card_kim.v`,
`five_card_exec.v`, `five_card_models.v` and `den_boer_encoding.v` are all in
`five_card_rows.v` above. That home is chosen for the recompile cost, which
this makes honest: `five_card_rows.v` has no reverse-dependants, the new
`lib/` file has none by construction, and `manifest/pgg_analysis_manifest.v`,
which a landing must also edit, has five. So a landing recompiles three files
plus those five, and no figure in the reverse-dependency table above applies
to it. The round-1 text spread thirteen declarations over six files with
reverse-dependency counts of 24, 20, 20, 16, 10 and 9 while claiming the cost
of one file; that claim is withdrawn.

`five_card_ideal_distE` has no row here. It is
`instances/kim2025/five_card_exec.v:756` `five_card_sample_cut_distE` after
unfolding `five_card_sample_cut_dist`, and the probe now uses that lemma at
both its call sites.

Collision scan, rerun after the round-2 renames: whole-word Python `\b`
search of the 56 declaration names now in the five files, over the 133 `.v`
files of `lib protocol groups security smc reconstruct instances manifest`,
the 62 under `legacy/`, and all 1153 `.v` files under
`_opam/lib/coq/user-contrib`. Zero hits in all three corpora. The two round-1
names that collided with the earlier probe
`notes/probes/2026-09-19-kim-tableau-sampled/`, `five_card_biased_sc_b` and
`five_card_biased_sc_Hd`, are renamed by N3 and N19 and no longer exist
here.

## What the spec got wrong

1. "the trivial ceiling 1 of a variation distance". infotheo's `var_dist` is
   the L1 sum, twice the total variation distance, so the ceiling is 2.
2. S1 asks for an on-support equality and suggests that a one-directional
   `<=` might suffice. The tree's `<=` is the data processing inequality and
   runs the wrong way for `sc_close`; the equality is needed, not a bound.
3. S2 suggests separate support statements for the three cut laws. One
   statement at arbitrary word length and arbitrary letter weights covers all
   three, because all three are `rho_from_words_weighted` over `fc_kim_gens`.
4. S8 expects both rows to need manifest changes. It is right. Round 1 of
   this probe answered that the biased row needed none, on the strength of an
   `erefl` between two row records; that answer was wrong, and the S8 section
   above gives the reason and the corrected change list.
5. The decomposition probe the method allows was not needed. Every lemma ends
   in `Qed`; no `Admitted`, `Abort`, `Axiom` or `admit` occurs in any of the
   five files.

## Assumptions

`Print Assumptions` on `var_dist_le2`, `var_dist_fdistmap_supp_inj`,
`fdistmap_inj_uniform_id`, `var_dist_fdistmap_const_neq`,
`fc_kim_rho_supp_pow`, `five_card_ideal_point_uniform`,
`kim_centi_cut_supp_pow`, `kim_centi_cut_mixing`, `kim_biased_cut_mixing`,
`kim_biased_exact_le_eps`, `den_boer_layout_law_const`,
`five_card_static_obs_const`, `five_card_row_repeated_spectral_tableau`,
`five_card_row_biased_ideal_tableau`, `five_card_row_repeated39` and
`five_card_row_biased_inv25` reports the three boolp axioms and nothing else:

    propositional_extensionality
    functional_extensionality_dep
    constructive_indefinite_description

`fc_sigma_pow_point_inj` and `card_tnth_count` are closed under the global
context. Eighteen `Print Assumptions` commands run across the five files, five
in `var_dist_injective_probe.v`, four in `five_card_rotation_probe.v`, three
in `kim_sc_close_probe.v`, two in `five_card_sc_const_probe.v` and four in
`kim_spectral_rows_probe.v`, and no other axiom appears in any of them.

## Round 1 audits and what changed

Round 1 of this probe was audited twice on 2026-09-19, once for names, homes
and statement comments (`naming-audit.md`, findings N1-N27) and once for
soundness (`soundness-audit.md`, findings F1-F9). Both returned NO-GO on
surface matters; neither disputed the mathematics. Round 1's five `.v` files
and this file are kept verbatim in `history/`, suffixed
`.2026-09-19-before-fix`. `rename_map.tsv` is the machine-readable record of
every identifier that changed, one `old<TAB>new` line each, with `-` as the
new name for a deletion.

What changed, by finding.

| finding | what was applied |
|---|---|
| N1 | `fc_rot_pow_faithful` is `fc_sigma_pow_point_inj`. The statement is triviality of the stabiliser of one card position, not MathComp's `faithful`, and not regularity. |
| N2 | `five_card_ideal_distE` is deleted. Both call sites use `five_card_sample_cut_distE` through a `have` with the unfolded type. |
| N3 | The eight identifiers built from `SpectralCert` field abbreviations carry domain words: `mixing` for a variation distance to an ideal cut, `marginal_bound` for a `ShuffleMarginalBound`, `sample_cut_witnessE` for the tying equation, `static_obs_const` for the invariance field. |
| N4 | The five row programs are `five_card_row_*`, matching the three programs already in `five_card_rows.v`. |
| N5 | The `_bad` suffix is gone. A recorded `Fail` is named after what is attempted. |
| N6, F3 | The landing change list in S8 is rewritten and now carries both manifest rows, the compile breakage at `five_card_rows.v:456`, and every header and docstring passage a landing makes false. |
| N7 | Reciprocals are spelled: `kim_biased_marginal_bound_exact`, `five_card_reprice_inv25`, `five_card_row_biased_inv25`, `five_card_inv50_split`. A numeral suffix now means an exponent of two in every name that carries one. |
| N8, N18 | `pow` replaces `rot` in every identifier, since `rot` is MathComp's sequence rotation and is used in that sense in this instance. Kim's objects take the `fc_kim_` prefix. |
| N9 | `den_boer_layout_law_const`. |
| N10 | `fdistmap_supp` is `fdistmap_neq0_codom`. |
| N11 | The generic lemmas go to a new `lib/var_dist_supp.v`, not to `security/`. See S10. |
| N12, F6 | The comment on `fc_sigma_pow5_eq1` claims order dividing five and no longer that the cut group has exactly five elements. |
| N13, F5 | The comment on `kim_biased_exact_le_eps` names the two numbers instead of pointing at a file header that does not exist. |
| N14 | "card position" everywhere the object is an `'I_5` in a marginal bound. "seat" is kept for an index of `pi_starts`. |
| N15, N16 | Proof-script narration and the positional pointer "below" are gone from the statement comments. |
| N17 | The one 81-column line is broken. |
| N19 | `kim_biased_*` for the one-cut model's bound, its epsilon and its distance statement. |
| N20 | The Require of `pgg_smc.pgl27_word_privacy` is removed and the identity is reproved locally as `five_card_pow2_39_split`. See S7, form 2, for what this keeps and what it costs. |
| N21, N22, N23, N24, N26, N27 | Notes, no change asked. The comment on `fdistmap_inj_uniform_id` now says in one clause how it differs from `fdistmap_inj_uniform`, which N21 asks for. |
| F1 | Both biased spectral programs are published at `IdealFinite`. The row equation against the manifest's `five_card_row_biased` is a recorded `Fail` at both, and `five_card_row_biased_ideal_publishedE` states what the published row holds. |
| F2 | `five_card_row_biased_forms_publishedE` states that two certificates with two different published numbers publish one row, and the S8 prose says that a row equation carries no security content. |
| F4 | `var_dist_le2` is proved in `var_dist_injective_probe.v`, adapted from the auditor's `A4_var_dist_le2`. Every "below the ceiling 2" sentence in the comments and in this file now rests on it. |
| F7, F8, F9 | Notes, no change asked. |

### Code changes that are not renames

1. `var_dist_le2` added to `var_dist_injective_probe.v`, with a
   `Print Assumptions` line for it. (F4.)
2. `five_card_ideal_distE` deleted. In `five_card_ideal_supp_pow` and
   `five_card_ideal_point_uniform` the `rewrite five_card_ideal_distE` becomes
   a two-line `have Hid : <unfolded type>. exact: five_card_sample_cut_distE.`
   followed by `rewrite Hid`. The `have` is needed because the library
   lemma's left side is the folded `five_card_sample_cut_dist R` and the goal
   carries `sa_cut_dist (five_card_sample R)`, which `rewrite` does not match.
   (N2.)
3. `five_card_sc_const_probe.v`: `have Hst :` is split over two lines. (N17.)
4. `kim_spectral_rows_probe.v`: the Require of `pgg_smc.pgl27_word_privacy` is
   removed; `five_card_pow2_39_split` is added, with `pow2_split`'s own
   one-line proof; the two uses of `pow2_split` point at it, and the first is
   split over two lines to stay inside 80 columns. (N20.)
5. `kim_spectral_rows_probe.v`: `kim_row_biased_spectral_static` and
   `kim_row_biased_static_rowE` are deleted. (F1, F2.)
6. `kim_spectral_rows_probe.v`: `five_card_row_biased_inv25` publishes at
   `IdealFinite` instead of `StaticExecutedOnly`, and
   `five_card_row_biased_inv25_rowE` becomes a recorded `Fail`. (F1.)
7. `kim_spectral_rows_probe.v`: `five_card_row_biased_ideal_publishedE` and
   `five_card_row_biased_forms_publishedE` are added. (F1, F2.)
8. `kim_spectral_rows_probe.v`: the `Print Assumptions` line for the deleted
   static program names `five_card_row_biased_ideal_tableau` instead.
9. `kim_spectral_rows_probe.v`: five declaration lines that the renames or
   the rewrites pushed past 80 columns are rewrapped, with no change of
   content: the two recorded `Fail`s of the row equations, the statement of
   `five_card_row_repeated_spectral_publishedE`, and the headers of
   `five_card_row_repeated39_bare` and `five_card_row_biased_inv25`.

No proof body was reordered, restructured or golfed, and no declaration moved.

### Audit findings not applied

- **N10, second half.** The audit suggests, as an option, restating
  `fdistmap_neq0_codom`'s conclusion as `b \\in codom f` so that `codomP`
  applies directly. Not applied: the conclusion is used by two proofs through
  a destructuring view, so changing it would edit three proof scripts, which
  is outside a rename pass. The name states the fact either way.
- **N4, one name.** The rename table gives
  `five_card_row_biased_spectral_tableau` to the biased program published at
  `StaticExecutedOnly`, and `five_card_row_biased_ideal_tableau` to the one at
  `IdealFinite`. F1 deletes the first program, so only the second name is
  used and the first appears nowhere.
- **N7 and N20, on `inv50_split`.** The rename table gives `inv50_split`,
  unprefixed. The coordinator's instruction for N20 asks for an
  instance-prefixed name on the identity that replaces `pow2_split`. Both
  identities are therefore prefixed, `five_card_inv50_split` and
  `five_card_pow2_39_split`, so that the two siblings read alike in one file.
- **N3, last row.** The audit flags `five_card_static_obs_const` here against
  `pgl27_word_view_const` there for the user's decision, because the two
  instances would then name one certificate field differently. The audit's own
  name is used and the divergence stands: `view` at this instance already
  means `ViewS`, the leakage space's colour tuple.
- **N24.** The landing target uses `(** ... *)`. The probe keeps `(* ... *)`,
  since the note is about the form a landing takes.
