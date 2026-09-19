# Can Kim's five-card rows be certified by the existing spectral arm?

Probe of `notes/20260919-kim-spectral-arm-probe-design.md`, 2026-09-19.

Verdict: **both claims hold**. The mixing and constancy fields are proved
for the five-card instance, both Kim rows assemble a `SpectralCert`, and both
`certify SpectralDecay ... |> publish ...` programs elaborate to a
`PublishedRow`. Nothing under `manifest/` needs a new arm. Both manifest rows
do change: under the repository's own definition of `IdealFinite` a
cut-carrier comparison with its base premise discharged is `IdealFinite`, so
the repeated row moves from `Sampled`/`NoModelComparison` and the biased row
from `StaticExecutedOnly`.

This file was rewritten on 2026-09-19 after two independent round-1 audits
returned NO-GO on surface matters, and revised again the same day after two
round-2 audits returned NO-GO on text alone. No audit in either round
disputed the mathematics. See "Round 1 audits and what changed" and
"Round 2 audits and what changed".

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
| S8 | GO | Three recorded `Fail`s, two lemmas reading off the published fields, and one equation between two published rows. What a landing changes is listed below for both rows: the two manifest row definitions, seven `erefl` pins, five in the manifest and two in the five-card facade, the manifest's Row 4 and Row 5 header tables, the facade's section 7, and the prose of `instances/kim2025/five_card_rows.v`. |
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
`kim_spectral_rows_probe.v` was 7.72 s; of the 3.3 s added, that new
comparison is one part and one new `Fail`,
`five_card_row_biased_inv25_rowE`, is another, each of which elaborates a
published row before the kernel rejects the `erefl`. The other three
recorded `Fail`s existed in round 1 under their round-1 names and account
for none of the added time. The rest is the two lemmas added,
`five_card_row_biased_ideal_publishedE` and
`five_card_row_biased_forms_publishedE`, less the two deleted.

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
above, so before this probe the ceiling was asserted in prose only. The
proof is nine lines between `Proof.` and `Qed.` and is adapted from the
soundness auditor's `A4_var_dist_le2`.

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
`2 * sqrt 5 * (1/80)^7`, about `2.13e-13`, far below the ceiling
`var_dist_le2` gives. To write "2^-39" a paper would have to cite
`kim_centi_cert_eps_lt` beside the row, because the row's own published
number is the expression and not the constant. As an upper bound the
constant is the weaker of the two by a factor of 8.53, which is the "about
eight and a half times weaker" of `soundness-audit.md:338-339`. Both figures
are Python: `2*math.sqrt(5)*(1/80)**7` is `2.1325e-13`, `2.0**-39` is
`1.8190e-12`, and the ratio is `8.5299`. Round 1 printed `1.6e-13` for the
expression, which would have made the ratio `11.37` and left the two records
inconsistent.

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
carrier, and the constancy field is what makes the ideal usable. Both Kim
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

Every line number in this section was read off the source at this revision.
Where the round-2 naming audit and the source disagree, the source wins, and
both places are named where they occur.

#### Manifest rows, in `manifest/pgg_analysis_manifest.v`

| row | manifest today | after a spectral landing | fields to change |
|---|---|---|---|
| `five_card_row_biased` (`:766-768`) | `AnalysisBridged`, `StaticExecutedOnly`, `BaselineClassicalOnly` | `AnalysisBridged`, `IdealFinite`, `BaselineClassicalOnly` | `apr_transfer`; the docstring at `:760-765`, which explains the row's level by `colour_view_leak_bound` and names no ideal; and the `erefl` pin at `:1779-1780` |
| `five_card_row_repeated` (`:776-778`) | `Sampled`, `NoModelComparison`, `BaselineClassicalOnly` | `AnalysisBridged`, `IdealFinite`, `BaselineClassicalOnly` | `apr_completion`, `apr_transfer`; the docstring at `:770-775`, which explains the level by `endpoint_bound` and `deal_centi_lt`; and the `erefl` pins at `:1787` and `:1788-1789` |

#### Compile breakages inside the manifest

The manifest pins each row's three status fields by `erefl` at the end of the
file, and its own header says so at `:67-72`:

> Every identifier in the tables below is checked at the end of this file by
> one Timeout-guarded Check against its spelled type, and every row by one
> Check against AnalysisPathRow together with three erefl pins on its status
> fields. Deleting an alias makes its line fail with a reference-not-found
> message, retyping one makes it fail with a type mismatch and restatusing a
> row makes its pin fail, so the tables cannot drift away from the code.

Three of the six pins on the two Kim rows hold a value a landing moves. A
failing `Check` is a hard error in this file, not a warning.

| where | the pin as the file has it | what a landing makes it |
|---|---|---|
| `:1779-1780` | `Timeout 60 Check`<br>`  (erefl : apr_transfer five_card_row_biased = StaticExecutedOnly).` | `= IdealFinite` |
| `:1787` | `Timeout 60 Check (erefl : apr_completion five_card_row_repeated = Sampled).` | `= AnalysisBridged` |
| `:1788-1789` | `Timeout 60 Check`<br>`  (erefl : apr_transfer five_card_row_repeated = NoModelComparison).` | `= IdealFinite` |

The other three pins on these two rows keep their values and stay as they
are: `apr_completion five_card_row_biased = AnalysisBridged` (`:1777-1778`),
which the landing does not move, and `apr_assumptions` of both rows at
`BaselineClassicalOnly` (`:1781-1782`, `:1790-1791`).

#### The manifest's Row 4 and Row 5 header tables

The manifest states each row twice, once as a `Definition` and once as a
header table in the file's own prose. The header tables are not compiled and
a landing therefore leaves them silently false unless it edits them.

Row 4, the biased row. These lines become false:

| line | text today | why a landing makes it false |
|---|---|---|
| `:301-302` | `bound or certificate \| none; kim_leak_bound is the numeric constant of the bridge theorem, not a shuffle certificate` | the row then carries a `SpectralCert` |
| `:305` | `model transfer \| none claimed` | the certificate's mixing field is the transfer |
| `:306` | `missing premise \| the ideal distribution equality, as in row 3` | the mixing field discharges it on the cut carrier |
| `:308` | `transfer status \| StaticExecutedOnly` | becomes `IdealFinite` |

`:303` `final bridge theorem | FiveCardAnalysis.colour_view_leak_bound`,
`:307` `completion level | AnalysisBridged` and `:310`
`typed row | five_card_row_biased` stay true. The level justification at
`:322-328` stays true as far as it goes: it justifies the completion level
and says nothing about a transfer, so a landing leaves it correct and
incomplete and must add the transfer sentence.

Row 5, the repeated row. These lines become false:

| line | text today | why a landing makes it false |
|---|---|---|
| `:351-354` | `bound or certificate \| FiveCardAnalysis.kim_bundle, centi_bundle, endpoint_bound, deal_centi_lt` | incomplete: the row then also carries a `SpectralCert` |
| `:355` | `final bridge theorem \| NONE` | the certified proposition is the bridge theorem |
| `:357` | `model transfer \| none claimed` | the mixing field is the transfer |
| `:358-360` | `missing premise \| the ideal distribution equality, as in row 3, and in addition no security statement is attached to either model` | false on both halves |
| `:361` | `completion level \| Sampled` | becomes `AnalysisBridged` |
| `:362` | `transfer status \| NoModelComparison` | becomes `IdealFinite` |
| `:374-380` | the level justification, ending `The row is NOT AnalysisBridged. endpoint_bound and deal_centi_lt bound the distance from uniform of ONE seat's endpoint distribution: neither quantifies over a coalition, neither mentions a second secret, and neither has the shape of an indistinguishability or leakage statement.` | the certified proposition quantifies over every coalition below the threshold, compares two committed pairs, and has exactly the shape the paragraph says is absent |

`:364` `typed row | five_card_row_repeated` stays true.

#### The five-card facade's typed transfer statuses

Neither round-2 audit names this file. It states both rows' transfer statuses
a second time, and those statements are pinned by four further `erefl`s, two
in the facade itself and two more inside the manifest.

`instances/kim2025/five_card_analysis.v` declares one typed transfer status
per analysis path:

```coq
(** exec_transfer_status — the transfer status of the two exact-cut paths, the
    uniform one and the single-biased one: they carry their landed static
    results to their executed observers, with no ideal-to-finite theorem. *)
Definition exec_transfer_status : TransferStatus := StaticExecutedOnly.

(** repeated_transfer_status — the transfer status of the repeated-cut path:
    it carries endpoint marginal bounds only. *)
Definition repeated_transfer_status : TransferStatus := NoModelComparison.
```

at `:364` and `:368`, under a section header at `:351-358` which says that
"No transfer-layer result exists for the five-card development ... the
five-card development has no ideal distribution equality to discharge its
second hypothesis, so there is nothing to alias and nothing is manufactured
to fill the section".

What a landing does to this file:

1. The section header at `:351-358` becomes false. The mixing field is the
   cut-carrier bound that discharges the second hypothesis, and the section
   then has a theorem to alias.
2. `exec_transfer_status` is shared by the uniform path and the single-biased
   path, and a landing moves only the biased one. The alias must split in
   two, the uniform path keeping `StaticExecutedOnly`, or the biased row's
   status can no longer be read off the facade at all. Its docstring at
   `:361-363` becomes false in either case, since it says both paths carry
   "no ideal-to-finite theorem".
3. `repeated_transfer_status` becomes `IdealFinite`, and its docstring at
   `:366-367`, "it carries endpoint marginal bounds only", becomes false.
4. The two `erefl` pins at `:433-436` break as soon as the aliases move.
5. Two further `erefl` pins inside the manifest break with them, at
   `:1385-1386` and `:1388-1389`, under a comment at `:1381-1383` saying
   "the five-card facade carries no transfer theorem, so the two typed
   statuses are all there is to check".

So the manifest carries five `erefl` pins a landing touches, not three: the
three row pins break on the manifest edit alone, and the two facade-status
pins break as soon as the facade aliases are retargeted. A landing that edits
the manifest rows and leaves the facade alone compiles green while the tree
states two different transfer statuses for the same path in two files.

`manifest/pgg_analysis_client.v` is safe. Its only mentions of the two rows
are `Check five_card_row_biased.` and `Check five_card_row_repeated.` at
`:149-150`, and of the two statuses `Check FiveCardAnalysis.exec_transfer_status.`
and `Check FiveCardAnalysis.repeated_transfer_status.` at `:48-49`. A bare
`Check` names a term and asserts nothing about its value, so all four survive
a restatusing. The file states no row's level or status in prose.

A whole-tree grep for `five_card_row_biased` and `five_card_row_repeated`
outside the manifest returns `instances/kim2025/five_card_rows.v` and those
two client `Check` lines and nothing else. A grep for the facade's model and
family names, `single_biased_sample`, `repeated_sample`, `centi_sample`,
`biased_family` and `centi_family`, returns their declarations in
`five_card_analysis.v:202-222`, their names in the manifest's Row 4 and Row 5
header tables and row definitions, and one spelled-type `Check` at
`five_card_analysis.v:402`. `five_card_rows.v` uses the underlying
`kim_biased_family` and `kim_centi_family` rather than the facade aliases, so
no name there moves with a restatusing. No file counts or pattern-matches
manifest rows by level or status, and no lemma anywhere states
`apr_completion` or `apr_transfer` of either row except
`five_card_row_biased_levelE`.

#### `instances/kim2025/five_card_rows.v`

Declarations and prose that a landing breaks or makes false. The first is a
compile breakage; the rest are prose.

1. `five_card_row_repeated_at_manifest_level` (`:456-458`) ascribes the
   `Sampled` program at `Tableau (apr_completion five_card_row_repeated)`.
   Moving that manifest row to `AnalysisBridged` makes the ascription fail to
   typecheck. It must be deleted or restated against the new row.
2. The header sentence at `:29-33`, that both Kim rows stop at `Sampled`,
   becomes obsolete. Its second half at `:30-33`, "The repeated row stops
   there because the manifest does", becomes false rather than obsolete,
   since the manifest no longer stops there.
3. The header sentence at `:39-42`, that the spectral arm "asks for a
   variation distance to an ideal cut on the shuffle group together with the
   constancy of a coalition's reading of that ideal, and neither of those is
   proved at this instance", becomes false. Both are now proved.
4. The header paragraph at `:42-50`, which explains the biased row's gap as
   "the manifest's criterion met by a theorem no arm takes" and compares it
   with `s5_row_word`, becomes obsolete for the biased row. It stays correct
   for S5 itself, where the constancy field is false for a reason no proof
   removes (`instances/s5/s5_rows.v:60-72`).
5. The docstring of `five_card_row_repeated_tableau` (`:383-389`), ending "so
   no security payload follows it", becomes false. The round-2 naming audit
   reports this range as `:382-388`; the file has `:383-389` and the range is
   left as it was.
6. The docstring of `five_card_row_biased_tableau` (`:394-400`), which says
   neither arm takes a bound of the kind the row has, becomes false. The
   round-1 range `:396-400` was short by two lines and the round-2 naming
   audit's `:393-399` is off by one in the other direction; `:394-400` is
   what the file has.
7. `five_card_row_biased_levelE` (`:465-467`) stays true, since only the
   biased row's transfer status changes and its completion level is already
   `AnalysisBridged`. Its docstring at `:460-464` describes a level gap and
   stays accurate for the `Sampled` program, but should say that the gap it
   describes is about the program and not about the manifest's transfer
   status.
8. The recorded `Fail five_card_row_biased_at_manifest_level` (`:473-475`)
   stays a `Fail`, because `five_card_row_biased_tableau` still reaches only
   `Sampled`. Its docstring at `:469-472` reads as a statement about the
   biased path rather than about one program and becomes misleading.

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
| `manifest/pgg_analysis_manifest.v` | 7 | no |
| `instances/kim2025/five_card_analysis.v` | 8 | no |
| `instances/denboer1989/den_boer_encoding.v` | 16 | no |
| `instances/pgl27/pgl27_mixing.v` | 20 | no |

The script and its output are below, under "The closure script". The
previous revision gave the manifest five reverse-dependants. It has seven:
the two files the
count missed are `manifest/pgg_tableau.v` and `manifest/pgg_tableau_syntax.v`,
which require the manifest because `publish` builds an `@MkAnalysisPathRow`
(`manifest/pgg_tableau.v:695`). Every other row of the table is confirmed by
the rerun, and `instances/psl211/psl211_endpoints.vo` is in none of the
closures on this page, so the freeze rule is respected by every home
considered here.

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
between the two directories. A landing does add one line to `_CoqProject`
for the new file, whichever directory it goes in. `_CoqProject` carries the
`-R` lines and then enumerates every `.v` file by name, 194 of them, and
`Makefile` regenerates `Makefile.rocq` from it by `rocq makefile -f
_CoqProject`, so a file the `-R` line covers but the enumeration omits is
never built. The `-R` line supplies the logical path and not the build
target. Batch 1 set the precedent with one line for
`reconstruct/dealer_privacy.v`, which `_CoqProject:172` still carries; the
new line goes after the file's dependencies, and the five existing `lib/`
lines are `:30-34`. Regenerating `Makefile.rocq` costs nothing further,
since only out-of-date targets then rebuild. The permanent
file should not require `pgg_collusion_bound.v`: the probe does so only for
two `Check` lines, and dropping that keeps the new file at mathcomp plus
infotheo. `card_tnth_count` is a tuple and fintype fact with no distribution
in it and cannot honestly live in a file named after `var_dist`, so it goes
either in a `lib/` file whose name covers it or local to
`den_boer_encoding.v`, which is where the deck layout it counts is defined.
Its only consumer is `den_boer_layout_law_const`, which is itself new and
which the table below sends elsewhere, so the choice is about subject matter
rather than about reach. It is not free: the recompile figures below hold on
the `lib/` branch, and sending `card_tnth_count` to `den_boer_encoding.v`
instead adds that file and its 16 reverse-dependants to the landing. The two
sets overlap, so the totals go from 9 or 10 to 18 and from 11 to 19, not to
25, 26 and 27. `instances/psl211/psl211_endpoints.vo` is in neither enlarged
set.

The generic lemmas go in one new `lib/` file. Where the instance-specific
lemmas go is an open decision, set out under "The home of the mixing and
constancy theorems" below. The table that follows records the second home as
`instances/kim2025/five_card_rows.v`, which is option 1 there; under option 2
the three theorems marked with a dagger move one file down.

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
| the two mixing fields † | `kim_centi_cut_mixing`, `kim_biased_cut_mixing` | same |
| the constancy field † | `five_card_static_obs_const` | same |
| the two reprice identities | `five_card_pow2_39_split`, `five_card_inv50_split` | same |
| the bounds and the certificates | `kim_biased_marginal_bound`, `kim_biased_sample_cut_witnessE`, `kim_centi_marginal_bound40`, `kim_biased_marginal_bound_exact`, `kim_centi_cert`, `kim_biased_cert`, `kim_centi_cert40`, `kim_biased_cert_exact` | same |
| the rows and the numbers | `five_card_row_repeated_spectral_tableau`, `five_card_row_biased_ideal_tableau`, `five_card_row_repeated39`, `five_card_row_biased_inv25`, and their `epsE`, `eps_lt`, `publishedE` and `rowE` declarations | same |

The lemmas the round-1 table sent to `five_card_program.v`, `five_card_kim.v`,
`five_card_exec.v`, `five_card_models.v` and `den_boer_encoding.v` are all in
`five_card_rows.v` above. The round-1 text spread thirteen declarations over
six files with reverse-dependency counts of 24, 20, 20, 16, 10 and 9 while
claiming the cost of one file; that claim is withdrawn.

### The home of the mixing and constancy theorems

**This one is the user's decision and is not taken here.** Both options are
below with their measured costs.

The three theorems at issue are `kim_centi_cut_mixing`,
`kim_biased_cut_mixing` and `five_card_static_obs_const`. Their statements
mention no manifest type: a mixing statement is
`var_dist (sw_rho_dist b) (sa_cut_dist (five_card_sample R)) <= sw_bound_eps b`
over `algebraic_rigidity` and `pgg_sample_adapter`, and the constancy
statement is an equality of two `fdistmap`s over `pgg_instance`. Both can
therefore sit anywhere at or above `five_card_exec.v`. The certificates and
the row programs cannot: `SpectralCert` and `PublishedRow` live in
`manifest/pgg_tableau.v`, which requires the manifest, so those stay in
`five_card_rows.v` under either option.

**Option 1: everything instance-specific in
`instances/kim2025/five_card_rows.v`.** That file requires
`pgg_analysis_manifest`, which requires `five_card_analysis.v`, so a theorem
placed there is strictly above both the manifest and the five-card facade.
The consequence is that the base premise of the row's own `IdealFinite`
status can never be aliased in `FiveCardAnalysis` nor `Check`-pinned by
spelled type in the manifest, because both files are compiled before it
exists. The manifest's Row 4 and Row 5 tables would then carry an
`IdealFinite` status whose supporting theorem they cannot name.

Files recompiled: **9**, or **10** once the facade's typed transfer statuses
are corrected with it. The nine are `lib/var_dist_supp.v`,
`manifest/pgg_analysis_manifest.v`, `manifest/pgg_tableau.v`,
`manifest/pgg_tableau_syntax.v`, `manifest/pgg_analysis_client.v`,
`instances/kim2025/five_card_rows.v`, `instances/pgl27/pgl27_rows.v`,
`instances/s5/s5_rows.v` and `instances/psl211/psl211_rows.v`: three files
edited, the manifest's seven reverse-dependants following, and
`five_card_rows.v` one of those seven.

Nine is the figure for a landing that leaves
`instances/kim2025/five_card_analysis.v` stating the old statuses. That
compiles, because the facade's two status aliases are independent
definitions that no manifest row consumes, and it leaves the tree saying two
different things about the same path in two files. A landing that corrects
them adds `five_card_analysis.v` and nothing else, since its own eight
reverse-dependants are already among the nine, giving ten.

**Option 2: a new `instances/kim2025/five_card_mixing.v` below the facade.**
This is the arrangement the tree already uses for the one row it publishes at
`IdealFinite`. `pgl27_word_mixing` is proved in
`instances/pgl27/pgl27_mixing.v`, below the facade; `pgl27_analysis.v:267`
aliases it as `Definition word_mixing := @pgl27_word_mixing.`; the manifest's
Row 2 table names `PGL27Analysis.word_mixing` twice, at `:173` as the row's
bound or certificate and at `:182` as what makes the missing premise none;
and the manifest pins it by spelled type at `:1048`. The new file would
mirror `pgl27_mixing.v`'s position exactly: required by
`instances/kim2025/five_card_analysis.v`, which aliases the three theorems,
which the manifest's Row 4 and Row 5 tables then name and pin.

Files recompiled: **11**. The one file added over option 1 corrected is the
new `instances/kim2025/five_card_mixing.v`; `five_card_analysis.v` is in
both, and its own eight reverse-dependants are already among the nine.
`instances/psl211/psl211_endpoints.vo` is in neither set, so the freeze rule
is respected by both.

| landing | files recompiled |
|---|---|
| option 1, facade left stating the old statuses | 9 |
| option 1, facade corrected | 10 |
| option 2 | 11 |

**Recommendation: option 2**, because a row at `IdealFinite` whose base
premise cannot be named by the manifest contradicts the manifest's own
convention. Two further facts found while checking this point tell the same
way. The manifest's header at `:67-72` says the tables "cannot drift away
from the code" precisely because every identifier they name is pinned;
option 1 puts the three theorems where no pin can reach them. And the
five-card facade must be edited under either option if the tree is to say
one thing about each path, so option 2 adds one file over option 1, not two.

One extra compile is the whole of the price. Under option 1 the three
theorems are read only by `five_card_rows.v`; under option 2 they are read by
the facade, the manifest and `five_card_rows.v`, and the added edges are all
inside `instances/kim2025` and `manifest/`.

### The closure script

Every figure on this page comes from one Python pass over `.Makefile.rocq.d`.
It splits each rule on `:`, keeps the `.vo` targets and `.vo` dependencies,
inverts the edge set and takes the transitive closure forward from a file,
excluding the file itself. Output:

```
=== S10 reverse-dependency table, recomputed ===
home                                             revdep  psl211_endpoints in closure
security/pgg_collusion_bound.v                      105  YES
lib/perm_uniform.v                                  107  YES
reconstruct/algebraic_rigidity.v                    102  YES
reconstruct/transitivity_privacy.v                   41  YES
security/pgg_weighted_words.v                        39  no
instances/denboer1989/five_card_program.v            24  no
instances/denboer1989/five_card_scheme_I5.v          20  no
instances/kim2025/five_card_kim.v                    20  no
instances/kim2025/five_card_exec.v                   10  no
instances/kim2025/five_card_models.v                  9  no
instances/kim2025/five_card_rows.v                    0  no
manifest/pgg_analysis_manifest.v                      7  no
instances/kim2025/five_card_analysis.v                8  no
instances/denboer1989/den_boer_encoding.v            16  no
instances/pgl27/pgl27_mixing.v                       20  no
instances/pgl27/pgl27_analysis.v                      8  no
manifest/pgg_analysis_client.v                        0  no
manifest/pgg_tableau.v                                5  no

--- members of the closure of manifest/pgg_analysis_manifest.v (7) ---
    instances/kim2025/five_card_rows.vo
    instances/pgl27/pgl27_rows.vo
    instances/psl211/psl211_rows.vo
    instances/s5/s5_rows.vo
    manifest/pgg_analysis_client.vo
    manifest/pgg_tableau.vo
    manifest/pgg_tableau_syntax.vo
    psl211_endpoints present: no

--- members of the closure of instances/kim2025/five_card_analysis.v (8) ---
    instances/kim2025/five_card_rows.vo
    instances/pgl27/pgl27_rows.vo
    instances/psl211/psl211_rows.vo
    instances/s5/s5_rows.vo
    manifest/pgg_analysis_client.vo
    manifest/pgg_analysis_manifest.vo
    manifest/pgg_tableau.vo
    manifest/pgg_tableau_syntax.vo
    psl211_endpoints present: no

--- members of the closure of instances/denboer1989/den_boer_encoding.v (16) ---
    instances/denboer1989/den_boer_run.vo
    instances/denboer1989/denboer_trace.vo
    instances/kim2025/five_card_analysis.vo
    instances/kim2025/five_card_exec.vo
    instances/kim2025/five_card_models.vo
    instances/kim2025/five_card_rows.vo
    instances/kim2025/kim_input_privacy.vo
    instances/kim2025/kim_run.vo
    instances/kim2025/kim_trace.vo
    instances/pgl27/pgl27_rows.vo
    instances/psl211/psl211_rows.vo
    instances/s5/s5_rows.vo
    manifest/pgg_analysis_client.vo
    manifest/pgg_analysis_manifest.vo
    manifest/pgg_tableau.vo
    manifest/pgg_tableau_syntax.vo
    psl211_endpoints present: no

--- members of the closure of instances/kim2025/five_card_rows.v (0) ---
    psl211_endpoints present: no

=== landing recompile totals ===
Option 1 (everything instance-specific in five_card_rows.v):
  edited: ['instances/kim2025/five_card_rows.vo', 'lib/var_dist_supp.vo',
           'manifest/pgg_analysis_manifest.vo']
  total distinct .vo recompiled: 9
    instances/kim2025/five_card_rows.vo
    instances/pgl27/pgl27_rows.vo
    instances/psl211/psl211_rows.vo
    instances/s5/s5_rows.vo
    lib/var_dist_supp.vo
    manifest/pgg_analysis_client.vo
    manifest/pgg_analysis_manifest.vo
    manifest/pgg_tableau.vo
    manifest/pgg_tableau_syntax.vo

Option 2 (new file below five_card_analysis.v, aliased in the facade):
  edited: ['instances/kim2025/five_card_analysis.vo',
           'instances/kim2025/five_card_mixing.vo',
           'instances/kim2025/five_card_rows.vo', 'lib/var_dist_supp.vo',
           'manifest/pgg_analysis_manifest.vo']
  total distinct .vo recompiled: 11
    instances/kim2025/five_card_analysis.vo
    instances/kim2025/five_card_mixing.vo
    instances/kim2025/five_card_rows.vo
    instances/pgl27/pgl27_rows.vo
    instances/psl211/psl211_rows.vo
    instances/s5/s5_rows.vo
    lib/var_dist_supp.vo
    manifest/pgg_analysis_client.vo
    manifest/pgg_analysis_manifest.vo
    manifest/pgg_tableau.vo
    manifest/pgg_tableau_syntax.vo
  psl211_endpoints in the option-2 set: no

=== direct requirers ===
instances/kim2025/five_card_analysis.vo <- ['manifest/pgg_analysis_manifest.vo']
manifest/pgg_analysis_manifest.vo <- ['instances/kim2025/five_card_rows.vo',
  'instances/pgl27/pgl27_rows.vo', 'instances/psl211/psl211_rows.vo',
  'instances/s5/s5_rows.vo', 'manifest/pgg_analysis_client.vo',
  'manifest/pgg_tableau.vo', 'manifest/pgg_tableau_syntax.vo']
instances/pgl27/pgl27_mixing.vo <- ['instances/pgl27/pgl27_analysis.vo',
  'instances/pgl27/pgl27_exec.vo', 'instances/pgl27/pgl27_models.vo',
  'instances/pgl27/pgl27_rows.vo', 'instances/pgl27/pgl27_spectral.vo',
  'instances/pgl27/pgl27_table_bridge.vo',
  'instances/pgl27/pgl27_word_privacy.vo']
```

The same script, run again for the two variants the home sections need: the
landing that corrects the facade's typed transfer statuses under option 1,
and the branch that sends `card_tnth_count` to `den_boer_encoding.v` rather
than to `lib/`.

```
option 1, facade left stale          : 9
option 1, facade statuses also fixed : 10
option 2                             : 11
difference option2 - option1(fixed)  : 1
closure(five_card_analysis) subset of option1 set: True

den_boer_encoding revdeps            : 16
option 1 + card_tnth to denboer      : 18
option 2 + card_tnth to denboer      : 19
psl211_endpoints in either           : False False
```

A direct grep of `Require` lines gives the manifest the same seven
dependants and no others. `instances/psl211/psl211_endpoints.vo` is in none
of the closures above and in none of the five landing sets computed here.

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
| N3 | The eight identifiers built from `SpectralCert` field abbreviations carry domain words: `mixing` for a variation distance to an ideal cut, `marginal_bound` for a `ShuffleMarginalBound`, `sample_cut_witnessE` for the tying equation, `static_obs_const` for the constancy field, which is the tree's own word for that field. |
| N4 | The four row programs are `five_card_row_*`, matching the three programs already in `five_card_rows.v`. Round 1's fifth program is deleted by F1. |
| N5 | The `_bad` suffix is gone. A recorded `Fail` is named after what is attempted. |
| N6, F3 | The landing change list in S8 is rewritten and carries both manifest rows and the compile breakage at `five_card_rows.v:456`. Its round-1 claim to carry "every" header and docstring passage a landing makes false is withdrawn: round 2 found the list missing five `erefl` pins, the manifest's Row 4 and Row 5 header tables, and the whole of the five-card facade's section 7. What the list states now is the result of a whole-tree grep for the two row names, for the facade's two typed transfer statuses, and for the manifest's status vocabulary at those rows, each result read in the source. |
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
| F7, F8 | Notes, no change asked, and none made. |
| F9 | A note, and a change was made for it although this table said otherwise until round 2 pointed it out: S9 now states that `sa_cut_dist sa` is the cut marginal with the input pinned outside it, and that the reading as a conditional law given the input rests on `kim_input_dist` being a product, a property of these two adapters and not of the arm. |

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
  `fdistmap_neq0_codom`'s conclusion as `b \in codom f` so that `codomP`
  applies directly. Not applied: the conclusion is used by two proofs through
  a destructuring view, so changing it would edit three proof scripts, which
  is outside a rename pass. The name states the fact either way.
- **N4, one name.** The rename table gives
  `five_card_row_biased_spectral_tableau` to the biased program published at
  `StaticExecutedOnly`, and `five_card_row_biased_ideal_tableau` to the one at
  `IdealFinite`. F1 deletes the first program, so only the second name is
  used and the first appears nowhere.
- **N7, on `inv50_split`.** The rename table gives `inv50_split`, unprefixed.
  It is prefixed instead, `five_card_inv50_split`, so that it reads alike
  with its sibling in one file.
- **N20, on `pow2_39_split`.** The coordinator's instruction for N20 asks for
  an instance-prefixed name on the identity that replaces `pow2_split`, which
  is `five_card_pow2_39_split`. Round 2 accepts both prefixes at its section
  2(a) and adds one consequence: if a later pass moves the two identities to
  `lib/var_dist_supp.v`, nothing in either statement is about five cards and
  the prefix must go with the move.
- **N3, last row.** The audit flags `five_card_static_obs_const` here against
  `pgl27_word_view_const` there for the user's decision, because the two
  instances would then name one certificate field differently. The audit's own
  name is used and the divergence stands: `view` at this instance already
  means `ViewS`, the leakage space's colour tuple.
- **N24.** The landing target uses `(** ... *)`. The probe keeps `(* ... *)`,
  since the note is about the form a landing takes.

## Round 2 audits and what changed

Round 1's fix pass was audited twice again on 2026-09-19, for names
(`naming-audit-round2.md`, blocking B1-B3, should-fix S1-S5, notes a-k) and
for soundness (`soundness-audit-round2.md`, blocking G1-G2, should-fix
G3-G4, notes G5-G7). Both returned NO-GO, and both on text alone: no audit
disputed a proof, a statement or a number that the kernel checks. The five
`.v` files and this file as the first fix pass left them are kept in
`history/`, suffixed `.2026-09-19-before-fix2`. This second pass changed no
code: with comments stripped, each `.v` file is byte-identical to its
`before-fix2` copy.

| finding | severity | disposition |
|---|---|---|
| B1 | blocking | "constancy" replaces "invariance" as the prose name of the `sc_const` field at all eleven sites, five in the `.v` files and six here. It is the tree's word for that field at ten sites in six files, `manifest/pgg_tableau.v:37,126,129,557`, `manifest/pgg_tableau_syntax.v:140`, `instances/pgl27/pgl27_rows.v:244`, `instances/s5/s5_rows.v:66`, `instances/psl211/psl211_rows.v:41` and `instances/kim2025/five_card_rows.v:41`, all read for this pass. The audit says seven files and lists six; six is what a whole-tree grep returns. The only other "constancy" in the tree, `reconstruct/s5_nogo.v:53`, is about a different object and is not a name for this field. `invariant by` as a Tableau surface keyword is untouched, and it does not occur in this probe. |
| B2 | blocking | `kim_centi_cert40`'s comment said one field changes. Two do: `sc_b` from `scb_bound (kim_security_bundle_centi R)` to `kim_centi_marginal_bound40 R`, and `sc_close` from `@kim_centi_cut_mixing R` to `@kim_centi_cut_mixing40 R`, because `sc_close`'s type mentions `sw_bound_eps sc_b`. Compared term by term against `kim_centi_cert`; `sc_Hd`, `sc_ideal` and `sc_const` are the same terms. The audit's replacement is applied. |
| B3, G3 | blocking, should-fix | The manifest's reverse-dependency row is 7, not 5, and the landing total on the branch both audits priced is 9, not 8. Both recomputed here from `.Makefile.rocq.d`; the script and its full output are under "The closure script". The two missed files are `manifest/pgg_tableau.v` and `manifest/pgg_tableau_syntax.v`. The other eleven rows of the twelve-row S10 table are confirmed unchanged, and three rows are added for the homes this pass had to price. The total rises to 10 once the facade is corrected too; see the G4 row. |
| G1 | blocking | The S8 change list is extended with the three `erefl` row pins at `:1779-1780`, `:1787` and `:1788-1789`, the manifest header passage at `:67-72` that announces them, and the Row 4 and Row 5 header tables at `:301-310`, `:322-328`, `:351-364` and `:374-380`, every line re-read in the source. The further search the fix pass was asked to run found what both audits missed: the five-card facade's two typed transfer statuses, their docstrings, their section header, and four more `erefl` pins, two in `instances/kim2025/five_card_analysis.v:433-436` and two in `manifest/pgg_analysis_manifest.v:1385-1389`. The claim to carry "every" such passage is withdrawn and replaced by a statement of what was searched. |
| G2 | blocking | "no `_CoqProject` edit is needed" is replaced. `_CoqProject` enumerates 194 `.v` files by name after its `-R` lines, and `Makefile` regenerates `Makefile.rocq` from it, so an unlisted file is never built. The precedent is `reconstruct/dealer_privacy.v` at `_CoqProject:172`; the five `lib/` lines are `:30-34`. |
| G4 | should-fix | Both homes are set out with measured costs under "The home of the mixing and constancy theorems", with the concrete option-2 file named as a new `instances/kim2025/five_card_mixing.v` mirroring `instances/pgl27/pgl27_mixing.v`. The audit's 9-against-11 is 10 against 11 once the facade's typed transfer statuses are corrected under option 1 as well, which the facade finding above makes necessary; 9 is the figure only for a landing that leaves the facade stale. The recommendation is option 2. **The decision is the user's and is not taken here.** |
| G5 | note | `2 * sqrt 5 * (1/80)^7` is `2.13e-13`, not `1.6e-13`. Corrected in S7, with the Python and the ratio `8.5299` against `2^-39 = 1.82e-12`. This is the first revision in which the figure and round 1's "about eight and a half times weaker" (`soundness-audit.md:338-339`) agree; at `1.6e-13` the ratio would have been `11.37`. |
| G6, S3 | note, should-fix | The comment on the recorded `Fail five_card_row_repeated39_bare` now says the identity is quantified over every real field but not over the family index, which is what `conclude` asks for. |
| G7 | note | F7 and F8 of round 1 stay unchanged as observations. No change asked, none made. |
| S1 | should-fix | `den_boer_layout_law_const`'s comment named the wrong carrier. The law is on the cards drawn, not on the positions, and the comment now says "read as the law of the card drawn". |
| S2 | should-fix | The comment on `five_card_row_repeated_spectral_tableau` said `pgg_analysis_status.v` "admits" the status. `publish` takes the status as a free parameter and nothing checks it; the comment now says so and names the criterion the status is claimed against. |
| S4 | should-fix | The N4 row said five row programs. Four remain, counted in the file: `five_card_row_repeated_spectral_tableau`, `five_card_row_biased_ideal_tableau`, `five_card_row_repeated39` and `five_card_row_biased_inv25`. |
| S5 | should-fix | `kim_biased_cert_eps_lt2`'s comment said the row excludes readings. It bounds a distance between two laws; the comment now says it rules out a coalition telling the two committed pairs apart with certainty. |
| note a | note | The 3.3 s sentence now says one `Fail` is new, `five_card_row_biased_inv25_rowE`. Counted: three `Fail`s in `history/kim_spectral_rows_probe.2026-09-19-before-fix.v`, four now. |
| note b | note | "six lines" is "nine lines between `Proof.` and `Qed.`", counted in `var_dist_injective_probe.v`. |
| note c | note | Half applied. `five_card_row_biased_tableau`'s docstring is `:394-400`; the round-1 `:396-400` and the audit's `:393-399` are both wrong and the range is corrected to what the file has. `five_card_row_repeated_tableau`'s docstring is `:383-389`, which is what this file already said; the audit's `:382-388` is off by one and the range is left alone. |
| note e | note | The clause duplicated on `fc_kim_word_eval_powE` and `fc_kim_rho_supp_pow` is carried by the first. The second now says what it adds, the quantifier over the letter weighting and the passage to the support of the pushforward. |
| note i | note | `b \\in codom f` is `b \in codom f`. |
| note j | note | The remit's six deviations and the section's five bullets are reconciled by splitting the N7-and-N20 bullet into one bullet each. |

### Round 2 findings not applied

- **naming note d**, the `(**` and `(*` split at `five_card_pow2_39_split`
  when the comments are converted to the landing target's shape. It is an
  instruction for a landing plan and needs no change to the probe. It is
  recorded in the landing list.
- **naming note f**, the instance prefix moving with the two identities if a
  later pass sends them to `lib/`. Recorded above under "Audit findings not
  applied"; no probe change follows from it.
- **naming note g**, that `fc_sigma_pow_ord_inj` in fact gives the exact
  order five while `fc_sigma_pow5_eq1`'s comment claims only that the order
  divides five. The audit states no change is needed and none is made: the
  comment is honest and understates.
- **naming note h**, that `Section five_card_static_obs_const` encloses
  `Lemma five_card_static_obs_const` and that `Section five_card_static_obs`
  would read better. Renaming a `Section` is a code change and this pass
  changes no code. It is a one-line edit for whoever lands the file.
- **naming note k**, two orientation observations on
  `kim_biased_sample_cut_witnessE` and `kim_biased_marginal_bound`. The audit
  asks for no change and confirms both are right.
- **naming N10, second half**, unchanged from round 1 and recorded above.
- A style pass over the probe files during this session flagged
  `boolp.funext` written fully qualified (`five_card_sc_const_probe.v:109`,
  `:120`), `apply: funext` where `apply/ffunP` would serve
  (`kim_spectral_rows_probe.v:53`), and `@` on several applied lemmas. All
  three are code changes and none is in either round-2 audit. They are left
  for a landing pass.
