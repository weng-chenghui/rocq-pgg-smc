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
returned NO-GO on surface matters, revised again the same day after two
round-2 audits returned NO-GO on text alone, and revised a third time after
two round-3 audits, again on text alone. No audit in any round disputed the
mathematics. See "Round 1 audits and what changed", "Round 2 audits and what
changed" and "Round 3 audits and what changed".

**The standing of the landing account has changed with this revision.** S8's
change list and S10's home prices are what has been found so far. They are
not claimed complete and a landing plan must not be written from them alone.
Each of four audit rounds added items the round before missed, always
because the list was built by searching for names while the tree also states
the same facts in sentences that carry no name; round 4 added four
propositions the seven-proposition rebuild list did not reach. S8 now carries a subsection,
"How a landing batch must rebuild this list", saying how the rebuild is done:
compile breakages mechanically, by compiling copies of the three files and
their reverse-dependants against the changed rows, and false sentences by
searching for the proposition in every spelling rather than for the row
names.

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
| S8 | GO | Three recorded `Fail`s, two lemmas reading off the published fields, and one equation between two published rows. What a landing changes is listed below for both rows, as the items known so far and not as a complete list: the two manifest row definitions, seven `erefl` pins, five in the manifest and two in the five-card facade, the manifest's Row 4 and Row 5 header tables, three further manifest passages about the development rather than about a row, the facade's section 7 and file header, and the prose and header index of `instances/kim2025/five_card_rows.v`. |
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
approaches the 20 s bug threshold.

The third fix pass re-ran all five, in `_CoqProject` order, in a fresh
directory holding only copies of the five sources, after deleting the dead
`Require` from `kim_sc_close_probe.v`. Real exit status 0 for every file, at
4.5 s, 4.2 s, 5.4 s, 4.2 s and 10.9 s. Peak RSS was not instrumented in that
run, though the 8000 MB cap was in force and never fired. The one figure the
deletion moves is `kim_sc_close_probe.v`, 6.16 s to 5.4 s; the table above is
kept as the instrumented measurement and its third row is stale by that much. One sentence takes over 3 s:
`five_card_row_biased_forms_publishedE`, 3.15 s, a `by []` between two
published rows that each contain the executed run. The round-1 figure for
`kim_spectral_rows_probe.v` was 7.72 s; of the 3.3 s added, the new
comparison `five_card_row_biased_forms_publishedE` is one part, and the new
`Fail five_card_row_biased_inv25_rowE` is another, which elaborates a
published row before the kernel rejects its `erefl`. The other three
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

Which field discharges which hypothesis, since the previous revision of this
file stated it backwards in two places, the Row 4 table cell and the first
item of the facade list.
`var_dist_fdistmap_transfer` sits in a section whose two hypotheses
are, in order, `PQ_close : var_dist P Q <= delta`
(`security/pgg_collusion_bound.v:980`) and
`ideal_eq : fdistmap fx Q = fdistmap fy Q` (`:981`), and `spectral_tail`
(`manifest/pgg_tableau.v:561-570`) fills them in that order: `:569`
`by rewrite -(sc_Hd cert); exact: (sc_close cert)` for the first and `:570`
`exact: (@sc_const _ _ _ _ cert C HC x x')` for the second. So the mixing
field discharges the FIRST hypothesis, the cut-carrier distance, and the
constancy field IS the second, the equality of the two reader pushforwards
under the ideal. Where the manifest and the facade call the second hypothesis
"the ideal distribution equality", they are right and the theorem that answers
them is `five_card_static_obs_const`, not a mixing lemma.

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

### What a landing changes: the items known so far

**This list is not claimed to be complete, and a landing plan must not treat
it as complete.** Three rounds of audit have each added items the round
before missed, and each time for the same reason: the list was built by
searching for names, and the tree also states these facts in sentences that
carry no name. Round 2 added three `erefl` row pins and two header tables;
the search after it added two more pins and the whole of the facade's section
7; round 3 added three manifest passages about the development rather than
about a row, the header index and file-title line of `five_card_rows.v`, and
the facade's own file header; round 4 added four propositions of the Row 4
and Row 5 tables that the rebuild list did not reach. The list below is
what has been found, every line of it read in the source at this revision. It
is the seed for the rebuild described under "How a landing batch must rebuild
this list", not a substitute for it.

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
| `:305` | `model transfer \| none claimed` | the certificate's two fields give the transfer through `spectral_tail`, the mixing field discharging the inequality's first hypothesis and the constancy field being its second |
| `:306` | `missing premise \| the ideal distribution equality, as in row 3` | the constancy field `five_card_static_obs_const` is that equality; the mixing field supplies the cut-carrier distance the inequality's first hypothesis asks for |
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
| `:357` | `model transfer \| none claimed` | the certificate's two fields give the transfer through `spectral_tail`, as at Row 4 |
| `:358-360` | `missing premise \| the ideal distribution equality, as in row 3, and in addition no security statement is attached to either model` | false on both halves |
| `:361` | `completion level \| Sampled` | becomes `AnalysisBridged` |
| `:362` | `transfer status \| NoModelComparison` | becomes `IdealFinite` |
| `:374-380` | the level justification, which says `The row is NOT AnalysisBridged. endpoint_bound and deal_centi_lt bound the distance from uniform of ONE seat's endpoint distribution: neither quantifies over a coalition, neither mentions a second secret, and neither has the shape of an indistinguishability or leakage statement.` and closes at `:379-380` with `A ShuffleCertificateBundle exists for both models and does not raise the level.` | the certified proposition quantifies over every coalition below the threshold, compares two committed pairs, and has exactly the shape the paragraph says is absent; and the certificate that raises the level is built from that same bundle's `scb_bound` |

`:364` `typed row | five_card_row_repeated` stays true.

#### Three further manifest passages about the development, not about a row

These carry neither row name, which is why every search keyed to
`five_card_row_biased` and `five_card_row_repeated` missed them for three
rounds. All three say that the five-card development supplies no ideal
distribution equality, and `five_card_static_obs_const` is exactly such an
equality at this development, so all three carry a clause a landing
falsifies.

(a) `manifest/pgg_analysis_manifest.v:244-248`, the Row 3 header table, the
five-card uniform row:

> `| missing premise | the ideal distribution equality: the second hypothesis
> of var_dist_fdistmap_transfer, an equality of two reader pushforwards under
> an ideal distribution, which the five-card development does not supply |`

This is the anchor. Row 4 at `:306` and Row 5 at `:358-360` both say "as in
row 3" and point here, so it must be rewritten before or with them. A landing
that rewrites Rows 4 and 5 and leaves Row 3 alone leaves the manifest
asserting, at the place the other two rows cite, the very thing the landing
disproves.

(b) `manifest/pgg_analysis_manifest.v:753-755`, the docstring of
`five_card_row_uniform`:

> `reaching AnalysisBridged; the development supplies no ideal-distribution
> equality, so no model transfer is claimed.`

The uniform row's own status does not change. The clause is not about the
row, it is about the development, and it becomes false.

(c) `manifest/pgg_analysis_manifest.v:669-673`, the "Absent capabilities"
section:

> `Five-card development. No transfer-layer result exists: section 7 of its
> facade carries typed status aliases and no theorem. The absent premise is
> the second hypothesis of var_dist_fdistmap_transfer, an equality of two
> reader pushforwards under an ideal distribution, which the development does
> not supply.`

Three clauses, and they do not all move together. "No transfer-layer result
exists" is false under either option, because the result exists as soon as the
certificates are proved, wherever they live. "Section 7 of its facade carries
typed status aliases and no theorem" stays true under option 1, where the
theorems sit above the facade in `five_card_rows.v` and cannot be aliased in
it, and is false under option 2, where section 7 gains three aliases. The last
sentence, naming the absent premise, is false under either option.

#### The five-card facade's typed transfer statuses

Neither round-2 audit reaches this file's typed transfer statuses. It states
both rows' transfer statuses a second time, and those statements are pinned
by four further `erefl`s, two in the facade itself and two more inside the
manifest.

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

1. The section header at `:351-358` becomes false. The constancy field is the
   ideal distribution equality that discharges the second hypothesis, and the
   mixing field is the cut-carrier bound the first asks for, so the section
   has three theorems to alias: `kim_centi_cut_mixing` and
   `kim_biased_cut_mixing` for the two models' mixing fields, and
   `five_card_static_obs_const` for the constancy field they share. Its
   clauses go at different rates, as at the
   "Absent capabilities" passage above. "No transfer-layer result exists" and
   "the five-card development has no ideal distribution equality" are false
   under either option. "There is nothing to alias" is false under option 2,
   and under option 1 it stays operationally true for a reason the sentence
   does not give: the theorems exist but sit above this file, so a landing
   under option 1 must rewrite the clause rather than keep it.
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
6. The file header at `:16-17`, "Section 7 is empty for this development and
   is documented as empty rather than omitted", becomes false under option 2,
   where section 7 gains three aliases. Under option 1 it stays as accurate
   as it is now. Under option 2 the new aliases also need a line in the
   phase-H1 check table at `:30-57`, a name in the manifest's Row 4 and Row 5
   tables and a spelled-type `Check` in the manifest's five-card section
   beside `:1385-1389`, because the manifest's header at `:67-72` requires
   every identifier a table names to be pinned.

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
two client `Check` lines, and returns no other site. A whole-word grep for the facade's
model and family names, `single_biased_sample`, `repeated_sample`,
`centi_sample`, `biased_family` and `centi_family`, over the 133 `.v` files of
the twelve production directories, rerun for this pass, returns their
declarations and alias table in `five_card_analysis.v:45-47` and `:202-222`,
their names in the manifest's Row 4 and Row 5 header tables at `:293`, `:315`,
`:322`, `:340-341` and `:370` and in the row definitions at `:768` and `:778`,
three bare `Check`s in `manifest/pgg_analysis_client.v:41,43,44`, one
spelled-type `Check` at `five_card_analysis.v:402`, three sampler `Check`s in
`manifest/pgg_analysis_manifest.v` at `:1177`, `:1182` and `:1187`, and seven
more occurrences inside five spelled-type `Check`s in the same file, opened at
`:1207`, `:1214`, `:1221`, `:1233` and `:1245`, with the names at `:1210`,
`:1217`, `:1225`, `:1229`, `:1235`, `:1248` and `:1253`. Of those, the two row
definitions carry a status and
`:322` opens the Row 4 level-justification paragraph, and all three are
already in the list above under their own headings. None of the other
sites states a level or a status, so no name there moves with a restatusing.
The previous form of this sentence reported one spelled-type `Check` where the
search returns nine, at eleven lines, and named none of the three bare
`Check`s in the client, none of the eight in the manifest and not the facade's
own alias table.
`five_card_rows.v` uses the
underlying `kim_biased_family` and `kim_centi_family` rather than the facade
aliases, so no name there moves with a restatusing. A search for row counts by
level or status returned no file that counts or pattern-matches manifest rows
that way, and a search for `apr_completion` and `apr_transfer` at these two
rows returned no lemma stating either except `five_card_row_biased_levelE`.
Both are results of a name-keyed search and carry its limit: they say what the
search found, not that no sentence anywhere says the same thing in words.

#### `instances/kim2025/five_card_rows.v`

Declarations and prose that a landing breaks or makes false. The first is a
compile breakage; the rest are prose.

**The landing ADDS the certified programs and keeps the two existing ones.**
Decided by the coordinator on the owner's design principle that a row states
one security claim and two claims about one model are two rows.
`five_card_row_repeated_tableau` (`:390`) and `five_card_row_biased_tableau`
(`:401`) keep their type `Tableau Sampled`, and the certified programs are
added beside them under the names of S6 and S7. Because those two keep that
type, `five_card_row_repeated_prefixE`
(`:418-425`), `five_card_row_biased_prefixE` (`:428-435`),
`five_card_row_repeated_modelE` (`:441-444`) and
`five_card_row_biased_modelE` (`:447-450`) go on compiling for their present
reasons, each applying `tableau_at` or `sp_f (tableau_at ...)` to a
`Tableau Sampled`, and the recorded `Fail five_card_row_biased_at_manifest_level`
(`:473-475`) goes on failing for its present reason, the level gap between
that program and the manifest's row.

Retyping the two in place is not available. `tableau_at` is a projection of
`TableauAt` (`manifest/pgg_tableau.v:411-414`) and a published row is a
`PublishedRowAt` (`:678-681`), which is a different record with no such
projection, so all four lemmas would stop typechecking and the recorded
`Fail` would change its reason to a mismatch between `PublishedRow` and
`Tableau (apr_completion five_card_row_biased)`.

The four certified programs are copied from the probe as they stand, each a
full chain from `five_card_committed` (`kim_spectral_rows_probe.v:100-104`,
`:110-114`, `:284-289`, `:360-366`), which is how every certified program in
the tree is written: from its own instance's prefix, at a level below
`Sampled`. `pgl27_row_exact_tableau` and `pgl27_row_word_tableau` chain from
`pgl27_dealt` (`instances/pgl27/pgl27_rows.v:270`, `:295`),
`s5_row_rand_tableau` from `s5_supplied` (`instances/s5/s5_rows.v:275`),
`psl211_row_alldecks_tableau` from `psl211_alldecks_prefix`
(`instances/psl211/psl211_rows.v:175`), and `five_card_row_uniform_tableau`
from `five_card_committed` (`instances/kim2025/five_card_rows.v:338`), all
four prefixes being `Tableau Observed`. The landing therefore does not need
T0 of `notes/20260919-tableau-three-extensions-probe-design.md:169`, which
asks whether two programs can continue from one named `Tableau Sampled`
value. Nothing in the tree does that today and this landing does not start.

1. `five_card_row_repeated_at_manifest_level` (`:456-458`) ascribes the
   `Sampled` program at `Tableau (apr_completion five_card_row_repeated)`.
   Moving that manifest row to `AnalysisBridged` makes the ascription fail to
   typecheck. It must be deleted or restated against the new row. This does
   not depend on the decision above: the ascription breaks because the
   manifest's level moves, whether or not the program keeps its type.
2. The header sentence at `:28-30`, "The manifest's two further five-card
   rows are written as programs below, and both stop at `Sampled`", stops
   describing the file. Under the decision above the two named programs do
   still stop at `Sampled`, so the sentence is not false of them; it is
   obsolete, because the file then also writes those two manifest rows as
   four certified programs that reach `AnalysisBridged`. The next sentence
   at `:30-33`, "The repeated row stops there because the manifest does",
   becomes false outright, since the manifest no longer stops there.
3. The header sentence at `:33-42`, "The biased row stops there although the
   manifest places it at `AnalysisBridged`, because the theorem that carries
   it to that level, `five_card_colour_view_leak_bound`, bounds a conditional
   mutual information, and neither arm of `certify` carries a bound of that
   kind: ... the spectral arm asks for a variation distance to an ideal cut
   on the shuffle group together with the constancy of a coalition's reading
   of that ideal, and neither of those is proved at this instance", becomes
   false. Both are now proved, so the spectral arm does carry a bound of that
   kind and the head of the sentence goes with the clause. The subordinate
   clause about the spectral arm is `:39-42`; the sentence it is part of
   begins at `:33`, and it is the sentence that must be rewritten.
4. The header paragraph at `:42-50`, which explains the biased row's gap as
   "the manifest's criterion met by a theorem no arm takes" and compares it
   with `s5_row_word`, becomes obsolete for the biased row. It stays correct
   for S5 itself, where the constancy field is false for a reason no proof
   removes (`instances/s5/s5_rows.v:60-72`).
5. The docstring of `five_card_row_repeated_tableau` (`:383-389`), ending "so
   no security payload follows it", becomes false. Two clauses in that range
   go false, for two reasons. The closing clause goes false because the
   certified proposition is a statement about what a set of seats reads. The
   opening clause at `:384`, "The program stops at Sampled, the level the
   manifest records for this row", goes false because the manifest's level for
   the repeated row moves to `AnalysisBridged` while the program keeps
   `Sampled`; the program's own level is unchanged and it is the agreement
   between the two that the clause asserts. The round-2 naming audit reports
   this range as `:382-388`; the file has `:383-389` and the range is left as
   it was.
6. The docstring of `five_card_row_biased_tableau` (`:394-400`), which says
   neither arm takes a bound of the kind the row has, becomes false. The
   round-1 range `:396-400` was short by two lines and the round-2 naming
   audit's `:393-399` is off by one in the other direction; `:394-400` is
   what the file has.
7. `five_card_row_biased_levelE` (`:465-467`) stays true, since only the
   biased row's transfer status changes and its completion level is already
   `AnalysisBridged`. The lemma states only `apr_completion
   five_card_row_biased = AnalysisBridged` and names no program, so it is
   independent of the decision above. Its docstring at `:460-464` is not: it
   says "The program above reaches Sampled", which the decision keeps true
   and a retype would make false. The docstring stays accurate for the
   `Sampled` program, but should say that the gap it
   describes is about the program and not about the manifest's transfer
   status.
8. The recorded `Fail five_card_row_biased_at_manifest_level` (`:473-475`)
   stays a `Fail`, and for its present reason, because the decision above
   keeps `five_card_row_biased_tableau` at `Tableau Sampled` while the
   manifest's biased row stays at `AnalysisBridged`. Its docstring at
   `:469-472` reads as a statement about the biased path rather than about
   one program and becomes misleading, since the path then has a program that
   does reach `AnalysisBridged`.
9. The header index at `:78-86` and `:119-122`, and the file-title line
   `:4`. `:84-86` indexes `five_card_row_repeated_at_manifest_level`, which
   item 1 deletes or restates, so the entry dangles either way. `:78-83`
   state both programs' level, "the repeated row as a program, stopping at
   `Sampled`" and the same for the biased row, which stays true of those two
   declarations but stops describing the file once the certified programs are
   added beside them. `:119-122` says the manifest's completion level for the
   biased row is one "which its program does not reach", and the file then
   has a program that does. `:4`, "the five-card instance's three rows,
   written as programs", is a count a landing changes, because the four new
   programs write two of those rows a second time.

Every other declaration in that file stays true, given the decision above to
keep the two `Tableau Sampled` programs at their present type. The file's
declarations were enumerated from the source for this pass, not counted from
memory: twenty-eight `Definition`, `Lemma` and `Theorem` commands and three
recorded `Fail`s. Four of the twenty-eight and one of the three `Fail`s are
in the list above, at `:390`, `:401`, `:456`, `:465` and `:473`. The other
twenty-four and the other two `Fail`s are
`five_card_committed` (`:175`), `five_card_committed_paramsE` (`:191`),
`five_card_colour_fill` (`:205`), the five static-reading lemmas
`five_card_viewS_nth` (`:216`), `five_card_static_obsE` (`:234`),
`five_card_viewS_indep` (`:270`), `five_card_exact_viewE` (`:286`) and
`five_card_static_obs_indep` (`:299`), `five_card_exact_witness` (`:321`),
`five_card_row_uniform_tableau` (`:338`) and its `rowE` (`:347`),
`five_card_exact_view_secrecy` (`:363`), the recorded
`Fail five_card_row_s5_family` (`:409`), the two `prefixE` lemmas (`:418`,
`:428`) and the two `modelE` lemmas (`:441`, `:447`),
`five_card_row_repeated_endpoint_lt` (`:488`), `kim_centi_small` (`:500`),
`five_card_row_biased_leak_bound` (`:516`), and the functionality block
`five_card_target` (`:542`), `five_card_F` (`:550`), `five_card_FE` (`:558`),
`five_card_F_ite` (`:564`), the recorded `Fail five_card_F_or` (`:571`) and
`five_card_realises_expected` (`:579`). None of them mentions the biased or
the repeated row's level or transfer status. Two mention the uniform row's:
`five_card_row_uniform_tableau` (`:338`) writes `StaticExecutedOnly` into its
`publish` step and fixes `AnalysisBridged` through it, and
`five_card_row_uniform_rowE` (`:347`) pins the manifest's
`five_card_row_uniform` by conversion. A spectral landing leaves the uniform
row alone, so both stay true. The previous form of this paragraph said "the
three `prefixE`" where the file has two, and covered twelve declarations out
of the twenty-six, eight by name and four by suffix.

#### How a landing batch must rebuild this list

The list above is a seed. A landing batch rebuilds it in two passes, because
the two kinds of item are found by two different means and only one of them
is mechanical.

**Compile breakages are found by compiling.** Take full copies of
`manifest/pgg_analysis_manifest.v`, `instances/kim2025/five_card_analysis.v`
and `instances/kim2025/five_card_rows.v` and of their reverse-dependants, make
the row changes in the copies, and compile them, as a
`/rocq-probe-first-spec` landing in this repository does. Every `erefl` pin,
every spelled-type `Check` and every ascription that moves shows up as an
error with a line number, one per compile: `coqc` halts at the first error, so
the pass is an iteration and not a single run that lists them all. Nothing
about that pass depends on having guessed
the right search terms, and it is the only way to be sure of the pins, since
the manifest's own header at `:67-72` says a failing `Check` is a hard error
in that file.

**Sentences that become false are found by searching for the proposition, not
for the row names.** This is where all four audit rounds found what the
previous list missed. Search for each proposition in every spelling it might
take, over the twelve production directories:

- no ideal distribution equality at the five-card development. Spellings
  found so far: "the ideal distribution equality ... which the five-card
  development does not supply", "the development supplies no
  ideal-distribution equality", "the absent premise is the second hypothesis
  of var_dist_fdistmap_transfer", "there is nothing to alias". None of the
  four names either Kim row, which is why a search keyed to the row names
  reached none of them.
- both Kim programs stop at `Sampled`, and the level gap between a program
  and its manifest row.
- the repeated row has endpoint marginals only, and no security statement is
  attached to either model.
- no model comparison, and no transfer-layer result exists.
- nothing to alias, and section 7 is empty.
- three rows, and any other count of the five-card rows or programs.
- row counts by completion level or by transfer status.
- the biased path carries no shuffle certificate, stated at
  `manifest/pgg_analysis_manifest.v:301-302` as `bound or certificate | none;
  kim_leak_bound is the numeric constant of the bridge theorem, not a shuffle
  certificate`.
- the repeated path's bound-or-certificate list is those four bundles and
  bounds, stated at `:351-354`.
- the repeated path has no final bridge theorem, stated at `:355` as
  `final bridge theorem | NONE`.
- the existing certificate bundle does not raise the level, stated at
  `:379-380` as `A ShuffleCertificate-Bundle exists for both models and does
  not raise the level.`

Those eleven propositions are the ones found so far. The list of propositions
is no more complete than the list of places, and it is open. The last four
were added in round 4 from this document's own cells, `:589`, `:605`, `:606`
and `:611`, each of which already records the proposition as falsified; the
seven before them reached none of the four. A landing batch extends this list
with every further proposition it meets while reading the Row 3, Row 4 and
Row 5 tables and the facade's section 7 in full, and does that before it
searches. The list in this section names where each proposition is stated
today; a landing batch must assume that both the propositions and their
places are undercounted, and search for the words, not for the names.

#### The two documents outside the `.v` files

`notes/20260919-kim-tableau-sampled-design.md` and
`docs/superpowers/plans/2026-09-19-kim-tableau-sampled.md` are as-built
records of one executed batch, not standing descriptions of the tree. A
landing adds one dated superseding line to the design note's status block,
naming the new design note, and leaves the body alone; the plan's as-built
table records a compile that happened and is not touched at all.

The design note's decision 2, "Do not extend the Tableau with a `certify
EndpointMarginal` arm" (`notes/20260919-kim-tableau-sampled-design.md:38`),
is NOT superseded. A spectral landing adds no arm: it uses the existing
`SpectralDecay` arm at `manifest/pgg_tableau.v:152`, which is what the verdict
at the top of this file says. The same holds for the first half of the plan's
construction choice 4
(`docs/superpowers/plans/2026-09-19-kim-tableau-sampled.md:35`), "No `certify`
arm is added".

What the landing does supersede is the level claim: the design note's title,
the last sentence of its decision 1 at `:35-37`, "The row stops at
`Sampled`", and the second half of that construction choice, "both Kim
programs stop at `Sampled`". Decision 1's declaration itself survives, because
the decision recorded above keeps `five_card_row_repeated_tableau` at
`Tableau Sampled`; what goes is the claim that the row stops there.

One further record expires with the landing. `soundness-audit.md:336-337`
cautions that no lemma in the tree proves the ceiling 2. That is true today,
because `var_dist_le2` lives in this probe and the probe is not in
`_CoqProject`, and it becomes false the moment `lib/var_dist_supp.v` lands.

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

**The two homes below are priced, not settled, and the prices are complete
only for what compiling measures.** The recompile totals come from the
dependency graph and are exact. What a home does to the prose of the tree is
the same open question as in S8: the list of sentences a landing makes false
is the one known so far and is not claimed complete. The home decision itself
is the user's and is not taken here.

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
the rerun. `instances/psl211/psl211_endpoints.vo` is in the closures of the
first four rows, which is why none of those four is proposed as a home, and
in none of the closures of the other eleven. It is in none of the five
landing sets computed below, under either option and on either branch for
`card_tnth_count`, which is the sense in which the freeze rule is respected:
not that the page mentions no home below `psl211_endpoints`, but that no home
the landing proposes is one.

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
every row marked with a dagger moves to the new file below the facade.

| lemma | proposed permanent name | proposed home |
|---|---|---|
| the ceiling of a variation distance | `var_dist_le2` | new `lib/var_dist_supp.v` |
| support-injective transport | `var_dist_fdistmap_supp_inj` | same |
| its mutation witness | `var_dist_fdistmap_const_neq` | same |
| pushforward support | `fdistmap_neq0_codom` | same |
| uniform fixed by an injective endomap | `fdistmap_inj_uniform_id` | same |
| tuple positions counted | `card_tnth_count` | `lib/`, in a file whose name covers it, or local to `den_boer_encoding.v` |
| `fc_sigma ^+ 5 = 1` † | `fc_sigma_pow5_eq1` | `instances/kim2025/five_card_rows.v` |
| two powers agreeing at one card position are equal † | `fc_sigma_pow_point_inj` | same |
| the exponent reader is injective † | `fc_sigma_pow_ord_inj` | same |
| the deck census † | `fc_arrange_countE` | same |
| word evaluates to a power † | `fc_kim_word_eval_powE` | same |
| the word law's support † | `fc_kim_rho_supp_pow` | same |
| the ideal law's support † | `five_card_ideal_supp_pow` | same |
| one card position of the ideal law is uniform † | `five_card_ideal_point_uniform` | same |
| the two Kim supports † | `kim_single_cut_supp_pow`, `kim_centi_cut_supp_pow` | same |
| one-position card law is input-free † | `den_boer_layout_law_const` | same |
| the generic distance transfer † | `five_card_cut_mixing_of_supp_pow` | same |
| the one-cut marginal bound, named by a mixing statement † | `kim_biased_marginal_bound` | same |
| the two mixing fields † | `kim_centi_cut_mixing`, `kim_biased_cut_mixing` | same |
| the constancy field † | `five_card_static_obs_const` | same |
| the two reprice identities | `five_card_pow2_39_split`, `five_card_inv50_split` | same |
| the three reprice definitions and the bound below the ceiling | `five_card_reprice39`, `five_card_reprice_inv25`, `five_card_reprice_inv25_lt2` | same |
| the one-cut bundle's number, and the exact number below it | `kim_biased_epsE`, `kim_biased_exact_le_eps` | same |
| the one-cut per-card-position bound | `kim_one_cut_centi_le` | same |
| the two form-2 mixing fields | `kim_centi_cut_mixing40`, `kim_biased_cut_mixing_exact` | same |
| the remaining bounds and the certificates | `kim_biased_sample_cut_witnessE`, `kim_centi_marginal_bound40`, `kim_biased_marginal_bound_exact`, `kim_centi_cert`, `kim_biased_cert`, `kim_centi_cert40`, `kim_biased_cert_exact` | same |
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

Their proofs do not travel alone. `kim_centi_cut_mixing` and
`kim_biased_cut_mixing` are proved by `five_card_cut_mixing_of_supp_pow` from
the two Kim supports, and `five_card_static_obs_const` from
`den_boer_layout_law_const` and `five_card_ideal_point_uniform`; the chain
closes at `fc_sigma_pow5_eq1` and `fc_kim_word_eval_powE`. Under option 2 all
of those, and `kim_biased_marginal_bound`, which a mixing statement names, go
in the new file too. Twenty-nine declarations stay above, enumerated under
option 2 below. They are the certificates, the row programs, the lemmas that
read off their published fields, the repricing definitions and identities,
the two bundle-number lemmas, the one-cut per-card-position bound and the
two form-2 mixing statements.
The whole cone is computed below under "The dependency cone of the three
theorems", declaration by declaration, rather than read off the statements:
a home argument that asks only what the three statements mention describes an
arrangement the kernel rejects, because the lemmas their proofs call would be
left in the file above them.

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

What the new file holds is the whole cone, not the three theorems:
`fc_sigma_pow5_eq1`, `fc_sigma_pow_point_inj`, `fc_sigma_pow_ord_inj`,
`fc_kim_word_eval_powE`, `fc_kim_rho_supp_pow`, `five_card_ideal_supp_pow`,
`five_card_ideal_point_uniform`, `kim_single_cut_supp_pow`,
`kim_centi_cut_supp_pow`, `fc_arrange_countE`, `den_boer_layout_law_const`,
`five_card_cut_mixing_of_supp_pow` and `kim_biased_marginal_bound`, then
`kim_centi_cut_mixing`, `kim_biased_cut_mixing` and
`five_card_static_obs_const`: sixteen declarations, the fourteen dagger rows
of the table above. Of the probe's remaining thirty-five declarations,
`instances/kim2025/five_card_rows.v` keeps twenty-nine, the other six being
the generic lemmas of `var_dist_injective_probe.v` named below. The
twenty-nine, enumerated from the sources rather than described: the four
certificates `kim_centi_cert`, `kim_biased_cert`, `kim_centi_cert40` and
`kim_biased_cert_exact` with the tying field `kim_biased_sample_cut_witnessE`
and the two form-2 marginal bounds `kim_centi_marginal_bound40` and
`kim_biased_marginal_bound_exact`; the four row programs
`five_card_row_repeated_spectral_tableau`, `five_card_row_biased_ideal_tableau`,
`five_card_row_repeated39` and `five_card_row_biased_inv25`; their eight
number and published-field lemmas `kim_centi_cert_epsE`,
`kim_centi_cert_eps_lt`, `kim_biased_cert_epsE`, `kim_biased_cert_eps_lt2`,
`kim_centi_cert40_epsE`, `five_card_row_repeated_spectral_publishedE`,
`five_card_row_biased_ideal_publishedE` and
`five_card_row_biased_forms_publishedE`, together with the four recorded
`Fail`s `five_card_row_repeated_spectral_rowE`,
`five_card_row_biased_ideal_rowE`, `five_card_row_repeated39_bare` and
`five_card_row_biased_inv25_rowE`, which are not counted among the
twenty-nine; the
two repricing identities `five_card_pow2_39_split` and
`five_card_inv50_split` and the three repricing definitions and bounds
`five_card_reprice39`, `five_card_reprice_inv25` and
`five_card_reprice_inv25_lt2`; the two bundle-number lemmas `kim_biased_epsE`
and `kim_biased_exact_le_eps`; the one-cut per-card-position bound
`kim_one_cut_centi_le`; and the two form-2 mixing statements
`kim_centi_cut_mixing40` and `kim_biased_cut_mixing_exact`.

The two form-2 mixing statements stay above because what the facade aliases
is the mixing field of the certificate a landed row publishes, which the
manifest then names as that row's base premise. The two form-1 rows publish
`kim_centi_cert` and `kim_biased_cert`, whose mixing fields are
`kim_centi_cut_mixing` and `kim_biased_cut_mixing`
(`kim_spectral_rows_probe.v:73`, `:87`), and those two are the ones that move.
Should a landing publish a form-2 row instead, `five_card_row_repeated39`
carrying `kim_centi_cert40` (`:267`) or `five_card_row_biased_inv25` carrying
`kim_biased_cert_exact` (`:344`), that row's form-2 mixing statement takes the
dagger and the form-1 one it replaces loses it, because a statement no
published certificate carries is named nowhere above the facade. The form
choice is open in S7 and is the user's, so this rule is stated rather than
resolved.

Checked with the same script that computes the cone: no declaration among the
sixteen that move references any of the twenty-nine that stay, so option 2 is
not a cycle in this direction either. The four generic
lemmas the cone also reaches, `var_dist_fdistmap_supp_inj`,
`fdistmap_inj_uniform_id`, `fdistmap_neq0_codom` and `card_tnth_count`, are
below the new file under either option, since they go to `lib/` or to
`den_boer_encoding.v`.

Nothing in the cone reaches the manifest, the Tableau files or the facade.
Checked mechanically: over the sixteen declarations' own spans in the probe's
`.glob` files, the number of references into `pgg_analysis_manifest`,
`pgg_analysis_status`, `pgg_tableau`, `pgg_tableau_syntax`,
`five_card_analysis` and `five_card_rows` is zero. The one thing that would
have made option 2 a cycle was a file-level import, not a reference:
`kim_sc_close_probe.v` carried
`From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.`,
which no identifier in that file used. It is removed in this revision and all
five files still compile, so the landed `five_card_mixing.v` must not carry
it back.

Files recompiled: **11**. The one file added over option 1 corrected is the
new `instances/kim2025/five_card_mixing.v`; `five_card_analysis.v` is in
both, and its own eight reverse-dependants are already among the nine.
`instances/psl211/psl211_endpoints.vo` is in neither set.

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

### The dependency cone of the three theorems

What option 2 moves is not the three theorems but their forward cone, and the
cone is computed rather than listed by hand. Each `.glob` file records every
declaration as `<kind> <start>:<end> <secpath> <name>` and every reference as
`R<start>:<end> <libpath> <secpath> <name> <kind>`, with byte offsets into the
`.v` file. A declaration owns the bytes from its own name position to the end
of its proof, so a probe-local reference inside that span is an edge. The cone
is the transitive closure of those edges. Two boundaries matter: the span is
cut at `Qed.`, `Defined.` or `Admitted.`, and at the next top-level `Print`,
`Check`, `Fail`, `Timeout`, `Eval`, `End`, `Section` or `Variable`, so that a
trailing `Print Assumptions` line does not attribute its references to the
declaration above it. Without that cut `var_dist_le2` and
`var_dist_fdistmap_const_neq` appear in the constancy cone, and they are not
in it.

The script reads byte offsets from the `.glob` files and line boundaries from
the `.v` files, so the two must come from the same compile. A `.glob` written
before a later source edit gives a smaller cone with no warning. Run against
the `.glob` files as they stood at the start of the fourth fix pass, written
before the third pass deleted a `Require` from `kim_sc_close_probe.v` and
rewrote a comment in `five_card_rotation_probe.v`, the same script printed
0, 1, 6 and a union of 7. The five `.glob` files beside this probe were
regenerated
from the current sources on 2026-09-19, in `_CoqProject` order, each compile
returning 0, and the script as published reproduces the output below against
them. The result does not rest on the script: the round-4 soundness auditor
and the round-4 naming auditor each recomputed the cone from the sources
alone, reading no `.glob`, by cutting each declaration's span at its `Qed`,
`Defined` or `Admitted` or at the next top-level command, stripping comments
and closing over whole-word references, and both got 12, 13 and 6 with the
same members and the same union of 17.

```python
import os, re
from collections import OrderedDict

G = "<directory holding the five .v files and their .glob files>"
FILES = ["var_dist_injective_probe", "five_card_rotation_probe",
         "kim_sc_close_probe", "five_card_sc_const_probe",
         "kim_spectral_rows_probe"]
DECL_KINDS = {"def", "prf", "thm", "ax", "ind", "constr"}
ABOVE = {"pgg_smc.pgg_analysis_manifest", "pgg_smc.pgg_analysis_status",
         "pgg_smc.pgg_tableau", "pgg_smc.pgg_tableau_syntax",
         "pgg_smc.five_card_analysis", "pgg_smc.five_card_rows"}

decls, spans, refs = OrderedDict(), {}, {f: [] for f in FILES}
for f in FILES:
    dl = []
    for line in open(os.path.join(G, f + ".glob")):
        line = line.rstrip("\n")
        m = re.match(r"^R(\d+):(\d+) (\S+) (\S+) (\S+) (\S+)$", line)
        if m:
            refs[f].append((int(m.group(1)), m.group(3), m.group(5), m.group(6)))
            continue
        m = re.match(r"^(\w+) (\d+):(\d+) (\S+) (\S+)$", line)
        if m and m.group(1) in DECL_KINDS:
            dl.append((int(m.group(2)), m.group(5)))
    dl.sort()
    src = open(os.path.join(G, f + ".v"), "rb").read()
    size = len(src)
    starts = [0] + [i + 1 for i, b in enumerate(src) if b == 0x0A]
    STOP = (b"Print ", b"Check ", b"Fail ", b"Timeout ", b"Eval ", b"Compute ",
            b"About ", b"Search ", b"End ", b"Section ", b"Variable ",
            b"Hypothesis ", b"Context ")
    CLOSE = (b"Qed.", b"Defined.", b"Admitted.", b"Abort.")

    def body_end(begin, cap):
        for ls in starts:
            if ls <= begin:
                continue
            if ls >= cap:
                break
            le = src.find(b"\n", ls)
            line = src[ls:le if le >= 0 else size]
            if line.startswith(CLOSE):
                return ls + len(line)
            if line.startswith(STOP):
                return ls
        return cap

    spans[f] = []
    for i, (s, n) in enumerate(dl):
        cap = dl[i + 1][0] if i + 1 < len(dl) else size
        spans[f].append((s, body_end(s, cap), n))
        decls[n] = (f, s)

edges = {n: set() for n in decls}
above_hits = {n: set() for n in decls}
for f in FILES:
    for start, end, owner in spans[f]:
        for pos, lib, name, kind in refs[f]:
            if not (start <= pos < end):
                continue
            if lib.startswith("kim_spectral_arm_probe.") and kind in DECL_KINDS:
                if name in decls and name != owner:
                    edges[owner].add(name)
            elif lib in ABOVE:
                above_hits[owner].add(lib + "." + name)

def closure(root):
    seen, stack = set(), [root]
    while stack:
        x = stack.pop()
        for y in sorted(edges.get(x, ())):
            if y not in seen:
                seen.add(y); stack.append(y)
    return seen
```

Output:

```
declarations found: 56

=== cone of kim_centi_cut_mixing: 12 probe-local declarations ===
    var_dist_fdistmap_supp_inj         var_dist_injective_probe.v
    fdistmap_inj_uniform_id            var_dist_injective_probe.v
    fdistmap_neq0_codom                var_dist_injective_probe.v
    fc_sigma_pow5_eq1                  five_card_rotation_probe.v
    fc_sigma_pow_point_inj             five_card_rotation_probe.v
    fc_sigma_pow_ord_inj               five_card_rotation_probe.v
    fc_kim_word_eval_powE              five_card_rotation_probe.v
    fc_kim_rho_supp_pow                five_card_rotation_probe.v
    five_card_ideal_supp_pow           five_card_rotation_probe.v
    five_card_ideal_point_uniform      five_card_rotation_probe.v
    kim_centi_cut_supp_pow             five_card_rotation_probe.v
    five_card_cut_mixing_of_supp_pow   kim_sc_close_probe.v

=== cone of kim_biased_cut_mixing: 13 probe-local declarations ===
    var_dist_fdistmap_supp_inj         var_dist_injective_probe.v
    fdistmap_inj_uniform_id            var_dist_injective_probe.v
    fdistmap_neq0_codom                var_dist_injective_probe.v
    fc_sigma_pow5_eq1                  five_card_rotation_probe.v
    fc_sigma_pow_point_inj             five_card_rotation_probe.v
    fc_sigma_pow_ord_inj               five_card_rotation_probe.v
    fc_kim_word_eval_powE              five_card_rotation_probe.v
    fc_kim_rho_supp_pow                five_card_rotation_probe.v
    five_card_ideal_supp_pow           five_card_rotation_probe.v
    five_card_ideal_point_uniform      five_card_rotation_probe.v
    kim_single_cut_supp_pow            five_card_rotation_probe.v
    five_card_cut_mixing_of_supp_pow   kim_sc_close_probe.v
    kim_biased_marginal_bound          kim_sc_close_probe.v

=== cone of five_card_static_obs_const: 6 probe-local declarations ===
    fdistmap_inj_uniform_id            var_dist_injective_probe.v
    card_tnth_count                    var_dist_injective_probe.v
    fc_sigma_pow_ord_inj               five_card_rotation_probe.v
    five_card_ideal_point_uniform      five_card_rotation_probe.v
    fc_arrange_countE                  five_card_sc_const_probe.v
    den_boer_layout_law_const          five_card_sc_const_probe.v

=== union of the three cones: 17 ===
    var_dist_fdistmap_supp_inj         var_dist_injective_probe.v
    fdistmap_inj_uniform_id            var_dist_injective_probe.v
    fdistmap_neq0_codom                var_dist_injective_probe.v
    card_tnth_count                    var_dist_injective_probe.v
    fc_sigma_pow5_eq1                  five_card_rotation_probe.v
    fc_sigma_pow_point_inj             five_card_rotation_probe.v
    fc_sigma_pow_ord_inj               five_card_rotation_probe.v
    fc_kim_word_eval_powE              five_card_rotation_probe.v
    fc_kim_rho_supp_pow                five_card_rotation_probe.v
    five_card_ideal_supp_pow           five_card_rotation_probe.v
    five_card_ideal_point_uniform      five_card_rotation_probe.v
    kim_single_cut_supp_pow            five_card_rotation_probe.v
    kim_centi_cut_supp_pow             five_card_rotation_probe.v
    five_card_cut_mixing_of_supp_pow   kim_sc_close_probe.v
    kim_biased_marginal_bound          kim_sc_close_probe.v
    fc_arrange_countE                  five_card_sc_const_probe.v
    den_boer_layout_law_const          five_card_sc_const_probe.v

=== references above the facade, inside the three theorems and their cone ===
    none
```

Thirteen of the seventeen are instance-specific and move with the three
theorems under option 2, which with the theorems themselves is the sixteen
declarations of the fourteen dagger rows. The other four,
`var_dist_fdistmap_supp_inj`, `fdistmap_inj_uniform_id`,
`fdistmap_neq0_codom` and `card_tnth_count`, are the generic lemmas already
bound for `lib/` or for `den_boer_encoding.v` under either option.

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
   the sum of absolute differences, `\sum_a |P a - Q a|`, twice the total
   variation distance, so the ceiling is 2. That ceiling is `var_dist_le2`.
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
| N6, F3 | The landing change list in S8 is rewritten and carries both manifest rows and the compile breakage at `five_card_rows.v:456`. Its round-1 claim to carry "every" header and docstring passage a landing makes false is withdrawn: round 2 found the list missing three `erefl` row pins and the manifest's Row 4 and Row 5 header tables, and the further search this pass ran added two more pins in the manifest and the whole of the five-card facade's section 7. What the list states now is the result of a whole-tree grep for the two row names, for the facade's two typed transfer statuses, and for the manifest's status vocabulary at those rows, each result read in the source. Round 3 then found three more classes of item that no name-keyed search reaches, the manifest's three passages about the development, the header index and file-title line of `five_card_rows.v`, and the facade's own file header, and the claim to completeness is withdrawn altogether rather than restated; see "Round 3 audits and what changed". |
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
| B1 | blocking | "constancy" replaces "invariance" as the prose name of the `sc_const` field at all eleven sites, five in the `.v` files and six here. It is the tree's word for that field at nine sites in six files, `manifest/pgg_tableau.v:37,126,129,557`, `manifest/pgg_tableau_syntax.v:140`, `instances/pgl27/pgl27_rows.v:244`, `instances/s5/s5_rows.v:66`, `instances/psl211/psl211_rows.v:41` and `instances/kim2025/five_card_rows.v:41`, all read for this pass. The audit says seven files and lists six; six is what a whole-tree grep returns. The only other "constancy" in the tree, `reconstruct/s5_nogo.v:53`, is about a different object and is not a name for this field. `invariant by` as a Tableau surface keyword is untouched, and it does not occur in this probe. |
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

## Round 3 audits and what changed

The second fix pass was audited twice again on 2026-09-19, for soundness
(`soundness-audit-round3.md`, blocking H1-H4, should-fix H5 and H10, notes
H6-H9) and for names (`naming-audit-round3.md`, blocking B-1 to B-4,
should-fix S-1 to S-6, notes a-h). Both returned NO-GO, and both on text
alone: no audit in this round disputed a proof, a statement or a number that
the kernel checks, and neither found an `Admitted`, `Axiom`, `admit` or
`Abort` anywhere in the five files. The five `.v` files and this file as the
second fix pass left them are kept in `history/`, suffixed
`.2026-09-19-before-fix3`.

This pass changed two lines of code and nothing else in any `.v` file. With
comments stripped, four of the five files are byte-identical to their
`before-fix3` copies and the fifth differs by one deleted `Require` line.
All five recompile, in `_CoqProject` order, with real exit status 0.

| finding | severity | disposition |
|---|---|---|
| H2 | blocking | Applied first, as the one finding about the mathematics. `var_dist_fdistmap_transfer`'s hypotheses are `PQ_close` (`security/pgg_collusion_bound.v:980`) then `ideal_eq` (`:981`), and `spectral_tail` (`manifest/pgg_tableau.v:561-570`) fills them in that order, mixing at `:569` and constancy at `:570`. So the mixing field discharges the FIRST hypothesis and the constancy field IS the second, the ideal distribution equality. Both sentences that said otherwise are corrected, the Row 4 table cell and facade item 1, and S8 now states the order once with its line citations so a landing plan cannot re-derive it wrongly. Every "first hypothesis" and "second hypothesis" in this file was re-read against the source: the two quoted passages, the facade's section header and the manifest's Row 3 cell, are right as quoted and are left as they are. |
| H1 | blocking | Applied. A new S8 subsection, "Three further manifest passages about the development, not about a row", carries `manifest/pgg_analysis_manifest.v:244-248`, `:753-755` and `:669-673` with their text quoted and each line re-read in the source. `:244-248` is named as the anchor Rows 4 and 5 point at with "as in row 3". The passage at `:669-673` is taken clause by clause rather than sentence by sentence, because its three clauses do not move together: "No transfer-layer result exists" and the absent-premise clause are false under either option, while "section 7 of its facade carries typed status aliases and no theorem" is false only under option 2. The same reading is applied to the facade's own section header at `:351-358`. |
| H3 | blocking | Applied as item 9 of the `five_card_rows.v` list: the header index at `:78-86` and `:119-122` and the file-title line at `:4`, each read in the source. |
| H4 | blocking | Decided, not merely recorded. The two `Tableau Sampled` programs are KEPT with their type and the certified programs are added beside them, on the owner's design principle that one row states one security claim. The decision is stated at the head of the `five_card_rows.v` list, with the reason the alternative is unavailable: `tableau_at` is a projection of `TableauAt` (`manifest/pgg_tableau.v:411-414`) and a published row is a `PublishedRowAt` (`:678-681`). Items 1, 7 and 8 and the closing "stays true" paragraph are each revisited against the decision. The list also records that no program in the tree continues from a named `Tableau Sampled` value today, so the construction is unverified and is row T0 of `notes/20260919-tableau-three-extensions-probe-design.md:169`. |
| H5 | should-fix | Applied as item 6 of the facade list: `instances/kim2025/five_card_analysis.v:16-17` and the phase-H1 check table at `:30-57`, with the manifest's pinning obligation at `:67-72` named. |
| H10 | should-fix | Applied as a code change. `kim_sc_close_probe.v:21`, `From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.`, is deleted. All five files then recompile with real exit status 0, which is the evidence that the import was dead. The same line in `kim_spectral_rows_probe.v:21` was tested the same way in a copy and is live: without it the file fails at `:49` with "The reference amf_sample was not found", `amf_sample` being a field of `AnalysisModelFamily` at `manifest/pgg_analysis_status.v:99-102`. The three remaining files carry no such Require. The option-2 paragraph records that the landed `five_card_mixing.v` must not carry the import back. |
| H6 | note | Applied. The file has two `prefixE` lemmas, at `five_card_rows.v:418` and `:428`. Folded into B-4's rewrite. |
| H7 | note | Applied. Item 2's range is `:28-30` and item 3's is `:33-42`, both read in the source; `:39-42` is named as the subordinate clause inside the sentence that begins at `:33`. |
| H8 | note | Applied through B-3. The grep was rerun for this pass and its full result is reported. |
| H9 | note | Applied, matching the reading H4 settles. Under the decision to keep the two programs, "both stop at `Sampled`" stays true of those two declarations, so item 2 says obsolete and says why; the next sentence, "The repeated row stops there because the manifest does", is marked false outright. |
| B-1 | blocking | Applied. The sentence claiming the freeze rule is respected by every home on the page is replaced. `psl211_endpoints` is in the closures of the first four rows, which is why none of those four is proposed as a home, and in none of the closures of the other eleven and in none of the five landing sets. |
| B-2 | blocking | Applied, with the cone computed rather than hand-listed. A new subsection, "The dependency cone of the three theorems", carries the script, its output and the two span boundaries that make it right. The three theorems reach thirteen further instance-specific declarations, which with themselves is sixteen, the fourteen dagger rows of the S10 table; `kim_biased_marginal_bound` is split out of the "bounds and the certificates" row because a mixing statement names it. Option 2 is restated as the new file holding that whole cone, with `five_card_rows.v` keeping only the certificates, the programs, their row lemmas and the repricing identities. The same script confirms that nothing in the cone references the manifest, the Tableau files or the facade. |
| B-3 | blocking | Applied. The grep was rerun over the 133 `.v` files of the twelve production directories and its full result reported: the facade's alias table and declarations, the manifest's Row 4 and Row 5 table lines at `:293`, `:315`, `:322`, `:340-341` and `:370`, the row definitions at `:768` and `:778`, three bare `Check`s in `pgg_analysis_client.v` and eleven spelled-type `Check`s. Three of those sites are already in the list under their own headings; none of the others states a level or a status. |
| B-4 | blocking | Applied, with the file's declarations enumerated from the source: twenty-eight `Definition`, `Lemma` and `Theorem` commands and three recorded `Fail`s, four and one of which are in the list above. The other twenty-four and two are named individually with their line numbers. |
| S-1 | should-fix | Applied. The B1 disposition row says nine sites in six files, which is what a whole-tree grep returns; `reconstruct/s5_nogo.v:53` is the tenth occurrence and is about a different object, as that row already says. |
| S-2 | should-fix | Applied as the first of the two code changes. `fc_kim_rho_supp_pow`'s comment (`five_card_rotation_probe.v:90-95`) no longer narrates the proof or points at a sibling declaration. It now says what the quantifier over the weighting adds: one statement covers all of Kim's cut laws, so each of them and the uniform rotation law live on one group. The audit's replacement text is used verbatim; every line is inside 80 bytes. |
| S-3 | should-fix | Applied. "Neither round-2 audit names this file" is replaced by the narrower and true claim, that neither reaches the file's typed transfer statuses. |
| S-4 | should-fix | Applied. The N6/F3 row now credits round 2 with three `erefl` row pins and the two header tables, and this pass's further search with the two extra pins and the facade's section 7, which is what the G1 row says. |
| S-5 | should-fix | Applied. The compile-table sentence no longer says the kernel rejects the `erefl` of `five_card_row_biased_forms_publishedE`, which is a `Lemma` closed by `Qed`. Only the `Fail` elaborates a published row before its `erefl` is rejected. |
| S-6 | should-fix | Applied. The Row 5 cell now quotes the sentence that closes the paragraph at `:379-380`, "A ShuffleCertificateBundle exists for both models and does not raise the level", and says that a landing falsifies it because the certificate that raises the level is built from that bundle's `scb_bound`. |

### Round 3 findings not applied

- **naming note c**, that the three rows appended to the S10 table in the
  previous revision leave it out of descending order of reverse-dependants.
  The audit calls it cosmetic and confirms every figure. Reordering the table
  would move rows a reader may be citing by position; left as it is.
- **naming note f**, that `Section five_card_static_obs_const`
  (`five_card_sc_const_probe.v:46`) encloses
  `Lemma five_card_static_obs_const` (`:91`). Recorded since round 2. It is a
  code change and this pass's two code changes were fixed in advance; it
  stays a one-line edit for whoever lands the file.
- **naming notes a, d, g and h**, and **soundness note G7's successor**: each
  states that no change is needed, and none is made.
- **round 2's notes d and f**, the `(**` and `(*` split at
  `five_card_pow2_39_split` and the instance prefix moving with the two
  identities if they go to `lib/`. Both remain open and both are recorded
  above under "Round 2 findings not applied".
- The style observations carried over from the previous session,
  `boolp.funext` written fully qualified, `apply: funext` where `apply/ffunP`
  would serve, and `@` on several applied lemmas. They are code changes, they
  are in no audit, and they are left for a landing pass.

## Round 4 audits and what changed

The third fix pass was audited twice on 2026-09-19, for soundness
(`soundness-audit-round4.md`, blocking I1 and I2, should-fix I3 and I4, notes
I5-I8) and for names (`naming-audit-round4.md`, blocking B4-1 to B4-4,
should-fix S4-1 to S4-4, notes a-f). Both returned NO-GO. Three of the eight
substantive findings are the same defect seen from two sides: I3 is B4-1, I4
is S4-4, and I5 is S4-2. No audit in this round disputed a proof, a statement
or a number the kernel checks. The five `.v` files and this file as the third
fix pass left them are in `history/`, suffixed `.2026-09-19-before-fix4`.

One `.v` character changed in this pass, the statement comment of
`fc_kim_rho_supp_pow`. Comments stripped, the five files are byte-identical to
their `before-fix4` copies, and all five recompile with return code 0.

| ID | Severity | Disposition |
|---|---|---|
| I1 | blocking | Applied. The sentence saying the certified programs continue from the two `Tableau Sampled` values is gone; the four are full chains from `five_card_committed`, as S6 and S7 already print them. The reason the four `prefixE` and `modelE` lemmas survive is now that the two named values keep their type. The false universal about the tree is replaced by the true one, each instance chaining from its own `Tableau Observed` prefix, with the five programs cited. T0 is recorded as no obligation of this landing. |
| I2 | blocking | Applied. The seven-proposition list is reopened and extended by the four the Row 4 and Row 5 tables already record: no shuffle certificate on the biased path, the repeated path's bound list, its absent final bridge theorem, and the bundle that does not raise the level. The closing sentence now says the list is open and tells a landing batch to extend it from the Row 3, Row 4 and Row 5 tables and the facade's section 7 before searching. |
| I3 = B4-1 | blocking / should-fix | Applied both ways. The five files were recompiled in place, in `_CoqProject` order, so the `.glob` files match the sources; the script as published then prints 12, 13, 6 and union 17 against them. A sentence above the script records that the two must come from the same compile, what the stale run printed, and that both auditors reproduced the cone by a text method reading no `.glob`. |
| I4 = S4-4 | should-fix | Applied. "keeps only" is replaced by the twenty-nine declarations enumerated from the sources, and the S10 table gains four rows covering the eight that had none. The two form-2 mixing statements stay above, because what the facade aliases is the mixing field of the certificate a landed row publishes, and the two rows written above publish `kim_centi_cert` and `kim_biased_cert`. |
| B4-2 | blocking | Applied. Section 7 has three theorems to alias, the two mixing theorems and the constancy theorem, which is what the aliases count says. |
| B4-3 | blocking | Applied. Two of the twenty-six do mention a row's level and status, `five_card_row_uniform_tableau` through its `publish` step and `five_card_row_uniform_rowE` by conversion. Both are about the uniform row, which a spectral landing does not restatus, so the conclusion stands on that reason instead. |
| B4-4 | blocking | Applied, the one `.v` edit. The covering quantifier is the one over the word length, not the one over the weighting: the two Kim cut laws derived here share the bias `1/100` and differ only at lengths 1 and 7. The defective sentence was round 3's own S-2 replacement text applied verbatim, so an audit's wording is checked against the lemma like any other text. |
| S4-1 | should-fix | Applied. Nine spelled-type `Check`s at eleven lines, not eleven `Check`s: the manifest's five are opened at `:1207`, `:1214`, `:1221`, `:1233` and `:1245`, beside the three sampler `Check`s and the facade's one. |
| S4-2 = I5 | should-fix / note | Applied. The `five_card_row_uniform` docstring citation is `:753-755`; "reaching" is the last word of `:753`. The H1 disposition row is corrected to match. |
| S4-3 | should-fix | Applied. The superseded paragraph covered twelve of the twenty-six, eight by name and four by suffix. |
| I6 | note | Applied. Item 5 now names both clauses of the docstring that go false and gives each its own reason, the second being that the manifest's level for the repeated row moves while the program's stays. |
| I7 | note | Applied as part of S4-3, which is the same sentence. |
| I8 | note | Applied. `coqc` halts at the first error, so the compile pass is an iteration. |
| vocabulary | owner's rule | Applied. The one place that named `var_dist` after the Lebesgue exponent now calls it the sum of absolute differences, twice the total variation distance, ceiling 2, which is `var_dist_le2`. In this project `L` is a word length, so that spelling reads as a word of length one. A whole-word grep for it now returns nothing in this file or in the five `.v` files. |

Line numbers the audits cite that the source does not bear, corrected while
applying: I2's citations of this file's Row 5 cells are `:605` and `:606`, not
`:606` and `:607`. I4 names five declarations with no S10 row; the script
finds eight, adding `kim_biased_epsE`, `kim_biased_exact_le_eps` and
`five_card_reprice_inv25_lt2`. S4-4 names ten declarations outside the prose
enumerations; there are eleven, the eleventh being
`kim_biased_sample_cut_witnessE`, which does have an S10 row.

### Round 4 findings not applied

- **naming notes a, b, c and f**: each states that no change is needed, and
  none is made.
- **naming note d**, that the five compile times could not be checked in a
  read-only round. This pass recompiled all five: 4.4 s, 4.2 s, 5.4 s, 4.2 s
  and 10.9 s, against the recorded 4.5, 4.2, 5.4, 4.2 and 10.9.
- **naming note e**, that `Section five_card_static_obs_const`
  (`five_card_sc_const_probe.v:46`) encloses the lemma of the same name. Open
  since round 2. It is a code change and this pass changed one comment only;
  it stays a one-line edit for whoever lands the file.
