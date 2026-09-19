(* PROBE, notes/probes/2026-09-19-kim-spectral-arm/kim_sc_close_probe.v       *)
(* Ledger rows S3 and S4 of                                                   *)
(* notes/20260919-kim-spectral-arm-probe-design.md.                           *)

From HB Require Import structures.
Require Import Lia.
From mathcomp Require Import zify.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import morphism.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_collusion_bound.
From pgg_smc Require Import pgg_weighted_words.
From pgg_smc Require Import pgg_monodromy_profile.
From pgg_smc Require Import pgg_instance pgg_functionality pgg_sample_adapter.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_encoding den_boer_profile.
From pgg_smc Require Import five_card_exec five_card_models.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_reconstruct Require Import algebraic_rigidity.
From kim_spectral_arm_probe Require Import var_dist_injective_probe.
From kim_spectral_arm_probe Require Import five_card_rotation_probe.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section five_card_cut_mixing.
Variable R : realType.

(******************************************************************************)
(*     The distance on the cut group, from the distance at one position       *)
(******************************************************************************)

(* A cut law carried by the powers of the five-cycle is within its own
   per-position bound of the uniform rotation law, as a distance on the cut
   group itself. The stabiliser of a card position in the rotation group is
   trivial, so reading one position loses nothing between two laws both
   carried by the rotations, and the number a shuffle certificate states
   about one position is already the group-level number the spectral arm
   asks for. *)
Lemma five_card_cut_mixing_of_supp_pow
    (b : ShuffleMarginalBound R (instance_M five_card_algebra)) :
  (forall g : {perm 'I_5}, sw_rho_dist b g != 0 ->
     exists k : nat, g = (fc_sigma ^+ k)%g) ->
  var_dist (sw_rho_dist b) (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps b.
Proof.
move=> Hsupp.
have Hinj : forall g h : {perm 'I_5},
    (sw_rho_dist b g != 0) || (sa_cut_dist (five_card_sample R) g != 0) ->
    (sw_rho_dist b h != 0) || (sa_cut_dist (five_card_sample R) h != 0) ->
    g ord0 = h ord0 -> g = h.
  move=> g h /orP Hg /orP Hh Hgh.
  have [jg Hjg] : exists k : nat, g = (fc_sigma ^+ k)%g.
    by case: Hg => [/Hsupp//|/five_card_ideal_supp_pow].
  have [jh Hjh] : exists k : nat, h = (fc_sigma ^+ k)%g.
    by case: Hh => [/Hsupp//|/five_card_ideal_supp_pow].
  rewrite Hjg Hjh; apply: (@fc_sigma_pow_point_inj ord0).
  by rewrite -Hjg -Hjh.
rewrite -(var_dist_fdistmap_supp_inj Hinj) five_card_ideal_point_uniform.
exact: (sw_bound b ord0).
Qed.

(******************************************************************************)
(*     S3: the repeated row, at the seven-cut bundle                          *)
(******************************************************************************)

(* The seven-cut law of Kim's repeated row is within the bundle's own
   spectral number of the uniform rotation law, in variation distance on
   the cut group. This is the mixing field of the spectral certificate for
   that row. The number is the bundle's and no new one is introduced, so
   the row's only inexact quantity is that spectral number. *)
Lemma kim_centi_cut_mixing :
  var_dist (sw_rho_dist (scb_bound (kim_security_bundle_centi R)))
           (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps (scb_bound (kim_security_bundle_centi R)).
Proof.
by apply: five_card_cut_mixing_of_supp_pow; exact: kim_centi_cut_supp_pow.
Qed.

(******************************************************************************)
(*     S4: the biased row, at the word-length-one bundle                      *)
(******************************************************************************)

(* The marginal bound Kim's bundle carries at bias one hundredth and word
   length one. It bounds, at every card position, the distance between the
   law that position takes under one biased cut and the uniform law, which
   is the form the spectral arm turns into a distance on the cut group. *)
Definition kim_biased_marginal_bound
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  scb_bound (@fc_kim_security_bundle R (1 / 100)
               (kim_centi_lt R) (kim_centi_gt R) (kim_centi_spec R) 1).

(* Kim's one-cut law is within the bundle's own spectral number of the
   uniform rotation law, in variation distance on the cut group. This is
   the mixing field of the spectral certificate for the one-cut row, at a
   number of hundredth scale rather than a cryptographic one. *)
Lemma kim_biased_cut_mixing :
  var_dist (sw_rho_dist kim_biased_marginal_bound)
           (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps kim_biased_marginal_bound.
Proof.
by apply: five_card_cut_mixing_of_supp_pow; exact: kim_single_cut_supp_pow.
Qed.

(******************************************************************************)
(*     The two numbers                                                        *)
(******************************************************************************)

(* The one-cut bundle's marginal bound is sqrt 5 over eighty. The one-cut
   row publishes twice that, because the triangle inequality through the
   ideal spends the number once for each of the two committed pairs. *)
Lemma kim_biased_epsE :
  sw_bound_eps kim_biased_marginal_bound = Num.sqrt 5%:R * (1 / 80).
Proof. by rewrite /kim_biased_marginal_bound /= kim_lambda2_at_centi expr1. Qed.

(* The exact one-cut distance of kim_one_cut_centiE, one fiftieth, is below
   the spectral bound the certificate publishes, sqrt 5 over eighty. The
   certificate's number is therefore an overestimate of the distance it
   certifies, and the row is honest rather than tight. *)
Lemma kim_biased_exact_le_eps :
  1 / 50 <= sw_bound_eps kim_biased_marginal_bound :> R.
Proof.
rewrite kim_biased_epsE -(@ler_pXn2r R 2 isT).
2: by rewrite nnegrE divr_ge0.
2: by rewrite nnegrE mulr_ge0 ?sqrtr_ge0 ?divr_ge0.
rewrite [X in _ <= X]exprMn sqr_sqrtr ?ler0n //.
rewrite !expr_div_n !expr1n [X in _ <= X]mulrA mulr1.
rewrite ler_pdivrMr ?exprn_gt0 ?ltr0n // mulrAC.
rewrite ler_pdivlMr ?exprn_gt0 ?ltr0n // mul1r.
rewrite -!natrX -natrM ler_nat.
by lia.
Qed.

End five_card_cut_mixing.

Print Assumptions kim_centi_cut_mixing.
Print Assumptions kim_biased_cut_mixing.
Print Assumptions kim_biased_exact_le_eps.
