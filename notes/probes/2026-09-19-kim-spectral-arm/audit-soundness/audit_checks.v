(* AUDIT SCRATCH -- not part of the repository, never imported by one.     *)
(* Adversarial checks of notes/probes/2026-09-19-kim-spectral-arm.         *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import morphism.
From mathcomp Require Import boolp reals.
From mathcomp Require Import lra.
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
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import five_card_rows.
From pgg_reconstruct Require Import algebraic_rigidity.
From kim_spectral_arm_probe Require Import var_dist_injective_probe.
From kim_spectral_arm_probe Require Import five_card_rotation_probe.
From kim_spectral_arm_probe Require Import kim_sc_close_probe.
From kim_spectral_arm_probe Require Import five_card_sc_const_probe.
From kim_spectral_arm_probe Require Import kim_spectral_rows_probe.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section audit.
Variable R : realType.

(**************************************************************************)
(*  A1  Field fidelity: the five slots hold the named terms.              *)
(**************************************************************************)

Definition A1_b (idx : unit) :
  sc_b (kim_centi_cert R idx) = scb_bound (kim_security_bundle_centi R)
  := erefl.

Definition A1_ideal (idx : unit) :
  sc_ideal (kim_centi_cert R idx) = sa_cut_dist (five_card_sample R)
  := erefl.

Definition A1_close (idx : unit) :
  sc_close (kim_centi_cert R idx) = kim_centi_sc_close R := erefl.

Definition A1_const (idx : unit) :
  sc_const (kim_centi_cert R idx) = five_card_sc_const R := erefl.

Definition A1b_ideal (idx : unit) :
  sc_ideal (kim_biased_cert R idx) = sa_cut_dist (five_card_sample R)
  := erefl.

Definition A1b_close (idx : unit) :
  sc_close (kim_biased_cert R idx) = kim_biased_sc_close R := erefl.

Definition A1b_const (idx : unit) :
  sc_const (kim_biased_cert R idx) = five_card_sc_const R := erefl.

Definition A1c40_ideal (idx : unit) :
  sc_ideal (kim_centi_cert40 R idx) = sa_cut_dist (five_card_sample R)
  := erefl.

Definition A1c50_ideal (idx : unit) :
  sc_ideal (kim_biased_cert50 R idx) = sa_cut_dist (five_card_sample R)
  := erefl.

Definition A1_eps40 : sw_bound_eps (kim_centi_bound40 R) = 2%:R ^- 40 := erefl.

Definition A1_eps50 : sw_bound_eps (kim_biased_bound50 R) = 1 / 50 :> R
  := erefl.

(* The ideal of sc_close and the ideal of sc_const are one field, so one
   term: a certificate measuring the distance against the row's own biased
   cut rather than the uniform one is rejected. *)
Fail Definition A1_wrong_ideal (idx : unit)
  : SpectralCert (amf_sample kim_centi_family R idx) :=
  @MkSpectralCert R five_card_algebra five_card_params
    (amf_sample kim_centi_family R idx)
    (scb_bound (kim_security_bundle_centi R))
    (esym (kim_centi_cut_distE R))
    (sa_cut_dist (amf_sample kim_centi_family R idx))
    (@kim_centi_sc_close R)
    (@five_card_sc_const R).

(**************************************************************************)
(*  A2  The epsilon of a marginal bound is not free.                      *)
(**************************************************************************)

Fail Definition A2_eps41
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  @MkShuffleMarginalBound R FiveCardKim_M 7 (2%:R ^- 41)
    (sw_rho_dist (scb_bound (kim_security_bundle_centi R)))
    (fun s => Order.POrderTheory.ltW (kim_deal_centi_lt R s)).

Fail Definition A2_eps100
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  @MkShuffleMarginalBound R FiveCardKim_M 1 (1 / 100)
    (@rho_from_words_weighted R 3 4 1 fc_kim_gens
       (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R)))
    (fun s => kim_one_cut_le R s).

(**************************************************************************)
(*  A3  What a seat reads: a colour, not a card identity.                 *)
(**************************************************************************)

Lemma A3_colour_only (C : {set 'I_5}) (x : bool * bool)
    (g : pgg_gT (mp_M (instance_profile five_card_algebra))) (i : 'I_5) :
  exists b : bool,
    @static_coalition_obs five_card_algebra five_card_params C x g i
    = encode_bool b.
Proof.
rewrite static_coalition_obsE; case: ifPn => iC; last first.
  by exists false; apply: val_inj; rewrite /encode_bool /= inordK.
exists (tnth (fc_arrange_tup x.1 x.2)
          (@pgg_rho FiveCardKim_M g (tnth (pi_starts FiveCardKim_PI) i))).
have -> : @ex_content_obs five_card_algebra five_card_params x
            (g, tnth (pi_starts (mp_PI (instance_profile five_card_algebra))) i)
        = tnth (den_boer_layout x)
            (@pgg_rho FiveCardKim_M g (tnth (pi_starts FiveCardKim_PI) i))
  by [].
by rewrite /den_boer_layout tnth_map.
Qed.

Lemma A3_two_valued (C : {set 'I_5}) (x : bool * bool)
    (g : pgg_gT (mp_M (instance_profile five_card_algebra))) (i : 'I_5) :
  @static_coalition_obs five_card_algebra five_card_params C x g i
  \in [:: encode_bool true; encode_bool false].
Proof.
have [b ->] := A3_colour_only C x g i.
by case: b; rewrite !inE eqxx ?orbT.
Qed.

(**************************************************************************)
(*  A4  The ceiling of a variation distance is two, unproved in the tree. *)
(**************************************************************************)

Lemma A4_var_dist_le2 (A : finType) (P Q : R.-fdist A) :
  var_dist P Q <= 2%:R.
Proof.
have Hf1 : forall d : R.-fdist A, \sum_(a : A) d a = 1.
  by move=> d; rewrite -(FDist.f1 d); apply: eq_bigl => a; rewrite inE.
rewrite /var_dist.
have -> : (2%:R : R) = \sum_(a : A) (P a + Q a).
  rewrite big_split /= !Hf1; by lra.
apply: ler_sum => a _.
rewrite -[X in _ <= X + _](ger0_norm (FDist.ge0 P a)).
rewrite -[X in _ <= _ + X](ger0_norm (FDist.ge0 Q a)).
exact: ler_normB.
Qed.

Lemma A4_pow2_39_lt2 : (2%:R ^- 39 : R) < 2%:R.
Proof.
apply: (Order.POrderTheory.le_lt_trans (y := 1)); last by rewrite ltr1n.
by rewrite invf_le1 ?exprn_gt0 ?ltr0n// exprn_ege1// ler1n.
Qed.

Lemma A4_repeated_form1_lt2 (idx : unit) :
  cert_eps (kim_centi_cert R idx) < 2%:R.
Proof.
apply: (Order.POrderTheory.lt_trans (kim_centi_cert_eps_lt R idx)).
exact: A4_pow2_39_lt2.
Qed.

Lemma A4_biased_form2_lt2 : (1 / 25 : R) < 2%:R.
Proof. by lra. Qed.

(* Form 2 of the repeated row publishes a number weaker than what form 1
   proves. *)
Lemma A4_form2_weaker (idx : unit) :
  cert_eps (kim_centi_cert R idx) < cert_eps (kim_centi_cert40 R idx).
Proof. by rewrite /cert_eps; apply: ltrD; exact: kim_bound_centi. Qed.

(* Form 2 of the one-cut row publishes a number stronger than form 1. *)
Lemma A4_biased_form2_stronger (idx : unit) :
  cert_eps (kim_biased_cert50 R idx) <= cert_eps (kim_biased_cert R idx).
Proof.
by rewrite /cert_eps; apply: lerD; exact: five_card_biased_exact_le_eps.
Qed.

(**************************************************************************)
(*  A5  What the row metadata equation does and does not carry.           *)
(**************************************************************************)

Definition A5_same_data :
  published_at kim_row_biased_spectral
  = published_at kim_row_biased_spectral_static := erefl.

Definition A5_same_thm :
  published_thm kim_row_biased_spectral
  = published_thm kim_row_biased_spectral_static := erefl.

Lemma A5_row_insensitive :
  published_row kim_row_biased_spectral_static = published_row kim_row_biased25.
Proof. by []. Qed.

Lemma A5_labels :
  apr_transfer (published_row kim_row_biased_spectral) = IdealFinite
  /\ apr_transfer (published_row kim_row_biased_spectral_static)
     = StaticExecutedOnly.
Proof. by []. Qed.

End audit.

Print Assumptions A3_colour_only.
Print Assumptions A4_var_dist_le2.
