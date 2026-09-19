(* Audit scratch, second soundness round. Conversion questions only.
   Not part of the landing. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_instance pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_monodromy_profile.
From pgg_smc Require Import five_card_kim five_card_exec five_card_models.
From pgg_smc Require Import den_boer_profile.
From pgg_reconstruct Require Import algebraic_rigidity.
From pgg_smc Require Import pgg_analysis_status.
From kim_landing_probe Require Import five_card_mixing.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(* Q-A: is profile_k at this instance literally 2, i.e. "at most one seat"? *)
Lemma audit_profile_k_is_2 :
  profile_k (instance_profile five_card_algebra) = 2.
Proof. by []. Qed.

(* Q-B: is the adapter of the biased family convertible with kim_single_sample
   at bias one hundredth?  If yes, the certificate's tying field typechecks by
   conversion and no further lemma is needed. *)
Lemma audit_biased_family_conv (R : realType) :
  sa_cut_dist (amf_sample kim_biased_family R tt)
  = sa_cut_dist (@kim_single_sample R (1 / 100)
                   (kim_centi_lt R) (kim_centi_gt R)).
Proof. by []. Qed.

(* Q-C: is the seven-cut tying equation a conversion?  STATUS says the two
   sides "are not convertible". *)
Goal forall R : realType,
  sa_cut_dist (amf_sample kim_centi_family R tt)
  = sw_rho_dist (scb_bound (kim_security_bundle_centi R)).
Proof. move=> R. Fail by []. Abort.

(* Q-D: the one-cut tying equation, likewise. *)
Goal forall R : realType,
  sw_rho_dist (kim_biased_marginal_bound R)
  = sa_cut_dist (amf_sample kim_biased_family R tt).
Proof. move=> R. Fail by []. Abort.
