(* Round-2 soundness audit scratch file, part 2. NOT part of the probe.
   The certified proposition written out in full and derived from the rows. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import morphism.
From mathcomp Require Import boolp reals.
From mathcomp Require Import lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import perm_uniform pgg_interface pgg_collusion_bound.
From pgg_smc Require Import pgg_weighted_words.
From pgg_smc Require Import pgg_monodromy_profile.
From pgg_smc Require Import pgg_instance pgg_functionality pgg_sample_adapter.
From pgg_smc Require Import pgg_trace_secrecy.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_encoding den_boer_run den_boer_profile.
From pgg_smc Require Import five_card_leakage five_card_exec five_card_models.
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

Local Open Scope fdist_scope.
Local Open Scope ring_scope.

(* B1. What the repriced one-cut row proves, written out. *)
Definition B1_inv25_statement (R : realType)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1})
    (x x' : ex_inputT five_card_params) :
  (#|C| < 2)%N ->
  var_dist
    (fdistmap (@static_coalition_obs five_card_algebra five_card_params C x)
       (sa_cut_dist (amf_sample kim_biased_family R tt)))
    (fdistmap (@static_coalition_obs five_card_algebra five_card_params C x')
       (sa_cut_dist (amf_sample kim_biased_family R tt)))
  <= 1 / 25
  := proj2 (published_thm five_card_row_biased_inv25) R tt C x x'.

(* B2. What the repriced repeated row proves, written out. *)
Definition B2_repeated39_statement (R : realType)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1})
    (x x' : ex_inputT five_card_params) :
  (#|C| < 2)%N ->
  var_dist
    (fdistmap (@static_coalition_obs five_card_algebra five_card_params C x)
       (sa_cut_dist (amf_sample kim_centi_family R tt)))
    (fdistmap (@static_coalition_obs five_card_algebra five_card_params C x')
       (sa_cut_dist (amf_sample kim_centi_family R tt)))
  <= 2%:R ^- 39
  := proj2 (published_thm five_card_row_repeated39) R tt C x x'.

(* B3. The cut law the statement is taken under is the row's own biased cut,
   not the ideal. *)
Definition B3_biased_cut_is_biased (R : realType)
  : sa_cut_dist (amf_sample kim_biased_family R tt)
  = sw_rho_dist (kim_biased_marginal_bound R)
  := esym (kim_biased_sample_cut_witnessE R).

(* B4. The statement is NOT independence of the reading from the secret: the
   ideal law is the uniform rotation law and the two run arguments range over
   all four committed pairs, but the distance is between two readings, not a
   product factorization. Recorded as the type of the exact arm's proposition
   for contrast. *)
Check @ExactProp.
Check @SpectralPropAt.

(* B5. The published numbers, at one field. *)
Definition B5_inv25_number (R : realType)
  : odflt (cert_eps (kim_biased_cert_exact R tt)) (five_card_reprice_inv25 R)
  = 1 / 25 :> R := erefl.

Definition B5b_pow39_number (R : realType)
  : odflt (cert_eps (kim_centi_cert40 R tt)) (five_card_reprice39 R)
  = 2%:R ^- 39 :> R := erefl.

(* B6. var_dist_le2 is tight: two point masses at distinct points realize it. *)
Lemma B6_var_dist_two (R : realType) :
  var_dist (fdist1 true : R.-fdist bool) (fdist1 false) = 2%:R.
Proof.
rewrite /var_dist big_bool /= !fdist1xx !fdist10 //.
by rewrite subr0 sub0r normr1 normrN normr1 mulr2n.
Qed.

Print Assumptions B1_inv25_statement.
Print Assumptions B2_repeated39_statement.
