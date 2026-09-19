(* PROBE, notes/probes/2026-09-19-kim-spectral-landing/                       *)
(* kim_asbuilt_fidelity.v                                                     *)
(*                                                                            *)
(* This is the assumption report of the permanent modules as they stand       *)
(* after the landing of 2026-09-19. It is the counterpart of                  *)
(* kim_landing_fidelity.v, which reports the same targets against the probe   *)
(* copies instead.                                                            *)
(*                                                                            *)
(* Provenance. This file is compiled with the production _CoqProject flags    *)
(* alone: the probe directory is mapped to no logical root on that command    *)
(* line, so no probe copy is reachable by any Require here, and every name    *)
(* below is the one production builds. Locate Library does not witness which  *)
(* file a Require picked and is not used; the three Locate sentences below    *)
(* print the full names the constants carry under pgg_smc.                    *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import reals boolp.
From infotheo Require Import fdist proba variation_dist.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_weighted_words pgg_analysis_status.
From pgg_smc Require Import five_card_kim five_card_exec five_card_models.
From pgg_smc Require Import var_dist_supp five_card_mixing.
From pgg_smc Require Import five_card_analysis.
From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax five_card_rows.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     Where the three constants live                                         *)
(******************************************************************************)

Locate kim_centi_static_obs_indist.
Locate five_card_row_repeated_spectral_tableau.
Locate var_dist_fdistmap_supp_inj.

(******************************************************************************)
(*     The two row equations, restated against the landed manifest rows       *)
(******************************************************************************)

Lemma asbuilt_repeated_rowE :
  published_row five_card_row_repeated_spectral_tableau
  = five_card_row_repeated.
Proof. exact: five_card_row_repeated_spectral_rowE. Qed.

Lemma asbuilt_biased_rowE :
  published_row five_card_row_biased_spectral_tableau = five_card_row_biased.
Proof. exact: five_card_row_biased_spectral_rowE. Qed.

(******************************************************************************)
(*     The certified proposition and the manifest's bridge corollary          *)
(*                                                                            *)
(* Each certified program carries SpectralPropAt at its own certificate and   *)
(* its own accumulated number, and the manifest's bridge cell names the       *)
(* corollary of five_card_mixing.v instead, because the manifest cannot name  *)
(* the program. For each row one lemma reads the corollary's statement off    *)
(* the published row through view_indist_of, naming no corollary, and one     *)
(* derives the certificate's own SpectralPropAt from the corollary. Both      *)
(* directions use the certificate's identification equation and nothing       *)
(* else, so the two propositions differ by that equation alone.               *)
(******************************************************************************)

(** The repeated row's corollary statement, read off the proposition the
    published certified program delivers. The premises are the program's, so
    a reader who trusts the Tableau reaches the manifest's bridge cell
    without the corollary. *)
Lemma asbuilt_centi_indist_of_program (R : realType)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1}) :
  (#|C| < profile_k (instance_profile five_card_algebra))%N ->
  forall x x' : ex_inputT five_card_params,
    var_dist
      (fdistmap (@static_coalition_obs five_card_algebra five_card_params C x)
         (sw_rho_dist (scb_bound (kim_security_bundle_centi R))))
      (fdistmap
         (@static_coalition_obs five_card_algebra five_card_params C x')
         (sw_rho_dist (scb_bound (kim_security_bundle_centi R))))
    <= cert_eps (kim_centi_cert R tt).
Proof.
move=> HC x x'.
have Hd : sa_cut_dist (amf_sample kim_centi_family R tt)
        = sw_rho_dist (scb_bound (kim_security_bundle_centi R)).
  exact: (kim_centi_cut_distE R).
rewrite -Hd.
by apply: (view_indist_of five_card_row_repeated_spectral_tableau R tt).
Qed.

(** The repeated certificate's own proposition, derived from the corollary.
    With the lemma above it makes the manifest's bridge cell and the
    program's payload the same claim about the same coalition. *)
Lemma asbuilt_centi_prop_of_indist (R : realType) (idx : unit) :
  SpectralPropAt (kim_centi_cert R idx) (cert_eps (kim_centi_cert R idx)).
Proof.
move=> C x x' HC.
have Hd : sa_cut_dist (amf_sample kim_centi_family R idx)
        = sw_rho_dist (scb_bound (kim_security_bundle_centi R)).
  exact: (kim_centi_cut_distE R).
rewrite Hd; exact (@kim_centi_static_obs_indist R C HC x x').
Qed.

(** The one-cut row's corollary statement, read off its published certified
    program in the same way and at that row's own number. *)
Lemma asbuilt_biased_indist_of_program (R : realType)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1}) :
  (#|C| < profile_k (instance_profile five_card_algebra))%N ->
  forall x x' : ex_inputT five_card_params,
    var_dist
      (fdistmap (@static_coalition_obs five_card_algebra five_card_params C x)
         (sw_rho_dist (kim_biased_marginal_bound R)))
      (fdistmap
         (@static_coalition_obs five_card_algebra five_card_params C x')
         (sw_rho_dist (kim_biased_marginal_bound R)))
    <= cert_eps (kim_biased_cert R tt).
Proof.
move=> HC x x'.
have Hd : sa_cut_dist (amf_sample kim_biased_family R tt)
        = sw_rho_dist (kim_biased_marginal_bound R).
  exact: (esym (kim_biased_sample_cut_witnessE R)).
rewrite -Hd.
by apply: (view_indist_of five_card_row_biased_spectral_tableau R tt).
Qed.

(** The one-cut certificate's own proposition, derived from the corollary at
    word length one. *)
Lemma asbuilt_biased_prop_of_indist (R : realType) (idx : unit) :
  SpectralPropAt (kim_biased_cert R idx) (cert_eps (kim_biased_cert R idx)).
Proof.
move=> C x x' HC.
have Hd : sa_cut_dist (amf_sample kim_biased_family R idx)
        = sw_rho_dist (kim_biased_marginal_bound R).
  exact: (esym (kim_biased_sample_cut_witnessE R)).
rewrite Hd; exact (@kim_biased_static_obs_indist R C HC x x').
Qed.

(******************************************************************************)
(*     lib/var_dist_supp.v                                                    *)
(******************************************************************************)

Print Assumptions var_dist_le2.
Print Assumptions var_dist_fdistmap_supp_inj.
Print Assumptions fdistmap_inj_uniform_id.
Print Assumptions fdistmap_neq0_codom.
Print Assumptions card_tnth_count.

(******************************************************************************)
(*     instances/kim2025/five_card_mixing.v                                   *)
(******************************************************************************)

Print Assumptions fc_sigma_pow5_eq1.
Print Assumptions fc_sigma_pow_point_inj.
Print Assumptions fc_sigma_pow_ord_inj.
Print Assumptions fc_kim_word_eval_powE.
Print Assumptions fc_kim_rho_supp_pow.
Print Assumptions five_card_ideal_supp_pow.
Print Assumptions five_card_ideal_point_uniform.
Print Assumptions kim_single_cut_supp_pow.
Print Assumptions kim_centi_cut_supp_pow.
Print Assumptions fc_arrange_countE.
Print Assumptions den_boer_layout_law_const.
Print Assumptions five_card_static_obs_const.
Print Assumptions five_card_cut_mixing_of_supp_pow.
Print Assumptions kim_centi_cut_mixing.
Print Assumptions kim_centi_static_obs_indist.
Print Assumptions kim_biased_marginal_bound.
Print Assumptions kim_biased_sample_cut_witnessE.
Print Assumptions kim_biased_cut_mixing.
Print Assumptions kim_biased_static_obs_indist.
Print Assumptions kim_centi_marginal_bound40.
Print Assumptions kim_centi_cut_mixing40.
Print Assumptions kim_one_cut_centi_le.
Print Assumptions kim_biased_marginal_bound_exact.
Print Assumptions kim_biased_cut_mixing_exact.

(******************************************************************************)
(*     instances/kim2025/five_card_analysis.v, section 7                      *)
(******************************************************************************)

Print Assumptions FiveCardAnalysis.biased_sample_cut_witnessE.
Print Assumptions FiveCardAnalysis.centi_cut_mixing.
Print Assumptions FiveCardAnalysis.biased_cut_mixing.
Print Assumptions FiveCardAnalysis.static_obs_const.
Print Assumptions FiveCardAnalysis.centi_static_obs_indist.
Print Assumptions FiveCardAnalysis.biased_static_obs_indist.
Print Assumptions FiveCardAnalysis.uniform_transfer_status.
Print Assumptions FiveCardAnalysis.biased_transfer_status.
Print Assumptions FiveCardAnalysis.repeated_transfer_status.

(******************************************************************************)
(*     manifest/pgg_analysis_manifest.v, the two landed rows                  *)
(******************************************************************************)

Print Assumptions five_card_row_biased.
Print Assumptions five_card_row_repeated.

(******************************************************************************)
(*     instances/kim2025/five_card_rows.v                                     *)
(******************************************************************************)

Print Assumptions kim_biased_epsE.
Print Assumptions kim_biased_exact_le_eps.
Print Assumptions kim_centi_cert.
Print Assumptions kim_biased_cert.
Print Assumptions five_card_row_repeated_spectral_tableau.
Print Assumptions five_card_row_biased_spectral_tableau.
Print Assumptions five_card_row_repeated_spectral_rowE.
Print Assumptions five_card_row_biased_spectral_rowE.
Print Assumptions five_card_row_repeated_spectral_publishedE.
Print Assumptions five_card_row_biased_spectral_publishedE.
Print Assumptions five_card_pow2_39_split.
Print Assumptions kim_centi_cert_epsE.
Print Assumptions kim_centi_cert_eps_lt.
Print Assumptions kim_biased_cert_epsE.
Print Assumptions kim_biased_cert_eps_lt2.
Print Assumptions kim_centi_cert40.
Print Assumptions kim_centi_cert40_epsE.
Print Assumptions five_card_reprice39.
Print Assumptions five_card_row_repeated39.
Print Assumptions kim_biased_cert_exact.
Print Assumptions five_card_inv50_split.
Print Assumptions five_card_reprice_inv25.
Print Assumptions five_card_row_biased_inv25.
Print Assumptions five_card_row_biased_forms_publishedE.
Print Assumptions five_card_reprice_inv25_lt2.

(******************************************************************************)
(*     The six restatements of this file                                      *)
(******************************************************************************)

Print Assumptions asbuilt_repeated_rowE.
Print Assumptions asbuilt_biased_rowE.
Print Assumptions asbuilt_centi_indist_of_program.
Print Assumptions asbuilt_centi_prop_of_indist.
Print Assumptions asbuilt_biased_indist_of_program.
Print Assumptions asbuilt_biased_prop_of_indist.
Print Assumptions FiveCardAnalysis.static_obs.
