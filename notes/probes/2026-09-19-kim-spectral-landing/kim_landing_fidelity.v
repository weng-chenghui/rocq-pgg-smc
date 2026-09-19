(* PROBE, notes/probes/2026-09-19-kim-spectral-landing/                       *)
(* kim_landing_fidelity.v                                                     *)
(* Ledger row L10 of notes/20260919-kim-spectral-landing-design.md.           *)
(*                                                                            *)
(* This file imports the landing copies and nothing else, restates the two    *)
(* row equations the landing makes hold, and prints the assumptions of every  *)
(* declaration the landing adds or moves.                                     *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import reals boolp.
From infotheo Require Import fdist proba variation_dist.
From kim_landing_probe Require Import var_dist_supp five_card_mixing.
From kim_landing_probe Require Import five_card_analysis.
From kim_landing_probe Require Import pgg_analysis_manifest pgg_tableau.
From kim_landing_probe Require Import pgg_tableau_syntax five_card_rows.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     The two row equations, restated against the moved manifest rows        *)
(******************************************************************************)

Lemma landing_repeated_rowE :
  published_row five_card_row_repeated_spectral_tableau
  = five_card_row_repeated.
Proof. exact: five_card_row_repeated_spectral_rowE. Qed.

Lemma landing_biased_rowE :
  published_row five_card_row_biased_ideal_tableau = five_card_row_biased.
Proof. exact: five_card_row_biased_ideal_rowE. Qed.

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
Print Assumptions kim_biased_marginal_bound.
Print Assumptions kim_biased_cut_mixing.
Print Assumptions kim_centi_marginal_bound40.
Print Assumptions kim_centi_cut_mixing40.
Print Assumptions kim_one_cut_centi_le.
Print Assumptions kim_biased_marginal_bound_exact.
Print Assumptions kim_biased_cut_mixing_exact.

(******************************************************************************)
(*     instances/kim2025/five_card_analysis.v, section 7                      *)
(******************************************************************************)

Print Assumptions FiveCardAnalysis.centi_cut_mixing.
Print Assumptions FiveCardAnalysis.biased_cut_mixing.
Print Assumptions FiveCardAnalysis.static_obs_const.
Print Assumptions FiveCardAnalysis.exec_transfer_status.
Print Assumptions FiveCardAnalysis.biased_transfer_status.
Print Assumptions FiveCardAnalysis.repeated_transfer_status.

(******************************************************************************)
(*     manifest/pgg_analysis_manifest.v, the two moved rows                   *)
(******************************************************************************)

Print Assumptions five_card_row_biased.
Print Assumptions five_card_row_repeated.

(******************************************************************************)
(*     instances/kim2025/five_card_rows.v                                     *)
(******************************************************************************)

Print Assumptions kim_biased_epsE.
Print Assumptions kim_biased_exact_le_eps.
Print Assumptions kim_biased_sample_cut_witnessE.
Print Assumptions kim_centi_cert.
Print Assumptions kim_biased_cert.
Print Assumptions five_card_row_repeated_spectral_tableau.
Print Assumptions five_card_row_biased_ideal_tableau.
Print Assumptions five_card_row_repeated_spectral_rowE.
Print Assumptions five_card_row_biased_ideal_rowE.
Print Assumptions five_card_row_repeated_spectral_publishedE.
Print Assumptions five_card_row_biased_ideal_publishedE.
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
(*     The two row equations of this file                                     *)
(******************************************************************************)

Print Assumptions landing_repeated_rowE.
Print Assumptions landing_biased_rowE.
