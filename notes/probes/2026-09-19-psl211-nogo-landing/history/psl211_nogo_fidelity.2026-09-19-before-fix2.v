(* Landing probe, 2026-09-19. Not a production file.                          *)
(******************************************************************************)
(* psl211_nogo_fidelity: what the landing copy of                             *)
(*                       instances/psl211/psl211_spectral_constancy.v carries *)
(*                                                                            *)
(* Every declaration of the landing copy is put through Print Assumptions,    *)
(* and the two refutations a paper would cite are restated here and closed    *)
(* by exact:, so a statement that drifted in the move would fail to           *)
(* typecheck at this file rather than at a reader.                            *)
(*                                                                            *)
(* This file Requires the landing copy for the results. It also Requires the  *)
(* production modules whose names the restated statements spell,              *)
(* psl211_alldecks_params, psl211_dealt_params, psl211_G_pos and psl211_M:    *)
(* a Require Import of the landing copy loads them but does not import them,  *)
(* so without those lines the three statements could not be written. No       *)
(* result is taken from them.                                                 *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_alldecks.
From pgg_smc Require Import psl211_models.
From psl211_nogo_landing Require Import psl211_spectral_constancy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Import Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(*****************************************************************************)
(*     The two refutations restated                                          *)
(*****************************************************************************)

(** fidelity_alldecks_constancy_false — the all-decks refutation at the
    group-uniform ideal, written out here and closed by the landing copy's
    own theorem. *)
Lemma fidelity_alldecks_constancy_false (R : realType) :
  ~ coalition_reading_constancy psl211_alldecks_params
      ((`U psl211_G_pos) : R.-fdist (pgg_gT psl211_M)).
Proof. exact: psl211_alldecks_constancy_false. Qed.

(** fidelity_dealt_constancy_false — the dealt-mode refutation, where the run
    argument is the secret. *)
Lemma fidelity_dealt_constancy_false (R : realType) :
  ~ coalition_reading_constancy psl211_dealt_params
      ((`U psl211_G_pos) : R.-fdist (pgg_gT psl211_M)).
Proof. exact: psl211_dealt_constancy_false. Qed.

(*****************************************************************************)
(*     Assumptions of every declaration of the landing copy                  *)
(*****************************************************************************)

Print Assumptions coalition_reading_constancy.
Print Assumptions spectral_cert_reading_constancy.
Print Assumptions psl211_perdeck_coalition_le3.
Print Assumptions psl211_perdeck_coalition_below_k.
Print Assumptions psl211_alldecks_constancy_false.
Print Assumptions psl211_blockline1_deal.
Print Assumptions psl211_blockline1_view.
Print Assumptions psl211_blockline1_test.
Print Assumptions psl211_blockline1_testE.
Print Assumptions psl211_alldecks_raw_viewE.
Print Assumptions psl211_blockline1_seq.
Print Assumptions psl211_blockline1_row_size.
Print Assumptions psl211_blockline1_corow_size.
Print Assumptions psl211_blockline1_seqE.
Print Assumptions psl211_blockline1_raw_count.
Print Assumptions psl211_blockline1_raw_countE.
Print Assumptions psl211_blockline1_fiber.
Print Assumptions psl211_blockline1_fiberE.
Print Assumptions psl211_blockline1_massE.
Print Assumptions psl211_blockline1_law_neq.
Print Assumptions fdistmap_point_condE.
Print Assumptions psl211_perdeck_ideal_lawE.
Print Assumptions psl211_perdeck_fiber_true0.
Print Assumptions psl211_alldecks_constancy_false_supp.
Print Assumptions psl211_alldecks_constancy_false_close.
Print Assumptions psl211_alldecks_cert_ideal_close.
Print Assumptions psl211_alldecks_no_small_eps_cert.
Print Assumptions psl211_alldecks_no_zero_eps_cert.
Print Assumptions psl211_alldecks_constancy_false_word.
Print Assumptions psl211_alldecks_constancy_false_word584.
Print Assumptions psl211_dealt_decktbl.
Print Assumptions psl211_dealt_decktblE.
Print Assumptions psl211_dealt_decktbl_mod.
Print Assumptions psl211_dealt_view.
Print Assumptions psl211_dealt_test.
Print Assumptions psl211_dealt_testE.
Print Assumptions psl211_dealt_raw_count.
Print Assumptions psl211_dealt_raw_countE.
Print Assumptions psl211_dealt_static_obsE.
Print Assumptions psl211_dealt_raw_viewE.
Print Assumptions psl211_dealt_fiber.
Print Assumptions psl211_dealt_fiberE.
Print Assumptions psl211_dealt_massE.
Print Assumptions psl211_dealt_constancy_false.
Print Assumptions psl211_alldecks_static_obs_set0.
Print Assumptions psl211_alldecks_constancy_set0.

Print Assumptions fidelity_alldecks_constancy_false.
Print Assumptions fidelity_dealt_constancy_false.
