(* Landing probe, 2026-09-19. Not a production file.                          *)
(******************************************************************************)
(* psl211_asbuilt_fidelity: what the permanent module                         *)
(*                          instances/psl211/psl211_spectral_constancy.v      *)
(*                          carries after the landing of 2026-09-19           *)
(*                                                                            *)
(* Every declaration of the permanent module, read through the pgg_smc root,  *)
(* is put through Print Assumptions here, the two refutations a paper would   *)
(* cite are restated and closed by exact:, and the two statements a row cites *)
(* are put through Check against the type the permanent file gives them. This *)
(* file is the counterpart of psl211_nogo_fidelity.v, which reports the same  *)
(* declarations in the landing copy under the psl211_nogo_landing root, and   *)
(* it Requires nothing from that root, so the module name that now exists     *)
(* under both roots resolves here to the production one only.                 *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_reconstruct Require Import pgg_sharing_framework algebraic_rigidity.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_alldecks.
From pgg_smc Require Import psl211_models.
From pgg_smc Require Import psl211_spectral_constancy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Import Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(*****************************************************************************)
(*     Which root the names resolve through                                  *)
(*****************************************************************************)

Locate psl211_alldecks_no_small_eps_cert.
Locate psl211_blockline1_law_neq.
Locate coalition_reading_constancy.

(*****************************************************************************)
(*     The two refutations restated                                          *)
(*****************************************************************************)

(** fidelity_alldecks_constancy_false — the all-decks refutation at the
    group-uniform ideal, written out here and closed by the permanent
    module's own theorem. *)
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
(*     The two statements a row cites, against their production spelling     *)
(*****************************************************************************)

Check (psl211_alldecks_no_small_eps_cert
  : forall (R : realType) (cert : SpectralCert (psl211_alldecks_sample R)),
    sw_bound_eps (sc_b cert) + sw_bound_eps (sc_b cert)
      < (#|pgg_G psl211_M|%:R)^-1 -> False).

Check (psl211_blockline1_law_neq
  : forall R : realType,
    fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
        psl211_perdeck_coalition (true, psl211_perdeck_deal))
      ((`U psl211_G_pos) : R.-fdist (pgg_gT psl211_M))
    != fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
        psl211_perdeck_coalition (true, psl211_blockline1_deal))
      ((`U psl211_G_pos) : R.-fdist (pgg_gT psl211_M))).

(*****************************************************************************)
(*     Assumptions of every declaration of the permanent module              *)
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
