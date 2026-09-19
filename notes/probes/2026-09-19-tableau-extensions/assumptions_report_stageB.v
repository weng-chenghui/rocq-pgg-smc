(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* What every declaration stage B adds rests on                               *)
(*                                                                            *)
(* One Print Assumptions per lemma and per published program written by stage *)
(* B of this probe, so that the constants an extension of the Tableau brings  *)
(* in are read off a compiled file and not off a reading of the proofs. The   *)
(* expected answer is the three boolp constants, functional_extensionality_   *)
(* dep, propositional_extensionality and constructive_indefinite_description, *)
(* wherever a five-card model is mentioned, since an fdist record carries     *)
(* them through its own section context, and nothing at all for the lemmas    *)
(* that speak of a bare finite carrier. No new axiom, assumed constant,       *)
(* Admitted or Abort is written anywhere in stage B.                          *)
(*                                                                            *)
(* The blocks are grouped by the file that writes the declaration.            *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset reals.
From infotheo Require Import fdist proba variation_dist.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_analysis_manifest.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.
From tableau_ext_probe Require Import p1_joint_law_distance.
From tableau_ext_probe Require Import p4_kim_biased_proximity.
From tableau_ext_probe Require Import p8_spectral_relation.
From tableau_ext_probe Require Import p9_actual_marginals.
From tableau_ext_probe Require Import p7_mutations.

Set Implicit Arguments.
Unset Strict Implicit.

(* The Tableau: the proximity arm's composition law, the terminal whose proof
   gained a case, and the arm reader of the new certify statement. *)
Print Assumptions idealproximity_tail.
Print Assumptions port_conclude.
Print Assumptions certify_idealproximity_armE.

(* The generic distance lemmas. *)
Print Assumptions var_dist_fdistmap_pair.
Print Assumptions var_dist_prodR.
Print Assumptions var_dist_prodL.
Print Assumptions fdist_prod_snd.
Print Assumptions fdist_uniform_prod.

(* The five-card certificate and the two rows over one model. *)
Print Assumptions five_card_uniform_pairE.
Print Assumptions five_card_reading_secretE.
Print Assumptions five_card_arg_cut_prodE.
Print Assumptions kim_biased_proximity_close.
Print Assumptions kim_biased_cert_idealE.
Print Assumptions kim_biased_proximity_cert_epsE.
Print Assumptions kim_biased_proximity_eps_halfE.
Print Assumptions five_card_sqrt5_le3.
Print Assumptions kim_biased_proximity_le_inv25.
Print Assumptions kim_biased_proximity_cert_eps_lt2.
Print Assumptions five_card_row_biased_branch_spectral.
Print Assumptions five_card_row_biased_branch_spectral_atE.
Print Assumptions five_card_row_biased_branch_spectral_rowE.
Print Assumptions five_card_row_biased_branch_spectral_armE.
Print Assumptions five_card_row_biased_proximity.
Print Assumptions five_card_row_biased_proximity_rowE.
Print Assumptions five_card_row_biased_proximity_publishedE.
Print Assumptions five_card_row_biased_proximity_armE.
Print Assumptions five_card_row_biased_arm_neq.
Print Assumptions five_card_biased_view_proximity.

(* The relation to the spectral arm. *)
Print Assumptions spectral_prop_cert_free.
Print Assumptions idealproximity_reading_le.

(* The corollary about the actual model alone. *)
Print Assumptions var_dist_own_marginals.
Print Assumptions five_card_biased_view_own_marginals.

(* The mutations that are not recorded failures. *)
Print Assumptions idealproximity_ceiling.
Print Assumptions five_card_singleton_below_threshold.
Print Assumptions five_card_biased_proximity_at_singleton.
