(******************************************************************************)
(* landing_fidelity: the checks that the landing copies restate the theorems  *)
(*                   they claim to restate, and assume nothing new            *)
(*                                                                            *)
(* This file is a probe artifact and is not a candidate for the permanent     *)
(* tree.  It holds three kinds of check.                                      *)
(*                                                                            *)
(* 1. Two-way type ascriptions.  Each _via_dealer theorem is ascribed the     *)
(*    type of the theorem it restates, and that theorem is ascribed the type  *)
(*    of the _via_dealer one.  The ltac: form takes each type from the        *)
(*    kernel, so it cannot be defeated by a transcription error; the spelled  *)
(*    form beside it is the statement copied from the production file.        *)
(*                                                                            *)
(* 2. uniform_fdistmap_fiberE at its production type, to show that re-proving *)
(*    it through uniform_fdistmap_pointE left its statement alone.            *)
(*                                                                            *)
(* 3. Print Assumptions on every landed declaration, and on two existing      *)
(*    lemmas of design_privacy.v in both the production and the landing       *)
(*    copy, to show that the edit moved no assumption.                        *)
(*                                                                            *)
(* Every mutation of the feasibility probe is kept inside the candidate file  *)
(* that owns the declaration it mutates: the three kernel and transport ones  *)
(* in dealer_privacy.v, the two PGL(2,7) ones in                              *)
(* pgl27_profile_privacy_landing.v, and the PSL(2,11) one in                  *)
(* psl211_models_landing.v.  None is left over for this file.                 *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_reconstruct Require Import transitivity_privacy.
From pgg_smc Require Import pgg_interface pgl27_group pgl27_orbit.
From pgg_smc Require Import pgl27_scheme pgl27_profile pgl27_secrecy.
From general_dealer_law_landing Require Import dealer_privacy.
From general_dealer_law_landing Require Import design_privacy_landing.
From general_dealer_law_landing Require Import pgl27_profile_privacy_landing.
From general_dealer_law_landing Require Import psl211_models_landing.
(* Required and not imported: the short names of these two modules are the
   ones the landing copies duplicate, so they are reached by qualification. *)
From pgg_reconstruct Require design_privacy.
From pgg_smc Require psl211_models.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     1. Two-way type ascriptions, types taken from the kernel               *)
(******************************************************************************)

Definition pgl27_via_dealer_at_secrecy_type :
  ltac:(let t := type of (@pgl27_view_indep) in exact t) :=
  @pgl27_view_indep_via_dealer.

Definition pgl27_secrecy_at_via_dealer_type :
  ltac:(let t := type of (@pgl27_view_indep_via_dealer) in exact t) :=
  @pgl27_view_indep.

Definition pgl27_alldecks_via_dealer_at_secrecy_type :
  ltac:(let t := type of (@pgl27_view_indep_alldecks) in exact t) :=
  @pgl27_view_indep_alldecks_via_dealer.

Definition pgl27_alldecks_secrecy_at_via_dealer_type :
  ltac:(let t := type of (@pgl27_view_indep_alldecks_via_dealer) in exact t) :=
  @pgl27_view_indep_alldecks.

Definition psl211_via_dealer_at_models_type :
  ltac:(let t := type of (@psl211_models.psl211_alldecks_view_indep)
        in exact t) :=
  @psl211_alldecks_view_indep_via_dealer.

Definition psl211_models_at_via_dealer_type :
  ltac:(let t := type of (@psl211_alldecks_view_indep_via_dealer)
        in exact t) :=
  @psl211_models.psl211_alldecks_view_indep.

(******************************************************************************)
(*     1b. The same, with the statements copied from the production files     *)
(******************************************************************************)

(* instances/pgl27/pgl27_secrecy.v, pgl27_view_indep, inside the section that
   binds R. *)
Definition pgl27_via_dealer_at_written_type :
  forall (R : realType) (C : {set 'I_8}), (#|C| <= 3)%N ->
  pgl27P R |= pgl27_view R C _|_ pgl27_secret R :=
  @pgl27_view_indep_via_dealer.

Definition pgl27_secrecy_at_written_type :
  forall (R : realType) (C : {set 'I_8}), (#|C| <= 3)%N ->
  pgl27P R |= pgl27_view R C _|_ pgl27_secret R :=
  @pgl27_view_indep.

(* instances/pgl27/pgl27_secrecy.v, pgl27_view_indep_alldecks. *)
Definition pgl27_alldecks_via_dealer_at_written_type :
  forall (R : realType) (C : {set 'I_8}), (#|C| <= 3)%N ->
  alldecksP (fdist_uniform card_bool) pgl27_G_pos (R:=R) pgl27_class_decks_pos
  |= alldecks_view (@pgg_rho pgl27_M) (fdist_uniform card_bool) pgl27_G_pos
       pgl27_class_decks_pos C
  _|_ alldecks_secret (fdist_uniform card_bool) pgl27_G_pos
        pgl27_class_decks_pos :=
  @pgl27_view_indep_alldecks_via_dealer.

Definition pgl27_alldecks_secrecy_at_written_type :
  forall (R : realType) (C : {set 'I_8}), (#|C| <= 3)%N ->
  alldecksP (fdist_uniform card_bool) pgl27_G_pos (R:=R) pgl27_class_decks_pos
  |= alldecks_view (@pgg_rho pgl27_M) (fdist_uniform card_bool) pgl27_G_pos
       pgl27_class_decks_pos C
  _|_ alldecks_secret (fdist_uniform card_bool) pgl27_G_pos
        pgl27_class_decks_pos :=
  @pgl27_view_indep_alldecks.

(******************************************************************************)
(*     2. uniform_fdistmap_fiberE keeps its statement                         *)
(******************************************************************************)

(* T is the statement of reconstruct/design_privacy.v, discharged out of
   Section fibers.  The landing copy, whose proof now goes through
   uniform_fdistmap_pointE, has it. *)
Check (@uniform_fdistmap_fiberE :
  forall (R : realType) (X : finType) (A : {set X}) (HA : (0 < #|A|)%N)
    (T : finType) (f0 f1 : X -> T),
  (forall v, #|[set x in A | f0 x == v]| = #|[set x in A | f1 x == v]|) ->
  fdistmap f0 (`U HA : R.-fdist X) = fdistmap f1 (`U HA)).

Definition fiberE_landing_at_production_type :
  ltac:(let t := type of (@design_privacy.uniform_fdistmap_fiberE)
        in exact t) :=
  @uniform_fdistmap_fiberE.

Definition fiberE_production_at_landing_type :
  ltac:(let t := type of (@uniform_fdistmap_fiberE) in exact t) :=
  @design_privacy.uniform_fdistmap_fiberE.

(******************************************************************************)
(*     3. Assumptions of every landed declaration                             *)
(******************************************************************************)

Print Assumptions dealer_shuffleP.
Print Assumptions dealer_shuffle_secret.
Print Assumptions dealer_shuffle_view.
Print Assumptions dealer_shufflePE.
Print Assumptions dealer_shuffle_view_indep.
Print Assumptions dealer_shuffle_view_indep_of_deck.
Print Assumptions inde_RV_fdistmap.
Print Assumptions fdistmap_prod_sectionE.
Print Assumptions dealer_shuffle_view_indep_with_common_law.
Print Assumptions fdistmap_prod_sectionE_with_sections.

Print Assumptions uniform_fdistmap_pointE.
Print Assumptions uniform_fdistmap_fiberTE.

Print Assumptions pgl27_dealer_delta.
Print Assumptions pgl27_dealer_nu.
Print Assumptions pgl27_dealerP.
Print Assumptions pgl27_dealer_embed.
Print Assumptions pgl27_dealer_view.
Print Assumptions pgl27_dealer_mu.
Print Assumptions pgl27_dealer_bad_embed.
Print Assumptions pgl27_alldecks_dealer_delta.
Print Assumptions pgl27_alldecks_dealerP.
Print Assumptions pgl27_dealerPE.
Print Assumptions pgl27_dealer_viewE.
Print Assumptions pgl27_dealer_secretE.
Print Assumptions pgl27_alldecks_dealer_view_law.
Print Assumptions pgl27_dealer_view_law.
Print Assumptions pgl27_dealer_view_indep.
Print Assumptions pgl27_view_indep_via_dealer.
Print Assumptions pgl27_alldecks_dealerPE.
Print Assumptions pgl27_alldecks_dealer_viewE.
Print Assumptions pgl27_alldecks_dealer_secretE.
Print Assumptions pgl27_view_indep_alldecks_via_dealer.
Print Assumptions pgl27_alldecks_dealer_view_law_with_validity.

Print Assumptions psl211_deal_pos.
Print Assumptions psl211_dealer_delta.
Print Assumptions psl211_dealer_nu.
Print Assumptions psl211_dealerP.
Print Assumptions psl211_dealer_assoc.
Print Assumptions psl211_dealer_view.
Print Assumptions psl211_dealer_bad_assoc.
Print Assumptions psl211_dealer_mixed_law.
Print Assumptions psl211_perdeck_deal.
Print Assumptions psl211_perdeck_coalition.
Print Assumptions psl211_perdeck_view.
Print Assumptions psl211_perdeck_seq.
Print Assumptions psl211_perdeck_raw_view.
Print Assumptions psl211_perdeck_test.
Print Assumptions psl211_perdeck_raw_count.
Print Assumptions psl211_perdeck_fiber.
Print Assumptions psl211_fixed_deal_delta.
Print Assumptions psl211_fixed_dealP.
Print Assumptions psl211_dealerPE.
Print Assumptions psl211_dealer_viewE.
Print Assumptions psl211_dealer_secretE.
Print Assumptions psl211_dealer_sectionE.
Print Assumptions psl211_dealer_mixed_lawE.
Print Assumptions psl211_dealer_view_indep.
Print Assumptions psl211_alldecks_view_indep_via_dealer.

(* the raw-count chain, expected to be closed under the global context *)
Print Assumptions psl211_perdeck_row_size.
Print Assumptions psl211_perdeck_corow_size.
Print Assumptions psl211_perdeck_seqE.
Print Assumptions psl211_perdeck_testE.
Print Assumptions psl211_perdeck_raw_countE.
Print Assumptions psl211_entry_perm_enum.
Print Assumptions psl211_perdeck_ptbl_nth.
Print Assumptions psl211_perdeck_raw_viewE.
Print Assumptions psl211_perdeck_ptbl_enum.
Print Assumptions psl211_perdeck_fiberE.
Print Assumptions psl211_perdeck_fiber_card_neq.

Print Assumptions psl211_perdeck_massE.
Print Assumptions psl211_perdeck_law_neq.
Print Assumptions psl211_perdeck_no_common_law.
Print Assumptions psl211_dealer_valid_forced.
Print Assumptions psl211_dealer_view_indep_of_deck_unsat.
Print Assumptions psl211_fixed_deal_view_dep.

(******************************************************************************)
(*     3b. The existing lemmas of design_privacy.v, in both copies            *)
(******************************************************************************)

Print Assumptions design_privacy.uniform_fdistmap_fiberE.
Print Assumptions uniform_fdistmap_fiberE.
Print Assumptions design_privacy.colour_view_indep_laws.
Print Assumptions colour_view_indep_laws.
Print Assumptions design_privacy.colour_view_indep_fibers.
Print Assumptions colour_view_indep_fibers.
Print Assumptions design_privacy.card_fiber_sum.
Print Assumptions card_fiber_sum.
Print Assumptions design_privacy.pr_countE.
Print Assumptions pr_countE.
Print Assumptions design_privacy.uniform_pair_indep_of_class.
Print Assumptions uniform_pair_indep_of_class.
Print Assumptions design_privacy.pair_fibers_class_sizes.
Print Assumptions pair_fibers_class_sizes.
Print Assumptions design_privacy.uniform_pair_indep_of_fibers.
Print Assumptions uniform_pair_indep_of_fibers.

(******************************************************************************)
(*     3c. The existing headline lemmas of the two instance files             *)
(******************************************************************************)

Print Assumptions psl211_models.psl211_alldecks_view_indep.
Print Assumptions psl211_alldecks_view_indep.
Print Assumptions psl211_models.psl211_alldecks_exec_exact_view_indep.
Print Assumptions psl211_alldecks_exec_exact_view_indep.
Print Assumptions pgl27_view_indep_via_profile.
Print Assumptions profile_distinct_deck_necessary.
