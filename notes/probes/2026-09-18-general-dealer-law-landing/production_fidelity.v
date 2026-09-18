(******************************************************************************)
(* production_fidelity: the same checks as landing_fidelity.v, run against    *)
(*                     the permanent files after the landing                  *)
(*                                                                            *)
(* This file is a probe artifact and is not a candidate for the permanent     *)
(* tree.  It is landing_fidelity.v with its imports pointed at the permanent  *)
(* modules, so every check below is made against what was landed.  It holds   *)
(* four kinds of check.                                                       *)
(*                                                                            *)
(* 1. Two-way type ascriptions.  Each _via_dealer theorem is ascribed the     *)
(*    type of the theorem it restates, and that theorem is ascribed the type  *)
(*    of the _via_dealer one.  The ltac: form takes each type from the        *)
(*    kernel, so it cannot be defeated by a transcription error; the spelled  *)
(*    form beside it is the statement copied from the production file.        *)
(*                                                                            *)
(* 2. uniform_fdistmap_fiberE at the statement it had before the landing,     *)
(*    pasted verbatim, to show that re-proving it through                     *)
(*    uniform_fdistmap_pointE left its statement alone.  There is one         *)
(*    design_privacy module now, so the written form replaces the two         *)
(*    cross-module ascriptions the landing probe carried.                     *)
(*                                                                            *)
(* 3. Print Assumptions on every landed declaration and on the existing       *)
(*    lemmas of design_privacy.v, to show that the edit moved no assumption.  *)
(*                                                                            *)
(* 4. The four generic mutations and their two positive controls. They were   *)
(*    checked against the landed reconstruct/dealer_privacy.v.  They are      *)
(*    here so that that file                                                  *)
(*    holds exactly the three sections and eight declarations its header      *)
(*    lists, and so that no positive control is left naming a mutation that   *)
(*    is no longer beside it. The mutations of the two instance copies stay   *)
(*    in those copies, beside the declarations they mutate, where the         *)
(*    repository has a precedent for a Fail in a permanent file.              *)
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
(* psl211_alldecks supplies psl211_alldecks_view, which the transcribed
   PSL(2,11) statement of section 1c names. *)
From pgg_smc Require Import psl211_alldecks.
From pgg_reconstruct Require Import dealer_privacy design_privacy.
From pgg_smc Require Import pgl27_profile_privacy psl211_models.

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
  ltac:(let t := type of (@psl211_alldecks_view_indep)
        in exact t) :=
  @psl211_alldecks_view_indep_via_dealer.

Definition psl211_models_at_via_dealer_type :
  ltac:(let t := type of (@psl211_alldecks_view_indep_via_dealer)
        in exact t) :=
  @psl211_alldecks_view_indep.

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
(*     1c. The same for PSL(2,11), statement copied from the production file  *)
(******************************************************************************)

(* instances/psl211/psl211_models.v:427-430, with the file's Local Notation
   seatT written out, since a Local Notation is not exported. *)
Definition psl211_via_dealer_at_written_type :
  forall (R : realType)
    (C : {set ('I_(pi_T' (pgg_monodromy_profile.mp_PI
                  (pgg_instance.instance_profile
                     psl211_exec.psl211_algebra))).+1)}),
  (#|C| <= 5)%N ->
  psl211_alldecksP R |= (fun u => psl211_alldecks_view C u.1 u.2)
                    _|_ psl211_alldecks_secret R :=
  @psl211_alldecks_view_indep_via_dealer.

Definition psl211_models_at_written_type :
  forall (R : realType)
    (C : {set ('I_(pi_T' (pgg_monodromy_profile.mp_PI
                  (pgg_instance.instance_profile
                     psl211_exec.psl211_algebra))).+1)}),
  (#|C| <= 5)%N ->
  psl211_alldecksP R |= (fun u => psl211_alldecks_view C u.1 u.2)
                    _|_ psl211_alldecks_secret R :=
  @psl211_alldecks_view_indep.

(******************************************************************************)
(*     2. uniform_fdistmap_fiberE keeps its statement                         *)
(******************************************************************************)

(* The type below is the statement reconstruct/design_privacy.v gave
   uniform_fdistmap_fiberE before the landing, discharged out of Section
   fibers and pasted verbatim.  The landed constant, whose proof now goes
   through uniform_fdistmap_pointE, has it. *)
Definition fiberE_at_its_pre_landing_statement :
  forall (R : realType) (X : finType) (A : {set X}) (HA : (0 < #|A|)%N)
    (T : finType) (f0 f1 : X -> T),
  (forall v, #|[set x in A | f0 x == v]| = #|[set x in A | f1 x == v]|) ->
  fdistmap f0 (`U HA : R.-fdist X) = fdistmap f1 (`U HA) :=
  @uniform_fdistmap_fiberE.

(******************************************************************************)
(*     2b. The generic mutations, moved out of dealer_privacy.v               *)
(******************************************************************************)

Section dealer_kernel_mutations.

Variables (R : realType) (secretT deckT shuffleT viewT : finType).
Variable secretP : R.-fdist secretT.
Variable delta : secretT -> R.-fdist deckT.
Variable nu : R.-fdist shuffleT.
Variable view : secretT -> deckT -> shuffleT -> viewT.
Variable x : viewT.
Hypothesis Hmix : forall s, secretP s != 0 ->
  fdistmap (fun dg => view s dg.1 dg.2) ((delta s) `x nu) =
    fdist1 x.

(* Expected failure: a dealer law with no shuffle.  The ascribed type is a law
   on secretT * (deckT * shuffleT), while secretP `X delta is a law on secretT *
   deckT, so the two types do not unify. *)
Fail Definition dealer_shuffleP_missing_shuffle :
    R.-fdist (secretT * (deckT * shuffleT)) :=
  secretP `X delta.

(* the positive control for the mutation below: with the common mixed law
   supplied, the same spelling of dealer_shuffle_view_indep is the
   independence statement *)
Definition dealer_shuffle_view_indep_with_common_law :
  @dealer_shuffleP R secretT deckT shuffleT secretP delta nu
  |= @dealer_shuffle_view R secretT deckT shuffleT viewT secretP delta nu view
     _|_ @dealer_shuffle_secret R secretT deckT shuffleT secretP delta nu :=
  @dealer_shuffle_view_indep R secretT deckT shuffleT viewT secretP delta nu
    view (fdist1 x) Hmix.

(* Expected failure: the common mixed law premise dropped.  Without Hmix the
   term still has the premise as an arrow in its type, so what is ascribed a
   bare independence statement is a function into one. *)
Fail Definition dealer_shuffle_view_indep_without_common_law :
  @dealer_shuffleP R secretT deckT shuffleT secretP delta nu
  |= @dealer_shuffle_view R secretT deckT shuffleT viewT secretP delta nu view
     _|_ @dealer_shuffle_secret R secretT deckT shuffleT secretP delta nu :=
  @dealer_shuffle_view_indep R secretT deckT shuffleT viewT secretP delta nu
    view (fdist1 x).

End dealer_kernel_mutations.

Section carrier_transport_mutation.

Variables (R : realType) (A B TA TB : finType).
Variable P : R.-fdist A.
Variables (f : A -> B) (X : B -> TA) (Y : B -> TB).
Variable Ybad : A -> TB.

(* Expected failure: a reader that is not a composite with f.  The transported
   statement concludes with Y \o f, and Ybad is an unrelated function out of A,
   so the ascribed type does not unify with the type of the transport. *)
Fail Definition inde_RV_fdistmap_bad_reader :
  fdistmap f P |= X _|_ Y -> P |= (X \o f) _|_ Ybad :=
  proj1 (@inde_RV_fdistmap R A B TA TB P f X Y).

End carrier_transport_mutation.

Section product_section_mutation.

Variables (R : realType) (D G V : finType).
Variables (PD : R.-fdist D) (PG : R.-fdist G).
Variables (f h : D -> G -> V).
Hypothesis Hs : forall g, PG g != 0 ->
  fdistmap (fun d => f d g) PD = fdistmap (fun d => h d g) PD.

(* the positive control for the mutation below: with the section-wise premise
   supplied, the same spelling is the equality of the two laws on the pair *)
Definition fdistmap_prod_sectionE_with_sections :
  fdistmap (fun dg => f dg.1 dg.2) (PD `x PG) =
  fdistmap (fun dg => h dg.1 dg.2) (PD `x PG) :=
  @fdistmap_prod_sectionE R D G V PD PG f h Hs.

(* Expected failure: the section-wise premise dropped.  Without Hs the term
   still has that premise as an arrow in its type, so what is ascribed a bare
   equality of laws is a function into one. *)
Fail Definition fdistmap_prod_sectionE_without_sections :
  fdistmap (fun dg => f dg.1 dg.2) (PD `x PG) =
  fdistmap (fun dg => h dg.1 dg.2) (PD `x PG) :=
  @fdistmap_prod_sectionE R D G V PD PG f h.

End product_section_mutation.

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
Print Assumptions psl211_perdeck_entry_perm_enum.
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
(*     3b. The existing lemmas of design_privacy.v                            *)
(******************************************************************************)

Print Assumptions uniform_fdistmap_fiberE.
Print Assumptions colour_view_indep_laws.
Print Assumptions colour_view_indep_fibers.
Print Assumptions card_fiber_sum.
Print Assumptions pr_countE.
Print Assumptions uniform_pair_indep_of_class.
Print Assumptions pair_fibers_class_sizes.
Print Assumptions uniform_pair_indep_of_fibers.

(******************************************************************************)
(*     3c. The existing headline lemmas of the two instance files             *)
(******************************************************************************)

Print Assumptions psl211_alldecks_view_indep.
Print Assumptions psl211_alldecks_exec_exact_view_indep.
Print Assumptions pgl27_view_indep_via_profile.
Print Assumptions profile_distinct_deck_necessary.
