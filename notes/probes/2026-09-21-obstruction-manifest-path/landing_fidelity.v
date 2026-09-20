(* Fidelity check of the 2026-09-21 landing: a published obstruction's number
   is positive, and the manifest records the obstruction as its twelfth path.

   The file requires production only and restates, at its full spelled type,
   every declaration the landing added, moved, restated or removed. A removed
   declaration is checked by its absence: this file names none of them, and a
   grep of the tree outside notes/ finds none either.

   Print Assumptions at the end reads the axioms of the alias the manifest's
   twelfth path names, of the published value, and of the two theorems the
   twelve-card instance states about input distinguishability. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import design_privacy algebraic_rigidity.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import psl211_group psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_exec.
From pgg_smc Require Import psl211_endpoints psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_alldecks_input_distinguishability.
From pgg_smc Require Import psl211_reading_constancy.
From pgg_smc Require Import psl211_tableau_sampled.
From pgg_smc Require Import psl211_tableau_analysis_bridged.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Notation seatT :=
  ('I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1).
Local Notation cardT :=
  ('I_(pgg_N' (mp_M (instance_profile psl211_algebra))).+1).
Local Notation cutT := (pgg_gT psl211_M).
Local Notation viewT := ({ffun seatT -> cardT}).

(* ===== Change A: the proposition a kind stands for ===== *)

(* ObstructionProp unfolded at the one constructor. *)
Check (fun (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (c : R) =>
  erefl : ObstructionProp (@InputDistinguishabilityObstruction R A E sa c)
          = (0 < c /\ InputDistinguishabilityPropAt sa c)).

(* The proposition the positivity is NOT part of, unchanged. *)
Check (@InputDistinguishabilityPropAt :
  forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
         (sa : SampleAdapter R (instance_exec E)) (c : R), Prop).

Check (@input_distinguishability_prop_le :
  forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
         (sa : SampleAdapter R (instance_exec E)) (c c' : R),
    c' <= c ->
    InputDistinguishabilityPropAt sa c -> InputDistinguishabilityPropAt sa c').

(* ===== Change B: the three moved declarations ===== *)

Check (@psl211_perdeck_static_mass_true :
  forall R : realType,
    (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
         psl211_perdeck_coalition (true, psl211_perdeck_deal))
       ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view = 0 :> R).

Check (@psl211_perdeck_static_mass_false :
  forall R : realType,
    (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
         psl211_perdeck_coalition (false, psl211_perdeck_deal))
       ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view
    = (#|pgg_G psl211_M|%:R)^-1 :> R).

Check (@psl211_alldecks_perdeck_reading_ge :
  forall R : realType,
    (#|pgg_G psl211_M|%:R)^-1 <=
    var_dist
      (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
           psl211_perdeck_coalition (true, psl211_perdeck_deal))
         (sa_cut_dist (psl211_alldecks_sample R)))
      (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
           psl211_perdeck_coalition (false, psl211_perdeck_deal))
         (sa_cut_dist (psl211_alldecks_sample R)))).

(* ===== The facade alias the manifest's twelfth path names ===== *)

Check (PSL211Analysis.perdeck_reading_ge :
  forall R : realType,
    (#|pgg_G (mp_M PSL211Analysis.profile)|%:R)^-1 <=
    var_dist
      (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
           psl211_perdeck_coalition (true, psl211_perdeck_deal))
         (sa_cut_dist (PSL211Analysis.exact_sample R)))
      (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
           psl211_perdeck_coalition (false, psl211_perdeck_deal))
         (sa_cut_dist (PSL211Analysis.exact_sample R)))).

(* ===== The typed path, with its three status pins ===== *)

Check (psl211_alldecks_obstruction_path : AnalysisPath).
Check (ap_model psl211_alldecks_obstruction_path
  : AnalysisModelFamily PSL211Analysis.observed).
Check (erefl
  : ap_completion psl211_alldecks_obstruction_path = AnalysisBridged).
Check (erefl
  : ap_transfer psl211_alldecks_obstruction_path = NegativeTransfer).
Check (erefl
  : ap_assumptions psl211_alldecks_obstruction_path = BaselineClassicalOnly).

(* The path it differs from, and in which coordinate. *)
Check (erefl : ap_transfer psl211_alldecks_path = StaticExecutedOnly).
Check (erefl
  : ap_observed psl211_alldecks_obstruction_path
    = ap_observed psl211_alldecks_path).

(* ===== The PSL(2,11) obstruction, its proof and its program ===== *)

Check (psl211_alldecks_obstruction
  : ObstructionPayload (tableau_at psl211_exact_sampled)).

Check (@psl211_alldecks_obstruction_gt0 :
  forall R : realType, 0 < (#|pgg_G psl211_M|%:R)^-1 :> R).

Check (psl211_alldecks_obstruction_pf
  : ObstructionPayloadProp psl211_alldecks_obstruction).

Check (psl211_alldecks_obstruction_published : PublishedObstruction).

Check (psl211_alldecks_obstruction_published_pathE
  : published_obstruction_path psl211_alldecks_obstruction_published
    = psl211_alldecks_obstruction_path).

(* ===== The readers ===== *)

Check (@psl211_alldecks_input_distinguishability :
  forall R : realType,
    InputDistinguishabilityPropAt (psl211_alldecks_sample R)
      ((#|pgg_G psl211_M|%:R)^-1)).

Check (@psl211_alldecks_indistinguishability_number_ge :
  forall (R : realType)
         (cert : IndistinguishabilityCert (psl211_alldecks_sample R)) (c : R),
    IndistinguishabilityPropAt cert c -> (#|pgg_G psl211_M|%:R)^-1 <= c).

Check (@psl211_alldecks_published_input_distinguishability :
  forall R : realType,
    InputDistinguishabilityPropAt (amf_sample psl211_exact_family R tt)
      ((#|pgg_G psl211_M|%:R)^-1)).

(* ===== The assumptions ===== *)

Print Assumptions PSL211Analysis.perdeck_reading_ge.
Print Assumptions psl211_alldecks_obstruction_published.
Print Assumptions psl211_alldecks_input_distinguishability.
Print Assumptions psl211_alldecks_published_input_distinguishability.
