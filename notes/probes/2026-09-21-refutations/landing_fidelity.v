(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* landing_fidelity: every declaration the 2026-09-21 refutations landing     *)
(* added, read back from the production files at its full statement. This     *)
(* file requires production only; it declares nothing.                        *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_collusion_bound.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_alldecks.
From pgg_smc Require Import psl211_models psl211_reading_constancy.
From pgg_smc Require Import psl211_tableau_sampled.
From pgg_smc Require Import psl211_tableau_analysis_bridged.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_exec.
From pgg_smc Require Import pgl27_models pgl27_tableau_analysis_bridged.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Notation cutT := (pgg_gT psl211_M).

(******************************************************************************)
(*     manifest/pgg_tableau.v                                                 *)
(******************************************************************************)

Check (@indistinguishability_prop_of_ideal_close
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E))
           (cert : IndistinguishabilityCert sa) (eps : R),
      var_dist (sa_cut_dist sa) (ic_ideal cert) <= eps ->
      IndistinguishabilityPropAt cert (eps + eps)).

Check (@InputDistinguishabilityPropAt
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A),
      SampleAdapter R (instance_exec E) -> R -> Prop).

Check (fun (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (c : R) =>
  erefl : InputDistinguishabilityPropAt sa c
        = exists (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1})
                 (x x' : ex_inputT E),
            (#|C| < profile_k (instance_profile A))%N /\
            c <= var_dist
                   (fdistmap (static_coalition_obs C x) (sa_cut_dist sa))
                   (fdistmap (static_coalition_obs C x') (sa_cut_dist sa))).

Check (@input_distinguishability_prop_le
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (c c' : R),
      c' <= c ->
      InputDistinguishabilityPropAt sa c ->
      InputDistinguishabilityPropAt sa c').

Check (@indistinguishability_number_ge_of_input_distinguishability
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E))
           (cert : IndistinguishabilityCert sa) (c c' : R),
      InputDistinguishabilityPropAt sa c ->
      IndistinguishabilityPropAt cert c' -> c <= c').

Check (@no_indistinguishability_cert_ideal_close_of_input_distinguishability
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (c eps : R),
      InputDistinguishabilityPropAt sa c -> eps + eps < c ->
      forall cert : IndistinguishabilityCert sa,
        var_dist (sa_cut_dist sa) (ic_ideal cert) <= eps -> False).

Check (@ObstructionKind
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A),
      SampleAdapter R (instance_exec E) -> Type).

Check (@InputDistinguishabilityObstruction
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)), R -> ObstructionKind sa).

Check (fun (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (c : R) =>
  erefl : ObstructionProp (@InputDistinguishabilityObstruction R A E sa c)
        = InputDistinguishabilityPropAt sa c).

Check (@ObstructionPayload : StackAt Sampled -> Type).
Check (@ObstructionPayloadProp
  : forall q : StackAt Sampled, ObstructionPayload q -> Prop).
Check (@PublishObstructionPayload : StackAt Sampled -> Type).
Check (@mk_obstruction
  : forall (q : StackAt Sampled) (o : ObstructionPayload q),
      ObstructionPayloadProp o -> PublishObstructionPayload q).

Check (@MkPublishedObstruction
  : forall (at_ : StackAt Sampled) (path : AnalysisPath)
           (kind : ObstructionPayload at_),
      StackProp Sampled at_ -> ObstructionPayloadProp kind ->
      PublishedObstruction).
Check (@published_obstruction_at : PublishedObstruction -> StackAt Sampled).
Check (@published_obstruction_path : PublishedObstruction -> AnalysisPath).
Check (@published_obstruction_kind
  : forall r : PublishedObstruction, ObstructionPayload
      (published_obstruction_at r)).
Check (@published_obstruction_thm
  : forall r : PublishedObstruction, StackProp Sampled
      (published_obstruction_at r)).
Check (@published_obstruction_pf
  : forall r : PublishedObstruction, ObstructionPayloadProp
      (published_obstruction_kind r)).

Check (@publish_obstruction
  : forall (a : AssumptionStatus) (q : StackAt Sampled),
      StackProp Sampled q -> PublishObstructionPayload q ->
      PublishedObstruction).

Check (@publish_obstruction_completionE
  : forall (a : AssumptionStatus) (q : StackAt Sampled)
           (pf : StackProp Sampled q) (p : PublishObstructionPayload q),
      ap_completion (published_obstruction_path (publish_obstruction a q pf p))
      = AnalysisBridged).
Check (@publish_obstruction_transferE
  : forall (a : AssumptionStatus) (q : StackAt Sampled)
           (pf : StackProp Sampled q) (p : PublishObstructionPayload q),
      ap_transfer (published_obstruction_path (publish_obstruction a q pf p))
      = NegativeTransfer).
Check (@publish_obstruction_modelE
  : forall (a : AssumptionStatus) (q : StackAt Sampled)
           (pf : StackProp Sampled q) (p : PublishObstructionPayload q),
      ap_model (published_obstruction_path (publish_obstruction a q pf p))
      = sp_f q).
Check (@publish_obstruction_observedE
  : forall (a : AssumptionStatus) (q : StackAt Sampled)
           (pf : StackProp Sampled q) (p : PublishObstructionPayload q),
      ap_observed (published_obstruction_path (publish_obstruction a q pf p))
      = sp_obs q).
Check (@publish_obstruction_assumptionsE
  : forall (a : AssumptionStatus) (q : StackAt Sampled)
           (pf : StackProp Sampled q) (p : PublishObstructionPayload q),
      ap_assumptions (published_obstruction_path
                        (publish_obstruction a q pf p)) = a).
Check (@publish_obstruction_kindE
  : forall (a : AssumptionStatus) (q : StackAt Sampled)
           (pf : StackProp Sampled q) (o : ObstructionPayload q)
           (H : ObstructionPayloadProp o),
      published_obstruction_kind
        (publish_obstruction a q pf (mk_obstruction q o H)) = o).

Check (@obstruction_of
  : forall r : PublishedObstruction,
      ObstructionPayloadProp (published_obstruction_kind r)).
Check (@run_correct_of_obstruction
  : forall r : PublishedObstruction,
      oe_correct_prop (sp_obs (published_obstruction_at r))).
Check (@view_identification_of_obstruction
  : forall r : PublishedObstruction,
      sampled_viewE_prop (sp_f (published_obstruction_at r))).

(******************************************************************************)
(*     manifest/pgg_tableau_syntax.v                                          *)
(******************************************************************************)

Section surface_rule.
Variable s : Tableau Sampled.
Variable a : AssumptionStatus.
Variable o : ObstructionPayload (tableau_at s).
Variable H : ObstructionPayloadProp o.
Check (s |> publish Obstruction o by H a : PublishedObstruction).
Check (erefl : (s |> publish Obstruction o by H a)
             = (s ;;; publish_obstruction a
                  of (mk_obstruction (tableau_at s) o H))).
End surface_rule.

(******************************************************************************)
(*     instances/psl211/psl211_reading_constancy.v                            *)
(******************************************************************************)

Check (@psl211_perdeck_static_mass_true
  : forall R : realType,
      (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
           psl211_perdeck_coalition (true, psl211_perdeck_deal))
         ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view = 0 :> R).

Check (@psl211_perdeck_static_mass_false
  : forall R : realType,
      (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
           psl211_perdeck_coalition (false, psl211_perdeck_deal))
         ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view
      = (#|pgg_G psl211_M|%:R)^-1 :> R).

Check (@psl211_alldecks_perdeck_reading_ge
  : forall R : realType,
      (#|pgg_G psl211_M|%:R)^-1 <=
      var_dist
        (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
             psl211_perdeck_coalition (true, psl211_perdeck_deal))
           (sa_cut_dist (psl211_alldecks_sample R)))
        (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
             psl211_perdeck_coalition (false, psl211_perdeck_deal))
           (sa_cut_dist (psl211_alldecks_sample R)))).

Check (@psl211_alldecks_input_distinguishability
  : forall R : realType,
      InputDistinguishabilityPropAt (psl211_alldecks_sample R)
        ((#|pgg_G psl211_M|%:R)^-1)).

Check (@psl211_alldecks_indistinguishability_number_ge
  : forall (R : realType)
           (cert : IndistinguishabilityCert (psl211_alldecks_sample R))
           (c : R),
      IndistinguishabilityPropAt cert c -> (#|pgg_G psl211_M|%:R)^-1 <= c).

(******************************************************************************)
(*     instances/psl211/tableau/psl211_tableau_analysis_bridged.v             *)
(******************************************************************************)

Check (psl211_alldecks_obstruction
  : ObstructionPayload (tableau_at psl211_exact_sampled)).
Check (psl211_alldecks_obstruction_pf
  : ObstructionPayloadProp psl211_alldecks_obstruction).
Check (psl211_alldecks_obstruction_published : PublishedObstruction).

Check (psl211_alldecks_obstruction_published_pathE
  : published_obstruction_path psl211_alldecks_obstruction_published
  = @MkAnalysisPath PSL211Analysis.observed AnalysisBridged
      PSL211Analysis.exact_family NegativeTransfer BaselineClassicalOnly).
Check (psl211_alldecks_obstruction_published_path_observedE
  : ap_observed
      (published_obstruction_path psl211_alldecks_obstruction_published)
  = ap_observed psl211_alldecks_path).
Check (psl211_alldecks_obstruction_published_path_transfer_neq
  : ap_transfer
      (published_obstruction_path psl211_alldecks_obstruction_published)
  <> ap_transfer psl211_alldecks_path).
Check (@psl211_alldecks_published_input_distinguishability
  : forall R : realType,
      InputDistinguishabilityPropAt (amf_sample psl211_exact_family R tt)
        ((#|pgg_G psl211_M|%:R)^-1)).

(******************************************************************************)
(*     instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v               *)
(******************************************************************************)

Check (@pgl27_word_input_distinguishability_false
  : forall (R : realType) (secretP : R.-fdist bool) (c : R),
      2%:R^-39 < c ->
      InputDistinguishabilityPropAt
        (amf_sample pgl27_word_family R secretP) c -> False).

(******************************************************************************)
(*     The assumption baselines                                               *)
(******************************************************************************)

Print Assumptions psl211_alldecks_perdeck_reading_ge.
Print Assumptions psl211_alldecks_indistinguishability_number_ge.
Print Assumptions psl211_alldecks_obstruction_published.
Print Assumptions psl211_alldecks_published_input_distinguishability.
Print Assumptions pgl27_word_input_distinguishability_false.
