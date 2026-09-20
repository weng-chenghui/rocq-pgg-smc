(* PROBE, not production. Every declaration this batch landed, ascribed at   *)
(* its full statement against the production files alone: no belowprobe      *)
(* module is required here, so what typechecks below is what the tree holds. *)
(*                                                                           *)
(* Homes: manifest/pgg_tableau.v (the two records, the restricted transfer   *)
(* payload, the two terminals, the six path equations, the three readers),   *)
(* manifest/pgg_tableau_syntax.v (the two surface rules) and                 *)
(* instances/s5/tableau/s5_tableau_observed.v (the five-seat value and its   *)
(* two lemmas). The four recorded rejections of s5_tableau_checks.v declare  *)
(* nothing and have no statement to ascribe.                                 *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset.
From mathcomp Require Import matrix zmodp ssralg ssrnum reals.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import s5_exec.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import s5_tableau_observed.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(******************************************************************************)
(*     The two records                                                        *)
(******************************************************************************)

Check (PublishedObserved : Type).
Check (MkPublishedObserved :
  forall (q : StackAt Observed) (p : AnalysisPath),
    StackProp Observed q -> PublishedObserved).
Check (published_observed_at : PublishedObserved -> StackAt Observed).
Check (published_observed_path : PublishedObserved -> AnalysisPath).
Check (published_observed_thm :
  forall r : PublishedObserved, StackProp Observed (published_observed_at r)).

Check (PublishedSampled : Type).
Check (MkPublishedSampled :
  forall (q : StackAt Sampled) (p : AnalysisPath),
    StackProp Sampled q -> PublishedSampled).
Check (published_sampled_at : PublishedSampled -> StackAt Sampled).
Check (published_sampled_path : PublishedSampled -> AnalysisPath).
Check (published_sampled_thm :
  forall r : PublishedSampled, StackProp Sampled (published_sampled_at r)).

(******************************************************************************)
(*     The restricted transfer payload                                        *)
(******************************************************************************)

Check (TransferStatusWithoutTheorem : Set).
Check (SampledNoModelComparison : TransferStatusWithoutTheorem).
Check (SampledStaticExecutedOnly : TransferStatusWithoutTheorem).
Check (transfer_of_without_theorem
         : TransferStatusWithoutTheorem -> TransferStatus).
Check (erefl : transfer_of_without_theorem SampledNoModelComparison
               = NoModelComparison).
Check (erefl : transfer_of_without_theorem SampledStaticExecutedOnly
               = StaticExecutedOnly).

(******************************************************************************)
(*     The two terminals and the six path equations                           *)
(******************************************************************************)

Check (publish_observed :
  forall q : StackAt Observed,
    StackProp Observed q -> AssumptionStatus -> PublishedObserved).
Check (publish_sampled :
  forall (a : AssumptionStatus) (q : StackAt Sampled),
    StackProp Sampled q -> TransferStatusWithoutTheorem -> PublishedSampled).

Check (publish_observed_completionE :
  forall (q : StackAt Observed) (pf : StackProp Observed q)
         (a : AssumptionStatus),
    ap_completion (published_observed_path (publish_observed q pf a))
    = Observed).
Check (publish_observed_transferE :
  forall (q : StackAt Observed) (pf : StackProp Observed q)
         (a : AssumptionStatus),
    ap_transfer (published_observed_path (publish_observed q pf a))
    = NoModelComparison).
Check (publish_observed_modelE :
  forall (q : StackAt Observed) (pf : StackProp Observed q)
         (a : AssumptionStatus),
    ap_model (published_observed_path (publish_observed q pf a)) = None).

Check (publish_sampled_completionE :
  forall (a : AssumptionStatus) (q : StackAt Sampled)
         (pf : StackProp Sampled q) (t : TransferStatusWithoutTheorem),
    ap_completion (published_sampled_path (publish_sampled a q pf t))
    = Sampled).
Check (publish_sampled_transferE :
  forall (a : AssumptionStatus) (q : StackAt Sampled)
         (pf : StackProp Sampled q) (t : TransferStatusWithoutTheorem),
    ap_transfer (published_sampled_path (publish_sampled a q pf t))
    = transfer_of_without_theorem t).
Check (publish_sampled_modelE :
  forall (a : AssumptionStatus) (q : StackAt Sampled)
         (pf : StackProp Sampled q) (t : TransferStatusWithoutTheorem),
    ap_model (published_sampled_path (publish_sampled a q pf t)) = sp_f q).

(******************************************************************************)
(*     The three readers                                                      *)
(******************************************************************************)

Check (run_correct_of_observed :
  forall r : PublishedObserved,
    oe_correct_prop (ob_obs (published_observed_at r))).
Check (run_correct_of_sampled :
  forall r : PublishedSampled,
    oe_correct_prop (sp_obs (published_sampled_at r))).
Check (view_identification_of_sampled :
  forall r : PublishedSampled,
    sampled_viewE_prop (sp_f (published_sampled_at r))).

(******************************************************************************)
(*     The two surface rules expand to the two terminals                      *)
(******************************************************************************)

Section SurfaceFidelity.
Variable a : AssumptionStatus.
Variable t : TransferStatusWithoutTheorem.
Variable qo : StackAt Observed.
Variable pfo : StackProp Observed qo.
Variable qs : StackAt Sampled.
Variable pfs : StackProp Sampled qs.

Check (erefl : (@MkTableau Observed (StackProp Observed) qo pfo
                |> publish Observed a)
               = publish_observed qo pfo a).
Check (erefl : (@MkTableau Sampled (StackProp Sampled) qs pfs
                |> publish Sampled t a)
               = publish_sampled a qs pfs t).

(* The rule the two new ones were added beside still parses, at each of the
   four transfer statuses and in particular at the two the thirty-one
   existing uses write. *)
Variable qb : StackAt AnalysisBridged.
Variable pfb : BridgedProp no_concluded_bound qb.

Check ((@MkTableau AnalysisBridged (StackProp AnalysisBridged) qb pfb
        |> publish IdealFinite a) : Published).
Check ((@MkTableau AnalysisBridged (StackProp AnalysisBridged) qb pfb
        |> publish StaticExecutedOnly a) : Published).
Check ((@MkTableau AnalysisBridged (StackProp AnalysisBridged) qb pfb
        |> publish NegativeTransfer a) : Published).
Check ((@MkTableau AnalysisBridged (StackProp AnalysisBridged) qb pfb
        |> publish NoModelComparison a) : Published).

End SurfaceFidelity.

(******************************************************************************)
(*     The five-seat value and its two lemmas                                 *)
(******************************************************************************)

Check (s5_dealt_observed_published : PublishedObserved).
Check (erefl : s5_dealt_observed_published
               = publish_observed (tableau_at s5_dealt) (tableau_thm s5_dealt)
                   (AcceptsAxioms [:: AxS5GroupOrder])).
Check (s5_dealt_observed_published_pathE :
  published_observed_path s5_dealt_observed_published = s5_det_path).
Check (s5_dealt_observed_published_recovers :
  forall (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    exec_decode S5Analysis.exec_plug
      (OE.oe_endpoints_size S5Analysis.observed s w0) = s).

Print Assumptions s5_dealt_observed_published.
Print Assumptions s5_dealt_observed_published_pathE.
Print Assumptions s5_dealt_observed_published_recovers.
