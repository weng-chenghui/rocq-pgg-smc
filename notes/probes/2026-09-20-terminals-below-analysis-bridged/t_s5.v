(* PROBE, not production. Rows T3, T4 at the instance, T5 at the instance and *)
(* T9 of notes/20260920-terminals-below-analysis-bridged-probe-design.md.     *)
(*                                                                            *)
(* The five-seat dealer-dealt program stops at Observed and the manifest      *)
(* carries a path that stops there with it. This file ties the two: the       *)
(* program's terminal builds that path from the program's own data, and the   *)
(* run-correctness statement a downstream file cites today is read off the    *)
(* published value.                                                           *)

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
From belowprobe Require Import t_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     T3: the five-seat dealer-dealt program, published at Observed          *)
(******************************************************************************)

(* The dealer-dealt run of the five-seat instance handed over with the
   manifest path that describes it. The assumption status is the instance's
   group-order fact, which enters through the reconstruction plug the profile
   carries. Nothing about a coalition is asserted: the value carries run
   correctness and no more, which is the honest content of this run, whose
   canonical encoding puts the whole secret on one card. *)
Definition s5_det_published : PublishedObserved :=
  publish_observed (AcceptsAxioms [:: AxS5GroupOrder]) s5_dealt.

(* The path this terminal builds is the manifest's own deterministic path.
   Conversion decides it, so the manifest's record of how far this path's
   theorems reach and the proof that they reach it are one term. *)
Lemma s5_det_published_pathE :
  published_level_path s5_det_published = s5_det_path.
Proof. exact: erefl. Qed.

(* The mutation: the same program published under the baseline assumption
   status does not build the manifest's path, the path recording the accepted
   group-order fact. *)
Fail Definition s5_det_baseline_pathE_false :
  published_level_path (publish_observed BaselineClassicalOnly s5_dealt)
  = s5_det_path := erefl.

(******************************************************************************)
(*     T4: the run-correctness reader at the instance                         *)
(******************************************************************************)

(* The third conjunct of run correctness, read off the published value: the
   endpoints of the deterministic run decode to the dealt position. It is the
   statement the manifest pins for this path's correctness theorem, so a
   reader of the published value reaches the same fact the facade alias
   names. *)
Definition s5_det_published_recovers
    (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile))
    (Gw0 : w0 \in pgg_G (mp_M S5Analysis.profile)) :
  exec_decode S5Analysis.exec_plug
    (OE.oe_endpoints_size S5Analysis.observed s w0) = s :=
  match run_correct_of_level s5_det_published s w0 Gw0 with
  | And3 _ _ H => H
  end.

(* The type just built is the one the manifest pins for the facade alias. *)
Check (s5_det_published_recovers :
  forall (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    exec_decode S5Analysis.exec_plug
      (OE.oe_endpoints_size S5Analysis.observed s w0) = s).

(* The same type, at the alias the manifest names today. *)
Check (S5Analysis.observed_recovers :
  forall (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    exec_decode S5Analysis.exec_plug
      (OE.oe_endpoints_size S5Analysis.observed s w0) = s).

(******************************************************************************)
(*     T5 at the instance: no security reader applies                         *)
(******************************************************************************)

(* The exact-independence reader does not apply to this value. *)
Fail Check (view_secrecy_of s5_det_published).

(* Neither does the reader naming a security property. *)
Fail Check (security_property_of s5_det_published).

(* And the value is not a Published. *)
Fail Check (s5_det_published : Published).

(******************************************************************************)
(*     T9: the assumptions of the published value and its path equation       *)
(******************************************************************************)

Print Assumptions s5_dealt.
Print Assumptions s5_det_published.
Print Assumptions s5_det_published_pathE.
Print Assumptions s5_det_published_recovers.
