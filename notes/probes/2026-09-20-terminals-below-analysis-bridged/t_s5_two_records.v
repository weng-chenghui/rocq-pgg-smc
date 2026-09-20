(* PROBE, not production. The five-seat value at the landing names and in    *)
(* the landing surface, decisions 1, 4 and 5 of                              *)
(* notes/20260920-terminals-below-analysis-bridged-probe-design.md.          *)
(*                                                                           *)
(* The three declarations below are what                                     *)
(* instances/s5/tableau/s5_tableau_observed.v receives, verbatim apart from  *)
(* the docstring delimiters that file uses.                                  *)

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
From belowprobe Require Import t_framework_two_records.
From belowprobe Require Import t_syntax_two_records.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* The dealer-dealt run handed over with the manifest path it answers. The
   assumption status is the instance's group-order fact, which enters through
   the reconstruction plug the profile carries; the status is written here
   and the manifest's prose defines when it is true, so nothing in the term
   checks it against Print Assumptions. What the value carries is run
   correctness and no more: nothing about a coalition is asserted, which is
   the honest content of this run, whose canonical encoding puts the whole
   secret on one card. *)
Definition s5_dealt_observed_published : PublishedObserved :=
  s5_dealt |> publish Observed (AcceptsAxioms [:: AxS5GroupOrder]).

(* The path this program builds is the manifest's own deterministic path.
   Four of its five coordinates are fixed by the terminal and one is the
   observed execution s5_dealt_path_observedE already identifies, so what the
   equation adds is that the theorem now travels beside the path rather than
   the path being a description a reader matches by eye. *)
Lemma s5_dealt_observed_published_pathE :
  published_observed_path s5_dealt_observed_published = s5_det_path.
Proof. exact: erefl. Qed.

(* The third conjunct of run correctness, read off the published value: the
   endpoints of the deterministic run decode to the dealt position. It is the
   statement S5Analysis.observed_recovers names, and the two other conjuncts
   of the same And3 come off the same reader. *)
Definition s5_dealt_observed_published_recovers
    (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile))
    (Gw0 : w0 \in pgg_G (mp_M S5Analysis.profile)) :
  exec_decode S5Analysis.exec_plug
    (OE.oe_endpoints_size S5Analysis.observed s w0) = s :=
  match run_correct_of_observed s5_dealt_observed_published s w0 Gw0 with
  | And3 _ _ H => H
  end.

(* The type just built is the one the manifest pins for the facade alias. *)
Check (s5_dealt_observed_published_recovers :
  forall (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    exec_decode S5Analysis.exec_plug
      (OE.oe_endpoints_size S5Analysis.observed s w0) = s).

Check (S5Analysis.observed_recovers :
  forall (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    exec_decode S5Analysis.exec_plug
      (OE.oe_endpoints_size S5Analysis.observed s w0) = s).

(******************************************************************************)
(*     The four rejections that land in s5_tableau_checks.v                   *)
(******************************************************************************)

Fail Check (view_secrecy_of s5_dealt_observed_published).
Fail Check (security_property_of s5_dealt_observed_published).
Fail Check (s5_dealt_observed_published : Published).
Fail Definition s5_dealt_baseline_pathE :
  published_observed_path (s5_dealt |> publish Observed BaselineClassicalOnly)
  = s5_det_path := erefl.

(******************************************************************************)
(*     The assumptions                                                        *)
(******************************************************************************)

Print Assumptions s5_dealt.
Print Assumptions s5_dealt_observed_published.
Print Assumptions s5_dealt_observed_published_pathE.
Print Assumptions s5_dealt_observed_published_recovers.
