(* PROBE, not production. Decision 4 of                                       *)
(* notes/20260920-terminals-below-analysis-bridged-probe-design.md: the two   *)
(* surface rules at the framework's own constructor names, with the transfer  *)
(* status before the assumption status as in all thirty-one existing uses.    *)
(*                                                                            *)
(* The keyword question is re-measured here at the capitalised spelling, and  *)
(* in t_keyword_check_two_records.v at the lexer alone. Observed and Sampled  *)
(* are constructors of CompletionLevel that every file of the surface writes, *)
(* so a reservation would be paid for at once and not later.                  *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset.
From mathcomp Require Import matrix zmodp ssralg ssrnum reals.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_smc Require Import pgg_observed_execution.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import s5_exec.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import s5_tableau_executable.
From pgg_smc Require Import s5_tableau_observed.
From belowprobe Require Import t_framework_two_records.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* One payload, the assumption status: the level, the model slot and the
   transfer status are read off the program's own data. *)
Notation "s |> 'publish' 'Observed' a" := (s ;;; publish_observed of a)
  (at level 90, left associativity, a at level 0).

(* The transfer status and then the assumption status, in the order the
   manifest's path record carries them and the order the existing publish
   rule writes them. *)
Notation "s |> 'publish' 'Sampled' t a" := (s ;;; publish_sampled a of t)
  (at level 90, left associativity, t at level 0, a at level 0).

(******************************************************************************)
(*     The three terminals parse side by side                                 *)
(******************************************************************************)

Section TerminalsParse.

Variable qo : StackAt Observed.
Variable pfo : StackProp Observed qo.

Definition probe2_observed_terminal : PublishedObserved :=
  @MkTableau Observed (StackProp Observed) qo pfo
  |> publish Observed BaselineClassicalOnly.

Variable qs : StackAt Sampled.
Variable pfs : StackProp Sampled qs.

Definition probe2_sampled_terminal : PublishedSampled :=
  @MkTableau Sampled (StackProp Sampled) qs pfs
  |> publish Sampled SampledNoModelComparison BaselineClassicalOnly.

Definition probe2_sampled_terminal_static : PublishedSampled :=
  @MkTableau Sampled (StackProp Sampled) qs pfs
  |> publish Sampled SampledStaticExecutedOnly BaselineClassicalOnly.

Variable qb : StackAt AnalysisBridged.
Variable pfb : BridgedProp no_concluded_bound qb.

(* The existing terminal at each of the four transfer statuses, all four
   written where the two new rules write a literal. *)
Definition probe2_bridged_idealfinite : Published :=
  @MkTableau AnalysisBridged (StackProp AnalysisBridged) qb pfb
  |> publish IdealFinite BaselineClassicalOnly.

Definition probe2_bridged_negative : Published :=
  @MkTableau AnalysisBridged (StackProp AnalysisBridged) qb pfb
  |> publish NegativeTransfer BaselineClassicalOnly.

Definition probe2_bridged_static : Published :=
  @MkTableau AnalysisBridged (StackProp AnalysisBridged) qb pfb
  |> publish StaticExecutedOnly BaselineClassicalOnly.

Definition probe2_bridged_nomodel : Published :=
  @MkTableau AnalysisBridged (StackProp AnalysisBridged) qb pfb
  |> publish NoModelComparison BaselineClassicalOnly.

End TerminalsParse.

(******************************************************************************)
(*     The two tokens are still the constructors they name                    *)
(******************************************************************************)

Check (StackAt Observed).
Check (StackAt Sampled).
Check (Tableau Observed).
Check (Tableau Sampled).
Check Observed.
Check Sampled.
Check (fun Observed : nat => Observed).
Check (fun Sampled : nat => Sampled).

(******************************************************************************)
(*     A program of the five-seat instance written in the surface             *)
(******************************************************************************)

Definition probe2_s5_dealt_observed_published : PublishedObserved :=
  s5_algebra
    dealt   fuel 150
    execute terminates by s5_dealt_terminates
            endpoints by s5_dealt_endpoints
            recon by s5_dealt_recon
  |> publish Observed (AcceptsAxioms [:: AxS5GroupOrder]).

(* The rule fired rather than the existing one parsing Observed as a term:
   the right side applies the Observed terminal by hand. *)
Lemma probe2_s5_surfaceE :
  probe2_s5_dealt_observed_published
  = publish_observed (tableau_at s5_dealt) (tableau_thm s5_dealt)
      (AcceptsAxioms [:: AxS5GroupOrder]).
Proof. exact: erefl. Qed.

Lemma probe2_s5_pathE :
  published_observed_path probe2_s5_dealt_observed_published = s5_det_path.
Proof. exact: erefl. Qed.
