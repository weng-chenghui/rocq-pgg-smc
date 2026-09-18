(* PROBE, notes/probes/2026-09-19-kim-tableau-sampled/                        *)
(* kim_production_fidelity.v                                                  *)
(*                                                                            *)
(* As built. kim_fidelity.v with its import pointed at the production module  *)
(* pgg_smc.five_card_rows, so that every number below is read off the file    *)
(* that now sits in instances/kim2025/ and not off the landing copy. The      *)
(* landing copy defines the same names under the logical path                 *)
(* kim_tableau_sampled_probe, and is deliberately not required here.          *)
(*                                                                            *)
(* The repository baseline is the classical trio                              *)
(* propositional_extensionality, functional_extensionality_dep and            *)
(* constructive_indefinite_description, which an fdist-record statement       *)
(* carries throughout the tree. Any fourth name printed below is a finding.   *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import reals boolp.
From infotheo Require Import fdist proba entropy.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter pgg_trace_secrecy.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage five_card_exec five_card_models.
From pgg_smc Require Import kim_input_privacy.
From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import five_card_rows.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     (a) The assumption closure of the eleven landed declarations           *)
(******************************************************************************)

Print Assumptions five_card_row_repeated_tableau.
Print Assumptions five_card_row_biased_tableau.
Print Assumptions five_card_row_repeated_prefixE.
Print Assumptions five_card_row_biased_prefixE.
Print Assumptions five_card_row_repeated_modelE.
Print Assumptions five_card_row_biased_modelE.
Print Assumptions five_card_row_repeated_at_manifest_level.
Print Assumptions five_card_row_biased_levelE.
Print Assumptions five_card_row_repeated_endpoint_lt.
Print Assumptions kim_centi_small.
Print Assumptions five_card_row_biased_leak_bound.

(******************************************************************************)
(*     (b) The two facts the programs rest on, at the production module       *)
(******************************************************************************)

(* The biased row's law is Kim's own joint input law, so the ascription of the
   three random variables in five_card_row_biased_leak_bound renames nothing.
   This is the soundness audit's B6(a). *)
Check (fun R : realType => erefl
  : sa_sampleP (amf_sample kim_biased_family R tt)
  = kim_input_dist (kim_centi_lt R) (kim_centi_gt R)).

(* The manifest row's model slot, at its unique index, is the concrete adapter
   the manifest's own bound theorems name. This is the soundness audit's B3. *)
Check (fun R : realType => erefl
  : amf_sample (apr_model five_card_row_repeated) R tt
  = FiveCardAnalysis.centi_sample R).

Check (fun R : realType => erefl
  : amf_sample (apr_model five_card_row_biased) R tt
  = FiveCardAnalysis.single_biased_sample (kim_centi_lt R) (kim_centi_gt R)).

(* The same at the cut law, which is the carrier
   five_card_row_repeated_endpoint_lt states its bound on. *)
Check (fun R : realType => erefl
  : sa_cut_dist (amf_sample (apr_model five_card_row_repeated) R tt)
  = sa_cut_dist (FiveCardAnalysis.centi_sample R)).

(* The negative control: the uniform family's member is a different law, so the
   biased row's bound is genuinely stated at the biased row's law and the
   ascription is not vacuous about which law it names. *)
Fail Check (fun R : realType => erefl
  : sa_sampleP (amf_sample five_card_uniform_family R tt)
  = kim_input_dist (kim_centi_lt R) (kim_centi_gt R)).

(******************************************************************************)
(*     (c) The two programs, at the production module                         *)
(******************************************************************************)

Check (five_card_row_repeated_tableau : Tableau Sampled).
Check (five_card_row_biased_tableau : Tableau Sampled).
