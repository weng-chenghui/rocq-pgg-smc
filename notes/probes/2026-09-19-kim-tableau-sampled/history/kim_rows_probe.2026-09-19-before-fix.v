(* PROBE, notes/probes/2026-09-19-kim-tableau-sampled/kim_rows_probe.v        *)
(* Ledger rows K1 to K6 of notes/20260919-kim-tableau-sampled-design.md.      *)
(* Imports are exactly those of instances/kim2025/five_card_rows.v, plus      *)
(* five_card_rows itself.                                                     *)

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
(*     K1 and K2: the two programs                                            *)
(******************************************************************************)

Definition five_card_row_repeated_tableau : Tableau Sampled :=
  five_card_committed
    sample kim_centi_family.

Definition five_card_row_biased_tableau : Tableau Sampled :=
  five_card_committed
    sample kim_biased_family.

(******************************************************************************)
(*     K3: the three programs share one prefix                                *)
(******************************************************************************)

Lemma five_card_row_repeated_prefixE :
  [/\ projT1 (tableau_at five_card_row_repeated_tableau)
      = projT1 (tableau_at five_card_committed),
      projT1 (projT2 (tableau_at five_card_row_repeated_tableau))
      = projT1 (projT2 (tableau_at five_card_committed)),
      sp_Ht (tableau_at five_card_row_repeated_tableau)
      = ob_Ht (tableau_at five_card_committed),
      sp_He (tableau_at five_card_row_repeated_tableau)
      = ob_He (tableau_at five_card_committed)
    & sp_Hr (tableau_at five_card_row_repeated_tableau)
      = ob_Hr (tableau_at five_card_committed)].
Proof. by split. Qed.

Lemma five_card_row_biased_prefixE :
  [/\ projT1 (tableau_at five_card_row_biased_tableau)
      = projT1 (tableau_at five_card_committed),
      projT1 (projT2 (tableau_at five_card_row_biased_tableau))
      = projT1 (projT2 (tableau_at five_card_committed)),
      sp_Ht (tableau_at five_card_row_biased_tableau)
      = ob_Ht (tableau_at five_card_committed),
      sp_He (tableau_at five_card_row_biased_tableau)
      = ob_He (tableau_at five_card_committed)
    & sp_Hr (tableau_at five_card_row_biased_tableau)
      = ob_Hr (tableau_at five_card_committed)].
Proof. by split. Qed.

(* Expected failure: S5Analysis.rand_family is an AnalysisModelFamily over
   S5Analysis.rand_observed, a different observed execution, so sample_step
   has no payload type for it at this prefix. *)
Fail Definition five_card_row_alien_tableau : Tableau Sampled :=
  five_card_committed
    sample S5Analysis.rand_family.

(* Expected failure: the same for the den Boer run's own observed execution
   under the uniform family's type. *)
Fail Definition five_card_row_alien2_tableau : Tableau Sampled :=
  five_card_committed
    sample PGL27Analysis.exact_family.

(******************************************************************************)
(*     K4: each program samples its manifest row's model                      *)
(******************************************************************************)

Lemma five_card_row_repeated_modelE :
  sp_f (tableau_at five_card_row_repeated_tableau)
  = apr_model five_card_row_repeated.
Proof. by []. Qed.

Lemma five_card_row_biased_modelE :
  sp_f (tableau_at five_card_row_biased_tableau)
  = apr_model five_card_row_biased.
Proof. by []. Qed.

(* The two rows name one observed execution, the manifest's own. *)
Lemma five_card_rows_obsE :
  [/\ sp_obs (tableau_at five_card_row_repeated_tableau)
      = FiveCardAnalysis.observed
    & sp_obs (tableau_at five_card_row_biased_tableau)
      = FiveCardAnalysis.observed].
Proof. by split. Qed.

(******************************************************************************)
(*     K5: the repeated row's manifest level                                  *)
(******************************************************************************)

Lemma five_card_row_repeated_levelE :
  apr_completion five_card_row_repeated = Sampled.
Proof. by []. Qed.

(* The level index of the program's type is the manifest row's own completion
   level, checked by the kernel rather than by the reader. *)
Definition five_card_row_repeated_at_manifest_level
  : Tableau (apr_completion five_card_row_repeated) :=
  five_card_row_repeated_tableau.

(* Expected failure: the biased row's manifest level is AnalysisBridged, and
   its program reaches Sampled, so the same ascription is rejected. *)
Fail Definition five_card_row_biased_at_manifest_level
  : Tableau (apr_completion five_card_row_biased) :=
  five_card_row_biased_tableau.

Check (erefl : apr_completion five_card_row_biased = AnalysisBridged).

(******************************************************************************)
(*     K6: one seat's endpoint marginal under the row's own cut law           *)
(******************************************************************************)

Lemma five_card_row_repeated_endpoint_lt (R : realType) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
              (sa_cut_dist (amf_sample kim_centi_family R tt)))
           (fdist_uniform (card_ord 5))
  < 2%:R ^- 40.
Proof. by rewrite kim_centi_cut_distE; exact: kim_deal_centi_lt. Qed.

Print Assumptions five_card_row_repeated_endpoint_lt.

(* Expected failure: the same script at 2^-41. kim_deal_centi_lt bounds the
   distance by 2^-40 and nothing in the tree tightens it, so the final
   exact does not unify. *)
Fail Definition five_card_row_repeated_endpoint_lt41
    (R : realType) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
              (sa_cut_dist (amf_sample kim_centi_family R tt)))
           (fdist_uniform (card_ord 5))
  < 2%:R ^- 41
  := ltac:(rewrite kim_centi_cut_distE; exact: kim_deal_centi_lt).

(* Expected failure: the same bound read on a pair of seats. kim_deal_centi_lt
   is a statement about one seat's marginal on 'I_5, so its conclusion does
   not typecheck against a distance on 'I_5 * 'I_5. *)
Fail Definition five_card_row_repeated_endpoint_pair_lt
    (R : realType) (s s' : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => (sigma s, sigma s'))
              (sa_cut_dist (amf_sample kim_centi_family R tt)))
           (fdist_prod (fdist_uniform (card_ord 5))
              (fun _ : 'I_5 => fdist_uniform (card_ord 5)))
  < 2%:R ^- 40
  := ltac:(rewrite kim_centi_cut_distE; exact: kim_deal_centi_lt).
