(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* five_card_tableau_sampled: the five-card instance at the Sampled level     *)
(*                                                                            *)
(* The Sampled level adjoins a probability model to a run, and what it adds   *)
(* to run correctness is the identification of the two readings of a          *)
(* coalition: at every real field and every index of the family, the reader   *)
(* built from the interpreter's own endpoints is the one computed directly    *)
(* from the run argument and the cut. That identification is what turns a     *)
(* claim about the messages a run exchanges into a claim about a group        *)
(* action, and it is the last thing proved before an arm is named.            *)
(*                                                                            *)
(* Three families are named here, one per model a published row continues     *)
(* from, and all three sit over the one committed run and are indexed by the  *)
(* unit type. five_card_uniform_family draws the cut uniformly from the five  *)
(* rotations. kim_centi_family draws it by seven repetitions of Kim's biased  *)
(* cut at bias one hundredth, and kim_biased_family by one such cut. The two  *)
(* Kim families differ from the uniform one in the law of the rotation and in *)
(* nothing else: the committed pair is drawn uniformly and independently of   *)
(* the cut in all three.                                                      *)
(*                                                                            *)
(* five_card_row_repeated_tableau and five_card_row_biased_tableau are names  *)
(* the instance already had, and they carry the published-row suffix although *)
(* both are Tableau Sampled values and neither is a published row. They are   *)
(* existing names and they stay. five_card_uniform_sampled follows the naming *)
(* scheme, and the five rows written out from the prefix are identified with  *)
(* these three values in five_card_tableau_analysis_bridged.v.                *)
(*                                                                            *)
(* What is proved at this level beside the three models is of two kinds, and  *)
(* no arm of certify takes a payload of either.                               *)
(* five_card_row_repeated_endpoint_lt is one starting position's endpoint     *)
(* marginal under the repeated model's cut law, a statement about where a     *)
(* single position is sent and not about what any set of seats reads.         *)
(* five_card_row_biased_leak_bound is Kim's input-privacy bound, an upper     *)
(* bound on the conditional mutual information between the two committed      *)
(* inputs and the executed colour reading at a list of card positions, given  *)
(* the conjunction the run computes, under the law the one-cut model samples; *)
(* it is about a reading at a list of card positions and not about a          *)
(* coalition of seats, and it is a bound and not a vanishing. It is the one   *)
(* security statement this instance makes below AnalysisBridged, and it is of *)
(* this level for two reasons: its subject is the law the named Sampled model *)
(* samples, and no arm of certify takes a conditional mutual information as a *)
(* payload, so no program can carry it one level up.                          *)
(*                                                                            *)
(* The manifest records AnalysisBridged for both Kim rows, which              *)
(* five_card_row_biased_levelE states for the one-cut row, and the two        *)
(* programs named here reach Sampled. Each of the two rows also carries a     *)
(* certified program that does reach AnalysisBridged, in                      *)
(* five_card_tableau_analysis_bridged.v, and the ascription of the one-cut    *)
(* Sampled program at the manifest's level is refused in                      *)
(* five_card_tableau_checks.v.                                                *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   five_card_uniform_sampled                                                *)
(*                           == the committed run under the uniform rotation, *)
(*                              named at Sampled                              *)
(*   five_card_row_repeated_tableau                                           *)
(*                           == the committed run under seven of Kim's biased *)
(*                              cuts, named at Sampled                        *)
(*   five_card_row_biased_tableau                                             *)
(*                           == the committed run under one of Kim's biased   *)
(*                              cuts, named at Sampled                        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   five_card_row_repeated_prefixE                                           *)
(*                           == the repeated model carries the prefix's       *)
(*                              algebra, parameters and observed execution    *)
(*   five_card_row_biased_prefixE                                             *)
(*                           == the one-cut model carries the same three      *)
(*   five_card_row_repeated_modelE                                            *)
(*                           == the repeated program samples the model the    *)
(*                              manifest's row names                          *)
(*   five_card_row_biased_modelE                                              *)
(*                           == the one-cut program samples the model the     *)
(*                              manifest's row names                          *)
(*   five_card_row_biased_levelE                                              *)
(*                           == the manifest's completion level for the one-  *)
(*                              cut row is AnalysisBridged                    *)
(*   five_card_row_repeated_endpoint_lt                                       *)
(*                           == one starting position's endpoint marginal     *)
(*                              under the repeated model's cut law is within  *)
(*                              2^-40 of uniform                              *)
(*   kim_centi_small         == the smallness condition at bias one hundredth *)
(*   five_card_row_biased_leak_bound                                          *)
(*                           == Kim's input-privacy bound at the law the one- *)
(*                              cut model samples                             *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import reals boolp lra.
From infotheo Require Import fdist proba entropy.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage five_card_exec five_card_models.
From pgg_smc Require Import kim_input_privacy.
From pgg_smc Require Import five_card_mixing.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import five_card_tableau_observed.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.


(******************************************************************************)
(*     The uniform rotation as a branch point                                 *)
(******************************************************************************)

(** The committed run under the uniform rotation, named at Sampled. The
    family is indexed by the unit type, so one member at each real field,
    and the cut that member draws is already the uniform one on the five
    rotations, so a row over this model compares no biased cut with an
    ideal. *)
Definition five_card_uniform_sampled : Tableau Sampled :=
  five_card_committed
    sample five_card_uniform_family.


(******************************************************************************)
(*     Kim's two models                                                       *)
(******************************************************************************)

(** The repeated row sampled and not certified: the prefix
    five_card_committed and the seven-cut model at bias one hundredth. The
    program stops at Sampled, one level under the AnalysisBridged the
    manifest records for this row. It names its model and nothing else, and
    what is proved beside it is the law of one starting position's endpoint
    under its cut, a statement about where a single starting position is
    sent and not about what any set of seats reads, so no security payload
    follows this program.
    five_card_row_repeated_indistinguishability_tableau is the certified
    program for the same row. *)
Definition five_card_row_repeated_tableau : Tableau Sampled :=
  five_card_committed
    sample kim_centi_family.

(** The biased row sampled and not certified: the same prefix and the single
    cut at the same bias. The program stops at Sampled, one level under the
    AnalysisBridged the manifest records for this row, because
    five_card_colour_view_leak_bound bounds a conditional mutual information
    and no arm of certify takes a bound of that kind. The manifest's
    level for this row rests on that theorem and on the certificate
    five_card_row_biased_indistinguishability_tableau carries, and on no
    payload of this program. *)
Definition five_card_row_biased_tableau : Tableau Sampled :=
  five_card_committed
    sample kim_biased_family.


(******************************************************************************)
(*     What the three models share with the prefix                            *)
(******************************************************************************)

(** The three rows are one prefix and three continuations: the algebra, the
    run parameters and the observed execution of each Kim row are those of
    five_card_committed, as terms, and the observed execution carries the
    three run facts in its own fields. A reader comparing the three rows is
    therefore comparing probability models and nothing else. *)
Lemma five_card_row_repeated_prefixE :
  [/\ projT1 (tableau_at five_card_row_repeated_tableau)
      = projT1 (tableau_at five_card_committed),
      projT1 (projT2 (tableau_at five_card_row_repeated_tableau))
      = projT1 (projT2 (tableau_at five_card_committed))
    & sp_obs (tableau_at five_card_row_repeated_tableau)
      = ob_obs (tableau_at five_card_committed)].
Proof. by split. Qed.

(** The same for the biased row. *)
Lemma five_card_row_biased_prefixE :
  [/\ projT1 (tableau_at five_card_row_biased_tableau)
      = projT1 (tableau_at five_card_committed),
      projT1 (projT2 (tableau_at five_card_row_biased_tableau))
      = projT1 (projT2 (tableau_at five_card_committed))
    & sp_obs (tableau_at five_card_row_biased_tableau)
      = ob_obs (tableau_at five_card_committed)].
Proof. by split. Qed.

(** The model each program samples is the model the manifest's row for it
    names. Conversion decides both, so the manifest's description of these
    two five-card paths and the programs are one term, as
    five_card_row_uniform_rowE makes them for the uniform path. *)
Lemma five_card_row_repeated_modelE :
  sp_f (tableau_at five_card_row_repeated_tableau)
  = apr_model five_card_row_repeated.
Proof. by []. Qed.

(** The same for the biased row and the manifest's biased row. *)
Lemma five_card_row_biased_modelE :
  sp_f (tableau_at five_card_row_biased_tableau)
  = apr_model five_card_row_biased.
Proof. by []. Qed.

(** The manifest's completion level for the biased row is AnalysisBridged.
    five_card_row_biased_tableau reaches Sampled, so this equation and the
    rejected ascription of five_card_tableau_checks.v are the two halves of
    that one program's level gap. The equation is a fact about the
    manifest's row and not about anything any program proves, and the biased
    path also carries a program that does reach AnalysisBridged. *)
Lemma five_card_row_biased_levelE :
  apr_completion five_card_row_biased = AnalysisBridged.
Proof. by []. Qed.


(******************************************************************************)
(*     What the two Kim models carry beside their programs                    *)
(******************************************************************************)

(** The law of the image of one starting position under the cut the repeated
    row samples is within two to the minus fortieth of the uniform law on the
    five card positions, in variation distance, at every starting position and
    every real field. Both laws are laws on card positions, so this is one
    position's endpoint marginal, and the statement names no seat, no set of
    seats and no secret. It is kim_deal_centi_lt read at the law the program
    names, through kim_centi_cut_distE. *)
Lemma five_card_row_repeated_endpoint_lt (R : realType) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
              (sa_cut_dist (amf_sample kim_centi_family R tt)))
           (fdist_uniform (card_ord 5))
  < 2%:R ^- 40.
Proof. by rewrite kim_centi_cut_distE; exact: kim_deal_centi_lt. Qed.

(** The bias one hundredth is smaller in absolute value than one fifth, the
    smallness condition of kim_input_private. It is the fourth of the side
    conditions on this bias, beside kim_centi_lt, kim_centi_gt and
    kim_centi_spec of five_card_kim.v, and the one Kim's input-privacy bound
    consumes. *)
Lemma kim_centi_small (R : realType) : 0 < 5%:R^-1 - `|1 / 100 : R|.
Proof.
by rewrite subr_gt0 ger0_norm ?divr_ge0// ltr_pdivrMr ?ltr0n//
   mulrC ltr_pdivlMr ?ltr0n// mul1r ltr_nat.
Qed.

(** The conditional mutual information between the two committed inputs and
    the executed colour reading at a list of card positions, given the
    conjunction the run computes, is at most kim_leak_bound at bias one
    hundredth, under the law the biased row samples. It is
    five_card_colour_view_leak_bound with every random variable typed at
    that law, which is what sa_sampleP of the family's member is by
    conversion. The statement is a numeric upper bound on that information and
    not the assertion that the information vanishes, it is about a reading
    at a list of card positions and not about a coalition of seats, and it
    is carried beside the program above rather than by it. *)
Lemma five_card_row_biased_leak_bound (R : realType) (A : seq nat) :
  cond_mutual_info
    (`p_ [% (kim_inputs (kim_centi_lt R) (kim_centi_gt R)
             : {RV (sa_sampleP (amf_sample kim_biased_family R tt))
                   -> bool * bool}),
            ((fun w : five_card_leakage.Omega =>
                five_card_exec_colour_view A w.1
                  (five_card_group.fc_sigma ^+ w.2)%g)
             : {RV (sa_sampleP (amf_sample kim_biased_family R tt))
                   -> (size A).-tuple bool}),
            (kim_secret (kim_centi_lt R) (kim_centi_gt R)
             : {RV (sa_sampleP (amf_sample kim_biased_family R tt)) -> bool})])
  <= kim_leak_bound (1 / 100 : R).
Proof. exact: (five_card_colour_view_leak_bound _ _ (kim_centi_small R)). Qed.
