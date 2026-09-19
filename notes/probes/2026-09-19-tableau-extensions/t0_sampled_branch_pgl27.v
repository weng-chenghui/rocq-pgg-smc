(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe T0 at PGL(2,7): the branch point under a spectral payload            *)
(*                                                                            *)
(* t0_sampled_branch.v names one Tableau Sampled value of the five-card       *)
(* instance and continues it with an exact witness twice. Two coordinates of  *)
(* that shape were left untested there: the payload of the spectral arm,      *)
(* whose type mentions the model index, and a family whose index is not the   *)
(* unit type. This file runs the same shape at PGL(2,7), where the exact      *)
(* family's index is unit and the word family's is a distribution on the      *)
(* booleans, so the reduction through the name is exercised at both.          *)
(*                                                                            *)
(* A branch point is one named value of type Tableau Sampled. What the        *)
(* continuations read off it is the sample adapter their payload is typed at, *)
(* so a continuation elaborates only when sp_f reduces through the name. The  *)
(* two rejections below are the negative half: the exact witness of one model *)
(* of this instance does not continue the other model's branch point, and     *)
(* conversely, which is the discrimination a second arm over one model will   *)
(* need.                                                                      *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_exact_sampled     == the exact model, named at Sampled             *)
(*   pgl27_word_sampled      == the word model, named at Sampled              *)
(*   pgl27_row_exact_branch  == the exact branch point published              *)
(*   pgl27_row_exact_branch_ideal                                             *)
(*                           == the same, at the transfer status of a model   *)
(*                              comparison                                    *)
(*   pgl27_row_word_branch   == the word branch point published               *)
(*   pgl27_row_word_branch39 == the same, concluded at 2^-39 first            *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_row_exact_branch_atE                                               *)
(*                           == the exact branch point and the unbranched     *)
(*                              program hold one coordinate                   *)
(*   pgl27_row_exact_branch_ideal_atE                                         *)
(*                           == so does its second continuation               *)
(*   pgl27_row_exact_branch_rowE                                              *)
(*                           == the branch publishes the manifest's exact row *)
(*   pgl27_row_word_branch_atE                                                *)
(*                           == the same for the word model, under a          *)
(*                              spectral payload                              *)
(*   pgl27_row_word_branch39_atE                                              *)
(*                           == concluding at 2^-39 leaves that coordinate    *)
(*   pgl27_row_word_branch_armE                                               *)
(*                           == the word branch point's rows carry the        *)
(*                              spectral arm                                  *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finset order ssralg ssrnum reals boolp.
From infotheo Require Import fdist.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.
From tableau_ext_probe Require Import pgl27_rows.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(******************************************************************************)
(*     The exact model as a branch point                                      *)
(******************************************************************************)

(** The exact model of PGL(2,7), named at the level where a row has fixed a
    probability model and has not yet committed to an arm. This family's
    index is the unit type, so a continuation reads the sample adapter off
    the name with nothing else to unify. *)
Definition pgl27_exact_sampled : Tableau Sampled :=
  pgl27_dealt sample pgl27_exact_family.

(** The first continuation, published at the status the unbranched exact
    program publishes. *)
Definition pgl27_row_exact_branch : PublishedRow :=
  pgl27_exact_sampled
    certify ExactIndependence pgl27_exact_witness
    |> publish StaticExecutedOnly BaselineClassicalOnly.

(** The second continuation from the same name, at the transfer status of a
    model comparison. Both continuations certify the exact arm with one
    witness, so the two finished rows differ in their manifest row alone. *)
Definition pgl27_row_exact_branch_ideal : PublishedRow :=
  pgl27_exact_sampled
    certify ExactIndependence pgl27_exact_witness
    |> publish IdealFinite BaselineClassicalOnly.

(* Every coordinate equation of this file closes by exact: erefl and not by
   [], because ssreflect's done does not reach reflexivity on a goal whose
   two sides are published_at of a branch point and of a continuation: it
   spends its search first, and on the concluded row below that search does
   not return. The conversion itself is a tenth of a second. Measured on
   2026-09-19; the numbers are in STATUS.md, under the T0 step. *)

(** The branch point and the unbranched exact program hold one and the same
    AnalysisBridged coordinate, so naming the Sampled value costs the row
    nothing it would otherwise have. *)
Lemma pgl27_row_exact_branch_atE :
  published_at pgl27_row_exact_branch
  = published_at pgl27_row_exact_tableau.
Proof. exact: erefl. Qed.

(** The second continuation holds that same coordinate, so the two finished
    rows of this branch point differ in their manifest row alone. *)
Lemma pgl27_row_exact_branch_ideal_atE :
  published_at pgl27_row_exact_branch
  = published_at pgl27_row_exact_branch_ideal.
Proof. exact: erefl. Qed.

(** The branch publishes the manifest's own exact row. *)
Lemma pgl27_row_exact_branch_rowE :
  published_row pgl27_row_exact_branch = pgl27_row_exact.
Proof. by []. Qed.

(******************************************************************************)
(*     The word model as a branch point, under a spectral payload            *)
(******************************************************************************)

(** The word model of PGL(2,7), named at Sampled. Its family is indexed by a
    distribution on the booleans, so a continuation here unifies a payload
    whose type mentions both the real field and that index. *)
Definition pgl27_word_sampled : Tableau Sampled :=
  pgl27_dealt sample pgl27_word_family.

(** The first continuation of the word branch point, published at the row's
    own accumulated bound. *)
Definition pgl27_row_word_branch : PublishedRow :=
  pgl27_word_sampled
    certify SpectralDecay pgl27_word_cert
    |> publish IdealFinite BaselineClassicalOnly.

(** The second continuation, concluded at 2^-39 before it is published. The
    terminal sits between the branch point and the manifest row, so this pair
    exercises the reduction through the name across a terminal as well. *)
Definition pgl27_row_word_branch39 : PublishedRowAt pgl27_reprice39 :=
  pgl27_word_sampled
    certify SpectralDecay pgl27_word_cert
    |> conclude pgl27_reprice39 by (fun R _ => ssr_ext.eqW (pow2_split R))
    |> publish IdealFinite BaselineClassicalOnly.

(** The word branch point and the unbranched word program hold one
    AnalysisBridged coordinate, so a spectral payload reduces through the name
    exactly as an exact one does. *)
Lemma pgl27_row_word_branch_atE :
  published_at pgl27_row_word_branch
  = published_at pgl27_row_word_tableau.
Proof. exact: erefl. Qed.

(** Concluding at 2^-39 leaves that coordinate alone, so the terminal between
    the branch point and the manifest row moves a number and no data. *)
Lemma pgl27_row_word_branch39_atE :
  published_at pgl27_row_word_branch
  = published_at pgl27_row_word_branch39.
Proof. exact: erefl. Qed.

(** Both continuations of the word branch point carry the spectral arm, which
    is the value a paper's table prints for either of them. *)
Lemma pgl27_row_word_branch_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_word_branch)) R) :
  security_arm_of pgl27_row_word_branch R idx = SpectralDecayArm.
Proof. by []. Qed.

(******************************************************************************)
(*     The branch point is typed at one model                                 *)
(******************************************************************************)

(** The exact model's witness does not continue the word model's branch
    point. The payload type is ExactPayload at the coordinate the name holds,
    so the sample adapter the witness is stated over and the one the branch
    point reached are compared where the clause is written. Two models of one
    instance are separated here, which is finer than the separation of two
    instances. *)
Fail Definition pgl27_cross_model : Tableau AnalysisBridged :=
  pgl27_word_sampled certify ExactIndependence pgl27_exact_witness.

(** The same in the other direction, with the word model's certificate over
    the exact model's branch point. *)
Fail Definition pgl27_cross_model_back : Tableau AnalysisBridged :=
  pgl27_exact_sampled certify SpectralDecay pgl27_word_cert.
