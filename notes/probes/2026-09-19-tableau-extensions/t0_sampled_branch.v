(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe T0: two claims continue from one named Tableau Sampled value         *)
(*                                                                            *)
(* A row is one security claim with its whole chain, so two claims about one  *)
(* probability model are two programs over one model. That shape needs a      *)
(* Tableau Sampled value to be namable and continuable twice, and no program  *)
(* of the tree branches at Sampled today. This file names the five-card       *)
(* uniform model as such a value and runs two certify continuations from it.  *)
(*                                                                            *)
(* The hazard the design audit records is that a continuation's payload type  *)
(* is ExactPayload (tableau_at X) for the named X, so sp_f must reduce        *)
(* through the name X before the instance's witness can unify with it.        *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   five_card_uniform_sampled == the five-card uniform model, named at       *)
(*                                Sampled and continued twice                 *)
(*   t0_row_uniform            == the first continuation, published           *)
(*   t0_row_uniform_transfer   == the second, published at another status     *)
(*   t0_s5_sampled             == another instance's model, named at Sampled  *)
(*                                                                            *)
(* Key results:                                                               *)
(*   t0_row_uniform_rowE   == the branch publishes the manifest row the       *)
(*                            unbranched five-card uniform program publishes  *)
(*   t0_row_uniform_atE    == the two continuations and the unbranched        *)
(*                            program hold one AnalysisBridged coordinate     *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import reals boolp.
From infotheo Require Import fdist proba entropy.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import five_card_exec five_card_models.
From pgg_smc Require Import s5_exec s5_models.
From pgg_smc Require Import pgg_analysis_manifest.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.
From tableau_ext_probe Require Import five_card_rows s5_rows.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     A branch point at Sampled                                              *)
(******************************************************************************)

(** The five-card uniform model, named at the level where a row has fixed a
    probability model and has not yet made a security claim. Naming it is what
    lets two claims about this one model be two rows that cannot drift apart
    in their algebra, their run or their law, since all three are read off
    this single term. *)
Definition five_card_uniform_sampled : Tableau Sampled :=
  five_card_committed
    sample five_card_uniform_family.

(** The first continuation: independence of a coalition's reading from the
    conjunction of the committed bits, published at the status the unbranched
    five-card uniform program publishes. The branch point enters as a name,
    so the witness clause is elaborated against sp_f of that name. *)
Definition t0_row_uniform : PublishedRow :=
  five_card_uniform_sampled
    certify ExactIndependence five_card_exact_witness
    |> publish StaticExecutedOnly BaselineClassicalOnly.

(** The second continuation from the same name, published at the transfer
    status of a model comparison. Two published rows over one Sampled value
    are what one model carrying two claims looks like. *)
Definition t0_row_uniform_transfer : PublishedRow :=
  five_card_uniform_sampled
    certify ExactIndependence five_card_exact_witness
    |> publish IdealFinite BaselineClassicalOnly.

(** The branch publishes the manifest row of the program that reaches the
    same claim without a branch point. Conversion decides it, so naming the
    Sampled value costs the row nothing it would otherwise have. *)
Lemma t0_row_uniform_rowE :
  published_row t0_row_uniform
  = published_row five_card_row_uniform_tableau.
Proof. by []. Qed.

(** The manifest row is also the one the manifest writes for this path. *)
Lemma t0_row_uniform_manifestE :
  published_row t0_row_uniform = five_card_row_uniform.
Proof. by []. Qed.

(** The two continuations and the unbranched program hold one and the same
    AnalysisBridged coordinate: the algebra, the run, the three run facts, the
    model and the port are one term in all three. What separates the two
    published rows is the transfer status alone. *)
Lemma t0_row_uniform_atE :
  [/\ published_at t0_row_uniform
      = published_at five_card_row_uniform_tableau,
      published_at t0_row_uniform_transfer
      = published_at five_card_row_uniform_tableau
    & published_at t0_row_uniform = published_at t0_row_uniform_transfer].
Proof. by split. Qed.

(** The two published rows differ, and differ only where the two claims about
    one model are meant to differ: in what the manifest records of the path. *)
Lemma t0_row_uniform_row_neq :
  published_row t0_row_uniform <> published_row t0_row_uniform_transfer.
Proof. by move=> H; move: (congr1 apr_transfer H). Qed.

(******************************************************************************)
(*     The branch point is typed at one instance                              *)
(******************************************************************************)

(** Another instance's model, named at the same level. *)
Definition t0_s5_sampled : Tableau Sampled :=
  s5_supplied
    sample s5_rand_family.

(** A witness of the five-card instance does not continue another instance's
    named Sampled value. The payload type is ExactPayload at the coordinate
    the name holds, so the sample adapter the witness is stated over and the
    one the branch point reached are compared where the clause is written. *)
Fail Definition t0_cross_instance : Tableau AnalysisBridged :=
  t0_s5_sampled
    certify ExactIndependence five_card_exact_witness.

(** The same in the other direction. *)
Fail Definition t0_cross_instance_back : Tableau AnalysisBridged :=
  five_card_uniform_sampled
    certify ExactIndependence s5_rand_exact_witness.
