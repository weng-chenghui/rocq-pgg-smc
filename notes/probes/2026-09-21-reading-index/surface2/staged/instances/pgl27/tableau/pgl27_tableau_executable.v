(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_tableau_executable: the eight-card orbit instance at the Executable  *)
(* level                                                                      *)
(*                                                                            *)
(* The Executable level adjoins run-level data to the algebra: what the run   *)
(* argument is, who commits, what the dealer lays, what a seat observes after *)
(* a shuffle, what value the run is meant to recover and how much interpreter *)
(* fuel it is allowed. The proposition is still True, so a reader shown this  *)
(* file has been shown which run is about to be made, and no proof that it    *)
(* terminates or that it recovers the value its parameters name.              *)
(*                                                                            *)
(* The instance does not branch here. One run mode is named, the dealer-dealt *)
(* one: the run argument is the orbit class the dealer holds, no party        *)
(* commits an input, the dealer lays the orbit scheme's canonical encoding of *)
(* that class into eight cards, and the interpreter is given pgl27_fuel. The  *)
(* line continues pgl27_algebraic_start through the raw bind rather than      *)
(* through a keyword rule, because the rules dealt and supplied begin at a    *)
(* PGGAlgebraic and encoded at a Targeted over one, so the keyword surface    *)
(* has no form that continues a named value at Algebraic.                     *)
(*                                                                            *)
(* The two identifications of the framework's static reading of a coalition   *)
(* with pgl27_view are statements about this parameter record and about no    *)
(* program value, and they are in instances/pgl27/pgl27_proximity.v beside    *)
(* the distance whose proof rewrites with them, so that the mathematics       *)
(* requires no tableau module.                                                *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_dealt_executable  == the dealer-dealt run's parameters as a        *)
(*                              program                                       *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_dealt_executable_paramsE                                           *)
(*                           == the dealt line builds the record              *)
(*                              pgl27_dealt_params names                      *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finset reals boolp.
From infotheo Require Import fdist.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import pgl27_tableau_algebraic.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.


(******************************************************************************)
(*     The dealer-dealt run's parameters                                      *)
(******************************************************************************)

(** The dealer-dealt mode at the Executable level: the run argument is the
    orbit class the dealer holds, no party commits an input, the dealer lays
    the orbit scheme's canonical encoding of that class, and the interpreter
    is given pgl27_fuel. Naming the parameters as a program is what lets the
    run facts of the level above be adjoined to a value rather than to a
    prefix spelled out again. *)
Definition pgl27_dealt_executable : Tableau Executable :=
  pgl27_algebraic_start ;;; dealt_step of pgl27_fuel.

(** The parameter record this line builds is the one pgl27_dealt_params
    names. The line writes a fuel and leaves dealt_step to build the record,
    so the equation is what lets a statement made at pgl27_dealt_params be
    read as a statement about this program. *)
Lemma pgl27_dealt_executable_paramsE :
  projT2 (tableau_at pgl27_dealt_executable) = pgl27_dealt_params.
Proof. exact: erefl. Qed.
