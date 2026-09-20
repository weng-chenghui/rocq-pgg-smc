(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5_tableau_executable: the five-seat instance at the Executable level      *)
(*                                                                            *)
(* The Executable level adjoins run-level data to the algebra: what the run   *)
(* argument is, who commits, what the dealer lays, what a seat observes after *)
(* a shuffle, what value the run is meant to recover and how much interpreter *)
(* fuel it is allowed. The proposition is still True, so a reader shown this  *)
(* file has been shown which run is about to be made, and no proof that it    *)
(* terminates or that it recovers the value its parameters name.              *)
(*                                                                            *)
(* The five-seat instance branches here, and only here below the models. The  *)
(* dealer-dealt mode makes the secret position itself the run argument and    *)
(* leaves the dealer to lay the scheme's canonical encoding, the tuple that   *)
(* is zero everywhere but the last coordinate. The supplied mode makes a      *)
(* sampler tape the run argument, lays the probability-free additive layout   *)
(* of that tape, and names the value the run is meant to recover beside it,   *)
(* because a sharing family has no ideal function of a committer's input to   *)
(* read that value off. Both modes run at fuel 150 over the one algebra.      *)
(*                                                                            *)
(* Both lines continue s5_algebraic_start through the raw bind rather than    *)
(* through a keyword rule. The rules dealt and supplied begin at a            *)
(* PGGAlgebraic and encoded at a Targeted over one, so the keyword surface    *)
(* has no form that continues a named value at Algebraic, and this is the one *)
(* edge of a row the surface cannot write when the two levels are two files.  *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   s5_dealt_executable  == the dealer-dealt run's parameters as a program   *)
(*   s5_supplied_executable                                                   *)
(*                        == the supplied run's parameters as a program       *)
(*                                                                            *)
(* Key results:                                                               *)
(*   s5_dealt_executable_paramsE                                              *)
(*                        == the dealer-dealt line builds the record          *)
(*                           s5_dealt_params names                            *)
(*   s5_supplied_executable_paramsE                                           *)
(*                        == the supplied line builds the record              *)
(*                           s5_supplied_params names                         *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset.
From mathcomp Require Import matrix zmodp ssralg ssrnum reals.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import s5_exec.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import s5_tableau_algebraic.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(******************************************************************************)
(*     The dealer-dealt run's parameters                                      *)
(******************************************************************************)

(** The dealer-dealt mode at the Executable level: the run argument is the
    secret position, no party commits an input, and the interpreter is given
    fuel 150. Naming the parameters as a program is what lets the run facts
    of the level above be adjoined to a value rather than to a prefix spelled
    out again. *)
Definition s5_dealt_executable : Tableau Executable :=
  s5_algebraic_start ;;; dealt_step of 150.

(** The parameter record this line builds is the one s5_dealt_params names.
    The line writes a fuel and leaves dealt_step to build the record, so the
    equation is what lets a statement made at s5_dealt_params be read as a
    statement about this program. *)
Lemma s5_dealt_executable_paramsE :
  projT2 (tableau_at s5_dealt_executable) = s5_dealt_params.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The supplied run's parameters                                          *)
(******************************************************************************)

(** The supplied mode at the Executable level: the run argument is a sampler
    tape, the dealer lays the additive layout of that tape, the value the run
    is meant to recover is the tape's secret coordinate carried through the
    codec, and the interpreter is given fuel 150. No sharing claim is written
    into the record, which is what leaves this mode with a reconstruction
    obligation of its own at the level above. *)
Definition s5_supplied_executable : Tableau Executable :=
  s5_algebraic_start ;;; params_step
    of (supplied_input_params s5_algebra 'rV['Z_5]_5
          s5_rfree_layout (fun u => s5_codec (s5_tape_secret u)) 150).

(** The parameter record this line builds is the one s5_supplied_params
    names. The clauses above spell the record out a second time, so the
    equation is what keeps the two spellings from parting. *)
Lemma s5_supplied_executable_paramsE :
  projT2 (tableau_at s5_supplied_executable) = s5_supplied_params.
Proof. exact: erefl. Qed.
