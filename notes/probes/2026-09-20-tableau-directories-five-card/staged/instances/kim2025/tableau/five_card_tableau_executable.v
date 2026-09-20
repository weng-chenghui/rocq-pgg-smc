(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* five_card_tableau_executable: the five-card instance at the Executable     *)
(* level                                                                      *)
(*                                                                            *)
(* The Executable level adjoins run-level data to the algebra: what the run   *)
(* argument is, who commits, what the dealer lays, what a seat observes after *)
(* a cut, what value the run is meant to recover and how much interpreter     *)
(* fuel it is allowed. The proposition is still True, so a reader shown this  *)
(* file has been shown which run is about to be made, and no proof that it    *)
(* terminates or that it recovers the value its parameters name.              *)
(*                                                                            *)
(* The instance does not branch here. One run mode is named, the committed    *)
(* one: the run argument is the pair of bits two parties commit,              *)
(* five_card_commits are the processes that commit them, den_boer_decode      *)
(* reads the pair back out of the payload list, the dealer lays               *)
(* den_boer_layout of that pair, den_boer_assemble_valid is the sharing claim *)
(* of the encoding and is checked where it is written, and the interpreter is *)
(* given fuel 100. The value the run is meant to recover is read off the      *)
(* Targeted rather than written again, which is what keeps the function a row *)
(* names and the value its run recovers one term.                             *)
(*                                                                            *)
(* The line continues five_card_algebraic_start through the raw bind rather   *)
(* than through a keyword rule. The rules dealt and supplied begin at a       *)
(* PGGAlgebraic and encoded at a Targeted over one, so the keyword surface    *)
(* has no form that continues a named value at Algebraic, and this is the one *)
(* edge of a row the surface cannot write when the two levels are two files.  *)
(* The record the line builds is encoded_input_params at five_card_target's   *)
(* own function, which is the record the encoded rule builds from that same   *)
(* Targeted.                                                                  *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   five_card_committed_executable                                           *)
(*                           == the committed run's parameters as a program   *)
(*                                                                            *)
(* Key results:                                                               *)
(*   five_card_committed_executable_paramsE                                   *)
(*                           == the committed line builds the record          *)
(*                              five_card_params names                        *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import order ssrnum ssralg reals boolp.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_observed_execution.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_exec.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import five_card_tableau_algebraic.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.


(******************************************************************************)
(*     The committed run's parameters                                         *)
(******************************************************************************)

(** The committed mode at the Executable level: the run argument is the pair
    of bits two parties commit, the dealer lays den Boer's five-card layout
    of the decoded pair, the value the run is meant to recover is the
    conjunction five_card_target names, and the interpreter is given fuel
    100. Naming the parameters as a program is what lets the run facts of
    the level above be adjoined to a value rather than to a prefix spelled
    out again. *)
Definition five_card_committed_executable : Tableau Executable :=
  five_card_algebraic_start ;;; params_step
    of (encoded_input_params five_card_algebra (bool * bool)
          (tg_f five_card_target) den_boer_layout
          den_boer_assemble_valid den_boer_decode
          five_card_commits 100).

(** The parameter record this line builds is the one five_card_params names.
    The clauses above spell the record out a second time, so the equation is
    what lets a statement made at five_card_params be read as a statement
    about this program. *)
Lemma five_card_committed_executable_paramsE :
  projT2 (tableau_at five_card_committed_executable)
  = five_card_params.
Proof. exact: erefl. Qed.
