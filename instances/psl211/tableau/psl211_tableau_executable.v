(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_tableau_executable: the twelve-card instance at the Executable      *)
(*                            level                                           *)
(*                                                                            *)
(* The Executable level adjoins run-level data to the algebra: what the run   *)
(* argument is, who commits, what the dealer lays, what a seat observes after *)
(* a shuffle, what value the run is meant to recover and how much interpreter *)
(* fuel it is allowed. The proposition is still True, so a reader shown this  *)
(* file has been shown which run is about to be made, and no proof that it    *)
(* terminates or that it recovers the value its parameters name.              *)
(*                                                                            *)
(* One run mode is named here, the all-decks one, in the supplied-layout mode *)
(* of the framework: the run argument is a whole deck description, a          *)
(* chirality bit with a deal, the layout lays that description as the dealt   *)
(* deck, and the value the run is meant to recover is the chirality bit.      *)
(* Three of the five paths the manifest carries for this instance,            *)
(* psl211_alldecks_path, psl211_word_path and                                 *)
(* psl211_alldecks_obstruction_path, are over this one run. The first two     *)
(* part at the model, and the third parts from the first at the transfer      *)
(* status. The other two, psl211_dealt_colour_path and                        *)
(* psl211_dealt_obstruction_path, are over the dealer-dealt run and not over  *)
(* this one.                                                                  *)
(*                                                                            *)
(* psl211_exec.v carries a second parameter record, psl211_dealt_params, in   *)
(* the dealer-dealt mode, where the run argument is the secret itself. It     *)
(* carries that record's own reconstruction and termination facts. The two    *)
(* programs of psl211_tableau_dealt.v continue from it and publish those      *)
(* other two paths, and the refutation psl211_dealt_constancy_false of        *)
(* psl211_reading_constancy.v is a further statement made at it. It is named  *)
(* here and not built into a value.                                           *)
(*                                                                            *)
(* The line below continues psl211_algebraic_start through the raw bind       *)
(* rather than through a keyword rule. The rules dealt and supplied begin at  *)
(* a PGGAlgebraic and encoded at a Targeted over one, so the keyword surface  *)
(* has no form that continues a named value at Algebraic, and this is the one *)
(* edge of a program the surface cannot write when the two levels are         *)
(* two files.                                                                 *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_alldecks_executable == the all-decks run's parameters as a        *)
(*                                 program                                    *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_alldecks_executable_paramsE                                       *)
(*                              == the all-decks line builds the record       *)
(*                                 psl211_alldecks_params names               *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import psl211_exec psl211_alldecks.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import psl211_tableau_algebraic.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(******************************************************************************)
(*     The all-decks run's parameters                                         *)
(******************************************************************************)

(** The all-decks mode at the Executable level: the run argument is a deck
    description, the dealer lays that description as the twelve dealt cards,
    the value the run is meant to recover is the chirality bit of its
    argument, and the interpreter is given the instance's fuel of 220
    steps. No party commits an input, so the run carries no commit process,
    and the value it names is a reading of the run's own argument rather than
    an ideal function of anyone's input. Naming the parameters as a program
    is what lets the run facts of the level above be adjoined to a value
    rather than to a prefix spelled out again. *)
Definition psl211_alldecks_executable : Tableau Executable :=
  psl211_algebraic_start ;;; params_step
    of (supplied_input_params psl211_algebra psl211_inputT
          psl211_alldecks_layout psl211_alldecks_expected psl211_fuel).

(** The parameter record this line builds is the one psl211_alldecks_params
    names. The clauses above spell the record out a second time, so the
    equation is what keeps the two spellings from parting: every statement of
    the levels above is made at psl211_alldecks_params, and the prefix is
    made at the clauses. *)
Lemma psl211_alldecks_executable_paramsE :
  projT2 (tableau_at psl211_alldecks_executable) = psl211_alldecks_params.
Proof. exact: erefl. Qed.
