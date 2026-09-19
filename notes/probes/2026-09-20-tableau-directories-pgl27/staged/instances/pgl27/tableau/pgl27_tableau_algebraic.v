(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_tableau_algebraic: the eight-card orbit instance at the Algebraic    *)
(* level                                                                      *)
(*                                                                            *)
(* The Algebraic level of a row holds an algebra and nothing besides, and the *)
(* proposition it carries is True. A reader shown only this file has been     *)
(* shown which group shuffles the deck, which scheme the dealer shares and    *)
(* which seats read, and no claim about a coalition, a run or a probability   *)
(* model. All seven published rows of this instance begin at that algebra, so *)
(* the value below is the one point at which the exact, the word and the      *)
(* prior-indexed exact analyses agree.                                        *)
(*                                                                            *)
(* The algebra is pgl27_algebra of pgl27_exec.v and is not restated here:     *)
(* PGL(2,7) acts on the eight card positions, the orbit scheme deals one of   *)
(* the two orbit classes into those eight cards and carries its own encoding, *)
(* reconstruction and privacy obligation, and the eight seats start at the    *)
(* eight card positions in order. Four is the threshold that algebra names,   *)
(* so every statement above this file that quantifies over a coalition        *)
(* quantifies over at most three of the eight seats. What this file adds is   *)
(* that algebra read as the first line of a program, which is what lets each  *)
(* level above it be named on its own.                                        *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_algebraic_start   == the eight-card orbit algebra as a program at  *)
(*                              Algebraic                                     *)
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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.


(******************************************************************************)
(*     The algebra as the first line of a row                                 *)
(******************************************************************************)

(** The eight-card orbit instance at the Algebraic level: the algebra alone,
    under True, the proposition that level carries. One run mode is built on
    this value, the dealer-dealt one, and pgl27_dealt_executableE is where
    the prefix all seven published rows continue from is identified with it.
    The three probability models the instance analyses part two levels
    above, so what this file fixes is shared by every row the instance
    publishes. *)
Definition pgl27_algebraic_start : Tableau Algebraic :=
  tableau_start pgl27_algebra.
