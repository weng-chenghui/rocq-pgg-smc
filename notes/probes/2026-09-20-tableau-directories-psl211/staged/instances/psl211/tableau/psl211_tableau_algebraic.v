(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_tableau_algebraic: the twelve-card instance at the Algebraic level  *)
(*                                                                            *)
(* The Algebraic level of a row holds an algebra and nothing besides, and the *)
(* proposition it carries is True. A reader shown only this file has been     *)
(* shown which group shuffles the deck, which scheme the dealer shares and    *)
(* which seats read, and no claim about a coalition, a run or a probability   *)
(* model. Every twelve-card row begins here.                                  *)
(*                                                                            *)
(* The algebra is psl211_algebra of psl211_exec.v and is not restated here:   *)
(* the shuffle group is PSL(2,11) in its twelve-point action, the scheme      *)
(* carries its own encoding, reconstruction and privacy obligation, and the   *)
(* twelve seats start at the deck positions in order. What this file adds is  *)
(* that algebra read as the first line of a program, which is what lets each  *)
(* level above it be named on its own.                                        *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_algebraic_start == the twelve-card algebra as a program at        *)
(*                             Algebraic                                      *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import psl211_exec.
From pgg_smc Require Import pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(******************************************************************************)
(*     The algebra as the first line of a row                                 *)
(******************************************************************************)

(** The twelve-card chirality instance at the Algebraic level: the algebra
    alone, under True, the proposition that level carries. One run mode is
    built on this value, the all-decks one, and psl211_alldecks_executableE
    is where the prefix both published rows continue from is identified with
    it. The dealer-dealt parameters of psl211_exec.v are built from the same
    algebra and from no program. What separates the run modes is the level
    above and not this one. *)
Definition psl211_algebraic_start : Tableau Algebraic :=
  tableau_start psl211_algebra.
