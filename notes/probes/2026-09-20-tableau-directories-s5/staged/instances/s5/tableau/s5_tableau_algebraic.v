(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5_tableau_algebraic: the five-seat instance at the Algebraic level        *)
(*                                                                            *)
(* The Algebraic level of a row holds an algebra and nothing besides, and the *)
(* proposition it carries is True. A reader shown only this file has been     *)
(* shown which group acts on the deck, which scheme the dealer shares and     *)
(* which seats read, and no claim about a coalition, a run or a probability   *)
(* model. Every five-seat row begins here, so the value below is the one      *)
(* point at which the instance's two sharing-family runs agree.               *)
(*                                                                            *)
(* The algebra is s5_algebra of s5_exec.v and is not restated here: the four  *)
(* adjacent transpositions of five card positions generate the shuffle group, *)
(* the sum-mod-5 scheme carries its own encoding, reconstruction and privacy  *)
(* obligation, and the seats start at the deck positions in order. What this  *)
(* file adds is that algebra read as the first line of a program, which is    *)
(* what lets each level above it be named on its own.                         *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   s5_algebraic         == the five-seat algebra as a program at Algebraic  *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset.
From mathcomp Require Import matrix zmodp ssralg ssrnum reals.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import s5_exec.
From pgg_smc Require Import pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(******************************************************************************)
(*     The algebra as the first line of a row                                 *)
(******************************************************************************)

(** The five-seat instance at the Algebraic level: the algebra alone, under
    the empty proposition that level carries. Both sharing-family runs
    continue from this one value, the dealer-dealt run through the scheme's
    canonical encoding and the supplied run through an additive layout of a
    sampler tape, so what separates the two modes is the level above and not
    this one. *)
Definition s5_algebraic : Tableau Algebraic := tableau_start s5_algebra.
