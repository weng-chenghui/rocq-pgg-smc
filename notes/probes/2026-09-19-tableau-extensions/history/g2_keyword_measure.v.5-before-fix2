(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe G2: what the conclude rule costs a file requiring the surface        *)
(*                                                                            *)
(* The statement surface spends an identifier as a global keyword in every    *)
(* file requiring it whenever that identifier follows a slot in some rule.    *)
(* The conclude rule writes s |> 'conclude' c 'by' p, so its two words        *)
(* follow the literal |> and the slot c. This file measures both against a    *)
(* file requiring the surface: a keyword can no longer be read as an          *)
(* identifier, cannot be bound, and cannot be written unqualified.            *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   conclude_stays_bindable == a binder named conclude, in a file that       *)
(*                             requires the surface                           *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset reals.
From infotheo Require Import fdist.
From pgg_smc Require Import pgg_analysis_status pgg_instance.
From pgg_smc Require Import pgg_analysis_manifest.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.

Set Implicit Arguments.
Unset Strict Implicit.

(* The framework's own terminal is still reachable under its bare name. *)
Check conclude.

(* And so is the type of the obligation the rule's last slot carries. *)
Check RepricePayload.

(* The word conclude is still an identifier: it binds, and the bound
   occurrence is read back as the binder and not as a notation token. *)
Definition conclude_stays_bindable (conclude : nat) : nat := conclude.

(* publish is the token the existing terminal rule spends in the same
   position, after the literal |>, and it is an identifier too. *)
Check publish.

(* The nineteen the header names cost what conclude does not. A binder named
   sample or certify is a parse error in this file, and a parse error is
   raised before Fail can see the command, so the contrast is recorded in the
   probe's status note and not as a Fail here. *)
