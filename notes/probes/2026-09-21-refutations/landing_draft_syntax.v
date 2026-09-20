(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* landing_draft_syntax: the surface rule of the landing, compiled before it  *)
(* is written into manifest/pgg_tableau_syntax.v. The Notation below is the   *)
(* production text; the coexistence section is not.                           *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From refuteprobe Require Import landing_draft_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* The obstruction, its proof and then the assumption status. The obstruction
   occupies the column the transfer status occupies in the other two publish
   rules, that coordinate being fixed at NegativeTransfer by the terminal, so
   a program's last statement still reads in the order the manifest column
   headings run. *)
Notation "s |> 'publish' 'Obstruction' o 'by' pf a" :=
  (s ;;; publish_obstruction a of (mk_obstruction (tableau_at s) o pf))
  (at level 90, left associativity, o at level 0, pf at level 0,
   a at level 0).

(******************************************************************************)
(*     The existing terminal rules still parse beside it                      *)
(******************************************************************************)

Section surface_coexistence.

Variable s : Tableau Sampled.
Variable u : Tableau AnalysisBridged.
Variable a : AssumptionStatus.
Variable tw : TransferStatusWithoutTheorem.
Variable t : TransferStatus.
Variable o : ObstructionPayload (tableau_at s).
Variable H : ObstructionPayloadProp o.

Check (s |> publish Sampled tw a : PublishedSampled).
Check (u |> publish t a : Published).
Check (s |> publish Obstruction o by H a : PublishedObstruction).

End surface_coexistence.
