(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* n_syntax: the surface of the refuting terminal (probe, ledger row N7)      *)
(*                                                                            *)
(* One rule, a terminal from Tableau Sampled. Its only quoted token is        *)
(* refute, which follows the literal |> as publish and conclude do in         *)
(* manifest/pgg_tableau_syntax.v, so it reserves no identifier; by follows    *)
(* the slot o and is ssreflect's already. The rule writes the obstruction and *)
(* its proof as two named things, as the five-clause certificate rule does.   *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From refuteprobe Require Import n_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* The obstruction and the proof of it, in the order the record carries them.
   The assumption status leads, as it is the only payload the manifest's path
   does not read off the program's own data, the transfer status of such a
   path being fixed at NegativeTransfer by the terminal. *)
Notation "s |> 'refute' a o 'by' pf" :=
  (s ;;; refute a of (mk_obstruction (tableau_at s) o pf))
  (at level 90, left associativity, a at level 0, o at level 0, pf at level 0).

(* refute is still an identifier in the file that declares the rule. *)
Check refute.

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
Variable H : ObstructionPropOf o.

Check (s |> publish Sampled tw a : PublishedSampled).
Check (u |> publish t a : Published).
Check (s |> refute a o by H : PublishedObstruction).

End surface_coexistence.
