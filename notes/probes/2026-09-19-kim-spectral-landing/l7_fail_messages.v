(* PROBE DIAGNOSTIC, not part of the landing and not in _CoqProject.          *)
(* It states, without the Fail guard, the declaration five_card_rows.v keeps   *)
(* as a recorded Fail, so that rocq compile prints the message the guard       *)
(* absorbs.  Compiling this file is expected to FAIL; its error text is the    *)
(* record.                                                                     *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import reals boolp.
From infotheo Require Import fdist proba entropy.
From kim_landing_probe Require Import five_card_mixing.
From kim_landing_probe Require Import pgg_analysis_manifest pgg_tableau.
From kim_landing_probe Require Import pgg_tableau_syntax five_card_rows.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition five_card_row_repeated_spectral_uniform_rowE
  : published_row five_card_row_repeated_spectral_tableau
    = five_card_row_uniform
  := erefl.
