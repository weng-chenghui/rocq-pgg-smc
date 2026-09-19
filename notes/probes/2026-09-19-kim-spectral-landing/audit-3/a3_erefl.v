(* AUDIT 3 scratch. Times the two closers of the one row equation that
   compares a concluded row with an unconcluded one. Lands nowhere. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import reals boolp.
From kim_landing_probe Require Import pgg_analysis_manifest pgg_tableau.
From kim_landing_probe Require Import five_card_rows.

Lemma a3_forms_by :
  published_row five_card_row_biased_spectral_tableau
  = published_row five_card_row_biased_inv25.
Proof. by []. Qed.

Lemma a3_forms_erefl :
  published_row five_card_row_biased_spectral_tableau
  = published_row five_card_row_biased_inv25.
Proof. exact: erefl. Qed.
