(* Audit round 2, question 5: the recorded Fail pgl27_row_word39_unindexed_bind,
   written without Fail so that the error message can be read. *)
From mathcomp Require Import fintype finset reals boolp.
From infotheo Require Import fdist.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest.
From tableau_ext_probe Require Import pgg_tableau.
From tableau_ext_probe Require Import pgg_tableau_syntax.
From tableau_ext_probe Require Import pgl27_rows.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Definition q5b_unindexed_bind : PublishedRowAt pgl27_reprice39 :=
  pgl27_dealt
    ;;; sample_step of pgl27_word_family
    ;;; certify_spectral of pgl27_word_cert
    ;;; conclude pgl27_reprice39 of (fun R => ssr_ext.eqW (pow2_split R))
    ;;; publish BaselineClassicalOnly of IdealFinite.
