(* Audit round 3, scratch: print the four cross-model / cross-instance
   rejection messages, to check the comments of the two T0 files. *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import order ssralg ssrnum reals boolp.
From infotheo Require Import fdist proba entropy.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import five_card_exec five_card_models.
From pgg_smc Require Import s5_exec s5_models.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.
From tableau_ext_probe Require Import five_card_rows s5_rows pgl27_rows.
From tableau_ext_probe Require Import t0_sampled_branch t0_sampled_branch_pgl27.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Definition m1 : Tableau AnalysisBridged :=
  s5_rand_sampled
    certify ExactIndependence five_card_exact_witness.
