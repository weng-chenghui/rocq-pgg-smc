(* Mutation check: the obstruction terminal taking a named payload, the
   spelling the inline rule replaces, is rejected by the staged surface.
   The rejection is a parse error, which Fail does not catch, so the file
   is compiled once without a guard and the message is kept beside it. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import var_dist_supp var_dist_joint_law.
From pgg_smc Require Import smc_interpreter pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_weighted_words.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import psl211_group psl211_orbit psl211_closure.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_mixing.
From pgg_smc Require Import psl211_exec psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_word_model psl211_word_proximity.
From pgg_smc Require Import psl211_reading_constancy.
From pgg_smc Require Import psl211_tableau_observed psl211_tableau_sampled.
From pgg_smc Require Import psl211_tableau_analysis_bridged.

Set Implicit Arguments.
Unset Strict Implicit.

Definition mutation_named_payload : PublishedObstruction :=
  psl211_exact_sampled
    |> publish Obstruction psl211_alldecks_obstruction
       by psl211_alldecks_obstruction_pf assuming BaselineClassicalOnly.
