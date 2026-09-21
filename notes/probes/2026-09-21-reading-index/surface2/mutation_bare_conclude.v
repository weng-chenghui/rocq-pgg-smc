(* Mutation check: a conclude terminal without at is rejected by the
   staged surface.  The program is pgl27_word_published39 with at removed
   and nothing else changed.  The rejection is a parse error, which Fail
   does not catch, so the file is compiled once without a guard and the
   message is kept beside it. *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import pgl27_tableau_observed pgl27_tableau_sampled.
From pgg_smc Require Import pgl27_proximity.
From pgg_smc Require Import pgl27_tableau_analysis_bridged.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition mutation_bare_conclude : PublishedAt pgl27_bound39 :=
  pgl27_word_sampled
    certify InputIndistinguishability by pgl27_word_cert
    |> conclude pgl27_bound39 by (fun R _ => ssr_ext.eqW (pow2_split R))
    |> publish IdealFinite assuming BaselineClassicalOnly.
