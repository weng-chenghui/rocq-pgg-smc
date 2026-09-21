(* Item 1(b): the inline obstruction terminal at the PSL(2,11) instance.

   Three questions, each answered by a declaration that compiles or does
   not.

   First, whether the term the inline rule reaches is the term the rule it
   replaces reached. k_obstruction_old_formE puts the migrated program
   against the bind form the round-1 surface expanded to, which names the
   payload psl211_alldecks_obstruction and its proof.

   Second, whether the instance still needs a named payload written by
   plain constructor application. k_obstruction_pf_inline states the proof
   at the builder's payload instead, with the same two conjuncts, and
   k_obstruction_no_named_payloadE puts the program it terminates against
   the instance's own. If both compile the named payload is a convenience
   and not a requirement.

   Third, whether a reader still gets the number back.
   k_obstruction_numberE reads the kind off the published value at the one
   index of the family. *)

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
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* The migrated program and the bind form of the rule it replaces. *)
Lemma k_obstruction_old_formE :
  psl211_alldecks_obstruction_published
  = (psl211_exact_sampled
       ;;; publish_obstruction BaselineClassicalOnly
             of (mk_obstruction (tableau_at psl211_exact_sampled)
                   psl211_alldecks_obstruction
                   psl211_alldecks_obstruction_pf)).
Proof. exact: erefl. Qed.

(* The proof stated at the builder's payload, with no named payload
   between it and the terminal. *)
Definition k_obstruction_pf_inline
  : ObstructionPayloadProp
      (input_distinguishability_obstruction (tableau_at psl211_exact_sampled)
         psl211_alldecks_number) :=
  fun (R : realType) (_ : unit) =>
    conj (psl211_alldecks_obstruction_gt0 R)
         (psl211_alldecks_input_distinguishability R).

Definition k_obstruction_no_named_payload : PublishedObstruction :=
  psl211_exact_sampled
    |> publish Obstruction InputDistinguishability
       at psl211_alldecks_number
       by k_obstruction_pf_inline assuming BaselineClassicalOnly.

Lemma k_obstruction_no_named_payloadE :
  k_obstruction_no_named_payload = psl211_alldecks_obstruction_published.
Proof. exact: erefl. Qed.

(* The number the published value carries, read back at the one index. *)
Lemma k_obstruction_numberE (R : realType) :
  published_obstruction_kind psl211_alldecks_obstruction_published R tt
  = @InputDistinguishabilityObstruction R psl211_algebra
      psl211_alldecks_params (amf_sample psl211_exact_family R tt)
      ((#|pgg_G psl211_M|%:R)^-1).
Proof. exact: erefl. Qed.
