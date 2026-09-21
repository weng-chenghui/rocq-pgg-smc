(* K16 of the claim ledger at the PSL(2,11) instance: the surface migration
   is notation only.

   Three equations put programs of the staged instance file, written in the
   decided surface, against the same programs written through the bind and
   its payloads.  exact: erefl decides them.

   This instance carries the terminal handing over an obstruction, whose
   rule is the one where the assumption status sat next to a proof and read
   as that proof's argument, and it is the only instance where the proximity
   statement and the obstruction terminal stand over one model.  The last
   equation is written here rather than taken from the tree: no file of the
   tree writes the terminal at Sampled, so the rule publish Sampled t
   assuming a has no program to migrate and is exercised only here. *)

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
Import Prenex Implicits.

(* certify IdealProximity by c, and publish t assuming a. *)
Lemma k16_psl211_proximity_bindE :
  psl211_word_proximity_published
  = (psl211_word_sampled
       ;;; certify_idealproximity of psl211_word_proximity_cert
       ;;; publish BaselineClassicalOnly of IdealFinite).
Proof. exact: erefl. Qed.

(* publish Obstruction o by pf assuming a. *)
Lemma k16_psl211_obstruction_bindE :
  psl211_alldecks_obstruction_published
  = (psl211_exact_sampled
       ;;; publish_obstruction BaselineClassicalOnly
             of (mk_obstruction (tableau_at psl211_exact_sampled)
                   psl211_alldecks_obstruction
                   psl211_alldecks_obstruction_pf)).
Proof. exact: erefl. Qed.

(* publish Sampled t assuming a, the rule no program of the tree writes. *)
Definition k16_psl211_sampled_published : PublishedSampled :=
  psl211_exact_sampled
    |> publish Sampled SampledStaticExecutedOnly assuming BaselineClassicalOnly.

Lemma k16_psl211_sampled_bindE :
  k16_psl211_sampled_published
  = (psl211_exact_sampled
       ;;; publish_sampled BaselineClassicalOnly of SampledStaticExecutedOnly).
Proof. exact: erefl. Qed.
