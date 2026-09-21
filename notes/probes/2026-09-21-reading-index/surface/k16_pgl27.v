(* K16 of the claim ledger at the PGL(2,7) instance: the surface migration is
   notation only.

   The equation puts the exact-independence program of the staged instance
   file, written in the decided surface with the tightness annotation,
   against the same program written through the bind and its payloads.
   exact: erefl decides it.

   This instance carries the annotated certify statement, the one rule whose
   evidence clause is followed by two further clauses, so it is where a by
   inserted before the evidence could have changed which term the annotation
   is checked against.

   Two further equations of the same kind are already in the staged instance
   file and compiled there unchanged: pgl27_word_published_certE, which puts
   the five-clause input-indistinguishability program against the bind form
   with its certificate as one record, and pgl27_word_published39_bindE,
   which puts the concluded program against the bind form through
   pgl27_word_published39_bind. *)

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

(* certify ExactIndependence by w leaks at k by H, and publish t assuming a. *)
Lemma k16_pgl27_exact_bindE :
  pgl27_exact_published
  = (pgl27_exact_sampled
       ;;; certify_exact of (exact_leaks (tableau_at pgl27_exact_sampled)
                               pgl27_exact_witness 4 pgl27_exact_leak4)
       ;;; publish BaselineClassicalOnly of StaticExecutedOnly).
Proof. exact: erefl. Qed.
