(* K16 of the claim ledger at the S5 instance: the surface migration is
   notation only.

   Each equation below puts a program of the staged instance files, written
   in the decided surface, against the same program written through the bind
   and its payloads, which is the spelling the surface expanded to before
   the migration.  exact: erefl decides them, so the two texts are one term
   and every theorem proved about a program before the migration is a
   theorem about the program after it.

   The S5 instance is where the terminal below AnalysisBridged is written,
   so it carries the evidence for publish Observed assuming a as well as for
   the exact-independence statement and the three-payload terminal. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset.
From mathcomp Require Import matrix zmodp reals.
From infotheo Require Import fdist proba entropy.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import pgg_randomized_sharing pgg_canonical_sharing.
From pgg_smc Require Import s5_profile s5_exec s5_models.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import s5_tableau_observed s5_tableau_sampled.
From pgg_smc Require Import s5_tableau_analysis_bridged.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* publish Observed assuming a. *)
Lemma k16_s5_observed_bindE :
  s5_dealt_observed_published
  = (s5_dealt ;;; publish_observed of (AcceptsAxioms [:: AxS5GroupOrder])).
Proof. exact: erefl. Qed.

(* certify ExactIndependence by w, and publish t assuming a. *)
Lemma k16_s5_exact_bindE :
  s5_rand_published
  = (s5_rand_sampled
       ;;; certify_exact of s5_rand_exact_witness
       ;;; publish (AcceptsAxioms [:: AxS5GroupOrder]) of StaticExecutedOnly).
Proof. exact: erefl. Qed.
