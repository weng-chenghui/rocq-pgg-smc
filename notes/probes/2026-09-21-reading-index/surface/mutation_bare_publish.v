(* Mutation check: a publish terminal without assuming is rejected by the
   staged surface.

   The program is s5_rand_published with assuming removed from its
   terminal and nothing else changed, so the assumption status sits next to
   the transfer status as a bare last term, the spelling the migration
   removes.  The rejection is a parse error, which Fail does not catch, so
   the file is compiled once without a guard and the message is kept in
   msg/mutation_bare_publish.after.msg. *)

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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition mutation_bare_publish : Published :=
  s5_rand_sampled
    certify ExactIndependence by s5_rand_exact_witness
    |> publish StaticExecutedOnly (AcceptsAxioms [:: AxS5GroupOrder]).
