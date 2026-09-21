(* Probe B round 2, item 6: where the endpoint obligation of the
   dealer-dealt PSL(2,11) run and the Observed value over it can live.

   instances/psl211/psl211_exec.v is frozen, so the obligation cannot be
   added there.  The file proposed is instances/psl211/psl211_models.v,
   which is NOT frozen and which already carries the all-decks twins
   psl211_alldecks_endpoints and psl211_alldecks_observed.  This probe has
   EXACTLY the Require lines of psl211_models.v at HEAD and nothing else, so
   that its compiling is evidence that psl211_models.v can hold the two
   definitions with no new Require and therefore with no new edge in the
   dependency graph and no cycle. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import dealer_privacy.
From pgg_reconstruct Require Import design_privacy.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import psl211_group psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_exec.
From pgg_smc Require Import psl211_endpoints psl211_alldecks.
From pgg_smc Require Import psl211_blocks psl211_closure.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(** psl211_dealt_endpoints — the interpreter's messages of the dealer-dealt
    run compute the direct computation of the laid deck.  The profile's
    abstract-readout equation quantifies over the content readout, so the
    dealer-dealt mode rests on the same equation the all-decks mode rests on
    and this costs no reduction of its own.  It is the twin of
    psl211_alldecks_endpoints and belongs beside it. *)
Definition psl211_dealt_endpoints : instance_endpoints_stmt psl211_dealt_params
  := profile_endpointsE psl211_profile_endpoints.

(** psl211_dealt_observed — the observed execution of the dealer-dealt run:
    it finishes inside its fuel, the verifier collects one endpoint per
    position, and decoding them returns the chirality.  It is the twin of
    psl211_alldecks_observed. *)
Definition psl211_dealt_observed : OE.ObservedExecution :=
  instance_observed psl211_dealt_terminates psl211_dealt_endpoints
    psl211_dealt_recon.

(* Neither definition needs a Require that psl211_models.v does not already
   have: profile_endpointsE is in pgg_instance, psl211_profile_endpoints in
   psl211_endpoints, and the other three run facts in psl211_exec, all three
   of which that file already requires for the all-decks twins.  The model
   family and the programs do NOT belong here: the family needs
   psl211_dealt_sample, which lives in psl211_colour_reading.v, and that file
   requires psl211_models.v, so putting the family here would reverse an
   existing edge.  A file requiring pgg_tableau must not be below the
   manifest either. *)
