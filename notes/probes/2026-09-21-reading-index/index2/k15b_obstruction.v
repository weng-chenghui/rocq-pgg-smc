(* Probe B round 2, K15 part b: the obstruction program over the
   fixed-dealer model, on top of the distinguishability lemma of
   k15a_distinguishable.v.  Split from it so that the cost of each half is
   its own measurement. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec.
From pgg_smc Require Import psl211_secrecy psl211_models.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax pgg_tableau_reading.
From pgg_smc Require Import psl211_reading_constancy psl211_colour_reading.
From reading_index Require Import k12_k14_psl211.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

From reading_index Require Import k15a_distinguishable.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(* The number is above zero, the shuffle group being non-empty. *)
Lemma psl211_dealt_distinguishing_number_gt0 (R : realType) :
  0 < ((#|pgg_G psl211_M|%:R)^-1 : R).
Proof. by rewrite invr_gt0 ltr0n; exact: psl211_G_pos. Qed.

(******************************************************************************)
(*     The obstruction the fixed-dealer model publishes                       *)
(******************************************************************************)

(* The obstruction at every real field and every prior on the chirality: the
   model is input distinguishable, at the coalition's own endpoint reading,
   at one cut's mass.  The reading is written into the kind, so the
   obstruction refutes certificates at that reading and says nothing about
   the colour reading, where psl211_colour_published certifies exact
   independence over the same model.  The two programs are the pair the
   whole design exists for. *)
Definition psl211_dealt_obstruction
  : ObstructionPayload (tableau_at psl211_dealt_prefix) :=
  fun (R : realType) (secretP : R.-fdist bool) =>
    @InputDistinguishabilityObstruction R psl211_algebra psl211_dealt_params
      (amf_sample psl211_dealt_family R secretP)
      (coalition_endpoint_reading psl211_algebra)
      ((#|pgg_G psl211_M|%:R)^-1).

Lemma psl211_dealt_obstruction_prop :
  ObstructionPayloadProp psl211_dealt_obstruction.
Proof.
move=> R secretP; split; first exact: psl211_dealt_distinguishing_number_gt0.
exact: psl211_dealt_input_distinguishable.
Qed.

(* The obstruction program over the fixed-dealer model. *)
Definition psl211_dealt_obstruction_published : PublishedObstruction :=
  psl211_dealt_prefix
    |> publish Obstruction psl211_dealt_obstruction
       by psl211_dealt_obstruction_prop BaselineClassicalOnly.

Lemma psl211_dealt_obstruction_published_kindE :
  published_obstruction_kind psl211_dealt_obstruction_published
  = psl211_dealt_obstruction.
Proof. exact: erefl. Qed.

(* Over this model no input-indistinguishability certificate at the
   coalition's own endpoint reading has its ideal cut within eps of the
   model's own cut law once eps added to itself stays below one cut's mass.
   It is the framework's exclusion lemma read at this obstruction. *)
Corollary psl211_dealt_no_close_ideal (R : realType) (secretP : R.-fdist bool)
    (eps : R) :
  eps + eps < (#|pgg_G psl211_M|%:R)^-1 ->
  forall cert : IndistinguishabilityCert (psl211_dealt_sample secretP)
                  (coalition_endpoint_reading psl211_algebra),
    var_dist (sa_cut_dist (psl211_dealt_sample secretP)) (ic_ideal cert)
    <= eps -> False.
Proof.
exact: no_indistinguishability_cert_ideal_close_of_input_distinguishability
  (psl211_dealt_input_distinguishable secretP).
Qed.

