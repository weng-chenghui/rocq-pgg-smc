(* Probe B, ledger rows K12, K13 and K14: the twelve-card chirality instance
   at the colour reading.

   K12 gives the colour reading as an EndpointReading and identifies its
   static form with psl211_colour_reading.  K13 builds the Observed and
   Sampled levels over the dealer-dealt run, which the tree does not have,
   and the analysis model family whose sample is psl211_dealt_sample.  K14
   writes the program that certifies exact independence of the colour reading
   and publishes it, and reads the reading and the security property back off
   the published value. *)

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
From pgg_reconstruct Require Import transitivity_privacy design_privacy.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_endpoints.
From pgg_smc Require Import psl211_secrecy psl211_models.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax pgg_tableau_reading.
From pgg_smc Require Import psl211_reading_constancy psl211_colour_reading.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Notation seats :=
  'I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1.
Local Notation cutT := (pgg_gT (mp_M (instance_profile psl211_algebra))).

(******************************************************************************)
(*     K12: the colour reading as a reading of a coalition's endpoints        *)
(******************************************************************************)

(* The colour a coalition sees at each of its positions, as a reading of that
   coalition's endpoints: keep the colour of the card each position holds and
   discard its identity.  It is a function of the endpoints alone, which is
   what psl211_colour_reading_factorsE says and what makes the colour reading
   an instance of this record rather than of the general StaticReading. *)
Definition psl211_colour_endpoint_reading : EndpointReading psl211_algebra :=
  @MkEndpointReading psl211_algebra
    (fun _ => [the finType of {ffun seats -> bool}])
    psl211_colour_of_reading.

(* The value type of the reading is the seat-indexed colour map, at every
   coalition. *)
Lemma psl211_colour_endpoint_readingTE (C : {set seats}) :
  @er_readT psl211_algebra psl211_colour_endpoint_reading C
  = [the finType of {ffun seats -> bool}].
Proof. exact: erefl. Qed.

(* K12: the static form of the endpoint reading is psl211_colour_reading, at
   every coalition, every chirality and every cut.  The proof is
   psl211_colour_reading_factorsE and nothing else. *)
Lemma psl211_colour_endpoint_reading_staticE (C : {set seats})
    (b : ex_inputT psl211_dealt_params) (g : cutT) :
  sr_read (static_reading_of_endpoint_reading psl211_dealt_params
             psl211_colour_endpoint_reading) C b g
  = sr_read psl211_colour_reading C b g.
Proof. exact: (esym (psl211_colour_reading_factorsE C b g)). Qed.

(******************************************************************************)
(*     K13: the dealer-dealt run at Observed and at Sampled                   *)
(******************************************************************************)

(* The endpoint obligation of the dealer-dealt run, read off the profile's own
   abstract-readout equation.  The tree names the terminates and recon facts
   of this run and not this one, which is why no program over the fixed-dealer
   colour model existed; the profile equation quantifies over the content
   readout, so the dealer-dealt mode costs no reduction of its own. *)
Definition psl211_dealt_endpoints : instance_endpoints_stmt psl211_dealt_params
  := profile_endpointsE psl211_profile_endpoints.

(* The observed execution of the dealer-dealt run. *)
Definition psl211_dealt_observed : OE.ObservedExecution :=
  instance_observed psl211_dealt_terminates psl211_dealt_endpoints
    psl211_dealt_recon.

(* The fixed-dealer colour model as an analysis model family: one member per
   prior on the chirality, at every real field.  The index is the prior and
   not the unit type, because the instance's colour theorems hold under every
   prior and the two that refute independence need one giving mass to both
   chiralities. *)
Definition psl211_dealt_family : AnalysisModelFamily psl211_dealt_observed :=
  @MkAnalysisModelFamily psl211_dealt_observed (fun R : realType => R.-fdist bool)
    (fun (R : realType) (secretP : R.-fdist bool) =>
       psl211_dealt_sample secretP).

(* The shared prefix of every program over the dealer-dealt run: the algebra,
   the run parameters, the three run facts and the model family. *)
Definition psl211_dealt_prefix : Tableau Sampled :=
  psl211_algebra dealt fuel psl211_fuel
    execute terminates by psl211_dealt_terminates
            endpoints  by psl211_dealt_endpoints
            recon      by psl211_dealt_recon
    sample psl211_dealt_family.

(* The link lemma the Sampled level proves is about this family, so the two
   readings of a coalition are identified at every prior. *)
Lemma psl211_dealt_prefix_viewE :
  sampled_viewE_prop (sp_f (tableau_at psl211_dealt_prefix)).
Proof. exact: (proj2 (tableau_thm psl211_dealt_prefix)). Qed.

(******************************************************************************)
(*     K14: the colour program                                                *)
(******************************************************************************)

(* The exact-independence witness at the colour reading: the dealt chirality
   as the secret, and, below the threshold of six positions, the independence
   of the coalition's colour reading from it.  The independence is
   psl211_colour_reading_indep, which is the instance's counting argument on
   five positions or fewer read as a privacy statement, transported along the
   factorisation that makes the colour reading a reading of the endpoints. *)
Definition psl211_colour_witness (R : realType) (secretP : R.-fdist bool)
  : ExactWitness (psl211_dealt_sample secretP) psl211_colour_endpoint_reading.
Proof.
apply: (@MkExactWitness R psl211_algebra psl211_dealt_params
  (psl211_dealt_sample secretP) psl211_colour_endpoint_reading bool
  (psl211_secret secretP)).
move=> C HC.
have -> : (fun u => @er_of_endpoints psl211_algebra
             psl211_colour_endpoint_reading C
             (static_coalition_obs C
                ((psl211_dealt_sample secretP).(sa_arg) u)
                ((psl211_dealt_sample secretP).(sa_cut) u)))
        = (fun u => sr_read psl211_colour_reading C
             ((psl211_dealt_sample secretP).(sa_arg) u)
             ((psl211_dealt_sample secretP).(sa_cut) u)).
  by apply: boolp.funext => u; exact: (esym (psl211_colour_reading_factorsE _ _ _)).
exact: psl211_colour_reading_indep HC.
Defined.

(* The colour program: the shared prefix, the witness above at the colour
   reading, and the manifest path.  What the finished program carries about a
   coalition of fewer than six of the twelve positions is independence of the
   dealt chirality FROM THE COLOUR READING, at every real field and every
   prior, with no numeric bound in it.  It says nothing about the
   card-identity reading of the same model, which K15 is about. *)
Definition psl211_colour_published : Published :=
  psl211_dealt_prefix
    certify ExactIndependence of psl211_colour_endpoint_reading
            by psl211_colour_witness
    |> publish StaticExecutedOnly BaselineClassicalOnly.

(* The reading the published program's claim is made at is the colour
   reading, decided by conversion. *)
Lemma psl211_colour_published_readingE (R : realType)
    (secretP : R.-fdist bool) :
  reading_of psl211_colour_published R secretP
  = psl211_colour_endpoint_reading.
Proof. exact: erefl. Qed.

(* And the security property it carries is exact independence. *)
Lemma psl211_colour_published_propertyE (R : realType)
    (secretP : R.-fdist bool) :
  security_property_of psl211_colour_published R secretP
  = ExactIndependenceProperty.
Proof. exact: erefl. Qed.

(* The path the program publishes records the dealer-dealt run, the
   AnalysisBridged level and the family the sample statement named. *)
Lemma psl211_colour_published_pathE :
  published_path psl211_colour_published
  = @MkAnalysisPath psl211_dealt_observed AnalysisBridged psl211_dealt_family
      StaticExecutedOnly BaselineClassicalOnly.
Proof. exact: erefl. Qed.

Print Assumptions psl211_colour_published.
Print Assumptions psl211_colour_published_readingE.
