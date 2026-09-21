(* Soundness audit scratch, question 3.

   A reading that grants a coalition nothing is an EndpointReading, and a
   program certified at it is a Published value of the framework.  Built
   here over PGL(2,7)'s exact model, from the instance's own witness through
   the post-processing construction, and put beside the instance's real
   exact program: the two publish the SAME manifest path and the SAME
   security property, and differ only in reading_of. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_instance pgg_sample_adapter pgg_interface.
From pgg_smc Require Import pgg_monodromy_profile pgg_collusion_bound.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgl27_tableau_algebraic pgl27_tableau_sampled.
From pgg_smc Require Import pgl27_tableau_analysis_bridged.
From reading_index Require Import k7_k11_tails.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Notation seats :=
  'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1.
Local Notation cards :=
  'I_(pgg_N' (mp_M (instance_profile pgl27_algebra))).+1.

Local Notation r0 := (coalition_endpoint_reading pgl27_algebra).

(* A reading that grants the coalition nothing: every endpoint map is read as
   the constant map at card zero. *)
Definition audit_blind : EndpointReading pgl27_algebra :=
  @MkEndpointReading pgl27_algebra
    (fun _ => [the finType of {ffun seats -> cards}])
    (fun _ _ => [ffun _ => ord0]).

Lemma audit_blind_factors :
  @reading_factors pgl27_algebra r0 audit_blind (fun _ _ => [ffun _ => ord0]).
Proof. by []. Qed.

Definition audit_blind_witness (R : realType) (idx : unit)
  : ExactWitness (amf_sample pgl27_exact_family R idx) audit_blind :=
  exact_witness_postprocessing audit_blind_factors (pgl27_exact_witness R idx).

(* A finished, published program certifying exact independence at a reading
   that grants the coalition nothing.  Same prefix, same statuses as the
   instance's real exact program. *)
Definition audit_blind_published : Published :=
  pgl27_exact_sampled
    certify ExactIndependence of audit_blind by audit_blind_witness
    |> publish StaticExecutedOnly BaselineClassicalOnly.

(* Its manifest path is the real exact program's path, term for term. *)
Lemma audit_blind_pathE :
  published_path audit_blind_published = published_path pgl27_exact_published.
Proof. exact: erefl. Qed.

(* And so is its security property. *)
Lemma audit_blind_propertyE (R : realType) (idx : unit) :
  security_property_of audit_blind_published R idx
  = security_property_of pgl27_exact_published R idx.
Proof. exact: erefl. Qed.

(* The reading is the only coordinate that separates them. *)
Lemma audit_blind_readingE (R : realType) (idx : unit) :
  reading_of audit_blind_published R idx = audit_blind.
Proof. exact: erefl. Qed.

Lemma audit_exact_readingE (R : realType) (idx : unit) :
  reading_of pgl27_exact_published R idx = r0.
Proof. exact: erefl. Qed.

(* What the blind program's proposition says at every coalition below the
   threshold: the coalition's reading is the constant map. *)
Lemma audit_blind_prop_is_constant (R : realType) (idx : unit)
    (C : {set seats})
    (u : sa_sampleT (amf_sample pgl27_exact_family R idx)) :
  @er_of_endpoints pgl27_algebra audit_blind C
    (static_coalition_obs C
       ((amf_sample pgl27_exact_family R idx).(sa_arg) u)
       ((amf_sample pgl27_exact_family R idx).(sa_cut) u))
  = [ffun _ : seats => (ord0 : cards)].
Proof. exact: erefl. Qed.
