(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* n_framework: a program that publishes an obstruction (probe)               *)
(*                                                                            *)
(* Probe for notes/20260921-refutations-probe-design.md, ledger rows N1, N2   *)
(* and N5. Nothing here is production text.                                   *)
(*                                                                            *)
(* A Tableau program certifies a security property with security evidence,    *)
(* and the manifest records the path it describes. The tree also proves       *)
(* theorems saying that a security property is NOT reachable at a model, and  *)
(* no program and no path says one. This file carries the framework half of   *)
(* saying it: a named family of propositions each denying something a         *)
(* security property's evidence would need, a record beside PublishedAt       *)
(* holding a program's data at Sampled with such a proposition and its        *)
(* proof, and a terminal building that record from a program.                 *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_weighted_words.
From pgg_smc Require Import pgg_observed_execution pgg_sample_adapter.
From pgg_smc Require Import pgg_collusion_bound pgg_analysis_status.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import pgg_instance pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     N1: the first obstruction proposition                                  *)
(******************************************************************************)

(** NoIndistinguishabilityCertNear sa U eps — over the model sa, no
    input-indistinguishability certificate has its ideal cut within eps of the
    law U, the distance taken as the sum of absolute differences. It denies a
    class of certificates and not the input-indistinguishability proposition:
    a certificate whose ideal sits further from U than eps is untouched, and
    so is the proposition IndistinguishabilityPropAt at some number, which
    could still hold by a route this record does not describe. *)
Definition NoIndistinguishabilityCertNear (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (U : R.-fdist (pgg_gT (mp_M (instance_profile A)))) (eps : R) : Prop :=
  forall cert : IndistinguishabilityCert sa,
    var_dist U (ic_ideal cert) <= eps -> False.

(* The conclusion delta-reduces to a dependent product, so Unset Strict
   Implicit takes the adapter for something to infer and the product's own
   binder steals its slot; the directive pins the three carrier arguments
   implicit and the three written ones explicit. *)
Arguments NoIndistinguishabilityCertNear {R A E} sa U eps.

(** Denying the certificates near U at eps denies those near U at any smaller
    number: the class shrinks with eps, so the sharpest statement is the one
    at the largest eps a model admits. *)
Lemma no_indistinguishability_cert_near_le (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (U : R.-fdist (pgg_gT (mp_M (instance_profile A)))) (eps eps' : R) :
  eps' <= eps ->
  NoIndistinguishabilityCertNear sa U eps ->
  NoIndistinguishabilityCertNear sa U eps'.
Proof.
move=> Hle H cert Hc.
exact: (H cert (Order.POrderTheory.le_trans Hc Hle)).
Qed.

(******************************************************************************)
(*     N2: the route from a refuted constancy to the obstruction              *)
(******************************************************************************)

(** A law on cuts that no coalition below the threshold reads the same way at
    every run argument is the ideal cut of no certificate, the constancy being
    the certificate's fifth field read at its own ideal. Refuting the
    constancy at every law within eps of U therefore denies the whole class of
    certificates near U, which is the obstruction above.

    The hypothesis is written out rather than named because the standalone
    form coalition_reading_constancy sits above this file, in
    instances/psl211/psl211_reading_constancy.v; the two are the same
    proposition by delta, and n_psl211.v states that identity. *)
Lemma no_indistinguishability_cert_nearP (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (U : R.-fdist (pgg_gT (mp_M (instance_profile A)))) (eps : R) :
  (forall ideal : R.-fdist (pgg_gT (mp_M (instance_profile A))),
     var_dist U ideal <= eps ->
     ~ (forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
          (#|C| < profile_k (instance_profile A))%N ->
          forall x x' : ex_inputT E,
            fdistmap (static_coalition_obs C x) ideal
            = fdistmap (static_coalition_obs C x') ideal)) ->
  NoIndistinguishabilityCertNear sa U eps.
Proof.
move=> H cert Hc.
exact: (H (ic_ideal cert) Hc (@ic_const R A E sa cert)).
Qed.

(******************************************************************************)
(*     N5: the named family, the record and the terminal                      *)
(******************************************************************************)

(** The obstruction propositions a program may publish at one model, one
    constructor each. A constructor of SecurityEvidence names a security
    property a program certifies; a constructor here names a security
    property's route the model refuses, so the two enumerations are disjoint
    in kind and this one adds nothing to SecurityEvidence. *)
Variant ObstructionKind (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) : Type :=
  | NoCertificateNear of R.-fdist (pgg_gT (mp_M (instance_profile A))) & R.

(** The proposition a kind stands for. The constructor selects it, as the
    constructor of SecurityEvidence selects the proposition EvidenceProp
    gives, so a program cannot publish one kind's constructor with another
    kind's proof. *)
Definition ObstructionProp (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (o : ObstructionKind sa) : Prop :=
  match o with
  | NoCertificateNear U eps => NoIndistinguishabilityCertNear sa U eps
  end.

(** A kind at every real field and every index of a program's model family.
    The evidence of a program is given at every field and index, and an
    obstruction is denied at every field and index for the same reason: the
    model is a family and a statement at one chosen field would describe a
    member and not the model. *)
Definition ObstructionPayload (q : StackAt Sampled) : Type :=
  forall (R : realType) (idx : amf_index (sp_f q) R),
    ObstructionKind (amf_sample (sp_f q) R idx).
Arguments ObstructionPayload q : assert.

(** What such a payload asserts: its proposition at every field and index. *)
Definition ObstructionPropOf (q : StackAt Sampled) (o : ObstructionPayload q)
    : Prop :=
  forall (R : realType) (idx : amf_index (sp_f q) R), ObstructionProp (o R idx).
Arguments ObstructionPropOf q o : assert.

(** The payload of the terminal below: a kind at every field and index
    together with its proof. The two travel as one term because the terminal
    carries one payload per line. *)
Definition RefutePayload (q : StackAt Sampled) : Type :=
  { o : ObstructionPayload q & ObstructionPropOf o }.
Arguments RefutePayload q : assert.

(** The two halves written apart, as mk_indistinguishability writes a
    certificate's five components apart: a statement then displays the
    proposition claimed and the proof of it as two named things. *)
Definition mk_obstruction (q : StackAt Sampled) (o : ObstructionPayload q)
    (H : ObstructionPropOf o) : RefutePayload q := existT _ o H.
Arguments mk_obstruction : clear implicits.

(** A program's data at Sampled, the manifest path describing it, the
    obstruction it publishes and the two proofs: what the program proved at
    Sampled, and the obstruction. It certifies no security property, its data
    carrying no SecurityEvidence, and it refutes only the class its kind
    names; a program over the same model publishing security evidence is
    untouched by it, the two being facts about one model that do not
    conflict. *)
Record PublishedObstruction := MkPublishedObstruction {
  published_obstruction_at   : StackAt Sampled ;
  published_obstruction_path : AnalysisPath ;
  published_obstruction_kind : ObstructionPayload published_obstruction_at ;
  published_obstruction_thm  : StackProp Sampled published_obstruction_at ;
  published_obstruction_pf   : ObstructionPropOf published_obstruction_kind }.

(* ObstructionPayload, StackProp Sampled and ObstructionPropOf all unfold to
   quantified statements, so Unset Strict Implicit takes the record for
   something to infer and the quantifier's own binder steals its slot. *)
Arguments published_obstruction_kind : clear implicits.
Arguments published_obstruction_thm : clear implicits.
Arguments published_obstruction_pf : clear implicits.

(** The terminal of a program that stops at a named model and publishes an
    obstruction there. The path is built from the program's own data: the
    observed execution the program reached, the level AnalysisBridged, the
    model family the sample statement named, and NegativeTransfer, which is
    not a payload because the record's own proposition is the obstruction the
    status names. The assumption status is the line's payload, as it is at the
    two terminals below. *)
Definition refute (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (p : RefutePayload q) : PublishedObstruction :=
  @MkPublishedObstruction q
    (@MkAnalysisPath (sp_obs q) AnalysisBridged (sp_f q) NegativeTransfer a)
    (projT1 p) pf (projT2 p).

(* The data occurs in the types of the proof and the payload, so Set Implicit
   Arguments would infer it and the bind, which passes the terminal unapplied,
   would have no slot to write it in. *)
Arguments refute : clear implicits.

(** The level of such a path is AnalysisBridged: the record's proposition is a
    theorem about the model's distribution and the path's observer, which is
    what that level records. Conversion decides it. *)
Lemma refute_completionE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (p : RefutePayload q) :
  ap_completion (published_obstruction_path (refute a q pf p))
  = AnalysisBridged.
Proof. exact: erefl. Qed.

(** The transfer status is fixed and not chosen: the theorem the record
    carries transports an obstruction to the path's observer, which is what
    NegativeTransfer names. *)
Lemma refute_transferE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (p : RefutePayload q) :
  ap_transfer (published_obstruction_path (refute a q pf p))
  = NegativeTransfer.
Proof. exact: erefl. Qed.

(** The model slot is the family the program's own data carries, so the path
    names the model the obstruction was proved at. *)
Lemma refute_modelE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (p : RefutePayload q) :
  ap_model (published_obstruction_path (refute a q pf p)) = sp_f q.
Proof. exact: erefl. Qed.

(** The observed execution of the path is the run the program made its three
    run facts about. *)
Lemma refute_observedE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (p : RefutePayload q) :
  ap_observed (published_obstruction_path (refute a q pf p)) = sp_obs q.
Proof. exact: erefl. Qed.

(** The assumption status of the path is the line's payload. *)
Lemma refute_assumptionsE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (p : RefutePayload q) :
  ap_assumptions (published_obstruction_path (refute a q pf p)) = a.
Proof. exact: erefl. Qed.

(** The kind such a value publishes is the one the line wrote. *)
Lemma refute_kindE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (o : ObstructionPayload q)
    (H : ObstructionPropOf o) :
  published_obstruction_kind (refute a q pf (mk_obstruction q o H)) = o.
Proof. exact: erefl. Qed.

(** The obstruction of a published program, under the name a reader of a
    refutation expects. It is the whole security content of such a value: no
    security reader of manifest/pgg_tableau.v applies to it, those readers
    projecting a BridgedProp out of a PublishedAt. *)
Definition obstruction_of (r : PublishedObstruction)
  : ObstructionPropOf (published_obstruction_kind r) :=
  published_obstruction_pf r.
Arguments obstruction_of : clear implicits.

(** Run correctness of such a program, the first of the two conjuncts the
    Sampled level carries. *)
Definition run_correct_of_obstruction (r : PublishedObstruction)
  : oe_correct_prop (sp_obs (published_obstruction_at r)) :=
  proj1 (published_obstruction_thm r).
Arguments run_correct_of_obstruction : clear implicits.

(** The link lemma of such a program, identifying its executed coalition
    reader with the direct computation. It is the fact the obstruction is
    stated alongside: the obstruction is about the direct reader and this is
    what ties that reader to the run. *)
Definition view_identification_of_obstruction (r : PublishedObstruction)
  : sampled_viewE_prop (sp_f (published_obstruction_at r)) :=
  proj2 (published_obstruction_thm r).
Arguments view_identification_of_obstruction : clear implicits.
