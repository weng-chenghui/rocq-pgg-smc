(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* landing_draft_framework: the framework text of the landing, compiled       *)
(* before it is written into manifest/pgg_tableau.v. Every declaration below  *)
(* is the production text; only this header is not.                           *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_collusion_bound.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(* ------ beside indistinguishability_tail ---------------------------------- *)

(* The input-indistinguishability proposition at twice a bound on the distance
   from the model's own cut law to a certificate's ideal cut. The two readings
   of the cut law each move by at most that distance when the law is replaced
   by the ideal, and the certificate's fifth field makes the two readings of
   the ideal one law, so the two readings of the cut law lie within the
   distance twice. It is indistinguishability_tail with the number left free:
   that lemma is this one at the certificate's own marginal-bound epsilon,
   reached through ic_close and ic_Hd. Read in the other direction it is what
   makes a lower bound on the two readings' distance a statement about every
   certificate whose ideal sits close to the cut law. *)
Lemma indistinguishability_prop_of_ideal_close (R : realType)
    (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E))
    (cert : IndistinguishabilityCert sa) (eps : R) :
  var_dist (sa_cut_dist sa) (ic_ideal cert) <= eps ->
  IndistinguishabilityPropAt cert (eps + eps).
Proof.
move=> Hc C x x' HC.
have H1 : var_dist (fdistmap (static_coalition_obs C x) (sa_cut_dist sa))
                   (fdistmap (static_coalition_obs C x) (ic_ideal cert))
        <= eps.
  exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) Hc).
have Hconst : fdistmap (static_coalition_obs C x) (ic_ideal cert)
            = fdistmap (static_coalition_obs C x') (ic_ideal cert)
  := @ic_const R A E sa cert C HC x x'.
have H2 : var_dist (fdistmap (static_coalition_obs C x) (ic_ideal cert))
                   (fdistmap (static_coalition_obs C x') (sa_cut_dist sa))
        <= eps.
  rewrite Hconst symmetric_var_dist.
  exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) Hc).
exact: (Order.POrderTheory.le_trans (var_dist_triangle _ _ _) (lerD H1 H2)).
Qed.
Arguments indistinguishability_prop_of_ideal_close {R A E sa} cert eps.

(* ------ new section: An obstruction a program publishes ------------------- *)

(* Input distinguishability at c: some coalition below the privacy threshold
   reads two run arguments of the model's own cut law at least c apart, in the
   sum of absolute differences. It is the quantitative negation of the
   input-indistinguishability proposition, and it mentions no certificate, so
   it is a fact about the model and the coalition's static reading and holds
   or fails whether or not a certificate over the model exists. The attack
   model is a static coalition of fewer than k seats reading its own
   endpoints, and the two run arguments are named rather than drawn, so a
   distinguisher told which two arguments to compare has advantage at least
   half of c there, var_dist being twice the total variation distance of the
   literature. *)
Definition InputDistinguishabilityPropAt (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (c : R) : Prop :=
  exists (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1})
         (x x' : ex_inputT E),
    (#|C| < profile_k (instance_profile A))%N /\
    c <= var_dist (fdistmap (static_coalition_obs C x) (sa_cut_dist sa))
                  (fdistmap (static_coalition_obs C x') (sa_cut_dist sa)).
Arguments InputDistinguishabilityPropAt {R A E} sa c.

(* A model distinguishable at c is distinguishable at every smaller number:
   the same coalition and the same two run arguments witness it. The family is
   downward closed in c, and a model's sharpest statement is at the largest
   number its own readings reach. *)
Lemma input_distinguishability_prop_le (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (c c' : R) :
  c' <= c ->
  InputDistinguishabilityPropAt sa c -> InputDistinguishabilityPropAt sa c'.
Proof.
move=> Hle [C [x [x' [HC Hge]]]].
by exists C, x, x'; split=> //; exact: (Order.POrderTheory.le_trans Hle Hge).
Qed.

(* Every number at which an input-indistinguishability program over a
   distinguishable model states its proposition is at least the number the
   model is distinguishable at. The proposition bounds the distance between
   the readings of every two run arguments, and distinguishability exhibits
   two whose distance is at least c, so c bounds from below what such a
   program can publish, whatever its certificate. *)
Lemma indistinguishability_number_ge_of_input_distinguishability
    (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E))
    (cert : IndistinguishabilityCert sa) (c c' : R) :
  InputDistinguishabilityPropAt sa c ->
  IndistinguishabilityPropAt cert c' -> c <= c'.
Proof.
move=> [C [x [x' [HC Hge]]]] Hprop.
exact: (Order.POrderTheory.le_trans Hge (Hprop C x x' HC)).
Qed.

(* Over a model distinguishable at c, no input-indistinguishability
   certificate has its ideal cut within eps of the model's own cut law once
   eps added to itself stays below c. The law is the model's and not a free
   argument: a certificate's third and fourth fields place its ideal within
   its marginal bound of the cut law the model draws and of no other law. The
   route is indistinguishability_prop_of_ideal_close, which turns closeness of
   the ideal into the proposition at eps twice, against which the number bound
   above is then read. *)
Lemma no_indistinguishability_cert_ideal_close_of_input_distinguishability
    (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E)) (c eps : R) :
  InputDistinguishabilityPropAt sa c -> eps + eps < c ->
  forall cert : IndistinguishabilityCert sa,
    var_dist (sa_cut_dist sa) (ic_ideal cert) <= eps -> False.
Proof.
move=> Hd Heps cert Hc.
have Hge := indistinguishability_number_ge_of_input_distinguishability Hd
  (indistinguishability_prop_of_ideal_close cert eps Hc).
by move: (Order.POrderTheory.le_lt_trans Hge Heps);
   rewrite Order.POrderTheory.ltxx.
Qed.

(* The obstructions a program may publish at one model, one constructor each.
   A constructor of SecurityEvidence names a security property a program
   certifies; a constructor here names a fact about the model that no security
   property follows from, so the two enumerations are disjoint in kind and
   this one leaves SecurityEvidence with its three members. A closed
   enumeration and not a free proposition: a free proposition is what restate
   hands over, and a reader of a free payload cannot tell what kind of fact
   was published. Its one member carries the number the model is
   distinguishable at; a number at or below zero makes the member's own
   proposition hold at every model, var_dist being non-negative. *)
Variant ObstructionKind (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) : Type :=
  | InputDistinguishabilityObstruction of R.

(* The proposition a kind stands for. The constructor selects it, as the
   constructor of SecurityEvidence selects the proposition EvidenceProp gives,
   so a program cannot publish one kind's constructor with another kind's
   proof. *)
Definition ObstructionProp (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (o : ObstructionKind sa) : Prop :=
  match o with
  | InputDistinguishabilityObstruction c => InputDistinguishabilityPropAt sa c
  end.

(* A kind at every real field and every index of a program's model family.
   The security evidence of a program is given at every field and index, and
   an obstruction is given at every field and index for the same reason: the
   model is a family and a statement at one chosen field would describe a
   member and not the model. The kind may differ at each field and each index,
   as ExactPayload and its two companions may, so a reader of a published
   obstruction reads the number off the field and index it asks about. *)
Definition ObstructionPayload (q : StackAt Sampled) : Type :=
  forall (R : realType) (idx : amf_index (sp_f q) R),
    ObstructionKind (amf_sample (sp_f q) R idx).
Arguments ObstructionPayload q : assert.

(* The proposition a payload asserts: its kind's proposition at every real
   field and every index, as BridgedProp is the proposition a program's
   evidence asserts there. *)
Definition ObstructionPayloadProp (q : StackAt Sampled)
    (o : ObstructionPayload q) : Prop :=
  forall (R : realType) (idx : amf_index (sp_f q) R), ObstructionProp (o R idx).
Arguments ObstructionPayloadProp q o : assert.

(* The payload of the terminal below: a kind at every field and index together
   with its proof. The two travel as one term because the terminal carries one
   payload per line. *)
Definition PublishObstructionPayload (q : StackAt Sampled) : Type :=
  { o : ObstructionPayload q & ObstructionPayloadProp o }.
Arguments PublishObstructionPayload q : assert.

(* The two halves written apart, as mk_indistinguishability writes a
   certificate's five components apart: a statement then displays the
   proposition claimed and the proof of it as two named things. *)
Definition mk_obstruction (q : StackAt Sampled) (o : ObstructionPayload q)
    (H : ObstructionPayloadProp o) : PublishObstructionPayload q :=
  existT _ o H.
Arguments mk_obstruction : clear implicits.

(* A program's data at Sampled, the manifest path describing it, the
   obstruction it publishes and two proofs: what the program proved at
   Sampled, and the obstruction. It certifies no security property, its data
   carrying no SecurityEvidence, and it refutes only what its kind names; a
   program over the same model publishing security evidence is untouched by
   it, the two being facts about one model. The path field is constrained by
   neither of the others, as PublishedAt's is not. *)
Record PublishedObstruction := MkPublishedObstruction {
  published_obstruction_at   : StackAt Sampled ;
  published_obstruction_path : AnalysisPath ;
  published_obstruction_kind : ObstructionPayload published_obstruction_at ;
  published_obstruction_thm  : StackProp Sampled published_obstruction_at ;
  published_obstruction_pf   : ObstructionPayloadProp
                                 published_obstruction_kind }.

(* ObstructionPayload, StackProp Sampled and ObstructionPayloadProp all unfold
   to quantified statements, so Unset Strict Implicit takes the record for
   something to infer and the quantifier's own binder steals its slot. *)
Arguments published_obstruction_kind : clear implicits.
Arguments published_obstruction_thm : clear implicits.
Arguments published_obstruction_pf : clear implicits.

(* The terminal of a program that stops at a named model and publishes an
   obstruction there. The path is built from the program's own data: the
   observed execution the program reached, the level AnalysisBridged, the
   model family the sample statement named, and NegativeTransfer, which is not
   a payload because the record's own proposition is the theorem that status
   names. The assumption status is the line's payload, as it is at the two
   terminals below. *)
Definition publish_obstruction (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (p : PublishObstructionPayload q)
    : PublishedObstruction :=
  @MkPublishedObstruction q
    (@MkAnalysisPath (sp_obs q) AnalysisBridged (sp_f q) NegativeTransfer a)
    (projT1 p) pf (projT2 p).

(* The data occurs in the types of the proof and the payload, so Set Implicit
   Arguments would infer it and the bind, which passes the terminal unapplied,
   would have no slot to write it in. *)
Arguments publish_obstruction : clear implicits.

(* The level of such a path is AnalysisBridged. The manifest's own definition
   of that level reads "AnalysisBridged + bridge alias to a named security,
   leakage, mixing or limitation theorem about the same distribution and the
   same observer", and an obstruction is a limitation theorem about the model's
   own cut law and the path's observer. Conversion decides it. *)
Lemma publish_obstruction_completionE (a : AssumptionStatus)
    (q : StackAt Sampled) (pf : StackProp Sampled q)
    (p : PublishObstructionPayload q) :
  ap_completion (published_obstruction_path (publish_obstruction a q pf p))
  = AnalysisBridged.
Proof. exact: erefl. Qed.

(* The transfer status is fixed and not chosen: NegativeTransfer is defined as
   a theorem transporting an obstruction to the path's observer, and the
   record's own proposition is that theorem. *)
Lemma publish_obstruction_transferE (a : AssumptionStatus)
    (q : StackAt Sampled) (pf : StackProp Sampled q)
    (p : PublishObstructionPayload q) :
  ap_transfer (published_obstruction_path (publish_obstruction a q pf p))
  = NegativeTransfer.
Proof. exact: erefl. Qed.

(* The model slot is the family the program's own data carries, so the path
   names the model the obstruction was proved at and not a second family that
   resembles it. *)
Lemma publish_obstruction_modelE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (p : PublishObstructionPayload q) :
  ap_model (published_obstruction_path (publish_obstruction a q pf p))
  = sp_f q.
Proof. exact: erefl. Qed.

(* The observed execution of the path is the run the program made its three
   run facts about. *)
Lemma publish_obstruction_observedE (a : AssumptionStatus)
    (q : StackAt Sampled) (pf : StackProp Sampled q)
    (p : PublishObstructionPayload q) :
  ap_observed (published_obstruction_path (publish_obstruction a q pf p))
  = sp_obs q.
Proof. exact: erefl. Qed.

(* The assumption status of the path is the line's payload, on the same
   footing as at the other three terminals. *)
Lemma publish_obstruction_assumptionsE (a : AssumptionStatus)
    (q : StackAt Sampled) (pf : StackProp Sampled q)
    (p : PublishObstructionPayload q) :
  ap_assumptions (published_obstruction_path (publish_obstruction a q pf p))
  = a.
Proof. exact: erefl. Qed.

(* The obstruction such a value publishes is the one the line wrote, so a
   reader of the value learns which fact was claimed without unfolding the
   terminal. *)
Lemma publish_obstruction_kindE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (o : ObstructionPayload q)
    (H : ObstructionPayloadProp o) :
  published_obstruction_kind
    (publish_obstruction a q pf (mk_obstruction q o H)) = o.
Proof. exact: erefl. Qed.

(* The obstruction of a published program, under the name a reader of a
   refutation expects. It is the whole of what such a value says beyond the
   Sampled level: the five security readers of this file project a BridgedProp
   out of a PublishedAt, and PublishedObstruction is a different inductive
   type, so none of them applies to one. *)
Definition obstruction_of (r : PublishedObstruction)
  : ObstructionPayloadProp (published_obstruction_kind r) :=
  published_obstruction_pf r.
Arguments obstruction_of : clear implicits.

(* Run correctness of such a program, the first of the two conjuncts the
   Sampled level carries. *)
Definition run_correct_of_obstruction (r : PublishedObstruction)
  : oe_correct_prop (sp_obs (published_obstruction_at r)) :=
  proj1 (published_obstruction_thm r).
Arguments run_correct_of_obstruction : clear implicits.

(* The link lemma of such a program, identifying its executed coalition reader
   with the direct computation. It is the fact the obstruction is stated
   beside: the obstruction is about the direct reader, and this is what ties
   that reader to the run. *)
Definition view_identification_of_obstruction (r : PublishedObstruction)
  : sampled_viewE_prop (sp_f (published_obstruction_at r)) :=
  proj2 (published_obstruction_thm r).
Arguments view_identification_of_obstruction : clear implicits.

(* ------ the tail lemma subsumes the tree's own, checked and not landed ---- *)

Lemma draft_tail_of_ideal_close (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IndistinguishabilityCert sa) :
  IndistinguishabilityPropAt cert (cert_eps cert).
Proof.
apply: (indistinguishability_prop_of_ideal_close cert).
have Hd : sw_rho_dist (ic_b cert) = sa_cut_dist sa := ic_Hd cert.
have Hcl := ic_close cert.
by rewrite Hd in Hcl.
Qed.

Print Assumptions indistinguishability_prop_of_ideal_close.
Print Assumptions no_indistinguishability_cert_ideal_close_of_input_distinguishability.
