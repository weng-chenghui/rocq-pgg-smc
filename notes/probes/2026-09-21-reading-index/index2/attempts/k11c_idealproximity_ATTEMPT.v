(* DOES NOT COMPILE.  Probe B round 2, the ideal-proximity half of K11 by
   the certificate route.  Kept as the record of the attempt.
   rc=1 at line 220: "Cannot apply lemma
   (MkIdealProximityCert (ipc_eps:=ipc_eps cert))".  The four field
   arguments are given to @MkIdealProximityCert and ipc_close is left as
   the goal; what the application will not accept is the third field,
   ipc_secret, whose type asks for ew_secretT of the NEW witness
   exact_witness_postprocessing Hf (ipc_witness cert) where the term
   given has ew_secretT of the old one.  The two are equal by one iota
   step through the record the construction builds, so the next attempt
   should build the witness by a Definition with an explicit
   @MkExactWitness rather than by apply/Defined, or state the field type
   with an explicit cast.  index2/k7_k11_tails.v is the round-1 file,
   which compiles; this one is not on the compile path. *)

(* Probe B, ledger rows K7 to K11: the three composition laws at a free
   reading, the number bound and the exclusion at a free reading with the
   same reading on both sides, and post-processing along a factorisation of
   readings.

   K7, K8 and K9 are discharged inside the staged framework itself, where
   exact_tail, indistinguishability_tail and idealproximity_tail are now
   stated at a free reading; the Check lines below record their types.  K10's
   two lemmas are there too; what is here is the mutation that pairs an
   obstruction at one reading with a certificate at another.  K11 is new
   mathematics and is proved here. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import pgg_leakage_witness pgg_trace_secrecy.
From pgg_reconstruct Require Import algebraic_rigidity pgg_sharing_framework.
From pgg_smc Require Import pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     K7, K8, K9: the three composition laws at a free reading               *)
(******************************************************************************)

Check @exact_tail :
  forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
         (sa : SampleAdapter R (instance_exec E)) (r : EndpointReading A)
         (w : ExactWitness sa r),
    (forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
       @sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C
       = (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u))) ->
    ExactProp w.

Check @indistinguishability_tail :
  forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
         (sa : SampleAdapter R (instance_exec E)) (r : EndpointReading A)
         (cert : IndistinguishabilityCert sa r),
    IndistinguishabilityPropAt cert (cert_eps cert).

Check @idealproximity_tail :
  forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
         (sa : SampleAdapter R (instance_exec E)) (r : EndpointReading A)
         (cert : IdealProximityCert sa r),
    (forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
       @sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C
       = (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u))) ->
    (forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
       @sa_coalition_view R (instance_profile A) (instance_exec E)
         (ipc_ideal cert) 0 C
       = (fun u => static_coalition_obs C ((ipc_ideal cert).(sa_arg) u)
                     ((ipc_ideal cert).(sa_cut) u))) ->
    IdealProximityPropAt cert (ipc_eps cert).

(******************************************************************************)
(*     K10: the number bound and the exclusion, at a free reading             *)
(******************************************************************************)

Check @indistinguishability_number_ge_of_input_distinguishability :
  forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
         (sa : SampleAdapter R (instance_exec E)) (r : EndpointReading A)
         (cert : IndistinguishabilityCert sa r) (c c' : R),
    InputDistinguishabilityPropAt sa r c ->
    IndistinguishabilityPropAt cert c' -> c <= c'.

Check @no_indistinguishability_cert_ideal_close_of_input_distinguishability :
  forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
         (sa : SampleAdapter R (instance_exec E)) (r : EndpointReading A)
         (c eps : R),
    InputDistinguishabilityPropAt sa r c -> eps + eps < c ->
    forall cert : IndistinguishabilityCert sa r,
      var_dist (sa_cut_dist sa) (ic_ideal cert) <= eps -> False.

Section k7_k11.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.

(* The mutation of K10: the same statement with the obstruction at one
   reading and the certificate at another.  It typechecks, both sides being
   propositions, and it has no proof: the number bound reads the two
   propositions at one coalition and one pair of run arguments, and at two
   readings they are about two different pushforwards. *)
Fail Definition k10_mutation (r r' : EndpointReading A)
    (cert : IndistinguishabilityCert sa r') (c c' : R)
    (Hd : InputDistinguishabilityPropAt sa r c)
    (Hp : IndistinguishabilityPropAt cert c') : c <= c' :=
  let: ex_intro C (ex_intro x (ex_intro x' (conj HC Hge))) := Hd in
  Order.POrderTheory.le_trans Hge (Hp C x x' HC).

(******************************************************************************)
(*     K11: post-processing along a factorisation of readings                 *)
(******************************************************************************)

(* A reading r' factors through a reading r when a coalitionwise map sends
   what r grants to what r' grants.  It is the hypothesis of the data
   processing inequality, stated on the readings rather than on one model, so
   a factorisation proved once serves every model of the instance. *)
Definition reading_factors (r r' : EndpointReading A)
    (f : forall C : {set seats}, @er_readT A r C -> @er_readT A r' C) : Prop :=
  forall (C : {set seats})
         (v : {ffun seats -> 'I_(pgg_N' (mp_M (instance_profile A))).+1}),
    @er_of_endpoints A r' C v = f C (@er_of_endpoints A r C v).

(* K11, input indistinguishability: the number a program publishes about a
   reading is published about every coarser reading.  This is the data
   processing inequality for the sum of absolute differences.  A coarser
   reading can only help the designer, which is invariant 4 of the spec for
   this property. *)
Lemma reading_indistinguishability_postprocessing_at
    (r r' : EndpointReading A)
    (f : forall C : {set seats}, @er_readT A r C -> @er_readT A r' C)
    (Hf : reading_factors f) (c : R) :
  IndistinguishabilityPropAtReading sa r c ->
  IndistinguishabilityPropAtReading sa r' c.
Proof.
move=> H C x x' HC.
(* a repeat rewrite with fdistmap_comp does not terminate here: its left side
   matches the image of any reading, so the second pass unifies the reading
   itself with a composition.  Each side is rewritten once, at its own
   instance *)
have Hlaw : forall y : ex_inputT E,
    fdistmap (fun g => @er_of_endpoints A r' C (static_coalition_obs C y g))
      (sa_cut_dist sa)
    = fdistmap (f C)
        (fdistmap (fun g => @er_of_endpoints A r C
                              (static_coalition_obs C y g)) (sa_cut_dist sa)).
  move=> y.
  have -> : (fun g => @er_of_endpoints A r' C (static_coalition_obs C y g))
          = (f C) \o (fun g => @er_of_endpoints A r C
                                 (static_coalition_obs C y g)).
    by apply: boolp.funext => g; exact: Hf.
  by rewrite fdistmap_comp.
rewrite (Hlaw x) (Hlaw x').
apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)).
exact: H.
Qed.

(* K11, exact independence: an exact-independence witness at a reading is an
   exact-independence witness at every reading that factors through it, at
   the same secret.  It is the fourth conjunct of ExactProp read as a
   construction rather than as a consequence, and the implication runs from
   the finer reading to the coarser one only. *)
Definition exact_witness_postprocessing (r r' : EndpointReading A)
    (f : forall C : {set seats}, @er_readT A r C -> @er_readT A r' C)
    (Hf : reading_factors f) (w : ExactWitness sa r) : ExactWitness sa r'.
Proof.
apply: (@MkExactWitness R A E sa r' (ew_secretT w) (ew_secret w)).
move=> C HC.
(* the composition notation `o leaves the distribution of its right factor to
   be inferred, and a bare equation between two functions does not fix it, so
   the composition is written out and the view lemma applied to the result *)
have H0 := pgg_trace_secrecy.inde_RV_comp (f C) (@ew_indep _ _ _ _ _ w C HC).
have -> : (fun u => @er_of_endpoints A r' C
                      (static_coalition_obs C (sa.(sa_arg) u)
                         (sa.(sa_cut) u)))
        = (fun u => f C (@er_of_endpoints A r C
                           (static_coalition_obs C (sa.(sa_arg) u)
                              (sa.(sa_cut) u)))).
  by apply: boolp.funext => u; exact: Hf.
exact: H0.
Defined.

(* The secret is untouched by the construction, so the two witnesses are
   witnesses about one secret and not about two. *)
Lemma exact_witness_postprocessing_secretE (r r' : EndpointReading A)
    (f : forall C : {set seats}, @er_readT A r C -> @er_readT A r' C)
    (Hf : reading_factors f) (w : ExactWitness sa r) :
  ew_secret (exact_witness_postprocessing Hf w) = ew_secret w.
Proof. exact: erefl. Qed.

(* And the framework's exact-independence proposition at the coarser reading
   follows, along the link lemma of the Sampled level. *)
Corollary exact_prop_postprocessing (r r' : EndpointReading A)
    (f : forall C : {set seats}, @er_readT A r C -> @er_readT A r' C)
    (Hf : reading_factors f) (w : ExactWitness sa r)
    (Hview : forall C : {set seats},
       @sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C
       = (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u))) :
  ExactProp (exact_witness_postprocessing Hf w).
Proof. exact: exact_tail (exact_witness_postprocessing Hf w) Hview. Qed.

(* K11, ideal proximity: the distance to the ideal model's product law is
   published about every coarser reading, at the same number.  The map
   applied on both sides carries the reading and leaves the secret alone,
   which is why the product on the right stays a product. *)
(* K11, ideal proximity: a proximity certificate at a reading is a proximity
   certificate at every reading that factors through it, at the SAME number
   and against the same ideal model.  The route is the certificate and not
   the free-reading proposition: on the certificate both sides of ipc_close
   are joint laws of a reading with a secret, both are images of the ones at
   the finer reading under the map that carries the reading and leaves the
   secret alone, and one data processing step closes it.  On the free-reading
   proposition the right side is a product of two marginals and the step
   would need a lemma pushing a map through a product, which infotheo does
   not appear to carry. *)
Definition idealproximity_cert_postprocessing (r r' : EndpointReading A)
    (f : forall C : {set seats}, @er_readT A r C -> @er_readT A r' C)
    (Hf : reading_factors f) (cert : IdealProximityCert sa r)
  : IdealProximityCert sa r'.
Proof.
apply: (@MkIdealProximityCert R A E sa r' (ipc_ideal cert)
  (exact_witness_postprocessing Hf (ipc_witness cert))
  (ipc_secret cert) (ipc_eps cert)).
move=> C HC.
pose F := fun p : (@er_readT A r C * ew_secretT (ipc_witness cert))%type =>
            (f C p.1, p.2).
have HL : forall (sb : SampleAdapter R (instance_exec E))
                 (sec : {RV (sa_sampleP sb) -> ew_secretT (ipc_witness cert)}),
    fdistmap (fun u => (@er_of_endpoints A r' C
                (static_coalition_obs C (sb.(sa_arg) u) (sb.(sa_cut) u)),
              sec u)) (sa_sampleP sb)
    = fdistmap F (fdistmap (fun u => (@er_of_endpoints A r C
                (static_coalition_obs C (sb.(sa_arg) u) (sb.(sa_cut) u)),
              sec u)) (sa_sampleP sb)).
  move=> sb sec.
  have -> : (fun u => (@er_of_endpoints A r' C
               (static_coalition_obs C (sb.(sa_arg) u) (sb.(sa_cut) u)),
             sec u))
          = F \o (fun u => (@er_of_endpoints A r C
               (static_coalition_obs C (sb.(sa_arg) u) (sb.(sa_cut) u)),
             sec u)).
    by apply: boolp.funext => u; rewrite /F /=; congr pair; exact: Hf.
  by rewrite fdistmap_comp.
rewrite (HL sa (ipc_secret cert))
        (HL (ipc_ideal cert) (ew_secret (ipc_witness cert))).
exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)
          (@ipc_close _ _ _ _ _ cert C HC)).
Defined.

(* The ideal model, the secret and the number are untouched by the
   construction, so the coarser certificate measures the same two models
   against each other at the same number. *)
Lemma idealproximity_cert_postprocessing_epsE (r r' : EndpointReading A)
    (f : forall C : {set seats}, @er_readT A r C -> @er_readT A r' C)
    (Hf : reading_factors f) (cert : IdealProximityCert sa r) :
  ipc_eps (idealproximity_cert_postprocessing Hf cert) = ipc_eps cert.
Proof. exact: erefl. Qed.

Lemma idealproximity_cert_postprocessing_idealE (r r' : EndpointReading A)
    (f : forall C : {set seats}, @er_readT A r C -> @er_readT A r' C)
    (Hf : reading_factors f) (cert : IdealProximityCert sa r) :
  ipc_ideal (idealproximity_cert_postprocessing Hf cert) = ipc_ideal cert.
Proof. exact: erefl. Qed.

(* And the framework's ideal-proximity proposition at the coarser reading
   follows, at the same number, along the two link lemmas. *)
Corollary idealproximity_prop_postprocessing (r r' : EndpointReading A)
    (f : forall C : {set seats}, @er_readT A r C -> @er_readT A r' C)
    (Hf : reading_factors f) (cert : IdealProximityCert sa r)
    (Hview : forall C : {set seats},
       @sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C
       = (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u)))
    (Hideal : forall C : {set seats},
       @sa_coalition_view R (instance_profile A) (instance_exec E)
         (ipc_ideal cert) 0 C
       = (fun u => static_coalition_obs C ((ipc_ideal cert).(sa_arg) u)
                     ((ipc_ideal cert).(sa_cut) u))) :
  IdealProximityPropAt (idealproximity_cert_postprocessing Hf cert)
    (ipc_eps cert).
Proof.
exact: (idealproximity_tail (idealproximity_cert_postprocessing Hf cert)
          Hview Hideal).
Qed.

End k7_k11.
