(* Soundness audit scratch.  Two questions the probe left open.

   S-a: is distinguishability monotone in the reading, in the direction
   opposite to post-processing?  If r' factors through r, an obstruction at
   r' (the coarser reading) is an obstruction at r (the finer one).

   S-b: is a certified program at a reading that grants nothing vacuous?
   Build an ExactWitness at the blind reading over an ARBITRARY model and an
   ARBITRARY secret, with no hypothesis. *)

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
From reading_index Require Import k7_k11_tails.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section audit.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.
Local Notation cards := 'I_(pgg_N' (mp_M (instance_profile A))).+1.

(* S-a.  The obstruction direction of post-processing. *)
Lemma audit_input_distinguishability_finer
    (r r' : EndpointReading A)
    (f : forall C : {set seats}, @er_readT A r C -> @er_readT A r' C)
    (Hf : @reading_factors A r r' f) (c : R) :
  InputDistinguishabilityPropAt sa r' c -> InputDistinguishabilityPropAt sa r c.
Proof.
move=> [C [x [x' [HC Hge]]]]; exists C, x, x'; split=> //.
apply: (Order.POrderTheory.le_trans Hge).
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
by rewrite (Hlaw x) (Hlaw x'); exact: var_dist_fdistmap.
Qed.

(* Every endpoint reading factors through the identity one, so the identity
   reading is the finest and an obstruction at any reading is an obstruction
   at it. *)
Lemma audit_every_reading_factors_through_identity (r : EndpointReading A) :
  @reading_factors A (coalition_endpoint_reading A) r (@er_of_endpoints A r).
Proof. by []. Qed.

Lemma audit_input_distinguishability_at_identity (r : EndpointReading A)
    (c : R) :
  InputDistinguishabilityPropAt sa r c ->
  InputDistinguishabilityPropAt sa (coalition_endpoint_reading A) c.
Proof.
exact: (audit_input_distinguishability_finer
          (audit_every_reading_factors_through_identity r)).
Qed.

(* The cross-reading number bound the K10 mutation is said to exclude.  An
   obstruction at the coarser reading and a certificate at the finer one do
   bound each other, so a failing proof term at two unrelated readings is not
   evidence that no cross-reading bound exists. *)
Lemma audit_number_ge_across_readings
    (r r' : EndpointReading A)
    (f : forall C : {set seats}, @er_readT A r C -> @er_readT A r' C)
    (Hf : @reading_factors A r r' f)
    (cert : IndistinguishabilityCert sa r) (c c' : R) :
  InputDistinguishabilityPropAt sa r' c ->
  IndistinguishabilityPropAt cert c' -> c <= c'.
Proof.
move=> [C [x [x' [HC Hge]]]] Hp.
have Hp' := reading_indistinguishability_postprocessing_at Hf Hp.
exact: (Order.POrderTheory.le_trans Hge (Hp' C x x' HC)).
Qed.

End audit.
