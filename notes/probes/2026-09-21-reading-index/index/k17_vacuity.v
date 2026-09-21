(* Probe B, ledger row K17: the hypothesis set of K7 to K11 is jointly
   satisfiable.  Every instantiation below is at PGL(2,7) and at the default
   reading, the exact model carrying the exact-independence hypotheses and
   the word model over the same algebra carrying the two that mention a
   certificate. *)

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

Section k17.
Variable R : realType.
Variable secretP : R.-fdist bool.

Local Notation r0 := (coalition_endpoint_reading pgl27_algebra).

(* The exact model of the instance at one real field, and the link lemma the
   Sampled level of the exact program proves about it. *)
Definition k17_exact_sa := amf_sample pgl27_exact_family R tt.

Definition k17_exact_view :
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1},
    @sa_coalition_view R (instance_profile pgl27_algebra)
      (instance_exec pgl27_dealt_params) k17_exact_sa 0 C
    = (fun u => static_coalition_obs C (k17_exact_sa.(sa_arg) u)
                  (k17_exact_sa.(sa_cut) u)) :=
  proj2 (tableau_thm pgl27_exact_sampled) R tt.

(* K7 instantiated: the exact-independence proposition of the instance's own
   witness at the default reading. *)
Definition k17_exact_prop : ExactProp (pgl27_exact_witness R tt) :=
  exact_tail (pgl27_exact_witness R tt) k17_exact_view.

(* K8 instantiated at the word model of the same algebra. *)
Definition k17_indistinguishability_prop :
  IndistinguishabilityPropAt (pgl27_word_cert secretP)
    (cert_eps (pgl27_word_cert secretP)) :=
  indistinguishability_tail (pgl27_word_cert secretP).

(* K9 instantiated at the word model's proximity certificate. *)
Definition k17_word_view :
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1},
    @sa_coalition_view R (instance_profile pgl27_algebra)
      (instance_exec pgl27_dealt_params)
      (amf_sample pgl27_word_family R secretP) 0 C
    = (fun u => static_coalition_obs C
                  ((amf_sample pgl27_word_family R secretP).(sa_arg) u)
                  ((amf_sample pgl27_word_family R secretP).(sa_cut) u)) :=
  proj2 (tableau_thm pgl27_word_sampled) R secretP.

Definition k17_ideal_view :
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1},
    @sa_coalition_view R (instance_profile pgl27_algebra)
      (instance_exec pgl27_dealt_params)
      (ipc_ideal (pgl27_word_proximity_cert secretP)) 0 C
    = (fun u => static_coalition_obs C
         ((ipc_ideal (pgl27_word_proximity_cert secretP)).(sa_arg) u)
         ((ipc_ideal (pgl27_word_proximity_cert secretP)).(sa_cut) u)) :=
  proj2 (tableau_thm pgl27_prior_exact_sampled) R secretP.

Definition k17_idealproximity_prop :
  IdealProximityPropAt (pgl27_word_proximity_cert secretP)
    (ipc_eps (pgl27_word_proximity_cert secretP)) :=
  idealproximity_tail (pgl27_word_proximity_cert secretP) k17_word_view
    k17_ideal_view.

(* K10 instantiated: the word model is input distinguishable at zero, the
   empty coalition and one run argument taken twice witnessing it, so the
   number bound and the exclusion have both their hypotheses inhabited over
   one model.  Zero is the only number this instance supports here, the same
   file proving the model not distinguishable above 2^-39. *)
Lemma k17_distinguishable_at_0 :
  InputDistinguishabilityPropAt (amf_sample pgl27_word_family R secretP) r0 0.
Proof.
exists set0, true, true; split; first by rewrite cards0.
by rewrite var_dist_refl.
Qed.

Definition k17_number_bound :
  0 <= cert_eps (pgl27_word_cert secretP) :=
  indistinguishability_number_ge_of_input_distinguishability
    k17_distinguishable_at_0 k17_indistinguishability_prop.

(* K11 instantiated: the identity factorisation of the default reading
   through itself, and the witness it carries. *)
Lemma k17_identity_factors :
  @reading_factors pgl27_algebra r0 r0 (fun _ v => v).
Proof. by []. Qed.

Definition k17_postprocessed_witness
  : ExactWitness k17_exact_sa r0 :=
  exact_witness_postprocessing k17_identity_factors (pgl27_exact_witness R tt).

Definition k17_postprocessed_prop : ExactProp k17_postprocessed_witness :=
  exact_prop_postprocessing k17_identity_factors (pgl27_exact_witness R tt)
    k17_exact_view.

End k17.

Print Assumptions k17_exact_prop.
