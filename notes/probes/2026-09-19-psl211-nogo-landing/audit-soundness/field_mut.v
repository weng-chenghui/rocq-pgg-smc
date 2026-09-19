(* Audit probe for N2: is coalition_reading_constancy the type of the fifth
   field sc_const of SpectralCert, with the same quantifier order and the same
   carrier, and does a change of the record break the projection lemma?
   The definition below is copied verbatim from the landing copy of
   psl211_spectral_nogo.v. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import design_privacy algebraic_rigidity.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Import Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Definition coalition_reading_constancy (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A)
    (ideal : R.-fdist (pgg_gT (mp_M (instance_profile A)))) : Prop :=
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| < profile_k (instance_profile A))%N ->
    forall x x' : ex_inputT E,
      fdistmap (@static_coalition_obs A E C x) ideal
      = fdistmap (@static_coalition_obs A E C x') ideal.

(* Positive control: the landing lemma, in term form. *)
Definition control (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : SpectralCert sa) : coalition_reading_constancy E (sc_ideal cert)
  := sc_const cert.

(* And the converse direction: the field's type is no stronger than the
   restatement, so the two are the same proposition and not merely one
   implying the other. *)
Definition control_back (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : SpectralCert sa)
    (H : coalition_reading_constancy E (sc_ideal cert)) :
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| < profile_k (instance_profile A))%N ->
    forall x x' : ex_inputT E,
      fdistmap (static_coalition_obs C x) (sc_ideal cert)
      = fdistmap (static_coalition_obs C x') (sc_ideal cert)
  := H.

(* M1: the coalition-size premise dropped. *)
Definition crc_m1 (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (ideal : R.-fdist (pgg_gT (mp_M (instance_profile A)))) : Prop :=
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    forall x x' : ex_inputT E,
      fdistmap (@static_coalition_obs A E C x) ideal
      = fdistmap (@static_coalition_obs A E C x') ideal.

Fail Definition m1 (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : SpectralCert sa) : crc_m1 E (sc_ideal cert) := sc_const cert.

(* M2: the two run arguments' roles swapped. *)
Definition crc_m2 (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (ideal : R.-fdist (pgg_gT (mp_M (instance_profile A)))) : Prop :=
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| < profile_k (instance_profile A))%N ->
    forall x x' : ex_inputT E,
      fdistmap (@static_coalition_obs A E C x') ideal
      = fdistmap (@static_coalition_obs A E C x) ideal.

Fail Definition m2 (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : SpectralCert sa) : crc_m2 E (sc_ideal cert) := sc_const cert.

(* M3: the threshold relaxed from < to <=. *)
Definition crc_m3 (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (ideal : R.-fdist (pgg_gT (mp_M (instance_profile A)))) : Prop :=
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| <= profile_k (instance_profile A))%N ->
    forall x x' : ex_inputT E,
      fdistmap (@static_coalition_obs A E C x) ideal
      = fdistmap (@static_coalition_obs A E C x') ideal.

Fail Definition m3 (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : SpectralCert sa) : crc_m3 E (sc_ideal cert) := sc_const cert.

(* M4: the restatement read at the adapter's cut instead of the certificate's
   own ideal, which is the law the certificate says nothing constant about. *)
Fail Definition m4 (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : SpectralCert sa) : coalition_reading_constancy E (sa_cut_dist sa)
  := sc_const cert.

(* The certificate's published number, for the word-form check. *)
Lemma cert_epsE (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E)) (cert : SpectralCert sa) :
  cert_eps cert = sw_bound_eps (sc_b cert) + sw_bound_eps (sc_b cert).
Proof. by []. Qed.

Print Assumptions control.
