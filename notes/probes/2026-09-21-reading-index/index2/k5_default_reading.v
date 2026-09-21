(* Probe B of notes/20260921-reading-index-and-surface-prepositions-probe-design.md
   Ledger row K5: at the default (identity) endpoint reading the four
   propositions of the framework are CONVERTIBLE with today's.

   Today's four definitions are copied verbatim below under a 0 suffix,
   together with the three records they take, so that the equations are
   against the text of manifest/pgg_tableau.v at HEAD 2fc0108 and not against
   a paraphrase of it.  Each equation is universally quantified over the
   evidence: the evidence is a variable, never a constructor application. *)

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
From pgg_smc Require Import pgg_leakage_witness pgg_trace_secrecy.
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
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     Verbatim copies of the three records of HEAD 2fc0108                   *)
(******************************************************************************)

Record ExactWitness0 (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) :=
  MkExactWitness0 {
    ew_secretT0 : finType ;
    ew_secret0  : {RV (sa_sampleP sa) -> ew_secretT0} ;
    ew_indep0   : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
      (#|C| < profile_k (instance_profile A))%N ->
      sa_sampleP sa |= (fun u => static_coalition_obs C (sa.(sa_arg) u)
                                   (sa.(sa_cut) u)) _|_ ew_secret0 }.

Record IndistinguishabilityCert0 (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) :=
  MkIndistinguishabilityCert0 {
    ic_b0 : ShuffleMarginalBound R (instance_M A) ;
    ic_Hd0 : sw_rho_dist ic_b0 = sa_cut_dist sa ;
    ic_ideal0 : R.-fdist (pgg_gT (mp_M (instance_profile A))) ;
    ic_close0 : var_dist (sw_rho_dist ic_b0) ic_ideal0 <= sw_bound_eps ic_b0 ;
    ic_const0 : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
        (#|C| < profile_k (instance_profile A))%N ->
        forall x x' : ex_inputT E,
          fdistmap (static_coalition_obs C x) ic_ideal0
          = fdistmap (static_coalition_obs C x') ic_ideal0 }.

Record IdealProximityCert0 (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) :=
  MkIdealProximityCert0 {
    ipc_ideal0   : SampleAdapter R (instance_exec E) ;
    ipc_witness0 : ExactWitness0 ipc_ideal0 ;
    ipc_secret0  : {RV (sa_sampleP sa) -> ew_secretT0 ipc_witness0} ;
    ipc_eps0     : R ;
    ipc_close0   : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
      (#|C| < profile_k (instance_profile A))%N ->
      var_dist
        (fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                               (sa.(sa_cut) u), ipc_secret0 u))
           (sa_sampleP sa))
        (fdistmap (fun u => (static_coalition_obs C (ipc_ideal0.(sa_arg) u)
                               (ipc_ideal0.(sa_cut) u),
                             ew_secret0 ipc_witness0 u))
           (sa_sampleP ipc_ideal0))
      <= ipc_eps0 }.

(******************************************************************************)
(*     Verbatim copies of the four propositions of HEAD 2fc0108               *)
(******************************************************************************)

Definition ExactProp0 (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (w : ExactWitness0 sa) : Prop :=
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| < profile_k (instance_profile A))%N ->
    [/\ sa_sampleP sa |= (@sa_coalition_view R (instance_profile A)
                            (instance_exec E) sa 0 C)
                         _|_ (ew_secret0 w),
        `I( ew_secret0 w ;
            @sa_coalition_view R (instance_profile A) (instance_exec E)
              sa 0 C ) = 0,
        `H( ew_secret0 w |
            @sa_coalition_view R (instance_profile A) (instance_exec E)
              sa 0 C ) = `H `p_ (ew_secret0 w)
      & forall (W : finType)
               (h : {ffun 'I_(pi_T' (mp_PI (instance_profile A))).+1
                       -> 'I_(pgg_N' (mp_M (instance_profile A))).+1} -> W),
          sa_sampleP sa
          |= (h `o (@sa_coalition_view R (instance_profile A)
                      (instance_exec E) sa 0 C))
             _|_ (ew_secret0 w)].
Arguments ExactProp0 {R A E sa} w.

Definition IndistinguishabilityPropAt0 (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IndistinguishabilityCert0 sa) (c : R) : Prop :=
  forall (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1})
         (x x' : ex_inputT E),
    (#|C| < profile_k (instance_profile A))%N ->
    var_dist (fdistmap (static_coalition_obs C x) (sa_cut_dist sa))
             (fdistmap (static_coalition_obs C x') (sa_cut_dist sa))
    <= c.
Arguments IndistinguishabilityPropAt0 {R A E sa} cert c.

Definition IdealProximityPropAt0 (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IdealProximityCert0 sa) (c : R) : Prop :=
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| < profile_k (instance_profile A))%N ->
    var_dist
      (fdistmap (fun u => (@sa_coalition_view R (instance_profile A)
                             (instance_exec E) sa 0 C u, ipc_secret0 cert u))
         (sa_sampleP sa))
      ((fdistmap (@sa_coalition_view R (instance_profile A) (instance_exec E)
                    (ipc_ideal0 cert) 0 C) (sa_sampleP (ipc_ideal0 cert)))
       `x (fdistmap (ew_secret0 (ipc_witness0 cert))
             (sa_sampleP (ipc_ideal0 cert))))
    <= c.
Arguments IdealProximityPropAt0 {R A E sa} cert c.

Definition InputDistinguishabilityPropAt0 (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (c : R) : Prop :=
  exists (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1})
         (x x' : ex_inputT E),
    (#|C| < profile_k (instance_profile A))%N /\
    c <= var_dist (fdistmap (static_coalition_obs C x) (sa_cut_dist sa))
                  (fdistmap (static_coalition_obs C x') (sa_cut_dist sa)).
Arguments InputDistinguishabilityPropAt0 {R A E} sa c.

(******************************************************************************)
(*     The four equations at the default reading                              *)
(******************************************************************************)

Section k5.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

Local Notation r0 := (coalition_endpoint_reading A).

(* The three records at the default reading and today's three records have
   convertible field types: each rebuild below is the field-by-field copy,
   with no transport anywhere in it. *)
Definition exact0_of (w : ExactWitness sa r0) : ExactWitness0 sa :=
  @MkExactWitness0 R A E sa (ew_secretT w) (ew_secret w)
    (@ew_indep R A E sa r0 w).

Definition exact_of0 (w : ExactWitness0 sa) : ExactWitness sa r0 :=
  @MkExactWitness R A E sa r0 (ew_secretT0 w) (ew_secret0 w)
    (@ew_indep0 R A E sa w).

Definition indist0_of (cert : IndistinguishabilityCert sa r0)
  : IndistinguishabilityCert0 sa :=
  @MkIndistinguishabilityCert0 R A E sa (ic_b cert) (ic_Hd cert)
    (ic_ideal cert) (ic_close cert) (@ic_const R A E sa r0 cert).

Definition indist_of0 (cert : IndistinguishabilityCert0 sa)
  : IndistinguishabilityCert sa r0 :=
  @MkIndistinguishabilityCert R A E sa r0 (ic_b0 cert) (ic_Hd0 cert)
    (ic_ideal0 cert) (ic_close0 cert) (@ic_const0 R A E sa cert).

Definition prox0_of (cert : IdealProximityCert sa r0)
  : IdealProximityCert0 sa :=
  @MkIdealProximityCert0 R A E sa (ipc_ideal cert)
    (@MkExactWitness0 R A E (ipc_ideal cert)
       (ew_secretT (ipc_witness cert)) (ew_secret (ipc_witness cert))
       (@ew_indep R A E (ipc_ideal cert) r0 (ipc_witness cert)))
    (ipc_secret cert) (ipc_eps cert) (@ipc_close R A E sa r0 cert).

(* K5a: the exact-independence proposition.  Universally quantified over the
   witness, which is a variable and not a constructor application. *)
Lemma k5_exact (w : ExactWitness sa r0) : ExactProp w = ExactProp0 (exact0_of w).
Proof. exact: erefl. Qed.

Lemma k5_exact_back (w : ExactWitness0 sa) :
  ExactProp (exact_of0 w) = ExactProp0 w.
Proof. exact: erefl. Qed.

(* K5b: the input-indistinguishability proposition. *)
Lemma k5_indistinguishability (cert : IndistinguishabilityCert sa r0) (c : R) :
  IndistinguishabilityPropAt cert c
  = IndistinguishabilityPropAt0 (indist0_of cert) c.
Proof. exact: erefl. Qed.

Lemma k5_indistinguishability_back (cert : IndistinguishabilityCert0 sa)
    (c : R) :
  IndistinguishabilityPropAt (indist_of0 cert) c
  = IndistinguishabilityPropAt0 cert c.
Proof. exact: erefl. Qed.

(* K5c: the ideal-proximity proposition. *)
Lemma k5_idealproximity (cert : IdealProximityCert sa r0) (c : R) :
  IdealProximityPropAt cert c = IdealProximityPropAt0 (prox0_of cert) c.
Proof. exact: erefl. Qed.

(* K5d: the input-distinguishability proposition, whose reading is explicit
   and whose statement mentions no evidence. *)
Lemma k5_input_distinguishability (c : R) :
  InputDistinguishabilityPropAt sa r0 c
  = InputDistinguishabilityPropAt0 sa c.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The mutation: a reading that is not the identity                       *)
(******************************************************************************)

(* A reading granting the coalition nothing at all: every endpoint map is
   read as the constant map at card zero. *)
Definition blind_reading : EndpointReading A :=
  @MkEndpointReading A
    (fun _ => [the finType of
                 {ffun 'I_(pi_T' (mp_PI (instance_profile A))).+1
                    -> 'I_(pgg_N' (mp_M (instance_profile A))).+1}])
    (fun _ _ => [ffun _ => ord0]).

(* The rebuild of K5a at this reading does not typecheck: the independence
   field is about a different random variable. *)
Fail Definition k5_mutation_rebuild (w : ExactWitness sa blind_reading)
  : ExactWitness0 sa :=
  @MkExactWitness0 R A E sa (ew_secretT w) (ew_secret w)
    (@ew_indep R A E sa blind_reading w).

(* And the proposition at this reading is not today's.  The equation is
   written as a definition so that the one Fail covers the proof term: a Fail
   on a Lemma command checks the statement alone, and the statement of an
   equation between two propositions typechecks at every reading. *)
Fail Definition k5_mutation (w : ExactWitness sa blind_reading)
    (w0 : ExactWitness0 sa) : ExactProp w = ExactProp0 w0 := erefl.

End k5.
