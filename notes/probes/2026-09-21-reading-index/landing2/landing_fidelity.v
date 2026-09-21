(* Fidelity file for landing commit 2, the reading as an index of the
   security claim.  Production Requires only.  It states, against the landed
   tree and nothing else:

   - the full statement of every declaration the landing added or restated in
     manifest/pgg_tableau.v, manifest/pgg_tableau_reading.v,
     manifest/pgg_tableau_security_property_relations.v and the new file
     instances/psl211/tableau/psl211_tableau_dealt.v;
   - the four K5 equations, against verbatim copies of the four propositions
     of HEAD 2fc0108, so that at the default reading the landed propositions
     are the ones the tree proved before this commit;
   - the three framework _readingE lemmas applied to one program per instance
     that names no reading, and the colour program's own _readingE;
   - a non-degenerate instance of the number bound at PSL(2,11);
   - Print Assumptions on the three tails, on the monotonicity lemma and on
     the two new PSL(2,11) results. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import smc_interpreter pgg_interface.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_sample_adapter.
From pgg_smc Require Import pgg_leakage_witness pgg_trace_secrecy.
From pgg_smc Require Import pgg_collusion_bound pgg_analysis_status.
From pgg_reconstruct Require Import pgg_sharing_framework algebraic_rigidity.
From pgg_smc Require Import pgg_instance pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import pgg_tableau_reading.
From pgg_smc Require Import pgg_tableau_security_property_relations.
From pgg_smc Require Import s5_exec five_card_exec pgl27_exec.
From pgg_smc Require Import s5_tableau_analysis_bridged.
From pgg_smc Require Import five_card_tableau_analysis_bridged.
From pgg_smc Require Import pgl27_tableau_analysis_bridged.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_models.
From pgg_smc Require Import psl211_reading_constancy psl211_colour_reading.
From pgg_smc Require Import psl211_tableau_sampled.
From pgg_smc Require Import psl211_tableau_analysis_bridged.
From pgg_smc Require Import psl211_tableau_dealt.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     The framework's new and restated declarations, in full                 *)
(******************************************************************************)

Check (CoalitionReading : PGGAlgebraic -> Type).

Check (coalition_endpoint_reading
       : forall A : PGGAlgebraic, CoalitionReading A).

Check (@cr_readT
       : forall A : PGGAlgebraic, CoalitionReading A ->
         {set 'I_(pi_T' (mp_PI (instance_profile A))).+1} -> finType).

Check (@cr_read
       : forall (A : PGGAlgebraic) (r : CoalitionReading A)
                (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}),
         {ffun 'I_(pi_T' (mp_PI (instance_profile A))).+1
            -> 'I_(pgg_N' (mp_M (instance_profile A))).+1} -> cr_readT r C).

Check (@ExactWitness
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A),
         SampleAdapter R (instance_exec E) -> CoalitionReading A -> Type).

Check (@IndistinguishabilityCert
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A),
         SampleAdapter R (instance_exec E) -> CoalitionReading A -> Type).

Check (@IdealProximityCert
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A),
         SampleAdapter R (instance_exec E) -> CoalitionReading A -> Type).

Check (@ExactIndependence
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
                (sa : SampleAdapter R (instance_exec E))
                (r : CoalitionReading A),
         ExactWitness sa r -> SecurityEvidence sa).

Check (@InputIndistinguishability
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
                (sa : SampleAdapter R (instance_exec E))
                (r : CoalitionReading A),
         IndistinguishabilityCert sa r -> SecurityEvidence sa).

Check (@IdealProximity
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
                (sa : SampleAdapter R (instance_exec E))
                (r : CoalitionReading A),
         IdealProximityCert sa r -> SecurityEvidence sa).

Check (@evidence_reading
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
                (sa : SampleAdapter R (instance_exec E)),
         SecurityEvidence sa -> CoalitionReading A).

Check (ab_reading
       : forall (q : StackAt AnalysisBridged) (R : realType),
         amf_index (ab_f q) R -> CoalitionReading (projT1 q)).

Check (@reading_of
       : forall (c : ConcludedBound) (p : PublishedAt c) (R : realType)
                (idx : amf_index (ab_f (published_at p)) R),
         CoalitionReading (projT1 (published_at p))).

Check (@ReadingIndistinguishabilityPropAt
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A),
         SampleAdapter R (instance_exec E) -> CoalitionReading A -> R -> Prop).

Check (@ReadingExactPayload : StackAt Sampled -> Type).
Check (@ReadingIndistinguishabilityPayload : StackAt Sampled -> Type).
Check (@ReadingIdealProximityPayload : StackAt Sampled -> Type).

Check (reading_exact_payload
       : forall (x : StackAt Sampled) (r : CoalitionReading (projT1 x)),
         (forall (R : realType) (idx : amf_index (sp_f x) R),
            ExactWitness (amf_sample (sp_f x) R idx) r) ->
         ReadingExactPayload x).

Check (reading_indistinguishability_payload
       : forall (x : StackAt Sampled) (r : CoalitionReading (projT1 x)),
         (forall (R : realType) (idx : amf_index (sp_f x) R),
            IndistinguishabilityCert (amf_sample (sp_f x) R idx) r) ->
         ReadingIndistinguishabilityPayload x).

Check (reading_idealproximity_payload
       : forall (x : StackAt Sampled) (r : CoalitionReading (projT1 x)),
         (forall (R : realType) (idx : amf_index (sp_f x) R),
            IdealProximityCert (amf_sample (sp_f x) R idx) r) ->
         ReadingIdealProximityPayload x).

Check (certify_reading_exact
       : forall (x : StackAt Sampled), StackProp Sampled x ->
         ReadingExactPayload x -> Tableau AnalysisBridged).

Check (certify_reading_indistinguishability
       : forall (x : StackAt Sampled), StackProp Sampled x ->
         ReadingIndistinguishabilityPayload x -> Tableau AnalysisBridged).

Check (certify_reading_idealproximity
       : forall (x : StackAt Sampled), StackProp Sampled x ->
         ReadingIdealProximityPayload x -> Tableau AnalysisBridged).

Check (@certify_exact_readingE
       : forall (x : StackAt Sampled) (q : StackProp Sampled x)
                (p : ExactPayload x) (R : realType)
                (idx : amf_index (ab_f (tableau_at (certify_exact q p))) R),
         ab_reading (tableau_at (certify_exact q p)) R idx
         = coalition_endpoint_reading (projT1 x)).

Check (@certify_indistinguishability_readingE
       : forall (x : StackAt Sampled) (q : StackProp Sampled x)
                (p : IndistinguishabilityPayload x) (R : realType)
                (idx : amf_index
                         (ab_f (tableau_at
                                  (certify_indistinguishability q p))) R),
         ab_reading (tableau_at (certify_indistinguishability q p)) R idx
         = coalition_endpoint_reading (projT1 x)).

Check (@certify_idealproximity_readingE
       : forall (x : StackAt Sampled) (q : StackProp Sampled x)
                (p : IdealProximityPayload x) (R : realType)
                (idx : amf_index
                         (ab_f (tableau_at
                                  (certify_idealproximity q p))) R),
         ab_reading (tableau_at (certify_idealproximity q p)) R idx
         = coalition_endpoint_reading (projT1 x)).

Check (@InputDistinguishabilityPropAt
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A),
         SampleAdapter R (instance_exec E) -> CoalitionReading A -> R -> Prop).

Check (@InputDistinguishabilityObstruction
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
                (sa : SampleAdapter R (instance_exec E)),
         CoalitionReading A -> R -> ObstructionKind sa).

Check (input_distinguishability_obstruction
       : forall (q : StackAt Sampled), CoalitionReading (projT1 q) ->
         (forall R : realType, R) -> ObstructionPayload q).

(******************************************************************************)
(*     The lemmas about readings, in full                                     *)
(******************************************************************************)

Check (@reading_factors
       : forall (A : PGGAlgebraic) (r r' : CoalitionReading A),
         (forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
            cr_readT r C -> cr_readT r' C) -> Prop).

Check (@reading_factors_coalition_endpoint_reading
       : forall (A : PGGAlgebraic) (r : CoalitionReading A),
         reading_factors (coalition_endpoint_reading A) r (@cr_read A r)).

Check (@reading_indistinguishability_postprocessing
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
                (sa : SampleAdapter R (instance_exec E))
                (r r' : CoalitionReading A)
                (f : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
                       cr_readT r C -> cr_readT r' C),
         reading_factors r r' f -> forall c : R,
         ReadingIndistinguishabilityPropAt sa r c ->
         ReadingIndistinguishabilityPropAt sa r' c).

Check (@input_distinguishability_prop_finer
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
                (sa : SampleAdapter R (instance_exec E))
                (r r' : CoalitionReading A)
                (f : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
                       cr_readT r C -> cr_readT r' C),
         reading_factors r r' f -> forall c : R,
         InputDistinguishabilityPropAt sa r' c ->
         InputDistinguishabilityPropAt sa r c).

Check (@input_distinguishability_prop_coalition_endpoint_reading
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
                (sa : SampleAdapter R (instance_exec E))
                (r : CoalitionReading A) (c : R),
         InputDistinguishabilityPropAt sa r c ->
         InputDistinguishabilityPropAt sa (coalition_endpoint_reading A) c).

Check (@indistinguishability_number_ge_across_readings
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
                (sa : SampleAdapter R (instance_exec E))
                (r r' : CoalitionReading A)
                (f : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
                       cr_readT r C -> cr_readT r' C),
         reading_factors r r' f ->
         forall (cert : IndistinguishabilityCert sa r) (c c' : R),
         InputDistinguishabilityPropAt sa r' c ->
         IndistinguishabilityPropAt cert c' -> c <= c').

Check (@exact_independence_of_witness
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
                (sa : SampleAdapter R (instance_exec E))
                (r : CoalitionReading A) (w : ExactWitness sa r),
         ReadingExactIndependence sa r (ew_secret w)).

Check (@coalition_reading_cst_unit
       : forall A : PGGAlgebraic, CoalitionReading A).

Check (@exact_witness_cst_reading
       : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
                (sa : SampleAdapter R (instance_exec E)) (secretT : finType)
                (secret : {RV (sa_sampleP sa) -> secretT}),
         ExactWitness sa (coalition_reading_cst_unit A)).

(******************************************************************************)
(*     The new PSL(2,11) file, in full                                        *)
(******************************************************************************)

Check (psl211_dealt_endpoints
       : instance_endpoints_stmt psl211_dealt_params).
Check (psl211_dealt_observed : OE.ObservedExecution).
Check (psl211_dealt_family : AnalysisModelFamily psl211_dealt_observed).
Check (psl211_dealt_sampled : Tableau Sampled).
Check (psl211_dealt_sampled_viewE
       : sampled_viewE_prop (sp_f (tableau_at psl211_dealt_sampled))).

Check (psl211_colour_reading : CoalitionReading psl211_algebra).

Check (psl211_colour_exact_witness
       : forall (R : realType) (secretP : R.-fdist bool),
         ExactWitness (psl211_dealt_sample secretP) psl211_colour_reading).

Check (psl211_colour_exact_published : Published).

Check (psl211_dealt_input_distinguishable
       : forall (R : realType) (secretP : R.-fdist bool),
         InputDistinguishabilityPropAt (psl211_dealt_sample secretP)
           (coalition_endpoint_reading psl211_algebra)
           ((#|pgg_G psl211_M|%:R)^-1 : R)).

Check (psl211_dealt_number : forall R : realType, R).
Check (psl211_dealt_obstruction
       : ObstructionPayload (tableau_at psl211_dealt_sampled)).
Check (psl211_dealt_obstruction_pf
       : ObstructionPayloadProp psl211_dealt_obstruction).
Check (psl211_dealt_obstruction_published : PublishedObstruction).

Check (psl211_colour_exact_published_readingE
       : forall (R : realType) (secretP : R.-fdist bool),
         reading_of psl211_colour_exact_published R secretP
         = psl211_colour_reading).

Check (psl211_colour_exact_published_propertyE
       : forall (R : realType) (secretP : R.-fdist bool),
         security_property_of psl211_colour_exact_published R secretP
         = ExactIndependenceProperty).

Check (psl211_colour_exact_published_pathE
       : published_path psl211_colour_exact_published
         = @MkAnalysisPath psl211_dealt_observed AnalysisBridged
             psl211_dealt_family StaticExecutedOnly BaselineClassicalOnly).

Check (psl211_dealt_number_gt0
       : forall R : realType, 0 < psl211_dealt_number R).

Check (psl211_dealt_obstruction_published_kindE
       : published_obstruction_kind psl211_dealt_obstruction_published
         = psl211_dealt_obstruction).

Check (psl211_dealt_obstruction_published_pathE
       : published_obstruction_path psl211_dealt_obstruction_published
         = @MkAnalysisPath psl211_dealt_observed AnalysisBridged
             psl211_dealt_family NegativeTransfer BaselineClassicalOnly).

(******************************************************************************)
(*     The obstruction terminal, in the landed surface                        *)
(******************************************************************************)

(* The all-decks obstruction program names the reading it publishes at after
   of, as the dealer-dealt one does, and the line the surface reads is the
   term the definition carries. *)
Check (erefl
       : psl211_alldecks_obstruction_published
         = (psl211_exact_sampled
              |> publish Obstruction InputDistinguishability
                 of (coalition_endpoint_reading psl211_algebra)
                 at psl211_alldecks_number
                 by psl211_alldecks_obstruction_pf
                 assuming BaselineClassicalOnly)).

(******************************************************************************)
(*     K5: the four propositions at the default reading are today's           *)
(******************************************************************************)

(* Verbatim copies of the three records of HEAD 2fc0108. *)

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

(* Verbatim copies of the four propositions of HEAD 2fc0108. *)

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

Section k5.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

Local Notation r0 := (coalition_endpoint_reading A).

Definition exact0_of (w : ExactWitness sa r0) : ExactWitness0 sa :=
  @MkExactWitness0 R A E sa (ew_secretT w) (ew_secret w)
    (@ew_indep R A E sa r0 w).

Definition indist0_of (cert : IndistinguishabilityCert sa r0)
  : IndistinguishabilityCert0 sa :=
  @MkIndistinguishabilityCert0 R A E sa (ic_b cert) (ic_Hd cert)
    (ic_ideal cert) (ic_close cert) (@ic_const R A E sa r0 cert).

Definition prox0_of (cert : IdealProximityCert sa r0)
  : IdealProximityCert0 sa :=
  @MkIdealProximityCert0 R A E sa (ipc_ideal cert)
    (@MkExactWitness0 R A E (ipc_ideal cert)
       (ew_secretT (ipc_witness cert)) (ew_secret (ipc_witness cert))
       (@ew_indep R A E (ipc_ideal cert) r0 (ipc_witness cert)))
    (ipc_secret cert) (ipc_eps cert) (@ipc_close R A E sa r0 cert).

Lemma k5_exact (w : ExactWitness sa r0) :
  ExactProp w = ExactProp0 (exact0_of w).
Proof. exact: erefl. Qed.

Lemma k5_indistinguishability (cert : IndistinguishabilityCert sa r0) (c : R) :
  IndistinguishabilityPropAt cert c
  = IndistinguishabilityPropAt0 (indist0_of cert) c.
Proof. exact: erefl. Qed.

Lemma k5_idealproximity (cert : IdealProximityCert sa r0) (c : R) :
  IdealProximityPropAt cert c = IdealProximityPropAt0 (prox0_of cert) c.
Proof. exact: erefl. Qed.

Lemma k5_input_distinguishability (c : R) :
  InputDistinguishabilityPropAt sa r0 c = InputDistinguishabilityPropAt0 sa c.
Proof. exact: erefl. Qed.

End k5.

(******************************************************************************)
(*     The reading of one default program per instance                        *)
(******************************************************************************)

Lemma fidelity_s5_readingE (R : realType) (idx : unit) :
  reading_of s5_rand_published R idx = coalition_endpoint_reading s5_algebra.
Proof. exact: erefl. Qed.

Lemma fidelity_five_card_readingE (R : realType) (idx : unit) :
  reading_of five_card_uniform_published R idx
  = coalition_endpoint_reading five_card_algebra.
Proof. exact: erefl. Qed.

Lemma fidelity_pgl27_readingE (R : realType) (idx : unit) :
  reading_of pgl27_exact_published R idx
  = coalition_endpoint_reading pgl27_algebra.
Proof. exact: erefl. Qed.

Lemma fidelity_psl211_readingE (R : realType) (idx : unit) :
  reading_of psl211_alldecks_published R idx
  = coalition_endpoint_reading psl211_algebra.
Proof. exact: erefl. Qed.

Lemma fidelity_colour_readingE (R : realType) (secretP : R.-fdist bool) :
  reading_of psl211_colour_exact_published R secretP = psl211_colour_reading.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     A non-degenerate instance of the number bound                          *)
(******************************************************************************)

(* The all-decks obstruction at 1/660 excludes the number zero for every
   input-indistinguishability certificate over that model at the coalition's
   own endpoint reading, so the bound is not the free inequality at zero. *)
Lemma fidelity_number_bound_nondegenerate (R : realType)
    (cert : IndistinguishabilityCert (psl211_alldecks_sample R)
              (coalition_endpoint_reading psl211_algebra)) :
  ~ IndistinguishabilityPropAt cert 0.
Proof.
move=> H.
have H0 := @psl211_alldecks_indistinguishability_number_ge R cert 0 H.
have Hp : (0 : R) < (#|pgg_G psl211_M|%:R)^-1
  by rewrite invr_gt0 ltr0n; exact: psl211_G_pos.
by move: (Order.POrderTheory.lt_le_trans Hp H0);
   rewrite Order.POrderTheory.ltxx.
Qed.

(******************************************************************************)
(*     Axiom dependencies                                                     *)
(******************************************************************************)

Timeout 300 Print Assumptions exact_tail.
Timeout 300 Print Assumptions indistinguishability_tail.
Timeout 300 Print Assumptions idealproximity_tail.
Timeout 300 Print Assumptions input_distinguishability_prop_finer.
Timeout 300 Print Assumptions psl211_colour_exact_published.
Timeout 300 Print Assumptions psl211_dealt_obstruction_published.
Timeout 300 Print Assumptions psl211_dealt_input_distinguishable.
