(* Fidelity file of the probe: every declaration of the two restated files
   checked against the statement it has in production today (M7), the two
   published paths against the manifest's typed paths (M6), and the axioms
   of the two raw theorems and the two programs.

   The statements below are extracted verbatim from the production text of
   instances/psl211/psl211_colour_reading.v and of
   instances/psl211/tableau/psl211_tableau_dealt.v, with the binders turned
   into a forall and the constant taken at @, so an implicit argument cannot
   hide a change. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_reconstruct Require Import transitivity_privacy design_privacy.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax pgg_tableau_reading.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_secrecy.
From pgg_smc Require Import psl211_models psl211_dealt_model.
From pgg_smc Require Import psl211_reading_constancy psl211_colour_reading.
From pgg_smc Require Import psl211_tableau_dealt.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Notation seats :=
  'I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1.
Local Notation cards :=
  'I_(pgg_N' (mp_M (instance_profile psl211_algebra))).+1.
Local Notation cutT := (pgg_gT (mp_M (instance_profile psl211_algebra))).

(**************************************************************************)
(*   M7: every declaration at the statement it has today                  *)
(**************************************************************************)

(* --- psl211_colour_reading.v --- *)

Timeout 300 Check (@psl211_dealt_inputTE
  : ep_inputT (instance_exec psl211_dealt_params) = bool).

Timeout 300 Check (@psl211_dealt_sample
  : forall (R : realType) (secretP : R.-fdist bool),
     SampleAdapter R (instance_exec psl211_dealt_params)).

Timeout 300 Check (@psl211_dealt_sample_lawE
  : forall (R : realType) (secretP : R.-fdist bool),
     sa_sampleP (psl211_dealt_sample secretP) = psl211P secretP).

Timeout 300 Check (@psl211_dealt_sample_argE
  : forall (R : realType) (secretP : R.-fdist bool)
    (u : bool * pgg_gT psl211_M),
     (psl211_dealt_sample secretP).(sa_arg) u = u.1).

Timeout 300 Check (@psl211_dealt_sample_cutE
  : forall (R : realType) (secretP : R.-fdist bool)
    (u : bool * pgg_gT psl211_M),
     (psl211_dealt_sample secretP).(sa_cut) u = u.2).

Timeout 300 Check (@psl211_dealt_sample_cut_distE
  : forall (R : realType) (secretP : R.-fdist bool),
     @sa_cut_dist R (instance_profile psl211_algebra)
    (instance_exec psl211_dealt_params) (psl211_dealt_sample secretP)
  = (`U psl211_G_pos : R.-fdist (pgg_gT psl211_M))).

Timeout 300 Check (@psl211_colour_of_reading
  : forall (C : {set seats})
    (v : {ffun seats -> cards}),
     {ffun seats -> bool}).

Timeout 300 Check (@psl211_colour_reading
  : CoalitionReading psl211_algebra).

Timeout 300 Check (@psl211_colour_of_reading_obsE
  : forall (C : {set seats})
    (b : ex_inputT psl211_dealt_params) (g : cutT),
     psl211_colour_of_reading C
    (@static_coalition_obs psl211_algebra psl211_dealt_params C b g)
  = [ffun i => if i \in C
               then psl211_is_heart
                      (tnth (psl211_orbit_encode b) (@pgg_rho psl211_M g i))
               else false]).

Timeout 300 Check (@psl211_colour_readingE
  : forall (R : realType) (secretP : R.-fdist bool)
    (C : {set seats}) (u : bool * pgg_gT psl211_M),
     psl211_colour_view secretP C u
  = cr_read psl211_colour_reading C
      (static_coalition_obs C ((psl211_dealt_sample secretP).(sa_arg) u)
         ((psl211_dealt_sample secretP).(sa_cut) u))).

Timeout 300 Check (@psl211_colour_reading_funE
  : forall (R : realType) (secretP : R.-fdist bool)
    (C : {set seats}),
     psl211_colour_view secretP C
  = (fun u => cr_read psl211_colour_reading C
                (static_coalition_obs C
                   ((psl211_dealt_sample secretP).(sa_arg) u)
                   ((psl211_dealt_sample secretP).(sa_cut) u)))).

Timeout 300 Check (@psl211_colour_indistinguishability_of_coalition_reading
  : forall (R : realType)
    (secretP : R.-fdist bool) (c : R),
     ReadingIndistinguishabilityPropAt (psl211_dealt_sample secretP)
    (coalition_endpoint_reading psl211_algebra) c ->
  ReadingIndistinguishabilityPropAt (psl211_dealt_sample secretP)
    psl211_colour_reading c).

Timeout 300 Check (@psl211_colour_of_reading_collides
  : forall (C : {set seats}) (i0 : seats),
     i0 \in C ->
  exists v w : {ffun seats -> cards},
    v != w /\ psl211_colour_of_reading C v = psl211_colour_of_reading C w).

Timeout 300 Check (@psl211_colour_reading_indep
  : forall (R : realType) (secretP : R.-fdist bool),
     ReadingExactIndependence (psl211_dealt_sample secretP) psl211_colour_reading
    (psl211_secret secretP)).

Timeout 300 Check (@psl211_leak_coalition_not_below_k
  : ~~ (#|psl211_leak_coalition| < profile_k (instance_profile psl211_algebra))%N).

Timeout 300 Check (@psl211_colour_reading_dep_k6
  : forall (R : realType) (secretP : R.-fdist bool),
     secretP true != 0 -> secretP false != 0 ->
  (#|psl211_leak_coalition| = profile_k (instance_profile psl211_algebra))%N /\
  ~ sa_sampleP (psl211_dealt_sample secretP)
      |= (fun u => cr_read psl211_colour_reading psl211_leak_coalition
                     (@static_coalition_obs psl211_algebra
                        psl211_dealt_params psl211_leak_coalition
                        ((psl211_dealt_sample secretP).(sa_arg) u)
                        ((psl211_dealt_sample secretP).(sa_cut) u)))
         _|_ psl211_secret secretP).

Timeout 300 Check (@psl211_dealt_perdeck_reading
  : forall (R : realType) (secretP : R.-fdist bool),
     {RV (psl211P secretP) -> {ffun seats -> cards}}).

Timeout 300 Check (@psl211_dealt_perdeck_readingE
  : forall (R : realType) (secretP : R.-fdist bool),
     (fun u => @cr_read psl211_algebra
              (coalition_endpoint_reading psl211_algebra)
              psl211_perdeck_coalition
              (static_coalition_obs psl211_perdeck_coalition
                 ((psl211_dealt_sample secretP).(sa_arg) u)
                 ((psl211_dealt_sample secretP).(sa_cut) u)))
  = psl211_dealt_perdeck_reading secretP).

Timeout 300 Check (@psl211_dealt_reading_indep_false
  : forall (R : realType)
    (secretP : R.-fdist bool),
     secretP true != 0 -> secretP false != 0 ->
  ~ ReadingExactIndependence (psl211_dealt_sample secretP)
      (coalition_endpoint_reading psl211_algebra) (psl211_secret secretP)).

(* --- psl211_tableau_dealt.v --- *)

Timeout 300 Check (@psl211_dealt_family
  : AnalysisModelFamily psl211_dealt_observed).

Timeout 300 Check (@psl211_dealt_sampled
  : Tableau Sampled).

Timeout 300 Check (@psl211_dealt_sampled_viewE
  : sampled_viewE_prop (sp_f (tableau_at psl211_dealt_sampled))).

Timeout 300 Check (@psl211_colour_exact_witness
  : forall (R : realType)
    (secretP : R.-fdist bool),
     ExactWitness (psl211_dealt_sample secretP) psl211_colour_reading).

Timeout 300 Check (@psl211_colour_exact_published
  : Published).

Timeout 300 Check (@psl211_colour_exact_published_readingE
  : forall (R : realType)
    (secretP : R.-fdist bool),
     reading_of psl211_colour_exact_published R secretP = psl211_colour_reading).

Timeout 300 Check (@psl211_colour_exact_published_propertyE
  : forall (R : realType)
    (secretP : R.-fdist bool),
     security_property_of psl211_colour_exact_published R secretP
  = ExactIndependenceProperty).

Timeout 300 Check (@psl211_colour_exact_published_pathE
  : published_path psl211_colour_exact_published
  = @MkAnalysisPath psl211_dealt_observed AnalysisBridged psl211_dealt_family
      StaticExecutedOnly BaselineClassicalOnly).

Timeout 300 Check (@psl211_dealt_input_distinguishable
  : forall (R : realType)
    (secretP : R.-fdist bool),
     InputDistinguishabilityPropAt (psl211_dealt_sample secretP)
    (coalition_endpoint_reading psl211_algebra)
    ((#|pgg_G psl211_M|%:R)^-1 : R)).

Timeout 300 Check (@psl211_dealt_number
  : forall R : realType, R).

Timeout 300 Check (@psl211_dealt_obstruction
  : ObstructionPayload (tableau_at psl211_dealt_sampled)).

Timeout 300 Check (@psl211_dealt_number_gt0
  : forall (R : realType),
     0 < psl211_dealt_number R).

Timeout 300 Check (@psl211_dealt_obstruction_pf
  : ObstructionPayloadProp psl211_dealt_obstruction).

Timeout 300 Check (@psl211_dealt_obstruction_published
  : PublishedObstruction).

Timeout 300 Check (@psl211_dealt_obstruction_published_kindE
  : published_obstruction_kind psl211_dealt_obstruction_published
  = psl211_dealt_obstruction).

Timeout 300 Check (@psl211_dealt_obstruction_published_pathE
  : published_obstruction_path psl211_dealt_obstruction_published
  = @MkAnalysisPath psl211_dealt_observed AnalysisBridged psl211_dealt_family
      NegativeTransfer BaselineClassicalOnly).

(**************************************************************************)
(*   M6: the two published paths are the manifest's thirteenth and        *)
(*   fourteenth, each decided by conversion                               *)
(**************************************************************************)

Timeout 300 Check
  (erefl : published_path psl211_colour_exact_published
           = psl211_dealt_colour_path).

Timeout 300 Check
  (erefl : published_obstruction_path psl211_dealt_obstruction_published
           = psl211_dealt_obstruction_path).

(* The right-hand side each equation carries in production today, so the
   change of spelling is shown to be a change of spelling alone. *)

Timeout 300 Check
  (erefl : published_path psl211_colour_exact_published
           = @MkAnalysisPath psl211_dealt_observed AnalysisBridged
               psl211_dealt_family StaticExecutedOnly BaselineClassicalOnly).

Timeout 300 Check
  (erefl : published_obstruction_path psl211_dealt_obstruction_published
           = @MkAnalysisPath psl211_dealt_observed AnalysisBridged
               psl211_dealt_family NegativeTransfer BaselineClassicalOnly).

(**************************************************************************)
(*   The axioms of the two raw theorems and of the two programs           *)
(**************************************************************************)

Print Assumptions psl211_dealt_colour_indep.
Print Assumptions psl211_dealt_perdeck_reading_ge.
Print Assumptions psl211_colour_exact_published.
Print Assumptions psl211_dealt_obstruction_published.
