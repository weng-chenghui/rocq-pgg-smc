(* Fidelity file of the landing: the probe's checks re-pointed at production,
   the thirteen declarations that left psl211_reading_constancy.v at the
   statements they carry, the dealer-dealt correctness theorem and its facade
   alias, the two typed paths with their status pins, the two published paths
   against those typed paths, and the axioms.

   Every statement below is extracted verbatim from the production text, with
   the binders turned into a forall and the constant taken at @, so an
   implicit argument cannot hide a change. *)

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
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import psl211_group psl211_closure psl211_orbit.
From pgg_smc Require Import psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_secrecy.
From pgg_smc Require Import psl211_alldecks psl211_models psl211_dealt_model.
From pgg_smc Require Import psl211_analysis.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax pgg_tableau_reading.
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
  = psl211_dealt_colour_path).

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
  = psl211_dealt_obstruction_path).

(**************************************************************************)
(*   The declarations that left psl211_reading_constancy.v, at the        *)
(*   statements they carry in psl211_dealt_model.v                        *)
(**************************************************************************)

Timeout 300 Check (psl211_perdeck_coalition_le3
  : (#|psl211_perdeck_coalition| <= 3)%N).

Timeout 300 Check (psl211_perdeck_coalition_below_k
  : (#|psl211_perdeck_coalition|
     < profile_k (instance_profile psl211_algebra))%N).

Timeout 300 Check (psl211_dealt_decktbl
  : bool -> seq nat).

Timeout 300 Check (@psl211_dealt_decktblE
  : forall (b : bool) (i : 'I_12),
     val (tnth (psl211_orbit_encode b) i)
  = nth 0 (psl211_dealt_decktbl b) (val i)).

Timeout 300 Check (@psl211_dealt_decktbl_mod
  : forall (b : bool) (k : nat),
     nth 0 (psl211_dealt_decktbl b) k %% 12
  = nth 0 (psl211_dealt_decktbl b) k).

Timeout 300 Check (psl211_dealt_view
  : {ffun seats -> cards}).

Timeout 300 Check (psl211_dealt_test
  : seq nat -> seq nat -> bool).

Timeout 300 Check (@psl211_dealt_testE
  : forall sq t : seq nat,
     (psl211_perdeck_raw_view sq t == psl211_dealt_view)
  = psl211_dealt_test sq t).

Timeout 300 Check (psl211_dealt_raw_count
  : bool -> nat).

Timeout 300 Check (psl211_dealt_raw_countE
  : psl211_dealt_raw_count true = 0 /\ psl211_dealt_raw_count false = 1).

Timeout 300 Check (@psl211_dealt_static_obsE
  : forall (C : {set seats}) (b : ex_inputT psl211_dealt_params) (g : cutT)
    (i : seats),
     @static_coalition_obs psl211_algebra psl211_dealt_params C b g i
  = if i \in C
    then tnth (psl211_orbit_encode b) (@pgg_rho psl211_M g i)
    else ord0).

Timeout 300 Check (@psl211_dealt_raw_viewE
  : forall (b : bool) (g : cutT),
     psl211_perdeck_raw_view (psl211_dealt_decktbl b) (psl211_ptbl g)
  = @static_coalition_obs psl211_algebra psl211_dealt_params
      psl211_perdeck_coalition b g).

Timeout 300 Check (psl211_dealt_fiber
  : bool -> {set cutT}).

Timeout 300 Check (@psl211_dealt_fiberE
  : forall b : bool,
     #|psl211_dealt_fiber b| = psl211_dealt_raw_count b).

Timeout 300 Check (@psl211_dealt_massE
  : forall (R : realType) (b : bool),
     (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
          psl211_perdeck_coalition b) ((`U psl211_G_pos) : R.-fdist cutT))
        psl211_dealt_view
  = (#|pgg_G psl211_M|%:R)^-1 *+ #|psl211_dealt_fiber b| :> R).

(**************************************************************************)
(*   The dealer-dealt correctness theorem and its facade alias            *)
(**************************************************************************)

Timeout 300 Check (@psl211_dealt_observed_recovers
  : forall (x : bool) (w0 : pgg_gT psl211_M),
     w0 \in pgg_G psl211_M ->
  @exec_decode (instance_profile psl211_algebra)
    (instance_exec psl211_dealt_params)
    (@exec_endpoints (instance_profile psl211_algebra)
       (instance_exec psl211_dealt_params) x w0 0)
    (OE.oe_endpoints_size psl211_dealt_observed x w0) = x).

Timeout 300 Check (PSL211Analysis.dealt_observed_recovers
  : forall (x : bool) (w0 : pgg_gT (mp_M PSL211Analysis.profile)),
     w0 \in pgg_G (mp_M PSL211Analysis.profile) ->
  exec_decode PSL211Analysis.dealt_exec_plug
    (OE.oe_endpoints_size PSL211Analysis.dealt_observed x w0) = x).

(**************************************************************************)
(*   The two typed paths of the manifest, with their status pins          *)
(**************************************************************************)

Timeout 300 Check (psl211_dealt_colour_path : AnalysisPath).
Timeout 300 Check (ap_model psl211_dealt_colour_path
  : AnalysisModelFamily psl211_dealt_observed).
Timeout 300 Check
  (erefl : ap_completion psl211_dealt_colour_path = AnalysisBridged).
Timeout 300 Check
  (erefl : ap_transfer psl211_dealt_colour_path = StaticExecutedOnly).
Timeout 300 Check
  (erefl : ap_assumptions psl211_dealt_colour_path = BaselineClassicalOnly).

Timeout 300 Check (psl211_dealt_obstruction_path : AnalysisPath).
Timeout 300 Check (ap_model psl211_dealt_obstruction_path
  : AnalysisModelFamily psl211_dealt_observed).
Timeout 300 Check
  (erefl : ap_completion psl211_dealt_obstruction_path = AnalysisBridged).
Timeout 300 Check
  (erefl : ap_transfer psl211_dealt_obstruction_path = NegativeTransfer).
Timeout 300 Check
  (erefl : ap_assumptions psl211_dealt_obstruction_path
           = BaselineClassicalOnly).

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

(* The right-hand side each equation carries in the spelled form, so the
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

Timeout 300 Print Assumptions psl211_dealt_colour_indep.
Timeout 300 Print Assumptions psl211_dealt_perdeck_reading_ge.
Timeout 300 Print Assumptions psl211_colour_exact_published.
Timeout 300 Print Assumptions psl211_dealt_obstruction_published.
