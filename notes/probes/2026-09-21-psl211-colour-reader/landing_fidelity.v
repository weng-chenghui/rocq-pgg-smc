(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* landing_fidelity: every declaration of the reading and marginal-bound      *)
(* landing, read back from production at its full statement                   *)
(*                                                                            *)
(* PROBE FILE. Nothing permanent requires it. Each Check ascribes the type    *)
(* the landed declaration is expected to have, with every argument explicit   *)
(* through @, so that a change to a statement or to an Arguments line fails   *)
(* here. The applications below the Checks elaborate each landed name with    *)
(* its implicit arguments left out, which is how the production call sites    *)
(* use them.                                                                  *)
(*                                                                            *)
(* The bodies of the four propositions are pinned by production, not here.    *)
(******************************************************************************)

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
From pgg_reconstruct Require Import algebraic_rigidity pgg_sharing_framework.
From pgg_reconstruct Require Import transitivity_privacy design_privacy.
From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.
From pgg_smc Require Import pgg_tableau_reading pgg_tableau_marginal_bounds.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run pgl27_secrecy.
From pgg_smc Require Import pgl27_trace pgl27_exec pgl27_models.
From pgg_smc Require Import pgl27_proximity.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_secrecy.
From pgg_smc Require Import psl211_models psl211_reading_constancy.
From pgg_smc Require Import psl211_colour_reading.
From pgg_smc Require Import s5_exec s5_mixing s5_models.
From pgg_smc Require Import s5_tableau_sampled.
From pgg_smc Require Import five_card_group five_card_program five_card_kim.
From pgg_smc Require Import five_card_exec five_card_models five_card_mixing.
From pgg_smc Require Import five_card_tableau_sampled.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Notation seatsOf A := ('I_(pi_T' (mp_PI (instance_profile A))).+1).
Local Notation cardsOf A := ('I_(pgg_N' (mp_M (instance_profile A))).+1).
Local Notation cutOf A := (pgg_gT (mp_M (instance_profile A))).


(******************************************************************************)
(*     manifest/pgg_tableau_reading.v                                         *)
(******************************************************************************)

Check @StaticReading : forall A : PGGAlgebraic, ExecutionParams A -> Type.

Check @MkStaticReading
  : forall (A : PGGAlgebraic) (E : ExecutionParams A)
           (readT : {set seatsOf A} -> finType),
      (forall C : {set seatsOf A}, ex_inputT E -> cutOf A -> readT C) ->
      StaticReading E.

Check @sr_readT
  : forall (A : PGGAlgebraic) (E : ExecutionParams A),
      StaticReading E -> {set seatsOf A} -> finType.

Check @sr_read
  : forall (A : PGGAlgebraic) (E : ExecutionParams A) (r : StaticReading E)
           (C : {set seatsOf A}),
      ex_inputT E -> cutOf A -> sr_readT r C.

Check @static_coalition_reading
  : forall (A : PGGAlgebraic) (E : ExecutionParams A), StaticReading E.

Check @static_coalition_readingTE
  : forall (A : PGGAlgebraic) (E : ExecutionParams A) (C : {set seatsOf A}),
      sr_readT (static_coalition_reading E) C
      = [the finType of {ffun seatsOf A -> cardsOf A}].

Check @static_coalition_readE
  : forall (A : PGGAlgebraic) (E : ExecutionParams A) (C : {set seatsOf A})
           (x : ex_inputT E) (g : cutOf A),
      sr_read (static_coalition_reading E) C x g
      = @static_coalition_obs A E C x g.

Check @ReadingIndistinguishabilityPropAt
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (r : StaticReading E)
           (c : R),
      Prop.

Check @reading_indistinguishability_static_coalitionE
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E))
           (cert : IndistinguishabilityCert sa) (c : R),
      ReadingIndistinguishabilityPropAt sa (static_coalition_reading E) c
      = IndistinguishabilityPropAt cert c.

Check @reading_indistinguishability_postprocessing
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (r r' : StaticReading E)
           (f : forall C : {set seatsOf A}, sr_readT r C -> sr_readT r' C),
      (forall (C : {set seatsOf A}) (x : ex_inputT E) (g : cutOf A),
         sr_read r' C x g = f C (sr_read r C x g)) ->
      forall c : R,
        ReadingIndistinguishabilityPropAt sa r c ->
        ReadingIndistinguishabilityPropAt sa r' c.

Check @ReadingExactIndependence
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (r : StaticReading E)
           (secretT : finType) (secret : {RV (sa_sampleP sa) -> secretT}),
      Prop.

Check @exact_independence_of_witness
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (w : ExactWitness sa),
      ReadingExactIndependence sa (static_coalition_reading E) (ew_secret w).

Check @exact_independence_executed_of_reading
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (secretT : finType)
           (secret : {RV (sa_sampleP sa) -> secretT}),
      (forall C : {set seatsOf A},
         @sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C
         = (fun u => @static_coalition_obs A E C (sa.(sa_arg) u)
                       (sa.(sa_cut) u))) ->
      ReadingExactIndependence sa (static_coalition_reading E) secret ->
      forall C : {set seatsOf A},
        (#|C| < profile_k (instance_profile A))%N ->
        sa_sampleP sa
        |= (@sa_coalition_view R (instance_profile A) (instance_exec E)
              sa 0 C)
           _|_ secret.

(* the implicit and explicit split the second probe's call sites depend on *)
Check (fun (A : PGGAlgebraic) (E : ExecutionParams A) => StaticReading E).
Check (fun (A : PGGAlgebraic) (E : ExecutionParams A) (r : StaticReading E)
           (C : {set seatsOf A}) => sr_read r C).
Check (fun (A : PGGAlgebraic) (E : ExecutionParams A) =>
         static_coalition_reading E).
Check (fun (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (r : StaticReading E)
           (secretT : finType) (secret : {RV (sa_sampleP sa) -> secretT}) =>
         ReadingExactIndependence sa r secret).
Check (fun (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (r : StaticReading E)
           (c : R) => ReadingIndistinguishabilityPropAt sa r c).


(******************************************************************************)
(*     manifest/pgg_tableau_marginal_bounds.v                                 *)
(******************************************************************************)

Check @SeatMarginalPropAt
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (i : seatsOf A)
           (ideal : R.-fdist (cardsOf A)) (c : R),
      Prop.

Check @CutMarginalPropAt
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (T : finType)
           (read : cutOf A -> T) (ideal : R.-fdist T) (c : R),
      Prop.

Check @seat_marginal_prop_at2
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (i : seatsOf A)
           (ideal : R.-fdist (cardsOf A)),
      SeatMarginalPropAt sa i ideal 2%:R.

Check @cut_marginal_prop_at2
  : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (T : finType)
           (read : cutOf A -> T) (ideal : R.-fdist T),
      CutMarginalPropAt sa read ideal 2%:R.


(******************************************************************************)
(*     instances/pgl27/pgl27_proximity.v                                      *)
(******************************************************************************)

Check @pgl27_coalition_trace_static_obsE
  : forall (R : realType) (C : {set 'I_8}) (s : bool) (g : pgg_gT pgl27_M),
      pgl27_coalition_trace R C (s, g)
      = @static_coalition_obs pgl27_algebra pgl27_dealt_params C s g.


(******************************************************************************)
(*     instances/s5/tableau/s5_tableau_sampled.v                              *)
(******************************************************************************)

Check @s5_word_seat_marginal
  : forall (R : realType) (secretP : R.-fdist 'I_5) (L : nat)
           (i : seatsOf s5_algebra),
      @SeatMarginalPropAt R s5_algebra s5_dealt_params
        (s5_word_sample secretP L) i (s5_ideal_reading secretP)
        (Num.sqrt 5%:R * (s5_alpha_R R) ^+ L).


(******************************************************************************)
(*     instances/kim2025/tableau/five_card_tableau_sampled.v                  *)
(******************************************************************************)

Check @five_card_repeated_cut_marginal
  : forall (R : realType) (s : 'I_5),
      @CutMarginalPropAt R five_card_algebra five_card_params
        (amf_sample kim_centi_family R tt) 'I_5
        (fun sigma : {perm 'I_5} => sigma s) (fdist_uniform (card_ord 5))
        (2%:R^-40).


(******************************************************************************)
(*     instances/psl211/psl211_colour_reading.v                               *)
(******************************************************************************)

Check @psl211_dealt_inputTE
  : ep_inputT (instance_exec psl211_dealt_params) = bool.

Check @psl211_dealt_sample
  : forall (R : realType) (secretP : R.-fdist bool),
      SampleAdapter R (instance_exec psl211_dealt_params).

Check @psl211_dealt_sample_lawE
  : forall (R : realType) (secretP : R.-fdist bool),
      sa_sampleP (psl211_dealt_sample secretP) = psl211P secretP.

Check @psl211_dealt_sample_argE
  : forall (R : realType) (secretP : R.-fdist bool)
           (u : bool * pgg_gT psl211_M),
      (psl211_dealt_sample secretP).(sa_arg) u = u.1.

Check @psl211_dealt_sample_cutE
  : forall (R : realType) (secretP : R.-fdist bool)
           (u : bool * pgg_gT psl211_M),
      (psl211_dealt_sample secretP).(sa_cut) u = u.2.

Check @psl211_dealt_sample_cut_distE
  : forall (R : realType) (secretP : R.-fdist bool),
      @sa_cut_dist R (instance_profile psl211_algebra)
        (instance_exec psl211_dealt_params) (psl211_dealt_sample secretP)
      = (`U psl211_G_pos : R.-fdist (pgg_gT psl211_M)).

Check @psl211_colour_reading : StaticReading psl211_dealt_params.

Check @psl211_colour_readingE
  : forall (R : realType) (secretP : R.-fdist bool)
           (C : {set seatsOf psl211_algebra})
           (u : bool * pgg_gT psl211_M),
      psl211_colour_view secretP C u
      = sr_read psl211_colour_reading C
          ((psl211_dealt_sample secretP).(sa_arg) u)
          ((psl211_dealt_sample secretP).(sa_cut) u).

Check @psl211_colour_reading_funE
  : forall (R : realType) (secretP : R.-fdist bool)
           (C : {set seatsOf psl211_algebra}),
      psl211_colour_view secretP C
      = (fun u => sr_read psl211_colour_reading C
                    ((psl211_dealt_sample secretP).(sa_arg) u)
                    ((psl211_dealt_sample secretP).(sa_cut) u)).

Check @psl211_colour_of_reading
  : forall C : {set seatsOf psl211_algebra},
      {ffun seatsOf psl211_algebra -> cardsOf psl211_algebra} ->
      {ffun seatsOf psl211_algebra -> bool}.

Check @psl211_colour_reading_factorsE
  : forall (C : {set seatsOf psl211_algebra})
           (b : ex_inputT psl211_dealt_params) (g : cutOf psl211_algebra),
      sr_read psl211_colour_reading C b g
      = psl211_colour_of_reading C
          (sr_read (static_coalition_reading psl211_dealt_params) C b g).

Check @psl211_colour_indistinguishability_of_coalition_reading
  : forall (R : realType) (secretP : R.-fdist bool) (c : R),
      ReadingIndistinguishabilityPropAt (psl211_dealt_sample secretP)
        (static_coalition_reading psl211_dealt_params) c ->
      ReadingIndistinguishabilityPropAt (psl211_dealt_sample secretP)
        psl211_colour_reading c.

Check @psl211_colour_of_reading_collides
  : forall (C : {set seatsOf psl211_algebra}) (i0 : seatsOf psl211_algebra),
      i0 \in C ->
      exists v w : {ffun seatsOf psl211_algebra -> cardsOf psl211_algebra},
        v != w /\ psl211_colour_of_reading C v = psl211_colour_of_reading C w.

Check @psl211_colour_reading_indep
  : forall (R : realType) (secretP : R.-fdist bool),
      ReadingExactIndependence (psl211_dealt_sample secretP)
        psl211_colour_reading (psl211_secret secretP).

Check @psl211_leak_coalition_not_below_k
  : ~~ (#|psl211_leak_coalition|
        < profile_k (instance_profile psl211_algebra))%N.

Check @psl211_colour_reading_dep_k6
  : forall (R : realType) (secretP : R.-fdist bool),
      secretP true != 0 -> secretP false != 0 ->
      (#|psl211_leak_coalition|
       = profile_k (instance_profile psl211_algebra))%N /\
      ~ sa_sampleP (psl211_dealt_sample secretP)
          |= (fun u => sr_read psl211_colour_reading psl211_leak_coalition
                         ((psl211_dealt_sample secretP).(sa_arg) u)
                         ((psl211_dealt_sample secretP).(sa_cut) u))
             _|_ psl211_secret secretP.

Check @psl211_dealt_perdeck_reading
  : forall (R : realType) (secretP : R.-fdist bool),
      {RV (psl211P secretP)
       -> {ffun seatsOf psl211_algebra -> cardsOf psl211_algebra}}.

Check @psl211_dealt_perdeck_readingE
  : forall (R : realType) (secretP : R.-fdist bool),
      (fun u => sr_read (static_coalition_reading psl211_dealt_params)
                  psl211_perdeck_coalition
                  ((psl211_dealt_sample secretP).(sa_arg) u)
                  ((psl211_dealt_sample secretP).(sa_cut) u))
      = psl211_dealt_perdeck_reading secretP.

Check @psl211_dealt_reading_indep_false
  : forall (R : realType) (secretP : R.-fdist bool),
      secretP true != 0 -> secretP false != 0 ->
      ~ ReadingExactIndependence (psl211_dealt_sample secretP)
          (static_coalition_reading psl211_dealt_params)
          (psl211_secret secretP).


(******************************************************************************)
(*     What the landed statements rest on                                     *)
(******************************************************************************)

Print Assumptions psl211_colour_reading_indep.
Print Assumptions psl211_colour_reading_dep_k6.
Print Assumptions psl211_dealt_reading_indep_false.
Print Assumptions psl211_colour_reading_factorsE.
Print Assumptions psl211_colour_indistinguishability_of_coalition_reading.
Print Assumptions pgl27_coalition_trace_static_obsE.
Print Assumptions s5_word_seat_marginal.
Print Assumptions five_card_repeated_cut_marginal.
Print Assumptions seat_marginal_prop_at2.
Print Assumptions cut_marginal_prop_at2.
