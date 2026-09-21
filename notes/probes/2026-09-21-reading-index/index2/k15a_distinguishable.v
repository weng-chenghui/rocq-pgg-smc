(* Probe B, ledger row K15: the card-identity sentence of the fixed-dealer
   twelve-card model, as an obstruction.

   The question the spec asks is whether there is a number above zero, a
   coalition below the privacy threshold and two run arguments whose default
   readings are that far apart under the fixed-dealer model.  There are: the
   number is the reciprocal of the order of the shuffle group, the coalition
   is the three positions psl211_perdeck_coalition, and the two run arguments
   are the two chiralities.  The encoder decks of the two chiralities reach
   one card-identity reading under exactly one cut and under none, which is
   psl211_dealt_raw_countE, so the two pushforwards of the model's own cut law
   differ at that reading by the mass of one cut.

   This is not psl211_dealt_reading_indep_false, which is a failed
   independence and exhibits no pair of run arguments.  It is the counting
   that lemma's proof rests on, read as a distance. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec.
From pgg_smc Require Import psl211_secrecy psl211_models.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax pgg_tableau_reading.
From pgg_smc Require Import psl211_reading_constancy psl211_colour_reading.
From reading_index Require Import k12_k14_psl211.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Notation cutT := (pgg_gT (mp_M (instance_profile psl211_algebra))).

(******************************************************************************)
(*     The two chiralities are read apart at three positions                  *)
(******************************************************************************)

(* The fixed-dealer model is input distinguishable at the coalition's own
   endpoint reading, at the reciprocal of the order of the shuffle group.
   The coalition is three of the twelve positions, below the threshold of
   six, and the two run arguments are the two chiralities of one deal: the
   encoder deck of one puts the three cards of psl211_dealt_view under
   exactly one cut and the other under none, so the two pushforwards of the
   uniform cut law differ at that reading by one cut's mass, and the sum of
   absolute differences is at least that.

   Each mass is pinned in a goal naming one chirality, and the two are
   brought together in term mode: a rewrite with the mass lemma in a goal
   holding both chiralities searches a goal holding both deck tables. *)
Lemma psl211_dealt_input_distinguishable (R : realType)
    (secretP : R.-fdist bool) :
  InputDistinguishabilityPropAt (psl211_dealt_sample secretP)
    (coalition_endpoint_reading psl211_algebra)
    ((#|pgg_G psl211_M|%:R)^-1 : R).
Proof.
have [Ht Hf] := psl211_dealt_raw_countE.
have Ct : #|psl211_dealt_fiber true| = 0 :=
  etrans (psl211_dealt_fiberE true) Ht.
have Cf : #|psl211_dealt_fiber false| = 1 :=
  etrans (psl211_dealt_fiberE false) Hf.
have Ut : (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
    psl211_perdeck_coalition true) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_dealt_view = 0 :> R.
  by rewrite psl211_dealt_massE Ct mulr0n.
have Uf : (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
    psl211_perdeck_coalition false) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_dealt_view = (#|pgg_G psl211_M|%:R)^-1 :> R.
  by rewrite psl211_dealt_massE Cf mulr1n.
have Hle : ((#|pgg_G psl211_M|%:R)^-1 : R)
  <= var_dist
       (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
          psl211_perdeck_coalition true) ((`U psl211_G_pos) : R.-fdist cutT))
       (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
          psl211_perdeck_coalition false) ((`U psl211_G_pos) : R.-fdist cutT)).
  apply: (Order.POrderTheory.le_trans _ (leq_var_dist _ _ psl211_dealt_view)).
  rewrite Ut Uf sub0r normrN ger0_norm ?invr_ge0 ?ler0n //.
(* the goal the existential leaves reads the coalition's endpoints through
   the identity reading, and the two masses above are stated at the bare
   reader.  The identification is one iota step and one eta step and is
   discharged here, in a statement naming one chirality, rather than left to
   the conversion that closes the goal: a goal holding both chiralities and
   both deck tables is the shape that does not return *)
Time have Hred (b : bool) :
    (fun g : cutT => @er_of_endpoints psl211_algebra
        (coalition_endpoint_reading psl211_algebra) psl211_perdeck_coalition
        (@static_coalition_obs psl211_algebra psl211_dealt_params
           psl211_perdeck_coalition b g))
  = @static_coalition_obs psl211_algebra psl211_dealt_params
      psl211_perdeck_coalition b.
  exact: erefl.
exists psl211_perdeck_coalition, true, false.
split; first exact: psl211_perdeck_coalition_below_k.
Time rewrite (Hred true) (Hred false).
Time rewrite (psl211_dealt_sample_cut_distE secretP).
Time exact: Hle.
Qed.

