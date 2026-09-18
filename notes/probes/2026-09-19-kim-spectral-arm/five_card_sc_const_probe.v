(* PROBE, notes/probes/2026-09-19-kim-spectral-arm/                           *)
(* five_card_sc_const_probe.v                                                 *)
(* Ledger row S5 of notes/20260919-kim-spectral-arm-probe-design.md.          *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import morphism.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_collusion_bound.
From pgg_smc Require Import pgg_weighted_words.
From pgg_smc Require Import pgg_monodromy_profile.
From pgg_smc Require Import pgg_instance pgg_functionality pgg_sample_adapter.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_encoding den_boer_profile.
From pgg_smc Require Import five_card_exec five_card_models.
From pgg_reconstruct Require Import algebraic_rigidity.
From kim_spectral_arm_probe Require Import var_dist_injective_probe.
From kim_spectral_arm_probe Require Import five_card_rotation_probe.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     The colour census of den Boer's deck                                   *)
(******************************************************************************)

(* Every committed pair is dealt as the same multiset of cards: three hearts
   and two clubs. The arrangement moves with the bits and the census does
   not, which is the whole of what makes one revealed card carry nothing. *)
Lemma fc_arrange_count (a b : bool) (p : pred bool) :
  count p (fc_arrange a b) = count p [:: true; true; true; false; false].
Proof.
by case: a; case: b; rewrite /fc_arrange /fc_negate /fc_encode /=;
   case: (p true); case: (p false).
Qed.

Section five_card_sc_const.
Variable R : realType.

(* The card at a uniformly chosen position has the same law at every
   committed pair. It is the census above read as a distribution, and it is
   the level at which the two run arguments of the spectral arm become
   indistinguishable. *)
Lemma den_boer_layout_law (x x' : bool * bool) :
  fdistmap (tnth (den_boer_layout x)) (fdist_uniform (card_ord 5))
  = fdistmap (tnth (den_boer_layout x')) (fdist_uniform (card_ord 5))
  :> R.-fdist 'I_5.
Proof.
apply/fdist_ext => c.
have Hval : forall y : bool * bool,
    fdistmap (tnth (den_boer_layout y)) (fdist_uniform (card_ord 5)) c
    = #|[pred k : 'I_5 | tnth (den_boer_layout y) k == c]|%:R * 5%:R^-1 :> R.
  move=> y; rewrite fdistmapE.
  rewrite (eq_bigl (fun k : 'I_5 => tnth (den_boer_layout y) k == c));
    last by move=> k /=; rewrite inE.
  under eq_bigr do rewrite fdist_uniformE card_ord.
  rewrite -sum1_card natr_sum mulr_suml.
  apply: eq_big => [k|k _]; first by rewrite inE.
  by rewrite mulr1n mul1r.
suff Hc : forall y : bool * bool,
    #|[pred k : 'I_5 | tnth (den_boer_layout y) k == c]|
    = count (preim encode_bool (fun z : 'I_5 => z == c))
            [:: true; true; true; false; false].
  by rewrite !Hval !Hc.
move=> y.
rewrite (card_tnth_count (den_boer_layout y) (fun z : 'I_5 => z == c)).
by rewrite /den_boer_layout /= count_map fc_arrange_count.
Qed.

(******************************************************************************)
(*     S5: the ideal cut's reading does not depend on the committed pair      *)
(******************************************************************************)

(* Below the privacy threshold, a coalition reads the same law from the
   uniform rotation law at every committed pair. The threshold is two, so the
   coalition is empty or one seat, and one seat reads one position of a deck
   whose colour census the encoding fixes. This is the fifth field of a
   SpectralCert for the five-card instance, and it is exact: it spends no
   mixing bound. *)
Lemma five_card_sc_const
    (C : {set 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1}) :
  (#|C| < profile_k (instance_profile five_card_algebra))%N ->
  forall x x' : ex_inputT five_card_params,
    fdistmap (@static_coalition_obs five_card_algebra five_card_params C x)
             (sa_cut_dist (five_card_sample R))
    = fdistmap (@static_coalition_obs five_card_algebra five_card_params C x')
               (sa_cut_dist (five_card_sample R)).
Proof.
move=> HC x x'.
have HC2 : (#|C| < 2)%N := HC.
have Hst : forall i : 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1,
    tnth (pi_starts (mp_PI (instance_profile five_card_algebra))) i = i.
  by move=> i; rewrite tnth_ord_tuple.
case/boolP: (C == set0) => [/eqP HC0|HCn].
  have Hf : @static_coalition_obs five_card_algebra five_card_params C x
          = @static_coalition_obs five_card_algebra five_card_params C x'.
    apply: boolp.funext => g; apply/ffunP => i.
    by rewrite !static_coalition_obsE HC0 inE.
  by rewrite Hf.
have /cards1P[i0 Hi0] : #|C| == 1.
  by rewrite eqn_leq -ltnS HC2 lt0n cards_eq0 HCn.
pose fill := fun v : 'I_5 =>
  [ffun i : 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1 =>
     if i \in C then v else ord0].
have Hfac : forall y : bool * bool,
    @static_coalition_obs five_card_algebra five_card_params C y
    = fill \o tnth (den_boer_layout y) \o (fun g : {perm 'I_5} => g i0).
  move=> y; apply: boolp.funext => g; apply/ffunP => i.
  rewrite static_coalition_obsE /= /fill ffunE.
  case: ifPn => // iC.
  have Hii : i = i0 by apply/eqP; move: iC; rewrite Hi0 inE.
  by rewrite Hst Hii.
rewrite !Hfac -!fdistmap_comp five_card_ideal_point_uniform.
by rewrite (den_boer_layout_law x x').
Qed.

End five_card_sc_const.

Print Assumptions den_boer_layout_law.
Print Assumptions five_card_sc_const.
