(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* five_card_mixing: the five-card cut laws against the uniform rotation law  *)
(*                                                                            *)
(* Kim's two cut laws and den Boer's ideal cut are all carried by the five    *)
(* powers of one five-cycle, and in that group one card position determines   *)
(* the cut. A number stated at one card position is therefore already a       *)
(* number about the cut law itself, which is what a comparison with an ideal  *)
(* cut asks for and what a per-position marginal bound alone does not give.   *)
(* Beside that distance sits the second premise of such a comparison: den     *)
(* Boer's encoding fixes the colour census of the dealt row at three hearts   *)
(* and two clubs, so the card a coalition of at most one seat reads under     *)
(* the ideal cut has the same law at both committed pairs.                    *)
(*                                                                            *)
(* Those two are the base premises of the certificates the analysis manifest  *)
(* records for Kim's one-cut and seven-cut rows. The constancy is exact and   *)
(* is quantified over every coalition below the privacy threshold and over    *)
(* both committed pairs; the distance is where the two rows' published        *)
(* numbers come from. Each law is given in the two forms the rows use, the    *)
(* bundle's own spectral number and the constant a text quotes.               *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   kim_biased_marginal_bound == the one-cut law's marginal bound at the     *)
(*                                bundle's spectral number                    *)
(*   kim_centi_marginal_bound40 == the seven-cut law's marginal bound at the  *)
(*                                 constant 2^-40                             *)
(*   kim_biased_marginal_bound_exact == the one-cut law's marginal bound at   *)
(*                                      the exact number one fiftieth         *)
(*                                                                            *)
(* Key results:                                                               *)
(*   fc_sigma_pow_point_inj == two rotations agreeing at one card position    *)
(*                             are equal                                      *)
(*   fc_kim_rho_supp_pow == every cut a Kim word shuffle charges is a         *)
(*                          rotation                                          *)
(*   five_card_ideal_point_uniform == one card position of the ideal cut      *)
(*                                    carries the uniform law                 *)
(*   five_card_cut_mixing_of_supp_pow == a cut law carried by the rotations   *)
(*                                       is within its own per-position       *)
(*                                       bound of the ideal cut               *)
(*   kim_centi_cut_mixing == the seven-cut law is within the bundle's         *)
(*                           spectral number of the ideal cut                 *)
(*   kim_biased_cut_mixing == the one-cut law likewise at word length one     *)
(*   den_boer_layout_law_const == the card at a uniformly chosen position     *)
(*                                has one law at every committed pair         *)
(*   five_card_static_obs_const == a coalition below the privacy threshold    *)
(*                                 reads the ideal cut alike at both          *)
(*                                 committed pairs                            *)
(*   kim_centi_cut_mixing40 == the same distance at the constant 2^-40        *)
(*   kim_biased_cut_mixing_exact == the same at the exact one fiftieth        *)
(******************************************************************************)

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
From kim_landing_probe Require Import var_dist_supp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     A rotation is determined by one card position                          *)
(******************************************************************************)

(** fc_sigma_pow5_eq1 — the fifth power of the five-cycle is the identity, so
    the order of the rotation group divides five. It is what makes the
    exponent of a cut a residue modulo five, and so what lets the exponent be
    read back from the image of a single card position. *)
Lemma fc_sigma_pow5_eq1 : (fc_sigma ^+ 5 = 1)%g.
Proof.
apply/permP => i; rewrite perm1; apply: val_inj.
rewrite /= fc_sigma_pow_val modnDr modn_small //.
exact: ltn_ord.
Qed.

(** fc_sigma_pow_point_inj — two powers of the five-cycle that agree at one
    card position are equal: the stabiliser of a position in the rotation
    group is trivial. This is the step that carries a statement about the law
    of one card position back to the law of the cut that produced it, which
    is what a comparison with an ideal cut needs and a per-position marginal
    bound does not supply. *)
Lemma fc_sigma_pow_point_inj (s : 'I_5) (j k : nat) :
  (fc_sigma ^+ j)%g s = (fc_sigma ^+ k)%g s ->
  (fc_sigma ^+ j = fc_sigma ^+ k)%g.
Proof.
move=> /(congr1 val); rewrite !fc_sigma_pow_val => /eqP.
rewrite eqn_modDl => /eqP Hjk.
by rewrite -(expg_mod j fc_sigma_pow5_eq1) -(expg_mod k fc_sigma_pow5_eq1) Hjk.
Qed.

(** fc_sigma_pow_ord_inj — the five rotation amounts send one card position to
    five distinct positions. It is the injectivity the uniform law on
    rotation amounts is pushed forward along, so one card position read under
    the ideal cut carries the uniform law on positions. *)
Lemma fc_sigma_pow_ord_inj (s : 'I_5) :
  injective (fun k : 'I_5 => (fc_sigma ^+ k)%g s).
Proof.
move=> j k /(congr1 val); rewrite !fc_sigma_pow_val => H.
apply: val_inj => /=.
move: H => /eqP; rewrite eqn_modDl => /eqP.
by rewrite !modn_small ?ltn_ord.
Qed.

(******************************************************************************)
(*     The three cut laws are carried by the rotations                        *)
(******************************************************************************)

(** fc_kim_word_eval_powE — a word over Kim's alphabet evaluates to the
    rotation by the sum of its letters. The alphabet is the five powers of
    one five-cycle, so a word shuffle never leaves the rotation group however
    long the word is, and one statement at arbitrary length covers every Kim
    cut law. *)
Lemma fc_kim_word_eval_powE (L : nat) (w : L.-tuple 'I_5) :
  @word_eval (Gen_PGGTypes fc_kim_gens) L w
  = (fc_sigma ^+ (\sum_(i < L) \val (tnth w i)))%g.
Proof.
rewrite /word_eval.
transitivity (\prod_(i < L) (fc_sigma ^+ \val (tnth w i)))%g.
  by apply: eq_bigr => i _; exact: fc_kim_gensE.
by rewrite -(big_morph _ (expgD fc_sigma) (expg0 fc_sigma)).
Qed.

(** fc_kim_rho_supp_pow — every cut the weighted word shuffle gives mass to is
    a power of the five-cycle, at every word length and every letter
    weighting. Both quantifiers are Kim's: the bias fixes the letter
    weighting and the number of cuts fixes the word length. The two Kim cut
    laws this development carries share the bias one hundredth and differ
    only at word lengths one and seven, so each of them and the uniform
    rotation law live on one group and a variation distance between them is a
    distance on that group. *)
Lemma fc_kim_rho_supp_pow (R : realType) (L : nat) (W : R.-fdist 'I_5)
    (g : {perm 'I_5}) :
  @rho_from_words_weighted R 3 4 L fc_kim_gens W g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.
Proof.
rewrite /rho_from_words_weighted => /fdistmap_neq0_codom [w Hw].
by exists (\sum_(i < L) \val (tnth w i)); rewrite -Hw fc_kim_word_eval_powE.
Qed.

(** five_card_ideal_supp_pow — every cut the den Boer model's ideal gives mass
    to is a power of the five-cycle. The ideal is the uniform law on the five
    rotation amounts pushed along k |-> fc_sigma ^+ k, which is
    five_card_sample_cut_distE, so the ideal and every Kim cut law are
    carried by one group and a variation distance between them is a distance
    on that group. *)
Lemma five_card_ideal_supp_pow (R : realType) (g : {perm 'I_5}) :
  sa_cut_dist (five_card_sample R) g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.
Proof.
have Hid : sa_cut_dist (five_card_sample R)
    = fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g) (fdist_uniform (card_ord 5)).
  exact: five_card_sample_cut_distE.
rewrite Hid => /fdistmap_neq0_codom [k Hk].
by exists (\val k); rewrite -Hk.
Qed.

(** five_card_ideal_point_uniform — one card position of the ideal cut carries
    the uniform law on card positions. This is the law a shuffle's marginal
    bound is stated against, so it is where a certificate's number and the
    ideal cut meet. *)
Lemma five_card_ideal_point_uniform (R : realType) (s : 'I_5) :
  fdistmap (fun g : {perm 'I_5} => g s) (sa_cut_dist (five_card_sample R))
  = fdist_uniform (card_ord 5).
Proof.
have Hid : sa_cut_dist (five_card_sample R)
    = fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g) (fdist_uniform (card_ord 5)).
  exact: five_card_sample_cut_distE.
rewrite Hid fdistmap_comp.
by apply: fdistmap_inj_uniform_id; exact: fc_sigma_pow_ord_inj.
Qed.

(******************************************************************************)
(*     The two Kim cut laws                                                   *)
(******************************************************************************)

Section kim_cut_supports.
Variable R : realType.

(** kim_single_cut_supp_pow — Kim's cut law at word length one gives mass only
    to powers of the five-cycle. Its distance to the ideal is therefore a
    distance inside the rotation group, where one card position determines
    the cut. *)
Lemma kim_single_cut_supp_pow (g : {perm 'I_5}) :
  sw_rho_dist (scb_bound (@fc_kim_security_bundle R (1 / 100)
    (kim_centi_lt R) (kim_centi_gt R) (kim_centi_spec R) 1)) g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.
Proof. exact: fc_kim_rho_supp_pow. Qed.

(** kim_centi_cut_supp_pow — Kim's cut law at word length seven gives mass
    only to powers of the five-cycle. The repeated row's distance to the
    ideal is therefore a distance inside the rotation group. *)
Lemma kim_centi_cut_supp_pow (g : {perm 'I_5}) :
  sw_rho_dist (scb_bound (kim_security_bundle_centi R)) g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.
Proof. exact: fc_kim_rho_supp_pow. Qed.

End kim_cut_supports.

(******************************************************************************)
(*     The colour census of den Boer's deck                                   *)
(******************************************************************************)

(** fc_arrange_countE — counting a colour in den Boer's dealt row gives the
    same number at every committed pair: three hearts and two clubs. The
    colour census is the coarsening of the deal that the two bits leave
    fixed, and the level at which a single seat's reading stops depending on
    them. *)
Lemma fc_arrange_countE (a b : bool) (p : pred bool) :
  count p (fc_arrange a b) = count p [:: true; true; true; false; false].
Proof.
by case: a; case: b; rewrite /fc_arrange /fc_negate /fc_encode /=;
   case: (p true); case: (p false).
Qed.

Section five_card_colour_census.
Variable R : realType.

(** den_boer_layout_law_const — the card at a uniformly chosen position has
    the same law at every committed pair. The arrangement moves with the two
    bits and the colour census does not, and this is that census read as the
    law of the card drawn. It is the level at which the two run arguments of
    a certificate's constancy field become indistinguishable to a single
    seat. *)
Lemma den_boer_layout_law_const (x x' : bool * bool) :
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
by rewrite /den_boer_layout /= count_map fc_arrange_countE.
Qed.

(******************************************************************************)
(*     The ideal cut's reading does not depend on the committed pair          *)
(******************************************************************************)

(** five_card_static_obs_const — the privacy threshold is two, so a coalition
    below it is empty or holds one seat. At every such coalition the static
    endpoint reading of the uniform rotation law has the same law at both
    committed pairs. One seat reads one card of a deck whose colour census
    den Boer's encoding fixes at three hearts and two clubs, so the reading
    cannot separate the pairs. This is the constancy field of the spectral
    certificate, and it is exact. It spends no mixing bound. *)
Lemma five_card_static_obs_const
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
have Hst :
    forall i : 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1,
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
by rewrite (den_boer_layout_law_const x x').
Qed.

End five_card_colour_census.

(******************************************************************************)
(*     The distance on the cut group, from the distance at one position       *)
(******************************************************************************)

Section five_card_cut_mixing.
Variable R : realType.

(** five_card_cut_mixing_of_supp_pow — a cut law carried by the powers of the
    five-cycle is within its own per-position bound of the uniform rotation
    law, as a distance on the cut group itself. The stabiliser of a card
    position in the rotation group is trivial, so reading one position loses
    nothing between two laws both carried by the rotations, and the number a
    shuffle certificate states about one card position is already the
    group-level number a comparison with an ideal cut asks for. *)
Lemma five_card_cut_mixing_of_supp_pow
    (b : ShuffleMarginalBound R (instance_M five_card_algebra)) :
  (forall g : {perm 'I_5}, sw_rho_dist b g != 0 ->
     exists k : nat, g = (fc_sigma ^+ k)%g) ->
  var_dist (sw_rho_dist b) (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps b.
Proof.
move=> Hsupp.
have Hinj : forall g h : {perm 'I_5},
    (sw_rho_dist b g != 0) || (sa_cut_dist (five_card_sample R) g != 0) ->
    (sw_rho_dist b h != 0) || (sa_cut_dist (five_card_sample R) h != 0) ->
    g ord0 = h ord0 -> g = h.
  move=> g h /orP Hg /orP Hh Hgh.
  have [jg Hjg] : exists k : nat, g = (fc_sigma ^+ k)%g.
    by case: Hg => [/Hsupp//|/five_card_ideal_supp_pow].
  have [jh Hjh] : exists k : nat, h = (fc_sigma ^+ k)%g.
    by case: Hh => [/Hsupp//|/five_card_ideal_supp_pow].
  rewrite Hjg Hjh; apply: (@fc_sigma_pow_point_inj ord0).
  by rewrite -Hjg -Hjh.
rewrite -(var_dist_fdistmap_supp_inj Hinj) five_card_ideal_point_uniform.
exact: (sw_bound b ord0).
Qed.

(******************************************************************************)
(*     The repeated row, at the seven-cut bundle                              *)
(******************************************************************************)

(** kim_centi_cut_mixing — the seven-cut law of Kim's repeated row is within
    the bundle's own spectral number of the uniform rotation law, in
    variation distance on the cut group. This is the mixing field of the
    spectral certificate for that row. The number is the bundle's and no new
    one is introduced, so the row's only inexact quantity is that spectral
    number. *)
Lemma kim_centi_cut_mixing :
  var_dist (sw_rho_dist (scb_bound (kim_security_bundle_centi R)))
           (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps (scb_bound (kim_security_bundle_centi R)).
Proof.
by apply: five_card_cut_mixing_of_supp_pow; exact: kim_centi_cut_supp_pow.
Qed.

(******************************************************************************)
(*     The biased row, at the word-length-one bundle                          *)
(******************************************************************************)

(** kim_biased_marginal_bound — the marginal bound Kim's bundle carries at
    bias one hundredth and word length one. It bounds, at every card
    position, the distance between the law that position takes under one
    biased cut and the uniform law, which is the form a comparison with an
    ideal cut turns into a distance on the cut group. *)
Definition kim_biased_marginal_bound
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  scb_bound (@fc_kim_security_bundle R (1 / 100)
               (kim_centi_lt R) (kim_centi_gt R) (kim_centi_spec R) 1).

(** kim_biased_cut_mixing — Kim's one-cut law is within the bundle's own
    spectral number of the uniform rotation law, in variation distance on the
    cut group. This is the mixing field of the spectral certificate for the
    one-cut row, at a number of hundredth scale rather than a cryptographic
    one. *)
Lemma kim_biased_cut_mixing :
  var_dist (sw_rho_dist kim_biased_marginal_bound)
           (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps kim_biased_marginal_bound.
Proof.
by apply: five_card_cut_mixing_of_supp_pow; exact: kim_single_cut_supp_pow.
Qed.

End five_card_cut_mixing.

(******************************************************************************)
(*     The same two distances at the constants the two rows republish         *)
(******************************************************************************)

(** kim_centi_marginal_bound40 — the seven-cut law's marginal bound with its
    number written as the constant two to the minus fortieth rather than as
    the spectral expression. The per-card-position proof is the tree's own
    kim_deal_centi_lt weakened to a non-strict inequality, so the record
    asserts nothing new. This is the shape PGL(2,7)'s word row carries, and
    the shape a published constant needs. *)
Definition kim_centi_marginal_bound40 (R : realType)
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  @MkShuffleMarginalBound R FiveCardKim_M 7 (2%:R ^- 40)
    (sw_rho_dist (scb_bound (kim_security_bundle_centi R)))
    (fun s => Order.POrderTheory.ltW (kim_deal_centi_lt R s)).

(** kim_centi_cut_mixing40 — the seven-cut law is within the constant two to
    the minus fortieth of the uniform rotation law, in variation distance on
    the cut group. It is the mixing field of the repeated row's certificate
    at the constant bound. *)
Lemma kim_centi_cut_mixing40 (R : realType) :
  var_dist (sw_rho_dist (kim_centi_marginal_bound40 R))
           (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps (kim_centi_marginal_bound40 R).
Proof.
by apply: five_card_cut_mixing_of_supp_pow; exact: kim_centi_cut_supp_pow.
Qed.

(** kim_one_cut_centi_le — one card position of Kim's one-cut law is within
    one fiftieth of the uniform law on card positions. kim_one_cut_centiE
    makes this an equality, so the one-cut row can publish the distance
    itself instead of the spectral overestimate. *)
Lemma kim_one_cut_centi_le (R : realType) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
              (@rho_from_words_weighted R 3 4 1 fc_kim_gens
                 (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R))))
           (fdist_uniform (card_ord 5)) <= 1 / 50 :> R.
Proof. by rewrite kim_one_cut_centiE. Qed.

(** kim_biased_marginal_bound_exact — the one-cut law's marginal bound at the
    exact number one fiftieth. *)
Definition kim_biased_marginal_bound_exact (R : realType)
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  @MkShuffleMarginalBound R FiveCardKim_M 1 (1 / 50)
    (@rho_from_words_weighted R 3 4 1 fc_kim_gens
       (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R)))
    (fun s => kim_one_cut_centi_le R s).

(** kim_biased_cut_mixing_exact — Kim's one-cut law is within one fiftieth of
    the uniform rotation law, in variation distance on the cut group. It is
    the mixing field of the one-cut row's certificate at the exact number. *)
Lemma kim_biased_cut_mixing_exact (R : realType) :
  var_dist (sw_rho_dist (kim_biased_marginal_bound_exact R))
           (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps (kim_biased_marginal_bound_exact R).
Proof.
by apply: five_card_cut_mixing_of_supp_pow; exact: fc_kim_rho_supp_pow.
Qed.
