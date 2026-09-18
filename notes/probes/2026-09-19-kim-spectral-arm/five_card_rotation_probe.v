(* PROBE, notes/probes/2026-09-19-kim-spectral-arm/                           *)
(* five_card_rotation_probe.v                                                 *)
(* Ledger row S2 of notes/20260919-kim-spectral-arm-probe-design.md.          *)

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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     The rotations act regularly on the card positions                      *)
(******************************************************************************)

(* The five-cycle has order dividing five. It is the fact that makes the
   exponent of a cut a residue modulo five, so that the cut group of the
   five-card instance has exactly the five elements the deck has positions. *)
Lemma fc_sigma_pow5 : (fc_sigma ^+ 5 = 1)%g.
Proof.
apply/permP => i; rewrite perm1; apply: val_inj.
rewrite /= fc_sigma_pow_val modnDr modn_small //.
exact: ltn_ord.
Qed.

(* A rotation is determined by where it sends one position. This is
   regularity of the cyclic action, and it is what lets a statement about the
   reading of a single seat be carried back to the cut that produced it. *)
Lemma fc_rot_pow_faithful (s : 'I_5) (j k : nat) :
  (fc_sigma ^+ j)%g s = (fc_sigma ^+ k)%g s ->
  (fc_sigma ^+ j = fc_sigma ^+ k)%g.
Proof.
move=> /(congr1 val); rewrite !fc_sigma_pow_val => /eqP.
rewrite eqn_modDl => /eqP Hjk.
by rewrite -(expg_mod j fc_sigma_pow5) -(expg_mod k fc_sigma_pow5) Hjk.
Qed.

(* Reading one position separates the five rotation amounts. It is the same
   regularity, stated on the exponents, and it is the injectivity the uniform
   rotation law is pushed forward along. *)
Lemma fc_rot_point_inj (s : 'I_5) :
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

(* A word over Kim's alphabet evaluates to the rotation by the sum of its
   letters. The alphabet is the five powers of one five-cycle, so a word
   shuffle never leaves the cyclic group however long the word is. *)
Lemma fc_word_eval_pow (L : nat) (w : L.-tuple 'I_5) :
  @word_eval (Gen_PGGTypes fc_kim_gens) L w
  = (fc_sigma ^+ (\sum_(i < L) \val (tnth w i)))%g.
Proof.
rewrite /word_eval.
transitivity (\prod_(i < L) (fc_sigma ^+ \val (tnth w i)))%g.
  by apply: eq_bigr => i _; exact: fc_kim_gensE.
by rewrite -(big_morph _ (expgD fc_sigma) (expg0 fc_sigma)).
Qed.

(* Every cut the weighted word shuffle gives mass to is a rotation, at every
   word length and every letter weighting. The three cut laws of the
   five-card instance are instances of this one law, so the support fact
   below is stated once. *)
Lemma rho_words_rot_supp (R : realType) (L : nat) (W : R.-fdist 'I_5)
    (g : {perm 'I_5}) :
  @rho_from_words_weighted R 3 4 L fc_kim_gens W g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.
Proof.
rewrite /rho_from_words_weighted => /fdistmap_supp [w Hw].
by exists (\sum_(i < L) \val (tnth w i)); rewrite -Hw fc_word_eval_pow.
Qed.

(* The uniform rotation law of the den Boer model, as a pushforward of the
   uniform law on rotation amounts. *)
Lemma five_card_ideal_distE (R : realType) :
  sa_cut_dist (five_card_sample R)
  = fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g) (fdist_uniform (card_ord 5)).
Proof. exact: five_card_sample_cut_distE. Qed.

(* The uniform rotation law is carried by the rotations. *)
Lemma five_card_ideal_rot_supp (R : realType) (g : {perm 'I_5}) :
  sa_cut_dist (five_card_sample R) g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.
Proof.
rewrite five_card_ideal_distE => /fdistmap_supp [k Hk].
by exists (\val k); rewrite -Hk.
Qed.

(* Reading one seat of the uniform rotation law gives the uniform law on card
   positions. This is the law the marginal bound of a shuffle is stated
   against, so it is the point at which the certificate's number and the
   ideal cut meet. *)
Lemma five_card_ideal_point_uniform (R : realType) (s : 'I_5) :
  fdistmap (fun g : {perm 'I_5} => g s) (sa_cut_dist (five_card_sample R))
  = fdist_uniform (card_ord 5).
Proof.
rewrite five_card_ideal_distE fdistmap_comp.
by apply: fdistmap_inj_uniform_id; exact: fc_rot_point_inj.
Qed.

(******************************************************************************)
(*     The two Kim cut laws                                                   *)
(******************************************************************************)

Section kim_cut_supports.
Variable R : realType.

(* The one-biased-cut law is carried by the rotations. *)
Lemma kim_single_rot_supp (g : {perm 'I_5}) :
  sw_rho_dist (scb_bound (@fc_kim_security_bundle R (1 / 100)
    (kim_centi_lt R) (kim_centi_gt R) (kim_centi_spec R) 1)) g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.
Proof. exact: rho_words_rot_supp. Qed.

(* The seven-biased-cut law is carried by the rotations. *)
Lemma kim_centi_rot_supp (g : {perm 'I_5}) :
  sw_rho_dist (scb_bound (kim_security_bundle_centi R)) g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.
Proof. exact: rho_words_rot_supp. Qed.

End kim_cut_supports.

Print Assumptions fc_rot_pow_faithful.
Print Assumptions rho_words_rot_supp.
Print Assumptions five_card_ideal_point_uniform.
Print Assumptions kim_centi_rot_supp.
