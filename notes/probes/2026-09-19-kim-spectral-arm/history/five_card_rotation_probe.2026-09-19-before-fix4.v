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
(*     A rotation is determined by one card position                          *)
(******************************************************************************)

(* The fifth power of the five-cycle is the identity, so the order of the
   rotation group divides five. It is what makes the exponent of a cut a
   residue modulo five, and so what lets the exponent be read back from the
   image of a single card position. *)
Lemma fc_sigma_pow5_eq1 : (fc_sigma ^+ 5 = 1)%g.
Proof.
apply/permP => i; rewrite perm1; apply: val_inj.
rewrite /= fc_sigma_pow_val modnDr modn_small //.
exact: ltn_ord.
Qed.

(* Two powers of the five-cycle that agree at one card position are equal:
   the stabiliser of a position in the rotation group is trivial. This is
   the step that carries a statement about the law of one card position
   back to the law of the cut that produced it, which is what the spectral
   arm needs and a per-position marginal bound does not supply. *)
Lemma fc_sigma_pow_point_inj (s : 'I_5) (j k : nat) :
  (fc_sigma ^+ j)%g s = (fc_sigma ^+ k)%g s ->
  (fc_sigma ^+ j = fc_sigma ^+ k)%g.
Proof.
move=> /(congr1 val); rewrite !fc_sigma_pow_val => /eqP.
rewrite eqn_modDl => /eqP Hjk.
by rewrite -(expg_mod j fc_sigma_pow5_eq1) -(expg_mod k fc_sigma_pow5_eq1) Hjk.
Qed.

(* The five rotation amounts send one card position to five distinct
   positions. It is the injectivity the uniform law on rotation amounts is
   pushed forward along, so one card position read under the ideal cut
   carries the uniform law on positions. *)
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

(* A word over Kim's alphabet evaluates to the rotation by the sum of its
   letters. The alphabet is the five powers of one five-cycle, so a word
   shuffle never leaves the rotation group however long the word is, and
   one statement at arbitrary length covers every Kim cut law. *)
Lemma fc_kim_word_eval_powE (L : nat) (w : L.-tuple 'I_5) :
  @word_eval (Gen_PGGTypes fc_kim_gens) L w
  = (fc_sigma ^+ (\sum_(i < L) \val (tnth w i)))%g.
Proof.
rewrite /word_eval.
transitivity (\prod_(i < L) (fc_sigma ^+ \val (tnth w i)))%g.
  by apply: eq_bigr => i _; exact: fc_kim_gensE.
by rewrite -(big_morph _ (expgD fc_sigma) (expg0 fc_sigma)).
Qed.

(* Every cut the weighted word shuffle gives mass to is a power of the
   five-cycle, at every word length and every letter weighting. The
   quantifier over the weighting is what lets one statement cover all of
   Kim's cut laws, so each of them and the uniform rotation law live on one
   group and a variation distance between them is a distance on that
   group. *)
Lemma fc_kim_rho_supp_pow (R : realType) (L : nat) (W : R.-fdist 'I_5)
    (g : {perm 'I_5}) :
  @rho_from_words_weighted R 3 4 L fc_kim_gens W g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.
Proof.
rewrite /rho_from_words_weighted => /fdistmap_neq0_codom [w Hw].
by exists (\sum_(i < L) \val (tnth w i)); rewrite -Hw fc_kim_word_eval_powE.
Qed.

(* Every cut the den Boer model's ideal gives mass to is a power of the
   five-cycle. The ideal is the uniform law on the five rotation amounts
   pushed along k |-> fc_sigma ^+ k, which is five_card_sample_cut_distE,
   so the ideal and every Kim cut law are carried by one group and a
   variation distance between them is a distance on that group. *)
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

(* One card position of the ideal cut carries the uniform law on card
   positions. This is the law a shuffle's marginal bound is stated against,
   so it is where the certificate's number and the ideal cut meet. *)
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

(* Kim's cut law at word length one gives mass only to powers of the
   five-cycle. Its distance to the ideal is therefore a distance inside the
   rotation group, where one card position determines the cut. *)
Lemma kim_single_cut_supp_pow (g : {perm 'I_5}) :
  sw_rho_dist (scb_bound (@fc_kim_security_bundle R (1 / 100)
    (kim_centi_lt R) (kim_centi_gt R) (kim_centi_spec R) 1)) g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.
Proof. exact: fc_kim_rho_supp_pow. Qed.

(* Kim's cut law at word length seven gives mass only to powers of the
   five-cycle. The repeated row's distance to the ideal is therefore a
   distance inside the rotation group. *)
Lemma kim_centi_cut_supp_pow (g : {perm 'I_5}) :
  sw_rho_dist (scb_bound (kim_security_bundle_centi R)) g != 0 ->
  exists k : nat, g = (fc_sigma ^+ k)%g.
Proof. exact: fc_kim_rho_supp_pow. Qed.

End kim_cut_supports.

Print Assumptions fc_sigma_pow_point_inj.
Print Assumptions fc_kim_rho_supp_pow.
Print Assumptions five_card_ideal_point_uniform.
Print Assumptions kim_centi_cut_supp_pow.
