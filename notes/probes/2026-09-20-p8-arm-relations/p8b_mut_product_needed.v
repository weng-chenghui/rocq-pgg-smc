(* P8 arm-relations probe, mutation check for B3: B1's product hypothesis is *)
(* what carries a distance on the cut group to a distance between the two    *)
(* joint laws, and without it the inequality is refutable.                   *)
(*                                                                           *)
(* B3 reads: two models sharing the prior on the run argument are no further *)
(* apart in the joint law of reading and argument than their two cut laws    *)
(* are. Drop the assumption that each model's joint law of argument and cut  *)
(* is a product, and the two marginals no longer determine the joint. On the *)
(* two booleans the diagonal law and the antidiagonal law have the same two  *)
(* marginals, the uniform law, so the right side of the inequality is zero;  *)
(* and their supports are disjoint, so by A1 the left side is two.           *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import var_dist_supp.
From p8probe Require Import p8a_degenerate_certificate.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section two_joint_laws_with_one_pair_of_marginals.
Variable R : realType.

(** The diagonal law on the two booleans: the uniform law read as a pair of
    equal coordinates. *)
Definition diagonal_bool2 : R.-fdist (bool * bool) :=
  fdistmap (fun b : bool => (b, b)) (fdist_uniform card_bool).

(** The antidiagonal law: the uniform law read as a pair of opposite
    coordinates. *)
Definition antidiagonal_bool2 : R.-fdist (bool * bool) :=
  fdistmap (fun b : bool => (b, ~~ b)) (fdist_uniform card_bool).

Lemma diagonal_bool2_fstE :
  fdistmap fst diagonal_bool2 = fdist_uniform (R := R) card_bool.
Proof.
rewrite /diagonal_bool2 fdistmap_comp.
by apply: fdistmap_inj_uniform_id => x y /=.
Qed.

Lemma diagonal_bool2_sndE :
  fdistmap snd diagonal_bool2 = fdist_uniform (R := R) card_bool.
Proof.
rewrite /diagonal_bool2 fdistmap_comp.
by apply: fdistmap_inj_uniform_id => x y /=.
Qed.

Lemma antidiagonal_bool2_fstE :
  fdistmap fst antidiagonal_bool2 = fdist_uniform (R := R) card_bool.
Proof.
rewrite /antidiagonal_bool2 fdistmap_comp.
by apply: fdistmap_inj_uniform_id => x y /=.
Qed.

Lemma antidiagonal_bool2_sndE :
  fdistmap snd antidiagonal_bool2 = fdist_uniform (R := R) card_bool.
Proof.
rewrite /antidiagonal_bool2 fdistmap_comp.
by apply: fdistmap_inj_uniform_id => x y /= /negb_inj.
Qed.

(** The two laws are two apart: no pair of booleans carries mass under
    both. *)
Lemma var_dist_diagonal_antidiagonal :
  var_dist diagonal_bool2 antidiagonal_bool2 = 2%:R.
Proof.
apply: var_dist_disjoint_supp_eq2 => -[x y].
case: (eqVneq x y) => [->|Hne].
- right; apply: fdistmap_notin_codom0 => b; rewrite xpair_eqE.
  by case: b; case: y.
- left; apply: fdistmap_notin_codom0 => b; rewrite xpair_eqE.
  apply/negP => /andP[/eqP Hb1 /eqP Hb2].
  by move: Hne; rewrite -Hb1 -Hb2 eqxx.
Qed.

(** The mutation check for B3: with the product hypothesis dropped, two joint
    laws sharing both marginals are not within their cut distance of each
    other. *)
Lemma joint_le_cut_without_product_false :
  ~ (forall (T G : finType) (P Q : R.-fdist (T * G)),
       fdistmap fst P = fdistmap fst Q ->
       fdistmap snd P = fdistmap snd Q ->
       var_dist P Q <= var_dist (fdistmap snd P) (fdistmap snd Q)).
Proof.
move=> H.
have Hf : fdistmap fst diagonal_bool2 = fdistmap fst antidiagonal_bool2.
  by rewrite diagonal_bool2_fstE antidiagonal_bool2_fstE.
have Hs : fdistmap snd diagonal_bool2 = fdistmap snd antidiagonal_bool2.
  by rewrite diagonal_bool2_sndE antidiagonal_bool2_sndE.
have H2 := H bool bool diagonal_bool2 antidiagonal_bool2 Hf Hs.
move: H2; rewrite var_dist_diagonal_antidiagonal.
rewrite diagonal_bool2_sndE antidiagonal_bool2_sndE var_dist_self => H2.
have Hlt : (0 : R) < 2%:R by rewrite ltr0n.
move: (Order.POrderTheory.le_lt_trans H2 Hlt).
by rewrite Order.POrderTheory.ltxx.
Qed.

End two_joint_laws_with_one_pair_of_marginals.
