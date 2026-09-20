(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* fdist_prod_cst_cond: constant conditional laws and constant random         *)
(* variables                                                                  *)
(*                                                                            *)
(* A model that draws two coordinates apart and shows a function of the pair  *)
(* tells an observer nothing about the first coordinate when the reading's    *)
(* conditional law does not move with that coordinate.                        *)
(* fdistmap_pair_fst_prodE states the direction a privacy argument uses: from *)
(* constancy of the conditional law to a joint law of the reading and the     *)
(* first coordinate that is the product of its two marginals. That product is *)
(* the right-hand side an ideal-proximity comparison is stated against, and   *)
(* an ideal model built by drawing a run argument apart from a cut is where   *)
(* it is applied. The three equations before it are the mass computations of  *)
(* its proof: the fibre of the reading over one value of the first            *)
(* coordinate, the joint mass there, and the law of the reading alone as a    *)
(* mixture of its conditional laws.                                           *)
(*                                                                            *)
(* inde_RV_cst is the same conclusion in the case where the coordinate the    *)
(* reading is compared against is one value. A constant random variable is    *)
(* independent of every other, so a constant secret satisfies the             *)
(* independence field of an exact witness over any model whatever, and        *)
(* carrying such a witness is by itself no statement about the model.         *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   inde_RV_cst             == a random variable with one value is           *)
(*                              independent of every random variable on the   *)
(*                              same space                                    *)
(*   sum_prod_fibreE         == the mass of one value of the reading and one  *)
(*                              value of the first coordinate under a product *)
(*   fdistmap_pair_fst_condE == the joint law of the reading and the first    *)
(*                              coordinate under a product law                *)
(*   fdistmap_prod_mixtureE  == the law of the reading alone is the mixture   *)
(*                              of its conditional laws                       *)
(*   fdistmap_pair_fst_prodE == a reading whose conditional law is one law is *)
(*                              independent of the first coordinate           *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     A random variable with one value                                       *)
(******************************************************************************)

(** A random variable with one value is independent of every random variable
    on the same space. It is what makes a constant secret a legal
    independence field of an exact witness over an arbitrary model, so the
    existence of such a witness is by itself no statement about the model. *)
Lemma inde_RV_cst (R : realType) (U : finType) (P : R.-fdist U)
    (TA TB : finType) (X : {RV P -> TA}) (c : TB) :
  P |= X _|_ ((fun=> c) : {RV P -> TB}).
Proof.
move=> x y; rewrite !pfwd1E.
case: (eqVneq y c) => [->|Hne].
- have -> : finset (preim ((fun=> c) : U -> TB) (pred1 c)) = setT.
    by apply/setP => u; rewrite !inE eqxx.
  rewrite Pr_setT mulr1; congr (Pr P _).
  by apply/setP => u; rewrite !inE /= xpair_eqE eqxx andbT.
- have -> : finset (preim ((fun=> c) : U -> TB) (pred1 y)) = set0.
    by apply/setP => u; rewrite !inE /= eq_sym (negbTE Hne).
  have -> : finset (preim [% X, ((fun=> c) : {RV P -> TB})] (pred1 (x, y)))
            = set0.
    apply/setP => u; rewrite !inE /= xpair_eqE.
    by rewrite [c == y]eq_sym (negbTE Hne) andbF.
  by rewrite !Pr_set0 mulr0.
Qed.

(******************************************************************************)
(*     A reading of a product law with a constant conditional law             *)
(******************************************************************************)

Section fdist_prod_cst_cond.
Variable R : realType.
Variables T G V : finType.
Variables (PT : R.-fdist T) (Q : R.-fdist G) (f : T -> G -> V).

(** The mass a product law puts on one value of the reading together with one
    value of the first coordinate: the mass of that coordinate times the mass
    its own conditional reading law puts on the value. *)
Lemma sum_prod_fibreE (v : V) (x : T) :
  \sum_(z : T * G | (f z.1 z.2 == v) && (z.1 == x)) PT z.1 * Q z.2
  = PT x * fdistmap (f x) Q v.
Proof.
rewrite (reindex_onto (fun g : G => (x, g)) snd) /=;
  last by case=> a g /= /andP[_ /eqP ->].
rewrite -big_distrr /=; congr (_ * _).
by rewrite fdistmapE; apply: eq_bigl => g; rewrite !inE /= !eqxx !andbT.
Qed.

(** The joint law of the reading and the first coordinate under a product
    law, point by point. *)
Lemma fdistmap_pair_fst_condE (v : V) (x : T) :
  fdistmap (fun z : T * G => (f z.1 z.2, z.1)) (PT `x Q) (v, x)
  = PT x * fdistmap (f x) Q v.
Proof.
rewrite fdistmapE -sum_prod_fibreE; apply: eq_big.
- by case=> a g; rewrite !inE /= xpair_eqE.
- by move=> i _; rewrite fdist_prodE.
Qed.

(** The law of the reading alone under a product law: the mixture of its
    conditional laws over the first coordinate, weighted by that
    coordinate's own law. *)
Lemma fdistmap_prod_mixtureE (v : V) :
  fdistmap (fun z : T * G => f z.1 z.2) (PT `x Q) v
  = \sum_(x : T) PT x * fdistmap (f x) Q v.
Proof.
rewrite fdistmapE.
rewrite (eq_big (fun z : T * G => f z.1 z.2 == v)
                (fun z : T * G => PT z.1 * Q z.2)); first last.
- by move=> i _; rewrite fdist_prodE.
- by case=> a g; rewrite !inE.
rewrite (partition_big fst xpredT) //=.
by apply: eq_bigr => x _; exact: sum_prod_fibreE.
Qed.

(** A reading whose conditional law does not move with the first coordinate
    is independent of that coordinate: the joint law of the two is the
    product of its two marginals. On an ideal model that draws a run argument
    apart from a cut, the constancy hypothesis is the ideal reading's
    constancy in the run argument, and the conclusion is the product the
    ideal-proximity proposition compares an actual joint law against. *)
Lemma fdistmap_pair_fst_prodE :
  (forall x x' : T, fdistmap (f x) Q = fdistmap (f x') Q) ->
  fdistmap (fun z : T * G => (f z.1 z.2, z.1)) (PT `x Q)
  = (fdistmap (fun z : T * G => f z.1 z.2) (PT `x Q)) `x PT.
Proof.
move=> Hc; apply/fdist_ext => -[v x].
have Hf1 : \sum_(x' : T) PT x' = 1.
  by rewrite -(FDist.f1 PT); apply: eq_bigl => a; rewrite inE.
rewrite fdist_prodE /= fdistmap_pair_fst_condE fdistmap_prod_mixtureE.
under eq_bigr do rewrite (Hc _ x).
by rewrite -big_distrl /= Hf1 mul1r mulrC.
Qed.

End fdist_prod_cst_cond.
