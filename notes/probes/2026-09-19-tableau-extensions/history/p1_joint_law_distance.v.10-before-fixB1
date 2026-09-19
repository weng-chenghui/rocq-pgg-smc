(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P1: the distance between two models' joint laws                      *)
(*                                                                            *)
(* The proximity arm compares two probability models of one execution on the  *)
(* pair of a coalition's reading and the secret. An instance proves its two   *)
(* models close on the cut group, where a shuffle bound lives, and owes the   *)
(* distance on that pair. The two lemmas here are the two halves of the step  *)
(* between those carriers. Data processing carries a distance down from any   *)
(* common carrier to the pair, because reading and secret are both functions  *)
(* of one sample point. The product laws carry it up from the cut: a model    *)
(* whose run argument is drawn independently of its cut has a joint law of    *)
(* argument and cut that is a product, and two such models sharing an         *)
(* argument law are exactly as far apart as their cut laws.                   *)
(*                                                                            *)
(* var_dist_prodR is Local in instances/pgl27/pgl27_mixing.v and in           *)
(* instances/psl211/psl211_mixing.v, so it is restated here rather than       *)
(* imported; a landing would make one copy global beside var_dist_le2 in      *)
(* lib/var_dist_supp.v. The two facts about a product's marginals below it    *)
(* are stated for the same reason: infotheo has fdist_prod1 for the first     *)
(* marginal of a product and no counterpart for the second.                   *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   var_dist_fdistmap_pair == two laws on one sample space stay within their *)
(*                             distance when read as a reading and a secret   *)
(*   var_dist_prodR         == two products with one left factor are as far   *)
(*                             apart as their right factors                   *)
(*   var_dist_prodL         == the same on the other side                     *)
(*   fdist_prod_snd         == the second marginal of a product is its second *)
(*                             factor                                         *)
(*   fdist_uniform_prod     == the uniform law on a product is the product of *)
(*                             the uniform laws                              *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset bigop order.
From mathcomp Require Import ssrnum ssralg boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_collusion_bound.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     Down to the pair of a reading and a secret                             *)
(******************************************************************************)

(** Two laws on one sample space, within d of each other, stay within d when
    each is read as the pair of a coalition's reading and the secret. It is
    the data processing inequality var_dist_fdistmap at the map pairing the
    two readers, and it is the step by which the proximity arm's certificate
    is discharged: the actual and the ideal model of one execution differ only
    in the law they draw a sample point from, and the pair the arm compares is
    a deterministic function of that point. *)
Lemma var_dist_fdistmap_pair (R : realType) (U V W : finType)
    (P Q : R.-fdist U) (reading : U -> V) (secret : U -> W) (d : R) :
  var_dist P Q <= d ->
  var_dist (fdistmap (fun u => (reading u, secret u)) P)
           (fdistmap (fun u => (reading u, secret u)) Q) <= d.
Proof.
move=> H.
exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) H).
Qed.

(******************************************************************************)
(*     Up from one factor of a product law                                    *)
(******************************************************************************)

Section var_dist_product_factor.
Variable R : realType.
Variables A B : finType.

(** Two product laws with the same left factor are exactly as far apart as
    their right factors. Tensoring a shuffle law with a run argument drawn
    independently of it therefore neither creates nor destroys variation
    distance, which is what lets a bound proved on the cut group be read as a
    bound on the joint law of argument and cut. *)
Lemma var_dist_prodR (P : R.-fdist A) (Q1 Q2 : R.-fdist B) :
  var_dist (P `x Q1) (P `x Q2) = var_dist Q1 Q2.
Proof.
rewrite /var_dist.
under eq_bigr => ab _ do
  rewrite !fdist_prodE -mulrBr normrM (ger0_norm (FDist.ge0 P ab.1)).
rewrite -(pair_bigA _ (fun a b => P a * `|Q1 b - Q2 b|)) /=.
rewrite exchange_big /=.
apply: eq_bigr => b _.
by rewrite -big_distrl /= FDist.f1 mul1r.
Qed.

(** The same on the other side: two product laws with the same right factor
    are as far apart as their left factors. The corollary about the actual
    model alone needs both sides, because it moves from the ideal model's two
    marginals to the actual model's one marginal at a time. *)
Lemma var_dist_prodL (P1 P2 : R.-fdist A) (Q : R.-fdist B) :
  var_dist (P1 `x Q) (P2 `x Q) = var_dist P1 P2.
Proof.
rewrite /var_dist.
under eq_bigr => ab _ do
  rewrite !fdist_prodE -mulrBl normrM (ger0_norm (FDist.ge0 Q ab.2)).
rewrite -(pair_bigA _ (fun a b => `|P1 a - P2 a| * Q b)) /=.
apply: eq_bigr => a _.
by rewrite -big_distrr /= FDist.f1 mulr1.
Qed.

(** The second marginal of a product law is its second factor. infotheo's
    fdist_prod1 states this for the first marginal of a product with a
    channel, and the second marginal of such a product is a mixture, so the
    statement for a constant channel has no counterpart there. *)
Lemma fdist_prod_snd (P : R.-fdist A) (Q : R.-fdist B) :
  fdistmap snd (P `x Q) = Q.
Proof. by rewrite -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1. Qed.

(** The uniform law on a product of two finite types is the product of the two
    uniform laws. It is what makes a sample space written as one uniform law
    on a pair usable by the two lemmas above, which ask for a product. *)
Lemma fdist_uniform_prod (k m n : nat) (cAB : #|{: A * B}| = k.+1)
    (cA : #|A| = m.+1) (cB : #|B| = n.+1) :
  fdist_uniform cAB = ((fdist_uniform cA) `x (fdist_uniform cB))
    :> R.-fdist (A * B).
Proof.
apply/fdist_ext => ab.
by rewrite fdist_prodE !fdist_uniformE card_prod natrM invfM.
Qed.

End var_dist_product_factor.
