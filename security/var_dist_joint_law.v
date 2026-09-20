(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* var_dist_joint_law: the sum of absolute differences between joint laws     *)
(*                                                                            *)
(* A shuffle bound is proved on the cut group. What a coalition is shown is a *)
(* bound on the pair of its reading and the secret. The two carriers are not  *)
(* the same, and the lemmas here are the steps between them. Each distance    *)
(* step is stated on the sum of the absolute differences of two laws, which   *)
(* is twice the total variation distance of the literature and bounds twice a *)
(* distinguisher's advantage. fdist_prod_snd is the marginal identity those   *)
(* steps consume.                                                             *)
(*                                                                            *)
(* Downward, var_dist_fdistmap_pair carries a bound from any common carrier   *)
(* to the pair, because a coalition's reading and the secret are both         *)
(* functions of one sample point. Upward, var_dist_prodR and var_dist_prodL   *)
(* carry a bound from one factor of a product to the product, because a model *)
(* whose run argument is drawn independently of its cut has a joint law of    *)
(* argument and cut that is a product, and tensoring with a common factor     *)
(* neither creates nor destroys the sum. fdist_prod_snd names the second      *)
(* marginal of such a product. var_dist_own_marginals removes the second      *)
(* model from the comparison: a joint law within a number of some product is  *)
(* within three times that number of the product of its own two marginals, so *)
(* a statement comparing two models becomes a statement about one.            *)
(*                                                                            *)
(* The two variation-distance lemmas this file takes from the tree,           *)
(* var_dist_fdistmap and var_dist_triangle, are stated in                     *)
(* security/pgg_collusion_bound.v, so the file sits above that one and not in *)
(* lib/, which carries no dependency on security/.                            *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   var_dist_fdistmap_pair     == two laws on one sample space stay within   *)
(*                                 their bound when read as a reading and a   *)
(*                                 secret                                     *)
(*   var_dist_prodR             == two products with a common left factor are *)
(*                                 exactly as far apart as their right        *)
(*                                 factors                                    *)
(*   var_dist_prodL             == the same on the other side                 *)
(*   fdist_prod_snd             == the second marginal of a product is its    *)
(*                                 second factor                              *)
(*   var_dist_fdistmap_prodR_le == one map applied to two products with a     *)
(*                                 common left factor keeps the two right     *)
(*                                 factors' bound                             *)
(*   var_dist_own_marginals     == a joint law within a number of a product   *)
(*                                 law is within three times that number of   *)
(*                                 the product of its own marginals           *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp reals lra.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import var_dist_supp pgg_collusion_bound.

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
    data processing along the map pairing the two readers, and it is the step
    by which a proximity certificate's ipc_close field is discharged: the
    actual and the ideal model of one execution differ only in the law they
    draw a sample point from, and the pair ipc_close compares is a
    deterministic function of that point. *)
Lemma var_dist_fdistmap_pair (R : realType) (U V W : finType)
    (P Q : R.-fdist U) (reading : U -> V) (secret : U -> W) (d : R) :
  var_dist P Q <= d ->
  var_dist (fdistmap (fun u => (reading u, secret u)) P)
           (fdistmap (fun u => (reading u, secret u)) Q) <= d.
Proof.
(* var_dist_fdistmap at (reading, secret), then transitivity. *)
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
    independently of it therefore neither creates nor destroys the sum, which
    is what lets a bound proved on the cut group be read as a bound on the
    joint law of argument and cut. Two files carry a section-local proof of
    the same statement, instances/pgl27/pgl27_mixing.v and
    instances/psl211/psl211_mixing.v. Each is used once, inside that file's
    joint mixing lemma, and neither is visible outside it. *)
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
    are as far apart as their left factors. The statement about the actual
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

(** The second marginal of a product law is its second factor. It is the
    second half of the identification a comparison with an ideal makes: the
    ideal's joint law is a product, so each of its marginals is one of the two
    laws the ideal was built from, and var_dist_own_marginals needs both
    halves. infotheo's fdist_prod1 gives the first half for a product with a
    channel, where the second marginal is a mixture and has no counterpart. *)
Lemma fdist_prod_snd (P : R.-fdist A) (Q : R.-fdist B) :
  fdistmap snd (P `x Q) = Q.
Proof. by rewrite -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1. Qed.

End var_dist_product_factor.

(******************************************************************************)
(*     One reading of two products sharing their left factor                  *)
(******************************************************************************)

(** One map applied to two product laws sharing their left factor gives two
    laws no further apart than the two right factors. It is the general core
    of the step that carries a bound on a model's cut law to a bound on the
    joint law of a coalition's reading and the model's run argument: the
    shared left factor is the prior on the run argument, the two right
    factors are the actual and the ideal cut law, and the map is the pair of
    the reading and the argument, a deterministic function of the pair. *)
Lemma var_dist_fdistmap_prodR_le (R : realType) (A B C : finType)
    (P : R.-fdist A) (Q1 Q2 : R.-fdist B) (h : A * B -> C) :
  var_dist (fdistmap h (P `x Q1)) (fdistmap h (P `x Q2)) <= var_dist Q1 Q2.
Proof.
(* Data processing along h, then var_dist_prodR removes the shared factor. *)
apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)).
by rewrite var_dist_prodR.
Qed.

(******************************************************************************)
(*     A joint law against the product of its own marginals                   *)
(******************************************************************************)

(** A joint law within d of a product of two laws is within three times d of
    the product of its own two marginals. It is what turns a statement
    comparing two models into a statement about one, at a constant no reader
    has to trace back to the ideal. *)
Lemma var_dist_own_marginals (R : realType) (V W : finType)
    (J : R.-fdist (V * W)) (Mr : R.-fdist V) (Ms : R.-fdist W) (d : R) :
  var_dist J (Mr `x Ms) <= d ->
  var_dist J ((fdistmap fst J) `x (fdistmap snd J)) <= 3%:R * d.
Proof.
(* The hypothesis gives the first hop. Each marginal of the joint law is within
   d of the corresponding factor by data processing, so replacing the two
   factors one at a time gives the other two, and the three hops each lose at
   most d, so the total is 3 * d. *)
move=> H.
have Hfst : fdistmap fst (Mr `x Ms) = Mr by exact: fdist_prod1.
have Hsnd : fdistmap snd (Mr `x Ms) = Ms by exact: fdist_prod_snd.
have Hr : var_dist Mr (fdistmap fst J) <= d.
  rewrite symmetric_var_dist -Hfst.
  exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) H).
have Hs : var_dist Ms (fdistmap snd J) <= d.
  rewrite symmetric_var_dist -Hsnd.
  exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) H).
have H3 : (3%:R : R) * d = d + (d + d) by lra.
rewrite H3.
apply: (Order.POrderTheory.le_trans (var_dist_triangle _ (Mr `x Ms) _)).
apply: lerD; first exact: H.
apply: (Order.POrderTheory.le_trans
          (var_dist_triangle _ (Mr `x (fdistmap snd J)) _)).
by apply: lerD; [rewrite var_dist_prodR | rewrite var_dist_prodL].
Qed.
