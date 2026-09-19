(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* var_dist_supp: variation distance under a reader separating the supports   *)
(*                                                                            *)
(* var_dist_fdistmap_inj, the equality case of the data processing            *)
(* inequality var_dist_fdistmap, asks that the reader be injective on the     *)
(* whole domain. A reader of the form sigma |-> sigma s on a permutation      *)
(* group is not, so that case carries no distance between two laws on the     *)
(* group back from a bound on the reading of one card position. Weakening     *)
(* the hypothesis to the union of the two supports restores the transport,    *)
(* and that is the form in which a per-position number becomes a number       *)
(* about the group. Beside it sit the ceiling a published variation           *)
(* distance is read against, the invariance of a uniform law under an         *)
(* injective endomap, and the fact that a pushforward charges only the        *)
(* image.                                                                     *)
(*                                                                            *)
(* The second group moves a distance between two probability models of one    *)
(* execution between the carriers on which it is proved and stated. A         *)
(* shuffle bound is proved on the cut group; what a coalition is shown is a   *)
(* bound on the pair of its reading and the secret. Data processing carries   *)
(* the distance down to that pair, because reading and secret are both        *)
(* functions of one sample point, and the product laws carry it up from the   *)
(* cut, because a model whose run argument is drawn independently of its cut  *)
(* has a joint law of argument and cut that is a product. The last lemma      *)
(* removes the ideal model from such a comparison at three times the number,  *)
(* leaving a statement about the actual model alone.                          *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   var_dist_le2               == a variation distance is at most two        *)
(*   var_dist_fdistmap_supp_inj == a reader separating the points that carry  *)
(*                                 mass transports the distance exactly       *)
(*   fdistmap_inj_uniform_id    == an injective endomap fixes the uniform law *)
(*   fdistmap_neq0_codom        == a pushforward charges only the image       *)
(*   var_dist_fdistmap_pair     == two laws on one sample space stay within   *)
(*                                 their distance when read as a reading and  *)
(*                                 a secret                                   *)
(*   var_dist_prodR             == two products with one left factor are as   *)
(*                                 far apart as their right factors           *)
(*   var_dist_prodL             == the same on the other side                 *)
(*   fdist_prod_snd             == the second marginal of a product is its    *)
(*                                 second factor                              *)
(*   var_dist_own_marginals     == a joint law close to a product law is      *)
(*                                 close to the product of its own marginals  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp reals lra.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_collusion_bound.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     The ceiling of a variation distance                                    *)
(******************************************************************************)

(** The variation distance between two laws on a finite carrier is at most
    two, since it is the sum of the absolute differences and each law sums to
    one. It is the scale a published number is read against: a certificate
    says something about a coalition's two readings exactly in so far as its
    number is below two, and the total variation distance of the literature
    is half of this quantity. *)
Lemma var_dist_le2 (R : realType) (A : finType) (P Q : R.-fdist A) :
  var_dist P Q <= 2%:R.
Proof.
have Hf1 : forall d : R.-fdist A, \sum_(a : A) d a = 1.
  by move=> d; rewrite -(FDist.f1 d); apply: eq_bigl => a; rewrite inE.
rewrite /var_dist.
have -> : (2%:R : R) = \sum_(a : A) (P a + Q a).
  by rewrite big_split /= !Hf1 mulr2n.
apply: ler_sum => a _.
rewrite -[X in _ <= X + _](ger0_norm (FDist.ge0 P a)).
rewrite -[X in _ <= _ + X](ger0_norm (FDist.ge0 Q a)).
exact: ler_normB.
Qed.

(******************************************************************************)
(*     Transport of the distance along a reader injective on the supports     *)
(******************************************************************************)

Section var_dist_supp_inj.
Variable R : realType.

(** A reader that separates the points carrying mass transports the
    variation distance exactly. It is var_dist_fdistmap_inj, the equality
    case of the data processing inequality var_dist_fdistmap, with
    injectivity weakened from the whole domain to the union of the two
    supports. The weakening is what a cut law needs: the inequality runs from
    the group to the reading, and a certificate states its bound on the
    reading and owes it on the group. *)
Lemma var_dist_fdistmap_supp_inj (A B : finType) (f : A -> B)
    (P Q : R.-fdist A) :
  (forall a b : A, (P a != 0) || (Q a != 0) ->
     (P b != 0) || (Q b != 0) -> f a = f b -> a = b) ->
  var_dist (fdistmap f P) (fdistmap f Q) = var_dist P Q.
Proof.
move=> Hinj.
rewrite /var_dist (partition_big f xpredT) //=.
apply: eq_bigr => b _.
rewrite !fdistmapE.
have Hsimp : forall d : R.-fdist A,
    \sum_(a in A | a \in f @^-1 b) d a = \sum_(a | f a == b) d a.
  by move=> d; apply: eq_bigl => a /=; rewrite inE.
rewrite !Hsimp -sumrB.
have Hzero : forall a : A, ~~ ((P a != 0) || (Q a != 0)) -> P a - Q a = 0.
  by move=> a; rewrite negb_or !negbK => /andP[/eqP-> /eqP->]; rewrite subrr.
case: (boolP [exists a : A, (f a == b) && ((P a != 0) || (Q a != 0))]).
  case/existsP => a0 /andP[Ha0 Hs0].
  have Hrest : forall a : A, (f a == b) && (a != a0) -> P a - Q a = 0.
    move=> a /andP[Ha Hne]; apply: Hzero; apply/negP => Hs.
    have Hf : f a = f a0 by rewrite (eqP Ha) (eqP Ha0).
    by move: Hne; rewrite (Hinj a a0 Hs Hs0 Hf) eqxx.
  rewrite (bigD1 a0) /=; last exact: Ha0.
  rewrite big1; last exact: Hrest.
  rewrite addr0 [in RHS](bigD1 a0) /=; last exact: Ha0.
  rewrite big1 ?addr0 // => a Ha.
  by rewrite Hrest // normr0.
move/existsPn => Hno.
have Hall : forall a : A, f a == b -> P a - Q a = 0.
  move=> a Ha; apply: Hzero; apply/negP => Hs.
  by move: (Hno a); rewrite Ha Hs.
rewrite big1; last exact: Hall.
rewrite normr0 big1 // => a Ha.
by rewrite Hall // normr0.
Qed.

End var_dist_supp_inj.

(******************************************************************************)
(*     A bijective reader on one finite type keeps a law uniform              *)
(******************************************************************************)

(** An injective endomap of a finite type leaves the uniform law fixed. It is
    the endomap case of fdistmap_inj_uniform, whose conclusion is uniform on
    the image and which does not simplify back to the uniform law when the
    two types differ. The ideal cut of the five-card instance is uniform on
    the rotations, and one card position of it is read by such an endomap, so
    the ideal cut read at a position is the uniform law a marginal bound is
    stated against. *)
Lemma fdistmap_inj_uniform_id (R : realType) (A : finType) (n : nat)
    (cA : #|A| = n.+1) (f : A -> A) :
  injective f ->
  fdistmap f (fdist_uniform cA) = fdist_uniform cA :> R.-fdist A.
Proof.
move=> Hinj; have [g fg gf] := injF_bij Hinj.
apply/fdist_ext => b; rewrite fdistmapE.
rewrite (bigD1 (g b)) /=; last by rewrite inE /= gf.
rewrite big1; last first.
  move=> a /andP[]; rewrite inE /= => /eqP Ha Hne.
  by move: Hne; rewrite -(fg a) Ha eqxx.
by rewrite addr0 !fdist_uniformE.
Qed.

(** A pushforward gives mass only to points in the image of the map. It is how
    the support of a cut law defined as a word-shuffle pushforward is read off
    the word evaluation. *)
Lemma fdistmap_neq0_codom (R : realType) (A B : finType) (f : A -> B)
    (P : R.-fdist A) (b : B) :
  fdistmap f P b != 0 -> exists a : A, f a = b.
Proof.
move=> H; case: (boolP [exists a : A, f a == b]).
  by case/existsP => a /eqP Ha; exists a.
move/existsPn => Hno; exfalso; move/negP: H; apply; apply/eqP.
have Hsimp : \sum_(a in A | a \in f @^-1 b) P a = \sum_(a | f a == b) P a.
  by apply: eq_bigl => a /=; rewrite inE.
rewrite fdistmapE Hsimp big1 // => a Ha.
by move: (Hno a); rewrite Ha.
Qed.

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
    bound on the joint law of argument and cut. Two section-local proofs of
    this statement predate the one here, at instances/pgl27/pgl27_mixing.v and
    instances/psl211/psl211_mixing.v; each is used once, inside its own file's
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

(** The second marginal of a product law is its second factor. infotheo's
    fdist_prod1 states this for the first marginal of a product with a
    channel, and the second marginal of such a product is a mixture, so the
    statement for a constant channel has no counterpart there. *)
Lemma fdist_prod_snd (P : R.-fdist A) (Q : R.-fdist B) :
  fdistmap snd (P `x Q) = Q.
Proof. by rewrite -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1. Qed.

End var_dist_product_factor.

(******************************************************************************)
(*     A joint law against the product of its own marginals                   *)
(******************************************************************************)

(** A joint law within d of a product of two laws is within three times d of
    the product of its own two marginals. Each marginal of the joint law is
    within d of the corresponding factor by data processing, and replacing the
    two factors one at a time costs d each, so the number is spent three
    times. It is what turns a statement comparing two models into a statement
    about one, at a constant no reader has to trace back to the ideal. *)
Lemma var_dist_own_marginals (R : realType) (V W : finType)
    (J : R.-fdist (V * W)) (Mr : R.-fdist V) (Ms : R.-fdist W) (d : R) :
  var_dist J (Mr `x Ms) <= d ->
  var_dist J ((fdistmap fst J) `x (fdistmap snd J)) <= 3%:R * d.
Proof.
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
