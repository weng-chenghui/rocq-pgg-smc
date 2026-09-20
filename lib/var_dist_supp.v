(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* var_dist_supp: variation distance under a reader separating the supports   *)
(*                                                                            *)
(* var_dist_fdistmap_inj, the equality case of the data processing inequality *)
(* var_dist_fdistmap, asks that the reader be injective on the whole domain.  *)
(* A reader of the form sigma |-> sigma s on a permutation group is not, so   *)
(* that case carries no distance between two laws on the group back from a    *)
(* bound on the reading of one card position. Weakening the hypothesis to the *)
(* union of the two supports restores the transport, and that is the form in  *)
(* which a per-position number becomes a number about the group. Beside it    *)
(* sit the scale a published variation distance is read against, the          *)
(* invariance of a uniform law under an injective endomap, the fact that a    *)
(* pushforward is supported in the image, and the distance between the point  *)
(* mass at true on the booleans and the uniform law there.                    *)
(* security/var_dist_joint_law.v carries the distance between two joint laws  *)
(* of a reading and a secret.                                                 *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   var_dist_le2               == a variation distance is at most two        *)
(*   var_dist_fdistmap_supp_inj == a reader separating the points that carry  *)
(*                                 mass transports the distance exactly       *)
(*   fdistmap_inj_uniform_id    == an injective endomap fixes the uniform law *)
(*   fdistmap_neq0_codom        == a pushforward is supported in the image    *)
(*   var_dist_fdist1_uniform    == the point mass at true and the uniform law *)
(*                                 on the booleans are one apart              *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp reals lra.
From infotheo Require Import realType_ext fdist proba variation_dist.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     The bound two on a variation distance                                  *)
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
    reading and must establish it on the group. *)
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
(*     The point mass at true against the uniform law on the booleans         *)
(******************************************************************************)

(** The distance between the point mass at true on the booleans and the
    uniform law on the booleans, in the sum of absolute differences: one.
    Pushing two joint laws of a reading and a secret along the secret
    coordinate leaves the two laws of the secret and can only shorten the
    distance, so a proximity number between two models whose secrets are
    drawn from these two laws is at least one, whatever the rest of the two
    executions does. *)
Lemma var_dist_fdist1_uniform (R : realType) :
  var_dist (fdist1 true : R.-fdist bool) (fdist_uniform (R := R) card_bool)
  = 1.
Proof.
have Hu : forall b : bool, (fdist_uniform (R := R) card_bool) b = 2%:R^-1.
  by move=> b; rewrite fdist_uniformE card_bool.
have H2 : (0:R) < 2%:R by rewrite ltr0n.
have Hhalf : (0:R) <= 2%:R^-1 by rewrite invr_ge0 ler0n.
have Hle1 : 2%:R^-1 <= (1:R) by rewrite invf_le1 // ler1n.
have Ht : (fdist1 true : R.-fdist bool) true = 1 by rewrite fdist1E eqxx.
have Hf : (fdist1 true : R.-fdist bool) false = 0.
  by rewrite fdist1E.
have E1 : `|(1:R) - 2%:R^-1| = 1 - 2%:R^-1 by rewrite ger0_norm ?subr_ge0.
have E2 : `|(0:R) - 2%:R^-1| = 2%:R^-1 by rewrite sub0r normrN ger0_norm.
rewrite /var_dist big_bool /= !Hu Ht Hf E1 E2.
by lra.
Qed.
