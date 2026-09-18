(* PROBE, notes/probes/2026-09-19-kim-spectral-arm/                           *)
(* var_dist_injective_probe.v                                                 *)
(* Ledger row S1 of notes/20260919-kim-spectral-arm-probe-design.md.          *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_collusion_bound.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(******************************************************************************)
(*     What the tree already carries                                          *)
(******************************************************************************)

(* The data processing inequality and its equality case at a globally
   injective reader. A reader of the form sigma |-> sigma s on a permutation
   group is not globally injective, so neither statement decides a distance
   between two laws carried by one regular orbit from a bound on the reading
   of one position. *)
Check var_dist_fdistmap.
Check var_dist_fdistmap_inj.

(******************************************************************************)
(*     Transport of the distance along a reader injective on the supports     *)
(******************************************************************************)

Section var_dist_supp_inj.
Variable R : realType.

(* A reader that separates the points carrying mass transports the variation
   distance exactly. It is the equality case of the data processing
   inequality with injectivity weakened from the whole domain to the union of
   the two supports. The weakening is what a cut law needs: the inequality
   runs from the group to the reading, and a certificate states its bound on
   the reading and owes it on the group. *)
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
(*     Mutation: the same equality at a reader that separates nothing         *)
(******************************************************************************)

(* At a constant reader the equality fails, and it fails by the whole
   distance: two distinct point masses coincide on the image. This is the
   boundary the support hypothesis above draws. *)
Lemma var_dist_const_reader_false (R : realType) :
  var_dist (fdistmap (fun _ : bool => tt) (fdist1 true : R.-fdist bool))
           (fdistmap (fun _ : bool => tt) (fdist1 false))
  <> var_dist (fdist1 true : R.-fdist bool) (fdist1 false).
Proof.
by rewrite !fdistmap1 var_dist_refl => /esym/def_var_dist/fdist1_inj H.
Qed.

(* The script of var_dist_fdistmap_supp_inj leaves the support hypothesis
   open at that reader, and no fact about the reader discharges it. *)
Fail Definition var_dist_const_reader_mutation (R : realType) :
  var_dist (fdistmap (fun _ : bool => tt) (fdist1 true : R.-fdist bool))
           (fdistmap (fun _ : bool => tt) (fdist1 false))
  = var_dist (fdist1 true : R.-fdist bool) (fdist1 false)
  := ltac:(by apply: var_dist_fdistmap_supp_inj).

(******************************************************************************)
(*     A bijective reader on one finite type keeps a law uniform              *)
(******************************************************************************)

(* An injective endomap leaves the uniform law fixed. The ideal cut of the
   five-card instance is the uniform law on the rotations, and the reading of
   one seat is such an endomap of card positions, so the reading of the ideal
   cut is the uniform law a marginal bound is stated against. *)
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

(* A pushforward gives mass only to points of the image. It is how a support
   statement about a law defined as a pushforward is read off the map. *)
Lemma fdistmap_supp (R : realType) (A B : finType) (f : A -> B)
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
(*     Counting a tuple's entries through the positions                       *)
(******************************************************************************)

(* The positions of a tuple at which a predicate holds are counted by the
   predicate on the underlying sequence. It is the bridge from a law on card
   positions to the deck's colour census, which is the level at which den
   Boer's encoding is constant in the committed bits. *)
Lemma card_tnth_count (n : nat) (T : Type) (t : n.-tuple T) (p : pred T) :
  #|[pred k : 'I_n | p (tnth t k)]| = count p t.
Proof. by rewrite -sum1_card -sum1_count big_tuple. Qed.

Print Assumptions var_dist_fdistmap_supp_inj.
Print Assumptions fdistmap_inj_uniform_id.
Print Assumptions card_tnth_count.
Print Assumptions var_dist_const_reader_false.
