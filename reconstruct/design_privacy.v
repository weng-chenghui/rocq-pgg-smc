(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: Design Privacy Bridge                                                 *)
(*                                                                            *)
(* A coalition whose observation has the same fiber cardinalities over the    *)
(* shuffle group under the two secrets observes a law independent of the      *)
(* secret. This is the sibling of the transitivity bridge                     *)
(* (transitivity_privacy.v): same sample space, same conclusion, a counting   *)
(* premise in place of t-transitivity. A t-transitive group satisfies the     *)
(* counting premise for every t-design orbit (an informal relation; the       *)
(* transitivity bridge is proved on its own, not through this file), and the  *)
(* counting premise also holds for orbits that are                            *)
(* t-designs of a group that is not t-transitive, which is the PSL(2,11)      *)
(* twelve-card instance.                                                      *)
(*                                                                            *)
(* Section 1 -- uniform_fdistmap_fiberE == equal fibers over a uniform law    *)
(*   give equal pushforwards.                                                 *)
(* Section 2 -- colour_view, colour_law, colour_view_indep_laws,              *)
(*   colour_view_indep_fibers == independence of the colour observer.         *)
(* Section 3 -- card_fiber_sum, pr_countE, uniform_pair_indep_of_class,       *)
(*   pair_fibers_class_sizes, uniform_pair_indep_of_fibers == independence of *)
(*   an observation of both coordinates from a secret read off the first one. *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import transitivity_privacy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Import Num.Theory.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Section fibers.
Variables (R : realType) (X : finType) (A : {set X}) (HA : (0 < #|A|)%N).
Variable T : finType.

(** uniform_fdistmap_fiberE — two maps with equal fiber cardinalities on A
    push the uniform law on A to the same law. *)
Lemma uniform_fdistmap_fiberE (f0 f1 : X -> T) :
  (forall v, #|[set x in A | f0 x == v]| = #|[set x in A | f1 x == v]|) ->
  fdistmap f0 (`U HA : R.-fdist X) = fdistmap f1 (`U HA).
Proof.
move=> Hfib; apply/fdist_ext => v; rewrite !fdistmapE.
have key (f : X -> T) :
    \sum_(x in X | x \in f @^-1 v) (`U HA) x
    = (#|A|%:R)^-1 *+ #|[set x in A | f x == v]| :> R.
  rewrite -sumr_const big_mkcond [RHS]big_mkcond /=.
  apply: eq_bigr => x _; rewrite !inE /=.
  case: (f x == v); last by rewrite andbF.
  rewrite andbT; case: ifPn => xA.
    by rewrite fdist_uniform_supp_in.
  by rewrite fdist_uniform_supp_notin.
by rewrite !key Hfib.
Qed.

End fibers.

Section colour_view.
Variables (N' : nat) (gT : finGroupType) (G : {group gT}).
Variable rho : gT -> {perm 'I_N'.+1}.
Variables (R : realType) (secretP : R.-fdist bool).
Hypothesis card_G_gt0 : (0 < #|G|)%N.
Variable encode : bool -> N'.+1.-tuple 'I_N'.+1.
Variable colour : 'I_N'.+1 -> bool.

Let P := secretP `x (`U card_G_gt0).

(** colour_view C — what a coalition C sees when cards of one colour are
    indistinguishable: the colour of the card dealt to each of its
    positions. The observer of the physical deck model. Positions outside C
    carry the constant false, which is also a real colour value; the
    collision is harmless because C is fixed in the statement, so those
    coordinates do not vary with the sample. *)
Definition colour_view (C : {set 'I_N'.+1}) :
    {RV P -> {ffun 'I_N'.+1 -> bool}} :=
  fun u => [ffun i => if i \in C
                      then colour (tnth (encode u.1) (rho u.2 i)) else false].

(** colour_law C b — the law of the colour view when the secret is b and
    the shuffle is drawn uniformly from G. The one place the uniform-shuffle
    assumption enters the bridge. *)
Definition colour_law (C : {set 'I_N'.+1}) (b : bool) :
    R.-fdist {ffun 'I_N'.+1 -> bool} :=
  fdistmap (fun g => colour_view C (b, g)) (`U card_G_gt0).

(** colour_view_indep_laws — equal conditional laws under the two secrets
    give independence of the colour view from the dealt secret. *)
Lemma colour_view_indep_laws (C : {set 'I_N'.+1}) :
  colour_law C true = colour_law C false ->
  P |= colour_view C _|_ (@dealt_secret gT G R secretP card_G_gt0).
Proof.
move=> Hlaw.
apply: (@inde_prod_fst R bool gT secretP (`U card_G_gt0) _
  (colour_view C) (colour_law C false)) => b.
by case: b; first exact: Hlaw.
Qed.

(** colour_view_indep_fibers — the same from equal counts, under the two
    secrets, of the group elements producing each view value: the form a
    table certificate delivers. *)
Lemma colour_view_indep_fibers (C : {set 'I_N'.+1}) :
  (forall v : {ffun 'I_N'.+1 -> bool},
     #|[set g in G | colour_view C (true, g) == v]|
     = #|[set g in G | colour_view C (false, g) == v]|) ->
  P |= colour_view C _|_ (@dealt_secret gT G R secretP card_G_gt0).
Proof.
move=> Hfib; apply: colour_view_indep_laws.
exact: (uniform_fdistmap_fiberE _ _ Hfib).
Qed.

End colour_view.

Section fiber_sum.
Variables (Y W : finType).

(** card_fiber_sum — the cardinality of a set is the sum of its cardinalities
    over the fibers of any map out of it.  The passage from per-value counts
    of an observation to the count of a whole secret class, which is what
    turns a design's per-value counting certificate into a statement about
    class sizes. *)
Lemma card_fiber_sum (g : Y -> W) (Q : pred Y) :
  #|[set y : Y | Q y]| = (\sum_(w : W) #|[set y : Y | Q y && (g y == w)]|)%N.
Proof.
transitivity (\sum_(w : W) \sum_(y in [set y : Y | Q y && (g y == w)]) 1)%N.
  rewrite -sum1_card (partition_big g xpredT) //=.
  by apply: eq_bigr => w _; apply: eq_bigl => y; rewrite !inE.
by apply: eq_bigr => w _; rewrite sum1_card.
Qed.

End fiber_sum.

Section bridge.
Variables (R : realType) (X G T : finType).
Variable s : X -> bool.
Variable A : {set G}.
Hypothesis HA : (0 < #|A|)%N.
Hypothesis HX : (0 < #|[set: X]|)%N.
Variable f : X -> G -> T.

(* The sample space of one deal: X is the dealt input, s reads a boolean
   secret off it, G carries the shuffles and A is the subset they are drawn
   from uniformly, and f is what a coalition observes of the pair.  G is a
   bare finite type here rather than a group, because the argument uses only
   the counts over A; an instance is free to supply a design orbit that is
   not a subgroup. *)

Let P := ((`U HX) `x (`U HA)) : R.-fdist (X * G)%type.

Let c : R := (#|[set: X]|%:R)^-1 * (#|A|%:R)^-1.

(** pr_countE — an event of the product of a uniform law on X and a uniform
    law supported on A has probability the number of its points whose second
    coordinate lies in A, divided by #|X| * #|A|, for any predicate Q agreeing
    pointwise with
    the event.  The step out of the probability layer and into the counting
    layer, where the counting premise is stated.  Each of the three
    probabilities of an independence statement crosses by this lemma. *)
Lemma pr_countE (W : eqType) (Y : {RV P -> W}) (w : W) (Q : pred (X * G)) :
  (forall u, (Y u == w) = Q u) ->
  `Pr[ Y = w ] = c *+ #|[set u : X * G | Q u && (u.2 \in A)]|.
Proof.
move=> HQ; rewrite pfwd1E /Pr.
under eq_bigl => u do rewrite inE /= HQ.
rewrite -sumr_const big_mkcond [RHS]big_mkcond.
apply: eq_bigr => u _; rewrite inE.
case: (Q u); last by [].
rewrite andTb.
(* the first explicit argument of fdist_uniform_supp_in is the positivity
   hypothesis, not the point *)
have -> : P u = (#|[set: X]|%:R)^-1 * ((`U HA) u.2) :> R.
  rewrite /P fdist_prodE /=; congr (_ * _).
  by apply: fdist_uniform_supp_in; rewrite inE.
case: ifPn => uA.
  by have -> : (`U HA) u.2 = (#|A|%:R)^-1 :> R by apply: fdist_uniform_supp_in.
have -> : (`U HA) u.2 = 0 :> R by apply: fdist_uniform_supp_notin.
by rewrite mulr0.
Qed.

(** uniform_pair_indep_of_class — when the two secret classes have equal size
    and every observation value is produced equally often over each of them,
    the observation is independent of the secret.  The two-premise form, from
    which uniform_pair_indep_of_fibers is obtained by deriving the first
    premise from the second.  Both counts range over a class paired with A
    and never over the whole of G, and that restriction to A is the content
    of the premise a design supplies. *)
Lemma uniform_pair_indep_of_class :
  #|[set x | s x]| = #|[set x | ~~ s x]| ->
  (forall v : T,
     #|[set u : X * G | (s u.1 == true) && (u.2 \in A) && (f u.1 u.2 == v)]|
     = #|[set u : X * G |
           (s u.1 == false) && (u.2 \in A) && (f u.1 u.2 == v)]|) ->
  P |= (fun u => f u.1 u.2 : T) _|_ (fun u => s u.1 : bool).
Proof.
move=> Hclass Hfib v b.
(* the class premise in == form *)
have e0 : [set x : X | s x] = [set x : X | s x == true].
  by apply/setP => x; rewrite !inE; case: (s x).
have e1 : [set x : X | ~~ s x] = [set x : X | s x == false].
  by apply/setP => x; rewrite !inE; case: (s x).
rewrite e0 e1 in Hclass.
(* the two classes partition X *)
have Htot : #|[set: X]|
  = (#|[set x : X | s x == true]| + #|[set x : X | s x == false]|)%N.
  have a1 : [set: X] :&: [set x : X | s x] = [set x : X | s x == true].
    by apply/setP => x; rewrite !inE; case: (s x).
  have a2 : [set: X] :\: [set x : X | s x] = [set x : X | s x == false].
    by apply/setP => x; rewrite !inE; case: (s x).
  by rewrite -(cardsID [set x : X | s x] [set: X]) a1 a2.
have hn2 : #|[set: X]| = (2 * #|[set x : X | s x == true]|)%N.
  by rewrite Htot -Hclass addnn -mul2n.
have hkt0 : (0 < #|[set x : X | s x == true]|)%N.
  by move: HX; rewrite hn2 muln_gt0 => /andP[].
(* both b-indexed counts reduce to the b = true one *)
have [HNb Hkb] :
  #|[set u : X * G | (s u.1 == b) && (u.2 \in A) && (f u.1 u.2 == v)]|
  = #|[set u : X * G | (s u.1 == true) && (u.2 \in A) && (f u.1 u.2 == v)]|
  /\ #|[set x : X | s x == b]| = #|[set x : X | s x == true]|.
  case: b; first by split.
  by split; [rewrite (Hfib v) | rewrite Hclass].
(* the three probabilities as counts.  rewrite counts occurrences up to
   conversion, so each of the three is pinned by its own pattern: an unpinned
   rewrite hits two convertible random variables at once *)
rewrite [LHS](pr_countE (Q := fun u : X * G =>
    (f u.1 u.2 == v) && (s u.1 == b))); last first.
  by move=> u; rewrite /RV2 /= xpair_eqE.
rewrite [X in _ = X * _](pr_countE (Q := fun u : X * G =>
    f u.1 u.2 == v)); last by [].
rewrite [X in _ = _ * X](pr_countE (Q := fun u : X * G =>
    s u.1 == b)); last by [].
(* the joint count *)
have -> : [set u : X * G | ((f u.1 u.2 == v) && (s u.1 == b)) && (u.2 \in A)]
        = [set u : X * G | (s u.1 == b) && (u.2 \in A) && (f u.1 u.2 == v)].
  apply/setP => u; rewrite !inE.
  by case: (f u.1 u.2 == v); case: (s u.1 == b); case: (u.2 \in A).
rewrite HNb.
(* the marginal count of the reading *)
have Hsplit : #|[set u : X * G | (f u.1 u.2 == v) && (u.2 \in A)]|
  = (#|[set u : X * G | (s u.1 == true) && (u.2 \in A) && (f u.1 u.2 == v)]|
   + #|[set u : X * G |
        (s u.1 == false) && (u.2 \in A) && (f u.1 u.2 == v)]|)%N.
  have b1 : [set u : X * G | (f u.1 u.2 == v) && (u.2 \in A)]
              :&: [set u : X * G | s u.1]
      = [set u : X * G | (s u.1 == true) && (u.2 \in A) && (f u.1 u.2 == v)].
    apply/setP => u; rewrite !inE.
    by case: (f u.1 u.2 == v); case: (s u.1); case: (u.2 \in A).
  have b2 : [set u : X * G | (f u.1 u.2 == v) && (u.2 \in A)]
              :\: [set u : X * G | s u.1]
      = [set u : X * G | (s u.1 == false) && (u.2 \in A) && (f u.1 u.2 == v)].
    apply/setP => u; rewrite !inE.
    by case: (f u.1 u.2 == v); case: (s u.1); case: (u.2 \in A).
  rewrite -(cardsID [set u : X * G | s u.1]
    [set u : X * G | (f u.1 u.2 == v) && (u.2 \in A)]).
  by rewrite b1 b2.
rewrite Hsplit -(Hfib v).
(* the marginal count of the class *)
have Hprod : [set u : X * G | (s u.1 == b) && (u.2 \in A)]
           = setX [set x : X | s x == b] A.
  by apply/setP => u; rewrite !inE.
rewrite Hprod cardsX Hkb.
(* arithmetic.  mulr_natl and mulr_natr grab the numeral inside 2^-1 unless
   the occurrence is pinned by a pattern *)
have h2 : (2%:R : R) != 0 by rewrite pnatr_eq0.
have hKA : (#|[set x : X | s x == true]|%:R * #|A|%:R : R) != 0.
  by apply: mulf_neq0; rewrite pnatr_eq0 -lt0n.
have half : forall y : R, (y *+ 2) * (2%:R)^-1 = y.
  by move=> y; rewrite -[y *+ 2]mulr_natr -mulrA divff// mulr1.
have hk : c *+ (#|[set x : X | s x == true]| * #|A|)%N = (2%:R : R)^-1.
  rewrite -[LHS]mulr_natl natrM /c hn2 natrM -invfM.
  have -> : 2%:R * #|[set x : X | s x == true]|%:R * #|A|%:R
          = 2%:R * (#|[set x : X | s x == true]|%:R * #|A|%:R) :> R.
    by rewrite mulrA.
  by rewrite invfM mulrCA divff// mulr1.
by rewrite hk mulrnDr -mulr2n half.
Qed.

(** pair_fibers_class_sizes — equal per-value counts of the observation over
    the two secret classes force the two classes to have equal size, each
    class size being recovered from those counts as their total divided by
    #|A|.  This is why uniform_pair_indep_of_fibers carries one premise and
    not two. *)
Lemma pair_fibers_class_sizes :
  (forall v : T,
     #|[set u : X * G | (s u.1 == true) && (u.2 \in A) && (f u.1 u.2 == v)]|
     = #|[set u : X * G |
           (s u.1 == false) && (u.2 \in A) && (f u.1 u.2 == v)]|) ->
  #|[set x | s x]| = #|[set x | ~~ s x]|.
Proof.
move=> Hfib.
(* each class size times #|A| is the total of that class's per-value counts *)
have key : forall bb : bool,
    (\sum_(v : T) #|[set u : X * G | (s u.1 == bb) && (u.2 \in A)
                                      && (f u.1 u.2 == v)]|)%N
    = (#|[set x : X | s x == bb]| * #|A|)%N.
  move=> bb.
  rewrite -(card_fiber_sum (fun u : X * G => f u.1 u.2)
                           (fun u : X * G => (s u.1 == bb) && (u.2 \in A))).
  have -> : [set u : X * G | (s u.1 == bb) && (u.2 \in A)]
          = setX [set x : X | s x == bb] A.
    by apply/setP => u; rewrite !inE.
  by rewrite cardsX.
have H2 : (#|[set x : X | s x == true]| * #|A|)%N
        = (#|[set x : X | s x == false]| * #|A|)%N.
  by rewrite -!key; apply: eq_bigr => v _; exact: Hfib.
(* eqn_pmul2r takes the 0 < m proof alone *)
have Hcl : #|[set x : X | s x == true]| = #|[set x : X | s x == false]|.
  by apply/eqP; rewrite -(eqn_pmul2r HA) H2.
have e0 : [set x : X | s x] = [set x : X | s x == true].
  by apply/setP => x; rewrite !inE; case: (s x).
have e1 : [set x : X | ~~ s x] = [set x : X | s x == false].
  by apply/setP => x; rewrite !inE; case: (s x).
by rewrite e0 e1.
Qed.

(** uniform_pair_indep_of_fibers — when a secret is read off the first
    coordinate of a uniform pair and an observation depends on both
    coordinates, equal per-value counts of the observation over the two
    secret classes make the observation independent of the secret.  The
    sibling of colour_view_indep_fibers for a secret that is a function of
    the first coordinate rather than the coordinate itself: there the counts
    range over the group alone and the conclusion is independence of the
    coordinate itself, which the present premise does not give, because the
    rest of the first coordinate need not be independent of the
    observation. *)
Lemma uniform_pair_indep_of_fibers :
  (forall v : T,
     #|[set u : X * G | (s u.1 == true) && (u.2 \in A) && (f u.1 u.2 == v)]|
     = #|[set u : X * G |
           (s u.1 == false) && (u.2 \in A) && (f u.1 u.2 == v)]|) ->
  P |= (fun u => f u.1 u.2 : T) _|_ (fun u => s u.1 : bool).
Proof.
(* inde_prod_fst does not apply: its second random variable is fst and its
   premise is a conditional law equal at every value of the first coordinate,
   not only across the two classes. *)
move=> Hfib; apply: uniform_pair_indep_of_class; last exact: Hfib.
exact: pair_fibers_class_sizes.
Qed.

End bridge.
