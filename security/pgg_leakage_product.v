(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Product-of-independences combinator at the LeakageWitness level: the joint *)
(* witness of two independent components on the two factors of a product       *)
(* distribution.                                                               *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset bigop ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy graphoid.
From pgg_smc Require Import pgg_leakage_witness.

Import GRing.Theory Num.Theory. Set Implicit Arguments. Unset Strict Implicit. Import Prenex Implicits.
Local Open Scope fdist_scope. Local Open Scope proba_scope.

Section joint.
Variables (R : realType) (U : finType) (P : R.-fdist U).
Variables (sT1 vT1 sT2 vT2 : finType).
Variables (S1 : {RV P -> sT1}) (V1 : {RV P -> vT1}) (S2 : {RV P -> sT2}) (V2 : {RV P -> vT2}).

(** joint_view_indep — if each component's view is independent of its own
    secret, and the two (view, secret) pairs are independent of each other
    across components, then the paired view [% V1, V2] is independent of
    the paired secret [% S1, S2]. The AND-composition rule for coalition
    secrecy: a coalition seeing both components' views learns nothing about
    the joint secret beyond what it already fails to learn from each
    component separately. *)
Lemma joint_view_indep :
  P |= V1 _|_ S1 -> P |= V2 _|_ S2 -> P |= [% V1, S1] _|_ [% V2, S2] ->
  P |= [% V1, V2] _|_ [% S1, S2].
Proof.
move=> H1 H2 Hcross.
have c12 : P |= V1 _|_ V2 by exact: (inde_RV_comp fst fst Hcross).
have s12 : P |= S1 _|_ S2 by exact: (inde_RV_comp snd snd Hcross).
move=> [v1 v2] [s1 s2].
have HT : pfwd1 [% V1, V2, [% S1, S2]] (v1, v2, (s1, s2)) =
          pfwd1 [% [% V1, S1], [% V2, S2]] ((v1, s1), (v2, s2)).
  rewrite !pfwd1E; congr (Pr P _).
  apply/setP => u; rewrite !inE /= !xpair_eqE /=.
  by move: (V1 u == v1) (V2 u == v2) (S1 u == s1) (S2 u == s2) => a b c d;
     case: a; case: b; case: c; case: d.
rewrite HT (Hcross (v1, s1) (v2, s2)) (H1 v1 s1) (H2 v2 s2) (c12 v1 v2) (s12 s1 s2).
by rewrite mulrACA.
Qed.
End joint.

Section product.
Variables (R : realType) (A B : finType) (P1 : R.-fdist A) (P2 : R.-fdist B).

(** inde_RV_fst_snd — reading a product distribution through any function of
    the first coordinate is independent of reading it through any function
    of the second: independence of the product's two factors survives
    arbitrary post-processing on each side. The unconditional cross-component
    term joint_view_indep needs when composing two coalition-secrecy
    witnesses over a product distribution. *)
Lemma inde_RV_fst_snd (TB1 TB2 : finType) (f : A -> TB1) (g : B -> TB2) :
  (P1 `x P2) |= ((fun ab => f ab.1) : {RV (P1 `x P2) -> TB1})
            _|_ ((fun ab => g ab.2) : {RV (P1 `x P2) -> TB2}).
Proof.
move=> x y; rewrite /inde_RV !pfwd1E.
have Hf : finset (preim (fun ab : (A * B)%type => f ab.1) (pred1 x)) =
          ((finset (preim f (pred1 x))) `*T).
  by apply/setP => -[a b]; rewrite !inE.
have Hg : finset (preim (fun ab : (A * B)%type => g ab.2) (pred1 y)) =
          (T`* finset (preim g (pred1 y))).
  by apply/setP => -[a b]; rewrite !inE.
rewrite Hf Hg -Pr_fdist_prod.
congr (Pr _ _).
apply/setP => -[a b]; rewrite !inE /= xpair_eqE /=.
by [].
Qed.

(** inde_RV_fst — two P1-independent random variables stay independent when
    read through the first projection of a product distribution: the
    second factor contributes no correlation. Transports the first
    component's own coalition-secrecy witness up to the product. *)
Lemma inde_RV_fst (TB1 TB2 : finType) (X : {RV P1 -> TB1}) (Y : {RV P1 -> TB2}) :
  P1 |= X _|_ Y ->
  (P1 `x P2) |= ((fun ab => X ab.1) : {RV (P1 `x P2) -> TB1})
            _|_ ((fun ab => Y ab.1) : {RV (P1 `x P2) -> TB2}).
Proof.
move=> H x y; rewrite /inde_RV !pfwd1E.
have Pr_fst : forall (T0 : eqType) (Z : A -> T0) (q : T0),
    Pr (P1 `x P2) (finset (preim (fun ab : (A * B)%type => Z ab.1) (pred1 q))) =
    Pr P1 (finset (preim Z (pred1 q))).
  move=> T0 Z q.
  have HE : finset (preim (fun ab : (A * B)%type => Z ab.1) (pred1 q)) =
            ((finset (preim Z (pred1 q))) `*T).
    by apply/setP => -[a b]; rewrite !inE.
  by rewrite HE -Pr_fdist_fst fdist_prod1.
rewrite (Pr_fst _ X x) (Pr_fst _ Y y) (Pr_fst _ [% X, Y] (x, y)).
by move: (H x y); rewrite /inde_RV !pfwd1E.
Qed.

(** inde_RV_snd — two P2-independent random variables stay independent when
    read through the second projection of a product distribution: the
    first factor contributes no correlation. Transports the second
    component's own coalition-secrecy witness up to the product. *)
Lemma inde_RV_snd (TB1 TB2 : finType) (X : {RV P2 -> TB1}) (Y : {RV P2 -> TB2}) :
  P2 |= X _|_ Y ->
  (P1 `x P2) |= ((fun ab => X ab.2) : {RV (P1 `x P2) -> TB1})
            _|_ ((fun ab => Y ab.2) : {RV (P1 `x P2) -> TB2}).
Proof.
move=> H x y; rewrite /inde_RV !pfwd1E.
have Pr_snd : forall (T0 : eqType) (Z : B -> T0) (q : T0),
    Pr (P1 `x P2) (finset (preim (fun ab : (A * B)%type => Z ab.2) (pred1 q))) =
    Pr P2 (finset (preim Z (pred1 q))).
  move=> T0 Z q.
  have HE : finset (preim (fun ab : (A * B)%type => Z ab.2) (pred1 q)) =
            (T`* finset (preim Z (pred1 q))).
    by apply/setP => -[a b]; rewrite !inE.
  by rewrite HE -Pr_fdist_snd -fdistX_prod fdistX2 fdist_prod1.
rewrite (Pr_snd _ X x) (Pr_snd _ Y y) (Pr_snd _ [% X, Y] (x, y)).
by move: (H x y); rewrite /inde_RV !pfwd1E.
Qed.

(** leakage_product — the joint LeakageWitness of two independent
    components: the combined secret [% s1, s2] paired with the combined
    view [% v1, v2] over P1 `x P2, independent by joint_view_indep. The
    composition rule that assembles a coalition-secrecy witness for a
    system built from two independent sub-protocols out of witnesses for
    the two parts separately, with no extra correlation term. *)
Definition leakage_product (lw1 : LeakageWitness P1) (lw2 : LeakageWitness P2)
    : LeakageWitness (P1 `x P2) :=
  let: MkLeakageWitness sT1 vT1 s1 v1 i1 := lw1 in
  let: MkLeakageWitness sT2 vT2 s2 v2 i2 := lw2 in
  @MkLeakageWitness _ _ (P1 `x P2) (sT1 * sT2)%type (vT1 * vT2)%type
    (fun ab => (s1 ab.1, s2 ab.2)) (fun ab => (v1 ab.1, v2 ab.2))
    (joint_view_indep (inde_RV_fst i1) (inde_RV_snd i2)
       (inde_RV_fst_snd [% v1, s1] [% v2, s2])).

End product.
