(* Lemmas inlined from the pinned infotheo repository
   (~/Projects/coq/infotheo @ dumas2017dual, commit b5a899f7), from
   du2002/spp_proba.v, du2002/spp_entropy.v, dumas2017dual/lib/
   {extra_algebra,extra_proba,extra_entropy}.v, so that this project
   depends only on core infotheo + smc/. Statements and proofs verbatim
   except section plumbing. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp boolp ring lra reals.
From infotheo Require Import realType_ext realType_ln ssr_ext ssralg_ext.
From infotheo Require Import bigop_ext fdist proba jfdist_cond graphoid entropy.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.

(* ========================================================================== *)
(*                           Log function lemmas                              *)
(* ========================================================================== *)

Section log_extra.

Context {R : realType}.

(* On the positive reals the logarithm vanishes exactly at 1. An entropy or
   mutual-information summand is zero precisely when its log factor is, so this
   is the step that turns a vanishing information quantity into a probability
   identity. *)
Lemma logr_eq1 (x : R) : 0 < x -> (log x = 0) <-> (x = 1).
Proof.
move=> Hpos; split.
- (* log x = 0 -> x = 1 *)
  move=> Hlog.
  rewrite -[x]logK //.
  by rewrite Hlog exp.powRr0.
- (* x = 1 -> log x = 0 *)
  move=> ->.
  exact: log1.
Qed.

End log_extra.

(* ========================================================================== *)
(*                    Independence of random variables                        *)
(* ========================================================================== *)

Section more_inde_RV.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A) (TA TB : finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}).

(* Independence stated on events rather than on point values: every product
   rectangle of the joint law factorises. This is the form in which
   independence is consumed when the two variables are pushed through
   functions, since a preimage of a set is again a set. *)
Definition inde_RV_ev :=
  forall E F,
    `Pr[ [% X, Y] \in E `* F] = `Pr[ X \in E ] * `Pr[ Y \in F ].

(* Point-value independence and rectangle independence are the same property. *)
Lemma inde_RV_events' : P |= X _|_ Y <-> inde_RV_ev.
Proof.
split=> H; last by move=> *; rewrite -!pr_in1 -H setX1.
move=> E F; rewrite !pr_inE'.
rewrite [LHS]/Pr; under eq_bigr=> *.
  rewrite fdistmapE.
  under eq_bigl do rewrite !inE /=.
  over.
rewrite [in RHS]/Pr big_distrl /=.
under [RHS]eq_bigr=> i ?.
  rewrite big_distrr /=.
  under eq_bigr do rewrite !dist_of_RVE -H -dist_of_RVE.
  over.
rewrite -big_setX; apply: eq_bigr=> *.
by rewrite fdistmapE.
Qed.

End more_inde_RV.

(* Pairing a variable with the constant unit variable does not change the fibre
   it cuts out, so conditioning on the unit variable is conditioning on
   nothing. *)
Lemma preimg_tt {R : realType} {T TY : finType} (P : R.-fdist T)
    (Y : {RV P -> TY}) (y : TY) :
  [% unit_RV P, Y] @^-1: [set (tt, y)] = Y @^-1: [set y].
Proof. by apply/setP => ?; rewrite !inE. Qed.

Section more_inde_RV_lemmas.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A).

(* Independence is preserved by applying a deterministic function to each side
   separately, since a post-processing map cannot create a dependence that the
   joint law does not already carry. *)
Lemma inde_RV_comp (TA TB UA UB : finType) (X : {RV P -> TA}) (Y : {RV P -> TB})
  (f : TA -> UA) (g : TB -> UB) :
  P |= X _|_ Y -> P|= (f `o X) _|_ (g `o Y).
Proof.
move=> /inde_RV_events' inde_XY'; apply/inde_RV_events' => E F.
by rewrite (pr_in_comp' f) (pr_in_comp' g) -inde_XY' -preimsetX -pr_in_comp'.
Qed.

(* The constant unit variable is independent of everything: it is the neutral
   element of the conditioning side, used to move between unconditional
   independence and conditional independence given nothing. *)
Lemma inde_unit_RV (TA : finType) (X : {RV P -> TA}) : P |= unit_RV P _|_ X.
Proof. by move=> [] b; rewrite pr_eq_unit mul1r !pfwd1E -preimg_set1. Qed.

Variables (TA TB TC TD : finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}).
Variables (UA UB UC: finType) (f : TA -> UA) (g : TB -> UB) (h : TC -> UC).

(* Independence in conditional-probability form: conditioning on any positive
   fibre of Y leaves the law of X unchanged. This is the shape an adversary
   argument uses, where the conditioning event is the observed view. *)
Lemma inde_rv_cprP : P |= X _|_ Y <->
  forall x y, `Pr[ Y = y ] != 0 -> `Pr[ X = x | Y = y] = `Pr[ X = x].
Proof.
split=> + x y => /(_ x y); rewrite cpr_eqE; first by move=> -> ?; field.
have[Hy _ |Hy <- //] := eqVneq `Pr[ Y = y ] 0; last by field.
by rewrite pfwd1_domin_RV1 Hy// mulr0.
Qed.

End more_inde_RV_lemmas.

(* ========================================================================== *)
(*                        Sums of random variables                            *)
(* ========================================================================== *)

Section add_RV.
Context {R : realType}.
Variables (T : finType) (A : finZmodType) (P : R.-fdist T).
Variables (X Y : {RV P -> A}).

(* Pointwise sum of two random variables valued in a finite abelian group; the
   masking operation of an additive sharing scheme. *)
Definition add_RV : {RV P -> A} := X \+ Y.

(* Convolution formula for the law of a sum of independent summands, with the
   outer sum ranging over the support of X. *)
Lemma pr_add_eqE' i :
  P |= X _|_ Y ->
  `Pr[ add_RV = i ] =
  (\sum_(k <- fin_img X) `Pr[ X = k ] * `Pr[ Y = (i - k)%R ]).
Proof.
move=> XY_indep.
rewrite -pr_in1 (reasoning_by_cases _ X); apply: eq_bigr=> a _.
rewrite setX1 pr_in1 -XY_indep !pfwd1E /Pr; apply: eq_bigl=> t /=.
rewrite !inE/= !xpair_eqE/= /add_RV/= andbC.
apply: andb_id2l=> /eqP->.
by rewrite [RHS]eq_sym subr_eq eq_sym addrC.
Qed.

(* A big operator indexed by the duplicate-free image of a function may be read
   as indexed by the membership predicate of that image. *)
Lemma big_fin_img :
  forall [R : Type] (op : SemiGroup.com_law R) (x : R) [I J : finType]
         (h : J -> I) (F : I -> R),
    \big[op/x]_(i <- fin_img h) F i = \big[op/x]_(i in fin_img h) F i.
Proof.
move=> *; rewrite -big_enum.
apply/esym/perm_big/uniq_perm; [exact: enum_uniq | exact: undup_uniq |].
exact: mem_enum.
Qed.

(* Convolution formula with the outer sum ranging over the whole group, the
   form needed to compare against a uniform law. *)
Lemma pr_add_eqE i :
  P |= X _|_ Y ->
  `Pr[ add_RV = i ] =
  (\sum_(k in A) `Pr[ X = k ] * `Pr[ Y = (i - k)%R ]).
Proof.
move/(pr_add_eqE' i)->; apply/esym.
rewrite big_fin_img/= (bigID (mem (fin_img X)))/= -[RHS]addr0.
by congr +%R; apply: big1=> ? H; rewrite (pfwd1_eq0 H) mul0r.
Qed.

End add_RV.

Section lemma_3_4.
Context {R : realType}.
Variables (T : finType) (A: finZmodType).
Variable P : R.-fdist T.
Variable n : nat.
Variables (X Y : {RV P -> A}).

Hypothesis card_A : #|A| = n.+1.
Variable pY_unif : `p_ Y = fdist_uniform card_A.
Variable XY_indep : P |= X _|_ Y.

(* Pointwise difference of two random variables valued in a finite abelian
   group; the unmasking operation dual to add_RV. *)
Definition sub_RV : {RV P -> A} := X \- Y.

(* Pointwise additive inverse of a random variable. *)
Definition neg_RV : {RV P -> A} := \0 \- X.

(* Adding an independent uniform summand yields a uniform law, irrespective of
   the law of the other summand: the one-time-pad property of the group. *)
Lemma add_RV_unif : `p_ (add_RV X Y) = fdist_uniform card_A .
Proof.
apply: fdist_ext=> /= i.
rewrite fdist_uniformE dist_of_RVE pr_add_eqE; last exact: XY_indep.
under eq_bigr do rewrite -(dist_of_RVE Y) pY_unif fdist_uniformE.
by rewrite -big_distrl sum_pfwd1 /= div1r.
Qed.

End lemma_3_4.

Global Arguments add_RV_unif [R T A P n].

Notation "X `+ Y" := (add_RV X Y) : proba_scope.

(* ========================================================================== *)
(*                     Conditioned distributions                              *)
(* ========================================================================== *)

Section fdist_cond_prop.
Context {R : realType}.
Variables T TX TY TZ : finType.
Variables (P : R.-fdist T) (y : TY).
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (Z : {RV P -> TZ}).

Hypothesis E0 : Pr P (Y @^-1: [set y]) != 0.

Variable (X' : {RV (fdist_cond E0) -> TX}).
Hypothesis EX' : X' = X :> (T -> TX).

(* Reading a variable under the conditioned distribution is the same as reading
   its conditional law under the original one; this is what lets a proof about
   an adversary's posterior be carried out in an ordinary fdist. *)
Lemma Pr_fdist_cond_RV x : `Pr[ X' = x ] = `Pr[ X = x | Y = y ].
Proof. by rewrite pfwd1EfinType Pr_fdist_cond cPr_eq_finType EX'. Qed.

Hypothesis Z_XY_indep : P |= Z _|_ [%X, Y].

(* A variable independent of the pair (X, Y) stays independent of X after
   conditioning on a fibre of Y: the mask remains fresh inside the posterior. *)
Lemma fdist_cond_indep : fdist_cond E0 |= X _|_ Z.
Proof.
move: Z_XY_indep => /cinde_RV_unit /weak_union.
rewrite /cinde_RV /= => H.
move => /= x z.
rewrite mulrC pfwd1_pairC.
have := H z x (tt,y).
by rewrite !pfwd1EfinType !Pr_fdist_cond !cPr_eq_finType preimg_tt.
Qed.

End fdist_cond_prop.

Section lemma_3_5.
Context {R : realType}.
Variable (T TY : finType) (TZ : finZmodType).
Variables (P : R.-fdist T) (X Z : {RV P -> TZ}) (Y : {RV P -> TY}).
Let XZ : {RV P -> TZ} := X `+ Z.

Variable Z_XY_indep : P |= Z _|_ [%X, Y].

Let Z_X_indep : P |= Z _|_ X.
Proof. exact/cinde_RV_unit/decomposition/cinde_RV_unit/Z_XY_indep. Qed.

Let Z_Y_indep : P |= Z _|_ Y.
Proof.
exact/cinde_RV_unit/decomposition/cinde_drv_2C/cinde_RV_unit/Z_XY_indep.
Qed.

Variable n : nat.
Hypothesis card_TZ : #|TZ| = n.+1.
Hypothesis pZ_unif : `p_ Z = fdist_uniform card_TZ.

Section iy.
Variable (y : TY).
Hypothesis Y0 : Pr P (Y @^-1: [set y]) != 0.

Let X' : {RV (fdist_cond Y0) -> TZ} := X.
Let Z' : {RV (fdist_cond Y0) -> TZ} := Z.
Let XZ' : {RV (fdist_cond Y0) -> TZ} := X' `+ Z'.

(* Conditioning the masked value on any positive fibre of Y leaves its law
   unchanged: the observation Y = y reveals nothing about X `+ Z. *)
Lemma lemma_3_5 z : `Pr[ XZ = z | Y = y] = `Pr[ XZ = z].
Proof.
rewrite -(Pr_fdist_cond_RV (X':=XZ')) //.
rewrite /XZ' pr_add_eqE'; last exact: fdist_cond_indep.
under eq_bigr => k _.
  rewrite (Pr_fdist_cond_RV (X:=X)) //.
  rewrite (Pr_fdist_cond_RV (X:=Z)) //.
  rewrite [X in _ * X]cpr_eqE.
  rewrite Z_Y_indep.
  rewrite -[(_/_)]mulrA mulfV; last by rewrite pfwd1EfinType.
  rewrite mulr1 -[X in _ * X]dist_of_RVE pZ_unif fdist_uniformE /=.
  over.
(* Pull the const part `Pr[ Y = (i - k) ] from the \sum_k *)
rewrite -big_distrl /=.
rewrite /X' cPr_1 ?mul1r//; last by rewrite pfwd1EfinType.
rewrite -dist_of_RVE (add_RV_unif X Z (card_TZ)) //.
- by rewrite fdist_uniformE.
- rewrite /inde_RV /= => /= z0 z1.
  by rewrite pfwd1_pairC/= Z_X_indep/= mulrC.
Qed.

End iy.

(* An input masked by an independent uniform summand is independent of any
   further observation the mask is fresh against: the one-time-pad step of the
   sharing scheme. *)
Lemma lemma_3_5' : P |= XZ _|_ Y.
Proof.
apply/inde_rv_cprP  => /= x y y0.
rewrite lemma_3_5//.
by rewrite -pfwd1EfinType.
Qed.

End lemma_3_5.

(* ========================================================================== *)
(*                    Conditional probability lemmas                          *)
(* ========================================================================== *)

Section proba_extra.

Context {R : realType}.

(* A pair whose first component misses the image of X misses the image of the
   joint variable, so such pairs contribute nothing to a sum over the joint
   support. *)
Lemma pair_notin_fin_img_fst (T A B : finType) (P : R.-fdist T)
  (X : {RV P -> A}) (Y : {RV P -> B}) (a : A) (b : B) :
  a \notin fin_img X -> (a, b) \notin fin_img [% X, Y].
Proof.
move=> a_notin_img.
apply/memPn => p Hp.
move: Hp.
rewrite /fin_img mem_undup.
move/mapP => [] t Ht ->.
rewrite xpair_eqE.
apply/nandP; left.
apply/eqP => Xt_eq_a.
move: a_notin_img.
rewrite mem_undup => /negP.
apply;apply/mapP.
exists t.
  exact: Ht.
symmetry.
exact: Xt_eq_a.
Qed.

(* Total probability for a posterior: conditioning on a positive fibre of Y
   gives a normalised law on the values of X. *)
Lemma sum_cPr_eq
  (T A B : finType) (P : R.-fdist T)
  (X : {RV P -> A}) (Y : {RV P -> B}) (y : B) :
  `Pr[Y = y] != 0 ->
  \sum_(a in A) `Pr[X = a | Y = y] = 1.
Proof.
move=> Hy_neq0.
rewrite (bigID (mem (fin_img X))) /=.
rewrite [X in _ + X = _](eq_bigr (fun=> 0)); last first.
  move=> a a_notin_img.
  rewrite cpr_eqE.
  have ->: `Pr[[% X, Y] = (a, y)] = 0.
    apply/eqP; rewrite pfwd1_eq0; apply/eqP.
      by [].
    apply/eqP.
    apply: pair_notin_fin_img_fst.
    exact: a_notin_img.
  by rewrite mul0r.
rewrite [X in _ + X]big1 ?addr0; last by move=> i _.
rewrite -big_uniq /=.
  apply: cPr_1.
  exact: Hy_neq0.
apply: undup_uniq.
Qed.

(* When a relation between X and Y holds at every sample point, the posterior
   of Y given X puts no mass on values violating it: a correctness constraint
   of the protocol transfers to the adversary's posterior. *)
Lemma cond_prob_zero_outside_constraint
  {T TX TY : finType} (P : R.-fdist T)
  (X : {RV P -> TX}) (Y : {RV P -> TY})
  (constraint : TX -> TY -> bool) :
  (* The constraint must hold almost surely *)
  (forall t, constraint (X t) (Y t)) ->
  (* Then conditional probability is zero outside the constraint *)
  forall x y,
    `Pr[X = x] != 0 ->
    ~~ constraint x y ->
    `Pr[Y = y | X = x] = 0.
Proof.
move=> Hconstraint x y Hx_pos Hnot_constraint.
rewrite cpr_eqE.
have Hempty: finset ([%Y, X] @^-1 (y, x)) = set0.
  apply/setP => t.
  rewrite in_set0 inE /preim /pred1 /= xpair_eqE.
  apply: contraTF Hnot_constraint => /andP[/eqP HY /eqP HX].
  by rewrite -HY -HX Hconstraint.
have ->: `Pr[[%Y, X] = (y, x)] = 0.
  by rewrite pfwd1E Hempty Pr_set0.
by rewrite mul0r.
Qed.

End proba_extra.

Section perm_extra.

Context {R : realType}.
Variables (T : finType) (P : R.-fdist T).

(* Dropping the first component of a triple's joint law leaves the joint law of
   the remaining pair, the identification that lets a conditional mutual
   information be rewritten in random-variable notation. *)
Lemma fdist_proj23_RV3 (TA TB TC : finType)
    (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC})
 : fdist_proj23 `p_[% X, Y, Z] = `p_[% Y, Z].
Proof.
by rewrite /fdist_proj23 /fdist_snd /fdistA /dist_of_RV /fdistC12 !fdistmap_comp.
Qed.

End perm_extra.

(* ========================================================================== *)
(*                       Negated random variables                             *)
(* ========================================================================== *)

Section neg_RV_lemmas.
Context {R : realType}.
Variables (T : finType) (m n: nat) (P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Hypothesis card_TX : #|TX| = m.+2.

(* Negation preserves the uniform law, since it permutes the group. *)
Lemma neg_RV_dist_eq (X : {RV P -> TX}):
  `p_ X = fdist_uniform card_TX ->
  `p_ X = `p_ (neg_RV X).
Proof.
rewrite /dist_of_RV=> Hunif.
apply/val_inj/ffunP => x /=. (* these two steps eq to apply: fdist_ext.*)
rewrite [RHS](_: _ = fdistmap X P (-x)).
  by rewrite !Hunif !fdist_uniformE.
rewrite /fdistmap !fdistbindE.
apply: eq_bigr=> a ?.
by rewrite /neg_RV !fdist1E /= sub0r eqr_oppLR.
Qed.

(* Negation preserves independence, so a subtractive mask is as good as an
   additive one. *)
Lemma neg_RV_inde_eq (U : finType) (V : finZmodType) (X : {RV P -> U})
    (Y : {RV P -> V}):
  P |= X _|_ Y ->
  P |= X _|_ neg_RV Y.
Proof.
move => H.
have ->: X = idfun `o X by [].
have ->: neg_RV Y = (fun y: V => 0 - y ) `o Y.
  exact: boolp.funext => ? //=.
apply: inde_RV_comp.
exact: H.
Qed.

End neg_RV_lemmas.

(* ========================================================================== *)
(*            Conditional independence and mutual information                 *)
(* ========================================================================== *)

Section cinde_cond_mutual_info0.

Context {R : realType}.
Variables (T TX TY TZ : finType).
Variable (P : R.-fdist T).
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (Z : {RV P -> TZ}).

(* Conditional independence of X and Y given Z makes the conditional mutual
   information I(X;Y|Z) vanish: the qualitative secrecy statement and its
   quantitative counterpart agree. *)
Lemma cinde_cond_mutual_info0 :
  P |= X _|_ Y | Z -> cond_mutual_info `p_[% X, Y, Z] = 0.
Proof.
move=> H_cinde.
rewrite cond_mutual_infoE.
apply/eqP.
rewrite big1 //.
case=> [[a b] c] _.
rewrite //=.
have [->|Habc_neq0] := eqVneq (`p_[% X, Y, Z] (a, b, c)) 0.
  by rewrite mul0r.
apply/eqP; rewrite mulf_eq0; apply/orP; right.
apply/eqP.
have H_pos: 0 < (\Pr_`p_ [% X, Y, Z][[set (a, b)] | [set c]] /
              (\Pr_(fdist_proj13 `p_ [% X, Y, Z])[[set a] | [set c]] *
               \Pr_(fdist_proj23 `p_ [% X, Y, Z])[[set b] | [set c]])).
  rewrite divr_gt0; last first.
  - apply: mulr_gt0.
    + rewrite -Pr_jcPr_gt0 lt0Pr setX1 Pr_set1.
      by rewrite (fdist_proj13_dominN (b:=b)).
    + rewrite -Pr_jcPr_gt0 lt0Pr setX1 Pr_set1.
      by rewrite (fdist_proj23_dominN (a:=a)).
  - rewrite -Pr_jcPr_gt0 lt0Pr setX1 Pr_set1.
    exact: Habc_neq0.
  - by [].
rewrite (logr_eq1 H_pos).
move: (H_cinde a b c); rewrite /cinde_RV => H_eq.
have Hzne0: `Pr[Z = c] != 0.
  apply: contra_neq Habc_neq0 => Hz0.
  rewrite dist_of_RVE pfwd1_pairC.
  by rewrite (pfwd1_domin_RV2 [%X, Y] (a,b) Hz0).
rewrite cpr_eqE in H_eq.
rewrite /jcPr !setX1 !Pr_set1.
have ->: (fdist_proj13 `p_ [% X, Y, Z])`2 = `p_ Z.
  by rewrite fdist_proj13_snd; apply/fdist_ext => x; rewrite snd_RV3 snd_RV2.
have ->: (fdist_proj23 `p_ [% X, Y, Z])`2 = `p_ Z.
  by rewrite fdist_proj23_snd; apply/fdist_ext => y; rewrite snd_RV3 snd_RV2.
rewrite fdist_proj13_RV3 fdist_proj23_RV3.
rewrite snd_RV3 snd_RV2 !dist_of_RVE -!cpr_eqE -H_eq cpr_eqE //=.
rewrite dist_of_RVE in Habc_neq0.
by field; rewrite ?Hzne0 ?Habc_neq0.
Qed.

End cinde_cond_mutual_info0.

Section inde_entropy_lemmas.

Context {R : realType}.

(* A view independent of the secret leaves the secret's entropy untouched:
   H(X | View) = H(X), the entropy form of "the view carries no information". *)
Lemma inde_cond_entropy (U A B : finType) (P : R.-fdist U)
  (View : {RV P -> A}) (X : {RV P -> B}) :
  P |= View _|_ X ->
  `H(X | View) = `H `p_ X.
Proof.
move=> Hinde; rewrite /centropy_RV.
have Hprod := inde_dist_of_RV2 Hinde.
have Hprod2 : (`p_[%X, View]) = (((`p_[%X, View])`1) `x ((`p_[%X, View])`2))%fdist.
  by rewrite fst_RV2 snd_RV2 -fdistX_RV2 Hprod fdistX_prod.
by rewrite (centropy_indep Hprod2) fst_RV2.
Qed.

End inde_entropy_lemmas.
