(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* support_posterior: posterior entropy of a Boolean secret behind a view     *)
(*                    injective on a support set                              *)
(*                                                                            *)
(* A uniform Boolean secret is drawn independently of a uniform element of a  *)
(* nonempty subset A of a finite type, and the adversary sees a map indexed   *)
(* by the secret that is injective on A for each secret. Every view that      *)
(* occurs at all is then produced by at most one element of A per secret, so  *)
(* it leaves one or two compatible secrets and its posterior entropy is the   *)
(* indicator of that ambiguity.                                               *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   support_posteriorP == the joint law of a uniform Boolean secret and a    *)
(*                         uniform element of A                               *)
(*   support_posterior_secret == the Boolean secret of a sample               *)
(*   support_posterior_view == the view of a sample                           *)
(*   support_compatible_secrets v == the secrets that produce v from A        *)
(*   support_ambiguous_view v == both secrets produce v from A                *)
(*                                                                            *)
(* Key results:                                                               *)
(*   support_posterior_secret_uniformE == at a reachable view the posterior   *)
(*     is uniform on the compatible secrets                                   *)
(*   support_compatible_secrets_cardE == a reachable view has two compatible  *)
(*     secrets when it is ambiguous and one otherwise                         *)
(*   support_posterior_entropy_ambiguousE == the posterior entropy of a       *)
(*     reachable view is the indicator of its ambiguity                       *)
(*                                                                            *)
(* The statements concern one pre-reveal view of a single execution, before   *)
(* any value is published.                                                    *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import ring reals.
From infotheo Require Import realType_ext realType_ln ssr_ext ssralg_ext.
From infotheo Require Import bigop_ext fdist proba jfdist_cond entropy.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.

Section support_centropy.

Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.
Variables (DomainT CodomainT : finType).
Variable X : {RV P -> DomainT}.
Variable Y : {RV P -> CodomainT}.

(** A conditional joint distribution agrees with event-based conditional
    probability whenever the conditioning value has nonzero probability.
    This equality lets the entropy calculation use its probability
    hypotheses. @composes: support_centropy1_uniform_over_set *)
Local Lemma support_jfdist_cond_cPr_eq
    {TX TY : finType} (X0 : {RV P -> TX}) (Y0 : {RV P -> TY}) x y :
  `Pr[X0 = x] != 0 ->
  jfdist_cond `p_[% X0, Y0] x y = `Pr[Y0 = y | X0 = x].
Proof.
move=> Hx_pos.
rewrite jfdist_condE; last first.
  by rewrite fst_RV2 dist_of_RVE.
rewrite cpr_eqE /jcPr.
congr (_ / _).
- rewrite Pr_fdistX setX1 Pr_set1 dist_of_RVE.
  by rewrite pfwd1_pairC.
- rewrite fdistX2 fst_RV2.
  by rewrite Pr_set1 dist_of_RVE.
Qed.

(** If the conditional law is uniform on a nonempty finite set and zero
    outside it, its entropy is the logarithm of the set's cardinality. This
    identifies the compatible-secret set with the adversary's remaining
    uncertainty. @composes: support_posterior_entropy_ambiguousE *)
Local Lemma support_centropy1_uniform_over_set
    (S : {set DomainT}) (c : CodomainT) :
  `Pr[Y = c] != 0 ->
  (forall x, x \in S -> `Pr[X = x | Y = c] = #|S|%:R^-1) ->
  (forall x, x \notin S -> `Pr[X = x | Y = c] = 0) ->
  (0 < #|S|)%N ->
  `H[X | Y = c] = log (#|S|%:R : R).
Proof.
move=> Hcond_pos Hsol_unif Hnonsol_zero Hcard_pos.
have -> : `H[X | Y = c] =
    - \sum_(x : DomainT)
        `Pr[X = x | Y = c] * log (`Pr[X = x | Y = c]).
  rewrite centropy1_RVE //.
    rewrite /entropy; congr (- _); apply: eq_bigr => x _.
    by rewrite (@support_jfdist_cond_cPr_eq CodomainT DomainT Y X c x).
  by rewrite fst_RV2 dist_of_RVE.
rewrite (bigID (mem S)) /=.
have -> : \sum_(i | i \notin S)
    `Pr[X = i | Y = c] * log (`Pr[X = i | Y = c]) = 0.
  apply: big1 => x Hx_notin.
  by rewrite (Hnonsol_zero x Hx_notin) mul0r.
rewrite addr0.
have -> : \sum_(i in S)
    `Pr[X = i | Y = c] * log (`Pr[X = i | Y = c]) =
    \sum_(i in S) #|S|%:R^-1 * log (#|S|%:R^-1 : R).
  apply: eq_bigr => x Hx_in.
  by rewrite (Hsol_unif x Hx_in).
rewrite big_const iter_addr addr0 -mulr_natr mul1r.
rewrite logV; last by rewrite ltr0n.
by field; rewrite pnatr_eq0 -lt0n.
Qed.

End support_centropy.

Section support_posterior.

Variable R : realType.
Variables (T V : finType).
Variable A : {set T}.
Hypothesis card_A_gt0 : (0 < #|A|)%N.
Variable view_of : bool -> T -> V.
Hypothesis view_of_injective_on : forall b, {in A &, injective (view_of b)}.

(** The source is the independent product of a uniform Boolean secret with a
    uniform draw from [A]. It is the law under which the adversary's posterior
    about the secret is taken. *)
Definition support_posteriorP : R.-fdist (bool * T) :=
  (fdist_uniform card_bool) `x
    (@fdist_uniform_supp R T A card_A_gt0).

(** The secret is the Boolean component of a sample. It is the quantity whose
    residual uncertainty given the adversary's view the posterior entropy
    measures, so secrecy of the scheme is a statement about this variable. *)
Definition support_posterior_secret : {RV support_posteriorP -> bool} := fst.

(** The view applies the secret-indexed map to the drawn element. It carries
    no other coordinate of the sample, so the adversary sees the secret only
    through this image. *)
Definition support_posterior_view : {RV support_posteriorP -> V} :=
  fun u => view_of u.1 u.2.

(** These are the secrets that produce the view [v] from some element of [A].
    They are exactly the secrets an adversary seeing [v] cannot rule out. *)
Definition support_compatible_secrets (v : V) : {set bool} :=
  [set b | [exists g in A, view_of b g == v]].

(** A view is ambiguous when both secrets produce it from [A]. Such a view
    leaves the secret completely undetermined. *)
Definition support_ambiguous_view (v : V) : bool :=
  [exists g in A, view_of false g == v] &&
  [exists g in A, view_of true g == v].

(** An event under the uniform Boolean source and the uniform distribution on
    [A] has mass equal to its supported cardinality times the common mass. It
    turns every probability of the posterior computation into a count of
    supported samples. *)
Lemma support_pr_countE (W : eqType)
    (Y : {RV support_posteriorP -> W}) (w : W) (Q : pred (bool * T)) :
  (forall u, (Y u == w) = Q u) ->
  `Pr[Y = w] =
    (2%:R^-1 * #|A|%:R^-1) *+
      #|[set u : bool * T | Q u && (u.2 \in A)]|.
Proof.
move=> HQ; rewrite pfwd1E /Pr.
under eq_bigl => u do rewrite inE /= HQ.
rewrite -sumr_const big_mkcond [RHS]big_mkcond.
apply: eq_bigr => u _; rewrite inE.
case: (Q u); last by [].
rewrite andTb.
rewrite /support_posteriorP fdist_prodE /= fdist_uniformE card_bool.
case: ifPn => Hg.
- by rewrite fdist_uniform_supp_in.
- by rewrite fdist_uniform_supp_notin // mulr0.
Qed.

(** The joint event containing one secret and one view has mass equal to its
    supported view-fibre size times the common source-point mass. It is the
    numerator of every posterior probability of the secret. *)
Lemma support_joint_secret_viewE b v :
  `Pr[[% support_posterior_secret, support_posterior_view] = (b, v)] =
  #|[set g in A | view_of b g == v]|%:R *
    (2%:R^-1 * #|A|%:R^-1).
Proof.
rewrite (support_pr_countE
  (Q := fun u => (u.1 == b) && (view_of u.1 u.2 == v))).
set F : {set T} := [set g in A | view_of b g == v].
set J : {set bool * T} := [set (b, g) | g in F].
have HJ : [set u : bool * T |
    ((u.1 == b) && (view_of u.1 u.2 == v)) && (u.2 \in A)] = J.
  apply/setP => -[b' g].
  rewrite !inE /J /F.
  apply/idP/imsetP.
  - move=> /andP[/andP[/eqP Hb /eqP Hv] HgA].
    move: Hb Hv HgA; rewrite /= => -> Hv HgA.
    exists g; first by rewrite inE HgA /= Hv.
    by [].
  - move=> [g' Hg' Hpair].
    move: Hpair => [= -> ->].
    move: Hg'; rewrite inE => /andP[HgA /eqP Hv].
    rewrite /= eqxx HgA andbT.
    exact/eqP.
have HJF : #|J| = #|F| by
  rewrite /J card_imset //; move=> g1 g2 [=].
rewrite HJ HJF.
by rewrite mulr_natl mulrC.
by move=> [b' g]; rewrite /support_posterior_secret
  /support_posterior_view /= xpair_eqE.
Qed.

(** At a fixed secret, restricted injectivity makes the supported fibre of the
    view map over [v] empty or a singleton, according to whether that secret is
    compatible with [v]. Injectivity on [A] is the assumption that no secret
    reaches one view from two distinct elements of [A], so the weight a view
    puts on a secret is a compatibility bit and never a multiplicity. *)
Lemma support_injective_fiber_card b v :
  #|[set g in A | view_of b g == v]| =
    if b \in support_compatible_secrets v then 1 else 0.
Proof.
case Hb: (b \in support_compatible_secrets v) => /=.
- move: Hb; rewrite /support_compatible_secrets inE =>
    /exists_inP[g gA /eqP Hg].
  apply: (@eq_card1 T g _) => g'.
  rewrite inE; apply/idP/eqP.
  + move=> /andP[g'A /eqP Hg'].
    exact: (view_of_injective_on (b:=b) g'A gA
      (trans_eq Hg' (esym Hg))).
  + move=> ->; rewrite gA /=.
    exact/eqP.
- apply: eq_card0 => g.
  rewrite inE.
  apply/negP => /andP[gA Hg].
  have Hmem : b \in support_compatible_secrets v.
    rewrite /support_compatible_secrets inE; apply/exists_inP.
    by exists g.
  by rewrite Hmem in Hb.
Qed.

(** The mass of a view is the number of compatible Boolean secrets times the
    common supported source-point mass. It is the denominator of every
    posterior probability of the secret. *)
Lemma support_posterior_view_massE v :
  `Pr[support_posterior_view = v] =
  #|support_compatible_secrets v|%:R *
    (2%:R^-1 * #|A|%:R^-1).
Proof.
rewrite -dist_of_RVE -(@snd_RV2 R _ _ _ _
  support_posterior_secret support_posterior_view).
rewrite fdist_sndE big_bool /=.
rewrite !dist_of_RVE !support_joint_secret_viewE.
have Hcard : #|support_compatible_secrets v| =
    ((if false \in support_compatible_secrets v then 1 else 0) +
     (if true \in support_compatible_secrets v then 1 else 0))%N.
  by rewrite -sum1_card big_mkcond big_bool /=.
rewrite !support_injective_fiber_card Hcard natrD.
ring.
Qed.

(** At a reachable view, the posterior is uniform on the compatible Boolean
    secrets under the distribution supported on [A]. The adversary therefore
    gains no preference among the secrets the view still allows. *)
Lemma support_posterior_secret_uniformE v :
  `Pr[support_posterior_view = v] != 0 ->
  forall b, b \in support_compatible_secrets v ->
  `Pr[support_posterior_secret = b | support_posterior_view = v] =
    #|support_compatible_secrets v|%:R^-1.
Proof.
move=> Hv b Hb.
rewrite cpr_eqE support_joint_secret_viewE support_posterior_view_massE.
rewrite support_injective_fiber_card Hb /= mul1r.
field.
apply/andP; split.
- rewrite pnatr_eq0 -lt0n; apply/card_gt0P.
  by exists b.
- by rewrite pnatr_eq0 -lt0n.
Qed.

(** At a reachable view, incompatible Boolean secrets have posterior
    probability zero under the distribution supported on [A]. The view thus
    rules out exactly the secrets that cannot produce it. *)
Lemma support_posterior_secret_eq0 v :
  `Pr[support_posterior_view = v] != 0 ->
  forall b, b \notin support_compatible_secrets v ->
  `Pr[support_posterior_secret = b | support_posterior_view = v] = 0.
Proof.
move=> Hv b Hb.
rewrite cpr_eqE support_joint_secret_viewE support_injective_fiber_card.
have Hb0 : (b \in support_compatible_secrets v) = false by exact: negbTE Hb.
by rewrite Hb0 /= !mul0r.
Qed.

(** A reachable view has two compatible secrets exactly when it is ambiguous,
    and one otherwise. The posterior support of a reachable view is therefore
    a two-valued quantity, which is what makes its entropy a Boolean
    indicator. *)
Lemma support_compatible_secrets_cardE v :
  `Pr[support_posterior_view = v] != 0 ->
  #|support_compatible_secrets v| =
    if support_ambiguous_view v then 2 else 1.
Proof.
move=> Hv.
have Hcard : #|support_compatible_secrets v| =
    ((if false \in support_compatible_secrets v then 1 else 0) +
     (if true \in support_compatible_secrets v then 1 else 0))%N.
  by rewrite -sum1_card big_mkcond big_bool /=.
have Hamb : support_ambiguous_view v =
    ((false \in support_compatible_secrets v) &&
     (true \in support_compatible_secrets v)).
  by rewrite /support_ambiguous_view /support_compatible_secrets !inE.
rewrite Hamb Hcard.
case Hf: (false \in support_compatible_secrets v);
case Ht: (true \in support_compatible_secrets v) => /=.
- by [].
- by [].
- by [].
- exfalso.
  move: Hv.
  rewrite support_posterior_view_massE.
  rewrite Hcard Hf Ht /=.
  by rewrite add0n mul0r eqxx.
Qed.

(** Every reachable view has posterior entropy one precisely when both
    Boolean secrets are compatible, and zero otherwise. It is the exact
    per-view uncertainty an adversary restricted to this view retains about
    the secret. *)
Lemma support_posterior_entropy_ambiguousE v :
  `Pr[support_posterior_view = v] != 0 ->
  `H[support_posterior_secret | support_posterior_view = v] =
    (support_ambiguous_view v)%:R.
Proof.
move=> Hv.
have Hsol := support_posterior_secret_uniformE Hv.
have Hout := support_posterior_secret_eq0 Hv.
have Hcard := support_compatible_secrets_cardE Hv.
rewrite (@support_centropy1_uniform_over_set R _ _ _ _
           support_posterior_secret support_posterior_view
           (support_compatible_secrets v) v Hv Hsol Hout); last first.
  by rewrite Hcard; case: (support_ambiguous_view v).
rewrite Hcard.
by case: (support_ambiguous_view v); rewrite /= ?log2 ?log1.
Qed.

End support_posterior.
