From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp boolp ring lra reals.
From infotheo Require Import realType_ext realType_ln ssr_ext ssralg_ext.
From infotheo Require Import bigop_ext fdist proba jfdist_cond graphoid entropy.
From infotheo.dumas2017dual.entropy_fiber Require Import entropy_fiber.
From pgg_smc Require Import proba_entropy_ext.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.

Section miniature.

Variable R : realType.

Definition posterior_bitP : R.-fdist bool := fdist_uniform card_bool.

Definition posterior_bit : {RV posterior_bitP -> bool} := id.

Definition posterior_reveal : {RV posterior_bitP -> bool} := id.

(** A revealed Boolean value leaves one compatible secret, so its posterior
    entropy is zero. *)
Lemma posterior_entropy_one_secret (c : bool) :
  `H[posterior_bit | posterior_reveal = c] = 0.
Proof.
set S := [set c].
have Hc : `Pr[posterior_reveal = c] != 0.
  rewrite -dist_of_RVE /posterior_reveal /dist_of_RV fdistmap_id.
  rewrite /posterior_bitP fdist_uniformE card_bool invr_eq0 pnatr_eq0.
  by [].
have Hsol : forall x, x \in S ->
    `Pr[posterior_bit = x | posterior_reveal = c] = #|S|%:R^-1.
  move=> x; rewrite /S inE => /eqP ->.
  by rewrite /posterior_bit /posterior_reveal cPr_eq_id // cards1 invr1.
have Hout : forall x, x \notin S ->
    `Pr[posterior_bit = x | posterior_reveal = c] = 0.
  move=> x xNS.
  apply: (@fiberC_cond_Pr0 R _ _ _ _ id posterior_bit posterior_reveal
            erefl c x Hc).
  by rewrite mem_fiber /id; rewrite /S inE in xNS.
rewrite (@centropy1_uniform_over_set R _ _ _ _
           posterior_bit posterior_reveal S c Hc Hsol Hout);
  last by rewrite /S cards1.
by rewrite /S cards1 log1.
Qed.

Definition posterior_hidden : {RV posterior_bitP -> unit} := fun=> tt.

(** A constant observation leaves both Boolean secrets compatible, so its
    posterior entropy is one bit. *)
Lemma posterior_entropy_two_secrets :
  `H[posterior_bit | posterior_hidden = tt] = 1.
Proof.
set S : {set bool} := [set: bool].
have Hc : `Pr[posterior_hidden = tt] != 0 by
  rewrite /posterior_hidden pr_eq_unit oner_eq0.
have Hsol : forall x, x \in S ->
    `Pr[posterior_bit = x | posterior_hidden = tt] = #|S|%:R^-1.
  move=> x _.
  rewrite /posterior_hidden cpr_eq_unit_RV -dist_of_RVE /posterior_bit.
  rewrite /dist_of_RV fdistmap_id /posterior_bitP fdist_uniformE card_bool.
  by rewrite /S cardsT card_bool.
have Hout : forall x, x \notin S ->
    `Pr[posterior_bit = x | posterior_hidden = tt] = 0.
  by move=> x; rewrite /S inE.
rewrite (@centropy1_uniform_over_set R _ _ _ _
           posterior_bit posterior_hidden S tt Hc Hsol Hout);
  last by rewrite /S cardsT card_bool.
by rewrite /S cardsT card_bool log2.
Qed.

End miniature.

Section support_posterior.

Variable R : realType.
Variables (G V : finType).
Variable A : {set G}.
Hypothesis card_A_gt0 : (0 < #|A|)%N.
Variable view_of : bool -> G -> V.
Hypothesis view_of_injective_on : forall b, {in A &, injective (view_of b)}.

Definition support_posteriorP : R.-fdist (bool * G) :=
  (fdist_uniform card_bool) `x
    (@fdist_uniform_supp R G A card_A_gt0).

Definition support_posterior_secret : {RV support_posteriorP -> bool} := fst.

Definition support_posterior_view : {RV support_posteriorP -> V} :=
  fun u => view_of u.1 u.2.

Definition support_compatible_secrets (v : V) : {set bool} :=
  [set b | [exists g in A, view_of b g == v]].

Definition support_ambiguous_view (v : V) : bool :=
  [exists g in A, view_of false g == v] &&
  [exists g in A, view_of true g == v].

(** An event under the uniform Boolean source and the uniform distribution on
    [A] has mass equal to its supported cardinality times the common mass. *)
Lemma support_pr_countE (W : eqType)
    (Y : {RV support_posteriorP -> W}) (w : W) (Q : pred (bool * G)) :
  (forall u, (Y u == w) = Q u) ->
  `Pr[Y = w] =
    (2%:R^-1 * #|A|%:R^-1) *+
      #|[set u : bool * G | Q u && (u.2 \in A)]|.
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
    supported view-fibre size times the common source-point mass. *)
Lemma support_joint_secret_viewE b v :
  `Pr[[% support_posterior_secret, support_posterior_view] = (b, v)] =
  #|[set g in A | view_of b g == v]|%:R *
    (2%:R^-1 * #|A|%:R^-1).
Proof.
rewrite (support_pr_countE
  (Q := fun u => (u.1 == b) && (view_of u.1 u.2 == v))).
set F : {set G} := [set g in A | view_of b g == v].
set J : {set bool * G} := [set (b, g) | g in F].
have HJ : [set u : bool * G |
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

(** Restricted injectivity makes every secret-indexed supported view fibre
    empty or a singleton according to compatibility with the view. *)
Lemma support_injective_fiber_card b v :
  #|[set g in A | view_of b g == v]| =
    if b \in support_compatible_secrets v then 1 else 0.
Proof.
case Hb: (b \in support_compatible_secrets v) => /=.
- move: Hb; rewrite /support_compatible_secrets inE =>
    /exists_inP[g gA /eqP Hg].
  apply: (@eq_card1 G g _) => g'.
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
    common supported source-point mass. *)
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
    secrets under the distribution supported on [A]. *)
Lemma support_posterior_secret_uniform v :
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
    probability zero under the distribution supported on [A]. *)
Lemma support_posterior_secret_zero v :
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
    and otherwise has one compatible secret. *)
Lemma support_compatible_secret_cardE v :
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
    Boolean secrets are compatible, and zero otherwise. *)
Lemma support_posterior_entropy_ambiguousE v :
  `Pr[support_posterior_view = v] != 0 ->
  `H[support_posterior_secret | support_posterior_view = v] =
    (support_ambiguous_view v)%:R.
Proof.
move=> Hv.
have Hsol := support_posterior_secret_uniform Hv.
have Hout := support_posterior_secret_zero Hv.
have Hcard := support_compatible_secret_cardE Hv.
rewrite (@centropy1_uniform_over_set R _ _ _ _
           support_posterior_secret support_posterior_view
           (support_compatible_secrets v) v Hv Hsol Hout); last first.
  by rewrite Hcard; case: (support_ambiguous_view v).
rewrite Hcard.
by case: (support_ambiguous_view v); rewrite /= ?log2 ?log1.
Qed.

End support_posterior.

From pgg_smc Require Import pgg_interface pgl27_group pgl27_profile.
From pgg_smc Require Import pgl27_secrecy.
From pgl27_view_entropy_probe Require Import probe_view_definitions.
From pgl27_view_entropy_probe Require Import view_collision_probability.

(** The support-set source specializes definitionally to the PGL(2,7) source,
    so the generic posterior theorems use the protocol's actual distribution. *)
Lemma support_posteriorP_pgl27E (R : realType) :
  @support_posteriorP R (pgg_gT pgl27_M) (pgg_G pgl27_M)
    pgl27_G_pos = pgl27P R.
Proof. by []. Qed.

From pgg_smc Require Import pgl27_leakage_census.

Local Lemma pgl27_ambiguous_viewsE
    (R : realType) (S : seq nat) (v : {ffun 'I_8 -> 'I_8}) :
  (v \in pgl27_ambiguous_views R S) =
  support_ambiguous_view (pgg_G pgl27_M)
    (fun b g => pgl27_view R (pgl27_code_coalition S) (b, g)) v.
Proof.
by rewrite /pgl27_ambiguous_views /support_ambiguous_view inE.
Qed.

(** A reachable PGL protocol view has one bit of posterior entropy precisely
    when both secrets can produce it, and zero bits otherwise. *)
Lemma pgl27_reachable_view_entropy_ambiguousE
    (R : realType) (S : seq nat)
    (Hinj : forall b,
      {in pgg_G pgl27_M &,
        injective
          (fun g => pgl27_view R (pgl27_code_coalition S) (b, g))})
    (v : {ffun 'I_8 -> 'I_8}) :
  pfwd1 (pgl27_view R (pgl27_code_coalition S)) v != 0 ->
  centropy1_RV
    (pgl27_view R (pgl27_code_coalition S))
    (pgl27_secret R) v =
  (v \in pgl27_ambiguous_views R S)%:R.
Proof.
move=> Hv.
rewrite pgl27_ambiguous_viewsE.
exact: (@support_posterior_entropy_ambiguousE
  R (pgg_gT pgl27_M) {ffun 'I_8 -> 'I_8}
  (pgg_G pgl27_M) pgl27_G_pos
  (fun b g => pgl27_view R (pgl27_code_coalition S) (b, g))
  Hinj v Hv).
Qed.

(** Every reachable harmonic four-position view has zero or one bit of
    posterior entropy, according to whether both secrets produce it. *)
Lemma pgl27_reachable_view_entropy_harmonicE (R : realType)
    (v : {ffun 'I_8 -> 'I_8}) :
  pfwd1 (pgl27_view R (pgl27_code_coalition rep_harmonic)) v != 0 ->
  centropy1_RV
    (pgl27_view R (pgl27_code_coalition rep_harmonic))
    (pgl27_secret R) v =
  (v \in pgl27_ambiguous_views R rep_harmonic)%:R.
Proof.
apply: pgl27_reachable_view_entropy_ambiguousE.
exact: pgl27_conditional_view_inj_harmonic.
Qed.

(** Every reachable equianharmonic four-position view has zero or one bit of
    posterior entropy, according to whether both secrets produce it. *)
Lemma pgl27_reachable_view_entropy_equianharmonicE (R : realType)
    (v : {ffun 'I_8 -> 'I_8}) :
  pfwd1 (pgl27_view R (pgl27_code_coalition rep_equianharmonic)) v != 0 ->
  centropy1_RV
    (pgl27_view R (pgl27_code_coalition rep_equianharmonic))
    (pgl27_secret R) v =
  (v \in pgl27_ambiguous_views R rep_equianharmonic)%:R.
Proof.
apply: pgl27_reachable_view_entropy_ambiguousE.
exact: pgl27_conditional_view_inj_equianharmonic.
Qed.

(** Every reachable five-position view has zero or one bit of posterior
    entropy, according to whether both secrets produce it. *)
Lemma pgl27_reachable_view_entropy_fiveE (R : realType)
    (v : {ffun 'I_8 -> 'I_8}) :
  pfwd1 (pgl27_view R (pgl27_code_coalition rep_five)) v != 0 ->
  centropy1_RV
    (pgl27_view R (pgl27_code_coalition rep_five))
    (pgl27_secret R) v =
  (v \in pgl27_ambiguous_views R rep_five)%:R.
Proof.
apply: pgl27_reachable_view_entropy_ambiguousE.
exact: pgl27_conditional_view_inj_five.
Qed.

(** Every reachable six-position view has zero or one bit of posterior
    entropy, according to whether both secrets produce it. *)
Lemma pgl27_reachable_view_entropy_sixE (R : realType)
    (v : {ffun 'I_8 -> 'I_8}) :
  pfwd1 (pgl27_view R (pgl27_code_coalition rep_six)) v != 0 ->
  centropy1_RV
    (pgl27_view R (pgl27_code_coalition rep_six))
    (pgl27_secret R) v =
  (v \in pgl27_ambiguous_views R rep_six)%:R.
Proof.
apply: pgl27_reachable_view_entropy_ambiguousE.
exact: pgl27_conditional_view_inj_six.
Qed.

Print Assumptions pgl27_reachable_view_entropy_harmonicE.
Print Assumptions pgl27_reachable_view_entropy_equianharmonicE.
Print Assumptions pgl27_reachable_view_entropy_fiveE.
Print Assumptions pgl27_reachable_view_entropy_sixE.
