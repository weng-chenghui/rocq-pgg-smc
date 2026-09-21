(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: Transitivity Privacy Bridge                                           *)
(*                                                                            *)
(* A t-transitive monodromy group acting on the deck of N = N'.+1 distinct    *)
(* cards makes every coalition of at most t positions perfectly private: any  *)
(* valid arrangement can be re-dealt to any target secret while agreeing with *)
(* the coalition's exact view. This file proves the reusable bridge over an   *)
(* abstract group, independent of any concrete instance.                      *)
(*                                                                            *)
(* Section 1 -- Fiber counting:                                               *)
(*   rho_tuple_fiber_card == every fiber of the k-tuple orbit map has equal   *)
(*     size #|G| %/ #|dtuple_on k| when k <= t.                               *)
(*                                                                            *)
(* Section 2 -- Re-dealing bridge:                                            *)
(*   ttrans_private == a t-transitive shuffle re-deals any coalition view of  *)
(*     size <= t to either secret.                                            *)
(*                                                                            *)
(* Section 3 -- Distributional corollaries:                                   *)
(*   ttrans_view_indep == the coalition view is independent of the secret.    *)
(*   ttrans_point_uniform == the single-point pushforward is uniform.         *)
(*                                                                            *)
(* Section 4 -- Monotone leakage ramp:                                        *)
(*   view_mutual_info_le == a deterministic reduction of the view has mutual  *)
(*     information with the secret at most that of the full view (DPI at the  *)
(*     random-variable level).                                                *)
(*                                                                            *)
(* Section 5 -- Coalition-general view independence:                          *)
(*   ttrans_view_indep_gen == every coalition of at most t positions has view *)
(*     independent of the secret, by k-tuple fiber counting.                  *)
(*   coalition_view_mutual_info_le == leakage about the secret is monotone    *)
(*     under coalition inclusion.                                             *)
(*                                                                            *)
(* Section 6 -- All-decks dealer variant:                                     *)
(*   ttrans_view_indep_alldecks == a dealer that redraws a fresh valid deck   *)
(*     of the secret's class before shuffling gives every coalition of at    *)
(*     most t positions a view independent of the secret.                    *)
(*   alldecks_shuffle_absorb == shuffling a uniform valid deck yields another *)
(*     uniform valid deck of the same class.                                 *)
(*   ttrans_view_indep_deck == the same independence holds with no shuffle   *)
(*     at all, once the deck itself is freshly and uniformly redrawn.         *)
(*                                                                            *)
(* Section 7 -- Record-level view independence:                               *)
(*   profile_deck == the deck a MonodromyProfile deals for a two-valued       *)
(*     secret, read off the threshold-scheme encoder of its plug.             *)
(*   profile_view_indep == ttrans_view_indep_gen stated over an arbitrary     *)
(*     MonodromyProfile, its hypotheses being premises about the projections  *)
(*     of the profile rather than fields of the record.                       *)
(*                                                                            *)
(* Section 8 -- Strength of the transitivity premise:                         *)
(*   ntransitive_card_le == a t-transitive group has at least as many         *)
(*     elements as the acted set has distinct t-tuples.                       *)
(*   ntransitive_trivial_degenerate == the trivial group is t-transitive only *)
(*     on a set carrying at most one distinct t-tuple.                        *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Import Num.Theory.

Local Open Scope fdist_scope.

Section product_independence.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Variables (R : realType) (A B : finType) (P1 : R.-fdist A) (P2 : R.-fdist B).

(** Over a product law P1 `x P2, a random variable Z whose conditional law
    given the first coordinate a is the same fixed law mu for every a is
    independent of that first coordinate. This is the general independence
    fact the file specializes throughout: every "coalition view independent
    of the secret" result below reduces to checking that the view's
    conditional law, given the secret, does not depend on the secret. *)
Lemma inde_prod_fst (T : finType) (Z : A * B -> T) (mu : R.-fdist T) :
  (forall a, fdistmap (fun b => Z (a, b)) P2 = mu) ->
  (P1 `x P2) |= (Z : {RV (P1 `x P2) -> T})
    _|_ ((fun ab => ab.1) : {RV (P1 `x P2) -> A}).
Proof.
move=> Hcond.
have HZa : forall (a : A) (z : T),
    Pr (P1 `x P2) (finset (preim [% (Z : {RV (P1 `x P2) -> T}),
       ((fun ab => ab.1) : {RV (P1 `x P2) -> A})] (pred1 (z, a))))
    = P1 a * mu z.
  move=> a z; rewrite /Pr.
  under eq_bigl => ab do rewrite inE /= xpair_eqE.
  rewrite (eq_bigr (fun ab => P1 ab.1 * P2 ab.2)); last first.
    by move=> ab _; rewrite fdist_prodE.
  rewrite (reindex_onto (fun b : B => (a, b)) (fun i => i.2)); last first.
    by move=> [a' b] /= /andP[_ /eqP ->].
  under eq_bigl => b do rewrite /= !eqxx !andbT.
  under eq_bigr => b _ do rewrite /=.
  by rewrite -big_distrr /= -(Hcond a) fdistmapE.
have HfstA : forall a0,
    `Pr[ ((fun ab => ab.1) : {RV (P1 `x P2) -> A}) = a0 ] = P1 a0.
  move=> a0; rewrite pfwd1E.
  have -> : finset (preim ((fun ab : A * B => ab.1)) (pred1 a0))
      = ((finset (preim (@id A) (pred1 a0))) `*T).
    by apply/setP => -[a' b]; rewrite !inE.
  rewrite -Pr_fdist_fst fdist_prod1.
  have -> : finset (preim (@id A) (pred1 a0)) = [set a0].
    by apply/setP => x; rewrite !inE.
  by rewrite Pr_set1.
have HZz : forall z0, `Pr[ (Z : {RV (P1 `x P2) -> T}) = z0 ] = mu z0.
  move=> z0; rewrite pfwd1E /Pr.
  under eq_bigl => ab do rewrite inE /=.
  under eq_bigr => ab _ do rewrite fdist_prodE.
  transitivity (\sum_(a' : A) (P1 a' * mu z0)); last first.
    by rewrite -big_distrl /= FDist.f1 mul1r.
  rewrite (partition_big (fun ab => ab.1) xpredT) //=.
  apply: eq_bigr => a' _.
  rewrite -(HZa a' z0) /Pr.
  apply: eq_big => [ab | ab _]; last by rewrite fdist_prodE.
  by rewrite inE /= xpair_eqE andbC.
by move=> z a; rewrite pfwd1E HZa HZz HfstA mulrC.
Qed.

End product_independence.

Section uniform_bijection.
Variables (R : realType) (A : finType) (n : nat).

(** A bijection f : A -> A pushes the uniform law on A to itself. Composing
    the uniform shuffle output with the per-secret encoding's injective card
    map (ttrans_view_indep) leaves the coalition's single observed value
    uniform regardless of which secret was dealt. *)
Lemma bij_uniform (card_A : #|A| = n.+1) (f : A -> A) : bijective f ->
  fdistmap f (fdist_uniform (R:=R) card_A) = fdist_uniform card_A.
Proof.
move=> bijf; have [g fg gf] := bijf.
apply: fdist_ext => a.
rewrite fdistmapE fdist_uniformE.
under eq_bigr => x _ do rewrite fdist_uniformE.
rewrite sumr_const.
have -> : #|[pred x | preim f (pred1 a) x]| = 1%N.
  rewrite -(card1 (g a)); apply: eq_card => x.
  by rewrite !inE -(can_eq gf) fg.
by rewrite mulr1n.
Qed.

End uniform_bijection.

Section kernel_independence.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Variables (R : realType) (A B : finType) (P : R.-fdist A) (W : A -> R.-fdist B).

(** Over a kernel product P `X W, a random variable Z whose conditional law
    given any positive-mass first coordinate a is the same fixed law mu is
    independent of that first coordinate. This is inde_prod_fst generalized
    from a plain product to a kernel product, needed once the dealt deck
    itself, not only the shuffle, is drawn from a secret-dependent law
    (ttrans_view_indep_alldecks). *)
Lemma inde_prod_kernel_fst (T : finType) (Z : A * B -> T) (mu : R.-fdist T) :
  (forall a, P a != 0 -> fdistmap (fun b => Z (a, b)) (W a) = mu) ->
  (P `X W) |= (Z : {RV (P `X W) -> T})
    _|_ ((fun ab => ab.1) : {RV (P `X W) -> A}).
Proof.
move=> Hcond.
have HZa : forall (a : A) (z : T),
    Pr (P `X W) (finset (preim [% (Z : {RV (P `X W) -> T}),
       ((fun ab => ab.1) : {RV (P `X W) -> A})] (pred1 (z, a))))
    = P a * mu z.
  move=> a z; rewrite /Pr.
  under eq_bigl => ab do rewrite inE /= xpair_eqE.
  rewrite (eq_bigr (fun ab => P ab.1 * W ab.1 ab.2)); last first.
    by move=> ab _; rewrite fdist_prodE.
  rewrite (reindex_onto (fun b : B => (a, b)) (fun i => i.2)); last first.
    by move=> [a' b] /= /andP[_ /eqP ->].
  under eq_bigl => b do rewrite /= !eqxx !andbT.
  under eq_bigr => b _ do rewrite /=.
  have [Pa0|Pa0] := eqVneq (P a) 0.
    rewrite Pa0 mul0r; apply: big1 => b _; by rewrite mul0r.
  by rewrite -big_distrr /= -(Hcond a Pa0) fdistmapE.
have HfstA : forall a0,
    `Pr[ ((fun ab => ab.1) : {RV (P `X W) -> A}) = a0 ] = P a0.
  move=> a0; rewrite pfwd1E.
  have -> : finset (preim ((fun ab : A * B => ab.1)) (pred1 a0))
      = ((finset (preim (@id A) (pred1 a0))) `*T).
    by apply/setP => -[a' b]; rewrite !inE.
  rewrite -Pr_fdist_fst fdist_prod1.
  have -> : finset (preim (@id A) (pred1 a0)) = [set a0].
    by apply/setP => x; rewrite !inE.
  by rewrite Pr_set1.
have HZz : forall z0, `Pr[ (Z : {RV (P `X W) -> T}) = z0 ] = mu z0.
  move=> z0; rewrite pfwd1E /Pr.
  under eq_bigl => ab do rewrite inE /=.
  under eq_bigr => ab _ do rewrite fdist_prodE.
  transitivity (\sum_(a' : A) (P a' * mu z0)); last first.
    by rewrite -big_distrl /= FDist.f1 mul1r.
  rewrite (partition_big (fun ab => ab.1) xpredT) //=.
  apply: eq_bigr => a' _.
  rewrite -(HZa a' z0) /Pr.
  apply: eq_big => [ab | ab _]; last by rewrite fdist_prodE.
  by rewrite inE /= xpair_eqE andbC.
by move=> z a; rewrite pfwd1E HZa HZz HfstA mulrC.
Qed.

(** A kernel product P `X W pushes forward under f to mu whenever every
    positive-mass first-coordinate section of f pushes W a to mu. Applied to
    the all-decks dealer, this collapses the secret-dependent deck-and-shuffle
    law to a single secret-independent law on coalition views. *)
Lemma fdistmap_prod_const (T : finType) (f : A * B -> T) (mu : R.-fdist T) :
  (forall a, P a != 0 -> fdistmap (fun b => f (a, b)) (W a) = mu) ->
  fdistmap f (P `X W) = mu.
Proof.
move=> Hf; apply: fdist_ext => t.
rewrite fdistmapE.
transitivity (\sum_(a : A) P a * mu t); last first.
  by rewrite -big_distrl /= FDist.f1 mul1r.
rewrite (partition_big (fun ab => ab.1) xpredT) //=.
apply: eq_bigr => a _.
have [Pa0|Pa0] := eqVneq (P a) 0.
  rewrite Pa0 mul0r; apply: big1 => ab /andP[_ /eqP Hab1].
  by rewrite fdist_prodE Hab1 Pa0 mul0r.
rewrite (reindex_onto (fun b : B => (a, b)) (fun i => i.2)); last first.
  by move=> [a' b] /= /andP[_ /eqP ->].
under eq_bigl => b do rewrite /= !eqxx !andbT.
under eq_bigr => b _ do rewrite fdist_prodE /=.
by rewrite -big_distrr /= -(Hf a Pa0) fdistmapE.
Qed.

(** Over a plain product P `x P2, if every positive-mass second-coordinate
    section of f pushes the first marginal to the same law mu, the pair
    pushforward is mu. This is fdistmap_prod_const with the roles of the two
    coordinates swapped, used to absorb the shuffle coordinate rather than the
    deck coordinate (alldecks_shuffle_absorb). *)
Lemma fdistmap_prod_snd_const (T : finType) (P2 : R.-fdist B)
    (f : A * B -> T) (mu : R.-fdist T) :
  (forall b, P2 b != 0 -> fdistmap (fun a => f (a, b)) P = mu) ->
  fdistmap f (P `x P2) = mu.
Proof.
move=> Hf; apply: fdist_ext => t.
rewrite fdistmapE.
transitivity (\sum_(b : B) mu t * P2 b); last first.
  by rewrite -big_distrr /= FDist.f1 mulr1.
rewrite (partition_big (fun ab => ab.2) xpredT) //=.
apply: eq_bigr => b _.
have [Pb0|Pb0] := eqVneq (P2 b) 0.
  rewrite Pb0 mulr0; apply: big1 => ab /andP[_ /eqP Hab2].
  by rewrite fdist_prodE Hab2 Pb0 mulr0.
rewrite (reindex_onto (fun a : A => (a, b)) (fun i => i.1)); last first.
  by move=> [a b'] /= /andP[_ /eqP ->].
under eq_bigl => a do rewrite /= !eqxx !andbT.
under eq_bigr => a _ do rewrite fdist_prodE /=.
by rewrite -big_distrl /= -(Hf b Pb0) fdistmapE.
Qed.

End kernel_independence.

Section uniform_supp_bij.
Local Open Scope ring_scope.
Variables (R : realType) (A : finType) (C : {set A}).
Hypothesis card_C_gt0 : (0 < #|C|)%N.

(** An injective endomap of A that stabilizes a support set C, mapping C to C
    and its complement to its complement, pushes the uniform law on C to
    itself. Applied to a shuffle permutation stabilizing the valid-deck set of
    a fixed orbit class, this shows shuffling a uniformly drawn valid deck
    yields another uniformly drawn valid deck of the same class
    (alldecks_shuffle_absorb). *)
Lemma fdist_uniform_supp_bij (f : A -> A) :
  injective f -> (forall a, (f a \in C) = (a \in C)) ->
  fdistmap f (fdist_uniform_supp R card_C_gt0) = fdist_uniform_supp R card_C_gt0.
Proof.
move=> finj Hstab.
have [f' f'K f'K'] := injF_bij finj.
apply: fdist_ext => a.
rewrite fdistmapE.
rewrite (eq_bigl (fun a0 => a0 == f' a)); last first.
  by move=> i; rewrite !inE /= (can2_eq f'K f'K').
rewrite big_pred1_eq.
have HfC : (f' a \in C) = (a \in C) by rewrite -{2}(f'K' a) Hstab.
case: (boolP (a \in C)) => Ha.
  have HfaC : f' a \in C by rewrite HfC.
  by rewrite (fdist_uniform_supp_in R card_C_gt0 HfaC)
             (fdist_uniform_supp_in R card_C_gt0 Ha).
have HfaC : f' a \notin C by rewrite HfC.
by rewrite (fdist_uniform_supp_notin R card_C_gt0 HfaC)
           (fdist_uniform_supp_notin R card_C_gt0 Ha).
Qed.

End uniform_supp_bij.

Section transitivity_privacy.
Variables (N' : nat) (gT : finGroupType) (G : {group gT}).
Variable rho : {morphism G >-> {perm 'I_N'.+1}}.
Variable t : nat.
Hypothesis rhoG_ntrans : ntransitive t (rho @* G) [set: 'I_N'.+1] 'P.

(** For k <= t and a fixed injective source k-tuple p, the map g |-> the
    k-tuple image of p under rho g has every fiber of the same size
    #|G| %/ #|dtuple_on k [set: 'I_N'.+1]|, uniformly over target tuples q in
    dtuple_on k. This equal-fiber-size fact is the combinatorial core of the
    file: it is what turns a uniform draw of the shuffle group element into a
    uniform draw of the k-tuple it produces, the mechanism behind every
    view-independence result below. *)
Lemma rho_tuple_fiber_card (k : nat) (p q : k.-tuple 'I_N'.+1) :
  (k <= t)%N -> p \in dtuple_on k [set: 'I_N'.+1] ->
  q \in dtuple_on k [set: 'I_N'.+1] ->
  #|[set g in G | [tuple (rho g) (tnth p i) | i < k] == q]|
  = (#|G| %/ #|dtuple_on k [set: 'I_N'.+1]|)%N.
Proof.
move=> Hkt Hp Hq.
have ktrans : [transitive^k rho @* G, on [set: 'I_N'.+1] | 'P].
  exact: (ntransitive_weak Hkt rhoG_ntrans).
have phiE : forall g, [tuple (rho g) (tnth p i) | i < k] = n_act 'P p (rho g).
  by move=> g; apply: eq_from_tnth => i; rewrite tnth_mktuple tnth_map.
pose Fb := fun r : k.-tuple 'I_N'.+1 => [set g in G | n_act 'P p (rho g) == r].
have goalE : [set g in G | [tuple (rho g) (tnth p i) | i < k] == q] = Fb q.
  by apply/setP => g; rewrite !inE phiE.
rewrite goalE.
have nactM : forall (u : k.-tuple 'I_N'.+1) (a b : {perm 'I_N'.+1}),
    n_act 'P u (a * b) = n_act 'P (n_act 'P u a) b.
  by move=> u a b; exact: (actM (n_act_action 'P k) u a b).
have nact1 : forall (u : k.-tuple 'I_N'.+1), n_act 'P u 1 = u.
  by move=> u; exact: (act1 (n_act_action 'P k) u).
have Heq : forall r, r \in dtuple_on k [set: 'I_N'.+1] -> #|Fb r| = #|Fb q|.
  move=> r Hr.
  have [h hin hqr] := atransP2 ktrans Hq Hr.
  have [g0 g0G _ hg0] := morphimP hin.
  have hr : n_act 'P q (rho g0) = r by rewrite hqr hg0.
  have -> : Fb r = [set (x * g0)%g | x in Fb q].
    apply/setP => x; rewrite inE; apply/idP/imsetP.
    - move=> /andP[xG /eqP xr].
      exists (x * g0^-1)%g; last by rewrite -mulgA mulVg mulg1.
      rewrite inE; apply/andP; split; first by rewrite groupM // groupV.
      apply/eqP.
      by rewrite morphM ?groupV // morphV // nactM xr -hr -nactM mulgV nact1.
    - case=> y; rewrite inE => /andP[yG /eqP yq] ->.
      apply/andP; split; first by rewrite groupM.
      by apply/eqP; rewrite morphM // nactM yq hr.
  exact: (card_imset (Fb q) (mulIg g0)).
have HG0 : (0 < #|dtuple_on k [set: 'I_N'.+1]|)%N by apply/card_gt0P; exists q.
have Hpart : #|G| = #|dtuple_on k [set: 'I_N'.+1]| * #|Fb q|.
  transitivity (\sum_(g in G) 1); first by rewrite sum1_card.
  rewrite (partition_big (fun g => n_act 'P p (rho g))
             (mem (dtuple_on k [set: 'I_N'.+1]))); last first.
    by move=> g gG; apply: n_act_dtuple => //; apply/astabsP => x; rewrite !inE.
  rewrite (eq_bigr (fun _ => #|Fb q|)); last first.
    by move=> r Hr; rewrite sum1dep_card -(Heq r Hr).
  by rewrite sum_nat_const.
by rewrite Hpart (mulKn _ HG0).
Qed.

Section redeal.
Variable orbit_class : N'.+1.-tuple 'I_N'.+1 -> bool.
Variable deck_ok : N'.+1.-tuple 'I_N'.+1 -> bool.
Hypothesis deck_ok_uniq : forall sh, deck_ok sh -> uniq sh.
Hypothesis orbit_class_inv : forall g sh, g \in G ->
  orbit_class [tuple tnth sh (rho g i) | i < N'.+1] = orbit_class sh.
Hypothesis deck_ok_stable : forall g sh, g \in G ->
  deck_ok [tuple tnth sh (rho g i) | i < N'.+1] = deck_ok sh.
Hypothesis orbit_class_onto : forall b : bool,
  exists sh, deck_ok sh /\ orbit_class sh = b.

(** For a t-transitive shuffle over a distinct-card deck, every coalition of
    at most t positions, and every target secret s2, some re-dealt valid
    arrangement agrees with the coalition's exact view while carrying secret
    s2. This is exactly the shape of a ThresholdScheme's ts_private
    obligation (pgg_sharing_framework.v): proved once here for any
    t-transitive monodromy, so no scheme built from one needs to reprove
    it. *)
Theorem ttrans_private (s2 : bool) (sh : N'.+1.-tuple 'I_N'.+1)
    (C : {set 'I_N'.+1}) :
  (#|C| <= t)%N -> deck_ok sh ->
  exists sh', [/\ deck_ok sh', orbit_class sh' = s2 &
    forall i, i \in C -> tnth sh' i = tnth sh i].
Proof.
move=> card_C_gt0 Hsh.
have [sh2 [Hsh2 Hsh2c]] := orbit_class_onto s2.
have sh_inj : injective (tnth sh) by apply/tuple_uniqP; exact: deck_ok_uniq.
have sh2_inj : injective (tnth sh2) by apply/tuple_uniqP; exact: deck_ok_uniq.
have [ps psE] : {ps : {perm 'I_N'.+1} | ps =1 tnth sh}.
  by exists (perm sh_inj); exact: permE.
have [ps2 ps2E] : {ps2 : {perm 'I_N'.+1} | ps2 =1 tnth sh2}.
  by exists (perm sh2_inj); exact: permE.
pose pih := (ps * ps2^-1)%g.
pose k := size (enum C).
pose st : k.-tuple 'I_N'.+1 := in_tuple (enum C).
pose tt : k.-tuple 'I_N'.+1 := [tuple pih (tnth st l) | l < k].
have Hk : (k <= t)%N by rewrite /k -cardE.
have Hst : st \in dtuple_on k [set: 'I_N'.+1].
  by rewrite inE; apply/andP; split; [rewrite enum_uniq | apply/subsetP].
have stinj : injective (tnth st) by apply/tuple_uniqP; exact: enum_uniq.
have Htt : tt \in dtuple_on k [set: 'I_N'.+1].
  rewrite inE; apply/andP; split; last by apply/subsetP.
  by apply/tuple_uniqP => i j; rewrite !tnth_mktuple => /perm_inj/stinj->.
have ktrans : [transitive^k rho @* G, on [set: 'I_N'.+1] | 'P].
  exact: (ntransitive_weak Hk rhoG_ntrans).
have [h hin htt] := atransP2 ktrans Hst Htt.
have [g gG _ hg] := morphimP hin.
have httE : forall l, h (tnth st l) = pih (tnth st l).
  move=> l; move: (congr1 (fun z : k.-tuple _ => tnth z l) htt).
  by rewrite tnth_mktuple tnth_map => ->.
have hpi : forall i, i \in C -> rho g i = pih i.
  move=> i iC.
  have iC2 : i \in st by rewrite mem_enum.
  by case/tnthP: iC2 => l ->; rewrite -hg httE.
exists [tuple tnth sh2 (rho g i) | i < N'.+1]; split.
- by rewrite (deck_ok_stable sh2 gG).
- by rewrite (orbit_class_inv sh2 gG).
- move=> i iC.
  by rewrite tnth_mktuple (hpi i iC) -ps2E /pih permM permKV psE.
Qed.

End redeal.

Section point_marginal.
Local Open Scope ring_scope.
Variable R : realType.

(** For a shuffle drawn uniformly from G, the single card value a fixed
    position s receives, rho g s, is itself exactly uniform over 'I_N'.+1.
    This is the k = 1 case of rho_tuple_fiber_card: it says a single
    corrupted party's observed card carries no information about which
    element of G was drawn, before any secret-dependent encoding is applied
    on top. *)
Lemma ttrans_point_uniform (Hpos : (0 < #|G|)%N) (s : 'I_N'.+1) :
  (0 < t)%N ->
  fdistmap (fun g : gT => rho g s) (`U Hpos : R.-fdist gT)
  = fdist_uniform (card_ord N'.+1).
Proof.
move=> t_gt0.
have Ht1 : (1 <= t)%N by [].
have Hs1 : [tuple s] \in dtuple_on 1 [set: 'I_N'.+1].
  by rewrite inE /=; apply/subsetP.
have key : forall (a : 'I_N'.+1) (g : gT),
  ([tuple rho g (tnth [tuple s] i) | i < 1] == [tuple a]) = (rho g s == a).
  move=> a g.
  by rewrite -!(inj_eq val_inj) /= [enum 'I_1]enum_ordSl enum_ord0 /=
    (tnth_nth s) /= eqseq_cons andbT.
set d := #|dtuple_on 1 [set: 'I_N'.+1]|.
set f := (#|G| %/ d)%N.
have fibE : forall a, #|[set g in G | rho g s == a]| = f.
  move=> a.
  have Ha : [tuple a] \in dtuple_on 1 [set: 'I_N'.+1].
    by rewrite inE /=; apply/subsetP.
  rewrite /f /d -(rho_tuple_fiber_card Ht1 Hs1 Ha).
  by apply: eq_card => g; rewrite !inE key.
have Hf : #|G| = (N'.+1 * f)%N.
  rewrite -[LHS]sum1_card (partition_big (fun g => rho g s) xpredT) //=.
  rewrite (eq_bigr (fun=> f)); last first.
    move=> a _; rewrite -(fibE a) sum1dep_card.
    by apply: eq_card => g; rewrite !inE.
  by rewrite sum_nat_const card_ord.
apply: fdist_ext => a.
rewrite fdistmapE fdist_uniformE card_ord.
rewrite (bigID (fun a0 => a0 \in G)) /=.
rewrite [X in (_ + X)%R]big1; last first.
  by move=> a0 /andP[_ Ha0]; rewrite fdist_uniform_supp_notin.
rewrite addr0.
rewrite (eq_bigr (fun=> (#|G|%:R^-1))); last first.
  by move=> i /andP[_ Hi]; rewrite fdist_uniform_supp_in.
rewrite sumr_const.
have -> : #|(fun i : gT =>
    (i \in preim (fun g : gT => rho g s) (pred1 a)) && (i \in G))| = f.
  by rewrite -(fibE a); apply: eq_card => i; rewrite !inE andbC.
have HGR : (#|G|%:R != 0 :> R) by rewrite pnatr_eq0 -lt0n.
have HNR : (N'.+1%:R != 0 :> R) by rewrite pnatr_eq0.
apply: (mulfI HGR).
by rewrite mulrnAr (mulfV HGR) Hf natrM mulrAC (mulfV HNR) mul1r.
Qed.

End point_marginal.

Section view_indep.
Local Open Scope proba_scope.
Variable R : realType.
Variable secretP : R.-fdist bool.
Hypothesis card_G_gt0 : (0 < #|G|)%N.
Variable encode : bool -> N'.+1.-tuple 'I_N'.+1.
Let P : R.-fdist (bool * gT)%type := secretP `x (`U card_G_gt0).

(** The random variable of what coalition C observes at a sample (secret,
    shuffle): the dealt card at each position rho g i for i in C, padded with
    ord0 outside C so the codomain does not depend on C. This is the "view"
    every independence result in the file names; proving it independent of
    dealt_secret is the file's privacy claim. *)
Definition coalition_view (C : {set 'I_N'.+1})
    : {RV P -> {ffun 'I_N'.+1 -> 'I_N'.+1}} :=
  fun u => [ffun i => if i \in C then tnth (encode u.1) (rho u.2 i) else ord0].

(** The secret-component projection u.1 of a sample (secret, shuffle): the
    random variable the coalition's view must be shown independent of. *)
Definition dealt_secret : {RV P -> bool} := fun u => u.1.

(** A single corrupted position's view of the uniformly shuffled deal is
    independent of the dealt secret, given a transitive shuffle group and an
    injective per-secret card encoding. This is the size-1 coalition case;
    Section 5 below (ttrans_view_indep_gen) generalizes it to every coalition
    of at most t positions. *)
Lemma ttrans_view_indep (i0 : 'I_N'.+1) :
  (0 < t)%N -> (forall b, uniq (encode b)) ->
  P |= coalition_view [set i0] _|_ dealt_secret.
Proof.
move=> t_gt0 Huniq.
pose pf := fun v : 'I_N'.+1 =>
  [ffun i : 'I_N'.+1 => if i \in [set i0] then v else ord0].
pose mu : R.-fdist {ffun 'I_N'.+1 -> 'I_N'.+1} :=
  fdistmap pf (fdist_uniform (card_ord N'.+1)).
apply: (@inde_prod_fst R bool gT secretP (`U card_G_gt0) _
  (coalition_view [set i0]) mu) => b.
have inj_b : injective (tnth (encode b)) by apply/tuple_uniqP; exact: Huniq.
have -> : (fun b0 : gT => coalition_view [set i0] (b, b0))
        = pf \o (tnth (encode b) \o (fun g0 : gT => rho g0 i0)).
  apply: boolp.funext => g0 /=; apply/ffunP => i.
  rewrite /coalition_view !ffunE.
  case Hi: (i \in [set i0]) => //.
  by move: Hi; rewrite in_set1 => /eqP ->.
rewrite -fdistmap_comp -fdistmap_comp.
rewrite ttrans_point_uniform //.
by rewrite (bij_uniform _ _ (injF_bij inj_b)).
Qed.

End view_indep.

End transitivity_privacy.

From infotheo Require Import entropy.

Section monotone_ramp.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Context {R : realType} {U : finType} (P : R.-fdist U).
Variables (secretT viewT viewT' : finType).
Variables (secret : {RV P -> secretT}) (fullview : {RV P -> viewT}).
Variable proj : viewT -> viewT'.

(** Conditioning on the pair (W, Z) cannot raise entropy above conditioning
    on Z alone: `H(X | [%W, Z]) <= `H(X | Z). This monotonicity-in-conditioning
    fact is the information-theoretic step view_mutual_info_le turns into the
    data-processing inequality for a deterministic view reduction. *)
Lemma centropy_pair_le (TX TW TZ : finType)
    (X : {RV P -> TX}) (W : {RV P -> TW}) (Z : {RV P -> TZ}) :
  `H(X | [% W, Z]) <= `H(X | Z).
Proof.
move: (cond_mutual_info_ge0 `p_[% X, W, Z]).
by rewrite /cond_mutual_info fdist_proj13_RV3 fdistA_RV3 subr_ge0.
Qed.

(** A deterministic reduction proj of the full view cannot increase the
    mutual information shared with the secret: `I(secret ; proj `o fullview)
    <= `I(secret ; fullview). This is the data-processing inequality at the
    random-variable level, and it is what makes a (k, T)-ramp ordering of
    leakage well-defined: shrinking or coarsening what a coalition observes
    never increases what it learns about the secret. *)
Lemma view_mutual_info_le :
  `I(secret ; proj `o fullview) <= `I(secret ; fullview).
Proof.
rewrite !mutual_info_RVE lerD2l lerN2.
rewrite -(centropy_RV_contraction secret fullview proj).
exact: centropy_pair_le.
Qed.

End monotone_ramp.

Section transitivity_privacy_gen.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Variables (N' : nat) (gT : finGroupType) (G : {group gT}).
Variable rho : {morphism G >-> {perm 'I_N'.+1}}.
Variable t : nat.
Hypothesis rhoG_ntrans : ntransitive t (rho @* G) [set: 'I_N'.+1] 'P.
Variable R : realType.
Variable secretP : R.-fdist bool.
Hypothesis card_G_gt0 : (0 < #|G|)%N.
Variable encode : bool -> N'.+1.-tuple 'I_N'.+1.

(** The uniform shuffle, pushed forward through the coalition's encoded
    k-tuple map g |-> the encode-b values at the k positions rho g moves the
    source tuple p to, is uniform over dtuple_on k. This upgrades
    rho_tuple_fiber_card's equal-fiber-size fact to an actual uniform
    pushforward once the secret-dependent card encoding is composed on top of
    the raw shuffle, and it is the computation ttrans_view_indep_gen reduces
    to. *)
Lemma ktuple_encode_uniform (k : nat) (p : k.-tuple 'I_N'.+1) (b : bool)
    (Hdt : (0 < #|dtuple_on k [set: 'I_N'.+1]|)%N) :
  (k <= t)%N -> uniq (encode b) ->
  p \in dtuple_on k [set: 'I_N'.+1] ->
  fdistmap (fun g : gT => [tuple tnth (encode b) (rho g (tnth p l)) | l < k])
    (`U card_G_gt0 : R.-fdist gT) = `U Hdt.
Proof.
move=> Hk Hub Hp.
have b_inj : injective (tnth (encode b)) by apply/tuple_uniqP; exact: Hub.
have [eb ebK ebK'] := injF_bij b_inj.
have phi_in : forall g : gT,
    [tuple tnth (encode b) (rho g (tnth p l)) | l < k]
      \in dtuple_on k [set: 'I_N'.+1].
  move=> g; rewrite inE; apply/andP; split.
    apply/tuple_uniqP => i j; rewrite !tnth_mktuple => /b_inj/perm_inj.
    by move: Hp; rewrite inE => /andP[/tuple_uniqP pinj _]; apply: pinj.
  by apply/subsetP => x _; rewrite inE.
have fibeqgen : forall r : k.-tuple 'I_N'.+1,
    r \in dtuple_on k [set: 'I_N'.+1] ->
    #|[set g in G | [tuple tnth (encode b) (rho g (tnth p l)) | l < k] == r]|
    = (#|G| %/ #|dtuple_on k [set: 'I_N'.+1]|)%N.
  move=> r Hr.
  have Hr' : [tuple eb (tnth r l) | l < k] \in dtuple_on k [set: 'I_N'.+1].
    rewrite inE; apply/andP; split.
      apply/tuple_uniqP => i j; rewrite !tnth_mktuple => /(can_inj ebK').
      by move: Hr; rewrite inE => /andP[/tuple_uniqP rinj _]; apply: rinj.
    by apply/subsetP => x _; rewrite inE.
  rewrite -(rho_tuple_fiber_card rhoG_ntrans Hk Hp Hr').
  apply: eq_card => g; rewrite !inE; congr (_ && _).
  apply/idP/idP => /eqP Htup; apply/eqP.
    apply: eq_from_tnth => l.
    move: (congr1 (fun z : k.-tuple _ => tnth z l) Htup).
    rewrite !tnth_mktuple => Hl.
    by rewrite -(ebK (rho g (tnth p l))) Hl.
  apply: eq_from_tnth => l.
  move: (congr1 (fun z : k.-tuple _ => tnth z l) Htup).
  rewrite !tnth_mktuple => Hl.
  by rewrite Hl ebK'.
have Hpart : #|G| = (#|dtuple_on k [set: 'I_N'.+1]|
                     * (#|G| %/ #|dtuple_on k [set: 'I_N'.+1]|))%N.
  rewrite -[LHS]sum1_card.
  rewrite (partition_big
    (fun g : gT => [tuple tnth (encode b) (rho g (tnth p l)) | l < k])
    (mem (dtuple_on k [set: 'I_N'.+1]))) /=; last first.
    by move=> g _; exact: phi_in.
  rewrite (eq_bigr (fun=> (#|G| %/ #|dtuple_on k [set: 'I_N'.+1]|)%N));
    last first.
    move=> r Hr; rewrite sum1dep_card -(fibeqgen r Hr).
    by apply: eq_card => g; rewrite !inE.
  by rewrite sum_nat_const.
apply: fdist_ext => q.
rewrite fdistmapE.
case: (boolP (q \in dtuple_on k [set: 'I_N'.+1])) => Hq.
  rewrite fdist_uniform_supp_in //.
  rewrite (bigID (fun g : gT => g \in G)) /=.
  rewrite [X in (_ + X)%R]big1; last first.
    by move=> g /andP[_ Hg]; rewrite fdist_uniform_supp_notin.
  rewrite addr0.
  rewrite (eq_bigr (fun=> (#|G|%:R^-1))); last first.
    by move=> g /andP[_ Hg]; rewrite fdist_uniform_supp_in.
  rewrite sumr_const.
  have -> : #|(fun i : gT =>
    (i \in preim (fun g : gT =>
              [tuple tnth (encode b) (rho g (tnth p l)) | l < k]) (pred1 q))
       && (i \in G))|
  = (#|G| %/ #|dtuple_on k [set: 'I_N'.+1]|)%N.
    by rewrite -(fibeqgen q Hq); apply: eq_card => i; rewrite !inE andbC.
  have HGR : (#|G|%:R != 0 :> R) by rewrite pnatr_eq0 -lt0n.
  have HdR : (#|dtuple_on k [set: 'I_N'.+1]|%:R != 0 :> R).
    by rewrite pnatr_eq0 -lt0n.
  apply: (mulfI HGR).
  by rewrite mulrnAr (mulfV HGR) {2}Hpart natrM mulrAC (mulfV HdR) mul1r.
rewrite fdist_uniform_supp_notin //.
apply: big1 => g Hg.
case/andP: Hg => _ /eqP Hgq.
by move: (phi_in g); rewrite Hgq (negbTE Hq).
Qed.

(** For a t-transitive shuffle over a distinct-card deck, every coalition of
    at most t positions has a view of the shuffled deal independent of the
    dealt secret. This generalizes ttrans_view_indep from a single position to
    an arbitrary coalition of size <= t, and is the coalition-general form of
    the file's distributional privacy claim. *)
Lemma ttrans_view_indep_gen (C : {set 'I_N'.+1}) :
  (#|C| <= t)%N -> (forall b, uniq (encode b)) ->
  secretP `x (`U card_G_gt0) |= coalition_view rho secretP card_G_gt0 encode C _|_
    @dealt_secret gT G R secretP card_G_gt0.
Proof.
move=> card_C_gt0 Huniq.
pose k := size (enum C).
pose p : k.-tuple 'I_N'.+1 := in_tuple (enum C).
have Hk : (k <= t)%N by rewrite /k -cardE.
have Hp : p \in dtuple_on k [set: 'I_N'.+1].
  by rewrite inE; apply/andP;
     split; [exact: enum_uniq | apply/subsetP => x _; rewrite inE].
have Hdt : (0 < #|dtuple_on k [set: 'I_N'.+1]|)%N by apply/card_gt0P; exists p.
pose maskf := fun r : k.-tuple 'I_N'.+1 =>
  [ffun i : 'I_N'.+1 => nth ord0 (val r) (index i (enum C))].
apply: (@inde_prod_fst R bool gT secretP (`U card_G_gt0) _
  (coalition_view rho secretP card_G_gt0 encode C) (fdistmap maskf (`U Hdt))) => b.
have Hcomp : (fun b0 : gT => coalition_view rho secretP card_G_gt0 encode C (b, b0))
    = maskf \o
      (fun g : gT => [tuple tnth (encode b) (rho g (tnth p l)) | l < k]).
  apply: boolp.funext => g; apply/ffunP => i.
  rewrite /= /maskf ffunE /coalition_view ffunE.
  case Hi: (i \in C).
    have Hmem : i \in enum C by rewrite mem_enum Hi.
    have Hj : (index i (enum C) < k)%N by rewrite /k index_mem.
    rewrite -(tnth_nth ord0 _ (Ordinal Hj)) tnth_mktuple.
    have -> : tnth p (Ordinal Hj) = i by rewrite (tnth_nth i) nth_index.
    by [].
  have Hni : i \notin enum C by rewrite mem_enum Hi.
  have Hidx : index i (enum C) = k.
    apply/eqP; rewrite eqn_leq; apply/andP.
    by split; [rewrite /k; exact: index_size | rewrite /k leqNgt index_mem].
  by rewrite Hidx nth_default // size_tuple.
rewrite Hcomp -fdistmap_comp.
by rewrite (@ktuple_encode_uniform k p b Hdt Hk (Huniq b) Hp).
Qed.

Local Open Scope entropy_scope.

(** For C' a subset of C, the mutual information the sub-coalition C' shares
    with the dealt secret is at most what the enclosing coalition C shares:
    leakage about the secret is monotone under coalition inclusion. Proved by
    instantiating view_mutual_info_le's deterministic-reduction bound at the
    restriction of C's view to C', this is the ramp ordering that makes "more
    colluders learn no less" a theorem rather than an assumption. *)
Lemma coalition_view_mutual_info_le (C C' : {set 'I_N'.+1}) :
  C' \subset C ->
  `I(dealt_secret secretP card_G_gt0 ;
       coalition_view rho secretP card_G_gt0 encode C')
    <= `I(dealt_secret secretP card_G_gt0 ; coalition_view rho secretP card_G_gt0 encode C).
Proof.
move=> HCC'.
pose restrict := fun v : {ffun 'I_N'.+1 -> 'I_N'.+1} =>
  [ffun i => if i \in C' then v i else ord0].
have Hview : coalition_view rho secretP card_G_gt0 encode C'
    = restrict `o coalition_view rho secretP card_G_gt0 encode C.
  apply: boolp.funext => u; apply/ffunP => i.
  rewrite /comp_RV /restrict /coalition_view !ffunE.
  case: (boolP (i \in C')) => iC' //=.
  by rewrite (subsetP HCC' _ iC').
rewrite Hview.
exact: view_mutual_info_le.
Qed.

End transitivity_privacy_gen.

Section alldecks_view_indep.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Variables (N' : nat) (gT : finGroupType) (G : {group gT}).
Variable rho : {morphism G >-> {perm 'I_N'.+1}}.
Variable t : nat.
Hypothesis rhoG_ntrans : ntransitive t (rho @* G) [set: 'I_N'.+1] 'P.
Variable R : realType.
Variable secretP : R.-fdist bool.
Hypothesis card_G_gt0 : (0 < #|G|)%N.
Variable orbit_class : N'.+1.-tuple 'I_N'.+1 -> bool.
Variable deck_ok : N'.+1.-tuple 'I_N'.+1 -> bool.
Hypothesis deck_ok_uniq : forall sh, deck_ok sh -> uniq sh.
Hypothesis orbit_class_inv : forall g sh, g \in G ->
  orbit_class [tuple tnth sh (rho g i) | i < N'.+1] = orbit_class sh.
Hypothesis deck_ok_stable : forall g sh, g \in G ->
  deck_ok [tuple tnth sh (rho g i) | i < N'.+1] = deck_ok sh.

(** The set of valid decks belonging to orbit class s: deck_ok sh with
    orbit_class sh = s. This is the support the all-decks dealer draws from
    when it deals a fresh deck for secret s, rather than shuffling one fixed
    deck. *)
Definition class_decks (s : bool) : {set N'.+1.-tuple 'I_N'.+1} :=
  [set sh | deck_ok sh && (orbit_class sh == s)].

Hypothesis card_class_decks_gt0 : forall s : bool, (0 < #|class_decks s|)%N.

(** The joint law of a secret, an independently and uniformly drawn valid
    deck of that secret's class, and an independent uniform shuffle. This is
    the sample space of the all-decks dealer, which redraws the deck itself
    per secret rather than fixing one deck and shuffling it. *)
Definition alldecksP : R.-fdist (bool * (N'.+1.-tuple 'I_N'.+1 * gT)) :=
  secretP `X (fun s => ((`U (card_class_decks_gt0 s)) `x (`U card_G_gt0))).

(** The secret-component projection of an alldecksP sample: the random
    variable the all-decks dealer's coalition view must be shown independent
    of. *)
Definition alldecks_secret : {RV alldecksP -> bool} := fun u => u.1.

(** The card values coalition C observes after the deck is shuffled, padded
    with ord0 outside C. This is alldecksP's analogue of coalition_view: the
    view ttrans_view_indep_alldecks shows independent of the secret. *)
Definition alldecks_view (C : {set 'I_N'.+1}) :
    {RV alldecksP -> {ffun 'I_N'.+1 -> 'I_N'.+1}} :=
  fun u => [ffun i => if i \in C then tnth u.2.1 (rho u.2.2 i) else ord0].

(* The per-class law of the shuffled coalition view is deck-independent:
   uniform over the masked injective value-tuples. *)
Local Lemma alldecks_view_law (C : {set 'I_N'.+1}) (s : bool)
    (Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_N'.+1]|)%N) :
  (#|C| <= t)%N ->
  fdistmap (fun dg => alldecks_view C (s, dg))
    ((`U (card_class_decks_gt0 s)) `x ((`U card_G_gt0) : R.-fdist gT))
  = fdistmap (fun r : (size (enum C)).-tuple 'I_N'.+1 =>
       [ffun i : 'I_N'.+1 => nth ord0 (val r) (index i (enum C))])
      (`U Hdt).
Proof.
move=> card_C_gt0.
pose k := size (enum C).
pose p : k.-tuple 'I_N'.+1 := in_tuple (enum C).
have Hk : (k <= t)%N by rewrite /k -cardE.
have Hp : p \in dtuple_on k [set: 'I_N'.+1].
  by rewrite inE; apply/andP;
     split; [exact: enum_uniq | apply/subsetP => x _; rewrite inE].
apply: (fdistmap_prod_const (P := `U (card_class_decks_gt0 s)) (W := fun _ => `U card_G_gt0)) => sh Hsh.
have Hmem : sh \in class_decks s.
  apply: contraNT Hsh => Hsh'.
  by rewrite (fdist_uniform_supp_notin R (card_class_decks_gt0 s) Hsh') eqxx.
move: Hmem; rewrite inE => /andP[Hok _].
have Huniqsh : uniq sh := deck_ok_uniq Hok.
have Hcomp : (fun g : gT => alldecks_view C (s, (sh, g)))
    = (fun r : k.-tuple 'I_N'.+1 =>
         [ffun i : 'I_N'.+1 => nth ord0 (val r) (index i (enum C))])
      \o (fun g : gT => [tuple tnth sh (rho g (tnth p l)) | l < k]).
  apply: boolp.funext => g; apply/ffunP => i.
  rewrite /alldecks_view /comp !ffunE.
  case Hi: (i \in C).
    have Hmem2 : i \in enum C by rewrite mem_enum Hi.
    have Hj : (index i (enum C) < k)%N by rewrite /k index_mem.
    rewrite -(tnth_nth ord0 [tuple tnth sh (rho g (tnth p l)) | l < k]
              (Ordinal Hj)) tnth_mktuple.
    have -> : tnth p (Ordinal Hj) = i by rewrite (tnth_nth i) nth_index.
    by [].
  have Hni : i \notin enum C by rewrite mem_enum Hi.
  have Hidx : index i (enum C) = k.
    apply/eqP; rewrite eqn_leq; apply/andP.
    by split; [rewrite /k; exact: index_size | rewrite /k leqNgt index_mem].
  by rewrite Hidx nth_default // size_tuple.
rewrite Hcomp -fdistmap_comp.
rewrite (@ktuple_encode_uniform N' gT G rho t rhoG_ntrans R card_G_gt0
          (fun _ => sh) k p true Hdt Hk Huniqsh Hp).
by [].
Qed.

(** A dealer that deals a uniform valid deck of the secret's class and then
    applies a t-transitive uniform shuffle gives every coalition of at most t
    positions a view independent of the secret. This transports
    ttrans_view_indep_gen's fixed-deck privacy claim across a secret-dependent
    choice of deck, the extra freedom a real dealer has over the single-deck
    model of the sections above. *)
Lemma ttrans_view_indep_alldecks (C : {set 'I_N'.+1}) :
  (#|C| <= t)%N -> alldecksP |= alldecks_view C _|_ alldecks_secret.
Proof.
move=> card_C_gt0.
have Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_N'.+1]|)%N.
  apply/card_gt0P; exists (in_tuple (enum C)).
  by rewrite inE; apply/andP;
     split; [exact: enum_uniq | apply/subsetP => x _; rewrite inE].
apply: (inde_prod_kernel_fst
   (mu := fdistmap (fun r : (size (enum C)).-tuple 'I_N'.+1 =>
            [ffun i => nth ord0 (val r) (index i (enum C))]) (`U Hdt))) => s _.
exact: (alldecks_view_law s Hdt card_C_gt0).
Qed.

(** Shuffling a uniformly drawn valid deck of orbit class s by an independent
    uniform group element yields another uniformly drawn valid deck of the
    same class. This is what lets a shuffle be dropped from the all-decks
    model without changing the law of the dealt deck, the step
    ttrans_view_indep_deck needs to pass from a shuffled to a
    representative-free dealer. *)
Lemma alldecks_shuffle_absorb (s : bool) :
  fdistmap (fun shg : N'.+1.-tuple 'I_N'.+1 * gT =>
              [tuple tnth shg.1 (rho shg.2 i) | i < N'.+1])
           ((`U (card_class_decks_gt0 s)) `x ((`U card_G_gt0) : R.-fdist gT))
  = `U (card_class_decks_gt0 s).
Proof.
apply: fdistmap_prod_snd_const => g Hg.
have gG : g \in G.
  apply: contraNT Hg => gN.
  by rewrite (fdist_uniform_supp_notin R card_G_gt0 gN) eqxx.
apply: (fdist_uniform_supp_bij R (card_class_decks_gt0 s)).
  move=> sh1 sh2 Heq; apply: eq_from_tnth => j.
  move: (congr1 (fun T : N'.+1.-tuple 'I_N'.+1 =>
                   tnth T (((rho g)^-1)%g j)) Heq).
  by rewrite !tnth_mktuple permKV.
move=> sh; rewrite /class_decks !inE (@deck_ok_stable g sh gG) (@orbit_class_inv g sh gG).
by [].
Qed.

(** The joint law of a secret and an independently, uniformly drawn valid
    deck of that secret's class, with no shuffle applied. This is alldecksP
    with the shuffle coordinate dropped: the sample space of a dealer that
    hands out a fresh valid deck per secret without shuffling it. *)
Definition uniform_deckP : R.-fdist (bool * N'.+1.-tuple 'I_N'.+1) :=
  secretP `X (fun s => `U (card_class_decks_gt0 s)).

(** The card values coalition C reads directly off the dealt deck, padded
    with ord0 outside C. This is uniform_deckP's analogue of coalition_view,
    the view ttrans_view_indep_deck shows independent of the secret with no
    shuffle in the model. *)
Definition uniform_deck_view (C : {set 'I_N'.+1}) :
    {RV uniform_deckP -> {ffun 'I_N'.+1 -> 'I_N'.+1}} :=
  fun u => [ffun i => if i \in C then tnth u.2 i else ord0].

(** A dealer that deals a uniform valid deck of the secret's class, with no
    shuffle applied afterward, gives every coalition of at most t positions a
    view independent of the secret. This is the representative-free form of
    the all-decks privacy claim: alldecks_shuffle_absorb already makes a
    shuffled uniform deck indistinguishable from an unshuffled one, so the
    shuffle in ttrans_view_indep_alldecks was never load-bearing. *)
Lemma ttrans_view_indep_deck (C : {set 'I_N'.+1}) :
  (#|C| <= t)%N ->
  uniform_deckP |= uniform_deck_view C
    _|_ ((fun u => u.1) : {RV uniform_deckP -> bool}).
Proof.
move=> card_C_gt0.
have Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_N'.+1]|)%N.
  apply/card_gt0P; exists (in_tuple (enum C)).
  by rewrite inE; apply/andP;
     split; [exact: enum_uniq | apply/subsetP => x _; rewrite inE].
apply: (inde_prod_kernel_fst
   (mu := fdistmap (fun r : (size (enum C)).-tuple 'I_N'.+1 =>
            [ffun i => nth ord0 (val r) (index i (enum C))]) (`U Hdt))) => s _.
rewrite -(alldecks_shuffle_absorb s) fdistmap_comp.
rewrite (_ : (fun b => uniform_deck_view C (s, b))
             \o (fun shg : N'.+1.-tuple 'I_N'.+1 * gT =>
                   [tuple tnth shg.1 (rho shg.2 i) | i < N'.+1])
           = (fun dg => alldecks_view C (s, dg))); last first.
  apply: boolp.funext => dg; apply/ffunP => i.
  rewrite /comp /uniform_deck_view /alldecks_view !ffunE.
  case: (i \in C) => //=.
  by rewrite tnth_mktuple.
exact: (alldecks_view_law s Hdt card_C_gt0).
Qed.

End alldecks_view_indep.

Section profile_view_privacy.
Local Open Scope proba_scope.

(** The deck a MonodromyProfile p deals for a two-valued secret: the
    threshold-scheme encoder of p's plug, read at the two secrets sel true
    and sel false, and cast along Hlen from the plug's share count to p's own
    count of card positions pgg_N' (mp_M p) .+1. This repackages an
    arbitrary
    MonodromyProfile's encoder into the encode : bool -> deck shape
    coalition_view and the sections above expect, so profile_view_indep below
    can instantiate the abstract bridge at any profile. *)
Definition profile_deck (p : MonodromyProfile) (sel : bool -> mp_secretT p)
    (Hlen : (ts_T' (rp_scheme (mp_plug p))).+1 = (pgg_N' (mp_M p)).+1)
    (b : bool) : (pgg_N' (mp_M p)).+1.-tuple 'I_(pgg_N' (mp_M p)).+1 :=
  tcast Hlen (ts_encode (rp_scheme (mp_plug p)) (sel b)).

(** For a MonodromyProfile p, transitivity degree t, and per-secret deck
    selector sel, if p's own shuffle image pgg_rho (mp_M p) @* pgg_G (mp_M p)
    is t-transitive on the card positions and the two decks
    profile_deck sel Hlen true and false are each injective, then every
    coalition of at most t
    positions has a view of the shuffled deal, read through p's own rho and
    deck, independent of the Boolean secret. This is ttrans_view_indep_gen
    with every one of its free group/rho/deck parameters replaced by a
    projection of a single MonodromyProfile record: a concrete instance
    inherits the privacy guarantee by supplying only p, sel, Hlen, and the
    transitivity and distinct-deck premises, rather than unpacking the group
    by hand at each instantiation site. Both premises are load-bearing:
    distinct-deck necessity is witnessed by profile_distinct_deck_necessary
    (pgl27_profile_privacy.v); the transitivity premise is calibrated by
    profile_view_indep_sharp, which refutes the coalition bound t.+1 at
    3-transitive PGL(2,7). *)
Lemma profile_view_indep (p : MonodromyProfile) (t : nat)
    (sel : bool -> mp_secretT p)
    (Hlen : (ts_T' (rp_scheme (mp_plug p))).+1 = (pgg_N' (mp_M p)).+1)
    (rhoG_ntrans : ntransitive t (@pgg_rho (mp_M p) @* pgg_G (mp_M p))
                            [set: 'I_(pgg_N' (mp_M p)).+1] 'P)
    (R : realType) (secretP : R.-fdist bool)
    (card_G_gt0 : (0 < #|pgg_G (mp_M p)|)%N)
    (Hdistinct : forall b : bool,
       uniq (ts_encode (rp_scheme (mp_plug p)) (sel b)))
    (C : {set 'I_(pgg_N' (mp_M p)).+1}) :
  (#|C| <= t)%N ->
  secretP `x (`U card_G_gt0)
    |= coalition_view (@pgg_rho (mp_M p)) secretP card_G_gt0 (profile_deck sel Hlen) C
    _|_ dealt_secret secretP card_G_gt0.
Proof.
move=> card_C_gt0.
apply: (ttrans_view_indep_gen rhoG_ntrans secretP card_G_gt0 card_C_gt0).
by move=> b; rewrite /profile_deck val_tcast; exact: Hdistinct.
Qed.

End profile_view_privacy.

Section transitivity_premise_strength.

(** A group A that is t-transitive on S has at least as many elements as S
    has distinct t-tuples: #|t.-dtuple(S)| <= #|A|. Immediate from
    ntransitive as the image of a group action being onto the distinct
    t-tuples. *)
Lemma ntransitive_card_le (aT : finGroupType) (rT : finType)
    (to : {action aT &-> rT}) (A : {group aT}) (S : {set rT}) (t : nat) :
  ntransitive t A S to -> (#|t.-dtuple(S)| <= #|A|)%N.
Proof.
rewrite /ntransitive => /imsetP[x Hx ->].
exact: leq_imset_card.
Qed.

(** The trivial group 1%G is t-transitive on S only if S has at most one
    distinct t-tuple: ntransitive t 1%G S to forces #|t.-dtuple(S)| <= 1.
    This is the non-vacuity check on the file's central hypothesis: the
    t-transitivity premise every privacy result above assumes cannot be
    satisfied by a trivial monodromy group unless the deck itself is
    degenerate, so the premise is doing real work whenever the deck has more
    than one t-tuple of distinct cards. *)
Lemma ntransitive_trivial_degenerate (aT : finGroupType) (rT : finType)
    (to : {action aT &-> rT}) (S : {set rT}) (t : nat) :
  ntransitive t 1%G S to -> (#|t.-dtuple(S)| <= 1)%N.
Proof. by move/ntransitive_card_le; rewrite cards1. Qed.

End transitivity_premise_strength.
