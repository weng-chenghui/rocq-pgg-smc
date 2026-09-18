From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order boolp reals.
From mathcomp Require Import primitive_action.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme.
From pgg_smc Require Import pgl27_profile pgl27_secrecy.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import transitivity_privacy.

Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section GenericCopy.

Variables (R0 : realType) (S0 D0 G0 V0 : finType).
Variable P0 : R0.-fdist S0.
Variable delta0 : S0 -> R0.-fdist D0.
Variable nu0 : R0.-fdist G0.

Definition bridge_dealerP : R0.-fdist (S0 * (D0 * G0)) :=
  P0 `X (fun s => (delta0 s) `x nu0).

Definition bridge_secret : {RV bridge_dealerP -> S0} := fun u => u.1.

Definition bridge_view (view : S0 -> D0 -> G0 -> V0) :
    {RV bridge_dealerP -> V0} :=
  fun u => view u.1 u.2.1 u.2.2.

Lemma bridge_view_indep (view : S0 -> D0 -> G0 -> V0)
    (mu : R0.-fdist V0) :
  (forall s, P0 s != 0 ->
     fdistmap (fun dg => view s dg.1 dg.2)
       ((delta0 s) `x nu0) = mu) ->
  bridge_dealerP |= bridge_view view _|_ bridge_secret.
Proof.
move=> Hview.
rewrite /bridge_dealerP /bridge_view /bridge_secret.
apply: (inde_prod_kernel_fst (mu := mu)) => s Hs.
exact: Hview Hs.
Qed.

Lemma bridge_pullback (A0 B0 TA0 TB0 : finType)
    (Q0 : R0.-fdist A0) (f0 : A0 -> B0)
    (X0 : B0 -> TA0) (Y0 : B0 -> TB0) :
  fdistmap f0 Q0 |= X0 _|_ Y0 ->
  Q0 |= (X0 \o f0) _|_ (Y0 \o f0).
Proof.
move=> H x y; move: (H x y).
rewrite -!dist_of_RVE /dist_of_RV !fdistmap_comp.
by [].
Qed.

Lemma bridge_pushforward (A0 B0 TA0 TB0 : finType)
    (Q0 : R0.-fdist A0) (f0 : A0 -> B0)
    (X0 : B0 -> TA0) (Y0 : B0 -> TB0) :
  Q0 |= (X0 \o f0) _|_ (Y0 \o f0) ->
  fdistmap f0 Q0 |= X0 _|_ Y0.
Proof.
move=> H x y; move: (H x y).
rewrite -!dist_of_RVE /dist_of_RV !fdistmap_comp.
by [].
Qed.

End GenericCopy.

Section PGLDeterministic.

Variable R : realType.
Local Notation deckT := (8.-tuple 'I_8).
Local Notation cutT := (pgg_gT pgl27_M).
Local Notation viewT := ({ffun 'I_8 -> 'I_8}).

Definition pgl_delta (s : bool) : R.-fdist deckT :=
  fdist1 (orbit_encode s).

Definition pgl_nu : R.-fdist cutT := `U pgl27_G_pos.

Definition pgl_dealerP : R.-fdist (bool * (deckT * cutT)) :=
  bridge_dealerP R bool deckT cutT
    (fdist_uniform card_bool) pgl_delta pgl_nu.

Definition pgl_embed (u : bool * cutT) : bool * (deckT * cutT) :=
  (u.1, (orbit_encode u.1, u.2)).

Lemma pgl_dealerP_map :
  fdistmap pgl_embed (pgl27P R) = pgl_dealerP.
Proof.
apply: fdist_ext => -[s [d g]].
rewrite fdistmapE /pgl_embed /pgl_dealerP /bridge_dealerP.
rewrite /pgl_delta /pgl_nu /pgl27P !fdist_prodE fdist1E.
case Hd: (d == orbit_encode s).
- move/eqP: Hd => Hd; subst d.
  rewrite (big_pred1 (s, g)) /=.
  + by rewrite fdist_prodE /= mul1r.
  + move=> [s' g']; rewrite !inE /= !xpair_eqE.
    by case: eqP => // ->; rewrite eqxx.
- rewrite /= mul0r mulr0.
  apply: big1 => -[s' g'].
  rewrite inE /= !xpair_eqE.
  move=> /andP[/eqP -> /andP[/eqP H /eqP ->]].
  move: Hd; rewrite -H eqxx.
  by [].
Qed.

Definition pgl_generic_view (C : {set 'I_8})
    (s : bool) (d : deckT) (g : cutT) : viewT :=
  [ffun i => if i \in C then
     tnth d (@pgg_rho pgl27_M g i) else ord0].

Lemma pgl_view_square (C : {set 'I_8}) :
  @bridge_view R bool deckT cutT viewT
     (fdist_uniform card_bool) pgl_delta pgl_nu
     (pgl_generic_view C) \o pgl_embed = pgl27_view R C.
Proof. by []. Qed.

Lemma pgl_secret_square :
  @bridge_secret R bool deckT cutT
      (fdist_uniform card_bool) pgl_delta pgl_nu \o pgl_embed =
    pgl27_secret R.
Proof. by []. Qed.

Definition pgl_common_mu (C : {set 'I_8})
    (Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N) :
    R.-fdist viewT :=
  fdistmap (fun r : (size (enum C)).-tuple 'I_8 =>
      [ffun i : 'I_8 => nth ord0 (val r) (index i (enum C))])
    (`U Hdt).

Lemma pgl_fixed_view_law (C : {set 'I_8}) (s : bool)
    (Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N) :
  (#|C| <= 3)%N ->
  fdistmap (fun g => pgl_generic_view C s (orbit_encode s) g)
    pgl_nu = pgl_common_mu C Hdt.
Proof.
move=> HC; pose k := size (enum C).
pose p : k.-tuple 'I_8 := in_tuple (enum C).
have Hk : (k <= 3)%N by rewrite /k -cardE.
have Hp : p \in dtuple_on k [set: 'I_8].
  by rewrite inE; apply/andP; split;
     [exact: enum_uniq | apply/subsetP => x _; rewrite inE].
have Hcomp :
    (fun g : cutT => pgl_generic_view C s (orbit_encode s) g) =
    (fun r : k.-tuple 'I_8 =>
       [ffun i : 'I_8 => nth ord0 (val r) (index i (enum C))]) \o
    (fun g : cutT =>
       [tuple tnth (orbit_encode s)
          (@pgg_rho pgl27_M g (tnth p l)) | l < k]).
  apply: boolp.funext => g; apply/ffunP => i.
  rewrite /pgl_generic_view /comp !ffunE.
  case Hi: (i \in C).
    have Hmem : i \in enum C by rewrite mem_enum Hi.
    have Hj : (index i (enum C) < k)%N by rewrite /k index_mem.
    rewrite -(tnth_nth ord0
      [tuple tnth (orbit_encode s)
         (@pgg_rho pgl27_M g (tnth p l)) | l < k]
      (Ordinal Hj)) tnth_mktuple.
    have -> : tnth p (Ordinal Hj) = i.
      by rewrite (tnth_nth i) nth_index.
    by [].
  have Hni : i \notin enum C by rewrite mem_enum Hi.
  have Hidx : index i (enum C) = k.
    apply/eqP; rewrite eqn_leq; apply/andP.
    by split; [rewrite /k; exact: index_size |
       rewrite /k leqNgt index_mem].
  by rewrite Hidx nth_default // size_tuple.
rewrite Hcomp -fdistmap_comp /pgl_nu /pgl_common_mu.
rewrite (@ktuple_encode_uniform 7 cutT (pgg_G pgl27_M)
  (@pgg_rho pgl27_M) 3 pgl27_3transitive R pgl27_G_pos
  orbit_encode k p s Hdt Hk (orbit_encode_deck s) Hp).
by [].
Qed.

Lemma pgl_generic_indep (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  pgl_dealerP |= @bridge_view R bool deckT cutT viewT
    (fdist_uniform card_bool) pgl_delta pgl_nu
    (pgl_generic_view C) _|_
    @bridge_secret R bool deckT cutT
      (fdist_uniform card_bool) pgl_delta pgl_nu.
Proof.
move=> HC.
have Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N.
  apply/card_gt0P; exists (in_tuple (enum C)).
  by rewrite inE; apply/andP; split;
     [exact: enum_uniq | apply/subsetP => x _; rewrite inE].
apply: (@bridge_view_indep R bool deckT cutT viewT
  (fdist_uniform card_bool) pgl_delta pgl_nu
  (pgl_generic_view C) (pgl_common_mu C Hdt)) => s _.
apply: (@fdistmap_prod_const R deckT cutT
  (pgl_delta s) (fun _ => pgl_nu) viewT
  (fun dg => pgl_generic_view C s dg.1 dg.2)
  (pgl_common_mu C Hdt)) => d Hd.
have Hdeq : d = orbit_encode s.
  apply: contraNeq Hd => Hneq.
  by rewrite /pgl_delta fdist1E (negbTE Hneq) /=.
subst d.
exact: pgl_fixed_view_law HC.
Qed.

Lemma pgl_indep_via_generic (C : {set 'I_8}) :
  (#|C| <= 3)%N -> pgl27P R |= pgl27_view R C _|_ pgl27_secret R.
Proof.
move=> HC.
have Hgen := pgl_generic_indep C HC.
rewrite -pgl_dealerP_map in Hgen.
have Hpull := @bridge_pullback R
  (bool * cutT)%type (bool * (deckT * cutT))%type viewT bool
  (pgl27P R) pgl_embed
  (@bridge_view R bool deckT cutT viewT
    (fdist_uniform card_bool) pgl_delta pgl_nu
    (pgl_generic_view C))
  (@bridge_secret R bool deckT cutT
    (fdist_uniform card_bool) pgl_delta pgl_nu) Hgen.
by rewrite pgl_view_square pgl_secret_square in Hpull.
Qed.

Definition pgl_bad_embed (u : bool * cutT) :
    bool * (deckT * cutT) :=
  (u.1, (orbit_encode (~~ u.1), u.2)).

Fail Definition pgl_bad_view_square (C : {set 'I_8}) :
  @bridge_view R bool deckT cutT viewT
     (fdist_uniform card_bool) pgl_delta pgl_nu
     (pgl_generic_view C) \o pgl_bad_embed = pgl27_view R C := erefl.

Print Assumptions pgl_dealerP_map.
Print Assumptions pgl_generic_indep.
Print Assumptions pgl_indep_via_generic.

End PGLDeterministic.

Section PGLAllDecks.

Variable R : realType.
Local Notation deckT := (8.-tuple 'I_8).
Local Notation cutT := (pgg_gT pgl27_M).
Local Notation viewT := ({ffun 'I_8 -> 'I_8}).

Definition pgl_all_delta (s : bool) : R.-fdist deckT :=
  `U (pgl27_class_decks_pos s).

Definition pgl_all_dealerP : R.-fdist (bool * (deckT * cutT)) :=
  bridge_dealerP R bool deckT cutT (fdist_uniform card_bool)
    pgl_all_delta (`U pgl27_G_pos).

Lemma pgl_all_dealerP_E :
  pgl_all_dealerP =
  alldecksP (fdist_uniform card_bool) pgl27_G_pos
    (R := R) pgl27_class_decks_pos.
Proof. by []. Qed.

Lemma pgl_all_viewE (C : {set 'I_8}) :
  @bridge_view R bool deckT cutT viewT
    (fdist_uniform card_bool) pgl_all_delta (`U pgl27_G_pos)
    (pgl_generic_view C) =
  alldecks_view (@pgg_rho pgl27_M) (fdist_uniform card_bool)
    pgl27_G_pos pgl27_class_decks_pos C.
Proof. by []. Qed.

Lemma pgl_deck_view_law (C : {set 'I_8}) (s : bool) (d : deckT)
    (Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N) :
  uniq d -> (#|C| <= 3)%N ->
  fdistmap (fun g => pgl_generic_view C s d g)
    ((`U pgl27_G_pos) : R.-fdist cutT) = pgl_common_mu R C Hdt.
Proof.
move=> Huniq HC; pose k := size (enum C).
pose p : k.-tuple 'I_8 := in_tuple (enum C).
have Hk : (k <= 3)%N by rewrite /k -cardE.
have Hp : p \in dtuple_on k [set: 'I_8].
  by rewrite inE; apply/andP; split;
     [exact: enum_uniq | apply/subsetP => x _; rewrite inE].
have Hcomp :
    (fun g : cutT => pgl_generic_view C s d g) =
    (fun r : k.-tuple 'I_8 =>
       [ffun i : 'I_8 => nth ord0 (val r) (index i (enum C))]) \o
    (fun g : cutT =>
       [tuple tnth d (@pgg_rho pgl27_M g (tnth p l)) | l < k]).
  apply: boolp.funext => g; apply/ffunP => i.
  rewrite /pgl_generic_view /comp !ffunE.
  case Hi: (i \in C).
    have Hmem : i \in enum C by rewrite mem_enum Hi.
    have Hj : (index i (enum C) < k)%N by rewrite /k index_mem.
    rewrite -(tnth_nth ord0
      [tuple tnth d (@pgg_rho pgl27_M g (tnth p l)) | l < k]
      (Ordinal Hj)) tnth_mktuple.
    have -> : tnth p (Ordinal Hj) = i.
      by rewrite (tnth_nth i) nth_index.
    by [].
  have Hni : i \notin enum C by rewrite mem_enum Hi.
  have Hidx : index i (enum C) = k.
    apply/eqP; rewrite eqn_leq; apply/andP.
    by split; [rewrite /k; exact: index_size |
       rewrite /k leqNgt index_mem].
  by rewrite Hidx nth_default // size_tuple.
rewrite Hcomp -fdistmap_comp /pgl_common_mu.
rewrite (@ktuple_encode_uniform 7 cutT (pgg_G pgl27_M)
  (@pgg_rho pgl27_M) 3 pgl27_3transitive R pgl27_G_pos
  (fun _ : bool => d) k p true Hdt Hk Huniq Hp).
by [].
Qed.

Fail Definition pgl_deck_view_law_without_validity
    (C : {set 'I_8}) (s : bool) (d : deckT)
    (Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N)
    (HC : (#|C| <= 3)%N) :
  fdistmap (fun g => pgl_generic_view C s d g)
    ((`U pgl27_G_pos) : R.-fdist cutT) = pgl_common_mu R C Hdt :=
  pgl_deck_view_law R C s d Hdt HC.

Lemma pgl_all_indep_via_generic (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  alldecksP (fdist_uniform card_bool) pgl27_G_pos
    (R := R) pgl27_class_decks_pos
  |= alldecks_view (@pgg_rho pgl27_M) (fdist_uniform card_bool)
       pgl27_G_pos pgl27_class_decks_pos C
  _|_ alldecks_secret (fdist_uniform card_bool) pgl27_G_pos
       pgl27_class_decks_pos.
Proof.
move=> HC.
have Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N.
  apply/card_gt0P; exists (in_tuple (enum C)).
  by rewrite inE; apply/andP; split;
     [exact: enum_uniq | apply/subsetP => x _; rewrite inE].
have Hgen :
  pgl_all_dealerP |=
    @bridge_view R bool deckT cutT viewT
      (fdist_uniform card_bool) pgl_all_delta (`U pgl27_G_pos)
      (pgl_generic_view C)
    _|_ @bridge_secret R bool deckT cutT
      (fdist_uniform card_bool) pgl_all_delta (`U pgl27_G_pos).
  apply: (@bridge_view_indep R bool deckT cutT viewT
    (fdist_uniform card_bool) pgl_all_delta (`U pgl27_G_pos)
    (pgl_generic_view C) (pgl_common_mu R C Hdt)) => s _.
  apply: (@fdistmap_prod_const R deckT cutT
    (pgl_all_delta s) (fun _ => `U pgl27_G_pos) viewT
    (fun dg => pgl_generic_view C s dg.1 dg.2)
    (pgl_common_mu R C Hdt)) => d Hd.
  have Hmem : d \in class_decks orbit_class deck_ok s.
    apply: contraNT Hd => Hnot.
    by rewrite /pgl_all_delta
      (fdist_uniform_supp_notin R (pgl27_class_decks_pos s) Hnot) eqxx.
  move: Hmem; rewrite inE => /andP[Hok _].
  rewrite /deck_ok in Hok.
  change (fdistmap (fun g => pgl_generic_view C s d g)
    (`U pgl27_G_pos) = pgl_common_mu R C Hdt).
  by apply: pgl_deck_view_law.
rewrite -pgl_all_dealerP_E -pgl_all_viewE.
exact: Hgen.
Qed.

Print Assumptions pgl_all_dealerP_E.
Print Assumptions pgl_all_indep_via_generic.

End PGLAllDecks.
