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
From general_dealer_law_probe Require Import dealer_kernel_probe.
From general_dealer_law_probe Require Import carrier_transport_probe.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section PGLDeterministic.

Variable R : realType.
Local Notation deckT := (8.-tuple 'I_8).
Local Notation cutT := (pgg_gT pgl27_M).
Local Notation viewT := ({ffun 'I_8 -> 'I_8}).

(** pgl_delta — the deterministic dealer of the exact PGL(2,7) row: at each
    orbit secret it lays the one representative deck orbit_encode s, with no
    randomness of its own.  It is the extreme case of a dealer kernel, and the
    one for which the deck is a function of the secret rather than a hidden
    draw. *)
Definition pgl_delta (s : bool) : R.-fdist deckT :=
  fdist1 (orbit_encode s).

(** pgl_nu — the cut law: a uniform element of the PGL(2,7) shuffle group. *)
Definition pgl_nu : R.-fdist cutT := `U pgl27_G_pos.

(** pgl_dealerP — the exact row's data placed in the dealer model's sample
    space, an orbit secret paired with a deck and a cut. *)
Definition pgl_dealerP : R.-fdist (bool * (deckT * cutT)) :=
  @dealer_shuffleP R bool deckT cutT
    (fdist_uniform card_bool) pgl_delta pgl_nu.

(** pgl_embed — the map that restores the deterministic deck to a sample of
    the exact row, which carries only a secret and a cut.  It is injective and
    its image is the support of the dealer law, so nothing is lost. *)
Definition pgl_embed (u : bool * cutT) : bool * (deckT * cutT) :=
  (u.1, (orbit_encode u.1, u.2)).

(** pgl_dealerP_map — the exact row's law pushed along pgl_embed is the dealer
    model's law at the deterministic kernel.  Here the modelling claim is
    checked rather than assumed: the row's two-coordinate law and the model's
    three-coordinate law agree once the deck coordinate is filled in by the
    function the row leaves implicit. *)
Lemma pgl_dealerP_map :
  fdistmap pgl_embed (pgl27P R) = pgl_dealerP.
Proof.
apply: fdist_ext => -[s [d g]].
rewrite fdistmapE /pgl_embed /pgl_dealerP dealer_shufflePE.
rewrite /pgl_delta /pgl_nu /pgl27P fdist1E.
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
  by move: Hd; rewrite -H eqxx.
Qed.

(** pgl_generic_view C — the card values a coalition C reads off the laid deck
    after the cut has acted, and ord0 at every position outside C.  Written as
    a function of the dealer model's three coordinates, it reads the secret
    only through the deck. *)
Definition pgl_generic_view (C : {set 'I_8})
    (s : bool) (d : deckT) (g : cutT) : viewT :=
  [ffun i => if i \in C then
     tnth d (@pgg_rho pgl27_M g i) else ord0].

(** pgl_view_square — the dealer model's view, composed with pgl_embed, is the
    exact row's view.  One of the two commuting equations carrier transport
    demands. *)
Lemma pgl_view_square (C : {set 'I_8}) :
  @dealer_view R bool deckT cutT viewT
     (fdist_uniform card_bool) pgl_delta pgl_nu
     (pgl_generic_view C) \o pgl_embed = pgl27_view R C.
Proof. by []. Qed.

(** pgl_secret_square — the dealer model's secret, composed with pgl_embed, is
    the exact row's orbit secret.  The other commuting equation. *)
Lemma pgl_secret_square :
  @dealer_secret R bool deckT cutT
      (fdist_uniform card_bool) pgl_delta pgl_nu \o pgl_embed =
    pgl27_secret R.
Proof. by []. Qed.

(** pgl_common_mu C Hdt — the law of a uniformly chosen injective placement of
    #|C| of the eight card values on the positions of C.  It is the common
    view law the two secrets must share, and it names no secret, which is the
    whole content of privacy at this coalition size. *)
Definition pgl_common_mu (C : {set 'I_8})
    (Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N) :
    R.-fdist viewT :=
  fdistmap (fun r : (size (enum C)).-tuple 'I_8 =>
      [ffun i : 'I_8 => nth ord0 (val r) (index i (enum C))])
    (`U Hdt).

(** pgl_fixed_view_law — at the representative deck of either secret, the
    uniform cut sends a coalition of at most three positions to the common
    law.  This is 3-transitivity of PGL(2,7) used at one deck, and it is where
    the group-theoretic content of the exact row enters the dealer model. *)
Lemma pgl_fixed_view_law (C : {set 'I_8}) (s : bool)
    (Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N) :
  (#|C| <= 3)%N ->
  fdistmap (fun g => pgl_generic_view C s (orbit_encode s) g)
    pgl_nu = @pgl_common_mu C Hdt.
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
by rewrite (@ktuple_encode_uniform 7 cutT (pgg_G pgl27_M)
  (@pgg_rho pgl27_M) 3 pgl27_3transitive R pgl27_G_pos
  orbit_encode k p s Hdt Hk (orbit_encode_deck s) Hp).
Qed.

(** pgl_generic_indep — in the dealer model's sample space at the
    deterministic kernel, the view of a coalition of at most three positions
    is independent of the orbit secret.  It is dealer_view_indep at
    pgl_common_mu; the deterministic kernel makes the mixed-law premise a
    statement about a single deck, which pgl_fixed_view_law supplies. *)
Lemma pgl_generic_indep (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  pgl_dealerP |= @dealer_view R bool deckT cutT viewT
    (fdist_uniform card_bool) pgl_delta pgl_nu
    (pgl_generic_view C) _|_
    @dealer_secret R bool deckT cutT
      (fdist_uniform card_bool) pgl_delta pgl_nu.
Proof.
move=> HC.
have Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N.
  apply/card_gt0P; exists (in_tuple (enum C)).
  by rewrite inE; apply/andP; split;
     [exact: enum_uniq | apply/subsetP => x _; rewrite inE].
apply: (@dealer_view_indep R bool deckT cutT viewT
  (fdist_uniform card_bool) pgl_delta pgl_nu
  (pgl_generic_view C) (@pgl_common_mu C Hdt)) => s _.
apply: (@fdistmap_prod_const R deckT cutT
  (pgl_delta s) (fun _ => pgl_nu) viewT
  (fun dg => pgl_generic_view C s dg.1 dg.2)
  (@pgl_common_mu C Hdt)) => d Hd.
have Hdeq : d = orbit_encode s.
  apply: contraNeq Hd => Hneq.
  by rewrite /pgl_delta fdist1E (negbTE Hneq) /=.
subst d.
exact: (@pgl_fixed_view_law C s Hdt HC).
Qed.

(** pgl_indep_via_generic — the exact row's own privacy statement, obtained by
    transporting the dealer model's independence back along pgl_embed.  No
    group theory is redone here: 3-transitivity entered at
    pgl_fixed_view_law and this step only rewrites the same law in the row's
    two coordinates. *)
Lemma pgl_indep_via_generic (C : {set 'I_8}) :
  (#|C| <= 3)%N -> pgl27P R |= pgl27_view R C _|_ pgl27_secret R.
Proof.
move=> HC.
have Hgen := @pgl_generic_indep C HC.
rewrite -pgl_dealerP_map in Hgen.
rewrite -(@pgl_view_square C) -pgl_secret_square.
by apply/inde_RV_fdistmap.
Qed.

(** pgl_bad_embed — the embedding with the orbit secret negated in the deck
    coordinate, used only to show that the view equation is not automatic. *)
Definition pgl_bad_embed (u : bool * cutT) :
    bool * (deckT * cutT) :=
  (u.1, (orbit_encode (~~ u.1), u.2)).

(* Expected failure: the view equation under a deck laid for the negated
   secret.  The two sides are convertible only if orbit_encode (~~ b) and
   orbit_encode b are, so erefl does not typecheck against the ascribed
   equation. *)
Fail Definition pgl_bad_view_square (C : {set 'I_8}) :
  @dealer_view R bool deckT cutT viewT
     (fdist_uniform card_bool) pgl_delta pgl_nu
     (pgl_generic_view C) \o pgl_bad_embed = pgl27_view R C := erefl.

End PGLDeterministic.

Print Assumptions pgl_dealerP_map.
Print Assumptions pgl_generic_indep.
Print Assumptions pgl_indep_via_generic.

Section PGLAllDecks.

Variable R : realType.
Local Notation deckT := (8.-tuple 'I_8).
Local Notation cutT := (pgg_gT pgl27_M).
Local Notation viewT := ({ffun 'I_8 -> 'I_8}).

(** pgl_all_delta — the all-decks dealer: at each orbit secret it lays a
    uniform deck of that secret's class.  Unlike pgl_delta it hides a genuine
    draw, and the privacy argument must survive every deck the draw can
    produce. *)
Definition pgl_all_delta (s : bool) : R.-fdist deckT :=
  `U (pgl27_class_decks_pos s).

(** pgl_all_dealerP — the all-decks row's data in the dealer model's sample
    space. *)
Definition pgl_all_dealerP : R.-fdist (bool * (deckT * cutT)) :=
  @dealer_shuffleP R bool deckT cutT (fdist_uniform card_bool)
    pgl_all_delta (`U pgl27_G_pos).

(** pgl_all_dealerP_E — that law is the all-decks law of the reconstruction
    layer, with no map between them: the two definitions are the same
    three-coordinate kernel product written in two vocabularies. *)
Lemma pgl_all_dealerP_E :
  pgl_all_dealerP =
  alldecksP (fdist_uniform card_bool) pgl27_G_pos
    (R := R) pgl27_class_decks_pos.
Proof. by []. Qed.

(** pgl_all_viewE — and the dealer model's view at pgl_generic_view is the
    all-decks view of the reconstruction layer. *)
Lemma pgl_all_viewE (C : {set 'I_8}) :
  @dealer_view R bool deckT cutT viewT
    (fdist_uniform card_bool) pgl_all_delta (`U pgl27_G_pos)
    (pgl_generic_view C) =
  alldecks_view (@pgg_rho pgl27_M) (fdist_uniform card_bool)
    pgl27_G_pos pgl27_class_decks_pos C.
Proof. by []. Qed.

(** pgl_deck_view_law — at every deck without repeated cards, whatever the
    secret, the uniform cut sends a coalition of at most three positions to
    the common law.  This is 3-transitivity again, now at an arbitrary valid
    deck rather than a representative, which is exactly the per-deck premise
    dealer_view_indep_of_deck asks for. *)
Lemma pgl_deck_view_law (C : {set 'I_8}) (s : bool) (d : deckT)
    (Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N) :
  uniq d -> (#|C| <= 3)%N ->
  fdistmap (fun g => pgl_generic_view C s d g)
    ((`U pgl27_G_pos) : R.-fdist cutT) = @pgl_common_mu R C Hdt.
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
by rewrite (@ktuple_encode_uniform 7 cutT (pgg_G pgl27_M)
  (@pgg_rho pgl27_M) 3 pgl27_3transitive R pgl27_G_pos
  (fun _ : bool => d) k p true Hdt Hk Huniq Hp).
Qed.

(* Expected failure: the per-deck view law without the validity premise.  A
   deck with a repeated card does not have the common view law, so uniq d is
   still the first premise and the coalition-size argument lands in its slot:
   "The term HC has type is_true (#|C| <= 3)%N while it is expected to have
   type is_true (uniq d)". *)
Fail Definition pgl_deck_view_law_without_validity
    (C : {set 'I_8}) (s : bool) (d : deckT)
    (Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N)
    (HC : (#|C| <= 3)%N) :
  fdistmap (fun g => pgl_generic_view C s d g)
    ((`U pgl27_G_pos) : R.-fdist cutT) = @pgl_common_mu R C Hdt :=
  @pgl_deck_view_law C s d Hdt HC.

(** pgl_all_indep_via_generic — under the all-decks dealer, the view of a
    coalition of at most three positions is independent of the orbit secret.
    It is dealer_view_indep_of_deck with validity taken to be a deck without
    repeated cards: every deck of a class has that property, and every deck
    with it has the same view law, so the average over decks is not needed and
    the conclusion holds deck by deck. *)
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
have Hvalid : forall (s : bool) (d : deckT),
    pgl_all_delta s d != 0 -> uniq d.
  move=> s d Hd.
  have Hmem : d \in class_decks orbit_class deck_ok s.
    apply: contraNT Hd => Hnot.
    by rewrite /pgl_all_delta
      (fdist_uniform_supp_notin R (pgl27_class_decks_pos s) Hnot) eqxx.
  by move: Hmem; rewrite inE => /andP[Hok _]; exact: Hok.
have Hlaw : forall (s : bool) (d : deckT),
    (fdist_uniform card_bool : R.-fdist bool) s != 0 -> uniq d ->
    fdistmap (pgl_generic_view C s d)
      ((`U pgl27_G_pos) : R.-fdist cutT) = @pgl_common_mu R C Hdt.
  by move=> s d _ Hu; exact: (@pgl_deck_view_law C s d Hdt Hu HC).
have Hgen := @dealer_view_indep_of_deck R bool deckT cutT viewT
  (fdist_uniform card_bool) pgl_all_delta
  ((`U pgl27_G_pos) : R.-fdist cutT)
  (fun _ d => uniq d) (pgl_generic_view C) (@pgl_common_mu R C Hdt)
  Hvalid Hlaw.
rewrite -pgl_all_dealerP_E -(@pgl_all_viewE C).
exact: Hgen.
Qed.

End PGLAllDecks.

Print Assumptions pgl_all_dealerP_E.
Print Assumptions pgl_deck_view_law.
Print Assumptions pgl_all_indep_via_generic.
