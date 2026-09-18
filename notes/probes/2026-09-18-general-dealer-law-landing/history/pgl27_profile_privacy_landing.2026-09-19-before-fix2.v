(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_profile_privacy: the eight-card scheme as a monodromy profile        *)
(*                                                                            *)
(* The record-level privacy theorem profile_view_indep                        *)
(* (reconstruct/transitivity_privacy.v) quantifies over an arbitrary          *)
(* MonodromyProfile and carries two mathematical premises about its           *)
(* projections: the image of the action is t-transitive on the card         *)
(* positions, and                                                            *)
(* the two dealt decks carry distinct cards. This file discharges that        *)
(* theorem at the PGL(2,7) orbit scheme and shows that neither premise nor    *)
(* the coalition bound can be relaxed.                                        *)
(*                                                                            *)
(* Discharge. pgl27_profile meets both premises, by pgl27_3transitive         *)
(* (pgl27_group.v) and orbit_encode_deck (pgl27_orbit.v), and the resulting   *)
(* statement is the landed pgl27_view_indep (pgl27_secrecy.v).                *)
(*                                                                            *)
(* Non-vacuity. A t-transitive group is at least as large as the set of       *)
(* distinct t-tuples of the acted set, so the transitivity premise fails for  *)
(* a trivial group on the eight card positions; the PGL(2,7) action image   *)
(* has more                                                                  *)
(* than one element.                                                          *)
(*                                                                            *)
(* Necessity. Both refutations are proved here because their witnesses are    *)
(* PGL(2,7) data: the four heart seats of pgl27_view_dep_k4 for the           *)
(* coalition bound, and constant_deck_profile, a monodromy profile over the   *)
(* same group whose encoder repeats one card, for the distinct-deck premise.  *)
(*                                                                            *)
(* The dealer route. The same two theorems are obtained a third way, from     *)
(* the dealer model of reconstruct/dealer_privacy.v, by placing the two       *)
(* PGL(2,7) rows in its sample space. The exact row goes through the          *)
(* mixed-law condition, its deterministic dealer making that condition a      *)
(* statement about a single deck; the all-decks row goes through the          *)
(* per-deck condition, with validity taken to be a deck without repeated      *)
(* cards. Both restate an existing theorem and replace no proof.              *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   constant_deck_encode == the encoder dealing one repeated card            *)
(*   constant_deck_recon  == the secret read off the card at position zero    *)
(*   constant_deck_scheme == the ThresholdScheme built from those two         *)
(*   constant_deck_monodromy == its trivial share-permutation map             *)
(*   constant_deck_plug      == the ReconPlug carrying that scheme            *)
(*   constant_deck_profile   == the MonodromyProfile dealing a constant deck  *)
(*   pgl27_dealer_delta      == the deterministic dealer of the exact row     *)
(*   pgl27_dealer_nu         == a uniform element of the shuffle group        *)
(*   pgl27_dealerP           == the exact row in the dealer sample space      *)
(*   pgl27_dealer_embed      == the map restoring the deterministic deck      *)
(*   pgl27_dealer_view       == the cards a coalition reads, as a function    *)
(*     of the dealer model's three coordinates                                *)
(*   pgl27_dealer_mu         == the common view law of a coalition            *)
(*   pgl27_alldecks_dealer_delta == the all-decks dealer                      *)
(*   pgl27_alldecks_dealerP  == the all-decks row in that sample space        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_view_indep_via_profile == pgl27_view_indep obtained from           *)
(*     profile_view_indep                                                     *)
(*   pgl27_action_nontrivial == the PGL(2,7) action image has more than one   *)
(*     element                                                                *)
(*   profile_view_indep_sharp == the coalition bound t of profile_view_indep  *)
(*     cannot be weakened to t.+1                                             *)
(*   profile_distinct_deck_necessary == the distinct-deck premise of          *)
(*     profile_view_indep cannot be dropped                                   *)
(*   pgl27_dealerPE == the exact row's law is the dealer model's law at the   *)
(*     deterministic kernel                                                   *)
(*   pgl27_alldecks_dealer_view_law == at every deck without repeated cards   *)
(*     the uniform shuffle sends a coalition of at most three positions to    *)
(*     the common law                                                         *)
(*   pgl27_dealer_view_law == that law at the representative deck             *)
(*   pgl27_dealer_view_indep == independence in the dealer sample space at    *)
(*     the deterministic kernel                                               *)
(*   pgl27_view_indep_via_dealer == pgl27_view_indep obtained from            *)
(*     dealer_shuffle_view_indep                                              *)
(*   pgl27_view_indep_alldecks_via_dealer == pgl27_view_indep_alldecks        *)
(*     obtained from dealer_shuffle_view_indep_of_deck                        *)
(*   pgl27_dealer_viewE == the model's view along the embedding is the exact  *)
(*     row's view                                                             *)
(*   pgl27_dealer_secretE == and its secret is the row's orbit secret         *)
(*   pgl27_alldecks_dealerPE == the all-decks row's law is the model's law    *)
(*   pgl27_alldecks_dealer_viewE == and its view is the all-decks view        *)
(*   pgl27_alldecks_dealer_secretE == and its secret the all-decks secret     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import transitivity_privacy.
From general_dealer_law_landing Require Import dealer_privacy.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme pgl27_profile.
From pgg_smc Require Import pgl27_secrecy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.

Section pgl27_profile_privacy.
Local Open Scope proba_scope.
Local Open Scope ring_scope.
Variable R : realType.

Local Notation ord8_1 := (@Ordinal 8 1 isT).
Local Notation ord8_2 := (@Ordinal 8 2 isT).

(** pgl27_view_indep_via_profile == the eight-card orbit scheme discharges the
    record-level theorem, reproving pgl27_view_indep.  The statement is
    pgl27_view_indep verbatim; only the route differs, so the record-level
    theorem costs the instance nothing beyond its two premises. *)
Lemma pgl27_view_indep_via_profile (C : {set 'I_8}) : (#|C| <= 3)%N ->
  pgl27P R |= pgl27_view R C _|_ pgl27_secret R.
Proof.
move=> HC.
exact: (@profile_view_indep pgl27_profile 3 id erefl pgl27_3transitive
  R (fdist_uniform card_bool) pgl27_G_pos orbit_encode_deck C HC).
Qed.

(** dtuple3_ord8_gt1 == the eight card positions carry more than one
    three-tuple of
    distinct positions. *)
Lemma dtuple3_ord8_gt1 : (1 < #|3.-dtuple([set: 'I_8])|)%N.
Proof.
apply/card_gt1P.
exists [tuple ord0; ord8_1; ord8_2], [tuple ord8_1; ord0; ord8_2]; split.
- by rewrite inE; apply/andP; split; [ | apply/subsetP => x _; rewrite inE].
- by rewrite inE; apply/andP; split; [ | apply/subsetP => x _; rewrite inE].
- by rewrite -val_eqE.
Qed.

(** pgl27_action_nontrivial == the image of the PGL(2,7) representation in the
    symmetric group on the eight card positions has more than one element.
    The
    transitivity premise discharged at PGL(2,7) is met by a non-trivial
    group. *)
Lemma pgl27_action_nontrivial :
  (1 < #|(@pgg_rho pgl27_M @* pgg_G pgl27_M)%g|)%N.
Proof.
exact: (leq_trans dtuple3_ord8_gt1 (ntransitive_card_le pgl27_3transitive)).
Qed.

(** profile_view_indep_sharp == the coalition bound of profile_view_indep is
    sharp: replacing #|C| <= t by #|C| <= t.+1 makes the statement false,
    witnessed at PGL(2,7) with t = 3 by pgl27_view_dep_k4. The coalition-size
    bound of the record-level privacy theorem cannot be weakened. *)
Lemma profile_view_indep_sharp :
  ~ (forall (p : MonodromyProfile) (t : nat) (sel : bool -> mp_secretT p)
       (Hlen : (ts_T' (rp_scheme (mp_plug p))).+1 = (pgg_N' (mp_M p)).+1)
       (Htrans : ntransitive t (@pgg_rho (mp_M p) @* pgg_G (mp_M p))
                   [set: 'I_(pgg_N' (mp_M p)).+1] 'P)
       (secretP : R.-fdist bool)
       (HG : (0 < #|pgg_G (mp_M p)|)%N)
       (Hdistinct : forall b : bool,
          uniq (ts_encode (rp_scheme (mp_plug p)) (sel b)))
       (C : {set 'I_(pgg_N' (mp_M p)).+1}),
     (#|C| <= t.+1)%N ->
     secretP `x (`U HG)
       |= coalition_view (@pgg_rho (mp_M p)) secretP HG
            (profile_deck sel Hlen) C
       _|_ dealt_secret secretP HG).
Proof.
move=> H.
apply: (proj2 (pgl27_view_dep_k4 R)).
apply/inde_RV_sym.
apply: (H pgl27_profile 3 id erefl pgl27_3transitive (fdist_uniform card_bool)
          pgl27_G_pos orbit_encode_deck pgl27_leak_coalition).
by rewrite (proj1 (pgl27_view_dep_k4 R)).
Qed.

(** constant_deck_encode == the encoder dealing card one at every position for
    the secret true and card zero at every position for false. An encoder
    whose dealt deck repeats a single card. *)
Definition constant_deck_encode (b : bool) : 8.-tuple 'I_8 :=
  [tuple (if b then ord8_1 else ord0) | i < 8].

(** constant_deck_recon == reading the secret off the card at position zero.
    The reconstruction map matching constant_deck_encode. *)
Definition constant_deck_recon (sh : 8.-tuple 'I_8) : bool :=
  tnth sh ord0 != ord0.

(** constant_deck_reconK == reconstruction inverts the constant-deck
    encoder. *)
Lemma constant_deck_reconK (s : bool) :
  constant_deck_recon (constant_deck_encode s) = s.
Proof.
by rewrite /constant_deck_recon /constant_deck_encode tnth_mktuple; case: s.
Qed.

(** constant_deck_private == with no corrupted position the constant-deck
    scheme re-deals any arrangement to either secret. *)
Lemma constant_deck_private (s1 s2 : bool) (shares : 8.-tuple 'I_8)
    (C : {set 'I_8}) :
  (#|C| < 1)%N -> constant_deck_recon shares = s1 ->
  exists shares' : 8.-tuple 'I_8,
    constant_deck_recon shares' = s2 /\
    (forall i : 'I_8, i \in C -> tnth shares' i = tnth shares i).
Proof.
move=> HC _; exists (constant_deck_encode s2); split.
  exact: constant_deck_reconK.
have /eqP HC0 : #|C| == 0 by rewrite -leqn0 -ltnS.
by move=> i; rewrite (cards0_eq HC0) inE.
Qed.

(** constant_deck_scheme == the eight-share threshold scheme whose encoder
    deals a single repeated card. A ThresholdScheme meeting every field of the
    record and dealing a non-distinct deck. *)
Definition constant_deck_scheme :
    ThresholdScheme bool 'I_(pgg_N' pgl27_M).+1 :=
  @MkThresholdScheme bool 'I_8 7 0
    (fun s sh => constant_deck_recon sh = s)
    constant_deck_recon constant_deck_encode
    (fun s sh H => H) constant_deck_private constant_deck_reconK.

(** constant_deck_monodromy == the trivial permutation action of the group on
    the shares of constant_deck_scheme. The share-permutation map of the
    counterexample plug. *)
Definition constant_deck_monodromy (g : pgg_gT pgl27_M) : {perm 'I_8} := 1%g.

(** constant_deck_recon_invariant == reconstruction from constant_deck_scheme
    is invariant under constant_deck_monodromy. *)
Lemma constant_deck_recon_invariant :
  @ts_recon_perm_invariant _ (pgg_G pgl27_M) _ _
    constant_deck_scheme constant_deck_monodromy.
Proof.
move=> g s sh _ Hv; rewrite -Hv /= /constant_deck_recon tnth_mktuple.
by rewrite /constant_deck_monodromy perm1.
Qed.

(** constant_deck_plug == the reconstruction plug of the PGL(2,7) group
    carrying constant_deck_scheme. The ReconPlug of the counterexample
    profile. *)
Definition constant_deck_plug : ReconPlug pgl27_M bool :=
  @MkReconPlug pgl27_M bool constant_deck_scheme id
    constant_deck_monodromy constant_deck_recon_invariant.

(** constant_deck_profile == the monodromy profile over the PGL(2,7) group
    whose plug deals a constant deck. A MonodromyProfile meeting every premise
    of profile_view_indep except the distinct-deck one. *)
Definition constant_deck_profile : MonodromyProfile :=
  @MkMonodromyProfile pgl27_M bool pgl27_PI constant_deck_plug.

(** profile_deck_constantE == the deck of constant_deck_profile is the
    constant-deck encoder. *)
Lemma profile_deck_constantE (b : bool) :
  profile_deck (p := constant_deck_profile) id erefl b
  = constant_deck_encode b.
Proof. by []. Qed.

(** constant_deck_view_dep == under constant_deck_profile a single position
    already has a view depending on the dealt secret. A profile meeting every
    premise of profile_view_indep except the distinct-deck one leaks the
    secret at one position. *)
Lemma constant_deck_view_dep :
  ~ pgl27P R |= coalition_view (@pgg_rho pgl27_M) (fdist_uniform card_bool)
                  pgl27_G_pos
                  (profile_deck (p := constant_deck_profile) id erefl)
                  [set ord0]
        _|_ dealt_secret (fdist_uniform card_bool) pgl27_G_pos.
Proof.
set V := coalition_view _ _ _ _ _.
set S := dealt_secret _ _.
move=> Hind.
pose vF : {ffun 'I_8 -> 'I_8} := [ffun _ => ord0].
have HVf : forall g, V (false, g) = vF.
  move=> g; apply/ffunP => i; rewrite /V /coalition_view /vF !ffunE.
  by rewrite profile_deck_constantE /constant_deck_encode tnth_mktuple;
     case: (i \in [set ord0]).
have HVt : forall g, V (true, g) <> vF.
  move=> g /ffunP/(_ ord0); rewrite /V /coalition_view /vF !ffunE.
  rewrite in_set1 eqxx profile_deck_constantE /constant_deck_encode.
  by rewrite tnth_mktuple => /eqP; rewrite -val_eqE.
have Hzero : `Pr[ [% V, S] = (vF, true) ] = 0.
  apply/eqP; apply/negPn; apply/negP => /pfwd1_neq0 [[s g] [Hmem Hpos]].
  move: Hmem; rewrite inE /= xpair_eqE => /andP[/eqP Hv /eqP Hs].
  by move: Hs Hv; rewrite /S /dealt_secret /= => ->; apply: HVt.
have HP1 : forall b : bool, 0 < pgl27P R (b, 1%g).
  move=> b; rewrite /pgl27P fdist_prodE /=; apply: mulr_gt0.
    by rewrite fdist_uniformE invr_gt0 ltr0n card_bool.
  rewrite (@fdist_uniform_supp_in R _ (pgg_G pgl27_M) pgl27_G_pos 1%g
    (group1 _)).
  by rewrite invr_gt0 ltr0n; exact: pgl27_G_pos.
have Hpt : 0 < `Pr[ S = true ].
  rewrite lt0r pfwd1_ge0 andbT.
  apply/pfwd1_neq0; exists (true, 1%g); split; last exact: HP1.
  by rewrite inE.
have Hpv : 0 < `Pr[ V = vF ].
  rewrite lt0r pfwd1_ge0 andbT.
  apply/pfwd1_neq0; exists (false, 1%g); split; last exact: HP1.
  by rewrite inE /= HVf.
move: (mulr_gt0 Hpv Hpt); rewrite -(Hind vF true) Hzero.
by move/lt0r_neq0; rewrite eqxx.
Qed.

(** profile_distinct_deck_necessary == the distinct-deck premise of
    profile_view_indep cannot be dropped: without it the statement is false,
    witnessed by constant_deck_profile. The distinct-deck obligation of the
    record-level privacy theorem is load-bearing. *)
Lemma profile_distinct_deck_necessary :
  ~ (forall (p : MonodromyProfile) (t : nat) (sel : bool -> mp_secretT p)
       (Hlen : (ts_T' (rp_scheme (mp_plug p))).+1 = (pgg_N' (mp_M p)).+1)
       (Htrans : ntransitive t (@pgg_rho (mp_M p) @* pgg_G (mp_M p))
                   [set: 'I_(pgg_N' (mp_M p)).+1] 'P)
       (secretP : R.-fdist bool)
       (HG : (0 < #|pgg_G (mp_M p)|)%N)
       (C : {set 'I_(pgg_N' (mp_M p)).+1}),
     (#|C| <= t)%N ->
     secretP `x (`U HG)
       |= coalition_view (@pgg_rho (mp_M p)) secretP HG
            (profile_deck sel Hlen) C
       _|_ dealt_secret secretP HG).
Proof.
move=> H; apply: constant_deck_view_dep.
apply: (H constant_deck_profile 3 id erefl pgl27_3transitive
          (fdist_uniform card_bool) pgl27_G_pos [set ord0]).
by rewrite cards1.
Qed.

End pgl27_profile_privacy.

Section pgl27_dealer.
Local Open Scope proba_scope.
Local Open Scope ring_scope.
Variable R : realType.
Local Notation deckT := (8.-tuple 'I_8).
Local Notation shuffleT := (pgg_gT pgl27_M).
Local Notation viewT := ({ffun 'I_8 -> 'I_8}).

(** pgl27_dealer_delta == the deterministic dealer of the exact PGL(2,7) row:
    at each orbit secret it lays the one representative deck orbit_encode s,
    with no randomness of its own.  It is the extreme case of a dealer kernel,
    and the one for which the deck is a function of the secret rather than a
    hidden draw. *)
Definition pgl27_dealer_delta (s : bool) : R.-fdist deckT :=
  fdist1 (orbit_encode s).

(** pgl27_dealer_nu == a uniform element of the PGL(2,7) shuffle group. *)
Definition pgl27_dealer_nu : R.-fdist shuffleT := `U pgl27_G_pos.

(** pgl27_dealerP == the exact row's data placed in the dealer model's sample
    space, an orbit secret paired with a deck and a shuffle. *)
Definition pgl27_dealerP : R.-fdist (bool * (deckT * shuffleT)) :=
  @dealer_shuffleP R bool deckT shuffleT
    (fdist_uniform card_bool) pgl27_dealer_delta pgl27_dealer_nu.

(** pgl27_dealer_embed == the map that restores the deterministic deck to a
    sample of the exact row, which carries only a secret and a shuffle. *)
Definition pgl27_dealer_embed (u : bool * shuffleT) :
    bool * (deckT * shuffleT) :=
  (u.1, (orbit_encode u.1, u.2)).

(** pgl27_dealerPE == the exact row's law pushed along pgl27_dealer_embed is
    the dealer model's law at the deterministic kernel.  Here the modelling
    claim is checked rather than assumed: the row's two-coordinate law and the
    model's three-coordinate law agree once the deck coordinate is filled in by
    the function the row leaves implicit. *)
Lemma pgl27_dealerPE :
  fdistmap pgl27_dealer_embed (pgl27P R) = pgl27_dealerP.
Proof.
apply: fdist_ext => -[s [d g]].
rewrite fdistmapE /pgl27_dealer_embed /pgl27_dealerP dealer_shufflePE.
rewrite /pgl27_dealer_delta /pgl27_dealer_nu /pgl27P fdist1E.
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

(** pgl27_dealer_view C == the card values a coalition C reads off the laid
    deck after the shuffle has acted, and ord0 at every position outside C.
    Written as a function of the dealer model's three coordinates, it reads the
    secret only through the deck. *)
Definition pgl27_dealer_view (C : {set 'I_8})
    (s : bool) (d : deckT) (g : shuffleT) : viewT :=
  [ffun i => if i \in C then
     tnth d (@pgg_rho pgl27_M g i) else ord0].

(** pgl27_dealer_viewE == the dealer model's view, composed with
    pgl27_dealer_embed, is the exact row's view.  One of the two commuting
    equations carrier transport demands. *)
Lemma pgl27_dealer_viewE (C : {set 'I_8}) :
  @dealer_shuffle_view R bool deckT shuffleT viewT
     (fdist_uniform card_bool) pgl27_dealer_delta pgl27_dealer_nu
     (pgl27_dealer_view C) \o pgl27_dealer_embed = pgl27_view R C.
Proof. by []. Qed.

(** pgl27_dealer_secretE == the dealer model's secret, composed with
    pgl27_dealer_embed, is the exact row's orbit secret.  The other commuting
    equation. *)
Lemma pgl27_dealer_secretE :
  @dealer_shuffle_secret R bool deckT shuffleT
      (fdist_uniform card_bool) pgl27_dealer_delta pgl27_dealer_nu
      \o pgl27_dealer_embed =
    pgl27_secret R.
Proof. by []. Qed.

(** pgl27_dealer_mu C Hdt == the law of a uniformly chosen injective placement
    of #|C| of the eight card values on the positions of C.  It is the common
    view law the two secrets must share, and it names no secret, which is the
    whole content of privacy at this coalition size. *)
Definition pgl27_dealer_mu (C : {set 'I_8})
    (Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N) :
    R.-fdist viewT :=
  fdistmap (fun r : (size (enum C)).-tuple 'I_8 =>
      [ffun i : 'I_8 => nth ord0 (val r) (index i (enum C))])
    (`U Hdt).

(** pgl27_alldecks_dealer_view_law == at every deck without repeated cards,
    whatever the secret, the uniform shuffle sends a coalition of at most three
    positions to the common law.  This is 3-transitivity of PGL(2,7), stated at
    an arbitrary valid deck rather than at a representative, which is the form
    dealer_shuffle_view_indep_of_deck takes as its per-deck premise and the
    only place where the group-theoretic content of the instance enters the
    dealer model. *)
Lemma pgl27_alldecks_dealer_view_law (C : {set 'I_8}) (s : bool) (d : deckT)
    (Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N) :
  (#|C| <= 3)%N -> uniq d ->
  fdistmap (fun g => pgl27_dealer_view C s d g)
    ((`U pgl27_G_pos) : R.-fdist shuffleT) = @pgl27_dealer_mu C Hdt.
Proof.
move=> HC Huniq; pose k := size (enum C).
pose p : k.-tuple 'I_8 := in_tuple (enum C).
have Hk : (k <= 3)%N by rewrite /k -cardE.
have Hp : p \in dtuple_on k [set: 'I_8].
  by rewrite inE; apply/andP; split;
     [exact: enum_uniq | apply/subsetP => x _; rewrite inE].
have Hcomp :
    (fun g : shuffleT => pgl27_dealer_view C s d g) =
    (fun r : k.-tuple 'I_8 =>
       [ffun i : 'I_8 => nth ord0 (val r) (index i (enum C))]) \o
    (fun g : shuffleT =>
       [tuple tnth d (@pgg_rho pgl27_M g (tnth p l)) | l < k]).
  apply: boolp.funext => g; apply/ffunP => i.
  rewrite /pgl27_dealer_view /comp !ffunE.
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
rewrite Hcomp -fdistmap_comp /pgl27_dealer_mu.
by rewrite (@ktuple_encode_uniform 7 shuffleT (pgg_G pgl27_M)
  (@pgg_rho pgl27_M) 3 pgl27_3transitive R pgl27_G_pos
  (fun _ : bool => d) k p true Hdt Hk Huniq Hp).
Qed.

(** pgl27_dealer_view_law == the same law at the representative deck of either
    secret, which is the deck the exact row lays.  It is the general per-deck
    law instantiated there, the representative being repetition-free, so the
    counting is done once. *)
Lemma pgl27_dealer_view_law (C : {set 'I_8}) (s : bool)
    (Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N) :
  (#|C| <= 3)%N ->
  fdistmap (fun g => pgl27_dealer_view C s (orbit_encode s) g)
    pgl27_dealer_nu = @pgl27_dealer_mu C Hdt.
Proof.
move=> HC; rewrite /pgl27_dealer_nu.
exact: (@pgl27_alldecks_dealer_view_law C s (orbit_encode s) Hdt HC
  (orbit_encode_deck s)).
Qed.

(** pgl27_dealer_view_indep == in the dealer model's sample space at the
    deterministic kernel, the view of a coalition of at most three positions
    is independent of the orbit secret.  It is dealer_shuffle_view_indep at
    pgl27_dealer_mu; the deterministic kernel makes the mixed-law premise a
    statement about a single deck, which pgl27_dealer_view_law supplies. *)
Lemma pgl27_dealer_view_indep (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  pgl27_dealerP |= @dealer_shuffle_view R bool deckT shuffleT viewT
    (fdist_uniform card_bool) pgl27_dealer_delta pgl27_dealer_nu
    (pgl27_dealer_view C) _|_
    @dealer_shuffle_secret R bool deckT shuffleT
      (fdist_uniform card_bool) pgl27_dealer_delta pgl27_dealer_nu.
Proof.
move=> HC.
have Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N.
  apply/card_gt0P; exists (in_tuple (enum C)).
  by rewrite inE; apply/andP; split;
     [exact: enum_uniq | apply/subsetP => x _; rewrite inE].
apply: (@dealer_shuffle_view_indep R bool deckT shuffleT viewT
  (fdist_uniform card_bool) pgl27_dealer_delta pgl27_dealer_nu
  (pgl27_dealer_view C) (@pgl27_dealer_mu C Hdt)) => s _.
apply: (@fdistmap_prod_const R deckT shuffleT
  (pgl27_dealer_delta s) (fun _ => pgl27_dealer_nu) viewT
  (fun dg => pgl27_dealer_view C s dg.1 dg.2)
  (@pgl27_dealer_mu C Hdt)) => d Hd.
have Hdeq : d = orbit_encode s.
  apply: contraNeq Hd => Hneq.
  by rewrite /pgl27_dealer_delta fdist1E (negbTE Hneq) /=.
subst d.
exact: (@pgl27_dealer_view_law C s Hdt HC).
Qed.

(** pgl27_view_indep_via_dealer == the statement is pgl27_view_indep verbatim;
    only the route differs.  It is the exact row's own privacy statement,
    obtained by transporting the dealer model's independence back along
    pgl27_dealer_embed.  No group theory is redone here: 3-transitivity entered
    at pgl27_dealer_view_law and this step only rewrites the same law in the
    row's two coordinates. *)
Lemma pgl27_view_indep_via_dealer (C : {set 'I_8}) :
  (#|C| <= 3)%N -> pgl27P R |= pgl27_view R C _|_ pgl27_secret R.
Proof.
move=> HC.
have Hgen := @pgl27_dealer_view_indep C HC.
rewrite -pgl27_dealerPE in Hgen.
rewrite -(@pgl27_dealer_viewE C) -pgl27_dealer_secretE.
by apply/inde_RV_fdistmap.
Qed.

(** pgl27_dealer_bad_embed == the embedding with the orbit secret negated in
    the deck coordinate, used only to show that the view equation is not
    automatic. *)
Definition pgl27_dealer_bad_embed (u : bool * shuffleT) :
    bool * (deckT * shuffleT) :=
  (u.1, (orbit_encode (~~ u.1), u.2)).

(* Expected failure: the view equation under a deck laid for the negated
   secret.  The two sides are convertible only if orbit_encode (~~ b) and
   orbit_encode b are, so erefl does not typecheck against the ascribed
   equation. *)
Fail Definition pgl27_dealer_bad_viewE (C : {set 'I_8}) :
  @dealer_shuffle_view R bool deckT shuffleT viewT
     (fdist_uniform card_bool) pgl27_dealer_delta pgl27_dealer_nu
     (pgl27_dealer_view C) \o pgl27_dealer_bad_embed = pgl27_view R C := erefl.

End pgl27_dealer.

Section pgl27_dealer_view_law_mutation.
Local Open Scope proba_scope.
Local Open Scope ring_scope.
Variable R : realType.
Variables (C : {set 'I_8}) (s : bool) (d : 8.-tuple 'I_8).
Variable Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N.
Hypothesis HC : (#|C| <= 3)%N.
Hypothesis Huniq : uniq d.

(** pgl27_alldecks_dealer_view_law_with_validity == the positive control for
    the mutation below: with the repetition-free premise supplied, the same
    spelling is the per-deck view law. *)
Definition pgl27_alldecks_dealer_view_law_with_validity :
  fdistmap (fun g => pgl27_dealer_view C s d g)
    ((`U pgl27_G_pos) : R.-fdist (pgg_gT pgl27_M)) = @pgl27_dealer_mu R C Hdt
  := @pgl27_alldecks_dealer_view_law R C s d Hdt HC Huniq.

(* the premises are declared coalition size first and validity last, so that
   dropping validity leaves an arrow rather than shifting an argument *)
(* Expected failure: the per-deck view law with the validity premise dropped.
   The two premises are declared coalition size first and validity last, so
   omitting the last argument leaves `uniq d ->` as an arrow in the term's
   type, and what is ascribed a bare equality of laws is a function into
   one. *)
Fail Definition pgl27_alldecks_dealer_view_law_without_validity :
  fdistmap (fun g => pgl27_dealer_view C s d g)
    ((`U pgl27_G_pos) : R.-fdist (pgg_gT pgl27_M)) = @pgl27_dealer_mu R C Hdt
  := @pgl27_alldecks_dealer_view_law R C s d Hdt HC.

End pgl27_dealer_view_law_mutation.

Section pgl27_alldecks_dealer.
Local Open Scope proba_scope.
Local Open Scope ring_scope.
Variable R : realType.
Local Notation deckT := (8.-tuple 'I_8).
Local Notation shuffleT := (pgg_gT pgl27_M).
Local Notation viewT := ({ffun 'I_8 -> 'I_8}).

(** pgl27_alldecks_dealer_delta == the all-decks dealer: at each orbit secret
    it lays a uniform deck of that secret's class.  Unlike pgl27_dealer_delta it
    hides a genuine draw, and the privacy argument must survive every deck the
    draw can produce. *)
Definition pgl27_alldecks_dealer_delta (s : bool) : R.-fdist deckT :=
  `U (pgl27_class_decks_pos s).

(** pgl27_alldecks_dealerP == the all-decks row's data in the dealer model's
    sample space. *)
Definition pgl27_alldecks_dealerP : R.-fdist (bool * (deckT * shuffleT)) :=
  @dealer_shuffleP R bool deckT shuffleT (fdist_uniform card_bool)
    pgl27_alldecks_dealer_delta (`U pgl27_G_pos).

(** pgl27_alldecks_dealerPE == that law is the all-decks law of the
    reconstruction layer, with no map between them: the two definitions are the
    same three-coordinate kernel product written in two vocabularies. *)
Lemma pgl27_alldecks_dealerPE :
  pgl27_alldecks_dealerP =
  alldecksP (fdist_uniform card_bool) pgl27_G_pos
    (R := R) pgl27_class_decks_pos.
Proof. by []. Qed.

(** pgl27_alldecks_dealer_viewE == and the dealer model's view at
    pgl27_dealer_view is the all-decks view of the reconstruction layer. *)
Lemma pgl27_alldecks_dealer_viewE (C : {set 'I_8}) :
  @dealer_shuffle_view R bool deckT shuffleT viewT
    (fdist_uniform card_bool) pgl27_alldecks_dealer_delta (`U pgl27_G_pos)
    (pgl27_dealer_view C) =
  alldecks_view (@pgg_rho pgl27_M) (fdist_uniform card_bool)
    pgl27_G_pos pgl27_class_decks_pos C.
Proof. by []. Qed.

(** pgl27_alldecks_dealer_secretE == the dealer model's secret is the all-decks
    secret of the reconstruction layer.  Carrier transport asks for a named
    equation on each reader, and this is the second one. *)
Lemma pgl27_alldecks_dealer_secretE :
  @dealer_shuffle_secret R bool deckT shuffleT
    (fdist_uniform card_bool) pgl27_alldecks_dealer_delta (`U pgl27_G_pos) =
  alldecks_secret (fdist_uniform card_bool) pgl27_G_pos
    pgl27_class_decks_pos.
Proof. by []. Qed.

(** pgl27_view_indep_alldecks_via_dealer == the statement is
    pgl27_view_indep_alldecks verbatim; only the route differs.  Under the
    all-decks dealer the view of a coalition of at most three positions is
    independent of the orbit secret.  It is dealer_shuffle_view_indep_of_deck
    with validity taken to be a deck without repeated cards: every deck of a
    class has that property, and every deck with it has the same view law, so
    the average over decks is not needed and the conclusion holds deck by
    deck. *)
Lemma pgl27_view_indep_alldecks_via_dealer (C : {set 'I_8}) :
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
    pgl27_alldecks_dealer_delta s d != 0 -> uniq d.
  move=> s d Hd.
  have Hmem : d \in class_decks orbit_class deck_ok s.
    apply: contraNT Hd => Hnot.
    by rewrite /pgl27_alldecks_dealer_delta
      (fdist_uniform_supp_notin R (pgl27_class_decks_pos s) Hnot) eqxx.
  by move: Hmem; rewrite inE => /andP[Hok _]; exact: Hok.
have Hlaw : forall (s : bool) (d : deckT),
    (fdist_uniform card_bool : R.-fdist bool) s != 0 -> uniq d ->
    fdistmap (pgl27_dealer_view C s d)
      ((`U pgl27_G_pos) : R.-fdist shuffleT) = @pgl27_dealer_mu R C Hdt.
  by move=> s d _ Hu;
     exact: (@pgl27_alldecks_dealer_view_law R C s d Hdt HC Hu).
have Hgen := @dealer_shuffle_view_indep_of_deck R bool deckT shuffleT viewT
  (fdist_uniform card_bool) pgl27_alldecks_dealer_delta
  ((`U pgl27_G_pos) : R.-fdist shuffleT)
  (fun _ d => uniq d) (pgl27_dealer_view C) (@pgl27_dealer_mu R C Hdt)
  Hvalid Hlaw.
rewrite -pgl27_alldecks_dealerPE -(@pgl27_alldecks_dealer_viewE C).
rewrite -pgl27_alldecks_dealer_secretE.
exact: Hgen.
Qed.

End pgl27_alldecks_dealer.
