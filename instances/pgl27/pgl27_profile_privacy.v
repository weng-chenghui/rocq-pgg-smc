(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_profile_privacy: the eight-card scheme as a monodromy profile        *)
(*                                                                            *)
(* The record-level privacy theorem profile_view_indep                        *)
(* (reconstruct/transitivity_privacy.v) quantifies over an arbitrary          *)
(* MonodromyProfile and carries two mathematical premises about its           *)
(* projections: the image of the action is t-transitive on the sheets, and    *)
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
(* a trivial group on the eight sheets; the PGL(2,7) action image has more    *)
(* than one element.                                                          *)
(*                                                                            *)
(* Necessity. Both refutations are proved here because their witnesses are    *)
(* PGL(2,7) data: the four heart seats of pgl27_view_dep_k4 for the           *)
(* coalition bound, and constant_deck_profile, a monodromy profile over the   *)
(* same group whose encoder repeats one card, for the distinct-deck premise.  *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   constant_deck_encode == the encoder dealing one repeated card            *)
(*   constant_deck_recon  == the secret read off the card at position zero    *)
(*   constant_deck_scheme == the ThresholdScheme built from those two         *)
(*   constant_deck_monodromy == its trivial share-permutation map             *)
(*   constant_deck_plug      == the ReconPlug carrying that scheme            *)
(*   constant_deck_profile   == the MonodromyProfile dealing a constant deck  *)
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

(** dtuple3_ord8_gt1 == the eight sheets carry more than one three-tuple of
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
    symmetric group on the eight sheets has more than one element. The
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
