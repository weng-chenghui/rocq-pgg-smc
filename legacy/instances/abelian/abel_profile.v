(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* abel_profile: the abelian (insecure) plug of the shared program            *)
(*                                                                            *)
(* The plug uses a sum-mod scheme on the 4 abelian card positions with the     *)
(* identity content readout, the abelian monodromy pgg_rho, and a              *)
(* reconstruction invariance that holds for any group acting by permutations.  *)
(* The differentiator from the secure plugs is the GROUP (commuting            *)
(* generators), not the scheme.                                                *)
(*                                                                            *)
(* The protocol interface of the profile is abel_PI, the four-seat interface   *)
(* whose starting layout is the four card positions in canonical order. Its    *)
(* seat count pi_T' = 3 is the share count ts_T' abel_ts of the sum-mod scheme *)
(* the plug carries, so an ExecutionPlug over this profile has its seat/share  *)
(* bridge at erefl. The two-generator value Gen_PGG_2 abel_sigmas keeps its    *)
(* group-level role of naming the two generators and is not the mp_PI of any   *)
(* protocol profile: its pi_T' is 1, so the bridge 1 = 3 has no proof.         *)
(*                                                                            *)
(* The file also carries the concrete description of the generated group: the  *)
(* two generators are disjoint transpositions, so they are commuting           *)
(* involutions and the group they generate is the Klein four-group             *)
(* {1, s1, s2, s1 s2}, of order four and abelian.                              *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   abel_ts             == the sum-mod scheme on the four card positions      *)
(*   abel_plug           == the abelian reconstruction plug                    *)
(*   abel_PI             == the four-seat abelian protocol interface           *)
(*   abel_profile        == the abelian MonodromyProfile                       *)
(*   abel_G4             == the set {1, s1, s2, s1 s2} of permutations         *)
(*                                                                            *)
(* Key results:                                                               *)
(*   profile_k_abel      == the plug's privacy threshold is four               *)
(*   abel_gens_commute   == the two generators commute                         *)
(*   abel_G4_group_set   == abel_G4 is a subgroup                              *)
(*   abel_pgg_GE         == the generated group is abel_G4                     *)
(*   abel_G4_card        == abel_G4 has four elements                          *)
(*   abel_pgg_G_card     == the generated group has four elements              *)
(*   abel_G_abelian      == the generated group is abelian                     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_abelian.
From pgg_smc Require Import card_exchange_pismc pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import rigidity_abelian_instance.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* abel_M — the abelian two-generator monodromy template at N = 4, the
   Gen_PGGTypes form abel_ts, abel_plug and abel_profile are built over. *)
Local Notation abel_M := (@Gen_PGGTypes 1 2 abel_sigmas).

(** abel_ts — the sum-mod threshold scheme on the four abelian card
    positions: four shares over 'I_4, reconstructed as their sum modulo four,
    so every share is needed and the privacy threshold is four.  The share
    indices are the card positions themselves, which is what lets a shuffle of
    the deck act on the shares at all.  The scheme is the one the secure
    instances also carry; what makes this instance the negative example is the
    group, not the sharing. *)
Definition abel_ts : ThresholdScheme 'I_4 'I_4 := @sum_mod_scheme 2 3.

(** abel_sum_mod_perm_compatible — reconstruction survives a shuffle: for
    every g in the group, permuting the shares by pgg_rho g and then summing
    modulo four returns what summing returned before.  A sum over all indices
    does not see the order of its terms, so the fact holds for any group
    acting by permutations and is not special to this one.  It is the
    obligation the plug below has to discharge for its endpoints to decode
    after the deck has been shuffled. *)
Lemma abel_sum_mod_perm_compatible :
  @ts_recon_perm_invariant _ (pgg_G (@Gen_PGGTypes 1 2 abel_sigmas)) _ _ abel_ts
    (@pgg_rho (@Gen_PGGTypes 1 2 abel_sigmas)).
Proof.
move=> g s shares Hg Hvalid.
apply: sum_mod_scheme_correct.
rewrite /sum_mod_valid_pred in Hvalid *.
rewrite -Hvalid; congr (_ %% _).
under eq_bigr do rewrite tnth_mktuple.
symmetry.
rewrite (reindex_inj (@perm_inj _ (@pgg_rho (@Gen_PGGTypes 1 2 abel_sigmas) g))).
by apply: eq_bigr.
Qed.

(** abel_plug — the reconstruction layer of the abelian instance: the sum-mod
    scheme, the identity readout of card content, the abelian monodromy, and
    the invariance above.  Identity readout means an endpoint records the card
    position itself rather than anything dealt onto it, so an observation of
    this plug depends on the shuffle and on nothing else. *)
Definition abel_plug : ReconPlug (@Gen_PGGTypes 1 2 abel_sigmas) 'I_4 :=
  @MkReconPlug (@Gen_PGGTypes 1 2 abel_sigmas) 'I_4 abel_ts id
    (@pgg_rho (@Gen_PGGTypes 1 2 abel_sigmas)) abel_sum_mod_perm_compatible.

(** abel_starts_uniq — the four starting card positions are pairwise
    distinct, so no two seats begin at the same card. *)
Lemma abel_starts_uniq : uniq (ord_tuple 4).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.

(** abel_PI — the seating of the abelian instance: four seats starting at
    card positions 0, 1, 2 and 3 in that order.  Four seats against the four
    shares of abel_ts, so an execution over this profile carries one share per
    seat with no reindexing. *)
Definition abel_PI : PGGInterface abel_M :=
  @MkPGGI abel_M 3 (ord_tuple 4) abel_starts_uniq.

(** abel_profile — the abelian instance as a program profile: the Klein
    four-group acting on four card positions, secrets in 'I_4, the four-seat
    interface and the sum-mod plug.  Its generators commute, and that is the
    property the whole negative analysis of this instance rests on.  The
    interface here is abel_PI and not the two-generator value
    Gen_PGG_2 abel_sigmas, which seats one player and so cannot be paired with
    a four-share scheme. *)
Definition abel_profile : MonodromyProfile :=
  @MkMonodromyProfile abel_M 'I_4 abel_PI abel_plug.

(** profile_k_abel — the profile's privacy threshold is four: sum-mod deals
    one share per card position and reconstruction consumes all of them, so
    no proper subset of the seats learns anything.  It is the sharing-layer
    number that distinguishes this instance from the S_5 plug's five, the
    groups differing separately. *)
Lemma profile_k_abel : profile_k abel_profile = 4.
Proof. by []. Qed.

(** abel_gens_commute — the two generators commute, being transpositions of
    disjoint pairs of card positions.  This is the structural root of the
    instance's negative character: commuting shuffles generate only four
    permutations, and the word distribution over them keeps a fixed distance
    from uniform that no number of rounds reduces.  The secure instances are
    exactly the ones where this fails. *)
Lemma abel_gens_commute : commute abel_s1 abel_s2.
Proof.
apply/permP => x; rewrite !permM /abel_s1 /abel_s2.
by case: x => -[|[|[|[|x]]]] Hx; rewrite ?permE.
Qed.

(******************************************************************************)
(*     The Klein four-group generated by the two disjoint transpositions      *)
(******************************************************************************)

(** abel_G4 — the four permutations 1, s1, s2 and s1 s2, spelled out as a
    set.  It is the Klein four-group, and it is the support the abelian
    shuffle models are read against: the ideal distribution of this instance
    is uniform on exactly these four and not on all of S_4, so the distance
    measured downstream is a failure to mix inside the reachable group and not
    the fact that the group is small. *)
Definition abel_G4 : {set {perm 'I_4}} :=
  [set 1%g; abel_s1; abel_s2; (abel_s1 * abel_s2)%g].

(* The eight identities below are the multiplication table of the Klein
   four-group, written out one product at a time.  Two commuting involutions
   generate a group of order four and no more, and these are the equations
   that say so. *)

(** abel_s1K — the first generator is an involution. *)
Lemma abel_s1K : (abel_s1 * abel_s1 = 1)%g.
Proof. exact: tperm2. Qed.

(** abel_s2K — the second generator is an involution. *)
Lemma abel_s2K : (abel_s2 * abel_s2 = 1)%g.
Proof. exact: tperm2. Qed.

(** abel_s21 — the product of the two generators is the same in either
    order. *)
Lemma abel_s21 : (abel_s2 * abel_s1)%g = (abel_s1 * abel_s2)%g.
Proof. exact: esym abel_gens_commute. Qed.

(** abel_s1_s1s2 — s1 absorbs the first factor of the product, leaving
    s2. *)
Lemma abel_s1_s1s2 : (abel_s1 * (abel_s1 * abel_s2))%g = abel_s2.
Proof. by rewrite mulgA abel_s1K mul1g. Qed.

(** abel_s2_s1s2 — s2 absorbs the second factor of the product, leaving
    s1. *)
Lemma abel_s2_s1s2 : (abel_s2 * (abel_s1 * abel_s2))%g = abel_s1.
Proof. by rewrite mulgA abel_s21 -mulgA abel_s2K mulg1. Qed.

(** abel_s1s2_s1 — the product followed by s1 is s2. *)
Lemma abel_s1s2_s1 : (abel_s1 * abel_s2 * abel_s1)%g = abel_s2.
Proof. by rewrite -mulgA abel_s21 mulgA abel_s1K mul1g. Qed.

(** abel_s1s2_s2 — the product followed by s2 is s1. *)
Lemma abel_s1s2_s2 : (abel_s1 * abel_s2 * abel_s2)%g = abel_s1.
Proof. by rewrite -mulgA abel_s2K mulg1. Qed.

(** abel_s1s2K — the product of the two generators is itself an involution,
    so every element of the group has order dividing two. *)
Lemma abel_s1s2K : (abel_s1 * abel_s2 * (abel_s1 * abel_s2))%g = 1%g.
Proof. by rewrite mulgA abel_s1s2_s1 abel_s2K. Qed.

(** abel_G4_group_set — the four listed permutations contain the identity and
    are closed under composition, so they form a subgroup of the permutations
    of the four card positions.  This is the step from a set someone wrote
    down to a group the fingroup theory applies to. *)
Lemma abel_G4_group_set : group_set abel_G4.
Proof.
apply/group_setP; split; first by rewrite !inE eqxx.
move=> x y; rewrite !inE.
move=> /orP[/orP[/orP[/eqP->|/eqP->]|/eqP->]|/eqP->]
       /orP[/orP[/orP[/eqP->|/eqP->]|/eqP->]|/eqP->];
  rewrite ?mul1g ?mulg1 ?abel_s1K ?abel_s2K ?abel_s21 ?abel_s1_s1s2
          ?abel_s2_s1s2 ?abel_s1s2_s1 ?abel_s1s2_s2 ?abel_s1s2K
          ?eqxx ?orbT //=.
Qed.

(* abel_G4_group registers abel_G4 as a group, so that the group-theoretic
   notation of fingroup applies to the set spelled out above. *)
Canonical abel_G4_group := group abel_G4_group_set.

(** abel_gen_setE — the image of the generator tuple is the two-element set
    {s1, s2}: the tuple names two permutations and no more. *)
Lemma abel_gen_setE :
  [set tnth abel_sigmas i | i : 'I_2] = [set abel_s1; abel_s2].
Proof.
apply/setP => g; rewrite !inE; apply/imsetP/orP.
  case=> i _ ->; move: i => [[|[|i]] Hi] //=;
    rewrite (tnth_nth abel_s1) /=; [by left | by right].
case=> /eqP ->;
  [exists (Ordinal (isT : (0 < 2)%N)) | exists (Ordinal (isT : (1 < 2)%N))];
  by rewrite // (tnth_nth abel_s1).
Qed.

(** abel_pgg_GE — the group the instance generates is exactly {1, s1, s2,
    s1 s2}.  It replaces an abstractly generated subgroup by a listed set, so
    every count and every distribution over the group below is finite
    arithmetic on four named permutations. *)
Lemma abel_pgg_GE : (pgg_G abel_M : {set {perm 'I_4}}) = abel_G4.
Proof.
have -> : (pgg_G abel_M : {set {perm 'I_4}})
        = <<[set tnth abel_sigmas i | i : 'I_2]>>%g by [].
rewrite abel_gen_setE; apply/eqP; rewrite eqEsubset; apply/andP; split.
  rewrite gen_subG; apply/subsetP => g.
  by rewrite !inE => /orP[/eqP->|/eqP->]; rewrite eqxx ?orbT.
apply/subsetP => g; rewrite !inE.
move=> /orP[/orP[/orP[/eqP->|/eqP->]|/eqP->]|/eqP->].
- exact: group1.
- by apply: mem_gen; rewrite !inE eqxx.
- by apply: mem_gen; rewrite !inE eqxx orbT.
- by apply: groupM; apply: mem_gen; rewrite !inE eqxx ?orbT.
Qed.

(* The two probes below separate the four group elements: reading a
   permutation at card position 0 tells s1 and s1 s2 from the identity, and
   reading it at position 2 tells s2 and s1 s2 from the identity. *)

(** abel_perm_eq0 — equal permutations agree at card position 0. *)
Lemma abel_perm_eq0 (g h : {perm 'I_4}) : g = h ->
  val (g (Ordinal (isT : (0 < 4)%N))) = val (h (Ordinal (isT : (0 < 4)%N))).
Proof. by move=> ->. Qed.

(** abel_perm_eq2 — equal permutations agree at card position 2. *)
Lemma abel_perm_eq2 (g h : {perm 'I_4}) : g = h ->
  val (g (Ordinal (isT : (2 < 4)%N))) = val (h (Ordinal (isT : (2 < 4)%N))).
Proof. by move=> ->. Qed.

(** abel_1_neq_s1 — the identity differs from the first generator. *)
Lemma abel_1_neq_s1 : (1%g == abel_s1) = false.
Proof.
by apply/negbTE/eqP => /abel_perm_eq0; rewrite perm1 /abel_s1 !permE.
Qed.

(** abel_1_neq_s2 — the identity differs from the second generator. *)
Lemma abel_1_neq_s2 : (1%g == abel_s2) = false.
Proof.
by apply/negbTE/eqP => /abel_perm_eq2; rewrite perm1 /abel_s2 !permE.
Qed.

(** abel_1_neq_s1s2 — the identity differs from the generator product. *)
Lemma abel_1_neq_s1s2 : (1%g == (abel_s1 * abel_s2)%g) = false.
Proof.
by apply/negbTE/eqP => /abel_perm_eq0;
   rewrite perm1 permM /abel_s1 /abel_s2 !permE.
Qed.

(** abel_s1_neq_s2E — the two generators differ. *)
Lemma abel_s1_neq_s2E : (abel_s1 == abel_s2) = false.
Proof.
by apply/negbTE/eqP => /abel_perm_eq0; rewrite /abel_s1 /abel_s2 !permE.
Qed.

(** abel_s1_neq_s1s2 — the first generator differs from the product. *)
Lemma abel_s1_neq_s1s2 : (abel_s1 == (abel_s1 * abel_s2)%g) = false.
Proof.
by apply/negbTE/eqP => /abel_perm_eq2; rewrite permM /abel_s1 /abel_s2 !permE.
Qed.

(** abel_s2_neq_s1s2 — the second generator differs from the product. *)
Lemma abel_s2_neq_s1s2 : (abel_s2 == (abel_s1 * abel_s2)%g) = false.
Proof.
by apply/negbTE/eqP => /abel_perm_eq0; rewrite permM /abel_s1 /abel_s2 !permE.
Qed.

(** abel_G4_card — the group has four elements, the six inequations above
    showing the listed permutations pairwise distinct.  This four is the
    normalising constant of the ideal uniform model, so every mass in the
    abelian distance computations is a quarter or a multiple of one. *)
Lemma abel_G4_card : #|abel_G4| = 4.
Proof.
rewrite /abel_G4 -!setUA !cardsU1 !inE cards1.
by rewrite abel_1_neq_s1 abel_1_neq_s2 abel_1_neq_s1s2 abel_s1_neq_s2E
           abel_s1_neq_s1s2 abel_s2_neq_s1s2.
Qed.

(** abel_G4_card_gt0 — the group is nonempty, which is what a uniform
    distribution supported on it needs in order to exist. *)
Lemma abel_G4_card_gt0 : (0 < #|abel_G4|)%N.
Proof. by rewrite abel_G4_card. Qed.

(** abel_pgg_G_card — the monodromy group has four elements.  It is the
    ceiling on the search space at every word length, so no number of rounds
    puts an adversary in front of more than four candidate shuffles. *)
Lemma abel_pgg_G_card : #|pgg_G abel_M| = 4.
Proof. by rewrite abel_pgg_GE abel_G4_card. Qed.

(** abel_G_abelian — the generated group is abelian.  It is the hypothesis
    the word-collapse theorems are stated under, so from here a word over the
    two generators is determined by how often each letter occurs and the
    search space collapses to a count of frequency vectors. *)
Lemma abel_G_abelian : abelian (pgg_G abel_M).
Proof.
have -> : (pgg_G abel_M : {set {perm 'I_4}})
        = <<[set tnth abel_sigmas i | i : 'I_2]>>%g by [].
rewrite abel_gen_setE abelian_gen.
apply/subsetP => x; rewrite !inE => /orP[/eqP->|/eqP->];
  apply/centP => y; rewrite !inE => /orP[/eqP->|/eqP->] //;
  [exact: abel_gens_commute | exact: esym abel_gens_commute].
Qed.
