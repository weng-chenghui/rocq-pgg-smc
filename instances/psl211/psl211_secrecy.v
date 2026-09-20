(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_secrecy: colour-view privacy of the twelve-card chirality scheme    *)
(*                                                                            *)
(* A coalition of card positions sees only the colours of the cards dealt to  *)
(* it, hearts against clubs, and never a card identity. The secret is the     *)
(* chirality bit: which of the two Steiner systems S(5,6,12) of               *)
(* psl211_blocks.v the heart positions form a block of. Privacy here is       *)
(* distributional. For a uniformly drawn PSL(2,11) shuffle and any prior on   *)
(* the secret, a coalition of at most five positions has a colour view whose  *)
(* law does not depend on the dealt chirality. At six positions, and at any   *)
(* prior giving mass to both chiralities, the law already depends on it.      *)
(*                                                                            *)
(* The two conditional laws are equal, not close. Nothing in the file is      *)
(* conditional on a computational assumption, and the only inputs are the     *)
(* block census and the uniformity of the shuffle.                            *)
(*                                                                            *)
(* The counting premise of the framework bridge design_privacy.v is met here  *)
(* by a census of blocks, not by transitivity of the shuffle group.           *)
(* PSL(2,11) is only 2-transitive on the twelve positions, so the bridge of   *)
(* transitivity_privacy.v reaches two positions, while the 5-design property  *)
(* of the two block systems reaches five.                                     *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211P               == the joint law of the chirality prior and a      *)
(*                            uniform shuffle                                 *)
(*   psl211_secret         == the dealt chirality bit of a sample             *)
(*   psl211_colour_view C  == the colours a coalition C sees                  *)
(*   psl211_leak_coalition == the six positions of the mirror representative  *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_colour_fiber_cardE == the two chiralities have equally many       *)
(*     shuffles showing each view value, at every coalition of at most five   *)
(*   psl211_colour_view_indep  == colour-view independence at five positions  *)
(*   psl211_leak_coalition_card6 == the leak coalition has six positions      *)
(*   psl211_colour_view_dep_k6 == at a prior giving mass to both chiralities, *)
(*     a six-position coalition's colour view depends on the chirality        *)
(*                                                                            *)
(* The coalition observes colours only. The all-decks code view, in which     *)
(* the dealt deck is redrawn uniformly over the valid decks of its class and  *)
(* the coalition reads card identities, is not proved here.                   *)
(*                                                                            *)
(* The fiber count runs through the set action 'P^* of the shuffle group on   *)
(* the six-subsets of positions. The shuffles carrying the representative     *)
(* block onto a block with a prescribed trace on the coalition split into     *)
(* right cosets of the block stabiliser, one coset per block of the system    *)
(* with that trace. The stabiliser has order 660 / 132 = 5, so a fiber        *)
(* cardinality is five times a block count, and the two block counts agree    *)
(* at every coalition of at most five positions by the table certificate      *)
(* psl211_count_okT.                                                          *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import transitivity_privacy design_privacy.
From pgg_smc Require Import psl211_blocks psl211_group psl211_closure.
From pgg_smc Require Import psl211_orbit.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
(* group_scope carries the centraliser notation 'C_G[x | to] of stab_cardE and
   fiber_partitionE; ring_scope is opened after it so that the real-valued
   statements of the leak lemma keep their usual reading.  Nat-valued
   cardinality statements therefore carry %N, since an unannotated numeral or
   product there would read in the semiring instead. *)
Local Open Scope group_scope.
Local Open Scope ring_scope.

(* -------------------------------------------------------------------------- *)
(* The block dealt by each chirality, and the fiber of the set action.        *)
(* -------------------------------------------------------------------------- *)

(* The heart positions of the encoded deck of chirality b, as a block. *)
Local Definition heart_block (b : bool) : {set 'I_12} :=
  psl211_heart_set (psl211_orbit_encode b).

(* The positions of C at which the view value v reads a heart. *)
Local Definition pattern_of (C : {set 'I_12}) (v : {ffun 'I_12 -> bool}) :
  {set 'I_12} := [set i in C | v i].

(* Each representative block has the whole system of its chirality as its
   orbit, so a count over the orbit is a count over the table. *)
Local Lemma orbit_blocksE (b : bool) :
  orbit 'P^* (pgg_G psl211_M) (heart_block b)
  = if b then psl211_mirror_blocks else psl211_hexad_blocks.
Proof.
rewrite /heart_block psl211_encode_heart_setE.
by case: b; [exact: psl211_mirror_orbitE | exact: psl211_hexad_orbitE].
Qed.

(* Position i of the deck re-dealt along g holds a heart exactly when i lies
   in the inverse image of the chirality's block: the colour a coalition
   reads at i is membership in a moved block. *)
Local Lemma colour_heartE (b : bool) (g : pgg_gT psl211_M) (i : 'I_12) :
  psl211_is_heart (tnth (psl211_orbit_encode b) (@pgg_rho psl211_M g i))
  = (i \in (g^-1)%g @: heart_block b).
Proof. by rewrite /heart_block -psl211_heart_set_act inE tnth_mktuple. Qed.

(* The elements of G carrying x to a point y of its orbit form one right
   coset of the stabiliser of x, so the fiber of the action map over y has
   the order of that stabiliser.  Stated at a total action, so that it
   instantiates at the set action 'P^* the block count runs through. *)
(* No psl211 content: a mathcomp-only home for it would be a lib file in the
   style of lib/perm_exchange.v. *)
Local Lemma card_amove (gT : finGroupType) (rT : finType)
    (to : {action gT &-> rT}) (G : {group gT}) (x y : rT) :
  y \in orbit to G x ->
  #|[set g in G | to x g == y]| = #|'C_G[x | to]|.
Proof.
case/orbitP => g0 g0G <-.
have -> : [set g in G | to x g == to x g0] = amove to G x (to x g0) by [].
by rewrite amove_act ?subsetT // card_rcoset.
Qed.

(* Inversion is a bijection of the group, so reading the block through g^-1
   and reading it through g give the same count. *)
Local Lemma fiber_inv_cardE (C A : {set 'I_12}) (b : bool) :
  #|[set g in pgg_G psl211_M | ((g^-1)%g @: heart_block b) :&: C == A]|
  = #|[set g in pgg_G psl211_M | (g @: heart_block b) :&: C == A]|.
Proof.
have -> : [set g in pgg_G psl211_M | ((g^-1)%g @: heart_block b) :&: C == A]
  = [set (g^-1)%g
    | g in [set g in pgg_G psl211_M | (g @: heart_block b) :&: C == A]].
  apply/setP => g; rewrite inE; apply/idP/imsetP => [/andP[gG Hg]|[h]].
    by exists (g^-1)%g; [rewrite inE groupV gG | rewrite invgK].
  by rewrite inE => /andP[hG Hh] ->; rewrite groupV hG /= invgK.
by rewrite card_imset //; exact: invg_inj.
Qed.

(* The shuffles moving the block to a set with trace A on C partition into
   the fibers of the action map over the blocks with that trace, and every
   such fiber is a coset of the stabiliser. *)
Local Lemma fiber_partitionE (C A : {set 'I_12}) (b : bool) :
  #|[set g in pgg_G psl211_M | (g @: heart_block b) :&: C == A]|
  = (#|[set B in orbit 'P^* (pgg_G psl211_M) (heart_block b) | B :&: C == A]|
     * #|'C_(pgg_G psl211_M)[heart_block b | 'P^*]|)%N.
Proof.
set G := pgg_G psl211_M; set Hb := heart_block b.
set s := #|'C_G[Hb | 'P^*]|.
rewrite -[LHS]sum1dep_card.
rewrite [LHS](partition_big (fun g : pgg_gT psl211_M => [set g x | x in Hb])
  (fun B => (B \in orbit 'P^* G Hb) && (B :&: C == A))); last first.
  by move=> g /andP[gG Hg]; rewrite Hg andbT; exact: mem_orbit.
rewrite (eq_bigr (fun _ => s)); last first.
  move=> j /andP[Hj HjA].
  rewrite (eq_bigl (fun i => (i \in G) && ([set i x | x in Hb] == j)));
    last first.
    move=> i; case Hij: ([set i x | x in Hb] == j); last by rewrite !andbF.
    by rewrite (eqP Hij) HjA !andbT.
  by rewrite sum1dep_card; exact: (card_amove Hj).
by rewrite big_const iter_addn_0 mulnC; congr (_ * _);
   apply: eq_card => B; rewrite inE.
Qed.

(* Orbit-stabiliser at 660 group elements and 132 blocks. *)
Local Lemma stab_cardE (b : bool) :
  (#|'C_(pgg_G psl211_M)[heart_block b | 'P^*]| = 5)%N.
Proof.
have Horb : (#|orbit 'P^* (pgg_G psl211_M) (heart_block b)| = 132)%N.
  rewrite orbit_blocksE; case: b;
    [exact: psl211_card_mirror_blocks | exact: psl211_card_hexad_blocks].
have Hos := card_orbit_stab 'P^* (pgg_G psl211_M) (heart_block b).
rewrite Horb psl211_card in Hos.
by apply/eqP; rewrite -(eqn_pmul2l (isT : (0 < 132)%N)) Hos.
Qed.

(* -------------------------------------------------------------------------- *)
(* Reading the block-count certificate at a coalition of positions.           *)
(* -------------------------------------------------------------------------- *)

(* The certificate read on position sets: at most five positions cannot tell
   the two systems apart by an intersection pattern.  The nonempty half is
   psl211_orbit.v's psl211_pattern_transfer; the empty coalition is a
   separate branch, at 132 = 132, because psl211_count_ok certifies the sizes
   one to five only. *)
Local Lemma pattern_transferE (C A : {set 'I_12}) :
  (#|C| <= 5)%N -> A \subset C ->
  #|[set B in psl211_mirror_blocks | B :&: C == A]|
  = #|[set B in psl211_hexad_blocks | B :&: C == A]|.
Proof.
move=> HC HAC; case: (posnP #|C|) => [/cards0_eq HC0|HC0].
  have HA : A = set0 by apply/eqP; rewrite -subset0 -HC0.
  have Hall (F : {set {set 'I_12}}) : [set B in F | B :&: set0 == set0] = F.
    by apply/setP => B; rewrite !inE setI0 eqxx andbT.
  rewrite HC0 HA !Hall.
  by rewrite psl211_card_mirror_blocks psl211_card_hexad_blocks.
exact: psl211_pattern_transfer C A HC0 HC HAC.
Qed.

(* -------------------------------------------------------------------------- *)
(* The leak coalition, the sample space, the colour observer and the privacy  *)
(* statements.  Everything above this line is combinatorics of the two block  *)
(* systems and carries no distribution, so it is stated outside the section   *)
(* rather than under its realType and prior variables, which would otherwise  *)
(* put the boolp axioms of an fdist on statements that do not need them.      *)
(* -------------------------------------------------------------------------- *)

(** psl211_leak_coalition — the six positions holding a heart in the mirror
    encoding, the representative row [2;3;5;7;8;9]. A coalition of the
    smallest size at which the two block systems can be told apart. *)
Definition psl211_leak_coalition : {set 'I_12} :=
  psl211_heart_set (psl211_orbit_encode true).

(** psl211_leak_coalition_card6 — the leak coalition holds six positions, one
    more than the privacy threshold. Unconditional on the prior, so a reader
    at a degenerate prior still has the coalition's size. *)
Lemma psl211_leak_coalition_card6 : (#|psl211_leak_coalition| = 6)%N.
Proof.
rewrite /psl211_leak_coalition psl211_encode_heart_setE.
by apply: psl211_block_card6; vm_compute.
Qed.

Section secrecy.
Variables (R : realType) (secretP : R.-fdist bool).

(** psl211P — the joint law of the chirality prior and a uniform PSL(2,11)
    shuffle, the two drawn independently. The sample space in which every
    privacy statement of this file is read. *)
Definition psl211P := secretP `x (`U psl211_G_pos).

(** psl211_secret — the dealt chirality bit of a sample. The one bit the
    coalition must not learn before the reveal. *)
Definition psl211_secret : {RV psl211P -> bool} :=
  @dealt_secret _ (pgg_G psl211_M) R secretP psl211_G_pos.

(** psl211_colour_view C — the colour, heart or club, of the card dealt to
    each position of C, and false at every position outside C. The whole
    observation of a coalition holding cards of two indistinguishable
    colours: it records the colour pattern on C and no card identity. *)
Definition psl211_colour_view (C : {set 'I_12}) :
    {RV psl211P -> {ffun 'I_12 -> bool}} :=
  @colour_view 11 _ (pgg_G psl211_M) (@pgg_rho psl211_M) R secretP psl211_G_pos
    psl211_orbit_encode psl211_is_heart C.

(* A view value that vanishes off C is shown by exactly the shuffles whose
   moved block meets C in the value's heart pattern, so a count of shuffles
   becomes a count of blocks. *)
Local Lemma view_fiberE (C : {set 'I_12}) (b : bool)
    (v : {ffun 'I_12 -> bool}) :
  (forall i, i \notin C -> v i = false) ->
  [set g in pgg_G psl211_M | psl211_colour_view C (b, g) == v]
  = [set g in pgg_G psl211_M
    | ((g^-1)%g @: heart_block b) :&: C == pattern_of C v].
Proof.
move=> Hv0; apply/setP => g; rewrite !inE.
case: (g \in pgg_G psl211_M) => //=.
apply/eqP/eqP => [Hv|HS].
  apply/setP => i; rewrite /pattern_of !inE.
  have := congr1 (fun f : {ffun 'I_12 -> bool} => f i) Hv.
  rewrite /psl211_colour_view /colour_view ffunE /= colour_heartE => Hi.
  by case: (i \in C) Hi => /= [-> | _]; rewrite ?andbT ?andbF.
apply/ffunP => i.
rewrite /psl211_colour_view /colour_view ffunE /= colour_heartE.
case: ifP => HiC; last by rewrite Hv0 // HiC.
have := congr1 (fun S : {set 'I_12} => i \in S) HS.
by rewrite /pattern_of !inE HiC andbT /=.
Qed.

(** psl211_colour_fiber_cardE — for every coalition of at most five positions
    and every value of its colour view, the two chiralities have equally many
    shuffles showing that value. The counting premise the design-privacy
    bridge consumes, stated on the group rather than on the law. *)
Lemma psl211_colour_fiber_cardE (C : {set 'I_12}) (v : {ffun 'I_12 -> bool}) :
  (#|C| <= 5)%N ->
  #|[set g in pgg_G psl211_M | psl211_colour_view C (true, g) == v]|
  = #|[set g in pgg_G psl211_M | psl211_colour_view C (false, g) == v]|.
Proof.
move=> HC.
have Hempty (b : bool) (i0 : 'I_12) : i0 \notin C -> v i0 ->
    [set g in pgg_G psl211_M | psl211_colour_view C (b, g) == v] = set0.
  move=> Hi0C Hi0v; apply/setP => g; rewrite !inE andbC.
  case: (boolP (_ == v)) => //= /eqP Hveq.
  by move: Hi0v; rewrite -Hveq /psl211_colour_view /colour_view ffunE /=
     (negbTE Hi0C).
case: (boolP [forall i, (i \in C) || ~~ v i]) => [/forallP Hall|Hex];
  last first.
  move: Hex; rewrite negb_forall => /existsP[i0].
  rewrite negb_or negbK => /andP[Hi0C Hi0v].
  by rewrite !(Hempty _ i0).
have Hv0 : forall i, i \notin C -> v i = false.
  by move=> i HiC; apply/negbTE; move: (Hall i); rewrite (negbTE HiC).
rewrite (view_fiberE true Hv0) (view_fiberE false Hv0).
rewrite (fiber_inv_cardE C (pattern_of C v) true)
        (fiber_inv_cardE C (pattern_of C v) false).
rewrite (fiber_partitionE C (pattern_of C v) true)
        (fiber_partitionE C (pattern_of C v) false).
rewrite (stab_cardE true) (stab_cardE false) !orbit_blocksE /=.
congr (_ * _); apply: pattern_transferE => //.
by apply/subsetP => i; rewrite /pattern_of !inE => /andP[].
Qed.

(** psl211_colour_view_indep — every coalition of at most five positions has
    a colour view independent of the dealt chirality, under every prior on
    the chirality. The privacy claim of the PSL(2,11) instance, and the
    threshold the shuffle group's own transitivity cannot reach. *)
Lemma psl211_colour_view_indep (C : {set 'I_12}) :
  (#|C| <= 5)%N ->
  psl211P |= psl211_colour_view C _|_ psl211_secret.
Proof.
by move=> HC; apply: colour_view_indep_fibers => v;
   exact: psl211_colour_fiber_cardE.
Qed.

(* The two positivity premises are part of the mathematics, not bookkeeping:
   at a prior supported on one chirality the secret is almost surely
   constant and every observable is independent of it, so the plan's
   premise-free form of this lemma is false.  The witness value is the
   all-hearts pattern on the leak coalition; it occurs at the identity
   shuffle under the mirror deal and under no hexad deal, because a hexad
   block containing the six mirror positions would equal that mirror block,
   which psl211_blocks_disjoint forbids. *)
(** psl211_colour_view_dep_k6 — under a prior giving mass to both chiralities,
    the colour view of the six positions of the mirror representative is not
    independent of the dealt chirality. The five-position threshold is sharp:
    one more position already separates the two block systems, and the coalition
    that achieves it is a block of one of them. *)
Lemma psl211_colour_view_dep_k6 :
  secretP true != 0 -> secretP false != 0 ->
  (#|psl211_leak_coalition| = 6)%N /\
  ~ psl211P |= psl211_colour_view psl211_leak_coalition _|_ psl211_secret.
Proof.
move=> Hpt Hpf.
have HCeq : psl211_leak_coalition = heart_block true by [].
have Hcard6 := psl211_leak_coalition_card6.
pose v0 : {ffun 'I_12 -> bool} := [ffun i => i \in psl211_leak_coalition].
have Hview_true : psl211_colour_view psl211_leak_coalition (true, 1%g) = v0.
  apply/ffunP => i; rewrite /psl211_colour_view /colour_view /v0 !ffunE /=.
  rewrite perm1 /psl211_leak_coalition inE.
  by case: (psl211_is_heart _).
have Hhexo :
    orbit 'P^* (pgg_G psl211_M) (heart_block false) = psl211_hexad_blocks.
  by rewrite orbit_blocksE.
have Hmiro :
    orbit 'P^* (pgg_G psl211_M) (heart_block true) = psl211_mirror_blocks.
  by rewrite orbit_blocksE.
have Hview_false : forall g, g \in pgg_G psl211_M ->
    psl211_colour_view psl211_leak_coalition (false, g) <> v0.
  move=> g gG Hveq.
  have Hsub : psl211_leak_coalition \subset (g^-1)%g @: heart_block false.
    apply/subsetP => i Hi.
    have := congr1 (fun f : {ffun 'I_12 -> bool} => f i) Hveq.
    rewrite /psl211_colour_view /colour_view /v0 !ffunE /= colour_heartE Hi /=.
    by move=> ->.
  have Hcard : (#|(g^-1)%g @: heart_block false| = 6)%N.
    rewrite card_imset; last exact: perm_inj.
    rewrite /heart_block psl211_encode_heart_setE.
    by apply: psl211_block_card6; vm_compute.
  (* Six positions inside a six-element image force equality of the two. *)
  have Heq : (g^-1)%g @: heart_block false = psl211_leak_coalition.
    by apply/esym/eqP; rewrite eqEcard Hsub Hcard Hcard6.
  have Hhex : psl211_leak_coalition \in psl211_hexad_blocks.
    by rewrite -Heq -Hhexo; exact: mem_orbit (groupVr gG).
  have Hmir : psl211_leak_coalition \in psl211_mirror_blocks.
    by rewrite HCeq -Hmiro; exact: orbit_refl.
  by move: Hhex; rewrite (disjointFr psl211_blocks_disjoint Hmir).
have HP1 (b : bool) : secretP b != 0 -> 0 < psl211P (b, 1%g).
  move=> Hb; rewrite /psl211P fdist_prodE /=; apply: mulr_gt0.
    by rewrite lt0r Hb FDist.ge0.
  rewrite (@fdist_uniform_supp_in R _ (pgg_G psl211_M) psl211_G_pos 1%g
    (group1 _)).
  by rewrite invr_gt0 ltr0n; exact: psl211_G_pos.
have Hpv : 0 < `Pr[ (psl211_colour_view psl211_leak_coalition) = v0 ].
  rewrite lt0r pfwd1_ge0 andbT.
  apply/pfwd1_neq0; exists (true, 1%g); split; last exact: HP1 true Hpt.
  by rewrite inE /= Hview_true.
have Hps : 0 < `Pr[ psl211_secret = false ].
  rewrite lt0r pfwd1_ge0 andbT.
  apply/pfwd1_neq0; exists (false, 1%g); split; last exact: HP1 false Hpf.
  by rewrite inE.
have Hzero : `Pr[ [% psl211_colour_view psl211_leak_coalition, psl211_secret]
                  = (v0, false) ] = 0.
  apply/eqP; apply/negPn; apply/negP => /pfwd1_neq0 [[s g] [Hmem Hpos]].
  have gG : g \in pgg_G psl211_M.
    apply: contraLR Hpos => gN.
    rewrite /psl211P fdist_prodE /=
      (@fdist_uniform_supp_notin R _ (pgg_G psl211_M) psl211_G_pos g gN) mulr0.
    by apply/negP => /lt0r_neq0; rewrite eqxx.
  move: Hmem; rewrite inE /= xpair_eqE => /andP[/eqP Hv /eqP Hs].
  by apply: (Hview_false g gG); rewrite -Hs.
split; first exact: psl211_leak_coalition_card6.
move=> Hind.
move: (Hind v0 false) => Heq.
move: (mulr_gt0 Hpv Hps); rewrite -Heq Hzero.
by move/lt0r_neq0; rewrite eqxx.
Qed.

End secrecy.

(* The prior is the subject of every statement above, so it stays an explicit
   argument.  The section discharge had made it implicit on
   psl211_colour_view_dep_k6 alone, because it occurs in the type of that
   lemma's first premise.  The trailing slots on the two independence
   statements are inde_RV's own quantifiers, showing through the definition;
   they are not arguments a caller supplies. *)
Arguments psl211_colour_view_dep_k6 [R] secretP _ _.
Arguments psl211_colour_view_indep [R] secretP [C]%_set_scope _.
