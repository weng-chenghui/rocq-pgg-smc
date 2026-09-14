(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_scheme: the twelve-card PSL(2,11) threshold scheme and its plug     *)
(*                                                                            *)
(* The chirality secret of psl211_orbit is packaged as a ThresholdScheme      *)
(* bool 'I_12 with privacy threshold five: a coalition of at most five card   *)
(* positions sees a view that occurs under both secrets (the distributional   *)
(* statement is psl211_secrecy.v's), while the implemented reconstruction     *)
(* reads all twelve endpoints.                                                *)
(*                                                                            *)
(* Privacy here does not come from transitivity, as it does for the           *)
(* eight-card PGL(2,7) scheme: PSL(2,11) is only 2-transitive on the twelve   *)
(* positions, so no group element fixes an arbitrary five-set. It comes       *)
(* instead from the design property of the two Steiner systems, that a        *)
(* coalition of at most five positions meets the blocks of the mirror system  *)
(* in exactly the same patterns, with the same multiplicities, as it meets    *)
(* the blocks of the hexad system (psl211_count_okT). A coalition therefore   *)
(* cannot tell which system its cards were dealt from.                        *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_orbit_valid s sh == sh is a distinct-card deck whose heart set is *)
(*                              a block of the system named by s              *)
(*   psl211_orbit_scheme     == the ThresholdScheme bool 'I_12, threshold 5   *)
(*   psl211_plug             == the ReconPlug over psl211_M, content the      *)
(*                              identity                                      *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_orbit_correct         == a valid deck reconstructs its chirality  *)
(*   psl211_orbit_encode_valid    == the encoder deals each chirality         *)
(*   psl211_private               == coalitions of at most five positions are *)
(*                                   re-dealable to either chirality          *)
(*   psl211_orbit_recon_invariant == recovery is invariant under the shuffle  *)
(*                                   action on positions                      *)
(*                                                                            *)
(* The secrecy statements concern the pre-reveal execution: after the         *)
(* public reveal every player learns the secret by design.                    *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import psl211_blocks psl211_group psl211_orbit.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* -------------------------------------------------------------------------- *)
(* Permutations moving one subset onto another of the same size.              *)
(* -------------------------------------------------------------------------- *)

(* Candidate for a mathcomp-only lib/perm_exchange.v; kept Local here until
   then. *)

(* perm_on is a subset statement, so it is monotone in its support. *)
Local Lemma perm_onS (T : finType) (S1 S2 : {set T}) (s : {perm T}) :
  S1 \subset S2 -> perm_on S1 s -> perm_on S2 s.
Proof. by move=> H1 H2; exact: subset_trans H2 H1. Qed.

(* Two equinumerous subsets are exchanged by a permutation supported on their
   union, which therefore fixes every point outside both.  The re-deal needs
   exactly this: the cards already on the coalition must not move. *)
Local Lemma perm_of_eq_card (T : finType) (n : nat) (U V : {set T}) :
  (#|U :\: V| <= n)%N -> #|U| = #|V| ->
  exists s : {perm T}, perm_on (U :|: V) s /\ [set s x | x in U] = V.
Proof.
elim: n U => [|n IH] U HD Hcard.
  have HUV : U \subset V by rewrite -setD_eq0 -cards_eq0 -leqn0.
  have -> : U = V by apply/eqP; rewrite eqEcard HUV Hcard leqnn.
  exists 1%g; split; first exact: perm_on1.
  by apply/setP => x; apply/imsetP/idP => [[y Hy ->]|Hx];
     rewrite ?perm1 //; exists x; rewrite ?perm1.
case: (set_0Vmem (U :\: V)) => [HU0 | [u Hu]].
  have HUV : U \subset V by rewrite -setD_eq0 HU0.
  have -> : U = V by apply/eqP; rewrite eqEcard HUV Hcard leqnn.
  exists 1%g; split; first exact: perm_on1.
  by apply/setP => x; apply/imsetP/idP => [[y Hy ->]|Hx];
     rewrite ?perm1 //; exists x; rewrite ?perm1.
have HVU : #|V :\: U| = #|U :\: V| by rewrite !cardsD Hcard setIC.
have : (0 < #|V :\: U|)%N by rewrite HVU (cardsD1 u) Hu.
case/card_gt0P => v Hv.
pose t := tperm u v.
have Hvu : v \notin U by move: Hv; rewrite inE => /andP[].
have HuU : u \in U by move: Hu; rewrite inE => /andP[].
have HuV : u \notin V by move: Hu; rewrite inE => /andP[].
have HvV : v \in V by move: Hv; rewrite inE => /andP[].
have Ht (y : T) : y \in U -> t y = (if y == u then v else y).
  move=> Hy; rewrite /t; case: tpermP => [->|Hy'|]; rewrite ?eqxx //.
    by rewrite Hy' (negbTE Hvu) in Hy.
  by move=> /eqP/negbTE-> _.
pose U1 := [set t x | x in U].
have HU1card : #|U1| = #|V| by rewrite card_imset ?Hcard //; exact: perm_inj.
have HU1sub : U1 \subset U :|: V.
  apply/subsetP => x /imsetP[y Hy ->]; rewrite Ht // inE.
  by case: ifP => _; [rewrite HvV orbT | rewrite Hy].
have HU1D : U1 :\: V \subset (U :\: V) :\ u.
  apply/subsetP => x; rewrite !inE => /andP[HxV /imsetP[y Hy Hxy]].
  move: Hxy; rewrite Ht //; case: ifP => [_ Hxv | Hyu Hxy].
    by rewrite Hxv HvV in HxV.
  by rewrite Hxy in HxV *; rewrite Hyu HxV Hy.
have HD1 : (#|U1 :\: V| <= n)%N.
  apply: (leq_trans (subset_leq_card HU1D)).
  have HE := cardsD1 u (U :\: V); rewrite Hu add1n in HE.
  by rewrite -ltnS -HE.
have [s1 [Hon1 Him1]] := IH U1 HD1 HU1card.
exists (t * s1)%g; split; last first.
  by rewrite -Him1 /U1 -imset_comp; apply: eq_imset => x; rewrite permM.
apply: perm_onM.
  apply: (perm_onS _ (tperm_on u v)).
  by apply/subsetP => x; rewrite !inE => /orP[/eqP->|/eqP->];
     rewrite ?HuU ?HvV ?orbT.
by apply: (perm_onS _ Hon1); rewrite subUset HU1sub subsetUr.
Qed.

(* -------------------------------------------------------------------------- *)
(* Reading the design certificate at a coalition of positions.                *)
(* -------------------------------------------------------------------------- *)

(* Every subsequence of a coalition code list is enumerated as a pattern. *)
Local Lemma mem_sublists (C L : seq nat) :
  subseq L C -> L \in psl211_sublists C.
Proof.
elim: C L => [|a C IH] L /=.
  by move=> /eqP ->; rewrite inE.
case: L => [_ | b L].
  by rewrite mem_cat IH ?sub0seq.
rewrite mem_cat; case: (altP (b =P a)) => [-> Hsub | Hne Hsub].
  by apply/orP; right; apply: map_f; exact: IH.
by apply/orP; left; exact: IH.
Qed.

(* The code list of a subset's enumeration is strictly ascending. *)
Local Lemma sorted_val_enum (S : {set 'I_12}) : sorted ltn (map val (enum S)).
Proof.
rewrite sorted_map.
have He : enum S = [seq x <- enum 'I_12 | x \in S]
  by rewrite enumT -deprecated_filter_index_enum.
rewrite He; apply: sorted_filter.
  by move=> y x z; apply: ltn_trans.
by rewrite -sorted_map val_enum_ord; exact: iota_ltn_sorted.
Qed.

(* Every code of a subset's enumeration lies below twelve. *)
Local Lemma all_lt12_enum (S : {set 'I_12}) :
  all (fun n => (n < 12)%N) (map val (enum S)).
Proof. by apply/allP => n /mapP[i _ ->]; exact: ltn_ord. Qed.

(* Enumerating a subset of a coalition gives a subsequence of its code list. *)
Local Lemma subseq_val_enum (A C : {set 'I_12}) :
  A \subset C -> subseq (map val (enum A)) (map val (enum C)).
Proof.
move=> HAC; apply: map_subseq.
have HeA : enum A = [seq x <- enum 'I_12 | x \in A]
  by rewrite enumT -deprecated_filter_index_enum.
have HeC : enum C = [seq x <- enum 'I_12 | x \in C]
  by rewrite enumT -deprecated_filter_index_enum.
rewrite HeC subseq_filter HeA filter_subseq andbT.
by apply/allP => x; rewrite mem_filter => /andP[/(subsetP HAC)].
Qed.

(* The certificate is a conjunction over the five coalition sizes; this is its
   projection at one size.  The false branches are discharged before the
   certificate enters the context, since deciding a hypothesis of the form
   psl211_count_ok_k i by computation does not terminate in usable time. *)
Local Lemma count_ok_k_le5 (k : nat) :
  (0 < k)%N -> (k < 5.+1)%N -> psl211_count_ok_k k.
Proof.
move=> Hk0 Hk.
have E : (k == 1) || ((k == 2) || ((k == 3) || ((k == 4) || (k == 5)))).
  by move: Hk0 Hk; case: k => [|[|[|[|[|[|m]]]]]].
case/and5P: psl211_count_okT => H1 H2 H3 H4 H5.
case/orP: E => [/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]].
- exact: H1.
- exact: H2.
- exact: H3.
- exact: H4.
- exact: H5.
Qed.

(* -------------------------------------------------------------------------- *)
(* The two systems, indexed by the chirality bit.                             *)
(* -------------------------------------------------------------------------- *)

(* The table of the system named by s. *)
Local Definition sys_tbl (s : bool) : seq (seq nat) :=
  if s then psl211_mirror_tbl else psl211_hexad_tbl.

(* The blocks of the system named by s, as position sets. *)
Local Definition sys_blocks (s : bool) : {set {set 'I_12}} :=
  psl211_sets_of (sys_tbl s).

Local Lemma sys_blocksT : sys_blocks true = psl211_mirror_blocks.
Proof. by []. Qed.

Local Lemma sys_blocksF : sys_blocks false = psl211_hexad_blocks.
Proof. by []. Qed.

Local Lemma asc6_sys_tbl (s : bool) : all psl211_asc6 (sys_tbl s).
Proof.
by case: s; [exact: (psl211_tbl_ok_asc6 psl211_tbl_ok_mirrorT)
           | exact: (psl211_tbl_ok_asc6 psl211_tbl_ok_hexadT)].
Qed.

Local Lemma uniq_sys_tbl (s : bool) : uniq (sys_tbl s).
Proof.
by case: s; [exact: psl211_mirror_tbl_uniq | exact: psl211_hexad_tbl_uniq].
Qed.

(* A block of either system has six positions. *)
Local Lemma sys_card6 (s : bool) (B : {set 'I_12}) :
  B \in sys_blocks s -> #|B| = 6.
Proof.
rewrite /sys_blocks inE => /hasP[R HR /eqP <-].
by apply: psl211_block_card6; exact: (allP (asc6_sys_tbl s) _ HR).
Qed.

(* A block of the system named by s carries the chirality bit s. *)
Local Lemma sys_class (s : bool) (B : {set 'I_12}) :
  B \in sys_blocks s -> psl211_subset_class B = s.
Proof.
case: s; rewrite ?sys_blocksT ?sys_blocksF => HB //.
exact: (disjointFl psl211_blocks_disjoint HB).
Qed.

(* A block of either system is a legitimate heart set. *)
Local Lemma sys_valid (s : bool) (B : {set 'I_12}) :
  B \in sys_blocks s -> psl211_subset_valid B.
Proof.
rewrite /psl211_subset_valid.
by case: s; rewrite ?sys_blocksT ?sys_blocksF => ->; rewrite ?orbT.
Qed.

(* The design certificate, read on position sets: a coalition of at most five
   positions meets the two systems in the same patterns with the same
   multiplicities.  This is the whole content of privacy at five. *)
Local Lemma sys_pattern_transfer (s1 s2 : bool) (C A : {set 'I_12}) :
  (0 < #|C|)%N -> (#|C| < 5.+1)%N -> A \subset C ->
  #|[set B in sys_blocks s1 | B :&: C == A]|
  = #|[set B in sys_blocks s2 | B :&: C == A]|.
Proof.
move=> HC0 HC HAC.
have Hlift (s : bool) :
    #|[set B in sys_blocks s | B :&: C == A]|
    = psl211_pattern_count (sys_tbl s) (map val (enum C)) (map val (enum A)).
  by rewrite /sys_blocks psl211_pattern_countE //;
     [exact: asc6_sys_tbl | exact: uniq_sys_tbl].
have Hmh :
    psl211_pattern_count psl211_mirror_tbl (map val (enum C))
      (map val (enum A))
    = psl211_pattern_count psl211_hexad_tbl (map val (enum C))
      (map val (enum A)).
  have HAl : map val (enum A) \in psl211_sublists (map val (enum C)).
    by apply: mem_sublists; exact: subseq_val_enum.
  have HCl : map val (enum C) \in psl211_subsets #|C|.
    apply: psl211_mem_subsets;
      [exact: sorted_val_enum | exact: all_lt12_enum |].
    by rewrite size_map -cardE.
  by move/allP: (count_ok_k_le5 HC0 HC) => /(_ _ HCl)/allP/(_ _ HAl)/eqP.
rewrite !Hlift; case: s1; case: s2.
- by [].
- exact: Hmh.
- exact: esym Hmh.
- by [].
Qed.

(* -------------------------------------------------------------------------- *)
(* Validity, correctness, and the re-deal at five.                            *)
(* -------------------------------------------------------------------------- *)

(** psl211_orbit_valid s sh — a distinct-card deck whose heart set is a block
    of the system named by s. The validity predicate of the twelve-card
    chirality scheme: the secret is carried by which Steiner system the six
    heart positions form a block of. *)
Definition psl211_orbit_valid (s : bool) (sh : 12.-tuple 'I_12) : Prop :=
  psl211_deck_ok sh /\ psl211_subset_valid (psl211_heart_set sh)
  /\ psl211_orbit_class sh = s.

(** psl211_orbit_correct — a valid deck reconstructs its chirality bit. The
    reconstruction of the scheme is the classifier itself, so correctness is
    the third conjunct of validity. *)
Lemma psl211_orbit_correct (s : bool) (sh : 12.-tuple 'I_12) :
  psl211_orbit_valid s sh -> psl211_orbit_class sh = s.
Proof. by move=> [_ [_ ->]]. Qed.

(** psl211_orbit_encode_valid — the encoder outputs a valid deck of the
    requested chirality, so both secrets are dealt by some deck. *)
Lemma psl211_orbit_encode_valid (s : bool) :
  psl211_orbit_valid s (psl211_orbit_encode s).
Proof.
split; first exact: psl211_orbit_encode_deck.
by split; [exact: psl211_orbit_encode_valid_set | exact: psl211_orbit_encodeK].
Qed.

(** psl211_private — every coalition of at most five positions is re-dealable
    to either chirality with the same cards at its positions. The set of
    five-player views is therefore identical under the two secrets; the
    distributional half, that the two views are also equally likely, is the
    counting premise discharged in design_privacy.v. *)
Lemma psl211_private (s1 s2 : bool) (sh : 12.-tuple 'I_12) (C : {set 'I_12}) :
  (#|C| < 5.+1)%N -> psl211_orbit_valid s1 sh ->
  exists sh', psl211_orbit_valid s2 sh' /\
    (forall i : 'I_12, i \in C -> tnth sh' i = tnth sh i).
Proof.
(* The coalition's pattern A = C cap H has the same block count in the target
   system (psl211_count_okT, lifted by sys_pattern_transfer), so some block B'
   of that system meets C in A.  Re-deal by permuting the twelve codes rather
   than the positions: a permutation supported off the codes already on C
   carries the codes of B' onto the heart codes, keeps the cards of C where
   they are, and is injective for free, which settles distinctness. *)
move=> HC [Hdeck [Hvalid Hclass]].
case: (posnP #|C|) => [HC0|HC0].
  exists (psl211_orbit_encode s2); split.
    exact: psl211_orbit_encode_valid.
  by move=> i; rewrite (cards0_eq HC0) inE.
have Hinj : injective (tnth sh) by apply/tuple_uniqP.
(* the coalition's pattern, and a block of the target system showing it *)
pose A := psl211_heart_set sh :&: C.
have HAC : A \subset C by exact: subsetIr.
have HHfam : psl211_heart_set sh \in sys_blocks s1.
  move: Hvalid Hclass; rewrite /psl211_subset_valid /psl211_orbit_class.
  rewrite /psl211_subset_class -sys_blocksT -sys_blocksF.
  by case: s1 => [_ ->|/orP[->|]] //.
have Hpos : (0 < #|[set B in sys_blocks s2 | B :&: C == A]|)%N.
  rewrite -(sys_pattern_transfer s1 s2 HC0 HC HAC).
  by apply/card_gt0P; exists (psl211_heart_set sh); rewrite inE HHfam /=;
     apply/eqP.
have [B' HB'] := card_gt0P Hpos.
move: HB'; rewrite inE => /andP[HB'fam /eqP HB'C].
(* P the codes on the coalition, U the codes on the target block, V the
   heart codes; the cards on C pin U and V to the same trace on P *)
pose P := [set tnth sh i | i in C].
pose U := [set tnth sh i | i in B'].
pose V := [set c : 'I_12 | psl211_is_heart c].
have HVE : V = psl211_list_to_set [:: 0; 1; 2; 3; 4; 5].
  apply/setP => x; rewrite !inE /psl211_is_heart.
  by case: x => -[|[|[|[|[|[|m]]]]]] Hm.
have HVcard : #|V| = 6 by rewrite HVE; apply: psl211_block_card6; vm_compute.
have HUcard : #|U| = 6.
  by rewrite /U (card_imset _ Hinj); exact: sys_card6 HB'fam.
have HUP : U :&: P = V :&: P.
  rewrite /U /P -imsetI; last by move=> x y _ _; exact: Hinj.
  rewrite HB'C; apply/setP => x; rewrite inE.
  apply/imsetP/andP => [[i]|].
    rewrite /A !inE => /andP[HiH HiC] ->; split => //.
    by rewrite imset_f.
  case=> Hx /imsetP[i HiC Hxi]; exists i; last exact: Hxi.
  by rewrite /A !inE HiC andbT -Hxi; move: Hx; rewrite inE.
(* the code permutation that re-deals the hearts onto B' and fixes P *)
have Hcard' : #|(U :\: P)| = #|(V :\: P)| by rewrite !cardsD HUcard HVcard HUP.
have [sg [Hon Him]] :=
  perm_of_eq_card (leqnn #|(U :\: P) :\: (V :\: P)|) Hcard'.
have Hfix (c : 'I_12) : c \in P -> sg c = c.
  move=> Hc; apply: (out_perm Hon).
  by rewrite !inE Hc.
have Hid (S : {set 'I_12}) : S \subset P -> [set sg x | x in S] = S.
  move=> HS; apply/setP => x; apply/imsetP/idP => [[y Hy ->]|Hx].
    by rewrite Hfix ?(subsetP HS).
  by exists x => //; rewrite Hfix ?(subsetP HS).
have HimU : [set sg x | x in U] = V.
  by rewrite -(setID U P) imsetU Him (Hid _ (subsetIr U P)) HUP setID.
(* the re-dealt deck *)
pose sh' := [tuple sg (tnth sh i) | i < 12].
have HPmem (i : 'I_12) : i \in C -> tnth sh i \in P.
  by move=> Hi; exact: imset_f.
have Hagree (i : 'I_12) : i \in C -> tnth sh' i = tnth sh i.
  by move=> Hi; rewrite tnth_mktuple (Hfix _ (HPmem _ Hi)).
have Hinj' : injective (tnth sh').
  by move=> i j; rewrite !tnth_mktuple => /perm_inj/Hinj.
have Hheart : psl211_heart_set sh' = B'.
  apply/setP => i; rewrite inE tnth_mktuple.
  have -> : psl211_is_heart (sg (tnth sh i)) = (sg (tnth sh i) \in V)
    by rewrite inE.
  by rewrite -HimU (mem_imset _ _ (@perm_inj _ sg)) (mem_imset _ _ Hinj).
exists sh'; split; last exact: Hagree.
split; first by apply/tuple_uniqP.
split; first by rewrite Hheart; exact: sys_valid HB'fam.
by rewrite /psl211_orbit_class Hheart; exact: sys_class HB'fam.
Qed.

(* -------------------------------------------------------------------------- *)
(* The records.                                                               *)
(* -------------------------------------------------------------------------- *)

(** psl211_orbit_scheme — the twelve-card chirality ThresholdScheme: secret
    bool, shares 'I_12, privacy threshold five. Reconstruction reads all
    twelve positions, so the threshold five is a privacy bound and not a
    recovery bound. *)
Definition psl211_orbit_scheme : ThresholdScheme bool 'I_12 :=
  @MkThresholdScheme bool 'I_12 (pgg_N' psl211_M) 5
    psl211_orbit_valid psl211_orbit_class psl211_orbit_encode
    psl211_orbit_correct psl211_private psl211_orbit_encode_valid.

(** psl211_orbit_recon_invariant — recovery is invariant under the shuffle
    action on positions, the compatibility contract between the scheme and
    the monodromy representation of psl211_M. *)
Lemma psl211_orbit_recon_invariant :
  @ts_recon_perm_invariant _ (pgg_G psl211_M) bool 'I_12
    psl211_orbit_scheme (fun g => @pgg_rho psl211_M g).
Proof.
by move=> g s shares gG [_ [_ <-]];
   exact: (psl211_orbit_class_invariant g shares gG).
Qed.

(** psl211_plug — the reconstruction plug over psl211_M, content the identity.
    The content is applied before validity is checked, and psl211_deck_ok
    demands twelve distinct cards, so the content cannot be the colour
    readout. What a coalition sees of the colours is stated separately, on
    the deck rather than through the plug. *)
Definition psl211_plug : ReconPlug psl211_M bool :=
  @MkReconPlug psl211_M bool psl211_orbit_scheme id
    (fun g => @pgg_rho psl211_M g) psl211_orbit_recon_invariant.
