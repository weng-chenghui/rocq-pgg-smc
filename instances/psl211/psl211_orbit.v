(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_orbit: the chirality secret of the twelve-card PSL(2,11) scheme     *)
(*                                                                            *)
(* A deck is a twelve-position arrangement [sh : 12.-tuple 'I_12] of the      *)
(* cards 'I_12; a heart is a card with code below six. The heart positions    *)
(* form a six-subset of the twelve positions, and the two Steiner systems     *)
(* S(5,6,12) of psl211_blocks.v split the six-subsets that occur: the mirror  *)
(* system and the hexad system are the two orbits of the shuffle group, and   *)
(* which of the two a deck's heart set belongs to is the one-bit secret.      *)
(* Every ground check runs on nat code lists, so it is vm_compute-safe; the   *)
(* one place where that fails is a mktuple over enum 'I_12, which is pinned   *)
(* to a literal list (enum_ord12) before reduction.                           *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_is_heart c    == the card c is a heart (code below six)           *)
(*   psl211_deck_ok sh    == the arrangement sh has distinct cards            *)
(*   psl211_heart_set sh  == the set of positions holding a heart             *)
(*   psl211_list_to_set L == the position set coded by the code list L        *)
(*   psl211_sets_of tbl   == the family of position sets coded by a table     *)
(*   psl211_mirror_blocks == the mirror Steiner system, as a set of sets      *)
(*   psl211_hexad_blocks  == the M12 hexad system, as a set of sets           *)
(*   psl211_subset_class  == the chirality bit of a six-subset of positions   *)
(*   psl211_orbit_class   == the chirality bit of a deck's heart set          *)
(*   psl211_orbit_encode  == a distinct-card deck of a chosen chirality       *)
(*   psl211_rep_list b    == the representative row of the system b names     *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_mirror_invariant, psl211_hexad_invariant                          *)
(*                          == each system is stable under every shuffle      *)
(*   psl211_blocks_disjoint == no six-subset lies in both systems             *)
(*   psl211_orbit_class_invariant == the chirality bit survives every shuffle *)
(*   psl211_deck_stable     == a shuffle preserves distinctness of cards      *)
(*   psl211_orbit_encodeK   == the encoder deals the requested chirality      *)
(*   psl211_card_mirror_blocks, psl211_card_hexad_blocks                      *)
(*                          == each system has 132 blocks                     *)
(*   psl211_pattern_countE  == the finset census of a leak pattern equals the *)
(*                             table-level count of psl211_blocks.v           *)
(*   psl211_mirror_orbitE, psl211_hexad_orbitE                                *)
(*                          == each system is the shuffle orbit of its        *)
(*                             representative row                             *)
(*                                                                            *)
(* This file deliberately omits Set Implicit Arguments, as pgl27_orbit.v      *)
(* does: the group argument of psl211_orbit_class_invariant and of            *)
(* psl211_deck_stable must stay explicit for the profile files.               *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From pgg_smc Require Import pgg_interface psl211_blocks psl211_group.

Import Prenex Implicits.

(* -------------------------------------------------------------------------- *)
(* Deck, hearts and the chirality classifier.                                 *)
(* -------------------------------------------------------------------------- *)

(** psl211_is_heart — the card c is a heart, i.e. carries a code below six.
    The colour predicate splitting the twelve cards into six hearts and six
    clubs. *)
Definition psl211_is_heart (c : 'I_12) : bool := (val c < 6)%N.

(** psl211_deck_ok — the arrangement sh deals twelve distinct cards. The
    valid-deck predicate of the twelve-card scheme. *)
Definition psl211_deck_ok (sh : 12.-tuple 'I_12) : bool := uniq sh.

(** psl211_heart_set — the set of positions of sh holding a heart. The
    six-subset of the twelve positions carrying the secret. *)
Definition psl211_heart_set (sh : 12.-tuple 'I_12) : {set 'I_12} :=
  [set i | psl211_is_heart (tnth sh i)].

(** psl211_list_to_set — the set of positions whose codes occur in the code
    list L. The bridge from the literal tables to the finset layer. *)
Definition psl211_list_to_set (L : seq nat) : {set 'I_12} :=
  [set x : 'I_12 | val x \in L].

(** psl211_sets_of — the family of position sets coded by the rows of a
    table. *)
Definition psl211_sets_of (tbl : seq (seq nat)) : {set {set 'I_12}} :=
  [set S | has (fun R => psl211_list_to_set R == S) tbl].

(** psl211_mirror_blocks — the mirror Steiner system as a family of position
    sets. One of the two secret classes. *)
Definition psl211_mirror_blocks : {set {set 'I_12}} :=
  psl211_sets_of psl211_mirror_tbl.

(** psl211_hexad_blocks — the M12 hexad system as a family of position sets.
    The other secret class. *)
Definition psl211_hexad_blocks : {set {set 'I_12}} :=
  psl211_sets_of psl211_hexad_tbl.

(** psl211_subset_valid — S is a block of one of the two Steiner systems, so
    S can be the heart set of a deal the scheme produces. *)
Definition psl211_subset_valid (S : {set 'I_12}) : bool :=
  (S \in psl211_mirror_blocks) || (S \in psl211_hexad_blocks).

(** psl211_subset_class — true on the mirror system, false on the hexad
    system, arbitrary elsewhere. The chirality bit of a six-subset. *)
Definition psl211_subset_class (S : {set 'I_12}) : bool :=
  S \in psl211_mirror_blocks.

(** psl211_orbit_class — the chirality bit of the heart positions of a deck.
    The one-bit secret dealt by the twelve-card PSL(2,11) scheme. *)
Definition psl211_orbit_class (sh : 12.-tuple 'I_12) : bool :=
  psl211_subset_class (psl211_heart_set sh).

(* -------------------------------------------------------------------------- *)
(* Invariance of the two systems under the shuffle group.                     *)
(* -------------------------------------------------------------------------- *)

(* Every code of every row lies below twelve. *)
Local Definition rows_lt12 (tbl : seq (seq nat)) : bool :=
  all (fun R => all (fun x => (x < 12)%N) R) tbl.

Local Lemma rows_lt12_mirror : rows_lt12 psl211_mirror_tbl.
Proof. by vm_compute. Qed.

Local Lemma rows_lt12_hexad : rows_lt12 psl211_hexad_tbl.
Proof. by vm_compute. Qed.

(* The image of a coded row under a table-given permutation is coded by the
   table image of the row. *)
Local Lemma imset_list_to_set (g : {perm 'I_12}) (t : seq nat) (R : seq nat) :
  (forall x : 'I_12, val (g x) = nth 0 t (val x)) ->
  all (fun x => (x < 12)%N) R ->
  g @: psl211_list_to_set R = psl211_list_to_set (psl211_map_row t R).
Proof.
move=> Hg HR; apply/setP => y; rewrite inE /psl211_map_row mem_sort.
apply/imsetP/idP => [[x]|].
  rewrite inE => Hx ->; rewrite Hg.
  by apply/mapP; exists (val x).
case/mapP => v Hv Hy.
have Hv12 : (v < 12)%N by move/allP: HR => /(_ v Hv).
exists (Ordinal Hv12); first by rewrite inE.
by apply: val_inj; rewrite Hg.
Qed.
Arguments imset_list_to_set [g t R].

(* A letter that maps every row of a table into the table maps the coded
   family into itself. *)
Local Lemma sets_of_gen_sub (tbl : seq (seq nat)) (g : {perm 'I_12})
    (t : seq nat) :
  (forall x : 'I_12, val (g x) = nth 0 t (val x)) ->
  rows_lt12 tbl -> psl211_stable_ok t tbl ->
  forall S, S \in psl211_sets_of tbl -> (g @: S) \in psl211_sets_of tbl.
Proof.
move=> Hg Hlt Hst S; rewrite !inE => /hasP[R Rtbl /eqP <-].
have HR : all (fun x => (x < 12)%N) R by move/allP: Hlt => /(_ R Rtbl).
apply/hasP; exists (psl211_map_row t R); first by move/allP: Hst => /(_ R Rtbl).
by rewrite -(imset_list_to_set Hg HR).
Qed.
Arguments sets_of_gen_sub [tbl g t].

(* An injective self-map that sends a finite set into itself reflects
   membership in it. *)
Local Lemma stab_of_sub (T : finType) (F : T -> T) (A : {set T}) :
  injective F -> (forall x, x \in A -> F x \in A) ->
  forall x, (F x \in A) = (x \in A).
Proof.
move=> Finj Hsub x; apply/idP/idP; last exact: Hsub.
have HFA : F @: A = A.
  apply/eqP; rewrite eqEcard (card_imset _ Finj) leqnn andbT.
  by apply/subsetP => y /imsetP[z zA ->]; exact: Hsub.
by rewrite -{1}HFA => /imsetP[z zA /Finj ->].
Qed.
Arguments stab_of_sub [T F A].

(* The permutations under which membership in a family of sets is invariant. *)
Local Definition stab_of (A : {set {set 'I_12}}) : {set {perm 'I_12}} :=
  [set g : {perm 'I_12} |
     [forall S : {set 'I_12}, ((g @: S) \in A) == (S \in A)]].

Local Lemma stab_ofP (A : {set {set 'I_12}}) (g : {perm 'I_12}) :
  reflect (forall S : {set 'I_12}, ((g @: S) \in A) = (S \in A))
          (g \in stab_of A).
Proof.
rewrite inE; apply: (iffP forallP) => H S; by [apply/eqP | apply/eqP].
Qed.

Local Lemma group_set_stab_of (A : {set {set 'I_12}}) : group_set (stab_of A).
Proof.
apply/group_setP; split.
  apply/stab_ofP => S.
  have -> : (1%g : {perm 'I_12}) @: S = S.
    apply/setP => x; apply/imsetP/idP => [[y yS ->]|xS]; first by rewrite perm1.
    by exists x => //; rewrite perm1.
  by [].
move=> g h /stab_ofP Hg /stab_ofP Hh; apply/stab_ofP => S.
have -> : ((g * h)%g) @: S = h @: (g @: S).
  by rewrite -imset_comp; apply: eq_imset => x; rewrite permM.
by rewrite Hh Hg.
Qed.

Local Canonical stab_of_group A := Group (group_set_stab_of A).

Local Lemma gens_sub_stab (A : {set {set 'I_12}}) :
  (forall S : {set 'I_12}, ((psl211_r4_perm @: S) \in A) = (S \in A)) ->
  (forall S : {set 'I_12}, ((psl211_m6_perm @: S) \in A) = (S \in A)) ->
  [set tnth psl211_gens i | i : 'I_2] \subset stab_of A.
Proof.
move=> H1 H2; apply/subsetP => x /imsetP[i _ ->]; apply/stab_ofP.
by case: i => -[|[|//]] Hlt.
Qed.

Local Lemma r4_stab_mirror (S : {set 'I_12}) :
  ((psl211_r4_perm @: S) \in psl211_mirror_blocks)
  = (S \in psl211_mirror_blocks).
Proof.
apply: (stab_of_sub (F := fun S0 : {set 'I_12} => psl211_r4_perm @: S0)).
  exact/imset_inj/perm_inj.
exact: (sets_of_gen_sub psl211_r4_permE rows_lt12_mirror
                        psl211_stable_r4_mirrorT).
Qed.

Local Lemma m6_stab_mirror (S : {set 'I_12}) :
  ((psl211_m6_perm @: S) \in psl211_mirror_blocks)
  = (S \in psl211_mirror_blocks).
Proof.
apply: (stab_of_sub (F := fun S0 : {set 'I_12} => psl211_m6_perm @: S0)).
  exact/imset_inj/perm_inj.
exact: (sets_of_gen_sub psl211_m6_permE rows_lt12_mirror
                        psl211_stable_m6_mirrorT).
Qed.

Local Lemma r4_stab_hexad (S : {set 'I_12}) :
  ((psl211_r4_perm @: S) \in psl211_hexad_blocks)
  = (S \in psl211_hexad_blocks).
Proof.
apply: (stab_of_sub (F := fun S0 : {set 'I_12} => psl211_r4_perm @: S0)).
  exact/imset_inj/perm_inj.
exact: (sets_of_gen_sub psl211_r4_permE rows_lt12_hexad
                        psl211_stable_r4_hexadT).
Qed.

Local Lemma m6_stab_hexad (S : {set 'I_12}) :
  ((psl211_m6_perm @: S) \in psl211_hexad_blocks)
  = (S \in psl211_hexad_blocks).
Proof.
apply: (stab_of_sub (F := fun S0 : {set 'I_12} => psl211_m6_perm @: S0)).
  exact/imset_inj/perm_inj.
exact: (sets_of_gen_sub psl211_m6_permE rows_lt12_hexad
                        psl211_stable_m6_hexadT).
Qed.

Local Lemma G_sub_stab_mirror :
  pgg_G psl211_M \subset stab_of psl211_mirror_blocks.
Proof.
by rewrite gen_subG; apply: gens_sub_stab;
   [exact: r4_stab_mirror | exact: m6_stab_mirror].
Qed.

Local Lemma G_sub_stab_hexad :
  pgg_G psl211_M \subset stab_of psl211_hexad_blocks.
Proof.
by rewrite gen_subG; apply: gens_sub_stab;
   [exact: r4_stab_hexad | exact: m6_stab_hexad].
Qed.

(** psl211_mirror_invariant — membership in the mirror system is invariant
    under every shuffle of the group. Privacy rests on the shuffle not moving
    a block out of its system. *)
Lemma psl211_mirror_invariant (g : pgg_gT psl211_M) (S : {set 'I_12}) :
  g \in pgg_G psl211_M ->
  ((g @: S) \in psl211_mirror_blocks) = (S \in psl211_mirror_blocks).
Proof.
move=> gG.
have /stab_ofP H : g \in stab_of psl211_mirror_blocks
  by exact: (subsetP G_sub_stab_mirror).
exact: H.
Qed.

(** psl211_hexad_invariant — membership in the hexad system is invariant
    under every shuffle of the group. *)
Lemma psl211_hexad_invariant (g : pgg_gT psl211_M) (S : {set 'I_12}) :
  g \in pgg_G psl211_M ->
  ((g @: S) \in psl211_hexad_blocks) = (S \in psl211_hexad_blocks).
Proof.
move=> gG.
have /stab_ofP H : g \in stab_of psl211_hexad_blocks
  by exact: (subsetP G_sub_stab_hexad).
exact: H.
Qed.

(* No row of one table has the same positions as a row of the other. *)
Local Definition tables_distinct : bool :=
  all (fun R => all (fun R' =>
         ~~ all (fun n => (n \in R) == (n \in R')) (iota 0 12))
       psl211_hexad_tbl) psl211_mirror_tbl.

Local Lemma tables_distinctT : tables_distinct.
Proof. by vm_compute. Qed.

(** psl211_blocks_disjoint — no six-subset of positions lies in both Steiner
    systems, so the chirality bit is well defined on the blocks that occur. *)
Lemma psl211_blocks_disjoint :
  [disjoint psl211_mirror_blocks & psl211_hexad_blocks].
Proof.
rewrite -setI_eq0; apply/eqP/setP => S; rewrite !inE.
apply/negbTE; apply/negP => /andP[/hasP[R RA /eqP HR] /hasP[R' RB /eqP HR']].
move/allP: tables_distinctT => /(_ R RA)/allP/(_ R' RB)/negP; apply.
apply/allP => n; rewrite mem_iota add0n /= => Hn.
have E : (n \in R) = (Ordinal Hn \in psl211_list_to_set R) by rewrite inE.
have E' : (n \in R') = (Ordinal Hn \in psl211_list_to_set R') by rewrite inE.
by rewrite E E' HR HR'.
Qed.

(* -------------------------------------------------------------------------- *)
(* The coordinate action of a shuffle on decks.                               *)
(* -------------------------------------------------------------------------- *)

(** psl211_heart_set_act — a shuffle moves the heart set of a deck by its
    inverse: re-dealing along g reads position i off position g i. *)
Lemma psl211_heart_set_act (g : pgg_gT psl211_M) (sh : 12.-tuple 'I_12) :
  psl211_heart_set [tuple tnth sh (@pgg_rho psl211_M g i) | i < 12]
  = (g^-1)%g @: psl211_heart_set sh.
Proof.
apply/setP => x; rewrite inE tnth_mktuple.
apply/idP/imsetP => [Hx | [y]].
  by exists (g x); [rewrite inE | rewrite permK].
by rewrite inE => Hy ->; rewrite permKV.
Qed.

(** psl211_orbit_class_invariant — the chirality bit survives every shuffle of
    the group. The shuffle re-deals the cards without changing the secret. *)
Lemma psl211_orbit_class_invariant (g : pgg_gT psl211_M)
    (sh : 12.-tuple 'I_12) :
  g \in pgg_G psl211_M ->
  psl211_orbit_class [tuple tnth sh (@pgg_rho psl211_M g i) | i < 12]
  = psl211_orbit_class sh.
Proof.
move=> gG; rewrite /psl211_orbit_class psl211_heart_set_act.
exact: (psl211_mirror_invariant _ _ (groupVr gG)).
Qed.

(** psl211_deck_stable — the coordinate action of a shuffle keeps the cards
    distinct, so a re-dealt arrangement is again a valid deck. *)
Lemma psl211_deck_stable (g : pgg_gT psl211_M) (sh : 12.-tuple 'I_12) :
  g \in pgg_G psl211_M ->
  psl211_deck_ok [tuple tnth sh (@pgg_rho psl211_M g i) | i < 12]
  = psl211_deck_ok sh.
Proof.
move=> _; rewrite /psl211_deck_ok; apply: perm_uniq.
rewrite (_ : [tuple tnth sh (@pgg_rho psl211_M g i) | i < 12]
           = [seq tnth sh (g i) | i <- enum 'I_12] :> seq _); last first.
  by apply: eq_map => i.
rewrite (map_comp (tnth sh) g (enum 'I_12)).
rewrite -[X in perm_eq _ X](map_tnth_enum sh).
apply: perm_map; apply: uniq_perm.
- by rewrite map_inj_uniq ?enum_uniq //; exact: perm_inj.
- exact: enum_uniq.
- move=> x; rewrite mem_enum; apply/mapP.
  by exists ((g^-1)%g x); [rewrite mem_enum | rewrite permKV].
Qed.

(* -------------------------------------------------------------------------- *)
(* Encoders: a distinct-card deck of each chirality.                          *)
(* -------------------------------------------------------------------------- *)

(* vm_compute cannot reduce enum 'I_12, so every ground fact about a mktuple
   deck goes through the literal enumeration, as pgl27_orbit.v does at eight
   positions. *)
Local Definition ord12_enum : seq 'I_12 :=
  [:: @Ordinal 12 0 isT; @Ordinal 12 1 isT; @Ordinal 12 2 isT;
      @Ordinal 12 3 isT; @Ordinal 12 4 isT; @Ordinal 12 5 isT;
      @Ordinal 12 6 isT; @Ordinal 12 7 isT; @Ordinal 12 8 isT;
      @Ordinal 12 9 isT; @Ordinal 12 10 isT; @Ordinal 12 11 isT].

Local Lemma enum_ord12 : enum 'I_12 = ord12_enum.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(* Position to card for the two representative decks, as twelve-entry tables:
   the heart codes 0..5 ascend along the representative row, the club codes
   6..11 ascend along its complement. *)
Local Definition hexad_deck_tbl : seq nat :=
  [:: 0; 1; 6; 2; 7; 8; 9; 3; 10; 11; 4; 5].
Local Definition mirror_deck_tbl : seq nat :=
  [:: 6; 7; 0; 1; 8; 2; 9; 3; 4; 5; 10; 11].

(* Ordinal in 'I_12 from a natural number, by reduction modulo twelve. *)
Local Definition Imod (k : nat) : 'I_12 := Ordinal (ltn_pmod k (ltn0Sn 11)).

(** psl211_rep_list — the representative row of each Steiner system: the
    mirror row [2;3;5;7;8;9] at true, the hexad row [0;1;3;7;10;11] at
    false. *)
Definition psl211_rep_list (b : bool) : seq nat :=
  if b then [:: 2; 3; 5; 7; 8; 9] else [:: 0; 1; 3; 7; 10; 11].

(** psl211_orbit_encode — a deck whose heart positions are the representative
    row of the system b names. The encoder dealing a chosen chirality. *)
Definition psl211_orbit_encode (b : bool) : 12.-tuple 'I_12 :=
  [tuple Imod (nth 0 (if b then mirror_deck_tbl else hexad_deck_tbl) i)
  | i < 12].

(** psl211_orbit_encode_deck — every encoded arrangement deals twelve distinct
    cards. *)
Lemma psl211_orbit_encode_deck (b : bool) :
  psl211_deck_ok (psl211_orbit_encode b).
Proof.
by case: b; rewrite /psl211_deck_ok /psl211_orbit_encode /= enum_ord12;
   vm_compute.
Qed.

(** psl211_encode_heart_setE — the heart positions of the encoded deck of
    chirality b are exactly the representative row of the system b names. *)
Lemma psl211_encode_heart_setE (b : bool) :
  psl211_heart_set (psl211_orbit_encode b)
  = psl211_list_to_set (psl211_rep_list b).
Proof.
apply/setP => i; rewrite !inE tnth_mktuple.
by case: b; case: i => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ascending code lists of six positions, and the census machinery.           *)
(* -------------------------------------------------------------------------- *)

(** psl211_asc6 — L is a strictly ascending six-list of codes below twelve,
    the code form of a six-subset of the twelve positions. *)
Definition psl211_asc6 (L : seq nat) : bool :=
  [&& sorted ltn L, all (fun n => (n < 12)%N) L & size L == 6].

(* The 924 strictly ascending six-lists of codes below twelve. *)
Local Definition sorted6 : seq (seq nat) := [::
  [:: 0; 1; 2; 3; 4; 5]; [:: 0; 1; 2; 3; 4; 6]; [:: 0; 1; 2; 3; 4; 7];
  [:: 0; 1; 2; 3; 4; 8]; [:: 0; 1; 2; 3; 4; 9]; [:: 0; 1; 2; 3; 4; 10];
  [:: 0; 1; 2; 3; 4; 11]; [:: 0; 1; 2; 3; 5; 6]; [:: 0; 1; 2; 3; 5; 7];
  [:: 0; 1; 2; 3; 5; 8]; [:: 0; 1; 2; 3; 5; 9]; [:: 0; 1; 2; 3; 5; 10];
  [:: 0; 1; 2; 3; 5; 11]; [:: 0; 1; 2; 3; 6; 7]; [:: 0; 1; 2; 3; 6; 8];
  [:: 0; 1; 2; 3; 6; 9]; [:: 0; 1; 2; 3; 6; 10]; [:: 0; 1; 2; 3; 6; 11];
  [:: 0; 1; 2; 3; 7; 8]; [:: 0; 1; 2; 3; 7; 9]; [:: 0; 1; 2; 3; 7; 10];
  [:: 0; 1; 2; 3; 7; 11]; [:: 0; 1; 2; 3; 8; 9]; [:: 0; 1; 2; 3; 8; 10];
  [:: 0; 1; 2; 3; 8; 11]; [:: 0; 1; 2; 3; 9; 10]; [:: 0; 1; 2; 3; 9; 11];
  [:: 0; 1; 2; 3; 10; 11]; [:: 0; 1; 2; 4; 5; 6]; [:: 0; 1; 2; 4; 5; 7];
  [:: 0; 1; 2; 4; 5; 8]; [:: 0; 1; 2; 4; 5; 9]; [:: 0; 1; 2; 4; 5; 10];
  [:: 0; 1; 2; 4; 5; 11]; [:: 0; 1; 2; 4; 6; 7]; [:: 0; 1; 2; 4; 6; 8];
  [:: 0; 1; 2; 4; 6; 9]; [:: 0; 1; 2; 4; 6; 10]; [:: 0; 1; 2; 4; 6; 11];
  [:: 0; 1; 2; 4; 7; 8]; [:: 0; 1; 2; 4; 7; 9]; [:: 0; 1; 2; 4; 7; 10];
  [:: 0; 1; 2; 4; 7; 11]; [:: 0; 1; 2; 4; 8; 9]; [:: 0; 1; 2; 4; 8; 10];
  [:: 0; 1; 2; 4; 8; 11]; [:: 0; 1; 2; 4; 9; 10]; [:: 0; 1; 2; 4; 9; 11];
  [:: 0; 1; 2; 4; 10; 11]; [:: 0; 1; 2; 5; 6; 7]; [:: 0; 1; 2; 5; 6; 8];
  [:: 0; 1; 2; 5; 6; 9]; [:: 0; 1; 2; 5; 6; 10]; [:: 0; 1; 2; 5; 6; 11];
  [:: 0; 1; 2; 5; 7; 8]; [:: 0; 1; 2; 5; 7; 9]; [:: 0; 1; 2; 5; 7; 10];
  [:: 0; 1; 2; 5; 7; 11]; [:: 0; 1; 2; 5; 8; 9]; [:: 0; 1; 2; 5; 8; 10];
  [:: 0; 1; 2; 5; 8; 11]; [:: 0; 1; 2; 5; 9; 10]; [:: 0; 1; 2; 5; 9; 11];
  [:: 0; 1; 2; 5; 10; 11]; [:: 0; 1; 2; 6; 7; 8]; [:: 0; 1; 2; 6; 7; 9];
  [:: 0; 1; 2; 6; 7; 10]; [:: 0; 1; 2; 6; 7; 11]; [:: 0; 1; 2; 6; 8; 9];
  [:: 0; 1; 2; 6; 8; 10]; [:: 0; 1; 2; 6; 8; 11]; [:: 0; 1; 2; 6; 9; 10];
  [:: 0; 1; 2; 6; 9; 11]; [:: 0; 1; 2; 6; 10; 11]; [:: 0; 1; 2; 7; 8; 9];
  [:: 0; 1; 2; 7; 8; 10]; [:: 0; 1; 2; 7; 8; 11]; [:: 0; 1; 2; 7; 9; 10];
  [:: 0; 1; 2; 7; 9; 11]; [:: 0; 1; 2; 7; 10; 11]; [:: 0; 1; 2; 8; 9; 10];
  [:: 0; 1; 2; 8; 9; 11]; [:: 0; 1; 2; 8; 10; 11]; [:: 0; 1; 2; 9; 10; 11];
  [:: 0; 1; 3; 4; 5; 6]; [:: 0; 1; 3; 4; 5; 7]; [:: 0; 1; 3; 4; 5; 8];
  [:: 0; 1; 3; 4; 5; 9]; [:: 0; 1; 3; 4; 5; 10]; [:: 0; 1; 3; 4; 5; 11];
  [:: 0; 1; 3; 4; 6; 7]; [:: 0; 1; 3; 4; 6; 8]; [:: 0; 1; 3; 4; 6; 9];
  [:: 0; 1; 3; 4; 6; 10]; [:: 0; 1; 3; 4; 6; 11]; [:: 0; 1; 3; 4; 7; 8];
  [:: 0; 1; 3; 4; 7; 9]; [:: 0; 1; 3; 4; 7; 10]; [:: 0; 1; 3; 4; 7; 11];
  [:: 0; 1; 3; 4; 8; 9]; [:: 0; 1; 3; 4; 8; 10]; [:: 0; 1; 3; 4; 8; 11];
  [:: 0; 1; 3; 4; 9; 10]; [:: 0; 1; 3; 4; 9; 11]; [:: 0; 1; 3; 4; 10; 11];
  [:: 0; 1; 3; 5; 6; 7]; [:: 0; 1; 3; 5; 6; 8]; [:: 0; 1; 3; 5; 6; 9];
  [:: 0; 1; 3; 5; 6; 10]; [:: 0; 1; 3; 5; 6; 11]; [:: 0; 1; 3; 5; 7; 8];
  [:: 0; 1; 3; 5; 7; 9]; [:: 0; 1; 3; 5; 7; 10]; [:: 0; 1; 3; 5; 7; 11];
  [:: 0; 1; 3; 5; 8; 9]; [:: 0; 1; 3; 5; 8; 10]; [:: 0; 1; 3; 5; 8; 11];
  [:: 0; 1; 3; 5; 9; 10]; [:: 0; 1; 3; 5; 9; 11]; [:: 0; 1; 3; 5; 10; 11];
  [:: 0; 1; 3; 6; 7; 8]; [:: 0; 1; 3; 6; 7; 9]; [:: 0; 1; 3; 6; 7; 10];
  [:: 0; 1; 3; 6; 7; 11]; [:: 0; 1; 3; 6; 8; 9]; [:: 0; 1; 3; 6; 8; 10];
  [:: 0; 1; 3; 6; 8; 11]; [:: 0; 1; 3; 6; 9; 10]; [:: 0; 1; 3; 6; 9; 11];
  [:: 0; 1; 3; 6; 10; 11]; [:: 0; 1; 3; 7; 8; 9]; [:: 0; 1; 3; 7; 8; 10];
  [:: 0; 1; 3; 7; 8; 11]; [:: 0; 1; 3; 7; 9; 10]; [:: 0; 1; 3; 7; 9; 11];
  [:: 0; 1; 3; 7; 10; 11]; [:: 0; 1; 3; 8; 9; 10]; [:: 0; 1; 3; 8; 9; 11];
  [:: 0; 1; 3; 8; 10; 11]; [:: 0; 1; 3; 9; 10; 11]; [:: 0; 1; 4; 5; 6; 7];
  [:: 0; 1; 4; 5; 6; 8]; [:: 0; 1; 4; 5; 6; 9]; [:: 0; 1; 4; 5; 6; 10];
  [:: 0; 1; 4; 5; 6; 11]; [:: 0; 1; 4; 5; 7; 8]; [:: 0; 1; 4; 5; 7; 9];
  [:: 0; 1; 4; 5; 7; 10]; [:: 0; 1; 4; 5; 7; 11]; [:: 0; 1; 4; 5; 8; 9];
  [:: 0; 1; 4; 5; 8; 10]; [:: 0; 1; 4; 5; 8; 11]; [:: 0; 1; 4; 5; 9; 10];
  [:: 0; 1; 4; 5; 9; 11]; [:: 0; 1; 4; 5; 10; 11]; [:: 0; 1; 4; 6; 7; 8];
  [:: 0; 1; 4; 6; 7; 9]; [:: 0; 1; 4; 6; 7; 10]; [:: 0; 1; 4; 6; 7; 11];
  [:: 0; 1; 4; 6; 8; 9]; [:: 0; 1; 4; 6; 8; 10]; [:: 0; 1; 4; 6; 8; 11];
  [:: 0; 1; 4; 6; 9; 10]; [:: 0; 1; 4; 6; 9; 11]; [:: 0; 1; 4; 6; 10; 11];
  [:: 0; 1; 4; 7; 8; 9]; [:: 0; 1; 4; 7; 8; 10]; [:: 0; 1; 4; 7; 8; 11];
  [:: 0; 1; 4; 7; 9; 10]; [:: 0; 1; 4; 7; 9; 11]; [:: 0; 1; 4; 7; 10; 11];
  [:: 0; 1; 4; 8; 9; 10]; [:: 0; 1; 4; 8; 9; 11]; [:: 0; 1; 4; 8; 10; 11];
  [:: 0; 1; 4; 9; 10; 11]; [:: 0; 1; 5; 6; 7; 8]; [:: 0; 1; 5; 6; 7; 9];
  [:: 0; 1; 5; 6; 7; 10]; [:: 0; 1; 5; 6; 7; 11]; [:: 0; 1; 5; 6; 8; 9];
  [:: 0; 1; 5; 6; 8; 10]; [:: 0; 1; 5; 6; 8; 11]; [:: 0; 1; 5; 6; 9; 10];
  [:: 0; 1; 5; 6; 9; 11]; [:: 0; 1; 5; 6; 10; 11]; [:: 0; 1; 5; 7; 8; 9];
  [:: 0; 1; 5; 7; 8; 10]; [:: 0; 1; 5; 7; 8; 11]; [:: 0; 1; 5; 7; 9; 10];
  [:: 0; 1; 5; 7; 9; 11]; [:: 0; 1; 5; 7; 10; 11]; [:: 0; 1; 5; 8; 9; 10];
  [:: 0; 1; 5; 8; 9; 11]; [:: 0; 1; 5; 8; 10; 11]; [:: 0; 1; 5; 9; 10; 11];
  [:: 0; 1; 6; 7; 8; 9]; [:: 0; 1; 6; 7; 8; 10]; [:: 0; 1; 6; 7; 8; 11];
  [:: 0; 1; 6; 7; 9; 10]; [:: 0; 1; 6; 7; 9; 11]; [:: 0; 1; 6; 7; 10; 11];
  [:: 0; 1; 6; 8; 9; 10]; [:: 0; 1; 6; 8; 9; 11]; [:: 0; 1; 6; 8; 10; 11];
  [:: 0; 1; 6; 9; 10; 11]; [:: 0; 1; 7; 8; 9; 10]; [:: 0; 1; 7; 8; 9; 11];
  [:: 0; 1; 7; 8; 10; 11]; [:: 0; 1; 7; 9; 10; 11]; [:: 0; 1; 8; 9; 10; 11];
  [:: 0; 2; 3; 4; 5; 6]; [:: 0; 2; 3; 4; 5; 7]; [:: 0; 2; 3; 4; 5; 8];
  [:: 0; 2; 3; 4; 5; 9]; [:: 0; 2; 3; 4; 5; 10]; [:: 0; 2; 3; 4; 5; 11];
  [:: 0; 2; 3; 4; 6; 7]; [:: 0; 2; 3; 4; 6; 8]; [:: 0; 2; 3; 4; 6; 9];
  [:: 0; 2; 3; 4; 6; 10]; [:: 0; 2; 3; 4; 6; 11]; [:: 0; 2; 3; 4; 7; 8];
  [:: 0; 2; 3; 4; 7; 9]; [:: 0; 2; 3; 4; 7; 10]; [:: 0; 2; 3; 4; 7; 11];
  [:: 0; 2; 3; 4; 8; 9]; [:: 0; 2; 3; 4; 8; 10]; [:: 0; 2; 3; 4; 8; 11];
  [:: 0; 2; 3; 4; 9; 10]; [:: 0; 2; 3; 4; 9; 11]; [:: 0; 2; 3; 4; 10; 11];
  [:: 0; 2; 3; 5; 6; 7]; [:: 0; 2; 3; 5; 6; 8]; [:: 0; 2; 3; 5; 6; 9];
  [:: 0; 2; 3; 5; 6; 10]; [:: 0; 2; 3; 5; 6; 11]; [:: 0; 2; 3; 5; 7; 8];
  [:: 0; 2; 3; 5; 7; 9]; [:: 0; 2; 3; 5; 7; 10]; [:: 0; 2; 3; 5; 7; 11];
  [:: 0; 2; 3; 5; 8; 9]; [:: 0; 2; 3; 5; 8; 10]; [:: 0; 2; 3; 5; 8; 11];
  [:: 0; 2; 3; 5; 9; 10]; [:: 0; 2; 3; 5; 9; 11]; [:: 0; 2; 3; 5; 10; 11];
  [:: 0; 2; 3; 6; 7; 8]; [:: 0; 2; 3; 6; 7; 9]; [:: 0; 2; 3; 6; 7; 10];
  [:: 0; 2; 3; 6; 7; 11]; [:: 0; 2; 3; 6; 8; 9]; [:: 0; 2; 3; 6; 8; 10];
  [:: 0; 2; 3; 6; 8; 11]; [:: 0; 2; 3; 6; 9; 10]; [:: 0; 2; 3; 6; 9; 11];
  [:: 0; 2; 3; 6; 10; 11]; [:: 0; 2; 3; 7; 8; 9]; [:: 0; 2; 3; 7; 8; 10];
  [:: 0; 2; 3; 7; 8; 11]; [:: 0; 2; 3; 7; 9; 10]; [:: 0; 2; 3; 7; 9; 11];
  [:: 0; 2; 3; 7; 10; 11]; [:: 0; 2; 3; 8; 9; 10]; [:: 0; 2; 3; 8; 9; 11];
  [:: 0; 2; 3; 8; 10; 11]; [:: 0; 2; 3; 9; 10; 11]; [:: 0; 2; 4; 5; 6; 7];
  [:: 0; 2; 4; 5; 6; 8]; [:: 0; 2; 4; 5; 6; 9]; [:: 0; 2; 4; 5; 6; 10];
  [:: 0; 2; 4; 5; 6; 11]; [:: 0; 2; 4; 5; 7; 8]; [:: 0; 2; 4; 5; 7; 9];
  [:: 0; 2; 4; 5; 7; 10]; [:: 0; 2; 4; 5; 7; 11]; [:: 0; 2; 4; 5; 8; 9];
  [:: 0; 2; 4; 5; 8; 10]; [:: 0; 2; 4; 5; 8; 11]; [:: 0; 2; 4; 5; 9; 10];
  [:: 0; 2; 4; 5; 9; 11]; [:: 0; 2; 4; 5; 10; 11]; [:: 0; 2; 4; 6; 7; 8];
  [:: 0; 2; 4; 6; 7; 9]; [:: 0; 2; 4; 6; 7; 10]; [:: 0; 2; 4; 6; 7; 11];
  [:: 0; 2; 4; 6; 8; 9]; [:: 0; 2; 4; 6; 8; 10]; [:: 0; 2; 4; 6; 8; 11];
  [:: 0; 2; 4; 6; 9; 10]; [:: 0; 2; 4; 6; 9; 11]; [:: 0; 2; 4; 6; 10; 11];
  [:: 0; 2; 4; 7; 8; 9]; [:: 0; 2; 4; 7; 8; 10]; [:: 0; 2; 4; 7; 8; 11];
  [:: 0; 2; 4; 7; 9; 10]; [:: 0; 2; 4; 7; 9; 11]; [:: 0; 2; 4; 7; 10; 11];
  [:: 0; 2; 4; 8; 9; 10]; [:: 0; 2; 4; 8; 9; 11]; [:: 0; 2; 4; 8; 10; 11];
  [:: 0; 2; 4; 9; 10; 11]; [:: 0; 2; 5; 6; 7; 8]; [:: 0; 2; 5; 6; 7; 9];
  [:: 0; 2; 5; 6; 7; 10]; [:: 0; 2; 5; 6; 7; 11]; [:: 0; 2; 5; 6; 8; 9];
  [:: 0; 2; 5; 6; 8; 10]; [:: 0; 2; 5; 6; 8; 11]; [:: 0; 2; 5; 6; 9; 10];
  [:: 0; 2; 5; 6; 9; 11]; [:: 0; 2; 5; 6; 10; 11]; [:: 0; 2; 5; 7; 8; 9];
  [:: 0; 2; 5; 7; 8; 10]; [:: 0; 2; 5; 7; 8; 11]; [:: 0; 2; 5; 7; 9; 10];
  [:: 0; 2; 5; 7; 9; 11]; [:: 0; 2; 5; 7; 10; 11]; [:: 0; 2; 5; 8; 9; 10];
  [:: 0; 2; 5; 8; 9; 11]; [:: 0; 2; 5; 8; 10; 11]; [:: 0; 2; 5; 9; 10; 11];
  [:: 0; 2; 6; 7; 8; 9]; [:: 0; 2; 6; 7; 8; 10]; [:: 0; 2; 6; 7; 8; 11];
  [:: 0; 2; 6; 7; 9; 10]; [:: 0; 2; 6; 7; 9; 11]; [:: 0; 2; 6; 7; 10; 11];
  [:: 0; 2; 6; 8; 9; 10]; [:: 0; 2; 6; 8; 9; 11]; [:: 0; 2; 6; 8; 10; 11];
  [:: 0; 2; 6; 9; 10; 11]; [:: 0; 2; 7; 8; 9; 10]; [:: 0; 2; 7; 8; 9; 11];
  [:: 0; 2; 7; 8; 10; 11]; [:: 0; 2; 7; 9; 10; 11]; [:: 0; 2; 8; 9; 10; 11];
  [:: 0; 3; 4; 5; 6; 7]; [:: 0; 3; 4; 5; 6; 8]; [:: 0; 3; 4; 5; 6; 9];
  [:: 0; 3; 4; 5; 6; 10]; [:: 0; 3; 4; 5; 6; 11]; [:: 0; 3; 4; 5; 7; 8];
  [:: 0; 3; 4; 5; 7; 9]; [:: 0; 3; 4; 5; 7; 10]; [:: 0; 3; 4; 5; 7; 11];
  [:: 0; 3; 4; 5; 8; 9]; [:: 0; 3; 4; 5; 8; 10]; [:: 0; 3; 4; 5; 8; 11];
  [:: 0; 3; 4; 5; 9; 10]; [:: 0; 3; 4; 5; 9; 11]; [:: 0; 3; 4; 5; 10; 11];
  [:: 0; 3; 4; 6; 7; 8]; [:: 0; 3; 4; 6; 7; 9]; [:: 0; 3; 4; 6; 7; 10];
  [:: 0; 3; 4; 6; 7; 11]; [:: 0; 3; 4; 6; 8; 9]; [:: 0; 3; 4; 6; 8; 10];
  [:: 0; 3; 4; 6; 8; 11]; [:: 0; 3; 4; 6; 9; 10]; [:: 0; 3; 4; 6; 9; 11];
  [:: 0; 3; 4; 6; 10; 11]; [:: 0; 3; 4; 7; 8; 9]; [:: 0; 3; 4; 7; 8; 10];
  [:: 0; 3; 4; 7; 8; 11]; [:: 0; 3; 4; 7; 9; 10]; [:: 0; 3; 4; 7; 9; 11];
  [:: 0; 3; 4; 7; 10; 11]; [:: 0; 3; 4; 8; 9; 10]; [:: 0; 3; 4; 8; 9; 11];
  [:: 0; 3; 4; 8; 10; 11]; [:: 0; 3; 4; 9; 10; 11]; [:: 0; 3; 5; 6; 7; 8];
  [:: 0; 3; 5; 6; 7; 9]; [:: 0; 3; 5; 6; 7; 10]; [:: 0; 3; 5; 6; 7; 11];
  [:: 0; 3; 5; 6; 8; 9]; [:: 0; 3; 5; 6; 8; 10]; [:: 0; 3; 5; 6; 8; 11];
  [:: 0; 3; 5; 6; 9; 10]; [:: 0; 3; 5; 6; 9; 11]; [:: 0; 3; 5; 6; 10; 11];
  [:: 0; 3; 5; 7; 8; 9]; [:: 0; 3; 5; 7; 8; 10]; [:: 0; 3; 5; 7; 8; 11];
  [:: 0; 3; 5; 7; 9; 10]; [:: 0; 3; 5; 7; 9; 11]; [:: 0; 3; 5; 7; 10; 11];
  [:: 0; 3; 5; 8; 9; 10]; [:: 0; 3; 5; 8; 9; 11]; [:: 0; 3; 5; 8; 10; 11];
  [:: 0; 3; 5; 9; 10; 11]; [:: 0; 3; 6; 7; 8; 9]; [:: 0; 3; 6; 7; 8; 10];
  [:: 0; 3; 6; 7; 8; 11]; [:: 0; 3; 6; 7; 9; 10]; [:: 0; 3; 6; 7; 9; 11];
  [:: 0; 3; 6; 7; 10; 11]; [:: 0; 3; 6; 8; 9; 10]; [:: 0; 3; 6; 8; 9; 11];
  [:: 0; 3; 6; 8; 10; 11]; [:: 0; 3; 6; 9; 10; 11]; [:: 0; 3; 7; 8; 9; 10];
  [:: 0; 3; 7; 8; 9; 11]; [:: 0; 3; 7; 8; 10; 11]; [:: 0; 3; 7; 9; 10; 11];
  [:: 0; 3; 8; 9; 10; 11]; [:: 0; 4; 5; 6; 7; 8]; [:: 0; 4; 5; 6; 7; 9];
  [:: 0; 4; 5; 6; 7; 10]; [:: 0; 4; 5; 6; 7; 11]; [:: 0; 4; 5; 6; 8; 9];
  [:: 0; 4; 5; 6; 8; 10]; [:: 0; 4; 5; 6; 8; 11]; [:: 0; 4; 5; 6; 9; 10];
  [:: 0; 4; 5; 6; 9; 11]; [:: 0; 4; 5; 6; 10; 11]; [:: 0; 4; 5; 7; 8; 9];
  [:: 0; 4; 5; 7; 8; 10]; [:: 0; 4; 5; 7; 8; 11]; [:: 0; 4; 5; 7; 9; 10];
  [:: 0; 4; 5; 7; 9; 11]; [:: 0; 4; 5; 7; 10; 11]; [:: 0; 4; 5; 8; 9; 10];
  [:: 0; 4; 5; 8; 9; 11]; [:: 0; 4; 5; 8; 10; 11]; [:: 0; 4; 5; 9; 10; 11];
  [:: 0; 4; 6; 7; 8; 9]; [:: 0; 4; 6; 7; 8; 10]; [:: 0; 4; 6; 7; 8; 11];
  [:: 0; 4; 6; 7; 9; 10]; [:: 0; 4; 6; 7; 9; 11]; [:: 0; 4; 6; 7; 10; 11];
  [:: 0; 4; 6; 8; 9; 10]; [:: 0; 4; 6; 8; 9; 11]; [:: 0; 4; 6; 8; 10; 11];
  [:: 0; 4; 6; 9; 10; 11]; [:: 0; 4; 7; 8; 9; 10]; [:: 0; 4; 7; 8; 9; 11];
  [:: 0; 4; 7; 8; 10; 11]; [:: 0; 4; 7; 9; 10; 11]; [:: 0; 4; 8; 9; 10; 11];
  [:: 0; 5; 6; 7; 8; 9]; [:: 0; 5; 6; 7; 8; 10]; [:: 0; 5; 6; 7; 8; 11];
  [:: 0; 5; 6; 7; 9; 10]; [:: 0; 5; 6; 7; 9; 11]; [:: 0; 5; 6; 7; 10; 11];
  [:: 0; 5; 6; 8; 9; 10]; [:: 0; 5; 6; 8; 9; 11]; [:: 0; 5; 6; 8; 10; 11];
  [:: 0; 5; 6; 9; 10; 11]; [:: 0; 5; 7; 8; 9; 10]; [:: 0; 5; 7; 8; 9; 11];
  [:: 0; 5; 7; 8; 10; 11]; [:: 0; 5; 7; 9; 10; 11]; [:: 0; 5; 8; 9; 10; 11];
  [:: 0; 6; 7; 8; 9; 10]; [:: 0; 6; 7; 8; 9; 11]; [:: 0; 6; 7; 8; 10; 11];
  [:: 0; 6; 7; 9; 10; 11]; [:: 0; 6; 8; 9; 10; 11]; [:: 0; 7; 8; 9; 10; 11];
  [:: 1; 2; 3; 4; 5; 6]; [:: 1; 2; 3; 4; 5; 7]; [:: 1; 2; 3; 4; 5; 8];
  [:: 1; 2; 3; 4; 5; 9]; [:: 1; 2; 3; 4; 5; 10]; [:: 1; 2; 3; 4; 5; 11];
  [:: 1; 2; 3; 4; 6; 7]; [:: 1; 2; 3; 4; 6; 8]; [:: 1; 2; 3; 4; 6; 9];
  [:: 1; 2; 3; 4; 6; 10]; [:: 1; 2; 3; 4; 6; 11]; [:: 1; 2; 3; 4; 7; 8];
  [:: 1; 2; 3; 4; 7; 9]; [:: 1; 2; 3; 4; 7; 10]; [:: 1; 2; 3; 4; 7; 11];
  [:: 1; 2; 3; 4; 8; 9]; [:: 1; 2; 3; 4; 8; 10]; [:: 1; 2; 3; 4; 8; 11];
  [:: 1; 2; 3; 4; 9; 10]; [:: 1; 2; 3; 4; 9; 11]; [:: 1; 2; 3; 4; 10; 11];
  [:: 1; 2; 3; 5; 6; 7]; [:: 1; 2; 3; 5; 6; 8]; [:: 1; 2; 3; 5; 6; 9];
  [:: 1; 2; 3; 5; 6; 10]; [:: 1; 2; 3; 5; 6; 11]; [:: 1; 2; 3; 5; 7; 8];
  [:: 1; 2; 3; 5; 7; 9]; [:: 1; 2; 3; 5; 7; 10]; [:: 1; 2; 3; 5; 7; 11];
  [:: 1; 2; 3; 5; 8; 9]; [:: 1; 2; 3; 5; 8; 10]; [:: 1; 2; 3; 5; 8; 11];
  [:: 1; 2; 3; 5; 9; 10]; [:: 1; 2; 3; 5; 9; 11]; [:: 1; 2; 3; 5; 10; 11];
  [:: 1; 2; 3; 6; 7; 8]; [:: 1; 2; 3; 6; 7; 9]; [:: 1; 2; 3; 6; 7; 10];
  [:: 1; 2; 3; 6; 7; 11]; [:: 1; 2; 3; 6; 8; 9]; [:: 1; 2; 3; 6; 8; 10];
  [:: 1; 2; 3; 6; 8; 11]; [:: 1; 2; 3; 6; 9; 10]; [:: 1; 2; 3; 6; 9; 11];
  [:: 1; 2; 3; 6; 10; 11]; [:: 1; 2; 3; 7; 8; 9]; [:: 1; 2; 3; 7; 8; 10];
  [:: 1; 2; 3; 7; 8; 11]; [:: 1; 2; 3; 7; 9; 10]; [:: 1; 2; 3; 7; 9; 11];
  [:: 1; 2; 3; 7; 10; 11]; [:: 1; 2; 3; 8; 9; 10]; [:: 1; 2; 3; 8; 9; 11];
  [:: 1; 2; 3; 8; 10; 11]; [:: 1; 2; 3; 9; 10; 11]; [:: 1; 2; 4; 5; 6; 7];
  [:: 1; 2; 4; 5; 6; 8]; [:: 1; 2; 4; 5; 6; 9]; [:: 1; 2; 4; 5; 6; 10];
  [:: 1; 2; 4; 5; 6; 11]; [:: 1; 2; 4; 5; 7; 8]; [:: 1; 2; 4; 5; 7; 9];
  [:: 1; 2; 4; 5; 7; 10]; [:: 1; 2; 4; 5; 7; 11]; [:: 1; 2; 4; 5; 8; 9];
  [:: 1; 2; 4; 5; 8; 10]; [:: 1; 2; 4; 5; 8; 11]; [:: 1; 2; 4; 5; 9; 10];
  [:: 1; 2; 4; 5; 9; 11]; [:: 1; 2; 4; 5; 10; 11]; [:: 1; 2; 4; 6; 7; 8];
  [:: 1; 2; 4; 6; 7; 9]; [:: 1; 2; 4; 6; 7; 10]; [:: 1; 2; 4; 6; 7; 11];
  [:: 1; 2; 4; 6; 8; 9]; [:: 1; 2; 4; 6; 8; 10]; [:: 1; 2; 4; 6; 8; 11];
  [:: 1; 2; 4; 6; 9; 10]; [:: 1; 2; 4; 6; 9; 11]; [:: 1; 2; 4; 6; 10; 11];
  [:: 1; 2; 4; 7; 8; 9]; [:: 1; 2; 4; 7; 8; 10]; [:: 1; 2; 4; 7; 8; 11];
  [:: 1; 2; 4; 7; 9; 10]; [:: 1; 2; 4; 7; 9; 11]; [:: 1; 2; 4; 7; 10; 11];
  [:: 1; 2; 4; 8; 9; 10]; [:: 1; 2; 4; 8; 9; 11]; [:: 1; 2; 4; 8; 10; 11];
  [:: 1; 2; 4; 9; 10; 11]; [:: 1; 2; 5; 6; 7; 8]; [:: 1; 2; 5; 6; 7; 9];
  [:: 1; 2; 5; 6; 7; 10]; [:: 1; 2; 5; 6; 7; 11]; [:: 1; 2; 5; 6; 8; 9];
  [:: 1; 2; 5; 6; 8; 10]; [:: 1; 2; 5; 6; 8; 11]; [:: 1; 2; 5; 6; 9; 10];
  [:: 1; 2; 5; 6; 9; 11]; [:: 1; 2; 5; 6; 10; 11]; [:: 1; 2; 5; 7; 8; 9];
  [:: 1; 2; 5; 7; 8; 10]; [:: 1; 2; 5; 7; 8; 11]; [:: 1; 2; 5; 7; 9; 10];
  [:: 1; 2; 5; 7; 9; 11]; [:: 1; 2; 5; 7; 10; 11]; [:: 1; 2; 5; 8; 9; 10];
  [:: 1; 2; 5; 8; 9; 11]; [:: 1; 2; 5; 8; 10; 11]; [:: 1; 2; 5; 9; 10; 11];
  [:: 1; 2; 6; 7; 8; 9]; [:: 1; 2; 6; 7; 8; 10]; [:: 1; 2; 6; 7; 8; 11];
  [:: 1; 2; 6; 7; 9; 10]; [:: 1; 2; 6; 7; 9; 11]; [:: 1; 2; 6; 7; 10; 11];
  [:: 1; 2; 6; 8; 9; 10]; [:: 1; 2; 6; 8; 9; 11]; [:: 1; 2; 6; 8; 10; 11];
  [:: 1; 2; 6; 9; 10; 11]; [:: 1; 2; 7; 8; 9; 10]; [:: 1; 2; 7; 8; 9; 11];
  [:: 1; 2; 7; 8; 10; 11]; [:: 1; 2; 7; 9; 10; 11]; [:: 1; 2; 8; 9; 10; 11];
  [:: 1; 3; 4; 5; 6; 7]; [:: 1; 3; 4; 5; 6; 8]; [:: 1; 3; 4; 5; 6; 9];
  [:: 1; 3; 4; 5; 6; 10]; [:: 1; 3; 4; 5; 6; 11]; [:: 1; 3; 4; 5; 7; 8];
  [:: 1; 3; 4; 5; 7; 9]; [:: 1; 3; 4; 5; 7; 10]; [:: 1; 3; 4; 5; 7; 11];
  [:: 1; 3; 4; 5; 8; 9]; [:: 1; 3; 4; 5; 8; 10]; [:: 1; 3; 4; 5; 8; 11];
  [:: 1; 3; 4; 5; 9; 10]; [:: 1; 3; 4; 5; 9; 11]; [:: 1; 3; 4; 5; 10; 11];
  [:: 1; 3; 4; 6; 7; 8]; [:: 1; 3; 4; 6; 7; 9]; [:: 1; 3; 4; 6; 7; 10];
  [:: 1; 3; 4; 6; 7; 11]; [:: 1; 3; 4; 6; 8; 9]; [:: 1; 3; 4; 6; 8; 10];
  [:: 1; 3; 4; 6; 8; 11]; [:: 1; 3; 4; 6; 9; 10]; [:: 1; 3; 4; 6; 9; 11];
  [:: 1; 3; 4; 6; 10; 11]; [:: 1; 3; 4; 7; 8; 9]; [:: 1; 3; 4; 7; 8; 10];
  [:: 1; 3; 4; 7; 8; 11]; [:: 1; 3; 4; 7; 9; 10]; [:: 1; 3; 4; 7; 9; 11];
  [:: 1; 3; 4; 7; 10; 11]; [:: 1; 3; 4; 8; 9; 10]; [:: 1; 3; 4; 8; 9; 11];
  [:: 1; 3; 4; 8; 10; 11]; [:: 1; 3; 4; 9; 10; 11]; [:: 1; 3; 5; 6; 7; 8];
  [:: 1; 3; 5; 6; 7; 9]; [:: 1; 3; 5; 6; 7; 10]; [:: 1; 3; 5; 6; 7; 11];
  [:: 1; 3; 5; 6; 8; 9]; [:: 1; 3; 5; 6; 8; 10]; [:: 1; 3; 5; 6; 8; 11];
  [:: 1; 3; 5; 6; 9; 10]; [:: 1; 3; 5; 6; 9; 11]; [:: 1; 3; 5; 6; 10; 11];
  [:: 1; 3; 5; 7; 8; 9]; [:: 1; 3; 5; 7; 8; 10]; [:: 1; 3; 5; 7; 8; 11];
  [:: 1; 3; 5; 7; 9; 10]; [:: 1; 3; 5; 7; 9; 11]; [:: 1; 3; 5; 7; 10; 11];
  [:: 1; 3; 5; 8; 9; 10]; [:: 1; 3; 5; 8; 9; 11]; [:: 1; 3; 5; 8; 10; 11];
  [:: 1; 3; 5; 9; 10; 11]; [:: 1; 3; 6; 7; 8; 9]; [:: 1; 3; 6; 7; 8; 10];
  [:: 1; 3; 6; 7; 8; 11]; [:: 1; 3; 6; 7; 9; 10]; [:: 1; 3; 6; 7; 9; 11];
  [:: 1; 3; 6; 7; 10; 11]; [:: 1; 3; 6; 8; 9; 10]; [:: 1; 3; 6; 8; 9; 11];
  [:: 1; 3; 6; 8; 10; 11]; [:: 1; 3; 6; 9; 10; 11]; [:: 1; 3; 7; 8; 9; 10];
  [:: 1; 3; 7; 8; 9; 11]; [:: 1; 3; 7; 8; 10; 11]; [:: 1; 3; 7; 9; 10; 11];
  [:: 1; 3; 8; 9; 10; 11]; [:: 1; 4; 5; 6; 7; 8]; [:: 1; 4; 5; 6; 7; 9];
  [:: 1; 4; 5; 6; 7; 10]; [:: 1; 4; 5; 6; 7; 11]; [:: 1; 4; 5; 6; 8; 9];
  [:: 1; 4; 5; 6; 8; 10]; [:: 1; 4; 5; 6; 8; 11]; [:: 1; 4; 5; 6; 9; 10];
  [:: 1; 4; 5; 6; 9; 11]; [:: 1; 4; 5; 6; 10; 11]; [:: 1; 4; 5; 7; 8; 9];
  [:: 1; 4; 5; 7; 8; 10]; [:: 1; 4; 5; 7; 8; 11]; [:: 1; 4; 5; 7; 9; 10];
  [:: 1; 4; 5; 7; 9; 11]; [:: 1; 4; 5; 7; 10; 11]; [:: 1; 4; 5; 8; 9; 10];
  [:: 1; 4; 5; 8; 9; 11]; [:: 1; 4; 5; 8; 10; 11]; [:: 1; 4; 5; 9; 10; 11];
  [:: 1; 4; 6; 7; 8; 9]; [:: 1; 4; 6; 7; 8; 10]; [:: 1; 4; 6; 7; 8; 11];
  [:: 1; 4; 6; 7; 9; 10]; [:: 1; 4; 6; 7; 9; 11]; [:: 1; 4; 6; 7; 10; 11];
  [:: 1; 4; 6; 8; 9; 10]; [:: 1; 4; 6; 8; 9; 11]; [:: 1; 4; 6; 8; 10; 11];
  [:: 1; 4; 6; 9; 10; 11]; [:: 1; 4; 7; 8; 9; 10]; [:: 1; 4; 7; 8; 9; 11];
  [:: 1; 4; 7; 8; 10; 11]; [:: 1; 4; 7; 9; 10; 11]; [:: 1; 4; 8; 9; 10; 11];
  [:: 1; 5; 6; 7; 8; 9]; [:: 1; 5; 6; 7; 8; 10]; [:: 1; 5; 6; 7; 8; 11];
  [:: 1; 5; 6; 7; 9; 10]; [:: 1; 5; 6; 7; 9; 11]; [:: 1; 5; 6; 7; 10; 11];
  [:: 1; 5; 6; 8; 9; 10]; [:: 1; 5; 6; 8; 9; 11]; [:: 1; 5; 6; 8; 10; 11];
  [:: 1; 5; 6; 9; 10; 11]; [:: 1; 5; 7; 8; 9; 10]; [:: 1; 5; 7; 8; 9; 11];
  [:: 1; 5; 7; 8; 10; 11]; [:: 1; 5; 7; 9; 10; 11]; [:: 1; 5; 8; 9; 10; 11];
  [:: 1; 6; 7; 8; 9; 10]; [:: 1; 6; 7; 8; 9; 11]; [:: 1; 6; 7; 8; 10; 11];
  [:: 1; 6; 7; 9; 10; 11]; [:: 1; 6; 8; 9; 10; 11]; [:: 1; 7; 8; 9; 10; 11];
  [:: 2; 3; 4; 5; 6; 7]; [:: 2; 3; 4; 5; 6; 8]; [:: 2; 3; 4; 5; 6; 9];
  [:: 2; 3; 4; 5; 6; 10]; [:: 2; 3; 4; 5; 6; 11]; [:: 2; 3; 4; 5; 7; 8];
  [:: 2; 3; 4; 5; 7; 9]; [:: 2; 3; 4; 5; 7; 10]; [:: 2; 3; 4; 5; 7; 11];
  [:: 2; 3; 4; 5; 8; 9]; [:: 2; 3; 4; 5; 8; 10]; [:: 2; 3; 4; 5; 8; 11];
  [:: 2; 3; 4; 5; 9; 10]; [:: 2; 3; 4; 5; 9; 11]; [:: 2; 3; 4; 5; 10; 11];
  [:: 2; 3; 4; 6; 7; 8]; [:: 2; 3; 4; 6; 7; 9]; [:: 2; 3; 4; 6; 7; 10];
  [:: 2; 3; 4; 6; 7; 11]; [:: 2; 3; 4; 6; 8; 9]; [:: 2; 3; 4; 6; 8; 10];
  [:: 2; 3; 4; 6; 8; 11]; [:: 2; 3; 4; 6; 9; 10]; [:: 2; 3; 4; 6; 9; 11];
  [:: 2; 3; 4; 6; 10; 11]; [:: 2; 3; 4; 7; 8; 9]; [:: 2; 3; 4; 7; 8; 10];
  [:: 2; 3; 4; 7; 8; 11]; [:: 2; 3; 4; 7; 9; 10]; [:: 2; 3; 4; 7; 9; 11];
  [:: 2; 3; 4; 7; 10; 11]; [:: 2; 3; 4; 8; 9; 10]; [:: 2; 3; 4; 8; 9; 11];
  [:: 2; 3; 4; 8; 10; 11]; [:: 2; 3; 4; 9; 10; 11]; [:: 2; 3; 5; 6; 7; 8];
  [:: 2; 3; 5; 6; 7; 9]; [:: 2; 3; 5; 6; 7; 10]; [:: 2; 3; 5; 6; 7; 11];
  [:: 2; 3; 5; 6; 8; 9]; [:: 2; 3; 5; 6; 8; 10]; [:: 2; 3; 5; 6; 8; 11];
  [:: 2; 3; 5; 6; 9; 10]; [:: 2; 3; 5; 6; 9; 11]; [:: 2; 3; 5; 6; 10; 11];
  [:: 2; 3; 5; 7; 8; 9]; [:: 2; 3; 5; 7; 8; 10]; [:: 2; 3; 5; 7; 8; 11];
  [:: 2; 3; 5; 7; 9; 10]; [:: 2; 3; 5; 7; 9; 11]; [:: 2; 3; 5; 7; 10; 11];
  [:: 2; 3; 5; 8; 9; 10]; [:: 2; 3; 5; 8; 9; 11]; [:: 2; 3; 5; 8; 10; 11];
  [:: 2; 3; 5; 9; 10; 11]; [:: 2; 3; 6; 7; 8; 9]; [:: 2; 3; 6; 7; 8; 10];
  [:: 2; 3; 6; 7; 8; 11]; [:: 2; 3; 6; 7; 9; 10]; [:: 2; 3; 6; 7; 9; 11];
  [:: 2; 3; 6; 7; 10; 11]; [:: 2; 3; 6; 8; 9; 10]; [:: 2; 3; 6; 8; 9; 11];
  [:: 2; 3; 6; 8; 10; 11]; [:: 2; 3; 6; 9; 10; 11]; [:: 2; 3; 7; 8; 9; 10];
  [:: 2; 3; 7; 8; 9; 11]; [:: 2; 3; 7; 8; 10; 11]; [:: 2; 3; 7; 9; 10; 11];
  [:: 2; 3; 8; 9; 10; 11]; [:: 2; 4; 5; 6; 7; 8]; [:: 2; 4; 5; 6; 7; 9];
  [:: 2; 4; 5; 6; 7; 10]; [:: 2; 4; 5; 6; 7; 11]; [:: 2; 4; 5; 6; 8; 9];
  [:: 2; 4; 5; 6; 8; 10]; [:: 2; 4; 5; 6; 8; 11]; [:: 2; 4; 5; 6; 9; 10];
  [:: 2; 4; 5; 6; 9; 11]; [:: 2; 4; 5; 6; 10; 11]; [:: 2; 4; 5; 7; 8; 9];
  [:: 2; 4; 5; 7; 8; 10]; [:: 2; 4; 5; 7; 8; 11]; [:: 2; 4; 5; 7; 9; 10];
  [:: 2; 4; 5; 7; 9; 11]; [:: 2; 4; 5; 7; 10; 11]; [:: 2; 4; 5; 8; 9; 10];
  [:: 2; 4; 5; 8; 9; 11]; [:: 2; 4; 5; 8; 10; 11]; [:: 2; 4; 5; 9; 10; 11];
  [:: 2; 4; 6; 7; 8; 9]; [:: 2; 4; 6; 7; 8; 10]; [:: 2; 4; 6; 7; 8; 11];
  [:: 2; 4; 6; 7; 9; 10]; [:: 2; 4; 6; 7; 9; 11]; [:: 2; 4; 6; 7; 10; 11];
  [:: 2; 4; 6; 8; 9; 10]; [:: 2; 4; 6; 8; 9; 11]; [:: 2; 4; 6; 8; 10; 11];
  [:: 2; 4; 6; 9; 10; 11]; [:: 2; 4; 7; 8; 9; 10]; [:: 2; 4; 7; 8; 9; 11];
  [:: 2; 4; 7; 8; 10; 11]; [:: 2; 4; 7; 9; 10; 11]; [:: 2; 4; 8; 9; 10; 11];
  [:: 2; 5; 6; 7; 8; 9]; [:: 2; 5; 6; 7; 8; 10]; [:: 2; 5; 6; 7; 8; 11];
  [:: 2; 5; 6; 7; 9; 10]; [:: 2; 5; 6; 7; 9; 11]; [:: 2; 5; 6; 7; 10; 11];
  [:: 2; 5; 6; 8; 9; 10]; [:: 2; 5; 6; 8; 9; 11]; [:: 2; 5; 6; 8; 10; 11];
  [:: 2; 5; 6; 9; 10; 11]; [:: 2; 5; 7; 8; 9; 10]; [:: 2; 5; 7; 8; 9; 11];
  [:: 2; 5; 7; 8; 10; 11]; [:: 2; 5; 7; 9; 10; 11]; [:: 2; 5; 8; 9; 10; 11];
  [:: 2; 6; 7; 8; 9; 10]; [:: 2; 6; 7; 8; 9; 11]; [:: 2; 6; 7; 8; 10; 11];
  [:: 2; 6; 7; 9; 10; 11]; [:: 2; 6; 8; 9; 10; 11]; [:: 2; 7; 8; 9; 10; 11];
  [:: 3; 4; 5; 6; 7; 8]; [:: 3; 4; 5; 6; 7; 9]; [:: 3; 4; 5; 6; 7; 10];
  [:: 3; 4; 5; 6; 7; 11]; [:: 3; 4; 5; 6; 8; 9]; [:: 3; 4; 5; 6; 8; 10];
  [:: 3; 4; 5; 6; 8; 11]; [:: 3; 4; 5; 6; 9; 10]; [:: 3; 4; 5; 6; 9; 11];
  [:: 3; 4; 5; 6; 10; 11]; [:: 3; 4; 5; 7; 8; 9]; [:: 3; 4; 5; 7; 8; 10];
  [:: 3; 4; 5; 7; 8; 11]; [:: 3; 4; 5; 7; 9; 10]; [:: 3; 4; 5; 7; 9; 11];
  [:: 3; 4; 5; 7; 10; 11]; [:: 3; 4; 5; 8; 9; 10]; [:: 3; 4; 5; 8; 9; 11];
  [:: 3; 4; 5; 8; 10; 11]; [:: 3; 4; 5; 9; 10; 11]; [:: 3; 4; 6; 7; 8; 9];
  [:: 3; 4; 6; 7; 8; 10]; [:: 3; 4; 6; 7; 8; 11]; [:: 3; 4; 6; 7; 9; 10];
  [:: 3; 4; 6; 7; 9; 11]; [:: 3; 4; 6; 7; 10; 11]; [:: 3; 4; 6; 8; 9; 10];
  [:: 3; 4; 6; 8; 9; 11]; [:: 3; 4; 6; 8; 10; 11]; [:: 3; 4; 6; 9; 10; 11];
  [:: 3; 4; 7; 8; 9; 10]; [:: 3; 4; 7; 8; 9; 11]; [:: 3; 4; 7; 8; 10; 11];
  [:: 3; 4; 7; 9; 10; 11]; [:: 3; 4; 8; 9; 10; 11]; [:: 3; 5; 6; 7; 8; 9];
  [:: 3; 5; 6; 7; 8; 10]; [:: 3; 5; 6; 7; 8; 11]; [:: 3; 5; 6; 7; 9; 10];
  [:: 3; 5; 6; 7; 9; 11]; [:: 3; 5; 6; 7; 10; 11]; [:: 3; 5; 6; 8; 9; 10];
  [:: 3; 5; 6; 8; 9; 11]; [:: 3; 5; 6; 8; 10; 11]; [:: 3; 5; 6; 9; 10; 11];
  [:: 3; 5; 7; 8; 9; 10]; [:: 3; 5; 7; 8; 9; 11]; [:: 3; 5; 7; 8; 10; 11];
  [:: 3; 5; 7; 9; 10; 11]; [:: 3; 5; 8; 9; 10; 11]; [:: 3; 6; 7; 8; 9; 10];
  [:: 3; 6; 7; 8; 9; 11]; [:: 3; 6; 7; 8; 10; 11]; [:: 3; 6; 7; 9; 10; 11];
  [:: 3; 6; 8; 9; 10; 11]; [:: 3; 7; 8; 9; 10; 11]; [:: 4; 5; 6; 7; 8; 9];
  [:: 4; 5; 6; 7; 8; 10]; [:: 4; 5; 6; 7; 8; 11]; [:: 4; 5; 6; 7; 9; 10];
  [:: 4; 5; 6; 7; 9; 11]; [:: 4; 5; 6; 7; 10; 11]; [:: 4; 5; 6; 8; 9; 10];
  [:: 4; 5; 6; 8; 9; 11]; [:: 4; 5; 6; 8; 10; 11]; [:: 4; 5; 6; 9; 10; 11];
  [:: 4; 5; 7; 8; 9; 10]; [:: 4; 5; 7; 8; 9; 11]; [:: 4; 5; 7; 8; 10; 11];
  [:: 4; 5; 7; 9; 10; 11]; [:: 4; 5; 8; 9; 10; 11]; [:: 4; 6; 7; 8; 9; 10];
  [:: 4; 6; 7; 8; 9; 11]; [:: 4; 6; 7; 8; 10; 11]; [:: 4; 6; 7; 9; 10; 11];
  [:: 4; 6; 8; 9; 10; 11]; [:: 4; 7; 8; 9; 10; 11]; [:: 5; 6; 7; 8; 9; 10];
  [:: 5; 6; 7; 8; 9; 11]; [:: 5; 6; 7; 8; 10; 11]; [:: 5; 6; 7; 9; 10; 11];
  [:: 5; 6; 8; 9; 10; 11]; [:: 5; 7; 8; 9; 10; 11]; [:: 6; 7; 8; 9; 10; 11]].

(* The same 924 lists, generated place by place; the shape the completeness
   proof of pgl27_orbit.v runs on. *)
Local Definition sorted6_gen : seq (seq nat) :=
  flatten [seq flatten [seq flatten [seq flatten [seq flatten
    [seq [seq [:: a; b; c; d; e; f] | f <- iota e.+1 (12 - e.+1)]
    | e <- iota d.+1 (12 - d.+1)]
    | d <- iota c.+1 (12 - c.+1)]
    | c <- iota b.+1 (12 - b.+1)]
    | b <- iota a.+1 (12 - a.+1)]
    | a <- iota 0 12].

Local Lemma sorted6E : sorted6 = sorted6_gen.
Proof. by vm_compute. Qed.

(* sorted6 lists no code six-tuple twice. *)
Local Lemma sorted6_uniq : uniq sorted6.
Proof. by vm_compute. Qed.

(* Every element of sorted6 is a strictly ascending six-list below twelve. *)
Local Lemma sorted6_asc : all psl211_asc6 sorted6.
Proof. by vm_compute. Qed.

(* sorted6 enumerates every strictly ascending six-list below twelve. *)
Local Lemma sorted6_complete (L : seq nat) : psl211_asc6 L -> L \in sorted6.
Proof.
rewrite sorted6E.
case: L => [|a [|b [|c [|d [|e [|f [|g l]]]]]]] A //.
all: try by case/and3P: A => _ _ /eqP.
case/and3P: A => Hsort Hall _.
move: Hsort; rewrite /= => /andP[Hab /andP[Hbc /andP[Hcd /andP[Hde Hef]]]].
move: Hall => /= /andP[Ha /andP[Hb /andP[Hc /andP[Hd /andP[He /andP[Hf _]]]]]].
move: Hef; rewrite andbT => Hef.
apply/flatten_mapP; exists a; first by rewrite mem_iota add0n Ha.
apply/flatten_mapP; exists b; first by rewrite mem_iota (subnKC Ha) Hab Hb.
apply/flatten_mapP; exists c; first by rewrite mem_iota (subnKC Hb) Hbc Hc.
apply/flatten_mapP; exists d; first by rewrite mem_iota (subnKC Hc) Hcd Hd.
apply/flatten_mapP; exists e; first by rewrite mem_iota (subnKC Hd) Hde He.
apply/mapP; exists f; first by rewrite mem_iota (subnKC He) Hef Hf.
by [].
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

(* psl211_list_to_set is a section of the code list of the enumeration. *)
Local Lemma list_to_setK (S : {set 'I_12}) :
  psl211_list_to_set (map val (enum S)) = S.
Proof.
by apply/setP => i; rewrite /psl211_list_to_set inE (mem_map val_inj) mem_enum.
Qed.

(* The code list of psl211_list_to_set L permutes L for ascending L. *)
Local Lemma perm_list_to_set (L : seq nat) :
  sorted ltn L -> all (fun n => (n < 12)%N) L ->
  perm_eq (map val (enum (psl211_list_to_set L))) L.
Proof.
move=> Hsort Hall.
apply: uniq_perm.
- rewrite (map_inj_uniq val_inj); exact: enum_uniq.
- exact: (sorted_uniq ltn_trans ltnn Hsort).
- move=> n; apply/mapP/idP => [[i Hi ->]|Hn];
    first by move: Hi; rewrite mem_enum inE.
  have Hn12 : (n < 12)%N by move/allP: Hall => /(_ n Hn).
  by exists (Ordinal Hn12); [rewrite mem_enum inE|].
Qed.
Arguments perm_list_to_set [L].

(** psl211_block_card6 — an ascending six-list codes a six-element set of
    positions: a block of either Steiner system has six positions. *)
Lemma psl211_block_card6 (L : seq nat) :
  psl211_asc6 L -> #|psl211_list_to_set L| = 6.
Proof.
move=> A; rewrite cardE -(size_map val (enum (psl211_list_to_set L))).
case/and3P: (A) => Hs Hl /eqP Hsz.
by rewrite (perm_size (perm_list_to_set Hs Hl)).
Qed.

(* psl211_list_to_set is injective on strictly ascending code lists. *)
Local Lemma list_to_set_inj (L1 L2 : seq nat) :
  sorted ltn L1 -> all (fun n => (n < 12)%N) L1 ->
  sorted ltn L2 -> all (fun n => (n < 12)%N) L2 ->
  psl211_list_to_set L1 = psl211_list_to_set L2 -> L1 = L2.
Proof.
move=> S1 A1 S2 A2 Heq; apply: (irr_sorted_eq ltn_trans ltnn) => //.
move=> n; rewrite -(perm_mem (perm_list_to_set S1 A1)) Heq.
by rewrite (perm_mem (perm_list_to_set S2 A2)).
Qed.
Arguments list_to_set_inj [L1 L2].

(* A census of the six-subsets runs at the code level over any complete,
   repetition-free enumeration s of the ascending six-lists.  The
   enumeration is a parameter rather than sorted6 itself: unifying eq_card
   against the 924-row literal does not terminate in usable time. *)
Local Lemma class_count (s : seq (seq nat)) (p : {set 'I_12} -> bool)
    (pn : seq nat -> bool) :
  uniq s -> all psl211_asc6 s -> (forall L, psl211_asc6 L -> L \in s) ->
  (forall L, psl211_asc6 L -> p (psl211_list_to_set L) = pn L) ->
  #|[set S : {set 'I_12} | (#|S| == 6) && p S]| = count pn s.
Proof.
move=> Hu Hasc Hcomp Hp.
have key : forall S : {set 'I_12}, #|S| = 6 -> psl211_asc6 (map val (enum S)).
  move=> S HcS; rewrite /psl211_asc6 sorted_val_enum /=; apply/andP; split.
    by apply/allP => n /mapP[i _ ->]; exact: ltn_ord.
  by rewrite size_map -cardE HcS.
have Huniq : uniq [seq psl211_list_to_set L | L <- filter pn s].
  rewrite map_inj_in_uniq; last first.
    move=> L1 L2; rewrite !mem_filter => /andP[_ H1] /andP[_ H2].
    have /and3P[S1 A1 _] := allP Hasc _ H1.
    have /and3P[S2 A2 _] := allP Hasc _ H2.
    exact: list_to_set_inj.
  by rewrite filter_uniq.
have Hmem : [set S : {set 'I_12} | (#|S| == 6) && p S]
              =i [seq psl211_list_to_set L | L <- filter pn s].
  move=> S; rewrite inE; apply/idP/idP.
    move=> /andP[/eqP HcS HpS]; apply/mapP.
    exists (map val (enum S)); last by rewrite list_to_setK.
    rewrite mem_filter (Hcomp _ (key S HcS)) andbT.
    by rewrite -(Hp _ (key S HcS)) list_to_setK.
  move=> /mapP[L]; rewrite mem_filter => /andP[HpnL HinL] ->.
  have AL : psl211_asc6 L by apply: (allP Hasc).
  by rewrite (psl211_block_card6 L AL) eqxx (Hp _ AL).
rewrite (eq_card Hmem).
transitivity (size [seq psl211_list_to_set L | L <- filter pn s]).
  by apply/card_uniqP.
by rewrite size_map size_filter.
Qed.

(* Both tables list ascending six-rows, without repetition. *)
Local Lemma asc6_mirrorT : all psl211_asc6 psl211_mirror_tbl.
Proof. by vm_compute. Qed.

Local Lemma asc6_hexadT : all psl211_asc6 psl211_hexad_tbl.
Proof. by vm_compute. Qed.

(** psl211_mirror_tbl_uniq — the mirror table lists its 132 blocks once
    each. *)
Lemma psl211_mirror_tbl_uniq : uniq psl211_mirror_tbl.
Proof. by vm_compute. Qed.

(** psl211_hexad_tbl_uniq — the hexad table lists its 132 blocks once each. *)
Lemma psl211_hexad_tbl_uniq : uniq psl211_hexad_tbl.
Proof. by vm_compute. Qed.

(* Membership in a coded family is membership of the code list in the table. *)
Local Lemma mem_sets_of (tbl : seq (seq nat)) (L : seq nat) :
  all psl211_asc6 tbl -> psl211_asc6 L ->
  (psl211_list_to_set L \in psl211_sets_of tbl) = (L \in tbl).
Proof.
move=> Htbl AL; rewrite inE; apply/hasP/idP => [[R Rt /eqP HR]|Lt].
  have /and3P[SR AR _] := allP Htbl _ Rt.
  case/and3P: AL => SL AL _.
  by rewrite -(list_to_set_inj SR AR SL AL HR).
by exists L.
Qed.
Arguments mem_sets_of [tbl L].

(* Each representative row is an ascending six-list. *)
Local Lemma asc6_rep (b : bool) : psl211_asc6 (psl211_rep_list b).
Proof. by case: b; vm_compute. Qed.

(** psl211_orbit_encodeK — the encoder is a section of the chirality
    classifier: it deals exactly the requested secret. *)
Lemma psl211_orbit_encodeK (b : bool) :
  psl211_orbit_class (psl211_orbit_encode b) = b.
Proof.
rewrite /psl211_orbit_class psl211_encode_heart_setE /psl211_subset_class.
rewrite /psl211_mirror_blocks (mem_sets_of asc6_mirrorT (asc6_rep b)).
by case: b; vm_compute.
Qed.

(** psl211_orbit_encode_valid_set — the heart set of an encoded deck is a
    block of one of the two Steiner systems. *)
Lemma psl211_orbit_encode_valid_set (b : bool) :
  psl211_subset_valid (psl211_heart_set (psl211_orbit_encode b)).
Proof.
rewrite /psl211_subset_valid psl211_encode_heart_setE.
rewrite /psl211_mirror_blocks /psl211_hexad_blocks.
rewrite (mem_sets_of asc6_mirrorT (asc6_rep b)).
rewrite (mem_sets_of asc6_hexadT (asc6_rep b)).
by case: b; vm_compute.
Qed.

(** psl211_orbit_populated — both chiralities occur among decks whose heart
    set is a block, so the secret space is covered by valid deals. *)
Lemma psl211_orbit_populated (b : bool) :
  exists sh, psl211_deck_ok sh
             /\ psl211_subset_valid (psl211_heart_set sh)
             /\ psl211_orbit_class sh = b.
Proof.
exists (psl211_orbit_encode b); split; first exact: psl211_orbit_encode_deck.
by split; [exact: psl211_orbit_encode_valid_set | exact: psl211_orbit_encodeK].
Qed.

(* -------------------------------------------------------------------------- *)
(* Block counts and the pattern census.                                       *)
(* -------------------------------------------------------------------------- *)

(* A coded family is carried by six-element sets only. *)
Local Lemma sets_of_card6 (tbl : seq (seq nat)) :
  all psl211_asc6 tbl ->
  psl211_sets_of tbl
    =i [set S : {set 'I_12} | (#|S| == 6) && (S \in psl211_sets_of tbl)].
Proof.
move=> Htbl S; apply/idP/idP.
  move=> HS; rewrite in_set HS andbT; move: HS.
  rewrite /psl211_sets_of in_set => /hasP[R Rt /eqP <-].
  by rewrite (psl211_block_card6 _ (allP Htbl _ Rt)).
by rewrite in_set => /andP[_ HS].
Qed.
Arguments sets_of_card6 [tbl].

(** psl211_card_mirror_blocks — the mirror Steiner system has 132 blocks, the
    orbit size of a six-subset under the shuffle group. *)
Lemma psl211_card_mirror_blocks : #|psl211_mirror_blocks| = 132.
Proof.
rewrite (eq_card (sets_of_card6 asc6_mirrorT)).
rewrite (class_count sorted6 (fun S => S \in psl211_sets_of psl211_mirror_tbl)
                     (fun L => L \in psl211_mirror_tbl)
                     sorted6_uniq sorted6_asc sorted6_complete); last first.
  by move=> L AL; exact: (mem_sets_of asc6_mirrorT AL).
by vm_compute.
Qed.

(** psl211_card_hexad_blocks — the hexad Steiner system has 132 blocks, the
    same orbit size. *)
Lemma psl211_card_hexad_blocks : #|psl211_hexad_blocks| = 132.
Proof.
rewrite (eq_card (sets_of_card6 asc6_hexadT)).
rewrite (class_count sorted6 (fun S => S \in psl211_sets_of psl211_hexad_tbl)
                     (fun L => L \in psl211_hexad_tbl)
                     sorted6_uniq sorted6_asc sorted6_complete); last first.
  by move=> L AL; exact: (mem_sets_of asc6_hexadT AL).
by vm_compute.
Qed.

(** psl211_pattern_countE — the number of blocks of a table meeting the
    coalition C in exactly A is the table-level count of psl211_blocks.v, so
    a leak census on position sets is a computation on code lists. *)
Lemma psl211_pattern_countE (tbl : seq (seq nat)) (C A : {set 'I_12}) :
  all psl211_asc6 tbl -> uniq tbl ->
  #|[set B in psl211_sets_of tbl | B :&: C == A]|
  = psl211_pattern_count tbl (map val (enum C)) (map val (enum A)).
Proof.
move=> Htbl Hu.
pose C' := map val (enum C); pose A' := map val (enum A).
pose p (R : seq nat) := psl211_inter R C' == A'.
have HmemC (x : 'I_12) : (val x \in C') = (x \in C).
  by rewrite /C' (mem_map val_inj) mem_enum.
have Hinter (R : seq nat) :
    psl211_list_to_set (psl211_inter R C') = psl211_list_to_set R :&: C.
  by apply/setP => x; rewrite !inE /psl211_inter mem_filter HmemC andbC.
have HA' : psl211_list_to_set A' = A by exact: list_to_setK.
have HascA' : sorted ltn A' /\ all (fun n => (n < 12)%N) A'.
  split; first exact: sorted_val_enum.
  by apply/allP => n /mapP[i _ ->]; exact: ltn_ord.
have Hasc (R : seq nat) : R \in tbl ->
    sorted ltn (psl211_inter R C')
    /\ all (fun n => (n < 12)%N) (psl211_inter R C').
  move=> Rt; have /and3P[SR AR _] := allP Htbl _ Rt; split.
    by apply: sorted_filter => // y x z; apply: ltn_trans.
  by apply/allP => n; rewrite mem_filter => /andP[_ /(allP AR)].
have Hrow (R : seq nat) : R \in tbl ->
    (psl211_list_to_set R :&: C == A) = p R.
  move=> Rt; have [S1 A1] := Hasc R Rt; have [S2 A2] := HascA'.
  apply/eqP/eqP => [HR|HR]; last by rewrite -Hinter HR HA'.
  by apply: (list_to_set_inj S1 A1 S2 A2); rewrite Hinter HA'.
have Huniq : uniq [seq psl211_list_to_set R | R <- filter p tbl].
  rewrite map_inj_in_uniq; last first.
    move=> L1 L2; rewrite !mem_filter => /andP[_ H1] /andP[_ H2].
    have /and3P[S1 A1 _] := allP Htbl _ H1.
    have /and3P[S2 A2 _] := allP Htbl _ H2.
    exact: list_to_set_inj.
  by rewrite filter_uniq.
have Hmem : [set B in psl211_sets_of tbl | B :&: C == A]
              =i [seq psl211_list_to_set R | R <- filter p tbl].
  move=> B; rewrite inE; apply/idP/idP.
    case/andP; rewrite inE => /hasP[R Rt /eqP HR] HB.
    apply/mapP; exists R; last by rewrite HR.
    by rewrite mem_filter Rt andbT -(Hrow R Rt) HR.
  case/mapP => R; rewrite mem_filter => /andP[HpR Rt] ->.
  rewrite (Hrow R Rt) HpR andbT inE.
  by apply/hasP; exists R.
rewrite (eq_card Hmem).
transitivity (size [seq psl211_list_to_set R | R <- filter p tbl]).
  by apply/card_uniqP.
by rewrite size_map size_filter.
Qed.

(* -------------------------------------------------------------------------- *)
(* Orbit certificate: a fueled BFS over the rows of each table.               *)
(* -------------------------------------------------------------------------- *)

(* One letter applied to a six-subset, in ascending canonical form. *)
Local Definition code_step (i : nat) (L : seq nat) : seq nat :=
  sort leq (map (psl211_wgenn i) L).

(* Fueled BFS over six-subsets, one carrying word per reached subset. *)
Local Fixpoint code_bfs (fuel : nat) (seen : seq (seq nat * seq nat)) :
    seq (seq nat * seq nat) :=
  match fuel with
  | 0 => seen
  | f.+1 =>
    let nxt := flatten
      [seq [seq (code_step i Lw.1, rcons Lw.2 i)
             | i <- [:: 0; 1]] | Lw <- seen] in
    let add := foldl (fun acc Lw =>
      if has (fun sw : seq nat * seq nat => sw.1 == Lw.1) (seen ++ acc)
      then acc else rcons acc Lw) [::] nxt in
    if nilp add then seen else code_bfs f (seen ++ add)
  end.

(* The BFS closure of the representative row of each system. *)
Local Definition code_table (b : bool) : seq (seq nat * seq nat) :=
  code_bfs 20 [:: (psl211_rep_list b, [::])].

(* Every row of the system carries a word from its representative row. The
   check recomputes each word from scratch, so a BFS bookkeeping error cannot
   make it true. *)
Local Definition code_table_ok (b : bool) : bool :=
  all (fun L => has (fun sw : seq nat * seq nat =>
                       sort leq (map (psl211_papply sw.2) (psl211_rep_list b))
                       == L)
                    (code_table b))
      (if b then psl211_mirror_tbl else psl211_hexad_tbl).

Local Lemma code_table_okP (b : bool) : code_table_ok b.
Proof. by case: b; vm_compute. Qed.

(* The same certificate with all at the head.  The allP view must not be
   asked to unfold code_table_ok: reducing code_table b outside the virtual
   machine does not terminate in usable time. *)
Local Lemma code_table_okA (b : bool) :
  all (fun L => has (fun sw : seq nat * seq nat =>
                       sort leq (map (psl211_papply sw.2) (psl211_rep_list b))
                       == L)
                    (code_table b))
      (if b then psl211_mirror_tbl else psl211_hexad_tbl).
Proof. exact: code_table_okP. Qed.

(* The image of a coded subset is coded by the word applied codewise. *)
Local Lemma psl211_word_perm_imset (w : seq nat) (L : seq nat) :
  all (fun n => (n < 12)%N) L ->
  psl211_word_perm w @: psl211_list_to_set L
  = psl211_list_to_set (map (psl211_papply w) L).
Proof.
move=> /allP HL; apply/setP => x; rewrite inE.
apply/imsetP/mapP => [[y]|[a aL Ha]].
  by rewrite inE => yL ->; exists (val y); rewrite // psl211_word_perm_val.
exists (Ordinal (HL a aL)); first by rewrite inE.
by apply/val_inj; rewrite psl211_word_perm_val.
Qed.
Arguments psl211_word_perm_imset w [L].

(* psl211_list_to_set reads membership only, so sorting is invisible to it. *)
Local Lemma list_to_set_sort (L : seq nat) :
  psl211_list_to_set (sort leq L) = psl211_list_to_set L.
Proof. by apply/setP => i; rewrite !inE mem_sort. Qed.

(* The set action of a shuffle is the image of the set under it. *)
Local Lemma setact_imset (g : {perm 'I_12}) (S : {set 'I_12}) :
  'P^*%act S g = g @: S.
Proof. by []. Qed.

(** psl211_mirror_orbitE — the mirror system is the shuffle orbit of its
    representative row: the group acts transitively on the 132 mirror
    blocks. *)
Lemma psl211_mirror_orbitE :
  orbit 'P^* (pgg_G psl211_M) (psl211_list_to_set (psl211_rep_list true))
  = psl211_mirror_blocks.
Proof.
have H12 : all (fun n => (n < 12)%N) (psl211_rep_list true) by vm_compute.
apply/setP => T; apply/orbitP/idP => [[g gG <-]|HT].
  rewrite setact_imset (psl211_mirror_invariant _ _ gG) /psl211_mirror_blocks.
  by rewrite (mem_sets_of asc6_mirrorT (asc6_rep true)); vm_compute.
move: HT; rewrite /psl211_mirror_blocks in_set => /hasP[R Rt /eqP <-].
move: (code_table_okA true) => /allP/(_ _ Rt)/hasP[sw _ /eqP Hw].
exists (psl211_word_perm sw.2); first exact: psl211_word_perm_mem.
by rewrite setact_imset (psl211_word_perm_imset sw.2 H12)
   -list_to_set_sort Hw.
Qed.

(** psl211_hexad_orbitE — the hexad system is the shuffle orbit of its
    representative row, the second orbit of the group on six-subsets. *)
Lemma psl211_hexad_orbitE :
  orbit 'P^* (pgg_G psl211_M) (psl211_list_to_set (psl211_rep_list false))
  = psl211_hexad_blocks.
Proof.
have H12 : all (fun n => (n < 12)%N) (psl211_rep_list false) by vm_compute.
apply/setP => T; apply/orbitP/idP => [[g gG <-]|HT].
  rewrite setact_imset (psl211_hexad_invariant _ _ gG) /psl211_hexad_blocks.
  by rewrite (mem_sets_of asc6_hexadT (asc6_rep false)); vm_compute.
move: HT; rewrite /psl211_hexad_blocks in_set => /hasP[R Rt /eqP <-].
move: (code_table_okA false) => /allP/(_ _ Rt)/hasP[sw _ /eqP Hw].
exists (psl211_word_perm sw.2); first exact: psl211_word_perm_mem.
by rewrite setact_imset (psl211_word_perm_imset sw.2 H12)
   -list_to_set_sort Hw.
Qed.
