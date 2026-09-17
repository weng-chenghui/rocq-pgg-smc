(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_table_bridge: the collision census rows as PGL(2,7) shuffles         *)
(*                                                                            *)
(* The collision census counts restricted views over a 336-row table of       *)
(* natural numbers, while the protocol shuffles with elements of              *)
(* pgg_G pgl27_M. This file identifies the two: every census row is the table *)
(* of a group element, distinct rows give distinct elements, every group      *)
(* element occurs as a row, and composing a row with the nat deal reproduces  *)
(* the encoded deck the protocol view reads. Every census count is therefore  *)
(* a count over the shuffle group itself.                                     *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_ptbl g == the permutation table of the shuffle g                   *)
(*   pgl27_table_perm k == the shuffle denoted by census row k                *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_group_card == the PGL(2,7) shuffle group has 336 elements          *)
(*   pgl27_ptbl_inj == distinct shuffles have distinct tables                 *)
(*   pgl27_ptbl_mem == the table of a PGL(2,7) shuffle is a census row        *)
(*   pgl27_table_perm_mem == every census row denotes a PGL(2,7) shuffle      *)
(*   pgl27_table_perm_inj == distinct census rows denote distinct shuffles    *)
(*   pgl27_table_perm_surj == every PGL(2,7) shuffle occurs as a census row   *)
(*   pgl27_code_comp_rowE == a census row and its shuffle produce the same    *)
(*     encoded card at every position                                         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From pgg_smc Require Import pgg_interface.
From pgg_smc Require Import pgl27_group pgl27_orbit.
From pgg_smc Require Import pgl27_leakage_census pgl27_mixing.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** The census and mixing tables contain the same permutation rows, possibly
    in different orders. Each row therefore denotes the same shuffle in both
    finite representations. *)
Lemma pgl27_group_table_perm :
  perm_eq pgl27_group_table (unzip1 pgl27_mixing.elem_table).
Proof. by vm_compute. Qed.

(** The permutation table of a shuffle: the images of the eight card
    positions, listed in position order. It is the form in which the census
    names a group element, so every count over census rows is a statement
    about shuffles once read along this map. *)
Definition pgl27_ptbl (g : {perm 'I_8}) : seq nat := pgl27_mixing.ptbl g.

(** Distinct shuffles have distinct tables. A census row therefore names at
    most one element of the shuffle group. *)
Lemma pgl27_ptbl_inj : injective pgl27_ptbl.
Proof. exact: pgl27_mixing.ptbl_inj. Qed.

(** The table of a PGL(2,7) shuffle occurs among the census rows. Every
    shuffle the protocol can draw is therefore already one of the 336
    executions the census enumerates. *)
Lemma pgl27_ptbl_mem (g : {perm 'I_8}) :
  g \in pgg_G pgl27_M -> pgl27_ptbl g \in pgl27_group_table.
Proof.
move=> gG; have Hgkey := pgl27_mixing.group_key gG.
have Heq :
    (pgl27_ptbl g \in pgl27_group_table) =
    (pgl27_ptbl g \in unzip1 pgl27_mixing.elem_table) :=
  perm_mem pgl27_group_table_perm _.
by rewrite Heq.
Qed.

(** The PGL(2,7) shuffle group has 336 elements. It is the number every
    census count is normalized by to become a probability. *)
Lemma pgl27_group_card : #|pgg_G pgl27_M| = 336.
Proof. exact: pgl27_mixing.pgl27_card. Qed.

(** The PGL(2,7) shuffle whose table is census row [k]. It is the map along
    which every count over the 336 census rows is read as a count over the
    shuffle group the protocol samples from. *)
Definition pgl27_table_perm (k : 'I_336) : {perm 'I_8} :=
  pgl27_mixing.entry_perm
    (index (nth [::] pgl27_group_table k)
       (unzip1 pgl27_mixing.elem_table)).

(** Every indexed census row occurs among the mixing enumeration keys. This
    gives each collision-table row a corresponding shuffle permutation. *)
Lemma pgl27_table_row_mem (k : 'I_336) :
  nth [::] pgl27_group_table k \in
    unzip1 pgl27_mixing.elem_table.
Proof.
have Hmem : nth [::] pgl27_group_table k \in pgl27_group_table.
  by apply: mem_nth; rewrite pgl27_group_table_size; exact: ltn_ord k.
have Heq :
    (nth [::] pgl27_group_table k \in pgl27_group_table) =
    (nth [::] pgl27_group_table k \in
       unzip1 pgl27_mixing.elem_table) :=
  perm_mem pgl27_group_table_perm _.
rewrite -Heq.
exact: Hmem.
Qed.

(** The matching mixing-table index of every census row lies below 336. Thus
    the associated permutation is one of the certified group entries. *)
Lemma pgl27_table_index_lt (k : 'I_336) :
  index (nth [::] pgl27_group_table k)
    (unzip1 pgl27_mixing.elem_table) < 336.
Proof.
have Hlt :
    index (nth [::] pgl27_group_table k)
      (unzip1 pgl27_mixing.elem_table) <
    size (unzip1 pgl27_mixing.elem_table).
  by rewrite index_mem pgl27_table_row_mem.
by move: Hlt; rewrite pgl27_mixing.keys_size.
Qed.

(** The shuffle named by census index [k] has census row [k] as its table.
    Row and shuffle therefore send each card position to the same place, so a
    statement proved about one transfers verbatim to the other. *)
Lemma pgl27_table_permE (k : 'I_336) :
  pgl27_ptbl (pgl27_table_perm k) =
  nth [::] pgl27_group_table k.
Proof.
rewrite /pgl27_ptbl /pgl27_table_perm
  (pgl27_mixing.ptbl_entry (pgl27_table_index_lt k)).
exact: nth_index (pgl27_table_row_mem k).
Qed.

(** Every permutation assigned to a census row belongs to the PGL shuffle
    group. Thus the table bridge never introduces an external permutation. *)
Lemma pgl27_table_perm_mem (k : 'I_336) :
  pgl27_table_perm k \in pgg_G pgl27_M.
Proof.
exact: pgl27_mixing.entry_perm_mem.
Qed.

(** Distinct census indices name distinct shuffle permutations. The 336-row
    enumeration therefore counts each shuffle at most once. *)
Lemma pgl27_table_perm_inj : injective pgl27_table_perm.
Proof.
move=> i j Hij; apply/val_inj; apply/eqP.
have Hi : i < size pgl27_group_table.
  by rewrite pgl27_group_table_size; exact: ltn_ord i.
have Hj : j < size pgl27_group_table.
  by rewrite pgl27_group_table_size; exact: ltn_ord j.
rewrite -(nth_uniq [::] Hi Hj pgl27_group_table_uniq).
apply/eqP.
by rewrite -(pgl27_table_permE i) -(pgl27_table_permE j) Hij.
Qed.

(** Every PGL shuffle is assigned to a census index. Together with
    injectivity, the census rows enumerate the shuffle group exactly once. *)
Lemma pgl27_table_perm_surj (g : {perm 'I_8}) :
  g \in pgg_G pgl27_M -> exists k : 'I_336, pgl27_table_perm k = g.
Proof.
move=> gG.
have Hgrow : pgl27_ptbl g \in pgl27_group_table := pgl27_ptbl_mem gG.
have Hklt : index (pgl27_ptbl g) pgl27_group_table < 336.
  have Hind : index (pgl27_ptbl g) pgl27_group_table <
      size pgl27_group_table.
    rewrite index_mem.
    exact: Hgrow.
  by move: Hind; rewrite pgl27_group_table_size.
pose k : 'I_336 := Ordinal Hklt.
have Hrow : nth [::] pgl27_group_table k = pgl27_ptbl g.
  change (nth [::] pgl27_group_table
    (index (pgl27_ptbl g) pgl27_group_table) =
    pgl27_ptbl g).
  exact: nth_index Hgrow.
exists k; apply: pgl27_ptbl_inj.
exact: (etrans (pgl27_table_permE k) Hrow).
Qed.

(** The nat-level deal table and the tuple-level encoder agree at every card
    position. Both representations therefore deal the same secret deck. *)
Lemma pgl27_code_deal_orbit_encodeE (b : bool) (i : 'I_8) :
  nth 0 (code_deal b) i = val (tnth (orbit_encode b) i).
Proof.
by case: b; case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi.
Qed.

(** Composing a permutation table with a deal table agrees with applying the
    permutation to the tuple-level encoded deck. Thus census composition and
    the protocol view use the same action convention. *)
Lemma pgl27_code_comp_ptblE (b : bool) (g : {perm 'I_8}) (t : seq nat)
    (Ht : pgl27_ptbl g = t) (i : 'I_8) :
  nth 0 (code_comp t (code_deal b)) i =
  val (tnth (orbit_encode b) (g i)).
Proof.
have Hsize : size t = 8 by rewrite -Ht /pgl27_ptbl pgl27_mixing.ptbl_size.
rewrite /code_comp (nth_map 0); last first.
  by rewrite Hsize; exact: ltn_ord i.
rewrite -Ht /pgl27_ptbl pgl27_mixing.ptbl_nth.
exact: pgl27_code_deal_orbit_encodeE.
Qed.

(** An indexed census row and its assigned shuffle give the same encoded card
    at every position. Thus restricted census views can be compared with the
    protocol's coalition view coordinate by coordinate. *)
Lemma pgl27_code_comp_rowE (b : bool) (k : 'I_336) (i : 'I_8) :
  nth 0
    (code_comp (nth [::] pgl27_group_table k) (code_deal b)) i =
  val (tnth (orbit_encode b) (pgl27_table_perm k i)).
Proof.
exact: (@pgl27_code_comp_ptblE b (pgl27_table_perm k)
  (nth [::] pgl27_group_table k) (pgl27_table_permE k) i).
Qed.
