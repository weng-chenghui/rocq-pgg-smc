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
Unset Printing Implicit Defensive.
Import Prenex Implicits.

(** The census and mixing tables contain the same permutation rows, possibly
    in different orders. Each row therefore denotes the same shuffle in both
    finite representations. *)
Lemma pgl27_group_table_perm :
  perm_eq pgl27_group_table (unzip1 pgl27_mixing.elem_table).
Proof. by vm_compute. Qed.

(** A valid census row lists eight distinct card positions below eight. This
    is the row condition needed to interpret a nat table as a permutation. *)
Definition pgl27_table_row_ok (t : seq nat) : bool :=
  [&& size t == 8, uniq t & all (fun x => x < 8) t].

(** Every census row has eight distinct entries below eight. Thus each row is
    the table of a permutation of the eight card positions. *)
Lemma pgl27_group_table_rows_ok :
  all pgl27_table_row_ok pgl27_group_table.
Proof. by vm_compute. Qed.

(** This malformed census row repeats its final card position. It witnesses
    that the row condition rejects a relation that is not a permutation. *)
Local Definition pgl27_bad_duplicate_row : seq nat :=
  [:: 0; 1; 2; 3; 4; 5; 6; 6].

(** The repeated final entry makes the malformed row fail the row condition.
    Thus distinctness is an effective part of the permutation bridge. *)
Local Lemma pgl27_bad_duplicate_rowN :
  ~~ pgl27_table_row_ok pgl27_bad_duplicate_row.
Proof. by vm_compute. Qed.

(** The mixing-table permutation indexed by the matching census row. This map
    turns census indices into elements of the shuffle permutation carrier. *)
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

(** The permutation assigned to an index has exactly the census row at that
    index as its table. This preserves the action of every card position. *)
Lemma pgl27_table_permE (k : 'I_336) :
  pgl27_mixing.ptbl (pgl27_table_perm k) =
  nth [::] pgl27_group_table k.
Proof.
rewrite /pgl27_table_perm
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

(** Swapping card positions three and four changes the encoded orbit class.
    It is therefore an explicit permutation outside the PGL shuffle group. *)
Local Definition pgl27_outside_perm : {perm 'I_8} :=
  tperm (@Ordinal 8 3 isT) (@Ordinal 8 4 isT).

(** The transposition of positions three and four is not a PGL shuffle. If it
    were available, a shuffle would change the bit carried by the orbit
    class. *)
Local Lemma pgl27_outside_permN :
  pgl27_outside_perm \notin pgg_G pgl27_M.
Proof.
apply/negP => outside_mem.
have class_invariant :=
  orbit_class_invariant pgl27_outside_perm (orbit_encode false) outside_mem.
have changed_deck :
    [tuple tnth (orbit_encode false)
       (@pgg_rho pgl27_M pgl27_outside_perm i) | i < 8] =
    orbit_encode true.
  apply: eq_from_tnth => i.
  rewrite tnth_mktuple.
  change (tnth (orbit_encode false) (pgl27_outside_perm i) =
    tnth (orbit_encode true) i).
  rewrite /pgl27_outside_perm.
  case: tpermP => [->|->|not_three not_four].
  - by vm_compute.
  - by vm_compute.
  - case: i not_three not_four =>
      -[|[|[|[|[|[|[|[|//]]]]]]]] i_lt not_three not_four.
    - by apply: val_inj.
    - by apply: val_inj.
    - by apply: val_inj.
    - exfalso; apply: not_three; apply: val_inj; by [].
    - exfalso; apply: not_four; apply: val_inj; by [].
    - by apply: val_inj.
    - by apply: val_inj.
    - by apply: val_inj.
by move: class_invariant; rewrite changed_deck !orbit_encodeK.
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
have Hgkey := pgl27_mixing.group_key gG.
have Heq :
    (pgl27_mixing.ptbl g \in pgl27_group_table) =
    (pgl27_mixing.ptbl g \in unzip1 pgl27_mixing.elem_table) :=
  perm_mem pgl27_group_table_perm _.
have Hgrow : pgl27_mixing.ptbl g \in pgl27_group_table.
  by rewrite Heq.
have Hklt : index (pgl27_mixing.ptbl g) pgl27_group_table < 336.
  have Hind : index (pgl27_mixing.ptbl g) pgl27_group_table <
      size pgl27_group_table.
    rewrite index_mem.
    exact: Hgrow.
  by move: Hind; rewrite pgl27_group_table_size.
pose k : 'I_336 := Ordinal Hklt.
have Hrow : nth [::] pgl27_group_table k = pgl27_mixing.ptbl g.
  change (nth [::] pgl27_group_table
    (index (pgl27_mixing.ptbl g) pgl27_group_table) =
    pgl27_mixing.ptbl g).
  exact: nth_index Hgrow.
exists k; apply: pgl27_mixing.ptbl_inj.
exact: (etrans (pgl27_table_permE k) Hrow).
Qed.

(** The nat-level deal table and the tuple-level encoder agree at every card
    position. Both representations therefore deal the same secret deck. *)
Lemma pgl27_code_deal_orbit_encodeE (b : bool) (i : 'I_8) :
  nth 0 (code_deal b) i = val (tnth (orbit_encode b) i).
Proof.
by case: b; case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi.
Qed.

(** This alternative deal swaps codes two and three instead of codes three
    and four. It represents a different encoding from the PGL orbit encoder. *)
Local Definition pgl27_changed_deal : seq nat :=
  [:: 0; 1; 3; 2; 4; 5; 6; 7].

(** The alternative deal disagrees with the true-secret orbit encoding at
    position two. The deal bridge therefore depends on the chosen code swap. *)
Local Lemma pgl27_changed_dealN :
  nth 0 pgl27_changed_deal (@Ordinal 8 2 isT) !=
  val (tnth (orbit_encode true) (@Ordinal 8 2 isT)).
Proof. by []. Qed.

(** Composing a permutation table with a deal table agrees with applying the
    permutation to the tuple-level encoded deck. Thus census composition and
    the protocol view use the same action convention. *)
Lemma pgl27_code_comp_ptblE (b : bool) (g : {perm 'I_8}) (t : seq nat)
    (Ht : pgl27_mixing.ptbl g = t) (i : 'I_8) :
  nth 0 (code_comp t (code_deal b)) i =
  val (tnth (orbit_encode b) (g i)).
Proof.
have Hsize : size t = 8 by rewrite -Ht pgl27_mixing.ptbl_size.
rewrite /code_comp (nth_map 0); last first.
  by rewrite Hsize; exact: ltn_ord i.
rewrite -Ht pgl27_mixing.ptbl_nth.
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

Print Assumptions pgl27_group_table_perm.
Print Assumptions pgl27_group_table_rows_ok.
Print Assumptions pgl27_bad_duplicate_rowN.
Print Assumptions pgl27_table_row_mem.
Print Assumptions pgl27_table_index_lt.
Print Assumptions pgl27_table_permE.
Print Assumptions pgl27_table_perm_mem.
Print Assumptions pgl27_outside_permN.
Print Assumptions pgl27_table_perm_inj.
Print Assumptions pgl27_table_perm_surj.
Print Assumptions pgl27_code_deal_orbit_encodeE.
Print Assumptions pgl27_changed_dealN.
Print Assumptions pgl27_code_comp_ptblE.
Print Assumptions pgl27_code_comp_rowE.
