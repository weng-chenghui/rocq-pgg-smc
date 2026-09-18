From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import action div bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface psl211_blocks psl211_group.
From pgg_smc Require Import psl211_closure psl211_alldecks.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Notation dealT := psl211_deal.
Local Notation cutT := (pgg_gT psl211_M).
Local Notation seatT := 'I_12.
Local Notation cardT := 'I_12.
Local Notation viewT := {ffun seatT -> cardT}.

(* Only raw nat data reduces here.  `inord` is `insubd ord0`, whose `insub`
   branches on the Qed-opaque `idP`, so `inord k` never becomes an `Ordinal`
   under vm_compute; measured 2026-09-18, `Eval vm_compute in val (inord 0)`
   returns a stuck `match idP with ...`.  Since `psl211_alldecks_seq` and
   every finfun or finset over 'I_12 go through `inord` or `ord_enum`, the
   counted term below names none of them: it is a `count` over the raw
   permutation tables, and the three lemmas psl_counter_seqE,
   psl_counter_raw_viewE and psl_counter_testP carry it back to the deck, the
   reading and the shuffle group symbolically. *)

(** psl_counter_deal — the deal that fixes the counterexample: block index
    zero of the class's table, with both labellings the identity. *)
Definition psl_counter_deal : dealT := (ord0, 1%g, 1%g).

(** psl_counter_coalition — the three seats 0, 1 and 2. *)
Definition psl_counter_coalition : {set seatT} :=
  [set i : seatT | val i \in [:: 0; 1; 2]].

(** psl_counter_view — the reading that gives cards 0, 1 and 5 to seats 0, 1
    and 2, and card 0 to every seat outside the coalition. *)
Definition psl_counter_view : viewT :=
  [ffun i => psl211_code12 (nth 0 [:: 0; 1; 5] (val i))].

(** psl_counter_seq b — the deck psl_counter_deal names in class b, as raw
    codes by position: a position of block zero carries its own rank in that
    block, and every other position carries six plus its rank in the
    complement, the identity labellings acting trivially. *)
Definition psl_counter_seq (b : bool) : seq nat :=
  let H := psl211_alldecks_row (b, psl_counter_deal) in
  let K := psl211_alldecks_corow (b, psl_counter_deal) in
  [seq (if p \in H then index p H else 6 + index p K) | p <- iota 0 12].

(** psl_counter_row_size — block zero of either class's table has six
    positions, the heart block of a Steiner sextet. *)
Lemma psl_counter_row_size (b : bool) :
  size (psl211_alldecks_row (b, psl_counter_deal)) = 6.
Proof. by case: b; vm_compute. Qed.

(** psl_counter_corow_size — its complement has the other six. *)
Lemma psl_counter_corow_size (b : bool) :
  size (psl211_alldecks_corow (b, psl_counter_deal)) = 6.
Proof. by case: b; vm_compute. Qed.

(** psl_counter_seqE — that raw list is the deck the all-decks dealer lays
    for this deal, so a count over raw codes is a count over dealt decks. *)
Lemma psl_counter_seqE (b : bool) :
  psl211_alldecks_seq (b, psl_counter_deal) = psl_counter_seq b.
Proof.
(* The two sides differ only by the identity labelling and the inord that
   names a rank: `\val (inord _)` is convertible to, but not syntactically,
   the `nat_of_ord (inord _)` that inordK keys on, so inordK is applied
   rather than rewritten with. *)
have Hrow := psl_counter_row_size b.
have Hcorow := psl_counter_corow_size b.
rewrite /psl_counter_deal in Hrow Hcorow.
rewrite /psl211_alldecks_seq /psl_counter_seq /psl_counter_deal.
apply/eq_in_map => p Hp.
case: ifP => Hin.
  rewrite perm1; apply: inordK.
  by rewrite -[X in _ < X]Hrow index_mem Hin.
rewrite perm1; apply/eqP; rewrite eqn_add2l; apply/eqP.
apply: inordK.
rewrite -[X in _ < X]Hcorow index_mem /psl211_alldecks_corow mem_filter.
by rewrite Hin Hp.
Qed.

(** psl_counter_raw_view sq t — the reading the coalition gets from the deck
    sq under the shuffle whose table is t, written on raw data. *)
Definition psl_counter_raw_view (sq t : seq nat) : viewT :=
  [ffun i => if val i \in [:: 0; 1; 2]
             then psl211_code12 (nth 0 sq (nth 0 t (val i)))
             else ord0].

(** psl_counter_test sq t — the same reading matches psl_counter_view, tested
    on raw codes. *)
Definition psl_counter_test (sq t : seq nat) : bool :=
  [&& nth 0 sq (nth 0 t 0) %% 12 == 0,
      nth 0 sq (nth 0 t 1) %% 12 == 1 &
      nth 0 sq (nth 0 t 2) %% 12 == 5].

(** psl_counter_testP — the raw test decides the reading, so the fiber over
    psl_counter_view is counted by a boolean on nat lists. *)
Lemma psl_counter_testP (sq t : seq nat) :
  (psl_counter_raw_view sq t == psl_counter_view) = psl_counter_test sq t.
Proof.
rewrite /psl_counter_test; apply/idP/idP.
- move/eqP/ffunP => H; apply/and3P; split; apply/eqP.
  + by move: (H (psl211_code12 0)) => /(congr1 val); rewrite !ffunE /=.
  + by move: (H (psl211_code12 1)) => /(congr1 val); rewrite !ffunE /=.
  + by move: (H (psl211_code12 2)) => /(congr1 val); rewrite !ffunE /=.
- case/and3P => H0 H1 H2; apply/eqP/ffunP => i.
  rewrite !ffunE; apply/val_inj.
  case: i => [] [|[|[|k]]] Hk //=.
  + by rewrite (eqP H0).
  + by rewrite (eqP H1).
  + by rewrite (eqP H2).
  + by rewrite nth_default.
Qed.

(** psl_counter_raw_count b — how many of the 660 shuffles carry the deck of
    class b to psl_counter_view. *)
Definition psl_counter_raw_count (b : bool) : nat :=
  let sq := psl_counter_seq b in
  count (psl_counter_test sq) (unzip1 psl211_elem_table).

(** psl_counter_raw_countE — that count is zero in one class and one in the
    other, which is the per-deck failure of the chirality symmetry: at a fixed
    deck description the two classes do not have equally many shuffles
    producing a given reading, even though summing over deals they do. *)
Lemma psl_counter_raw_countE :
  psl_counter_raw_count true = 0 /\ psl_counter_raw_count false = 1.
Proof. by split; vm_compute. Qed.

(** psl_entry_perm_enum — the 660 tabulated entries list the shuffle group. *)
Lemma psl_entry_perm_enum :
  perm_eq (enum (pgg_G psl211_M))
    [seq psl211_entry_perm k | k <- iota 0 660].
Proof.
apply: uniq_perm.
- exact: enum_uniq.
- rewrite map_inj_in_uniq.
    exact: iota_uniq.
  exact: psl211_entry_perm_inj.
- move=> g; rewrite mem_enum.
  apply/idP/idP.
    exact: psl211_mem_entry_perm.
  move=> /mapP[k _ ->].
  exact: psl211_entry_perm_mem.
Qed.

(** psl_counter_ptbl_nth — a shuffle's table reads off its images. *)
Lemma psl_counter_ptbl_nth (g : cutT) (i : seatT) :
  nth 0 (psl211_ptbl g) i = val (g i).
Proof.
rewrite /psl211_ptbl (nth_map i) ?size_enum_ord ?ltn_ord //.
by rewrite nth_ord_enum.
Qed.

(** psl_counter_raw_viewE — the raw reading is the instance's reading. *)
Lemma psl_counter_raw_viewE (b : bool) (g : cutT) :
  psl_counter_raw_view (psl211_alldecks_seq (b, psl_counter_deal))
    (psl211_ptbl g) =
  psl211_alldecks_view psl_counter_coalition (b, psl_counter_deal) g.
Proof.
apply/ffunP => i.
(* in_set and not inE: inE would rewrite the seq membership on the left
   instead of the set membership on the right, leaving the two conditions
   different and the case split incomplete. *)
rewrite /psl_counter_raw_view /psl211_alldecks_view !ffunE.
rewrite /psl_counter_coalition in_set.
case Hi: (val i \in [:: 0; 1; 2]) => //.
rewrite /psl211_alldecks_layout tnth_mktuple.
by rewrite psl_counter_ptbl_nth.
Qed.

(** psl_counter_ptbl_enum — the tabulated tables are the tables of the group's
    elements, so a count over the table list is a count over the group. *)
Lemma psl_counter_ptbl_enum :
  perm_eq [seq psl211_ptbl g | g <- enum (pgg_G psl211_M)]
    (unzip1 psl211_elem_table).
Proof.
apply: (perm_trans (perm_map psl211_ptbl psl_entry_perm_enum)).
rewrite -map_comp.
have Heq :
    [seq (psl211_ptbl \o psl211_entry_perm) k | k <- iota 0 660] =
    unzip1 psl211_elem_table.
  apply: (@eq_from_nth _ [::]); first by rewrite size_map size_iota
    psl211_size_keys.
  (* nth_iota and exact:, never /=: a simpl here would descend into the
     closure that psl211_elem_table is defined by. *)
  move=> k; rewrite size_map size_iota => Hk.
  rewrite (nth_map 0) ?size_iota // nth_iota //.
  exact: psl211_ptbl_entry Hk.
(* exact: perm_refl, never by: after the rewrite the goal is a perm_eq of the
   closure with itself, and done would try to decide it. *)
rewrite Heq; exact: perm_refl.
Qed.

(* Past this point no proof needs the body of the laid deck or of the
   closure table, and every step that names both chiralities must not be left
   to a tactic that searches for a match. *)
Local Opaque psl211_alldecks_view psl211_elem_table.

(** psl_counter_fiber b — the shuffles of the group carrying the deck of
    class b at psl_counter_deal to psl_counter_view. *)
Definition psl_counter_fiber (b : bool) : {set cutT} :=
  [set g in pgg_G psl211_M |
     psl211_alldecks_view psl_counter_coalition
       (b, psl_counter_deal) g == psl_counter_view].

(** psl_counter_fiberE — that fiber has the raw count as its cardinality. *)
Lemma psl_counter_fiberE (b : bool) :
  #|psl_counter_fiber b| = psl_counter_raw_count b.
Proof.
rewrite /psl_counter_fiber /psl_counter_raw_count.
transitivity
  (count (fun g => psl211_alldecks_view psl_counter_coalition
      (b, psl_counter_deal) g == psl_counter_view)
    (enum (pgg_G psl211_M))).
  rewrite cardE /enum_mem size_filter count_filter.
  by apply: eq_count => g; rewrite !inE andbC.
transitivity
  (count (psl_counter_test (psl_counter_seq b))
    [seq psl211_ptbl g | g <- enum (pgg_G psl211_M)]).
  rewrite count_map; apply: eq_count => g.
  by rewrite -psl_counter_raw_viewE psl_counter_seqE psl_counter_testP.
rewrite -!size_filter; apply: perm_size.
exact: (perm_filter _ psl_counter_ptbl_enum).
Qed.

(** psl_per_deck_fibers_differ — at one deck description the two chiralities
    have different numbers of shuffles producing one reading.  The per-deal
    symmetry that the all-decks counting argument uses is therefore genuinely
    a statement about the average over deals and not about a single deal, so a
    general dealer law cannot be obtained by fixing a representative deck. *)
Lemma psl_per_deck_fibers_differ :
  #|psl_counter_fiber true| != #|psl_counter_fiber false|.
Proof.
(* Each cardinality is pinned to its numeral in term mode before the two are
   brought together, so no tactic ever searches a goal in which the two
   chiralities of the same definition could be matched against each other. *)
have [Ht Hf] := psl_counter_raw_countE.
have H1 : #|psl_counter_fiber true| = 0 :=
  etrans (psl_counter_fiberE true) Ht.
have H0 : #|psl_counter_fiber false| = 1 :=
  etrans (psl_counter_fiberE false) Hf.
apply/negP => /eqP Heq.
by case: (etrans (esym H1) (etrans Heq H0)).
Qed.

(* Nothing after this point reasons about the reading or the closure table,
   so the seals are released; Opaque is not section-scoped and would otherwise
   leak into every file that requires this one. *)
Local Transparent psl211_alldecks_view psl211_elem_table.

Print Assumptions psl_counter_seqE.
Print Assumptions psl_counter_testP.
Print Assumptions psl_counter_raw_countE.
Print Assumptions psl_entry_perm_enum.
Print Assumptions psl_counter_raw_viewE.
Print Assumptions psl_counter_ptbl_enum.
Print Assumptions psl_counter_fiberE.
Print Assumptions psl_per_deck_fibers_differ.
