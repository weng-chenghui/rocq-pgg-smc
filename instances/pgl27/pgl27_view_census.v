(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_view_census: the ambiguous-view event of a PGL(2,7) coalition        *)
(*                                                                            *)
(* A coalition is named by a list of card positions and sees the masked       *)
(* protocol view at those positions. Two facts tie that view to the collision *)
(* census of natural numbers, at every deck pair. When a secret's census view *)
(* list is repetition-free, the conditional view map is injective on the      *)
(* shuffle group, so one view comes from at most one shuffle per secret. And  *)
(* the probability that a view is produced by both secrets is the census      *)
(* collision count divided by the group order.                                *)
(*                                                                            *)
(* Both facts take two premises: that S lists card positions below eight, and *)
(* that the census view lists of the deck pair are repetition-free. Which     *)
(* reveal sets satisfy the second, and what the collision count is there, are *)
(* facts of the deck pair and are established in pgl27_encoding_r7.v and      *)
(* pgl27_encoding_r5.v.                                                       *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_code_coalition S == the card positions listed by S                 *)
(*   pgl27_view_codes S v == the coordinates of v at the positions listed     *)
(*                           by S                                             *)
(*   pgl27_ambiguous_views R e S == the views of S produced by both secrets   *)
(*                                  under the deck pair e                     *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_masked_view_eq == two views masked outside a coalition are equal   *)
(*     exactly when their listed coordinates are equal                        *)
(*   pgl27_conditional_view_inj == a repetition-free census view list makes   *)
(*     the conditional view map injective on the shuffle group                *)
(*   pgl27_ambiguous_probabilityE == the ambiguous-view event has probability *)
(*     pgl27_collisions (enc_code e) S over 336                               *)
(*                                                                            *)
(* Every statement concerns the pre-reveal coalition view of one execution.   *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp ring lra reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import transitivity_privacy.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_secrecy.
From pgg_smc Require Import pgl27_leakage_census pgl27_encoding.
From pgg_smc Require Import pgl27_table_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(** The set of card positions named by the entries of [S], the coalition
    whose masked card values are the protocol view. Entries of [S] at least
    eight name no position and repeated entries name one, which is why the
    results of this file assume every entry of [S] is below eight. *)
Definition pgl27_code_coalition (S : seq nat) : {set 'I_8} :=
  [set i | val i \in S].

(** The coordinates of the masked view [v] at the positions listed by [S], in
    the order [S] lists them. It carries a coalition view into the sequence
    form the nat collision census counts, so census multiplicities become
    multiplicities of protocol views. *)
Definition pgl27_view_codes
    (S : seq nat) (v : {ffun 'I_8 -> 'I_8}) : seq nat :=
  [seq val (v (inord x)) | x <- S].

(** An ambiguous view is reachable under both orbit-class secrets. Such a
    view leaves the Boolean secret undetermined by the coalition. The real
    carrier [R] indexes the distribution the view map is typed against and
    does not change which views this set contains. *)
Definition pgl27_ambiguous_views
    (R : realType) (e : pgl27_encoding) (S : seq nat) :
    {set {ffun 'I_8 -> 'I_8}} :=
  [set v |
     [exists g in pgg_G pgl27_M,
        pgl27_enc_view R e (pgl27_code_coalition S) (false, g) == v] &&
     [exists g in pgg_G pgl27_M,
        pgl27_enc_view R e (pgl27_code_coalition S) (true, g) == v]].

(** Two views masked outside the coalition selected by [S] are equal exactly
    when their coordinates listed by [S] are equal. Repeated listed positions
    do not affect this equivalence. *)
Lemma pgl27_masked_view_eq (S : seq nat) (v w : {ffun 'I_8 -> 'I_8}) :
  (forall i, i \notin pgl27_code_coalition S -> v i = ord0) ->
  (forall i, i \notin pgl27_code_coalition S -> w i = ord0) ->
  (v = w <-> pgl27_view_codes S v = pgl27_view_codes S w).
Proof.
move=> Hv Hw; split=> [-> //|Hcodes].
apply/ffunP => i.
case Hi: (i \in pgl27_code_coalition S).
- have Hmem : val i \in S.
    by move: Hi; rewrite /pgl27_code_coalition inE.
  have Hidx : (index (val i) S < size S)%N by rewrite index_mem Hmem.
  have Hnth := congr1 (fun l => nth 0%N l (index (val i) S)) Hcodes.
  rewrite /pgl27_view_codes !(@nth_map nat 0%N nat 0%N) //
    (nth_index 0%N Hmem) !inord_val in Hnth.
  exact: val_inj Hnth.
- have Hout : i \notin pgl27_code_coalition S by rewrite Hi.
  by rewrite (Hv i Hout) (Hw i Hout).
Qed.

(** The protocol view is zero outside the selected coalition. The mask keeps
    unobserved coordinates from contributing to equality of views. *)
Local Lemma pgl27_view_outside (R : realType) (e : pgl27_encoding)
    (S : seq nat) (u : bool * pgg_gT pgl27_M) (i : 'I_8) :
  i \notin pgl27_code_coalition S ->
  pgl27_enc_view R e (pgl27_code_coalition S) u i = ord0.
Proof.
move=> Hi; rewrite /pgl27_enc_view /coalition_view ffunE.
by rewrite (negbTE Hi).
Qed.

(** A repetition-free image list makes the mapped function injective on the
    list it was taken over. *)
Local Lemma map_uniq_inj_in
    (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1) :
  uniq (map f s) -> {in s &, injective f}.
Proof.
move=> /uniqP Huniq x y Hx Hy Hf.
have Hix : (index x s < size (map f s))%N by rewrite size_map index_mem Hx.
have Hiy : (index y s < size (map f s))%N by rewrite size_map index_mem Hy.
have Hidx : index x s = index y s.
  apply: (Huniq (f x)) => //.
  rewrite (nth_map x) ?(nth_map y) ?index_mem ?Hx ?Hy //
    !nth_index // Hf.
by rewrite -(nth_index x Hx) -(nth_index x Hy) Hidx.
Qed.

(** A repetition-free census view list makes the restricted composite of a
    census row with one deck's code table injective on the census rows. *)
Local Lemma pgl27_code_views_inj (e : pgl27_encoding) (S : seq nat)
    (b : bool) :
  uniq (code_views (enc_code e) b S) ->
  {in pgl27_group_table &,
    injective
      (fun t => code_restrict S (code_comp t (enc_code e b)))}.
Proof.
(* Unfolding code_views once and sealing the result with Qed keeps the
   transparent 336-row closure from being expanded again at every use. *)
rewrite /code_views.
exact: map_uniq_inj_in.
Qed.

(** Reading the listed coordinates of a protocol view gives the same sequence
    as restricting the composite of the shuffle table and that deck's code
    table. It identifies the masked view with the restricted census row. *)
Local Lemma pgl27_view_codesE (R : realType) (e : pgl27_encoding)
    (S : seq nat) (b : bool) (g : {perm 'I_8}) :
  all (fun x => (x < 8)%N) S ->
  pgl27_view_codes S
      (pgl27_enc_view R e (pgl27_code_coalition S) (b, g)) =
    code_restrict S
      (code_comp (pgl27_ptbl g) (enc_code e b)).
Proof.
move=> HS; rewrite /pgl27_view_codes /code_restrict.
apply/eq_in_map => x Hx.
have Hx8 : (x < 8)%N := (allP HS) x Hx.
rewrite /pgl27_enc_view /coalition_view ffunE /pgl27_code_coalition inE.
pose ox : 'I_8 := Ordinal Hx8.
have Hinord : inord x = ox by apply/val_inj; exact: inordK Hx8.
rewrite Hinord /ox /= Hx /=.
symmetry.
exact: (@pgl27_code_comp_ptblE e b g (pgl27_ptbl g) erefl ox).
Qed.

(** If the census view list for one secret is repetition-free, then the
    protocol's conditional view map is injective on the shuffle group. Thus a
    reachable view has at most one shuffle preimage for that secret. *)
Lemma pgl27_conditional_view_inj (R : realType) (e : pgl27_encoding)
    (S : seq nat) (b : bool) :
  all (fun x => (x < 8)%N) S -> uniq (code_views (enc_code e) b S) ->
  {in pgg_G pgl27_M &,
    injective
      (fun g => pgl27_enc_view R e (pgl27_code_coalition S) (b, g))}.
Proof.
move=> HS Huniq g h gG hG Hview.
have Hlisted := congr1 (pgl27_view_codes S) Hview.
have Hgcodes := @pgl27_view_codesE R e S b g HS.
have Hhcodes := @pgl27_view_codesE R e S b h HS.
have Hlisted' :
    code_restrict S
      (code_comp (pgl27_ptbl g) (enc_code e b)) =
    code_restrict S
      (code_comp (pgl27_ptbl h) (enc_code e b)) :=
  etrans (esym Hgcodes) (etrans Hlisted Hhcodes).
have Hfinj :
    {in pgl27_group_table &,
      injective
        (fun t => code_restrict S (code_comp t (enc_code e b)))} :=
  pgl27_code_views_inj Huniq.
have Htable : pgl27_ptbl g = pgl27_ptbl h.
  apply: Hfinj; [exact: pgl27_ptbl_mem gG |
                 exact: pgl27_ptbl_mem hG | exact: Hlisted'].
exact: pgl27_ptbl_inj Htable.
Qed.

(** A masked protocol view is reachable from one secret exactly when its
    listed coordinates occur in that secret's census list. *)
Local Lemma pgl27_support_codesP (R : realType) (e : pgl27_encoding)
    (S : seq nat) (b : bool) (v : {ffun 'I_8 -> 'I_8}) :
  all (fun x => (x < 8)%N) S ->
  (forall i, i \notin pgl27_code_coalition S -> v i = ord0) ->
  ((exists2 g, g \in pgg_G pgl27_M &
      pgl27_enc_view R e (pgl27_code_coalition S) (b, g) = v) <->
   pgl27_view_codes S v \in code_views (enc_code e) b S).
Proof.
move=> HS Hv; split.
- move=> [g gG Hgv].
  rewrite /code_views.
  apply/mapP; exists (pgl27_ptbl g); first exact: pgl27_ptbl_mem.
  rewrite -Hgv.
  exact: (@pgl27_view_codesE R e S b g HS).
- rewrite /code_views => /mapP [t tG Ht].
  have Hklt : (index t pgl27_group_table < 336)%N.
    have Hidx :
        (index t pgl27_group_table < size pgl27_group_table)%N
      by rewrite index_mem.
    by move: Hidx; rewrite pgl27_group_table_size.
  pose k : 'I_336 := Ordinal Hklt.
  have Hrow : nth [::] pgl27_group_table k = t.
    exact: nth_index tG.
  exists (pgl27_table_perm k); first exact: pgl27_table_perm_mem.
  have Hout : forall i, i \notin pgl27_code_coalition S ->
      pgl27_enc_view R e (pgl27_code_coalition S)
        (b, pgl27_table_perm k) i = ord0 :=
    @pgl27_view_outside R e S (b, pgl27_table_perm k).
  have Heq := @pgl27_masked_view_eq S
    (pgl27_enc_view R e (pgl27_code_coalition S) (b, pgl27_table_perm k))
    v Hout Hv.
  apply: (proj2 Heq).
  rewrite (@pgl27_view_codesE R e S b (pgl27_table_perm k) HS).
  rewrite pgl27_table_permE Hrow.
  exact: esym Ht.
Qed.

(** Census row [u.2] dealt under secret [u.1] restricts to a view of [S] that
    both secrets can produce. It is the collision event of the nat census,
    stated per row rather than as a count. *)
Local Definition pgl27_code_ambiguous (e : pgl27_encoding)
    (S : seq nat) (u : bool * 'I_336) : bool :=
  let t := nth [::] pgl27_group_table u.2 in
  let v := code_restrict S (code_comp t (enc_code e u.1)) in
  (v \in code_views (enc_code e) false S)
  && (v \in code_views (enc_code e) true S).

(** The support-intersection event on a table row is the corresponding
    collision event in the nat census. *)
Local Lemma pgl27_table_ambiguousP (R : realType) (e : pgl27_encoding)
    (S : seq nat) (b : bool) (k : 'I_336) :
  all (fun x => (x < 8)%N) S ->
  (pgl27_enc_view R e (pgl27_code_coalition S) (b, pgl27_table_perm k)
       \in pgl27_ambiguous_views R e S <->
   pgl27_code_ambiguous e S (b, k)).
Proof.
move=> HS.
rewrite /pgl27_ambiguous_views inE.
rewrite /pgl27_code_ambiguous.
cbn beta iota zeta.
have Hout : forall i, i \notin pgl27_code_coalition S ->
    pgl27_enc_view R e (pgl27_code_coalition S)
      (b, pgl27_table_perm k) i = ord0 :=
  @pgl27_view_outside R e S (b, pgl27_table_perm k).
have Hcomp :
    code_comp (pgl27_ptbl (pgl27_table_perm k)) (enc_code e b) =
    code_comp (nth [::] pgl27_group_table k) (enc_code e b) :=
  congr1 (fun t => code_comp t (enc_code e b)) (pgl27_table_permE k).
have Hcr := congr1 (code_restrict S) Hcomp.
have Hvc := @pgl27_view_codesE R e S b (pgl27_table_perm k) HS.
have Heq := etrans Hvc Hcr.
split.
- move=> /andP [Hfalse Htrue]; apply/andP; split.
  + have Hex : exists2 g, g \in pgg_G pgl27_M &
        pgl27_enc_view R e (pgl27_code_coalition S) (false, g) =
        pgl27_enc_view R e (pgl27_code_coalition S)
          (b, pgl27_table_perm k).
      move/exists_inP: Hfalse => [g gG /eqP Hg].
      by exists g.
    have Hmem :=
      (proj1 (@pgl27_support_codesP R e S false _ HS Hout)) Hex.
    move: Hmem.
    by rewrite Heq.
  + have Hex : exists2 g, g \in pgg_G pgl27_M &
        pgl27_enc_view R e (pgl27_code_coalition S) (true, g) =
        pgl27_enc_view R e (pgl27_code_coalition S)
          (b, pgl27_table_perm k).
      move/exists_inP: Htrue => [g gG /eqP Hg].
      by exists g.
    have Hmem :=
      (proj1 (@pgl27_support_codesP R e S true _ HS Hout)) Hex.
    move: Hmem.
    by rewrite Heq.
- move=> /andP [Hfalse Htrue]; apply/andP; split.
  + have Hmem : pgl27_view_codes S
          (pgl27_enc_view R e (pgl27_code_coalition S)
            (b, pgl27_table_perm k)) \in code_views (enc_code e) false S.
      move: Hfalse.
      by rewrite -Heq.
    have Hex :=
      (proj2 (@pgl27_support_codesP R e S false _ HS Hout)) Hmem.
    apply/exists_inP.
    move: Hex => [g gG Hg].
    exists g; first exact: gG.
    exact/eqP.
  + have Hmem : pgl27_view_codes S
          (pgl27_enc_view R e (pgl27_code_coalition S)
            (b, pgl27_table_perm k)) \in code_views (enc_code e) true S.
      move: Htrue.
      by rewrite -Heq.
    have Hex :=
      (proj2 (@pgl27_support_codesP R e S true _ HS Hout)) Hmem.
    apply/exists_inP.
    move: Hex => [g gG Hg].
    exists g; first exact: gG.
    exact/eqP.
Qed.

(** The protocol sample named by a secret and a census index. It transports
    the uniform law on the 2 * 336 table samples to the uniform law on secret
    and shuffle that the protocol actually runs. *)
Local Definition pgl27_table_sample
    (u : bool * 'I_336) : bool * pgg_gT pgl27_M :=
  let: (b, k) := u in (b, pgl27_table_perm k).

(** Distinct secret-and-index pairs name distinct protocol samples. *)
Local Lemma pgl27_table_sample_inj : injective pgl27_table_sample.
Proof.
(* The pair equation is taken apart through xpair_eqE rather than by an
   injection intro pattern: the latter forces a head normal form of
   pgl27_table_perm, which expands the 336-row tables. *)
move=> [b k] [c l] H.
rewrite /pgl27_table_sample /= in H.
have Hbool : (b, pgl27_table_perm k) == (c, pgl27_table_perm l)
  by exact/eqP.
move: Hbool; rewrite xpair_eqE => /andP [/eqP Hb /eqP Hkl].
have Hk := pgl27_table_perm_inj Hkl.
apply/eqP; rewrite xpair_eqE; apply/andP; split; exact/eqP.
Qed.

(** The secret-and-shuffle pairs whose coalition view is reachable under both
    orbit secrets. Its cardinality over the 2 * 336 executions is the
    probability that one view leaves the secret undetermined. *)
Local Definition pgl27_ambiguous_samples
    (R : realType) (e : pgl27_encoding) (S : seq nat) :
    {set bool * pgg_gT pgl27_M} :=
  [set u | let: (b, g) := u in
     (pgl27_enc_view R e (pgl27_code_coalition S) (b, g)
        \in pgl27_ambiguous_views R e S) &&
     (g \in pgg_G pgl27_M)].

(** The secret-and-row pairs satisfying the census collision event, the nat
    counterpart of pgl27_ambiguous_samples. *)
Local Definition pgl27_code_ambiguous_samples (e : pgl27_encoding)
    (S : seq nat) : {set bool * 'I_336} :=
  [set u | pgl27_code_ambiguous e S u].

(** The supported samples of the actual experiment are the injective image
    of the table samples satisfying the census collision event. *)
Local Lemma pgl27_ambiguous_samplesE (R : realType) (e : pgl27_encoding)
    (S : seq nat) :
  all (fun x => (x < 8)%N) S ->
  pgl27_ambiguous_samples R e S =
    pgl27_table_sample @: pgl27_code_ambiguous_samples e S.
Proof.
move=> HS; apply/setP => [[b g]].
rewrite /pgl27_ambiguous_samples inE /=.
apply/idP/imsetP.
- move=> /andP [Hamb gG].
  have [k Hkg] := pgl27_table_perm_surj gG.
  exists (b, k).
  + rewrite /pgl27_code_ambiguous_samples inE.
    apply: (proj1 (@pgl27_table_ambiguousP R e S b k HS)).
    by rewrite Hkg.
  + rewrite /pgl27_table_sample /=.
    apply/eqP; rewrite xpair_eqE; apply/andP; split; first exact: eqxx.
    exact/eqP/esym.
- move=> [[c k] Hcode Heq].
  rewrite /pgl27_table_sample /= in Heq.
  have Hpair : (b, g) == (c, pgl27_table_perm k) by exact/eqP.
  move: Hpair; rewrite xpair_eqE => /andP [/eqP Hb /eqP Hg].
  apply/andP; split.
  + have Hamb :
        pgl27_enc_view R e (pgl27_code_coalition S)
          (c, pgl27_table_perm k) \in pgl27_ambiguous_views R e S.
      apply: (proj2 (@pgl27_table_ambiguousP R e S c k HS)).
      by move: Hcode; rewrite /pgl27_code_ambiguous_samples inE.
    move: Hb Hg => -> ->.
    exact: Hamb.
  + move: Hg => ->.
    exact: (pgl27_table_perm_mem k).
Qed.

(** The two ambiguous-sample sets have the same cardinality. *)
Local Lemma card_pgl27_ambiguous_samples (R : realType)
    (e : pgl27_encoding) (S : seq nat) :
  all (fun x => (x < 8)%N) S ->
  #|pgl27_ambiguous_samples R e S| = #|pgl27_code_ambiguous_samples e S|.
Proof.
move=> HS; rewrite (pgl27_ambiguous_samplesE R e HS).
exact: card_imset pgl27_table_sample_inj.
Qed.

(** Counting the indices of a list of length [n] that satisfy a predicate at
    their entry is counting the entries that satisfy it. *)
Local Lemma card_ord_count (T : eqType) (n : nat)
    (s : seq T) (x0 : T) (p : pred T) :
  size s = n ->
  #|[set i : 'I_n | p (nth x0 s (val i))]| = count p s.
Proof.
move=> Hs.
rewrite -sum1_card sum1_count.
rewrite [index_enum _]unlock -enumT.
have Hcount :
    count (in_mem^~ (mem [set i : 'I_n |
      p (nth x0 s (val i))])) (enum 'I_n) =
    count (fun i : 'I_n => p (nth x0 s (val i))) (enum 'I_n).
  apply: eq_in_count => i _.
  by rewrite inE.
rewrite Hcount.
rewrite -(@count_map 'I_n T
  (fun i => nth x0 s (val i)) p (enum 'I_n)).
congr (count p _).
have Hsizeb : size s == n by exact/eqP.
pose t : n.-tuple T := Tuple Hsizeb.
change ([seq nth x0 t (val i) | i <- enum 'I_n] = val t).
under eq_map do rewrite -tnth_nth.
exact: map_tnth_enum t.
Qed.

(** Two repetition-free lists meet in the same number of entries counted from
    either side. *)
Local Lemma count_mem_sym (T : eqType) (s t : seq T) :
  uniq s -> uniq t ->
  count (mem t) s = count (mem s) t.
Proof.
move=> Hs Ht.
rewrite -size_filter -size_filter.
apply: perm_size.
apply: uniq_perm.
exact: filter_uniq _ Hs.
exact: filter_uniq _ Ht.
move=> x.
by rewrite !mem_filter andbC.
Qed.

(** The census view of [S] produced by row [k] under the secret [b]. *)
Local Definition pgl27_code_view_row (e : pgl27_encoding)
    (S : seq nat) (b : bool) (k : 'I_336) : seq nat :=
  code_restrict S
    (code_comp (nth [::] pgl27_group_table (val k)) (enc_code e b)).

(** Every census view of a row occurs in that secret's census view list. *)
Local Lemma pgl27_code_view_row_mem (e : pgl27_encoding)
    (S : seq nat) (b : bool) (k : 'I_336) :
  pgl27_code_view_row e S b k \in code_views (enc_code e) b S.
Proof.
rewrite /pgl27_code_view_row /code_views.
apply/mapP.
exists (nth [::] pgl27_group_table (val k)).
apply: mem_nth.
by rewrite pgl27_group_table_size; exact: ltn_ord k.
by [].
Qed.

(* Sealing the 336-row table keeps the cardinality proofs from expanding it
   during conversion. *)
Local Opaque pgl27_group_table.

(** Under the secret false the collision event on a row reduces to membership
    of that row's census view in the other secret's list. *)
Local Lemma pgl27_code_ambiguous_falseE (e : pgl27_encoding)
    (S : seq nat) (k : 'I_336) :
  pgl27_code_ambiguous e S (false, k) =
  (pgl27_code_view_row e S false k \in code_views (enc_code e) true S).
Proof.
change ((pgl27_code_view_row e S false k \in code_views (enc_code e) false S) &&
  (pgl27_code_view_row e S false k \in code_views (enc_code e) true S) =
  (pgl27_code_view_row e S false k \in code_views (enc_code e) true S)).
have Hfalse :
    (pgl27_code_view_row e S false k
       \in code_views (enc_code e) false S) = true :=
  @pgl27_code_view_row_mem e S false k.
exact (@andb_idl
  (pgl27_code_view_row e S false k \in code_views (enc_code e) false S)
  (pgl27_code_view_row e S false k \in code_views (enc_code e) true S)
  (fun _ => Hfalse)).
Qed.

(** Under the secret true the collision event on a row reduces to membership
    of that row's census view in the other secret's list. *)
Local Lemma pgl27_code_ambiguous_trueE (e : pgl27_encoding)
    (S : seq nat) (k : 'I_336) :
  pgl27_code_ambiguous e S (true, k) =
  (pgl27_code_view_row e S true k \in code_views (enc_code e) false S).
Proof.
change ((pgl27_code_view_row e S true k \in code_views (enc_code e) false S) &&
  (pgl27_code_view_row e S true k \in code_views (enc_code e) true S) =
  (pgl27_code_view_row e S true k \in code_views (enc_code e) false S)).
have Htrue :
    (pgl27_code_view_row e S true k
       \in code_views (enc_code e) true S) = true :=
  @pgl27_code_view_row_mem e S true k.
exact (@andb_idr
  (pgl27_code_view_row e S true k \in code_views (enc_code e) false S)
  (pgl27_code_view_row e S true k \in code_views (enc_code e) true S)
  (fun _ => Htrue)).
Qed.

(** The rows ambiguous under the secret false number the census collision
    count, once both census view lists are repetition-free. *)
Local Lemma card_pgl27_code_ambiguous_false (e : pgl27_encoding)
    (S : seq nat) :
  uniq (code_views (enc_code e) false S) ->
  uniq (code_views (enc_code e) true S) ->
  #|[set k : 'I_336 | pgl27_code_ambiguous e S (false, k)]| =
  pgl27_collisions (enc_code e) S.
Proof.
move=> Hfalse Htrue.
have Hset :
    [set k : 'I_336 | pgl27_code_ambiguous e S (false, k)] =
    [set k : 'I_336 |
      pgl27_code_view_row e S false k \in code_views (enc_code e) true S].
  apply/setP => k.
  rewrite [in LHS]inE [in RHS]inE.
  exact (@pgl27_code_ambiguous_falseE e S k).
rewrite Hset /pgl27_code_view_row.
rewrite (@card_ord_count (seq nat) 336
  pgl27_group_table [::]
  (fun t => code_restrict S (code_comp t (enc_code e false))
    \in code_views (enc_code e) true S)
  pgl27_group_table_size).
rewrite -(@count_map (seq nat) (seq nat)
  (fun t => code_restrict S (code_comp t (enc_code e false)))
  (mem (code_views (enc_code e) true S)) pgl27_group_table).
change (count (mem (code_views (enc_code e) true S))
          (code_views (enc_code e) false S) =
  pgl27_collisions (enc_code e) S).
rewrite /pgl27_collisions.
exact: count_mem_sym Hfalse Htrue.
Qed.

(** The rows ambiguous under the secret true number the census collision
    count. *)
Local Lemma card_pgl27_code_ambiguous_true (e : pgl27_encoding)
    (S : seq nat) :
  #|[set k : 'I_336 | pgl27_code_ambiguous e S (true, k)]| =
  pgl27_collisions (enc_code e) S.
Proof.
have Hset :
    [set k : 'I_336 | pgl27_code_ambiguous e S (true, k)] =
    [set k : 'I_336 |
      pgl27_code_view_row e S true k \in code_views (enc_code e) false S].
  apply/setP => k.
  rewrite [in LHS]inE [in RHS]inE.
  exact (@pgl27_code_ambiguous_trueE e S k).
rewrite Hset /pgl27_code_view_row.
rewrite (@card_ord_count (seq nat) 336
  pgl27_group_table [::]
  (fun t => code_restrict S (code_comp t (enc_code e true))
    \in code_views (enc_code e) false S)
  pgl27_group_table_size).
rewrite -(@count_map (seq nat) (seq nat)
  (fun t => code_restrict S (code_comp t (enc_code e true)))
  (mem (code_views (enc_code e) false S)) pgl27_group_table).
change (count (mem (code_views (enc_code e) false S))
          (code_views (enc_code e) true S) =
  pgl27_collisions (enc_code e) S).
by rewrite /pgl27_collisions.
Qed.

(** The two secret-indexed table samples contribute one copy of the
    cross-secret collision count each. *)
Local Lemma card_pgl27_code_ambiguous_samplesE (e : pgl27_encoding)
    (S : seq nat) :
  uniq (code_views (enc_code e) false S) ->
  uniq (code_views (enc_code e) true S) ->
  #|pgl27_code_ambiguous_samples e S| = 2 * pgl27_collisions (enc_code e) S.
Proof.
move=> Hfalse Htrue.
rewrite /pgl27_code_ambiguous_samples -sum1_card.
have Hsplit :
    (\sum_(u in [set z | pgl27_code_ambiguous e S z]) 1)%N =
    (\sum_(b : bool)
       \sum_(k in [set j : 'I_336 |
         pgl27_code_ambiguous e S (b, j)]) 1)%N.
  symmetry.
  rewrite pair_big_dep.
  apply: eq_bigl => [[b k]].
  rewrite [in LHS]inE [in RHS]inE /=.
  reflexivity.
apply: (etrans Hsplit).
rewrite big_bool.
rewrite [in LHS]sum1_card.
rewrite [in LHS]sum1_card.
apply: (etrans (congr2 addn
  (@card_pgl27_code_ambiguous_true e S)
  (card_pgl27_code_ambiguous_false Hfalse Htrue))).
rewrite addnn.
symmetry.
exact: mul2n.
Qed.

(** A pair of a uniform bit and a uniform census row carries mass one over
    672 per sample, so a set of two copies of a row count has mass that count
    over 336. *)
Local Lemma uniform_pair_massE (R : realType) (n : nat) :
  (((2%:R : R)^-1 * (336%:R : R)^-1) *+ (2 * n)) =
  n%:R / 336%:R.
Proof.
rewrite -mulr_natl natrM.
lra.
Qed.

(** The Boolean random variable that is true exactly on the executions whose
    coalition view is ambiguous. *)
Local Definition pgl27_ambiguous_indicator (R : realType)
    (e : pgl27_encoding) (S : seq nat) : {RV (pgl27P R) -> bool} :=
  fun u => pgl27_enc_view R e (pgl27_code_coalition S) u
             \in pgl27_ambiguous_views R e S.

(** The ambiguity indicator is true with mass the common sample mass times
    the number of ambiguous samples. *)
Local Lemma pgl27_pr_ambiguous_indicatorE (R : realType)
    (e : pgl27_encoding) (S : seq nat) :
  `Pr[(pgl27_ambiguous_indicator R e S) = true] =
  ((2%:R : R)^-1 * (336%:R : R)^-1) *+
    #|pgl27_ambiguous_samples R e S|.
Proof.
rewrite pfwd1E /Pr.
under eq_bigl => u do
  rewrite inE /= /pgl27_ambiguous_indicator eqb_id.
rewrite -sumr_const big_mkcond [RHS]big_mkcond.
apply: eq_bigr => [[b g]] _.
rewrite /pgl27_ambiguous_samples [in RHS]inE /=.
case: (pgl27_enc_view R e (pgl27_code_coalition S) (b, g)
  \in pgl27_ambiguous_views R e S); last by [].
rewrite andTb /pgl27P fdist_prodE /= fdist_uniformE card_bool.
case: ifPn => gG.
- rewrite fdist_uniform_supp_in // pgl27_group_card.
  by [].
- by rewrite fdist_uniform_supp_notin // mulr0.
Qed.

(** The ambiguous-view event and the ambiguity indicator have the same
    probability. *)
Local Lemma pgl27_pr_ambiguousE (R : realType) (e : pgl27_encoding)
    (S : seq nat) :
  `Pr[(pgl27_enc_view R e (pgl27_code_coalition S))
        \in pgl27_ambiguous_views R e S] =
  `Pr[(pgl27_ambiguous_indicator R e S) = true].
Proof.
rewrite pr_inE pfwd1E; congr Pr; apply/setP => u.
rewrite [in LHS]inE [in RHS]inE /=
  /pgl27_ambiguous_indicator eqb_id.
reflexivity.
Qed.

(** A coalition whose two census view lists are repetition-free sees a view
    compatible with both orbit secrets exactly as often as the census counts
    cross-secret collisions. It is the probability of learning nothing about
    the secret from a single pre-reveal view. *)
Lemma pgl27_ambiguous_probabilityE (R : realType) (e : pgl27_encoding)
    (S : seq nat) :
  all (fun x => (x < 8)%N) S ->
  uniq (code_views (enc_code e) false S) ->
  uniq (code_views (enc_code e) true S) ->
  `Pr[(pgl27_enc_view R e (pgl27_code_coalition S))
        \in pgl27_ambiguous_views R e S] =
  (pgl27_collisions (enc_code e) S)%:R / 336%:R.
Proof.
move=> HS Hfalse Htrue.
rewrite pgl27_pr_ambiguousE pgl27_pr_ambiguous_indicatorE.
rewrite (card_pgl27_ambiguous_samples R e HS).
rewrite (card_pgl27_code_ambiguous_samplesE Hfalse Htrue).
exact: uniform_pair_massE.
Qed.
