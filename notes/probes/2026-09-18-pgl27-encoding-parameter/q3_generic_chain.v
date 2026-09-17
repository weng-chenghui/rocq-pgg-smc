(* PROBE Q3 (task P0, plan 2026-09-18-pgl27-encoding-parameter).
   Re-prove over an abstract encoding record the two chain steps that touch
   the concrete deal: the table-bridge composition lemma of
   pgl27_table_bridge.v and the conditional-view injectivity of
   pgl27_view_census.v.  Both are the hardest per-file uses of orbit_encode /
   code_deal.  The question is whether they need a per-encoding computed fact
   or only the record's fields. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import transitivity_privacy.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_profile pgl27_secrecy.
From pgg_smc Require Import pgl27_leakage_census pgl27_mixing.
From pgg_smc Require Import pgl27_table_bridge pgl27_view_census.
From probe Require Import q2_record.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(* pgl27_view_census.v's map_uniq_inj_in is Local, so it is reproved here. *)
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

Section q3_generic.
Variable e : pgl27_encoding.

(* The census view lists of the encoding e. *)
Definition enc_views (b : bool) (S : seq nat) : seq (seq nat) :=
  [seq code_restrict S (code_comp t (enc_code e b)) | t <- pgl27_group_table].

Definition enc_collisions (S : seq nat) : nat :=
  count (fun v => v \in enc_views false S) (enc_views true S).

(* The coalition view of the encoding e: the generic coalition_view of
   reconstruct/transitivity_privacy.v at the deck function enc_deck e. *)
Definition enc_view (R : realType) (C : {set 'I_8}) :
    {RV (pgl27P R) -> {ffun 'I_8 -> 'I_8}} :=
  coalition_view (@pgg_rho pgl27_M) (fdist_uniform card_bool) pgl27_G_pos
    (enc_deck e) C.

(* --------------------------------------------------------------------- *)
(* Step 1: pgl27_table_bridge.v's composition lemma, over the record.     *)
(* Needs only enc_code_nthE, a derived consequence of enc_codeE.          *)
(* --------------------------------------------------------------------- *)

Lemma enc_code_comp_ptblE (b : bool) (g : {perm 'I_8}) (t : seq nat)
    (Ht : pgl27_ptbl g = t) (i : 'I_8) :
  nth 0 (code_comp t (enc_code e b)) i =
  val (tnth (enc_deck e b) (g i)).
Proof.
have Hsize : size t = 8 by rewrite -Ht /pgl27_ptbl pgl27_mixing.ptbl_size.
rewrite /code_comp (nth_map 0); last first.
  by rewrite Hsize; exact: ltn_ord i.
rewrite -Ht /pgl27_ptbl pgl27_mixing.ptbl_nth.
exact: enc_code_nthE.
Qed.

Lemma enc_code_comp_rowE (b : bool) (k : 'I_336) (i : 'I_8) :
  nth 0 (code_comp (nth [::] pgl27_group_table k) (enc_code e b)) i =
  val (tnth (enc_deck e b) (pgl27_table_perm k i)).
Proof.
exact: (@enc_code_comp_ptblE b (pgl27_table_perm k)
  (nth [::] pgl27_group_table k) (pgl27_table_permE k) i).
Qed.

(* --------------------------------------------------------------------- *)
(* Step 2: pgl27_view_census.v's view-codes and injectivity, over e.      *)
(* --------------------------------------------------------------------- *)

Lemma enc_view_outside (R : realType) (S : seq nat)
    (u : bool * pgg_gT pgl27_M) (i : 'I_8) :
  i \notin pgl27_code_coalition S ->
  enc_view R (pgl27_code_coalition S) u i = ord0.
Proof.
by move=> Hi; rewrite /enc_view /coalition_view ffunE (negbTE Hi).
Qed.

Lemma enc_view_codesE (R : realType) (S : seq nat) (b : bool)
    (g : {perm 'I_8}) :
  all (fun x => (x < 8)%N) S ->
  pgl27_view_codes S (enc_view R (pgl27_code_coalition S) (b, g))
  = code_restrict S (code_comp (pgl27_ptbl g) (enc_code e b)).
Proof.
move=> HS; rewrite /pgl27_view_codes /code_restrict.
apply/eq_in_map => x Hx.
have Hx8 : (x < 8)%N := (allP HS) x Hx.
rewrite /enc_view /coalition_view ffunE /pgl27_code_coalition inE.
pose ox : 'I_8 := Ordinal Hx8.
have Hinord : inord x = ox by apply/val_inj; exact: inordK Hx8.
rewrite Hinord /ox /= Hx /=.
symmetry.
exact: (@enc_code_comp_ptblE b g (pgl27_ptbl g) erefl ox).
Qed.

Lemma enc_code_views_inj (S : seq nat) (b : bool) :
  uniq (enc_views b S) ->
  {in pgl27_group_table &,
    injective (fun t => code_restrict S (code_comp t (enc_code e b)))}.
Proof. rewrite /enc_views; exact: map_uniq_inj_in. Qed.

Lemma enc_conditional_view_inj (R : realType) (S : seq nat) (b : bool) :
  all (fun x => (x < 8)%N) S -> uniq (enc_views b S) ->
  {in pgg_G pgl27_M &,
    injective (fun g => enc_view R (pgl27_code_coalition S) (b, g))}.
Proof.
move=> HS Huniq g h gG hG Hview.
have Hlisted := congr1 (pgl27_view_codes S) Hview.
have Hgcodes := @enc_view_codesE R S b g HS.
have Hhcodes := @enc_view_codesE R S b h HS.
have Hlisted' :
    code_restrict S (code_comp (pgl27_ptbl g) (enc_code e b)) =
    code_restrict S (code_comp (pgl27_ptbl h) (enc_code e b)) :=
  etrans (esym Hgcodes) (etrans Hlisted Hhcodes).
have Hfinj :
    {in pgl27_group_table &,
      injective (fun t => code_restrict S (code_comp t (enc_code e b)))} :=
  enc_code_views_inj Huniq.
have Htable : pgl27_ptbl g = pgl27_ptbl h.
  apply: Hfinj; [exact: pgl27_ptbl_mem gG |
                 exact: pgl27_ptbl_mem hG | exact: Hlisted'].
exact: pgl27_ptbl_inj Htable.
Qed.

(* --------------------------------------------------------------------- *)
(* Step 3: the ambiguity support characterisation, over e.  This is the   *)
(* one that carries the census count into the probability.                *)
(* --------------------------------------------------------------------- *)

Definition enc_ambiguous_views (R : realType) (S : seq nat) :
    {set {ffun 'I_8 -> 'I_8}} :=
  [set v |
     [exists g in pgg_G pgl27_M,
        enc_view R (pgl27_code_coalition S) (false, g) == v] &&
     [exists g in pgg_G pgl27_M,
        enc_view R (pgl27_code_coalition S) (true, g) == v]].

Lemma enc_support_codesP (R : realType) (S : seq nat) (b : bool)
    (v : {ffun 'I_8 -> 'I_8}) :
  all (fun x => (x < 8)%N) S ->
  (forall i, i \notin pgl27_code_coalition S -> v i = ord0) ->
  ((exists2 g, g \in pgg_G pgl27_M &
      enc_view R (pgl27_code_coalition S) (b, g) = v) <->
   pgl27_view_codes S v \in enc_views b S).
Proof.
move=> HS Hv; split.
- move=> [g gG Hgv].
  rewrite /enc_views.
  apply/mapP; exists (pgl27_ptbl g); first exact: pgl27_ptbl_mem.
  rewrite -Hgv.
  exact: (@enc_view_codesE R S b g HS).
- rewrite /enc_views => /mapP [t tG Ht].
  have Hklt : (index t pgl27_group_table < 336)%N.
    have Hidx : (index t pgl27_group_table < size pgl27_group_table)%N
      by rewrite index_mem.
    by move: Hidx; rewrite pgl27_group_table_size.
  pose k : 'I_336 := Ordinal Hklt.
  have Hrow : nth [::] pgl27_group_table k = t by exact: nth_index tG.
  exists (pgl27_table_perm k); first exact: pgl27_table_perm_mem.
  have Hout : forall i, i \notin pgl27_code_coalition S ->
      enc_view R (pgl27_code_coalition S) (b, pgl27_table_perm k) i = ord0 :=
    @enc_view_outside R S (b, pgl27_table_perm k).
  have Heq := @pgl27_masked_view_eq S
    (enc_view R (pgl27_code_coalition S) (b, pgl27_table_perm k)) v Hout Hv.
  apply: (proj2 Heq).
  rewrite (@enc_view_codesE R S b (pgl27_table_perm k) HS).
  rewrite pgl27_table_permE Hrow.
  exact: esym Ht.
Qed.

End q3_generic.

(* --------------------------------------------------------------------- *)
(* Q3 checks at the r7 instance: the generic forms are the source forms.  *)
(* --------------------------------------------------------------------- *)

(* The agreement lemmas take the delta-only route.  Closing them with "by []"
   drives conversion into the 336-row table closure and diverges; see
   q1c_conv_bisect.v for the measurement. *)
Lemma q3_r7_views (b : bool) (S : seq nat) :
  enc_views enc_r7 b S = code_views b S.
Proof. by rewrite /enc_views /code_views q2_r7_code. Qed.

Lemma q3_r7_collisions (S : seq nat) :
  enc_collisions enc_r7 S = pgl27_collisions S.
Proof. by rewrite /enc_collisions /pgl27_collisions !q3_r7_views. Qed.

(* The coalition view carries no table, so this conversion is cheap. *)
Lemma q3_r7_view (R : realType) (C : {set 'I_8}) :
  enc_view enc_r7 R C = pgl27_view R C.
Proof. by rewrite /enc_view q2_r7_deck. Qed.

Lemma q3_r7_ambiguous (R : realType) (S : seq nat) :
  enc_ambiguous_views enc_r7 R S = pgl27_ambiguous_views R S.
Proof.
apply/setP => v.
by rewrite /enc_ambiguous_views /pgl27_ambiguous_views !inE q3_r7_view.
Qed.

Lemma q3_r7_bridge (b : bool) (k : 'I_336) (i : 'I_8) :
  nth 0 (code_comp (nth [::] pgl27_group_table k) (code_deal b)) i
  = val (tnth (orbit_encode b) (pgl27_table_perm k i)).
Proof. exact: (enc_code_comp_rowE enc_r7). Qed.

Print Assumptions enc_code_comp_ptblE.
Print Assumptions enc_conditional_view_inj.
Print Assumptions enc_support_codesP.
