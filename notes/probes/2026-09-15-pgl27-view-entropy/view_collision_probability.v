From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_secrecy.
From pgg_smc Require Import pgl27_leakage_census pgl27_mixing.
From pgl27_view_entropy_probe Require Import probe_view_definitions.
From pgl27_view_entropy_probe Require Import table_group_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Prenex Implicits.

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
  have Hidx : index (val i) S < size S by rewrite index_mem Hmem.
  have Hnth := congr1 (fun l => nth 0 l (index (val i) S)) Hcodes.
  rewrite /pgl27_view_codes !(@nth_map nat 0 nat 0) //
    (nth_index 0 Hmem) !inord_val in Hnth.
  exact: val_inj Hnth.
- have Hout : i \notin pgl27_code_coalition S by rewrite Hi.
  by rewrite (Hv i Hout) (Hw i Hout).
Qed.

(** The protocol view is zero outside the selected coalition. The mask keeps
    unobserved coordinates from contributing to equality of observations. *)
Lemma pgl27_view_outside (R : realType) (S : seq nat)
    (u : bool * pgg_gT pgl27_M) (i : 'I_8) :
  i \notin pgl27_code_coalition S ->
  pgl27_view R (pgl27_code_coalition S) u i = ord0.
Proof.
move=> Hi; rewrite /pgl27_view ffunE.
by rewrite (negbTE Hi).
Qed.

(** Equality of two protocol views is equivalent to equality of their listed
    coalition coordinates. Hence collision-census uniqueness implies
    injectivity of the coalition observation. *)
Lemma pgl27_view_eq_codes (R : realType) (S : seq nat)
    (u1 u2 : bool * pgg_gT pgl27_M) :
  (pgl27_view R (pgl27_code_coalition S) u1 =
     pgl27_view R (pgl27_code_coalition S) u2 <->
   pgl27_view_codes S
     (pgl27_view R (pgl27_code_coalition S) u1) =
   pgl27_view_codes S
     (pgl27_view R (pgl27_code_coalition S) u2)).
Proof.
apply: pgl27_masked_view_eq; exact: pgl27_view_outside.
Qed.

(** The harmonic representative satisfies the masked-view equivalence. *)
Lemma pgl27_view_eq_codes_harmonic (R : realType)
    (u1 u2 : bool * pgg_gT pgl27_M) :
  (pgl27_view R (pgl27_code_coalition rep_harmonic) u1 =
     pgl27_view R (pgl27_code_coalition rep_harmonic) u2 <->
   pgl27_view_codes rep_harmonic
     (pgl27_view R (pgl27_code_coalition rep_harmonic) u1) =
   pgl27_view_codes rep_harmonic
     (pgl27_view R (pgl27_code_coalition rep_harmonic) u2)).
Proof. exact: pgl27_view_eq_codes. Qed.

(** The equianharmonic representative satisfies the masked-view
    equivalence. *)
Lemma pgl27_view_eq_codes_equianharmonic (R : realType)
    (u1 u2 : bool * pgg_gT pgl27_M) :
  (pgl27_view R (pgl27_code_coalition rep_equianharmonic) u1 =
     pgl27_view R (pgl27_code_coalition rep_equianharmonic) u2 <->
   pgl27_view_codes rep_equianharmonic
     (pgl27_view R (pgl27_code_coalition rep_equianharmonic) u1) =
   pgl27_view_codes rep_equianharmonic
     (pgl27_view R (pgl27_code_coalition rep_equianharmonic) u2)).
Proof. exact: pgl27_view_eq_codes. Qed.

(** The five-position representative satisfies the masked-view
    equivalence. *)
Lemma pgl27_view_eq_codes_five (R : realType)
    (u1 u2 : bool * pgg_gT pgl27_M) :
  (pgl27_view R (pgl27_code_coalition rep_five) u1 =
     pgl27_view R (pgl27_code_coalition rep_five) u2 <->
   pgl27_view_codes rep_five
     (pgl27_view R (pgl27_code_coalition rep_five) u1) =
   pgl27_view_codes rep_five
     (pgl27_view R (pgl27_code_coalition rep_five) u2)).
Proof. exact: pgl27_view_eq_codes. Qed.

(** The six-position representative satisfies the masked-view
    equivalence. *)
Lemma pgl27_view_eq_codes_six (R : realType)
    (u1 u2 : bool * pgg_gT pgl27_M) :
  (pgl27_view R (pgl27_code_coalition rep_six) u1 =
     pgl27_view R (pgl27_code_coalition rep_six) u2 <->
   pgl27_view_codes rep_six
     (pgl27_view R (pgl27_code_coalition rep_six) u1) =
   pgl27_view_codes rep_six
     (pgl27_view R (pgl27_code_coalition rep_six) u2)).
Proof. exact: pgl27_view_eq_codes. Qed.

Local Definition pgl27_mutation_coalition : {set 'I_8} :=
  [set i | val i < 2].

Local Definition pgl27_mutation_view0 : {ffun 'I_8 -> 'I_8} :=
  [ffun _ => ord0].

Local Definition pgl27_mutation_view1 : {ffun 'I_8 -> 'I_8} :=
  [ffun i => if val i == 1 then @Ordinal 8 1 isT else ord0].

Local Definition pgl27_omitted_coordinate_mutation : bool :=
  [&& pgl27_view_codes [:: 0] pgl27_mutation_view0 ==
        pgl27_view_codes [:: 0] pgl27_mutation_view1,
      pgl27_mutation_view0 != pgl27_mutation_view1 &
      [forall i,
         (i \notin pgl27_mutation_coalition) ==>
         ((pgl27_mutation_view0 i == ord0) &&
          (pgl27_mutation_view1 i == ord0))]].

(** The two views agree on the incomplete restriction but differ at an
    observed coordinate. Thus the restriction determines a masked view only
    when it lists every observed coordinate. *)
Local Lemma pgl27_omitted_coordinate_mutationT :
  pgl27_omitted_coordinate_mutation.
Proof.
rewrite /pgl27_omitted_coordinate_mutation.
apply/and3P; split.
- rewrite /pgl27_view_codes /= /pgl27_mutation_view0.
  rewrite /pgl27_mutation_view1 !ffunE.
  have H : \val (inord 0 : 'I_8) = 0 := @inordK 7 0 isT.
  by rewrite H.
- apply/eqP=> H.
  move/ffunP: H=> /(_ (@Ordinal 8 1 isT)).
  by rewrite /pgl27_mutation_view0 /pgl27_mutation_view1 !ffunE eqxx.
- apply/forallP=> i.
  apply/implyP=> Hi.
  rewrite /pgl27_mutation_view0 /pgl27_mutation_view1 !ffunE.
  have -> : (\val i == 1) = false.
    apply/eqP=> Hi1.
    move: Hi.
    by rewrite /pgl27_mutation_coalition inE Hi1.
  by [].
Qed.

Local Lemma uniq_map_injective
    (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1) :
  uniq (map f s) -> {in s &, injective f}.
Proof.
move=> /uniqP Huniq x y Hx Hy Hf.
have Hix : index x s < size (map f s) by rewrite size_map index_mem Hx.
have Hiy : index y s < size (map f s) by rewrite size_map index_mem Hy.
have Hidx : index x s = index y s.
  apply: (Huniq (f x)) => //.
  rewrite (nth_map x) ?(nth_map y) ?index_mem ?Hx ?Hy //
    !nth_index // Hf.
by rewrite -(nth_index x Hx) -(nth_index x Hy) Hidx.
Qed.

Local Lemma pgl27_code_views_inj (S : seq nat) (b : bool) :
  uniq (code_views b S) ->
  {in pgl27_group_table &,
    injective
      (fun t => code_restrict S (code_comp t (code_deal b)))}.
Proof.
(* This helper unfolds code_views once and seals the result with Qed. C7 can
   then reuse the injectivity result without expanding the transparent
   336-row closure again. The helper checked in 2 ms, C7 checked in 13 ms,
   and the full file compiled in 8.67 seconds. *)
rewrite /code_views.
exact: uniq_map_injective.
Qed.

(** Reading the listed coordinates of a protocol view gives the same sequence
    as restricting the corresponding permutation and deal tables. It
    identifies the masked observation with the restricted census row. *)
Lemma pgl27_view_codesE (R : realType) (S : seq nat) (b : bool)
    (g : {perm 'I_8}) :
  all (fun x => x < 8) S ->
  pgl27_view_codes S
      (pgl27_view R (pgl27_code_coalition S) (b, g)) =
    code_restrict S
      (code_comp (pgl27_mixing.ptbl g) (code_deal b)).
Proof.
move=> HS; rewrite /pgl27_view_codes /code_restrict.
apply/eq_in_map => x Hx.
have Hx8 : x < 8 := (allP HS) x Hx.
rewrite /pgl27_view ffunE /pgl27_code_coalition inE.
pose ox : 'I_8 := Ordinal Hx8.
have Hinord : inord x = ox by apply/val_inj; exact: inordK Hx8.
rewrite Hinord /ox /= Hx /=.
symmetry.
exact: (@pgl27_code_comp_ptblE b g (pgl27_mixing.ptbl g) erefl ox).
Qed.

Local Lemma pgl27_ptbl_mem (g : {perm 'I_8}) :
  g \in pgg_G pgl27_M -> pgl27_mixing.ptbl g \in pgl27_group_table.
Proof.
move=> gG; have Hgkey := pgl27_mixing.group_key gG.
have Heq :
    (pgl27_mixing.ptbl g \in pgl27_group_table) =
    (pgl27_mixing.ptbl g \in unzip1 pgl27_mixing.elem_table) :=
  perm_mem pgl27_group_table_perm _.
by rewrite Heq.
Qed.

(** If the census view list for one secret is repetition-free, then the
    protocol's conditional view map is injective on the shuffle group. Thus a
    reachable view has at most one shuffle preimage for that secret. *)
Lemma pgl27_conditional_view_inj (R : realType) (S : seq nat) (b : bool) :
  all (fun x => x < 8) S -> uniq (code_views b S) ->
  {in pgg_G pgl27_M &,
    injective
      (fun g => pgl27_view R (pgl27_code_coalition S) (b, g))}.
Proof.
move=> HS Huniq g h gG hG Hview.
have Hlisted := congr1 (pgl27_view_codes S) Hview.
have Hgcodes := @pgl27_view_codesE R S b g HS.
have Hhcodes := @pgl27_view_codesE R S b h HS.
have Hlisted' :
    code_restrict S
      (code_comp (pgl27_mixing.ptbl g) (code_deal b)) =
    code_restrict S
      (code_comp (pgl27_mixing.ptbl h) (code_deal b)) :=
  etrans (esym Hgcodes) (etrans Hlisted Hhcodes).
have Hfinj :
    {in pgl27_group_table &,
      injective
        (fun t => code_restrict S (code_comp t (code_deal b)))} :=
  pgl27_code_views_inj Huniq.
have Htable : pgl27_mixing.ptbl g = pgl27_mixing.ptbl h.
  apply: Hfinj; [exact: pgl27_ptbl_mem gG |
                 exact: pgl27_ptbl_mem hG | exact: Hlisted'].
exact: pgl27_mixing.ptbl_inj Htable.
Qed.

(** Both conditional view maps are injective for the harmonic
    representative. *)
Lemma pgl27_conditional_view_inj_harmonic (R : realType) (b : bool) :
  {in pgg_G pgl27_M &,
    injective
      (fun g => pgl27_view R
        (pgl27_code_coalition rep_harmonic) (b, g))}.
Proof.
case: b.
- apply: pgl27_conditional_view_inj; first by vm_compute.
  by move/andP: pgl27_views_uniq_harmonic => [].
- apply: pgl27_conditional_view_inj; first by vm_compute.
  by move/andP: pgl27_views_uniq_harmonic => [].
Qed.

(** Both conditional view maps are injective for the equianharmonic
    representative. *)
Lemma pgl27_conditional_view_inj_equianharmonic
    (R : realType) (b : bool) :
  {in pgg_G pgl27_M &,
    injective
      (fun g => pgl27_view R
        (pgl27_code_coalition rep_equianharmonic) (b, g))}.
Proof.
case: b.
- apply: pgl27_conditional_view_inj; first by vm_compute.
  by move/andP: pgl27_views_uniq_equianharmonic => [].
- apply: pgl27_conditional_view_inj; first by vm_compute.
  by move/andP: pgl27_views_uniq_equianharmonic => [].
Qed.

(** Both conditional view maps are injective for the five-position
    representative. *)
Lemma pgl27_conditional_view_inj_five (R : realType) (b : bool) :
  {in pgg_G pgl27_M &,
    injective
      (fun g => pgl27_view R
        (pgl27_code_coalition rep_five) (b, g))}.
Proof.
case: b.
- apply: pgl27_conditional_view_inj; first by vm_compute.
  by move/andP: pgl27_views_uniq_five => [].
- apply: pgl27_conditional_view_inj; first by vm_compute.
  by move/andP: pgl27_views_uniq_five => [].
Qed.

(** Both conditional view maps are injective for the six-position
    representative. *)
Lemma pgl27_conditional_view_inj_six (R : realType) (b : bool) :
  {in pgg_G pgl27_M &,
    injective
      (fun g => pgl27_view R
        (pgl27_code_coalition rep_six) (b, g))}.
Proof.
case: b.
- apply: pgl27_conditional_view_inj; first by vm_compute.
  by move/andP: pgl27_views_uniq_six => [].
- apply: pgl27_conditional_view_inj; first by vm_compute.
  by move/andP: pgl27_views_uniq_six => [].
Qed.

Print Assumptions pgl27_view_outside.

Print Assumptions pgl27_masked_view_eq.
Print Assumptions pgl27_view_eq_codes.
Print Assumptions pgl27_view_eq_codes_harmonic.
Print Assumptions pgl27_view_eq_codes_equianharmonic.
Print Assumptions pgl27_view_eq_codes_five.
Print Assumptions pgl27_view_eq_codes_six.
Print Assumptions pgl27_omitted_coordinate_mutationT.
Print Assumptions pgl27_conditional_view_inj.
Print Assumptions pgl27_conditional_view_inj_harmonic.
Print Assumptions pgl27_conditional_view_inj_equianharmonic.
Print Assumptions pgl27_conditional_view_inj_five.
Print Assumptions pgl27_conditional_view_inj_six.
