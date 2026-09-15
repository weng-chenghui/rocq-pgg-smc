From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp ring lra reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_secrecy.
From pgg_smc Require Import pgl27_leakage_census pgl27_mixing.
From pgg_reconstruct Require Import design_privacy.
From pgl27_view_entropy_probe Require Import probe_view_definitions.
From pgl27_view_entropy_probe Require Import table_group_bridge.
From pgl27_view_entropy_probe Require Import view_collision_probability.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Lemma pgl27_ptbl_mem (g : {perm 'I_8}) :
  g \in pgg_G pgl27_M ->
  pgl27_mixing.ptbl g \in pgl27_group_table.
Proof.
move=> gG; have Hgkey := pgl27_mixing.group_key gG.
have Heq :
    (pgl27_mixing.ptbl g \in pgl27_group_table) =
    (pgl27_mixing.ptbl g \in unzip1 pgl27_mixing.elem_table) :=
  perm_mem pgl27_group_table_perm _.
by rewrite Heq.
Qed.

(** A masked protocol view is reachable from one secret exactly when its
    listed coordinates occur in that secret's census list. *)
Local Lemma pgl27_support_codesP (R : realType) (S : seq nat) (b : bool)
    (v : {ffun 'I_8 -> 'I_8}) :
  all (fun x => (x < 8)%N) S ->
  (forall i, i \notin pgl27_code_coalition S -> v i = ord0) ->
  ((exists2 g, g \in pgg_G pgl27_M &
      pgl27_view R (pgl27_code_coalition S) (b, g) = v) <->
   pgl27_view_codes S v \in code_views b S).
Proof.
move=> HS Hv; split.
- move=> [g gG Hgv].
  rewrite /code_views.
  apply/mapP; exists (pgl27_mixing.ptbl g); first exact: pgl27_ptbl_mem.
  rewrite -Hgv.
  exact: (@pgl27_view_codesE R S b g HS).
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
      pgl27_view R (pgl27_code_coalition S)
        (b, pgl27_table_perm k) i = ord0 :=
    @pgl27_view_outside R S (b, pgl27_table_perm k).
  have Heq := @pgl27_masked_view_eq S
    (pgl27_view R (pgl27_code_coalition S) (b, pgl27_table_perm k))
    v Hout Hv.
  apply: (proj2 Heq).
  rewrite (@pgl27_view_codesE R S b (pgl27_table_perm k) HS).
  rewrite pgl27_table_permE Hrow.
  exact: esym Ht.
Qed.

Local Definition pgl27_code_ambiguous
    (S : seq nat) (u : bool * 'I_336) : bool :=
  let t := nth [::] pgl27_group_table u.2 in
  let v := code_restrict S (code_comp t (code_deal u.1)) in
  (v \in code_views false S) && (v \in code_views true S).

(** The support-intersection event on a table row is the corresponding
    collision event in the nat census. *)
Local Lemma pgl27_table_ambiguousP (R : realType) (S : seq nat)
    (b : bool) (k : 'I_336) :
  all (fun x => (x < 8)%N) S ->
  (pgl27_view R (pgl27_code_coalition S) (b, pgl27_table_perm k)
       \in pgl27_ambiguous_views R S <->
   pgl27_code_ambiguous S (b, k)).
Proof.
move=> HS.
rewrite /pgl27_ambiguous_views inE.
rewrite /pgl27_code_ambiguous.
cbn beta iota zeta.
split.
- move=> /andP [Hfalse Htrue]; apply/andP; split.
  + have Hout : forall i, i \notin pgl27_code_coalition S ->
        pgl27_view R (pgl27_code_coalition S)
          (b, pgl27_table_perm k) i = ord0 :=
      @pgl27_view_outside R S (b, pgl27_table_perm k).
    have Hex : exists2 g, g \in pgg_G pgl27_M &
        pgl27_view R (pgl27_code_coalition S) (false, g) =
        pgl27_view R (pgl27_code_coalition S)
          (b, pgl27_table_perm k).
      move/exists_inP: Hfalse => [g gG /eqP Hg].
      by exists g.
    have Hmem :=
      (proj1 (@pgl27_support_codesP R S false _ HS Hout)) Hex.
    have Hcomp :
        code_comp (pgl27_mixing.ptbl (pgl27_table_perm k)) (code_deal b) =
        code_comp (nth [::] pgl27_group_table k) (code_deal b) :=
      congr1 (fun t => code_comp t (code_deal b)) (pgl27_table_permE k).
    have Hcr := congr1 (code_restrict S) Hcomp.
    have Hvc := @pgl27_view_codesE R S b (pgl27_table_perm k) HS.
    have Heq := etrans Hvc Hcr.
    move: Hmem.
    by rewrite Heq.
  + have Hout : forall i, i \notin pgl27_code_coalition S ->
        pgl27_view R (pgl27_code_coalition S)
          (b, pgl27_table_perm k) i = ord0 :=
      @pgl27_view_outside R S (b, pgl27_table_perm k).
    have Hex : exists2 g, g \in pgg_G pgl27_M &
        pgl27_view R (pgl27_code_coalition S) (true, g) =
        pgl27_view R (pgl27_code_coalition S)
          (b, pgl27_table_perm k).
      move/exists_inP: Htrue => [g gG /eqP Hg].
      by exists g.
    have Hmem :=
      (proj1 (@pgl27_support_codesP R S true _ HS Hout)) Hex.
    have Hcomp :
        code_comp (pgl27_mixing.ptbl (pgl27_table_perm k)) (code_deal b) =
        code_comp (nth [::] pgl27_group_table k) (code_deal b) :=
      congr1 (fun t => code_comp t (code_deal b)) (pgl27_table_permE k).
    have Hcr := congr1 (code_restrict S) Hcomp.
    have Hvc := @pgl27_view_codesE R S b (pgl27_table_perm k) HS.
    have Heq := etrans Hvc Hcr.
    move: Hmem.
    by rewrite Heq.
- move=> /andP [Hfalse Htrue]; apply/andP; split.
  + have Hout : forall i, i \notin pgl27_code_coalition S ->
        pgl27_view R (pgl27_code_coalition S)
          (b, pgl27_table_perm k) i = ord0 :=
      @pgl27_view_outside R S (b, pgl27_table_perm k).
    have Hcomp :
        code_comp (pgl27_mixing.ptbl (pgl27_table_perm k)) (code_deal b) =
        code_comp (nth [::] pgl27_group_table k) (code_deal b) :=
      congr1 (fun t => code_comp t (code_deal b)) (pgl27_table_permE k).
    have Hcr := congr1 (code_restrict S) Hcomp.
    have Hvc := @pgl27_view_codesE R S b (pgl27_table_perm k) HS.
    have Heq := etrans Hvc Hcr.
    have Hmem : pgl27_view_codes S
          (pgl27_view R (pgl27_code_coalition S)
            (b, pgl27_table_perm k)) \in code_views false S.
      move: Hfalse.
      by rewrite -Heq.
    have Hex :=
      (proj2 (@pgl27_support_codesP R S false _ HS Hout)) Hmem.
    apply/exists_inP.
    move: Hex => [g gG Hg].
    exists g; first exact: gG.
    exact/eqP.
  + have Hout : forall i, i \notin pgl27_code_coalition S ->
        pgl27_view R (pgl27_code_coalition S)
          (b, pgl27_table_perm k) i = ord0 :=
      @pgl27_view_outside R S (b, pgl27_table_perm k).
    have Hcomp :
        code_comp (pgl27_mixing.ptbl (pgl27_table_perm k)) (code_deal b) =
        code_comp (nth [::] pgl27_group_table k) (code_deal b) :=
      congr1 (fun t => code_comp t (code_deal b)) (pgl27_table_permE k).
    have Hcr := congr1 (code_restrict S) Hcomp.
    have Hvc := @pgl27_view_codesE R S b (pgl27_table_perm k) HS.
    have Heq := etrans Hvc Hcr.
    have Hmem : pgl27_view_codes S
          (pgl27_view R (pgl27_code_coalition S)
            (b, pgl27_table_perm k)) \in code_views true S.
      move: Htrue.
      by rewrite -Heq.
    have Hex :=
      (proj2 (@pgl27_support_codesP R S true _ HS Hout)) Hmem.
    apply/exists_inP.
    move: Hex => [g gG Hg].
    exists g; first exact: gG.
    exact/eqP.
Qed.

Local Definition pgl27_table_sample
    (u : bool * 'I_336) : bool * pgg_gT pgl27_M :=
  let: (b, k) := u in (b, pgl27_table_perm k).

Local Lemma pgl27_table_sample_inj : injective pgl27_table_sample.
Proof.
move=> [b k] [c l] H.
rewrite /pgl27_table_sample /= in H.
have Hbool : (b, pgl27_table_perm k) == (c, pgl27_table_perm l)
  by exact/eqP.
move: Hbool; rewrite xpair_eqE => /andP [/eqP Hb /eqP Hkl].
have Hk := pgl27_table_perm_inj Hkl.
apply/eqP; rewrite xpair_eqE; apply/andP; split; exact/eqP.
Qed.

Local Definition pgl27_ambiguous_samples
    (R : realType) (S : seq nat) : {set bool * pgg_gT pgl27_M} :=
  [set u | let: (b, g) := u in
     (pgl27_view R (pgl27_code_coalition S) (b, g)
        \in pgl27_ambiguous_views R S) &&
     (g \in pgg_G pgl27_M)].

Local Definition pgl27_code_ambiguous_samples
    (S : seq nat) : {set bool * 'I_336} :=
  [set u | pgl27_code_ambiguous S u].

(** The supported samples of the actual experiment are the injective image
    of the table samples satisfying the census collision event. *)
Local Lemma pgl27_ambiguous_samplesE (R : realType) (S : seq nat) :
  all (fun x => (x < 8)%N) S ->
  pgl27_ambiguous_samples R S =
    pgl27_table_sample @: pgl27_code_ambiguous_samples S.
Proof.
move=> HS; apply/setP => [[b g]].
rewrite /pgl27_ambiguous_samples inE /=.
apply/idP/imsetP.
- move=> /andP [Hamb gG].
  have [k Hkg] := pgl27_table_perm_surj gG.
  exists (b, k).
  + rewrite /pgl27_code_ambiguous_samples inE.
    apply: (proj1 (@pgl27_table_ambiguousP R S b k HS)).
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
        pgl27_view R (pgl27_code_coalition S)
          (c, pgl27_table_perm k) \in pgl27_ambiguous_views R S.
      apply: (proj2 (@pgl27_table_ambiguousP R S c k HS)).
      by move: Hcode; rewrite /pgl27_code_ambiguous_samples inE.
    move: Hb Hg => -> ->.
    exact: Hamb.
  + move: Hg => ->.
    exact: (pgl27_table_perm_mem k).
Qed.

Local Lemma card_pgl27_ambiguous_samples (R : realType) (S : seq nat) :
  all (fun x => (x < 8)%N) S ->
  #|pgl27_ambiguous_samples R S| = #|pgl27_code_ambiguous_samples S|.
Proof.
move=> HS; rewrite (pgl27_ambiguous_samplesE R HS).
exact: card_imset pgl27_table_sample_inj.
Qed.

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

Local Definition pgl27_code_view_at
    (S : seq nat) (b : bool) (k : 'I_336) : seq nat :=
  code_restrict S
    (code_comp (nth [::] pgl27_group_table (val k)) (code_deal b)).

Local Lemma pgl27_code_view_at_mem S b k :
  pgl27_code_view_at S b k \in code_views b S.
Proof.
rewrite /pgl27_code_view_at /code_views.
apply/mapP.
exists (nth [::] pgl27_group_table (val k)).
apply: mem_nth.
by rewrite pgl27_group_table_size; exact: ltn_ord k.
by [].
Qed.

Local Opaque pgl27_group_table.

Local Lemma pgl27_code_ambiguous_falseE S k :
  pgl27_code_ambiguous S (false, k) =
  (pgl27_code_view_at S false k \in code_views true S).
Proof.
change ((pgl27_code_view_at S false k \in code_views false S) &&
  (pgl27_code_view_at S false k \in code_views true S) =
  (pgl27_code_view_at S false k \in code_views true S)).
have Hfalse :
    (pgl27_code_view_at S false k \in code_views false S) = true :=
  @pgl27_code_view_at_mem S false k.
exact (@andb_idl
  (pgl27_code_view_at S false k \in code_views false S)
  (pgl27_code_view_at S false k \in code_views true S)
  (fun _ => Hfalse)).
Qed.

Local Lemma pgl27_code_ambiguous_trueE S k :
  pgl27_code_ambiguous S (true, k) =
  (pgl27_code_view_at S true k \in code_views false S).
Proof.
change ((pgl27_code_view_at S true k \in code_views false S) &&
  (pgl27_code_view_at S true k \in code_views true S) =
  (pgl27_code_view_at S true k \in code_views false S)).
have Htrue :
    (pgl27_code_view_at S true k \in code_views true S) = true :=
  @pgl27_code_view_at_mem S true k.
exact (@andb_idr
  (pgl27_code_view_at S true k \in code_views false S)
  (pgl27_code_view_at S true k \in code_views true S)
  (fun _ => Htrue)).
Qed.

Local Lemma card_pgl27_code_ambiguous_false S :
  uniq (code_views false S) ->
  uniq (code_views true S) ->
  #|[set k : 'I_336 | pgl27_code_ambiguous S (false, k)]| =
  pgl27_collisions S.
Proof.
move=> Hfalse Htrue.
  have Hset :
    [set k : 'I_336 | pgl27_code_ambiguous S (false, k)] =
    [set k : 'I_336 |
      pgl27_code_view_at S false k \in code_views true S].
  apply/setP => k.
  rewrite [in LHS]inE [in RHS]inE.
  exact (@pgl27_code_ambiguous_falseE S k).
rewrite Hset /pgl27_code_view_at.
rewrite (@card_ord_count (seq nat) 336
  pgl27_group_table [::]
  (fun t => code_restrict S (code_comp t (code_deal false))
    \in code_views true S)
  pgl27_group_table_size).
rewrite -(@count_map (seq nat) (seq nat)
  (fun t => code_restrict S (code_comp t (code_deal false)))
  (mem (code_views true S)) pgl27_group_table).
change (count (mem (code_views true S)) (code_views false S) =
  pgl27_collisions S).
rewrite /pgl27_collisions.
exact: count_mem_sym Hfalse Htrue.
Qed.

Local Lemma card_pgl27_code_ambiguous_true S :
  uniq (code_views false S) ->
  uniq (code_views true S) ->
  #|[set k : 'I_336 | pgl27_code_ambiguous S (true, k)]| =
  pgl27_collisions S.
Proof.
move=> Hfalse Htrue.
have Hset :
    [set k : 'I_336 | pgl27_code_ambiguous S (true, k)] =
    [set k : 'I_336 |
      pgl27_code_view_at S true k \in code_views false S].
  apply/setP => k.
  rewrite [in LHS]inE [in RHS]inE.
  exact (@pgl27_code_ambiguous_trueE S k).
rewrite Hset /pgl27_code_view_at.
rewrite (@card_ord_count (seq nat) 336
  pgl27_group_table [::]
  (fun t => code_restrict S (code_comp t (code_deal true))
    \in code_views false S)
  pgl27_group_table_size).
rewrite -(@count_map (seq nat) (seq nat)
  (fun t => code_restrict S (code_comp t (code_deal true)))
  (mem (code_views false S)) pgl27_group_table).
change (count (mem (code_views false S)) (code_views true S) =
  pgl27_collisions S).
by rewrite /pgl27_collisions.
Qed.

(** The two secret-indexed table samples contribute one copy of the
    cross-secret collision count each. *)
Local Lemma card_pgl27_code_ambiguous_samplesE S :
  uniq (code_views false S) ->
  uniq (code_views true S) ->
  #|pgl27_code_ambiguous_samples S| = 2 * pgl27_collisions S.
Proof.
move=> Hfalse Htrue.
rewrite /pgl27_code_ambiguous_samples -sum1_card.
have Hsplit :
    (\sum_(u in [set z | pgl27_code_ambiguous S z]) 1)%N =
    (\sum_(b : bool)
       \sum_(k in [set j : 'I_336 |
         pgl27_code_ambiguous S (b, j)]) 1)%N.
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
  (card_pgl27_code_ambiguous_true Hfalse Htrue)
  (card_pgl27_code_ambiguous_false Hfalse Htrue))).
rewrite addnn.
symmetry.
exact: mul2n.
Qed.

Local Lemma pgl27_code_ambiguous_samples_harmonic :
  #|pgl27_code_ambiguous_samples rep_harmonic| =
  2 * pgl27_collisions rep_harmonic.
Proof.
move/andP: pgl27_views_uniq_harmonic => [Hfalse Htrue].
exact: card_pgl27_code_ambiguous_samplesE Hfalse Htrue.
Qed.

Local Lemma pgl27_code_ambiguous_samples_equianharmonic :
  #|pgl27_code_ambiguous_samples rep_equianharmonic| =
  2 * pgl27_collisions rep_equianharmonic.
Proof.
move/andP: pgl27_views_uniq_equianharmonic => [Hfalse Htrue].
exact: card_pgl27_code_ambiguous_samplesE Hfalse Htrue.
Qed.

Local Lemma pgl27_code_ambiguous_samples_five :
  #|pgl27_code_ambiguous_samples rep_five| =
  2 * pgl27_collisions rep_five.
Proof.
move/andP: pgl27_views_uniq_five => [Hfalse Htrue].
exact: card_pgl27_code_ambiguous_samplesE Hfalse Htrue.
Qed.

Local Lemma pgl27_code_ambiguous_samples_six :
  #|pgl27_code_ambiguous_samples rep_six| =
  2 * pgl27_collisions rep_six.
Proof.
move/andP: pgl27_views_uniq_six => [Hfalse Htrue].
exact: card_pgl27_code_ambiguous_samplesE Hfalse Htrue.
Qed.

Local Lemma half_uniform_double (R : realType) (n : nat) :
  (((2%:R : R)^-1 * (336%:R : R)^-1) *+ (2 * n)) =
  n%:R / 336%:R.
Proof.
rewrite -mulr_natl natrM.
lra.
Qed.

Local Definition pgl27_ambiguous_indicator (R : realType) (S : seq nat) :
    {RV (pgl27P R) -> bool} :=
  fun u => pgl27_view R (pgl27_code_coalition S) u
             \in pgl27_ambiguous_views R S.

Local Lemma eqb_trueE (b : bool) : (b == true) = b.
Proof. by case: b. Qed.

Local Lemma pgl27_pr_ambiguous_indicatorE (R : realType) (S : seq nat) :
  `Pr[(pgl27_ambiguous_indicator R S) = true] =
  ((2%:R : R)^-1 * (336%:R : R)^-1) *+
    #|pgl27_ambiguous_samples R S|.
Proof.
rewrite pfwd1E /Pr.
under eq_bigl => u do
  rewrite inE /= /pgl27_ambiguous_indicator eqb_trueE.
rewrite -sumr_const big_mkcond [RHS]big_mkcond.
apply: eq_bigr => [[b g]] _.
rewrite /pgl27_ambiguous_samples [in RHS]inE /=.
case: (pgl27_view R (pgl27_code_coalition S) (b, g)
  \in pgl27_ambiguous_views R S); last by [].
rewrite andTb /pgl27P fdist_prodE /= fdist_uniformE card_bool.
case: ifPn => gG.
- rewrite fdist_uniform_supp_in // pgl27_card.
  by [].
- by rewrite fdist_uniform_supp_notin // mulr0.
Qed.

Local Lemma pgl27_pr_ambiguousE (R : realType) (S : seq nat) :
  `Pr[(pgl27_view R (pgl27_code_coalition S))
        \in pgl27_ambiguous_views R S] =
  `Pr[(pgl27_ambiguous_indicator R S) = true].
Proof.
rewrite pr_inE pfwd1E; congr Pr; apply/setP => u.
rewrite [in LHS]inE [in RHS]inE /=
  /pgl27_ambiguous_indicator eqb_trueE.
reflexivity.
Qed.

Local Lemma pgl27_ambiguous_probabilityE (R : realType) (S : seq nat) :
  all (fun x => (x < 8)%N) S ->
  uniq (code_views false S) ->
  uniq (code_views true S) ->
  `Pr[(pgl27_view R (pgl27_code_coalition S))
        \in pgl27_ambiguous_views R S] =
  (pgl27_collisions S)%:R / 336%:R.
Proof.
move=> HS Hfalse Htrue.
rewrite pgl27_pr_ambiguousE pgl27_pr_ambiguous_indicatorE.
rewrite (card_pgl27_ambiguous_samples R HS).
rewrite (card_pgl27_code_ambiguous_samplesE Hfalse Htrue).
exact: half_uniform_double.
Qed.

(** Under the actual uniform secret and PGL shuffle distribution, the
    harmonic ambiguous-view probability is its census collision ratio. *)
Lemma pgl27_ambiguous_probability_harmonicE (R : realType) :
  `Pr[(pgl27_view R (pgl27_code_coalition rep_harmonic))
        \in pgl27_ambiguous_views R rep_harmonic] =
  (pgl27_collisions rep_harmonic)%:R / 336%:R.
Proof.
move/andP: pgl27_views_uniq_harmonic => [Hfalse Htrue].
apply: (@pgl27_ambiguous_probabilityE R rep_harmonic).
- by vm_compute.
- exact: Hfalse.
- exact: Htrue.
Qed.

(** Under the actual uniform secret and PGL shuffle distribution, the
    equianharmonic ambiguous-view probability is its census collision ratio. *)
Lemma pgl27_ambiguous_probability_equianharmonicE (R : realType) :
  `Pr[(pgl27_view R (pgl27_code_coalition rep_equianharmonic))
        \in pgl27_ambiguous_views R rep_equianharmonic] =
  (pgl27_collisions rep_equianharmonic)%:R / 336%:R.
Proof.
move/andP: pgl27_views_uniq_equianharmonic => [Hfalse Htrue].
apply: (@pgl27_ambiguous_probabilityE R rep_equianharmonic).
- by vm_compute.
- exact: Hfalse.
- exact: Htrue.
Qed.

(** Under the actual uniform secret and PGL shuffle distribution, the
    five-position ambiguous-view probability is its census collision ratio. *)
Lemma pgl27_ambiguous_probability_fiveE (R : realType) :
  `Pr[(pgl27_view R (pgl27_code_coalition rep_five))
        \in pgl27_ambiguous_views R rep_five] =
  (pgl27_collisions rep_five)%:R / 336%:R.
Proof.
move/andP: pgl27_views_uniq_five => [Hfalse Htrue].
apply: (@pgl27_ambiguous_probabilityE R rep_five).
- by vm_compute.
- exact: Hfalse.
- exact: Htrue.
Qed.

(** Under the actual uniform secret and PGL shuffle distribution, the
    six-position ambiguous-view probability is its census collision ratio. *)
Lemma pgl27_ambiguous_probability_sixE (R : realType) :
  `Pr[(pgl27_view R (pgl27_code_coalition rep_six))
        \in pgl27_ambiguous_views R rep_six] =
  (pgl27_collisions rep_six)%:R / 336%:R.
Proof.
move/andP: pgl27_views_uniq_six => [Hfalse Htrue].
apply: (@pgl27_ambiguous_probabilityE R rep_six).
- by vm_compute.
- exact: Hfalse.
- exact: Htrue.
Qed.

Local Lemma pgl27_ambiguous_probability_harmonic_not_definitional
    (R : realType) :
  `Pr[(pgl27_view R (pgl27_code_coalition rep_harmonic))
        \in pgl27_ambiguous_views R rep_harmonic] =
  (pgl27_collisions rep_harmonic)%:R / 336%:R.
Proof.
Fail reflexivity.
exact: pgl27_ambiguous_probability_harmonicE.
Qed.

Local Lemma pgl27_ambiguous_probability_harmonic_neq_neighbor :
  pgl27_collisions rep_harmonic != 97.
Proof. exact: pgl27_collisions_harmonic_neq. Qed.

Local Lemma pgl27_ambiguous_probability_equianharmonic_neq_neighbor :
  pgl27_collisions rep_equianharmonic != 96.
Proof. exact: pgl27_collisions_equianharmonic_neq. Qed.

Local Lemma pgl27_ambiguous_probability_five_neq_neighbor :
  pgl27_collisions rep_five != 35.
Proof. exact: pgl27_collisions_five_neq. Qed.

Local Lemma pgl27_ambiguous_probability_six_neq_neighbor :
  pgl27_collisions rep_six != 0.
Proof. exact: pgl27_collisions_six_neq. Qed.

Print Assumptions pgl27_ambiguous_probability_harmonicE.
Print Assumptions pgl27_ambiguous_probability_equianharmonicE.
Print Assumptions pgl27_ambiguous_probability_fiveE.
Print Assumptions pgl27_ambiguous_probability_sixE.
Print Assumptions pgl27_ambiguous_probability_harmonic_not_definitional.
Print Assumptions pgl27_ambiguous_probability_harmonic_neq_neighbor.
Print Assumptions pgl27_ambiguous_probability_equianharmonic_neq_neighbor.
Print Assumptions pgl27_ambiguous_probability_five_neq_neighbor.
Print Assumptions pgl27_ambiguous_probability_six_neq_neighbor.
