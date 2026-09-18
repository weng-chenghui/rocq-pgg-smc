From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import design_privacy transitivity_privacy.
From pgg_smc Require Import psl211_group psl211_alldecks psl211_models.

Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

(* psl211_alldecks_view expands to the laid deck and through it to the two
   132-row block tables of psl211_alldecks.v.  Sealing it keeps a failed
   unification from descending into those tables: a rule differing from the
   other side of the goal only in the chirality bit makes the matcher compare
   the two table literals, and it does not come back.  Measured 2026-09-18 in
   this same goal: rewrite Htrue, move: Htrue => -> and rewrite Htrue Hfalse
   each hit a 30 s Timeout, against 0.01 s for every other sentence.  No step
   below needs the view's body; each names it and closes by exact. *)
Local Opaque psl211_alldecks_view.

Section GenericCopy.

Variables (R0 : realType) (S0 D0 G0 V0 : finType).
Variable P0 : R0.-fdist S0.
Variable delta0 : S0 -> R0.-fdist D0.
Variable nu0 : R0.-fdist G0.

Definition psl_bridge_dealerP : R0.-fdist (S0 * (D0 * G0)) :=
  P0 `X (fun s => (delta0 s) `x nu0).

Definition psl_bridge_secret : {RV psl_bridge_dealerP -> S0} :=
  fun u => u.1.

Definition psl_bridge_view (view : S0 -> D0 -> G0 -> V0) :
    {RV psl_bridge_dealerP -> V0} :=
  fun u => view u.1 u.2.1 u.2.2.

Lemma psl_bridge_view_indep (view : S0 -> D0 -> G0 -> V0)
    (mu : R0.-fdist V0) :
  (forall s, P0 s != 0 ->
     fdistmap (fun dg => view s dg.1 dg.2)
       ((delta0 s) `x nu0) = mu) ->
  psl_bridge_dealerP |= psl_bridge_view view _|_ psl_bridge_secret.
Proof.
move=> Hview.
rewrite /psl_bridge_dealerP /psl_bridge_view /psl_bridge_secret.
apply: (inde_prod_kernel_fst (mu := mu)) => s Hs.
exact: Hview Hs.
Qed.

Lemma psl_bridge_pullback (A0 B0 TA0 TB0 : finType)
    (Q0 : R0.-fdist A0) (f0 : A0 -> B0)
    (X0 : B0 -> TA0) (Y0 : B0 -> TB0) :
  fdistmap f0 Q0 |= X0 _|_ Y0 ->
  Q0 |= (X0 \o f0) _|_ (Y0 \o f0).
Proof.
move=> H x y; move: (H x y).
rewrite -!dist_of_RVE /dist_of_RV !fdistmap_comp.
by [].
Qed.

(** psl_bridge_pullback_eq — independence transported along a reindexing of
    the sample space, with the two composites supplied as equations instead
    of left to appear in the conclusion.  An instance names its coalition
    reading and its secret as functions of its own sample space, not as
    composites, so the transport is stated in the form the instance already
    has; the two equations are where the instance says which of its data the
    generic view and the generic secret are. *)
Lemma psl_bridge_pullback_eq (A0 B0 TA0 TB0 : finType)
    (Q0 : R0.-fdist A0) (f0 : A0 -> B0)
    (X0 : B0 -> TA0) (Y0 : B0 -> TB0)
    (X1 : A0 -> TA0) (Y1 : A0 -> TB0) :
  X0 \o f0 = X1 -> Y0 \o f0 = Y1 ->
  fdistmap f0 Q0 |= X0 _|_ Y0 ->
  Q0 |= X1 _|_ Y1.
Proof. by move=> <- <-; exact: psl_bridge_pullback. Qed.

Lemma fdistmap_prod_sections (D G V : finType)
    (PD : R0.-fdist D) (PG : R0.-fdist G)
    (f h : D -> G -> V) :
  (forall g, fdistmap (fun d => f d g) PD =
             fdistmap (fun d => h d g) PD) ->
  fdistmap (fun dg => f dg.1 dg.2) (PD `x PG) =
  fdistmap (fun dg => h dg.1 dg.2) (PD `x PG).
Proof.
move=> H; apply: fdist_ext => v; rewrite !fdistmapE.
rewrite !(partition_big snd xpredT) //=.
apply: eq_bigr => g _.
rewrite (reindex_onto (fun d : D => (d, g)) (fun i => i.1));
  last by move=> [d g'] /= /andP[_ /eqP ->].
under eq_bigl => d do rewrite /= !inE eqxx andbT.
under eq_bigr => d _ do rewrite fdist_prodE /=.
rewrite [in RHS](reindex_onto (fun d : D => (d, g)) (fun i => i.1));
  last by move=> [d g'] /= /andP[_ /eqP ->].
under [in RHS]eq_bigl => d do rewrite /= !inE eqxx andbT.
under [in RHS]eq_bigr => d _ do rewrite fdist_prodE /=.
under [in LHS]eq_bigl => d do rewrite /= eqxx andbT.
under [in RHS]eq_bigl => d do rewrite /= eqxx andbT.
rewrite -!big_distrl /=.
move: (congr1 (fun q : R0.-fdist V => q v) (H g)).
rewrite !fdistmapE => Heq; congr (_ * _).
transitivity (\sum_(a in D | a \in preim (f^~ g) (pred1 v)) PD a).
- by apply: eq_bigl => i; rewrite inE.
- rewrite Heq; apply: eq_bigl => i; by rewrite inE.
Qed.

Fail Definition fdistmap_prod_sections_without_sections
    (D G V : finType) (PD : R0.-fdist D) (PG : R0.-fdist G)
    (f h : D -> G -> V) :
  fdistmap (fun dg => f dg.1 dg.2) (PD `x PG) =
  fdistmap (fun dg => h dg.1 dg.2) (PD `x PG) :=
  fdistmap_prod_sections PD PG f h.

(** uniform_fdistmap_sectionsT — two maps out of a finite type whose fibers
    over every value are equinumerous push the uniform law on that type to
    the same law.  It is uniform_fdistmap_fiberE with the fibers written as
    comprehensions over the whole type, which is the shape a count of the
    deals producing one reading takes, so a per-cut deal count becomes an
    equality of the two chiralities' laid-deck laws. *)
Lemma uniform_fdistmap_sectionsT (D V : finType)
    (HD : (0 < #|[set: D]|)%N) (f h : D -> V) :
  (forall v, #|[set d : D | f d == v]| =
             #|[set d : D | h d == v]|) ->
  fdistmap f ((`U HD) : R0.-fdist D) = fdistmap h (`U HD).
Proof.
(* f and h are still variables here, so the two comprehension shapes are
   reconciled without any instance's map being reachable by conversion. *)
have Hfull : forall (k : D -> V) (w : V),
    [set d in [set: D] | k d == w] = [set d : D | k d == w].
  by move=> k w; apply/setP => d; rewrite !inE.
move=> Hfib; apply: uniform_fdistmap_fiberE => v.
rewrite (Hfull f v) (Hfull h v); exact: Hfib v.
Qed.

End GenericCopy.

Section PSLBridge.

Variable R : realType.
Local Notation dealT := psl211_deal.
Local Notation cutT := (pgg_gT psl211_M).
Local Notation seatT := ('I_12).
Local Notation cardT := ('I_12).
Local Notation viewT := ({ffun seatT -> cardT}).

Lemma psl_deal_pos : (0 < #|[set: dealT]|)%N.
Proof.
apply/card_gt0P.
by exists (ord0, 1%g, 1%g); rewrite inE.
Qed.

Definition psl_delta (_ : bool) : R.-fdist dealT := `U psl_deal_pos.

Definition psl_nu : R.-fdist cutT := `U psl211_G_pos.

Definition psl_genericP : R.-fdist (bool * (dealT * cutT)) :=
  psl_bridge_dealerP R bool dealT cutT
    (fdist_uniform card_bool) psl_delta psl_nu.

Definition psl_assoc
    (u : psl211_inputT * cutT) : bool * (dealT * cutT) :=
  (u.1.1, (u.1.2, u.2)).

Lemma psl_law_E :
  fdistmap psl_assoc (psl211_alldecksP R) = psl_genericP.
Proof.
apply: fdist_ext => -[b [d g]].
rewrite fdistmapE /psl_assoc /psl211_alldecksP /psl_genericP.
rewrite /psl_bridge_dealerP /psl_delta /psl_nu !fdist_prodE.
rewrite (big_pred1 ((b, d), g)) /=.
- rewrite !fdist_prodE /= !fdist_uniformE.
  have Hall : (b, d) \in [set: psl211_inputT] by rewrite inE.
  have Hdall : d \in [set: dealT] by rewrite inE.
  rewrite (fdist_uniform_supp_in R psl211_alldecks_gt0 Hall).
  rewrite (fdist_uniform_supp_in R psl_deal_pos Hdall).
  by rewrite !cardsT card_prod card_bool natrM invfM mulrA.
- move=> [[b' d'] g']; rewrite !inE /= !xpair_eqE.
  by rewrite andbA.
Qed.

Definition psl_generic_view (C : {set seatT})
    (b : bool) (d : dealT) (g : cutT) : viewT :=
  psl211_alldecks_view C (b, d) g.

Lemma psl_view_square (C : {set seatT}) :
  @psl_bridge_view R bool dealT cutT viewT
    (fdist_uniform card_bool) psl_delta psl_nu
    (psl_generic_view C) \o psl_assoc =
  (fun u => psl211_alldecks_view C u.1 u.2).
Proof. by apply: boolp.funext => -[[b d] g]. Qed.

Lemma psl_secret_square :
  @psl_bridge_secret R bool dealT cutT
    (fdist_uniform card_bool) psl_delta psl_nu \o psl_assoc =
  psl211_alldecks_secret R.
Proof. by []. Qed.

Definition psl_bad_assoc
    (u : psl211_inputT * cutT) : bool * (dealT * cutT) :=
  (~~ u.1.1, (u.1.2, u.2)).

Fail Definition psl_bad_secret_square :
  @psl_bridge_secret R bool dealT cutT
    (fdist_uniform card_bool) psl_delta psl_nu \o psl_bad_assoc =
  psl211_alldecks_secret R := erefl.

Definition psl_mixed_law (C : {set seatT}) (b : bool) :
    R.-fdist viewT :=
  fdistmap (fun dg => psl_generic_view C b dg.1 dg.2)
    ((psl_delta b) `x psl_nu).

(** psl_section_law — at one cut, the two chiralities send the uniform law on
    deck descriptions to the same law on what a coalition of at most five
    seats reads.  This is the per-cut deal count of psl211_alldecks read as an
    equality of laws, and it is the only place where the instance's laid deck
    enters the bridge. *)
Lemma psl_section_law (C : {set seatT}) (g : cutT) :
  (#|C| <= 5)%N ->
  fdistmap (fun d => psl_generic_view C true d g)
    ((`U psl_deal_pos) : R.-fdist dealT) =
  fdistmap (fun d => psl_generic_view C false d g)
    ((`U psl_deal_pos) : R.-fdist dealT).
Proof.
move=> HC; apply: uniform_fdistmap_sectionsT => v.
rewrite /psl_generic_view.
exact: (psl211_alldecks_per_cut_count C g v HC).
Qed.

Lemma psl_mixed_lawE (C : {set seatT}) :
  (#|C| <= 5)%N -> psl_mixed_law C false = psl_mixed_law C true.
Proof.
move=> HC; rewrite /psl_mixed_law /psl_delta /psl_nu.
apply: (@fdistmap_prod_sections R dealT cutT viewT
  ((`U psl_deal_pos) : R.-fdist dealT) psl_nu
  (fun d g => psl_generic_view C false d g)
  (fun d g => psl_generic_view C true d g)) => g.
symmetry; exact: (psl_section_law C g HC).
Qed.

Lemma psl_generic_indep (C : {set seatT}) :
  (#|C| <= 5)%N ->
  psl_genericP |=
    @psl_bridge_view R bool dealT cutT viewT
      (fdist_uniform card_bool) psl_delta psl_nu
      (psl_generic_view C)
    _|_ @psl_bridge_secret R bool dealT cutT
      (fdist_uniform card_bool) psl_delta psl_nu.
Proof.
move=> HC.
apply: (@psl_bridge_view_indep R bool dealT cutT viewT
  (fdist_uniform card_bool) psl_delta psl_nu
  (psl_generic_view C) (psl_mixed_law C true)) => b _.
case: b; first exact: erefl.
exact: (psl_mixed_lawE C HC).
Qed.

Lemma psl_indep_via_generic (C : {set seatT}) :
  (#|C| <= 5)%N ->
  psl211_alldecksP R |=
    (fun u => psl211_alldecks_view C u.1 u.2)
    _|_ psl211_alldecks_secret R.
Proof.
move=> HC; have Hgen := psl_generic_indep C HC.
rewrite -psl_law_E in Hgen.
exact: (@psl_bridge_pullback_eq R
  (psl211_inputT * cutT)%type
  (bool * (dealT * cutT))%type viewT bool
  (psl211_alldecksP R) psl_assoc
  (@psl_bridge_view R bool dealT cutT viewT
    (fdist_uniform card_bool) psl_delta psl_nu
    (psl_generic_view C))
  (@psl_bridge_secret R bool dealT cutT
    (fdist_uniform card_bool) psl_delta psl_nu)
  _ _ (psl_view_square C) psl_secret_square Hgen).
Qed.

End PSLBridge.

Print Assumptions psl_law_E.
Print Assumptions psl_section_law.
Print Assumptions psl_mixed_lawE.
Print Assumptions psl_generic_indep.
Print Assumptions psl_indep_via_generic.
