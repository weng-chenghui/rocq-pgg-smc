From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import design_privacy transitivity_privacy.
From pgg_smc Require Import psl211_group psl211_alldecks psl211_models.
From general_dealer_law_probe Require Import dealer_kernel_probe.
From general_dealer_law_probe Require Import carrier_transport_probe.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

(* psl211_alldecks_view expands to the laid deck and through it to the two
   132-row block tables of psl211_alldecks.v.  Sealing it keeps a failed
   unification from descending into those tables: a rule differing from the
   other side of the goal only in the chirality bit makes the matcher compare
   the two table literals, and it does not come back.  No step below needs the
   body of the reading; each names it and closes by exact.  The measurements
   are in STATUS.md. *)
Local Opaque psl211_alldecks_view.

Section UniformPushforwardLaws.

Variable R : realType.

(** fdistmap_prod_sectionE — two observations of an independent pair agree in
    law on the pair as soon as they agree in law on every section through a
    cut of positive mass.  It is the section form of fdistmap_prod_const, with
    observation in place of a constant target law, and it is what carries a
    per-cut count of deals up to the law of the whole sample. *)
Lemma fdistmap_prod_sectionE (D G V : finType)
    (PD : R.-fdist D) (PG : R.-fdist G)
    (f h : D -> G -> V) :
  (forall g, PG g != 0 ->
     fdistmap (fun d => f d g) PD =
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
(* a cut of zero mass contributes zero to both sums, so the premise is needed
   only where the cut law is supported *)
have [->|Hg] := eqVneq (PG g) 0; first by rewrite !mulr0.
move: (congr1 (fun q : R.-fdist V => q v) (H g Hg)).
rewrite !fdistmapE => Heq; congr (_ * _).
transitivity (\sum_(a in D | a \in preim (f^~ g) (pred1 v)) PD a).
- by apply: eq_bigl => i; rewrite inE.
- by rewrite Heq; apply: eq_bigl => i; rewrite inE.
Qed.

(** uniform_fdistmap_fiberTE — two maps out of a finite type whose fibers over
    every value are equinumerous push the uniform law on the whole type to the
    same law.  It is uniform_fdistmap_fiberE at the full set, with the fibers
    written as comprehensions over the type, which is the shape a count of the
    deals producing one reading takes. *)
Lemma uniform_fdistmap_fiberTE (X T : finType)
    (HX : (0 < #|[set: X]|)%N) (f0 f1 : X -> T) :
  (forall v, #|[set x : X | f0 x == v]| =
             #|[set x : X | f1 x == v]|) ->
  fdistmap f0 ((`U HX) : R.-fdist X) = fdistmap f1 (`U HX).
Proof.
(* f0 and f1 are still variables here, so the two comprehension shapes are
   reconciled without any instance's map being reachable by conversion. *)
have Hfull : forall (k : X -> T) (w : T),
    [set x in [set: X] | k x == w] = [set x : X | k x == w].
  by move=> k w; apply/setP => x; rewrite !inE.
move=> Hfib; apply: uniform_fdistmap_fiberE => v.
rewrite (Hfull f0 v) (Hfull f1 v); exact: Hfib v.
Qed.

End UniformPushforwardLaws.

Section ProductSectionMutation.

Variables (R : realType) (D G V : finType).
Variables (PD : R.-fdist D) (PG : R.-fdist G).
Variables (f h : D -> G -> V).
Hypothesis Hs : forall g, PG g != 0 ->
  fdistmap (fun d => f d g) PD = fdistmap (fun d => h d g) PD.

(** fdistmap_prod_sectionE_with_sections — the positive control for the
    mutation below: with the section-wise premise supplied, the same spelling
    is the equality of the two laws on the pair. *)
Definition fdistmap_prod_sectionE_with_sections :
  fdistmap (fun dg => f dg.1 dg.2) (PD `x PG) =
  fdistmap (fun dg => h dg.1 dg.2) (PD `x PG) :=
  @fdistmap_prod_sectionE R D G V PD PG f h Hs.

(* Expected failure: the section-wise premise dropped.  Without Hs the term
   still has that premise as an arrow in its type, so what is ascribed a bare
   equality of laws is a function into one. *)
Fail Definition fdistmap_prod_sectionE_without_sections :
  fdistmap (fun dg => f dg.1 dg.2) (PD `x PG) =
  fdistmap (fun dg => h dg.1 dg.2) (PD `x PG) :=
  @fdistmap_prod_sectionE R D G V PD PG f h.

End ProductSectionMutation.

Section PSLBridge.

Variable R : realType.
Local Notation dealT := psl211_deal.
Local Notation cutT := (pgg_gT psl211_M).
Local Notation seatT := ('I_12).
Local Notation cardT := ('I_12).
Local Notation viewT := ({ffun seatT -> cardT}).

(** psl211_deal_pos — the type of deal descriptions is inhabited, so it
    carries a uniform law. *)
Lemma psl211_deal_pos : (0 < #|[set: dealT]|)%N.
Proof.
apply/card_gt0P.
by exists (ord0, 1%g, 1%g); rewrite inE.
Qed.

(** psl211_dealer_delta — the all-decks dealer: whatever the chirality, the
    deal description is drawn uniformly and independently of it.  This is the
    instance's dealer kernel, and its independence of the chirality is what
    makes the averaged symmetry of psl211_alldecks available. *)
Definition psl211_dealer_delta (_ : bool) : R.-fdist dealT :=
  `U psl211_deal_pos.

(** psl211_dealer_nu — the cut law: a uniform element of the PSL(2,11) shuffle
    group. *)
Definition psl211_dealer_nu : R.-fdist cutT := `U psl211_G_pos.

(** psl211_dealerP — the instance's data placed in the dealer model's sample
    space, a chirality paired with a deal and a cut. *)
Definition psl211_dealerP : R.-fdist (bool * (dealT * cutT)) :=
  @dealer_shuffleP R bool dealT cutT
    (fdist_uniform card_bool) psl211_dealer_delta psl211_dealer_nu.

(** psl211_dealer_assoc — the reassociation of the instance's sample space,
    which pairs a chirality with a deal before pairing with the cut, into the
    dealer model's, which pairs the chirality with the pair.  It moves no
    mass. *)
Definition psl211_dealer_assoc
    (u : psl211_inputT * cutT) : bool * (dealT * cutT) :=
  (u.1.1, (u.1.2, u.2)).

(** psl211_dealerPE — the reassociation carries the instance's all-decks law
    to the dealer model's law at psl211_dealer_delta and psl211_dealer_nu.  Both
    are uniform on the same finite set written in two associations, so the
    identification costs nothing probabilistic and fixes which of the dealer
    model's three draws each of the instance's coordinates is. *)
Lemma psl211_dealerPE :
  fdistmap psl211_dealer_assoc (psl211_alldecksP R) = psl211_dealerP.
Proof.
apply: fdist_ext => -[b [d g]].
rewrite fdistmapE /psl211_dealer_assoc /psl211_alldecksP /psl211_dealerP.
rewrite dealer_shufflePE /psl211_dealer_delta /psl211_dealer_nu.
rewrite (big_pred1 ((b, d), g)) /=.
- rewrite !fdist_prodE /= !fdist_uniformE.
  have Hall : (b, d) \in [set: psl211_inputT] by rewrite inE.
  have Hdall : d \in [set: dealT] by rewrite inE.
  rewrite (fdist_uniform_supp_in R psl211_alldecks_gt0 Hall).
  rewrite (fdist_uniform_supp_in R psl211_deal_pos Hdall).
  by rewrite !cardsT card_prod card_bool natrM invfM mulrA.
- move=> [[b' d'] g']; rewrite !inE /= !xpair_eqE.
  by rewrite andbA.
Qed.

(** psl211_dealer_view C — the reading of a coalition C of seats, as a
    function of the dealer model's three coordinates.  It reads the chirality
    only through the deck the deal lays, which is why a symmetry between the two
    chiralities is enough to hide the chirality from C. *)
Definition psl211_dealer_view (C : {set seatT})
    (b : bool) (d : dealT) (g : cutT) : viewT :=
  psl211_alldecks_view C (b, d) g.

(** psl211_dealer_viewE — the dealer model's reading, composed with the
    reassociation, is the instance's reading. *)
Lemma psl211_dealer_viewE (C : {set seatT}) :
  @dealer_shuffle_view R bool dealT cutT viewT
    (fdist_uniform card_bool) psl211_dealer_delta psl211_dealer_nu
    (psl211_dealer_view C) \o psl211_dealer_assoc =
  (fun u => psl211_alldecks_view C u.1 u.2).
Proof. by apply: boolp.funext => -[[b d] g]. Qed.

(** psl211_dealer_secretE — the dealer model's secret, composed with the
    reassociation, is the instance's chirality. *)
Lemma psl211_dealer_secretE :
  @dealer_shuffle_secret R bool dealT cutT
    (fdist_uniform card_bool) psl211_dealer_delta psl211_dealer_nu
    \o psl211_dealer_assoc =
  psl211_alldecks_secret R.
Proof. by []. Qed.

(** psl211_dealer_bad_assoc — the reassociation with the chirality negated,
    used only to show that the identification of the secret is not automatic. *)
Definition psl211_dealer_bad_assoc
    (u : psl211_inputT * cutT) : bool * (dealT * cutT) :=
  (~~ u.1.1, (u.1.2, u.2)).

(* Expected failure: the secret identification under a negated chirality.  The
   two sides are convertible only if ~~ b and b are, so erefl does not
   typecheck against the ascribed equation. *)
Fail Definition psl211_dealer_bad_secretE :
  @dealer_shuffle_secret R bool dealT cutT
    (fdist_uniform card_bool) psl211_dealer_delta psl211_dealer_nu
    \o psl211_dealer_bad_assoc =
  psl211_alldecks_secret R := erefl.

(** psl211_dealer_mixed_law C b — the law of the coalition's reading at
    chirality b, averaged over the deal and the cut.  It is the quantity the
    dealer model's privacy premise asks to be the same for both chiralities. *)
Definition psl211_dealer_mixed_law (C : {set seatT}) (b : bool) :
    R.-fdist viewT :=
  fdistmap (fun dg => psl211_dealer_view C b dg.1 dg.2)
    ((psl211_dealer_delta b) `x psl211_dealer_nu).

(** psl211_dealer_sectionE — at one cut, the two chiralities send the uniform
    law on deal descriptions to the same law on what a coalition of at most
    five seats reads.  This is the per-cut deal count of psl211_alldecks read
    as an equality of laws, and it is the only place where the instance's laid
    deck enters the bridge. *)
Lemma psl211_dealer_sectionE (C : {set seatT}) (g : cutT) :
  (#|C| <= 5)%N ->
  fdistmap (fun d => psl211_dealer_view C true d g)
    ((`U psl211_deal_pos) : R.-fdist dealT) =
  fdistmap (fun d => psl211_dealer_view C false d g)
    ((`U psl211_deal_pos) : R.-fdist dealT).
Proof.
move=> HC; apply: uniform_fdistmap_fiberTE => v.
rewrite /psl211_dealer_view.
exact: (psl211_alldecks_per_cut_count C g v HC).
Qed.

(** psl211_dealer_mixed_lawE — the two chiralities have the same averaged
    reading law.  The per-cut equality is lifted to the pair of deal and cut,
    which is the dealer model's privacy premise at this instance. *)
Lemma psl211_dealer_mixed_lawE (C : {set seatT}) :
  (#|C| <= 5)%N ->
  psl211_dealer_mixed_law C false = psl211_dealer_mixed_law C true.
Proof.
move=> HC.
rewrite /psl211_dealer_mixed_law /psl211_dealer_delta /psl211_dealer_nu.
apply: (@fdistmap_prod_sectionE R dealT cutT viewT
  ((`U psl211_deal_pos) : R.-fdist dealT) psl211_dealer_nu
  (fun d g => psl211_dealer_view C false d g)
  (fun d g => psl211_dealer_view C true d g)) => g _.
symmetry; exact: (@psl211_dealer_sectionE C g HC).
Qed.

(** psl211_dealer_view_indep — in the dealer model's sample space, the reading
    of a coalition of at most five seats is independent of the chirality.  This
    is dealer_view_indep at the common averaged law, and it is exact: no
    approximation and no computational premise. *)
Lemma psl211_dealer_view_indep (C : {set seatT}) :
  (#|C| <= 5)%N ->
  psl211_dealerP |=
    @dealer_shuffle_view R bool dealT cutT viewT
      (fdist_uniform card_bool) psl211_dealer_delta psl211_dealer_nu
      (psl211_dealer_view C)
    _|_ @dealer_shuffle_secret R bool dealT cutT
      (fdist_uniform card_bool) psl211_dealer_delta psl211_dealer_nu.
Proof.
move=> HC.
apply: (@dealer_view_indep R bool dealT cutT viewT
  (fdist_uniform card_bool) psl211_dealer_delta psl211_dealer_nu
  (psl211_dealer_view C) (psl211_dealer_mixed_law C true)) => b _.
case: b; first exact: erefl.
exact: (@psl211_dealer_mixed_lawE C HC).
Qed.

(** psl211_alldecks_view_indep_via_dealer — the instance's own privacy
    statement, obtained by transporting the dealer model's independence back
    across the reassociation.  Nothing of the counting argument is redone here:
    the deal count of psl211_alldecks entered at psl211_dealer_sectionE and
    this step only changes the coordinates the same law is written in. *)
Lemma psl211_alldecks_view_indep_via_dealer (C : {set seatT}) :
  (#|C| <= 5)%N ->
  psl211_alldecksP R |=
    (fun u => psl211_alldecks_view C u.1 u.2)
    _|_ psl211_alldecks_secret R.
Proof.
move=> HC; have Hgen := @psl211_dealer_view_indep C HC.
rewrite -psl211_dealerPE in Hgen.
(* the two commuting equations are rewritten into the goal, not into Hgen: the
   goal names the reading only through psl211_alldecks_view, which is sealed,
   so the matcher never reaches the block tables underneath it *)
rewrite -(@psl211_dealer_viewE C) -psl211_dealer_secretE.
by apply/inde_RV_fdistmap.
Qed.

End PSLBridge.

(* Nothing after this point reasons about the reading, so the seal is
   released; Opaque is not section-scoped and would otherwise leak into every
   file that requires this one. *)
Local Transparent psl211_alldecks_view.

Print Assumptions fdistmap_prod_sectionE.
Print Assumptions uniform_fdistmap_fiberTE.
Print Assumptions psl211_dealerPE.
Print Assumptions psl211_dealer_sectionE.
Print Assumptions psl211_dealer_mixed_lawE.
Print Assumptions psl211_dealer_view_indep.
Print Assumptions psl211_alldecks_view_indep_via_dealer.
