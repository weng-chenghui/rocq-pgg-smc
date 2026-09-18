From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import action div bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface psl211_group psl211_alldecks.
From general_dealer_law_probe Require Import dealer_kernel_probe.
From general_dealer_law_probe Require Import psl211_alldecks_bridge.
From general_dealer_law_probe Require Import psl211_per_deck_counter.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Local Notation cutT := (pgg_gT psl211_M).
Local Notation viewT := ({ffun 'I_12 -> 'I_12}).

(* The reading is sealed again here: Opaque is not carried across a file
   boundary, and the two chiralities of psl211_alldecks_view differ only in a
   boolean under a constant whose body reaches the block tables. *)
Local Opaque psl211_alldecks_view.

(* psl211_perdeck_raw_count is sealed for the whole file: nothing below needs
   its body, psl211_perdeck_raw_countE supplies both values, and leaving it
   transparent lets a unifier that falls back to conversion evaluate the count
   over the 660 tabulated shuffles. *)
Local Opaque psl211_perdeck_raw_count.

(** uniform_fdistmap_pointE — the mass a pushed-forward uniform law gives to a
    value is the size of that value's fiber inside the support, divided by the
    size of the support.  It is the point form of uniform_fdistmap_fiberE, and
    it is what turns a difference of two fiber counts into a difference of two
    laws, which is the direction fiberE does not give. *)
Lemma uniform_fdistmap_pointE (R : realType) (X T : finType)
    (A : {set X}) (HA : (0 < #|A|)%N) (f : X -> T) (v : T) :
  (fdistmap f ((`U HA) : R.-fdist X)) v =
    (#|A|%:R)^-1 *+ #|[set x in A | f x == v]| :> R.
Proof.
rewrite fdistmapE -sumr_const big_mkcond [RHS]big_mkcond /=.
apply: eq_bigr => x _; rewrite !inE /=.
case: (f x == v); last by rewrite andbF.
rewrite andbT; case: ifPn => xA.
  by rewrite fdist_uniform_supp_in.
by rewrite fdist_uniform_supp_notin.
Qed.

(** psl211_perdeck_massE b — at the deal psl211_perdeck_deal, the law of what
    the coalition reads under chirality b gives psl211_perdeck_view the mass of
    its fiber of cuts over the order of the shuffle group. *)
Lemma psl211_perdeck_massE (R : realType) (b : bool) :
  (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
       (b, psl211_perdeck_deal) g)
     ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view =
  (#|pgg_G psl211_M|%:R)^-1 *+ #|psl211_perdeck_fiber b| :> R.
Proof. by rewrite /psl211_perdeck_fiber uniform_fdistmap_pointE. Qed.

(** psl211_perdeck_law_neq — at the single deal psl211_perdeck_deal the two
    chiralities send the uniform cut law to two different laws on what the
    coalition reads.  The averaged symmetry that psl211_alldecks establishes
    is therefore genuinely a statement about the average over deals: fixing
    one deal destroys it, and with it the per-deck route to privacy. *)
Lemma psl211_perdeck_law_neq (R : realType) :
  fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
      (true, psl211_perdeck_deal) g)
    ((`U psl211_G_pos) : R.-fdist cutT) !=
  fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
      (false, psl211_perdeck_deal) g)
    ((`U psl211_G_pos) : R.-fdist cutT).
Proof.
(* each mass is pinned to its value in a goal naming one chirality only, and
   the two are brought together in term mode, so no tactic ever searches a
   goal in which the two chiralities could be matched against each other *)
have [Ht Hf] := psl211_perdeck_raw_countE.
have H0 : #|psl211_perdeck_fiber true| = 0 :=
  etrans (psl211_perdeck_fiberE true) Ht.
have H1 : #|psl211_perdeck_fiber false| = 1 :=
  etrans (psl211_perdeck_fiberE false) Hf.
have Lt : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
      (true, psl211_perdeck_deal) g)
    ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view = 0 :> R.
  by rewrite psl211_perdeck_massE H0 mulr0n.
have Lf : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
      (false, psl211_perdeck_deal) g)
    ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view =
  (#|pgg_G psl211_M|%:R)^-1 :> R.
  by rewrite psl211_perdeck_massE H1 mulr1n.
apply/negP => /eqP Heq.
have Hz : (0 : R) = (#|pgg_G psl211_M|%:R)^-1 :=
  etrans (esym Lt)
    (etrans (congr1 (fun q : R.-fdist viewT => q psl211_perdeck_view) Heq) Lf).
have : (#|pgg_G psl211_M|%:R)^-1 == 0 :> R by rewrite -Hz.
rewrite invr_eq0 pnatr_eq0 => /eqP Hcard.
by move: psl211_G_pos; rewrite Hcard.
Qed.

(** psl211_perdeck_no_common_law — no law on readings is the law of the
    coalition's reading at psl211_perdeck_deal under both chiralities.  This is
    the second premise of dealer_shuffle_view_indep_of_deck written at
    PSL(2,11), for an arbitrary validity predicate that accepts that deal, and
    it has no solution, so the per-deck condition of
    dealer_shuffle_view_indep_of_deck is not available at this deal. *)
Lemma psl211_perdeck_no_common_law (R : realType)
    (valid : bool -> psl211_deal -> bool) (mu : R.-fdist viewT) :
  (forall b : bool, valid b psl211_perdeck_deal) ->
  ~ (forall (b : bool) (d : psl211_deal),
       (fdist_uniform card_bool : R.-fdist bool) b != 0 -> valid b d ->
       fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
           (b, d) g) ((`U psl211_G_pos) : R.-fdist cutT) = mu).
Proof.
move=> Hvalid Hlaw.
have Hpos : forall b : bool,
    (fdist_uniform card_bool : R.-fdist bool) b != 0.
  (* card_bool is needed: done cannot evaluate #|bool| on its own *)
  by move=> b; rewrite fdist_uniformE invr_eq0 pnatr_eq0 card_bool.
move/negP: (psl211_perdeck_law_neq R); apply; apply/eqP.
exact: etrans (Hlaw true psl211_perdeck_deal (Hpos true) (Hvalid true))
  (esym (Hlaw false psl211_perdeck_deal (Hpos false) (Hvalid false))).
Qed.

(** psl211_dealer_valid_forced — the all-decks dealer gives every deal
    description positive mass, so the first premise of
    dealer_shuffle_view_indep_of_deck cannot exclude any deal: a validity
    predicate satisfying it accepts psl211_perdeck_deal at both chiralities.
    This is what stops the per-deck route from being repaired by a narrower
    notion of validity. *)
Lemma psl211_dealer_valid_forced (R : realType)
    (valid : bool -> psl211_deal -> bool) :
  (forall (b : bool) (d : psl211_deal),
     psl211_dealer_delta R b d != 0 -> valid b d) ->
  forall b : bool, valid b psl211_perdeck_deal.
Proof.
move=> Hvalid b; apply: Hvalid.
by rewrite /psl211_dealer_delta fdist_uniform_supp_neq0 inE.
Qed.

(** psl211_dealer_view_indep_of_deck_unsat — at PSL(2,11) under its own dealer
    law the two premises of dealer_shuffle_view_indep_of_deck have no common
    solution, for every validity predicate and every candidate reading law.
    So of the model's two conditions only the mixed-law condition of
    dealer_shuffle_view_indep is available to this instance, and the uniform
    deal law is the law that meets it. *)
Lemma psl211_dealer_view_indep_of_deck_unsat (R : realType)
    (valid : bool -> psl211_deal -> bool) (mu : R.-fdist viewT) :
  (forall (b : bool) (d : psl211_deal),
     psl211_dealer_delta R b d != 0 -> valid b d) ->
  ~ (forall (b : bool) (d : psl211_deal),
       (fdist_uniform card_bool : R.-fdist bool) b != 0 -> valid b d ->
       fdistmap (psl211_dealer_view psl211_perdeck_coalition b d)
         (psl211_dealer_nu R) = mu).
Proof.
move=> Hvalid Hlaw.
apply: (@psl211_perdeck_no_common_law R valid mu
  (psl211_dealer_valid_forced Hvalid)).
exact: Hlaw.
Qed.

(** psl211_fixed_deal_delta — the degenerate dealer that lays one and the same
    deal description whatever the chirality.  It is a dealer kernel in the
    sense of dealer_shuffleP, and it is named here so that the general model
    can be asked whether it claims privacy for it.  The kernel does not depend
    on the chirality at all, and what the coalition reads still does, because
    psl211_alldecks_seq reads the class table at the chirality: one deal
    description names two different decks. *)
Definition psl211_fixed_deal_delta (R : realType) (_ : bool) :
    R.-fdist psl211_deal := fdist1 psl211_perdeck_deal.

(** psl211_fixed_dealP — the dealer law at that kernel: a uniform chirality, a
    fixed deal description, a uniform shuffle. *)
Definition psl211_fixed_dealP (R : realType) :
    R.-fdist (bool * (psl211_deal * cutT)) :=
  @dealer_shuffleP R bool psl211_deal cutT (fdist_uniform card_bool)
    (@psl211_fixed_deal_delta R) (`U psl211_G_pos).

(** psl211_fixed_deal_view_dep — under that dealer law the reading of three
    seats is NOT independent of the chirality.  This is what entitles the
    paper to say that privacy is a property of the dealer law and not of the
    protocol alone: the shuffle group, the design and the coalition are the
    ones PSL(2,11) uses, only the dealer changed, and the conclusion fails.
    Read together with psl211_alldecks_view_indep_via_dealer it says that for
    PSL(2,11) privacy depends on which deal law the dealer uses: the uniform
    one delivers it, and the point mass at psl211_perdeck_deal does not.  What
    is NOT shown here is that a hidden uniform deal leaks: the deal is public
    in this refutation, being a point mass. *)
Lemma psl211_fixed_deal_view_dep (R : realType) :
  ~ (psl211_fixed_dealP R |=
       @dealer_shuffle_view R bool psl211_deal cutT viewT
         (fdist_uniform card_bool) (@psl211_fixed_deal_delta R)
         (`U psl211_G_pos)
         (psl211_dealer_view psl211_perdeck_coalition)
     _|_ @dealer_shuffle_secret R bool psl211_deal cutT
         (fdist_uniform card_bool) (@psl211_fixed_deal_delta R)
         (`U psl211_G_pos)).
Proof.
move=> H.
have [Ht Hf] := psl211_perdeck_raw_countE.
(* both cardinalities are pinned in term mode with the type ascribed, before
   any tactic sees a goal that spells the cardinal differently: an exact: of
   the same etrans against the goal left by rewrite -cards_eq0 makes the
   unifier fall back to conversion and re-evaluate psl211_perdeck_raw_count *)
have Hcard0 : #|psl211_perdeck_fiber true| = 0 :=
  etrans (psl211_perdeck_fiberE true) Ht.
have Hcard1 : #|psl211_perdeck_fiber false| = 1 :=
  etrans (psl211_perdeck_fiberE false) Hf.
have Hemp : psl211_perdeck_fiber true = set0.
  by apply/eqP; rewrite -cards_eq0 Hcard0.
have Hmass : forall (b : bool) (g : cutT), g \in pgg_G psl211_M ->
    0 < psl211_fixed_dealP R (b, (psl211_perdeck_deal, g)).
  move=> b g Hg; rewrite /psl211_fixed_dealP dealer_shufflePE.
  rewrite /psl211_fixed_deal_delta fdist1xx mul1r.
  rewrite (fdist_uniform_supp_in R psl211_G_pos Hg) fdist_uniformE.
  (* never // or done on a goal holding #|pgg_G psl211_M|: done would try to
     evaluate the 660-element closure and does not come back *)
  apply: mulr_gt0.
    by rewrite invr_gt0 ltr0n card_bool.
  by rewrite invr_gt0 ltr0n; exact: psl211_G_pos.
have /card_gt0P[g0 Hg0] : (0 < #|psl211_perdeck_fiber false|)%N.
  by rewrite Hcard1.
move: Hg0; rewrite inE => /andP[Hg0G /eqP Hg0v].
move: (H psl211_perdeck_view true).
(* the joint vanishes term by term: off the fixed deal the deal factor is
   zero, off the group the shuffle factor is zero, and on both the sample
   would put its shuffle in the empty true fiber *)
(* no /= and no case on a boolean numeral anywhere below: the sample carries
   psl211_perdeck_deal, whose permutations a simplification would try to
   compute, and the reading is only ever moved by conversion at an ascription
   or by a named rewrite *)
rewrite pfwd1E /Pr big1; last first.
  move=> [b [d g]]; rewrite inE => /eqP [Hv Hb].
  have Hb' : b = true := Hb.
  rewrite Hb' dealer_shufflePE /psl211_fixed_deal_delta.
  have [Hd|Hd] := eqVneq d psl211_perdeck_deal; last first.
    by rewrite (fdist10 _ Hd) mul0r mulr0.
  have [Hg|Hg] := boolP (g \in pgg_G psl211_M); last first.
    by rewrite (fdist_uniform_supp_notin R psl211_G_pos Hg) mulr0 mulr0.
  have Hin : g \in psl211_perdeck_fiber b.
    by rewrite inE Hg andTb; apply/eqP; rewrite -Hd; exact: Hv.
  by move: Hin; rewrite Hb' Hemp inE.
move/esym/eqP; rewrite mulf_eq0.
case/orP => H0; move: H0; apply/negP; apply/pfwd1_neq0.
- exists (false, (psl211_perdeck_deal, g0)); split; last by apply: Hmass.
  by rewrite inE; apply/eqP; exact: Hg0v.
- exists (true, (psl211_perdeck_deal, g0)); split; last by apply: Hmass.
  by rewrite inE; apply/eqP.
Qed.

(* Nothing after this point reasons about the reading, so the seal is
   released; Opaque is not section-scoped. *)
Local Transparent psl211_alldecks_view psl211_perdeck_raw_count.

Print Assumptions uniform_fdistmap_pointE.
Print Assumptions psl211_perdeck_massE.
Print Assumptions psl211_perdeck_law_neq.
Print Assumptions psl211_perdeck_no_common_law.
Print Assumptions psl211_dealer_valid_forced.
Print Assumptions psl211_dealer_view_indep_of_deck_unsat.
Print Assumptions psl211_fixed_deal_view_dep.
