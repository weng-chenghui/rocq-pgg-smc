From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import action div bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface psl211_group psl211_alldecks.
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

(** psl211_perdeck_massE b — at the deal psl_counter_deal, the law of what the
    coalition reads under chirality b gives psl_counter_view the mass of its
    fiber of cuts over the order of the shuffle group. *)
Lemma psl211_perdeck_massE (R : realType) (b : bool) :
  (fdistmap (fun g => psl211_alldecks_view psl_counter_coalition
       (b, psl_counter_deal) g)
     ((`U psl211_G_pos) : R.-fdist cutT)) psl_counter_view =
  (#|pgg_G psl211_M|%:R)^-1 *+ #|psl_counter_fiber b| :> R.
Proof. by rewrite /psl_counter_fiber uniform_fdistmap_pointE. Qed.

(** psl211_perdeck_law_differ — at the single deal psl_counter_deal the two
    chiralities send the uniform cut law to two different laws on what the
    coalition reads.  The averaged symmetry that psl211_alldecks establishes
    is therefore genuinely a statement about the average over deals: fixing
    one deal destroys it, and with it the per-deck route to privacy. *)
Lemma psl211_perdeck_law_differ (R : realType) :
  fdistmap (fun g => psl211_alldecks_view psl_counter_coalition
      (true, psl_counter_deal) g)
    ((`U psl211_G_pos) : R.-fdist cutT) !=
  fdistmap (fun g => psl211_alldecks_view psl_counter_coalition
      (false, psl_counter_deal) g)
    ((`U psl211_G_pos) : R.-fdist cutT).
Proof.
(* each mass is pinned to its value in a goal naming one chirality only, and
   the two are brought together in term mode, so no tactic ever searches a
   goal in which the two chiralities could be matched against each other *)
have [Ht Hf] := psl_counter_raw_countE.
have H0 : #|psl_counter_fiber true| = 0 :=
  etrans (psl_counter_fiberE true) Ht.
have H1 : #|psl_counter_fiber false| = 1 :=
  etrans (psl_counter_fiberE false) Hf.
have Lt : (fdistmap (fun g => psl211_alldecks_view psl_counter_coalition
      (true, psl_counter_deal) g)
    ((`U psl211_G_pos) : R.-fdist cutT)) psl_counter_view = 0 :> R.
  by rewrite psl211_perdeck_massE H0 mulr0n.
have Lf : (fdistmap (fun g => psl211_alldecks_view psl_counter_coalition
      (false, psl_counter_deal) g)
    ((`U psl211_G_pos) : R.-fdist cutT)) psl_counter_view =
  (#|pgg_G psl211_M|%:R)^-1 :> R.
  by rewrite psl211_perdeck_massE H1 mulr1n.
apply/negP => /eqP Heq.
have Hz : (0 : R) = (#|pgg_G psl211_M|%:R)^-1 :=
  etrans (esym Lt)
    (etrans (congr1 (fun q : R.-fdist viewT => q psl_counter_view) Heq) Lf).
have : (#|pgg_G psl211_M|%:R)^-1 == 0 :> R by rewrite -Hz.
rewrite invr_eq0 pnatr_eq0 => /eqP Hcard.
by move: psl211_G_pos; rewrite Hcard.
Qed.

(** psl211_perdeck_no_common_law — no law on readings is the law of the
    coalition's reading at psl_counter_deal under both chiralities.  This is
    the second premise of dealer_view_indep_of_deck written at PSL(2,11), for
    an arbitrary validity predicate that accepts that deal, and it has no
    solution: the per-deck route to privacy is closed for this instance, and
    only the average over deals that dealer_view_indep asks for remains. *)
Lemma psl211_perdeck_no_common_law (R : realType)
    (valid : bool -> psl211_deal -> bool) (mu : R.-fdist viewT) :
  (forall b : bool, valid b psl_counter_deal) ->
  ~ (forall (b : bool) (d : psl211_deal),
       (fdist_uniform card_bool : R.-fdist bool) b != 0 -> valid b d ->
       fdistmap (fun g => psl211_alldecks_view psl_counter_coalition
           (b, d) g) ((`U psl211_G_pos) : R.-fdist cutT) = mu).
Proof.
move=> Hvalid Hlaw.
have Hpos : forall b : bool,
    (fdist_uniform card_bool : R.-fdist bool) b != 0.
  (* card_bool is needed: done cannot evaluate #|bool| on its own *)
  by move=> b; rewrite fdist_uniformE invr_eq0 pnatr_eq0 card_bool.
move/negP: (psl211_perdeck_law_differ R); apply; apply/eqP.
exact: etrans (Hlaw true psl_counter_deal (Hpos true) (Hvalid true))
  (esym (Hlaw false psl_counter_deal (Hpos false) (Hvalid false))).
Qed.

(* Nothing after this point reasons about the reading, so the seal is
   released; Opaque is not section-scoped. *)
Local Transparent psl211_alldecks_view.

Print Assumptions uniform_fdistmap_pointE.
Print Assumptions psl211_perdeck_massE.
Print Assumptions psl211_perdeck_law_differ.
Print Assumptions psl211_perdeck_no_common_law.
