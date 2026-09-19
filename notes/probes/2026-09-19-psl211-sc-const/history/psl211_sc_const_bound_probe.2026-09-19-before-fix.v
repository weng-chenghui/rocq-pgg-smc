(* Probe, 2026-09-19. Not a production file.                                 *)
(*****************************************************************************)
(* psl211_sc_const_bound_probe: which ideal cuts the twelve-card chirality   *)
(*                              instance leaves a spectral certificate, and  *)
(*                              the certificate's own distance field         *)
(*                                                                          *)
(* The constancy field of a spectral certificate fails at the uniform law on *)
(* the shuffle group. This file measures how far a candidate ideal may sit   *)
(* from that law and still fail it. Two answers are given, one by support    *)
(* and one by variation distance, and the second closes the question the     *)
(* instance actually asks: the certificate's own distance field pins its     *)
(* ideal to within the shuffle bound's epsilon of the group-uniform law, so  *)
(* no certificate over the all-decks run carries an epsilon below half the   *)
(* reciprocal of the group order.                                           *)
(*                                                                          *)
(* The premise of the second answer is the one the record supplies. A        *)
(* certificate's sc_Hd identifies its shuffle law with the adapter's cut,    *)
(* and the all-decks adapter draws the cut uniformly on the group, so the    *)
(* distance field is a statement about the group-uniform law whatever        *)
(* marginal bound record the certificate carries.                           *)
(*****************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import design_privacy algebraic_rigidity.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import psl211_group psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_exec.
From pgg_smc Require Import psl211_endpoints psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_blocks psl211_closure.
From psl211_sc_const_probe Require Import psl211_sc_const_probe.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Import Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Notation seatT :=
  ('I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1).
Local Notation cardT :=
  ('I_(pgg_N' (mp_M (instance_profile psl211_algebra))).+1).
Local Notation cutT := (pgg_gT psl211_M).

(* Nothing below needs the body of the laid deck, of the closure table or of
   the raw count, and a tactic left free to unfold them searches the 660-row
   table with the two chiralities present in one goal. *)
Local Opaque psl211_alldecks_view psl211_elem_table psl211_perdeck_raw_count.

(*****************************************************************************)
(*     Generic facts about the variation distance                           *)
(*****************************************************************************)

(** var_dist_point_le — one point's mass gap is at most the whole variation
    distance. This is what lets a distance premise, which is a statement about
    a law, be spent on a single reading a coalition might produce. *)
Lemma var_dist_point_le (R : realType) (T : finType) (P Q : R.-fdist T)
    (t : T) : `| P t - Q t | <= var_dist P Q.
Proof.
rewrite /var_dist (bigD1 t) //.
rewrite -{1}(addr0 `| P t - Q t |) lerD2l.
by apply: sumr_ge0 => a _; exact: normr_ge0.
Qed.

(** fdist_uniform_close_supp — a law closer than one atom of the uniform law
    to the uniform law gives every point positive mass. The hypothesis is the
    infotheo variation distance, which is the full L1 sum and not half of it,
    so the threshold is the atom itself and not half of it. *)
Lemma fdist_uniform_close_supp (R : realType) (T : finType) (n : nat)
    (HT : #|T| = n.+1) (Q : R.-fdist T) :
  var_dist (fdist_uniform HT) Q < (#|T|%:R)^-1 -> forall t, Q t != 0.
Proof.
move=> Hlt t; apply/eqP => H0.
have Hpos : (0 : R) < (#|T|%:R)^-1 by rewrite invr_gt0 ltr0n HT.
have Hge := var_dist_point_le (fdist_uniform HT) Q t.
move: Hge; rewrite fdist_uniformE H0 subr0 (gtr0_norm Hpos) => Hge.
have Hbad := Order.POrderTheory.le_lt_trans Hge Hlt.
by move: Hbad; rewrite Order.POrderTheory.ltxx.
Qed.

(** fdistmap_point_condE — the mass a pushed-forward law gives a value is the
    mass of that value's preimage. The form with the preimage written as a
    bigop condition, which is the form a support hypothesis is spent in. *)
Lemma fdistmap_point_condE (R : realType) (X T : finType) (f : X -> T)
    (p : R.-fdist X) (v : T) :
  (fdistmap f p) v = \sum_(x | f x == v) p x.
Proof.
rewrite fdistmapE big_mkcond [RHS]big_mkcond /=.
by apply: eq_bigr => x _; rewrite !inE.
Qed.

(*****************************************************************************)
(*     The constancy field transported to the instance's reading            *)
(*****************************************************************************)

(** psl211_perdeck_ideal_lawE — a law on cuts satisfying the constancy field
    sends the two chiralities of psl211_perdeck_deal to one law on what seats
    0, 1 and 2 read. The constancy field is quantified over run arguments and
    the all-decks run argument is the deck description, so the field's content
    at this instance is exactly a per-deck symmetry of the chirality. *)
Lemma psl211_perdeck_ideal_lawE (R : realType) (ideal : R.-fdist cutT) :
  sc_const_prop psl211_alldecks_params ideal ->
  fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
      (true, psl211_perdeck_deal) g) ideal
  = fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
      (false, psl211_perdeck_deal) g) ideal.
Proof.
move=> Hconst.
have Heq := Hconst psl211_perdeck_coalition psl211_perdeck_coalition_below_k
  (true, psl211_perdeck_deal) (false, psl211_perdeck_deal).
have Et : @static_coalition_obs psl211_algebra psl211_alldecks_params
     psl211_perdeck_coalition (true, psl211_perdeck_deal)
   = (fun g => psl211_alldecks_view psl211_perdeck_coalition
        (true, psl211_perdeck_deal) g)
  := psl211_alldecks_static_obs_funE _ _.
have Ef : @static_coalition_obs psl211_algebra psl211_alldecks_params
     psl211_perdeck_coalition (false, psl211_perdeck_deal)
   = (fun g => psl211_alldecks_view psl211_perdeck_coalition
        (false, psl211_perdeck_deal) g)
  := psl211_alldecks_static_obs_funE _ _.
exact: (etrans (esym (congr1 (fun f => fdistmap f ideal) Et))
  (etrans Heq (congr1 (fun f => fdistmap f ideal) Ef))).
Qed.

(*****************************************************************************)
(*     The answer by support                                                *)
(*****************************************************************************)

(** psl211_perdeck_fiber_true0 — no cut of the shuffle group carries the
    chirality-true deck of psl211_perdeck_deal to the reading
    psl211_perdeck_view. The reading is one the false chirality produces and
    the true one cannot, which is the whole of the per-deck asymmetry. *)
Lemma psl211_perdeck_fiber_true0 : psl211_perdeck_fiber true = set0.
Proof.
have [Ht _] := psl211_perdeck_raw_countE.
have Hcard0 : #|psl211_perdeck_fiber true| = 0 :=
  etrans (psl211_perdeck_fiberE true) Ht.
by apply/eqP; rewrite -cards_eq0 Hcard0.
Qed.

(** psl211_alldecks_sc_const_false_supp — no law on cuts carried by the
    shuffle group and positive on all of it satisfies the constancy field.
    The reading psl211_perdeck_view is unreachable at the true chirality and
    reachable at the false one, so any law that sees the group at all
    separates the two. *)
Lemma psl211_alldecks_sc_const_false_supp (R : realType)
    (ideal : R.-fdist cutT) :
  (forall g : cutT, g \notin pgg_G psl211_M -> ideal g = 0) ->
  (forall g : cutT, g \in pgg_G psl211_M -> ideal g != 0) ->
  ~ sc_const_prop psl211_alldecks_params ideal.
Proof.
move=> Hout Hin Hconst.
have Hlaw := psl211_perdeck_ideal_lawE Hconst.
have [_ Hf] := psl211_perdeck_raw_countE.
have Hcard1 : #|psl211_perdeck_fiber false| = 1 :=
  etrans (psl211_perdeck_fiberE false) Hf.
have /cards1P[g0 Hset] : #|psl211_perdeck_fiber false| == 1 by rewrite Hcard1.
have Hg0 : g0 \in psl211_perdeck_fiber false by rewrite Hset inE.
move: Hg0; rewrite inE => /andP[Hg0G Hg0v].
(* the true mass vanishes term by term: a cut producing the reading is either
   outside the group, where the law is zero, or inside it and in the empty
   true fiber *)
have Ht0 : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
    (true, psl211_perdeck_deal) g) ideal) psl211_perdeck_view = 0 :> R.
  rewrite fdistmap_point_condE; apply: big1 => g Hg.
  apply: Hout; apply/negP => HgG.
  have Hmem : g \in psl211_perdeck_fiber true by rewrite inE HgG Hg.
  by move: Hmem; rewrite psl211_perdeck_fiber_true0 inE.
have Hfge : ideal g0 <= (fdistmap (fun g => psl211_alldecks_view
    psl211_perdeck_coalition (false, psl211_perdeck_deal) g) ideal)
    psl211_perdeck_view.
  (* no /= and no // here: the sum runs over the ambient permutation group,
     and a simplification descends into its enumeration *)
  rewrite fdistmap_point_condE (bigD1 g0 Hg0v).
  rewrite -{1}(addr0 (ideal g0)) lerD2l.
  by apply: sumr_ge0 => g _; exact: FDist.ge0.
move: Hfge; rewrite -Hlaw Ht0 => Hle.
have Hzero : ideal g0 = 0 :> R.
  by apply/eqP; rewrite Order.POrderTheory.eq_le Hle andTb; exact: FDist.ge0.
by move: (Hin g0 Hg0G); rewrite Hzero eqxx.
Qed.

(*****************************************************************************)
(*     The answer by variation distance                                     *)
(*****************************************************************************)

(** psl211_alldecks_sc_const_false_close — no law on cuts within variation
    distance epsilon of the group-uniform law satisfies the constancy field,
    once twice epsilon stays below the reciprocal of the group order. At the
    group-uniform law the two chiralities give the reading
    psl211_perdeck_view masses zero and one over the group order, and a
    variation distance moves each of those by at most epsilon. *)
Lemma psl211_alldecks_sc_const_false_close (R : realType)
    (ideal : R.-fdist cutT) (eps : R) :
  var_dist ((`U psl211_G_pos) : R.-fdist cutT) ideal <= eps ->
  eps + eps < (#|pgg_G psl211_M|%:R)^-1 ->
  ~ sc_const_prop psl211_alldecks_params ideal.
Proof.
move=> Hclose Heps Hconst.
have Hlaw := psl211_perdeck_ideal_lawE Hconst.
have [Ht Hf] := psl211_perdeck_raw_countE.
have H0 : #|psl211_perdeck_fiber true| = 0 :=
  etrans (psl211_perdeck_fiberE true) Ht.
have H1 : #|psl211_perdeck_fiber false| = 1 :=
  etrans (psl211_perdeck_fiberE false) Hf.
(* each chirality's uniform mass is pinned in a goal naming that chirality
   only, as psl211_perdeck_law_neq does *)
have Ut : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
    (true, psl211_perdeck_deal) g) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_perdeck_view = 0 :> R.
  by rewrite psl211_perdeck_massE H0 mulr0n.
have Uf : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
    (false, psl211_perdeck_deal) g) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_perdeck_view = (#|pgg_G psl211_M|%:R)^-1 :> R.
  by rewrite psl211_perdeck_massE H1 mulr1n.
have Hgap : forall b : bool,
    `| (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
          (b, psl211_perdeck_deal) g) ((`U psl211_G_pos) : R.-fdist cutT))
         psl211_perdeck_view
      - (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
          (b, psl211_perdeck_deal) g) ideal) psl211_perdeck_view | <= eps.
  move=> b; exact: (Order.POrderTheory.le_trans (var_dist_point_le _ _ _)
    (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) Hclose)).
have T1 : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
    (true, psl211_perdeck_deal) g) ideal) psl211_perdeck_view <= eps.
  have H := Hgap true.
  move: H; rewrite Ut sub0r normrN ler_norml => /andP[_ Hup]; exact: Hup.
have T2 : (#|pgg_G psl211_M|%:R)^-1
    <= eps + (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
         (false, psl211_perdeck_deal) g) ideal) psl211_perdeck_view.
  have H := Hgap false.
  move: H; rewrite Uf ler_norml lerBlDr => /andP[_ Hlo]; exact: Hlo.
have T3 : eps + (fdistmap (fun g => psl211_alldecks_view
    psl211_perdeck_coalition (false, psl211_perdeck_deal) g) ideal)
    psl211_perdeck_view <= eps + eps.
  by rewrite lerD2l -Hlaw; exact: T1.
have Hbad := Order.POrderTheory.le_lt_trans
  (Order.POrderTheory.le_trans T2 T3) Heps.
by move: Hbad; rewrite Order.POrderTheory.ltxx.
Qed.

(*****************************************************************************)
(*     No spectral certificate over the all-decks run                       *)
(*****************************************************************************)

(** psl211_alldecks_cert_ideal_close — a spectral certificate over the
    all-decks model states its distance against the group-uniform law. The
    certificate's own identification field says its shuffle law is the
    adapter's cut, and this adapter's cut is the uniform law on the shuffle
    group, so the epsilon a certificate quotes is an epsilon against that
    law however its marginal bound record was built. *)
Lemma psl211_alldecks_cert_ideal_close (R : realType)
    (cert : SpectralCert (psl211_alldecks_sample R)) :
  var_dist ((`U psl211_G_pos) : R.-fdist cutT) (sc_ideal cert)
  <= sw_bound_eps (sc_b cert).
Proof.
have Hd : sw_rho_dist (sc_b cert) = ((`U psl211_G_pos) : R.-fdist cutT)
  := etrans (sc_Hd cert) (psl211_alldecks_cut_distE R).
have Hc := sc_close cert.
rewrite Hd in Hc; exact: Hc.
Qed.

(** psl211_alldecks_no_spectral_cert — the all-decks run of the twelve-card
    chirality instance admits no spectral certificate whose shuffle bound is
    below half the reciprocal of the group order. The exact arm's witness is
    therefore not one of two available readings of this instance: it is the
    only arm the model can close, and a spectral row would have to quote an
    epsilon at least 1/1320 against a shuffle whose marginal error is zero. *)
Theorem psl211_alldecks_no_spectral_cert (R : realType)
    (cert : SpectralCert (psl211_alldecks_sample R)) :
  sw_bound_eps (sc_b cert) + sw_bound_eps (sc_b cert)
    < (#|pgg_G psl211_M|%:R)^-1 -> False.
Proof.
move=> Heps.
apply: (@psl211_alldecks_sc_const_false_close R (sc_ideal cert)
  (sw_bound_eps (sc_b cert)) (psl211_alldecks_cert_ideal_close cert) Heps).
exact: sc_const_prop_field cert.
Qed.

(** psl211_alldecks_no_spectral_cert0 — in particular no spectral certificate
    over the all-decks model carries the instance's own marginal bound, whose
    epsilon is zero because the single-card pushforward of this shuffle is
    exactly uniform. What the instance proves about its shuffle is too strong
    for the spectral arm to use, the arm needing an ideal cut a coalition
    reads constantly and the group-uniform cut not being one. *)
Corollary psl211_alldecks_no_spectral_cert0 (R : realType)
    (cert : SpectralCert (psl211_alldecks_sample R)) :
  sw_bound_eps (sc_b cert) = 0 -> False.
Proof.
move=> H0.
have Hlt : sw_bound_eps (sc_b cert) + sw_bound_eps (sc_b cert)
    < (#|pgg_G psl211_M|%:R)^-1.
  by rewrite H0 addr0 invr_gt0 ltr0n; exact: psl211_G_pos.
(* cert is an implicit argument of the theorem, occurring in the type of its
   hypothesis, so the certificate is supplied at the @ form *)
exact: (@psl211_alldecks_no_spectral_cert R cert Hlt).
Qed.

Print Assumptions psl211_alldecks_sc_const_false_supp.
Print Assumptions psl211_alldecks_sc_const_false_close.
Print Assumptions psl211_alldecks_no_spectral_cert.
Print Assumptions psl211_alldecks_no_spectral_cert0.
Print Assumptions fdist_uniform_close_supp.
