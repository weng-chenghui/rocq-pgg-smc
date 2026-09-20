(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* landing_draft_tableau: the text appended to                                *)
(* instances/psl211/tableau/psl211_tableau_analysis_bridged.v, and the        *)
(* PGL(2,7) non-vacuity lemma, compiled before they are written there. Every  *)
(* declaration below is the production text; only this header is not.         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals lra.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_collusion_bound.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_alldecks.
From pgg_smc Require Import psl211_models psl211_reading_constancy.
From pgg_smc Require Import psl211_tableau_sampled.
From pgg_smc Require Import psl211_tableau_analysis_bridged.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_exec.
From pgg_smc Require Import pgl27_models pgl27_tableau_analysis_bridged.
From refuteprobe Require Import landing_draft_framework landing_draft_syntax.
From refuteprobe Require Import landing_draft_psl211.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     The obstruction the all-decks model publishes                          *)
(******************************************************************************)

(** psl211_alldecks_obstruction — the obstruction, at every real field and at
    the one index of the all-decks family: the model is input distinguishable
    at 1/660, the reciprocal of the order of the shuffle group. *)
Definition psl211_alldecks_obstruction
  : ObstructionPayload (tableau_at psl211_exact_sampled) :=
  fun (R : realType) (idx : unit) =>
    @InputDistinguishabilityObstruction R psl211_algebra
      psl211_alldecks_params (amf_sample psl211_exact_family R idx)
      ((#|pgg_G psl211_M|%:R)^-1).

(** psl211_alldecks_obstruction_pf — its proof at every field and index, which
    is psl211_alldecks_input_distinguishability at the model the family
    returns there. *)
Definition psl211_alldecks_obstruction_pf
  : ObstructionPayloadProp psl211_alldecks_obstruction :=
  fun (R : realType) (_ : unit) =>
    psl211_alldecks_input_distinguishability R.

(** psl211_alldecks_obstruction_published — the all-decks run, the exact model
    and the obstruction, published. What the value carries about the model is
    that three of the twelve seats read the two chiralities of the deal
    psl211_perdeck_deal at least 1/660 apart under the model's own cut law, so
    a distinguisher told to compare those two run arguments has advantage at
    least 1/1320 there, the sum of absolute differences being twice the total
    variation distance of the literature. It certifies no security property:
    its data carries no SecurityEvidence and the five security readers of
    manifest/pgg_tableau.v project out of PublishedAt, a different inductive
    type.

    What it refutes. Every number at which an input-indistinguishability
    program over this model states its proposition is at least 1/660, whatever
    the certificate, by
    psl211_alldecks_indistinguishability_number_ge. Through the general form
    of the tail lemma, indistinguishability_prop_of_ideal_close, it also rules
    out every certificate whose ideal cut sits within eps of this model's own
    cut law once eps added to itself stays below 1/660, which is
    no_indistinguishability_cert_ideal_close_of_input_distinguishability at
    this model. The tree's psl211_alldecks_no_small_eps_cert is the companion
    exclusion on the other coordinate: it constrains a certificate's own
    marginal bound rather than where its ideal sits, and it follows from the
    same route at the certificate's own number.

    Why it does not conflict with psl211_alldecks_published. The two are facts
    about one model under different quantifiers over the run argument. Exact
    independence is stated with the deck description drawn uniformly, and it
    says that a coalition of at most five of the twelve seats then learns
    nothing about the chirality, exactly. The obstruction fixes two run
    arguments and compares the readings at those two values. A second and
    separate fact is that the chirality reindexes the laid deck.

    The path. All five coordinates are honest. The level is AnalysisBridged
    because the manifest's own definition of that level admits a limitation
    theorem about the same distribution and the same observer, and this is
    one; the transfer status is NegativeTransfer because that status is
    defined as a theorem transporting an obstruction to the path's observer,
    and the value's own proposition is that theorem. The manifest gains no
    twelfth path in this batch: it records paths and imposes its duties on
    paths, no duty requires a published program to have one, and the single
    coordinate with no honest value is the capability line, whose closed
    vocabulary is correctness, exact privacy, approximate privacy, trace
    secrecy, conditional entropy, mutual information and endpoint marginal
    mixing, none of which labels a limitation; extending that vocabulary is
    the owner's call. Were the path recorded it would be a twelfth path and
    not a second description of psl211_alldecks_path: the two agree on the
    observed execution, the level, the model family and the assumption status
    and differ in the transfer status, and two paths over one model and one
    pair of statuses are one path. *)
Definition psl211_alldecks_obstruction_published : PublishedObstruction :=
  psl211_exact_sampled
    |> publish Obstruction psl211_alldecks_obstruction
       by psl211_alldecks_obstruction_pf BaselineClassicalOnly.

(** psl211_alldecks_obstruction_published_pathE — the path this program
    publishes: the instance's own observed execution, the level
    AnalysisBridged, the unit-indexed exact-uniform family, NegativeTransfer
    and BaselineClassicalOnly. Conversion decides it against the facade's
    vocabulary, as the instance's two published paths are decided. *)
Lemma psl211_alldecks_obstruction_published_pathE :
  published_obstruction_path psl211_alldecks_obstruction_published
  = @MkAnalysisPath PSL211Analysis.observed AnalysisBridged
      PSL211Analysis.exact_family NegativeTransfer BaselineClassicalOnly.
Proof. exact: erefl. Qed.

(** psl211_alldecks_obstruction_published_path_observedE — that path and the
    manifest's all-decks path are about one run and one static observation of
    it. *)
Lemma psl211_alldecks_obstruction_published_path_observedE :
  ap_observed
    (published_obstruction_path psl211_alldecks_obstruction_published)
  = ap_observed psl211_alldecks_path.
Proof. exact: erefl. Qed.

(** psl211_alldecks_obstruction_published_path_transfer_neq — and they differ
    in the transfer status, which is the coordinate that separates a
    limitation from the instance's exact-independence claim. *)
Lemma psl211_alldecks_obstruction_published_path_transfer_neq :
  ap_transfer
    (published_obstruction_path psl211_alldecks_obstruction_published)
  <> ap_transfer psl211_alldecks_path.
Proof. by []. Qed.

(** psl211_alldecks_published_input_distinguishability — the program's reader
    gives the obstruction back, at every real field: the all-decks model is
    input distinguishable at 1/660. The published value and this statement are
    one theorem. *)
Theorem psl211_alldecks_published_input_distinguishability (R : realType) :
  InputDistinguishabilityPropAt (amf_sample psl211_exact_family R tt)
    ((#|pgg_G psl211_M|%:R)^-1).
Proof.
exact: (obstruction_of psl211_alldecks_obstruction_published R tt).
Qed.

(******************************************************************************)
(*     The same proposition at the eight-card orbit instance's word model     *)
(******************************************************************************)

(** pgl27_word_input_distinguishability_false — at the eight-card orbit
    instance's two-hundred-letter word model the input-distinguishability
    proposition fails at every number above 2^-39: the published program
    pgl27_word_published39 bounds the distance between the readings of every
    two dealt secrets below four colluding seats by 2^-39, so no pair of run
    arguments separates them further. The obstruction the twelve-card
    chirality instance publishes is therefore a statement about that model and
    not a proposition every model satisfies. *)
Theorem pgl27_word_input_distinguishability_false (R : realType)
    (secretP : R.-fdist bool) (c : R) :
  2%:R^-39 < c ->
  InputDistinguishabilityPropAt (amf_sample pgl27_word_family R secretP) c ->
  False.
Proof.
move=> Hc Hd.
have Hprop : IndistinguishabilityPropAt (pgl27_word_cert secretP) (2%:R^-39)
  := view_indistinguishability_of pgl27_word_published39 R secretP.
have Hge := indistinguishability_number_ge_of_input_distinguishability Hd Hprop.
by move: (Order.POrderTheory.lt_le_trans Hc Hge);
   rewrite Order.POrderTheory.ltxx.
Qed.

Print Assumptions psl211_alldecks_obstruction_published.
Print Assumptions psl211_alldecks_published_input_distinguishability.
Print Assumptions pgl27_word_input_distinguishability_false.
