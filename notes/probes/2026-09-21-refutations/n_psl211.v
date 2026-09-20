(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* n_psl211: the twelve-card chirality instance publishes an obstruction      *)
(*           (probe, ledger rows N2, N3, N6, N8)                              *)
(*                                                                            *)
(* At the all-decks execution under the group-uniform cut, three of the       *)
(* twelve seats read two run arguments differently, and they still do at      *)
(* every law near that cut. A certificate's fifth field asks for the          *)
(* opposite, so no input-indistinguishability certificate over this model     *)
(* has its ideal cut that near the group-uniform law. This file states that   *)
(* as the framework's obstruction, publishes it as a program, and drafts the  *)
(* manifest path such a program would carry.                                  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals lra.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_alldecks.
From pgg_smc Require Import psl211_models psl211_reading_constancy.
From pgg_smc Require Import psl211_tableau_observed psl211_tableau_sampled.
From refuteprobe Require Import n_framework n_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(** cutT — a cut, an element of the ambient permutation group the shuffle
    group sits inside. *)
Local Notation cutT := (pgg_gT psl211_M).

(******************************************************************************)
(*     N2: the constancy proposition and the framework hypothesis             *)
(******************************************************************************)

(** The standalone constancy proposition of
    instances/psl211/psl211_reading_constancy.v and the hypothesis the
    framework lemma takes are one proposition, by delta on the definition.
    The framework file states the hypothesis written out because the
    standalone name sits above it. *)
Lemma coalition_reading_constancy_unfoldE (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A)
    (u : R.-fdist (pgg_gT (mp_M (instance_profile A)))) :
  coalition_reading_constancy E u
  = (forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
       (#|C| < profile_k (instance_profile A))%N ->
       forall x x' : ex_inputT E,
         fdistmap (static_coalition_obs C x) u
         = fdistmap (static_coalition_obs C x') u).
Proof. exact: erefl. Qed.

(** The route from a refuted constancy to the obstruction, at the name the
    tree uses for the proposition. Refuting the constancy at every law within
    eps of U denies every certificate whose ideal sits that near U, the
    certificate's fifth field being that constancy at its own ideal. *)
Lemma no_certificate_near_of_constancy_false (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (U : R.-fdist (pgg_gT (mp_M (instance_profile A)))) (eps : R) :
  (forall u : R.-fdist (pgg_gT (mp_M (instance_profile A))),
     var_dist U u <= eps -> ~ coalition_reading_constancy E u) ->
  NoIndistinguishabilityCertNear sa U eps.
Proof.
move=> H cert Hc.
exact: (H (ic_ideal cert) Hc (indistinguishability_cert_reading_constancy cert)).
Qed.

(******************************************************************************)
(*     N3: the obstruction at the all-decks model                             *)
(******************************************************************************)

(** No input-indistinguishability certificate over the all-decks model of the
    twelve-card chirality instance has its ideal cut within eps of the
    group-uniform law, once eps added to itself stays below the reciprocal of
    the group order. A certificate's ideal is read by three seats at two
    masses that differ by that reciprocal, psl211_perdeck_view being reached
    by one cut of the group at one chirality of psl211_perdeck_deal and by
    none at the other, and a law within eps of the uniform one moves each
    mass by at most eps. What this excludes is a route to input
    indistinguishability at this model and not the proposition
    IndistinguishabilityPropAt at some number. *)
Theorem psl211_alldecks_no_certificate_near (R : realType) (eps : R) :
  eps + eps < (#|pgg_G psl211_M|%:R)^-1 ->
  NoIndistinguishabilityCertNear (amf_sample psl211_exact_family R tt)
    ((`U psl211_G_pos) : R.-fdist cutT) eps.
Proof.
move=> Heps.
apply: (@no_certificate_near_of_constancy_false R psl211_algebra
          psl211_alldecks_params (amf_sample psl211_exact_family R tt)
          ((`U psl211_G_pos) : R.-fdist cutT) eps).
move=> u Hclose.
exact: (@psl211_alldecks_constancy_false_close R u eps Hclose Heps).
Qed.

(******************************************************************************)
(*     N8: the program                                                        *)
(******************************************************************************)

(** The number the program publishes: a quarter of the reciprocal of the
    order of the shuffle group. The theorem above holds at every number below
    half that reciprocal, the strict inequality leaving the half itself out,
    and a program names one; this one is the largest round fraction inside
    the range. *)
Definition psl211_alldecks_obstruction_eps (R : realType) : R :=
  (#|pgg_G psl211_M|%:R)^-1 / 4%:R.

(** That number is inside the range the theorem needs, the order of the
    shuffle group being positive. *)
Lemma psl211_alldecks_obstruction_eps_lt (R : realType) :
  psl211_alldecks_obstruction_eps R + psl211_alldecks_obstruction_eps R
  < (#|pgg_G psl211_M|%:R)^-1.
Proof.
rewrite /psl211_alldecks_obstruction_eps.
have Hq : (0:R) < (#|pgg_G psl211_M|%:R)^-1.
  by rewrite invr_gt0 ltr0n; exact: psl211_G_pos.
lra.
Qed.

(** The obstruction the program publishes, at every real field and at the one
    index of the all-decks family: no certificate over this model has its
    ideal cut that near the group-uniform law. *)
Definition psl211_alldecks_obstruction
  : ObstructionPayload (tableau_at psl211_exact_sampled) :=
  fun (R : realType) (idx : unit) =>
    @NoCertificateNear R psl211_algebra psl211_alldecks_params
      (amf_sample psl211_exact_family R idx)
      ((`U psl211_G_pos) : R.-fdist cutT)
      (psl211_alldecks_obstruction_eps R).

(** Its proof at every field and index, which is the theorem above at the
    number the program names. *)
Definition psl211_alldecks_obstruction_proof
  : ObstructionPropOf psl211_alldecks_obstruction :=
  fun (R : realType) (idx : unit) =>
    psl211_alldecks_no_certificate_near (psl211_alldecks_obstruction_eps_lt R).

(** The all-decks run, the exact model and the obstruction, published. The
    same model carries the instance's exact-independence program,
    psl211_alldecks_published: a coalition of at most five seats learns
    nothing about the chirality there, exactly. The two facts are about one
    model and do not conflict, the certificate's fifth field asking for
    constancy of a reading in the whole run argument, of which the chirality
    is one coordinate of four. *)
Definition psl211_alldecks_obstruction_published : PublishedObstruction :=
  psl211_exact_sampled
    |> refute BaselineClassicalOnly psl211_alldecks_obstruction
       by psl211_alldecks_obstruction_proof.

(** The program's reader gives the obstruction back, at every real field. *)
Theorem psl211_alldecks_published_no_certificate_near (R : realType) :
  NoIndistinguishabilityCertNear (amf_sample psl211_exact_family R tt)
    ((`U psl211_G_pos) : R.-fdist cutT) (psl211_alldecks_obstruction_eps R).
Proof.
exact: (obstruction_of psl211_alldecks_obstruction_published R tt).
Qed.

(** Run correctness reaches the reader of a published obstruction unchanged:
    the value carries what the program proved at Sampled beside the
    obstruction, and nothing above it. *)
Lemma psl211_alldecks_obstruction_run_correct :
  oe_correct_prop
    (sp_obs (published_obstruction_at psl211_alldecks_obstruction_published)).
Proof.
exact: (run_correct_of_obstruction psl211_alldecks_obstruction_published).
Qed.

(******************************************************************************)
(*     N6: the manifest path such a program would carry                       *)
(******************************************************************************)

(** The path the terminal builds: the instance's own observed execution, the
    level AnalysisBridged, the unit-indexed exact-uniform family,
    NegativeTransfer and BaselineClassicalOnly. Conversion decides it against
    the facade's vocabulary, as the two published paths of this instance are
    decided. It differs from psl211_alldecks_path in the transfer status
    alone. *)
Lemma psl211_alldecks_obstruction_pathE :
  published_obstruction_path psl211_alldecks_obstruction_published
  = @MkAnalysisPath PSL211Analysis.observed AnalysisBridged
      PSL211Analysis.exact_family NegativeTransfer BaselineClassicalOnly.
Proof. exact: erefl. Qed.

(** That path and the manifest's existing all-decks path agree on their first
    three coordinates and on the assumption status, and differ on the
    transfer status. Two paths over one model and one pair of statuses are
    one manifest path, so a manifest entry for the obstruction is a twelfth
    path and not a second description of the eleventh. *)
Lemma psl211_alldecks_obstruction_path_observedE :
  ap_observed (published_obstruction_path psl211_alldecks_obstruction_published)
  = ap_observed psl211_alldecks_path.
Proof. exact: erefl. Qed.

Lemma psl211_alldecks_obstruction_path_transfer_neq :
  ap_transfer (published_obstruction_path psl211_alldecks_obstruction_published)
  <> ap_transfer psl211_alldecks_path.
Proof. by []. Qed.

(******************************************************************************)
(*     The assumption baselines                                               *)
(******************************************************************************)

Print Assumptions psl211_alldecks_no_certificate_near.
Print Assumptions psl211_alldecks_published_no_certificate_near.
Print Assumptions psl211_alldecks_obstruction_published.
