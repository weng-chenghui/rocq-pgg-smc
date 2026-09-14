(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* The statement surface of a Tableau row                                     *)
(*                                                                            *)
(* A row of pgg_tableau.v is a chain of binds whose payloads are anonymous    *)
(* tuples. This file gives each statement a named surface, so that a line     *)
(* says which fact occupies which slot and a payload written in the wrong     *)
(* position is rejected where it is written rather than deep inside an        *)
(* existT. Nothing here proves anything: every rule expands to one            *)
(* tableau_bind, and the propositions a row accumulates are those of          *)
(* pgg_tableau.v unchanged.                                                   *)
(*                                                                            *)
(* Two typed builders carry the work. obs_payload takes the three run facts   *)
(* in order at the coordinate the previous line reached; its point is that    *)
(* the coordinate is passed explicitly, because a payload slot elaborated at  *)
(* an evar-typed position accepts a proof of the wrong statement, and an      *)
(* ltac: slot at such a position is closed by done with a term that proves    *)
(* nothing. mk_spectral takes the five components of a spectral certificate   *)
(* separately, each quantified over the real field and the family index, so a *)
(* line displays the marginal bound, the law identification, the ideal cut,   *)
(* the mixing distance and the ideal's secret-independence as five named      *)
(* things rather than one record.                                             *)
(*                                                                            *)
(* The termination line comes in two forms. One names a lemma; the other      *)
(* writes the literal vm_compute and builds the proof in place. The two are   *)
(* not the same term, so a row through the literal is a different row from a  *)
(* row through the lemma, proving the same proposition.                       *)
(*                                                                            *)
(* The surface spends eleven identifiers as global keywords in every file     *)
(* that requires this one: dealt, functionality, execute, endpoints, recon,   *)
(* sample, certify, tied, ideal, mixing and invariant. Each follows a slot in *)
(* some rule. The tokens fuel, terminates, publish, vm_compute,               *)
(* ExactIndependence and SpectralDecay follow a literal and stay identifiers, *)
(* which is what keeps the two port constructors usable by name.              *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   obs_payload  == the three run facts in the shape execute_step wants      *)
(*   mk_spectral  == a spectral payload from its five components              *)
(*   Targeted     == an algebra with the ideal function a run of it computes  *)
(*   targeted_F   == the Functionality a Targeted names                       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_weighted_words.
From pgg_smc Require Import pgg_observed_execution pgg_sample_adapter.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     The two typed payload builders                                         *)
(******************************************************************************)

(* The three run facts of a parameter record, in the order execute_step reads
   them. The coordinate is an argument and not inferred, which is what fixes
   each of the three statements before its proof is elaborated. *)
Definition obs_payload (x : StackAt Executable)
    (Ht : instance_terminates_stmt (projT2 x))
    (He : instance_endpoints_stmt (projT2 x))
    (Hr : instance_recon_stmt (projT2 x)) : ObsPayload x :=
  existT _ Ht (existT _ He Hr).
Arguments obs_payload : clear implicits.

(* A spectral payload assembled from its five components, each given at every
   real field and every index of the accumulated family: the shuffle's
   marginal bound, the identification of that bound's law with the law the
   model draws its cut from, the ideal cut, the distance of the shuffle from
   the ideal, and the constancy of a coalition's reading of the ideal cut in
   the run argument. The split is what makes the two currencies of the arm
   visible on the line: the fourth component is the only inexact one, and the
   fifth is an exact statement about the ideal. *)
Definition mk_spectral (x : StackAt Sampled)
    (b : forall (R : realType) (idx : amf_index (sp_f x) R),
           ShuffleMarginalBound R (instance_M (projT1 x)))
    (Hd : forall (R : realType) (idx : amf_index (sp_f x) R),
            sw_rho_dist (b R idx) = sa_cut_dist (amf_sample (sp_f x) R idx))
    (u : forall (R : realType) (idx : amf_index (sp_f x) R),
           R.-fdist (pgg_gT (mp_M (instance_profile (projT1 x)))))
    (Hc : forall (R : realType) (idx : amf_index (sp_f x) R),
            var_dist (sw_rho_dist (b R idx)) (u R idx)
            <= sw_bound_eps (b R idx))
    (Hk : forall (R : realType) (idx : amf_index (sp_f x) R)
            (C : {set 'I_(pi_T' (mp_PI (instance_profile (projT1 x)))).+1}),
            (#|C| < profile_k (instance_profile (projT1 x)))%N ->
            forall y y' : ex_inputT (projT1 (projT2 x)),
              fdistmap (static_coalition_obs C y) (u R idx)
              = fdistmap (static_coalition_obs C y') (u R idx))
    : SpectralPayload x :=
  fun R idx => @MkSpectralCert R (projT1 x) (projT1 (projT2 x))
    (amf_sample (sp_f x) R idx)
    (b R idx) (Hd R idx) (u R idx) (Hc R idx) (Hk R idx).
Arguments mk_spectral : clear implicits.

(******************************************************************************)
(*     The ideal function a run computes                                      *)
(******************************************************************************)

(* An algebra together with the function a run of it is meant to compute, from
   whatever a run takes as argument to the value it reconstructs. The record
   exists because the completion-level stack has no slot for a functionality:
   the propositions a row accumulates are about a coalition's view and none of
   them mentions the ideal function, so naming one has to happen beside the
   chain rather than inside it. For a dealer-dealt run the function is forced
   to be the identity, and the record is written only where it is not, namely
   where the run argument is an encoded input. *)
Record Targeted := MkTargeted {
  tg_algebra : PGGAlgebraic ;
  tg_inputT  : Type ;
  tg_f       : tg_inputT -> pga_secretT tg_algebra }.

(* The tg_f projection returns an arrow, so Unset Strict Implicit takes the
   record for something to infer and the arrow's own argument steals its
   slot; the directive pins it back. *)
Arguments tg_f : clear implicits.

(* The specification a Targeted names: its own function, at the privacy
   threshold of the algebra's scheme. The threshold is read off the scheme and
   not written, because an execution narrows no coalition size the scheme
   already guarantees. *)
Definition targeted_F (t : Targeted)
    : Functionality (tg_inputT t) (pga_secretT (tg_algebra t)) :=
  MkFunctionality (tg_f t) (ts_k' (pga_scheme (tg_algebra t))).

Notation "A 'functionality' f" := (@MkTargeted A _ f)
  (at level 90, left associativity, f at level 0).

(******************************************************************************)
(*     The row statements                                                     *)
(******************************************************************************)

Notation "A 'dealt' 'fuel' n" := (tableau_start A ;;; dealt_step of n)
  (at level 90, left associativity, n at level 0).

Notation "s 'execute' 'terminates' 'by' t 'endpoints' 'by' e 'recon' 'by' r" :=
  (s ;;; execute_step of (obs_payload (tableau_at s) t e r))
  (at level 90, left associativity, t at level 0, e at level 0, r at level 0,
   only parsing).

Notation "s 'execute' 'terminates' 'by' 'vm_compute' 'endpoints' 'by' e 'recon' 'by' r" :=
  (s ;;; execute_step
       of (obs_payload (tableau_at s) ltac:(by vm_compute) e r))
  (at level 90, left associativity, e at level 0, r at level 0, only parsing).

Notation "s 'sample' f" := (s ;;; sample_step of f)
  (at level 90, left associativity, f at level 0).

Notation "s 'certify' 'ExactIndependence' w" := (s ;;; certify_exact of w)
  (at level 90, left associativity, w at level 0).

Notation "s 'certify' 'SpectralDecay' c" := (s ;;; certify_spectral of c)
  (at level 90, left associativity, c at level 0).

Notation "s 'certify' 'SpectralDecay' b 'tied' 'by' Hd 'ideal' u 'mixing' 'by' Hc 'invariant' 'by' Hk" :=
  (s ;;; certify_spectral of (mk_spectral (tableau_at s) b Hd u Hc Hk))
  (at level 90, left associativity, b at level 0, Hd at level 0, u at level 0,
   Hc at level 0, Hk at level 0, only parsing).

Notation "s |> 'publish' t a" := (s ;;; publish a of t)
  (at level 90, left associativity, t at level 0, a at level 0).
