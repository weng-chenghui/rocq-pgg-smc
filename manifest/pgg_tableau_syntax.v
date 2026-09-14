(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* The statement surface of a Tableau program                                 *)
(*                                                                            *)
(* A program of pgg_tableau.v is a sequence of binds over anonymous tuples.   *)
(* This file gives each statement a named surface, so that a statement says   *)
(* which fact occupies which clause and a term written in the wrong clause is *)
(* rejected where it is written rather than deep inside an existT. Nothing    *)
(* here proves anything: every rule expands to one tableau_bind, and the      *)
(* accumulated proposition is that of pgg_tableau.v unchanged.                *)
(*                                                                            *)
(* Two typed builders carry the work. obs_payload takes the three run facts   *)
(* in order at the data the previous statement reached; its point is that the *)
(* data is passed explicitly, because a clause elaborated at an evar-typed    *)
(* position accepts an obligation for the wrong proposition, and an ltac:     *)
(* clause at such a position is closed by done with a term that proves        *)
(* nothing. mk_spectral takes the five components of a certificate            *)
(* separately, each quantified over the real field and the model index, so a  *)
(* statement displays the marginal bound, the equation between that bound's   *)
(* law and the model's cut law, the ideal cut, the mixing distance and the    *)
(* ideal's secret-independence as five named things rather than one record.   *)
(* The statement binds those two variables once, after at, and abstracts      *)
(* every clause over them, so a clause is a term in R and idx rather than a   *)
(* function of them.                                                          *)
(*                                                                            *)
(* The termination statement comes in two forms. One names a lemma; the other *)
(* writes the literal vm_compute and builds the obligation in place. The two  *)
(* are not the same term, so a program through the literal is a different     *)
(* program from one through the lemma, proving the same proposition.          *)
(*                                                                            *)
(* The publish separator is |>. Measured on 2026-09-14, |> occurs as a        *)
(* standalone notation token nowhere in the kept tree, MathComp with          *)
(* analysis, infotheo or Stdlib: every occurrence is inside infotheo's convex *)
(* notation x <| p |> y, in fdist_scope and fsdist_scope, and in              *)
(* mathcomp-analysis convex.v, with which it was checked to coexist in one    *)
(* file.                                                                      *)
(*                                                                            *)
(* The surface spends twelve identifiers as global keywords in every file     *)
(* that requires this one: dealt, functionality, execute, endpoints, recon,   *)
(* sample, certify, leaks, tied, ideal, mixing and invariant. Each follows a  *)
(* slot in some rule. The tokens fuel, terminates, publish, vm_compute,       *)
(* ExactIndependence and SpectralDecay follow a literal and stay identifiers, *)
(* which is what keeps the two port constructors usable by name; at follows a *)
(* literal too and was a keyword of Rocq before this file.                    *)
(*                                                                            *)
(* One of the twelve shadows a framework definition: endpoints is also the    *)
(* verifier's endpoint tuple in pgg_interface.v. A file requiring this        *)
(* surface must write that one through its module path. No file in the tree   *)
(* writes it bare.                                                            *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   obs_payload  == the three run facts in the shape execute_step wants      *)
(*   mk_spectral  == a certificate at every field and index, from its five    *)
(*                   components                                               *)
(*   Targeted     == an algebra with the ideal function a run of it computes  *)
(*   targeted_F   == the Functionality a Targeted names                       *)
(*   ExactLeakAt  == some coalition of k seats has a view of positive mutual  *)
(*                   information with the secret                              *)
(*   exact_leaks  == the witness again, with such an annotation checked       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     The two typed builders                                                 *)
(******************************************************************************)

(* The three run facts of a parameter record, in the order execute_step reads
   them. The accumulated data is an argument and not inferred, which is what
   fixes each of the three propositions before its obligation is
   elaborated. *)
Definition obs_payload (x : StackAt Executable)
    (Ht : instance_terminates_stmt (projT2 x))
    (He : instance_endpoints_stmt (projT2 x))
    (Hr : instance_recon_stmt (projT2 x)) : ObsPayload x :=
  existT _ Ht (existT _ He Hr).
Arguments obs_payload : clear implicits.

(* A certificate at every real field and every index of the accumulated model,
   assembled from its five components: the cut's marginal bound, the equation
   between that bound's law and the law the model draws its cut from, the
   ideal cut, the distance of the drawn cut from the ideal, and the constancy
   of a coalition's view of the ideal cut in the run argument. The split is
   what makes the two currencies of the port visible where it is written: the
   fourth component is the only inexact one, and the fifth is exact. *)
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

(* An algebra together with the ideal function a run of it is meant to
   compute, from whatever a run takes as argument to the value it
   reconstructs. The record exists because the completion-level stack carries
   no functionality: the accumulated proposition is about a coalition's view
   and never mentions the ideal function, so naming one happens beside the
   program rather than inside it. For a dealer-dealt run the ideal function is
   forced to be the identity, and the record is written only for an input
   family, where it is not.

   targeted_F is what such a run is measured against: a run whose recovered
   value ex_expected is written as this ideal function meets
   realises_expected by conversion, which is the whole obligation of the
   functionality statement. *)
Record Targeted := MkTargeted {
  tg_algebra : PGGAlgebraic ;
  tg_inputT  : Type ;
  tg_f       : tg_inputT -> pga_secretT tg_algebra }.

(* The tg_f projection returns an arrow, so Unset Strict Implicit takes the
   record for something to infer and the arrow's own argument steals its
   slot; the directive pins it back. *)
Arguments tg_f : clear implicits.

(* The specification a Targeted names: its own ideal function, at the privacy
   threshold of the algebra's scheme. The threshold is read off the scheme and
   not written, because an execution narrows no coalition size the scheme
   already guarantees. *)
Definition targeted_F (t : Targeted)
    : Functionality (tg_inputT t) (pga_secretT (tg_algebra t)) :=
  MkFunctionality (tg_f t) (ts_k' (pga_scheme (tg_algebra t))).

Notation "A 'functionality' f" := (@MkTargeted A _ f)
  (at level 90, left associativity, f at level 0).

(******************************************************************************)
(*     The tightness annotation of the exact arm                              *)
(******************************************************************************)

(* At every real field and index, some coalition of exactly k seats reads a
   view whose mutual information with the secret is strictly positive. It is
   the affirmation, at size k, of what an ExactWitness denies below the
   threshold, stated at the same reader ew_indep is stated at, so the two are
   claims about one object rather than two.

   A scheme guarantees nothing at or above its threshold, and this is what
   separates a threshold that is sharp from one that is merely as far as a
   proof reached. It is an annotation on the guarantee and not part of it: k
   occurs in the type, so the kernel checks the number against the proof, and
   the annotated program is convertible with the unannotated one. It attaches
   to the exact arm alone, so a program certifying decay carries no such
   claim. *)
Definition ExactLeakAt (k : nat) (x : StackAt Sampled) (p : ExactPayload x)
    : Prop :=
  forall (R : realType) (idx : amf_index (sp_f x) R),
    exists C : {set 'I_(pi_T' (mp_PI (instance_profile (projT1 x)))).+1},
      #|C| = k
      /\ 0 < `I( ew_secret (p R idx) ;
                 (fun u => static_coalition_obs C
                             ((amf_sample (sp_f x) R idx).(sa_arg) u)
                             ((amf_sample (sp_f x) R idx).(sa_cut) u)) ).
Arguments ExactLeakAt : clear implicits.

(* The exact arm's witness, with a tightness annotation checked against it and
   then dropped. The result is the witness itself, so the annotation costs
   nothing in the term a row builds and everything proved about an annotated
   program is proved about the unannotated one. *)
Definition exact_leaks (x : StackAt Sampled) (p : ExactPayload x)
    (k : nat) (H : ExactLeakAt k x p) : ExactPayload x := p.
Arguments exact_leaks : clear implicits.

(******************************************************************************)
(*     The row statements                                                     *)
(******************************************************************************)

Notation "A 'dealt' 'fuel' n" := (tableau_start A ;;; dealt_step of n)
  (at level 90, left associativity, n at level 0).

(* The run the three obligations are made about is the framework's own process
   list, exec_saprocs of pgg_execution_plug.v: a dealer carrying the plug's
   content function, a verifier, one player per seat, and then ep_input_procs,
   the commit processes an input family supplies and a sharing family leaves
   empty. exec_procs is that list erased to what the interpreter consumes, and
   termination and the endpoint equation are both stated over it.

   What this statement builds is the observed execution, and publish writes it
   unchanged into the row's apr_observed. A row therefore describes the run
   these three obligations were proved about, and not a second run that
   resembles it. *)
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

Notation "s 'certify' 'ExactIndependence' w 'leaks' 'at' k 'by' H" :=
  (s ;;; certify_exact of (exact_leaks (tableau_at s) w k H))
  (at level 90, left associativity, w at level 0, k at level 0, H at level 0,
   only parsing).

Notation "s 'certify' 'SpectralDecay' c" := (s ;;; certify_spectral of c)
  (at level 90, left associativity, c at level 0).

(* The five clauses name the real field and the model index once, after at,
   and the statement abstracts every clause over them. Each component is a
   term in those two variables rather than a function of them, so what a
   clause displays is the component and not the plumbing that quantifies it. *)
Notation "s 'certify' 'SpectralDecay' 'at' R idx b 'tied' 'by' Hd 'ideal' u 'mixing' 'by' Hc 'invariant' 'by' Hk" :=
  (s ;;; certify_spectral of (mk_spectral (tableau_at s)
     (fun R idx => b) (fun R idx => Hd) (fun R idx => u)
     (fun R idx => Hc) (fun R idx => Hk)))
  (at level 90, left associativity, R ident, idx ident,
   b at level 10, Hd at level 10, u at level 10, Hc at level 10,
   Hk at level 10, only parsing).

(* The two statuses are written transfer first, against the argument order of
   publish itself, so that a row's last statement reads in the order the
   manifest column headings run. *)
Notation "s |> 'publish' t a" := (s ;;; publish a of t)
  (at level 90, left associativity, t at level 0, a at level 0).
