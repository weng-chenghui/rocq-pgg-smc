(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5_tableau_checks: the terms the kernel refuses at the five-seat instance  *)
(*                                                                            *)
(* Each entry below is one written term that the kernel rejects, recorded so  *)
(* that the rejection is compiled rather than described. A recorded rejection *)
(* says what it says about the one term written under it and about no other   *)
(* term: it fixes a spelling that does not typecheck, and states no general   *)
(* impossibility. The file declares nothing and nothing depends on it.        *)
(*                                                                            *)
(* Three boundaries are recorded. The first is that a probability model       *)
(* belongs to one run: a model is typed over the observed execution it was    *)
(* built over, so the tape model samples the supplied run and the same        *)
(* statement at the dealer-dealt run is refused. The two modes of the sharing *)
(* family therefore share no model, and no statement made at one run's model  *)
(* is a statement about the other's. The second is that the tolerated         *)
(* coalition size of s5_F is read off the algebra: the equation asserting it  *)
(* is five, where the sum-mod scheme tolerates four, is refused. The third is *)
(* that the readers of a security property do not apply to the dealer-dealt   *)
(* program's published value, which is a PublishedObserved and not a          *)
(* Published, and that the path built for that value records the assumption   *)
(* status it was published under.                                             *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset.
From mathcomp Require Import matrix zmodp ssralg ssrnum reals.
From infotheo Require Import fdist proba entropy.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import s5_exec s5_models.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import s5_tableau_observed s5_tableau_sampled.
From pgg_smc Require Import s5_tableau_analysis_bridged.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     A model belongs to the run it was built over                           *)
(******************************************************************************)

(* A model built over one run of the sharing family does not sample the
   other. The tape model is typed over this run's observed execution, so the
   positive holds; the dealt run's observed execution is a different value
   and the same statement at it is rejected. The two modes of the sharing
   family therefore share no probability model, and no evidence stated in
   one reaches the other. *)
Check (s5_rand_sampled : Tableau Sampled).
Fail Definition s5_dealt_rand : Tableau Sampled :=
  s5_dealt sample s5_rand_family.

(******************************************************************************)
(*     The tolerated coalition size is read off the algebra                   *)
(******************************************************************************)

(* Writing five where the scheme tolerates four is rejected, so the number a
   specification carries is decided by the kernel rather than by the
   reader. *)
Fail Definition s5_F_k5 : s5_F = MkFunctionality id 5 := erefl.

(******************************************************************************)
(*     Terms refused at the dealer-dealt program published at Observed        *)
(******************************************************************************)

(* The reader of an exact-independence statement takes a PublishedAt, whose
   data is at AnalysisBridged. The term written under this line applies it to
   the dealer-dealt program's published value, which is a PublishedObserved,
   and the kernel refuses that term. *)
Fail Check (view_secrecy_of s5_dealt_observed_published).

(* The reader naming which security property a program certified takes the
   same record, and the same value is refused under it. *)
Fail Check (security_property_of s5_dealt_observed_published).

(* Nor is that value a Published, which is PublishedAt at the empty bound.
   PublishedObserved and PublishedAt are distinct inductive types with no
   coercion between them, so the ascription written here is refused. *)
Fail Check (s5_dealt_observed_published : Published).

(* The same program published under the baseline assumption status: the path
   it builds is not the manifest's, which records the accepted group-order
   fact. Conversion decides the two paths apart, so the equation written here
   is refused. Both sides of that disagreement are written by hand, the
   payload here and the manifest's field there, so what the kernel decides is
   whether two authors' statements agree and not which axioms the program
   uses. *)
Fail Definition s5_dealt_observed_published_baseline_pathE :
  published_observed_path
    (s5_dealt |> publish Observed assuming BaselineClassicalOnly)
  = s5_det_path := erefl.
