(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5_tableau_checks: what the five-seat instance's phases reject             *)
(*                                                                            *)
(* Each recorded failure below is one written term the kernel refuses, kept   *)
(* beside the term it is the near miss of. A boundary a reader can only be    *)
(* told about is a boundary a reader has to take on trust; a boundary written *)
(* out and refused is one the kernel decides. The file declares nothing and   *)
(* nothing depends on it.                                                     *)
(*                                                                            *)
(* Two boundaries are recorded. The first is that a probability model belongs *)
(* to one run: a model is typed over the observed execution it was built      *)
(* over, so the tape model samples the supplied run and the same statement    *)
(* at the dealer-dealt run is refused. The two modes of the sharing family    *)
(* therefore share no model, and no evidence stated in one reaches the other. *)
(* The second is that the coalition size a specification carries is decided   *)
(* by the kernel and not by whoever writes it: five where the sum-mod scheme  *)
(* tolerates four is refused.                                                 *)
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
Check (s5_supplied sample s5_rand_family : Tableau Sampled).
Fail Definition s5_dealt_rand : Tableau Sampled :=
  s5_dealt sample s5_rand_family.

(******************************************************************************)
(*     The tolerated coalition size is not a free choice                      *)
(******************************************************************************)

(* Writing five where the scheme tolerates four is rejected, so the number a
   specification carries is decided by the kernel rather than by the
   reader. *)
Fail Definition s5_F_k5 : s5_F = MkFunctionality id 5 := erefl.
