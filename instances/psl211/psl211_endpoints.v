(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_endpoints: the endpoint equation of the twelve-card instance        *)
(*                                                                            *)
(* One declaration, alone in its own file.  Compiling it on 2026-09-15 cost   *)
(* 568 s of vm_compute, 324 s of Qed and 898 s wall, with a resident set      *)
(* reported at 10.45 GB through make.  The same reduction run directly under  *)
(* /usr/bin/time -l as probe P1b2, in a file that also carried the            *)
(* termination lemma, reported 17.15 GB.  Budget 17 GB on a 32 GB machine.    *)
(* The cost is the twelve-card, fourteen-process interpreter trace and not    *)
(* the budget: the same reduction at fuel 380 measured 562 s and 343 s, a     *)
(* difference inside the noise.  The reduction is symbolic in the cut; were   *)
(* it enumerating the 479001600 permutations of twelve points it would not    *)
(* finish at any per-element cost.                                            *)
(*                                                                            *)
(* Do not run this compile beside a second rocqworker.  Use make -j1.         *)
(*                                                                            *)
(* This .vo is invalidated by any rebuild of psl211_exec.v, psl211_profile.v, *)
(* psl211_scheme.v, psl211_orbit.v, psl211_closure.v, psl211_group.v,         *)
(* psl211_blocks.v, lib/perm_exchange.v, lib/perm_uniform.v or the framework  *)
(* under them, INCLUDING a rebuild from byte-identical sources: the library   *)
(* digest changes and every dependent then reports inconsistent assumptions.  *)
(*                                                                            *)
(* Definitions: none.                                                         *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_profile_endpoints == the executed endpoints of a run over this    *)
(*                               profile are its static group-action reading  *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From pgg_smc Require Import smc_interpreter pgg_instance.
From pgg_smc Require Import psl211_exec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** psl211_profile_endpoints — at every content readout, the executed
    endpoints of a run over this profile are its static group-action reading.
    Keeping the readout a variable removes the dealt card from the statement,
    so the equation holds of every run driven over this profile: the
    dealer-dealt mode reads it through profile_endpointsE and the
    supplied-layout mode through supplied_endpointsE.  This is what carries a
    claim about the interpreter's messages to a claim about the group action,
    and every security statement of this instance is made on the group-action
    side. *)
Lemma psl211_profile_endpoints :
  profile_endpoints_stmt psl211_algebra psl211_fuel.
Proof.
  Time by vm_compute.
  Optimize Proof.
  Optimize Heap.
Time Qed.
