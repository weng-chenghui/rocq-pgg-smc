(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_exec: the algebraic record of the twelve-card chirality instance    *)
(*              and the dealt run over it                                     *)
(*                                                                            *)
(* The twelve-card chirality instance is written as a PGGAlgebraic in the     *)
(* block surface of pgg_algebra_syntax.v: two generating permutations of      *)
(* twelve card positions, the inverse-closed three-letter walk alphabet, the  *)
(* Boolean chirality secret the orbit scheme deals, and the explicit seat     *)
(* list the interpreter reads because enum 'I_12 does not reduce.  From that  *)
(* one value the framework of pgg_instance.v derives the seat interface, the  *)
(* monodromy profile and the execution plug.  The run written here is the     *)
(* dealer-dealt one: the dealer draws the chirality bit, no party commits an  *)
(* input, and the interpreter fuel is psl211_fuel.  Of the three run facts    *)
(* termination is its only obligation, decided by reduction at fuel 220 in    *)
(* 0.49 s of vm_compute and 0.47 s of Qed (measured 2026-09-15 with Time in   *)
(* place, then removed); reconstruction follows from the coordinate law and   *)
(* uses no reduction, and the endpoint equation is stated once at the profile *)
(* in psl211_endpoints.v.                                                     *)
(*                                                                            *)
(* This file and its whole import closure lie below psl211_endpoints.v, whose *)
(* single declaration compiled on 2026-09-15 in 568 seconds of vm_compute and *)
(* 324 seconds of Qed, with a resident set reported at 10.45 GB through make  *)
(* and at 17.15 GB when the same reduction ran as probe P1b2 directly under   *)
(* /usr/bin/time -l, in a file that also carried the termination lemma.       *)
(* Rebuilding this file from byte-identical sources changes the library       *)
(* digest and invalidates that .vo.  The closure psl211_endpoints.v freezes   *)
(* is 35 files, this one included.                                            *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_players      == the twelve explicit seat ordinals                 *)
(*   psl211_algebra      == the algebraic data of the twelve-card chirality   *)
(*                          instance                                          *)
(*   psl211_fuel         == the interpreter fuel of the fourteen-process run  *)
(*   psl211_dealt_params == the run-level data of the dealer-dealt run        *)
(*   psl211_dealt_recon  == the reconstruction obligation of that run         *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_players_enumE    == the participant list is the seat enumeration  *)
(*   psl211_profileE         == the derived profile is psl211_profile         *)
(*   psl211_dealt_terminates == every process of the dealt run reaches Finish *)
(*                              inside the fuel                               *)
(*   profile_k_psl211_algebra == the derived privacy threshold is six         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From pgg_smc Require Import smc_interpreter.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_instance pgg_algebra_syntax.
From pgg_smc Require Import psl211_group psl211_closure psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** psl211_players — the twelve explicit seat ordinals.  Spelled out rather
    than enum 'I_12 so that the dealer's fold_senv reduces under vm_compute. *)
Definition psl211_players : seq 'I_(pi_T' psl211_PI).+1 :=
  [:: @Ordinal 12 0 isT; @Ordinal 12 1 isT; @Ordinal 12 2 isT;
      @Ordinal 12 3 isT; @Ordinal 12 4 isT; @Ordinal 12 5 isT;
      @Ordinal 12 6 isT; @Ordinal 12 7 isT; @Ordinal 12 8 isT;
      @Ordinal 12 9 isT; @Ordinal 12 10 isT; @Ordinal 12 11 isT].

(** psl211_players_enumE — the twelve-element participant list is the seat
    enumeration. *)
Lemma psl211_players_enumE : psl211_players = enum 'I_(pi_T' psl211_PI).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** psl211_algebra — the algebraic data of the twelve-card chirality
    instance: two generating permutations of twelve card positions, the
    inverse-closed three-letter walk alphabet with the proof that it
    generates the same group, the Boolean chirality secret the orbit scheme
    deals with its encoding, its class readout and its privacy obligation,
    and the seat list the run reads because enum 'I_12 does not reduce. *)
Definition psl211_algebra : PGGAlgebraic := algebra {
  mount   << psl211_gens >> ;
  walk    along psl211_moves by psl211_gen3_eq ;
  seat    players (ord_tuple 12) by psl211_starts_uniq ;
  secret  bool ;
  deal    psl211_orbit_scheme
          encode psl211_orbit_encode
          read   psl211_orbit_class
          private by psl211_private
          shuffled_by pgg_rho by psl211_orbit_recon_invariant ;
  cache   seats psl211_players by psl211_players_enumE }.

(** psl211_profileE — the profile derived from the algebra is the instance's
    own monodromy profile.  The two are the same term, so every theorem about
    psl211_profile is a theorem about the derived profile. *)
Lemma psl211_profileE : instance_profile psl211_algebra = psl211_profile.
Proof. by []. Qed.

(** psl211_fuel — the interpreter fuel of the fourteen-process run: the
    dealer, the verifier and the twelve seats.  220 steps, the fuel the
    eight-card instance uses.  The value has only to exceed the number of
    communication rounds: the interpreter halts once no process advances, so
    fuel past that number is never used, and that 220 exceeds it is decided
    by reduction, not by counting rounds. *)
Definition psl211_fuel : nat := 220.

(** psl211_dealt_params — the run-level data of a run that deals the
    chirality bit and recovers it: the run argument is the secret itself, no
    party commits an input, and the interpreter fuel is psl211_fuel.  The
    dealer-dealt mode is what leaves termination as the instance's only
    obligation among the three run facts. *)
Definition psl211_dealt_params : ExecutionParams psl211_algebra :=
  dealt_secret_params psl211_algebra psl211_fuel.

(** psl211_dealt_recon — the reconstruction obligation, derived by the
    framework from the coordinate law alone.  No reduction is used. *)
Definition psl211_dealt_recon : instance_recon_stmt psl211_dealt_params :=
  dealt_static_recon psl211_algebra psl211_fuel.

(** psl211_dealt_terminates — every process of the dealer-dealt run reaches
    Finish inside that fuel.  The reduction is symbolic in the cut, so it
    does not enumerate the group. *)
Lemma psl211_dealt_terminates : instance_terminates_stmt psl211_dealt_params.
Proof. by vm_compute. Qed.

(** profile_k_psl211_algebra — the privacy threshold the derived profile
    declares is six, so the security proposition of every program over this
    algebra quantifies over coalitions of at most five of the twelve seats.
    It is profile_k_psl211 read at the derived profile.  The programs' witness
    converts the framework's threshold hypothesis to the numeric bound
    directly, and this lemma records the number that conversion relies on. *)
Lemma profile_k_psl211_algebra :
  profile_k (instance_profile psl211_algebra) = 6.
Proof. by []. Qed.
