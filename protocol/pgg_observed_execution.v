(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* ObservedExecution: one executed run packed with its static observation     *)
(*                                                                            *)
(* An ObservedExecution bundles a MonodromyProfile, an ExecutionPlug over     *)
(* that profile, the process offset the run is read at, the static            *)
(* group-action observation the run realises, the value it recovers, and the  *)
(* three run facts: termination, the endpoint equation and static recovery.   *)
(* The record has no parameter. Its plug field depends on its own profile     *)
(* field, its three proof fields quantify over every run argument and every   *)
(* cut, and the group-membership hypothesis on the cut appears on the         *)
(* recovery field alone.                                                      *)
(*                                                                            *)
(* Module OE holds the record together with the derivations it supports.      *)
(* Each derivation is one application of the corresponding theorem of         *)
(* pgg_execution_plug.v to the record's own fields, so no proof of that file  *)
(* is repeated here. The five raw-row extractors are specialisations of the   *)
(* generic extractors and carry no equation: the record has no field          *)
(* relating a raw trace row to a card content, so a raw-row equation is not   *)
(* derivable at this generality and is stated per instance instead.           *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   ObservedExecution     == the packed run: profile, plug, offset, static   *)
(*                            observation, expected value and three run facts *)
(*   oe_participant_trace  == the executed trace of the run's seat-i player   *)
(*   oe_input_trace        == the executed trace of committing party j        *)
(*   oe_dealer_trace       == the executed trace of the run's dealer          *)
(*   oe_verifier_trace     == the executed trace of the run's verifier        *)
(*   oe_coalition_trace    == the run's coalition raw traces                  *)
(*                                                                            *)
(* Key results:                                                               *)
(*   oe_endpoints_size       == the run collects one endpoint per seat        *)
(*   oe_run_recovers         == decoding the executed endpoints returns the   *)
(*                              expected value                                *)
(*   oe_run_correct          == termination, endpoint count and recovery      *)
(*   oe_seat_endpointE       == seat i's endpoint is the static observation   *)
(*                              at seat i                                     *)
(*   oe_coalition_endpointsE == a coalition's endpoint readings are the       *)
(*                              static observation over its seats             *)
(*                                                                            *)
(* The in-scope values filling this record are pgl27_observed                 *)
(* (instances/pgl27/pgl27_exec.v), the eight-card orbit run at cut index 0,   *)
(* and five_card_observed (instances/kim2025/five_card_exec.v), the five-card *)
(* run at cut index 0, which the den Boer and the Kim members of the          *)
(* five-card family share through den_boer_observed.                          *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Module OE.

(* Set Implicit Arguments demotes every binder occurring in the type of a
   later one. In this package that binder is the record argument of nearly
   every declaration: oe_profile occurs in the type of oe_execution, and the
   record itself occurs in the type of the run argument of every derived
   declaration, so oe_endpoints oe x w0 would elaborate oe against the type of
   x. The three proof-field projections and the nine derived declarations are
   affected; the five data-field projections take no further argument and are
   not. One module-level flag replaces fourteen Arguments lines. *)
Unset Implicit Arguments.

(* One executed run of a plugged monodromy profile at a fixed process
   offset, together with the static observation it realises and the value it
   recovers. A constructor supplies the profile oe_profile, the execution
   plug oe_execution over that same profile, the process offset oe_P_idx,
   the static observation oe_content_obs, the expected value oe_expected and
   the three run facts oe_terminates, oe_endpoints and oe_static_recon.
   Its plug field depends on its own profile field, its three proof fields
   quantify over every run argument and every cut, and the group-membership
   hypothesis on the cut appears on the recovery field alone. *)
Record ObservedExecution := MkObservedExecution {
  (* oe_profile is the program data of the run: the group action, the secret
     carrier, the starting layout and the reconstruction plug. *)
  oe_profile     : MonodromyProfile ;
  (* oe_execution is the execution plug over oe_profile itself, not over some
     other profile: the field's type mentions the previous field, which is what
     makes the record self-contained. *)
  oe_execution   : ExecutionPlug oe_profile ;
  (* oe_P_idx is the process offset the run is read at. *)
  oe_P_idx       : nat ;
  (* oe_content_obs is the static group-action observation: the card content a
     seat sees, as a function of the run argument, the cut and the seat's
     starting position. It mentions no interpreter state. *)
  oe_content_obs : ep_inputT oe_execution
                     -> pgg_gT (mp_M oe_profile)
                        * 'I_(pgg_N' (mp_M oe_profile)).+1
                     -> 'I_(pgg_N' (mp_M oe_profile)).+1 ;
  (* oe_expected is the value the run is expected to recover, in the profile's
     own secret carrier. *)
  oe_expected    : ep_inputT oe_execution -> mp_secretT oe_profile ;
  (* oe_terminates states that every process of the run reaches Finish, at
     every run argument and every cut. *)
  oe_terminates  : forall (x : ep_inputT oe_execution)
                          (w0 : pgg_gT (mp_M oe_profile)),
    (@exec_run oe_profile oe_execution x w0 oe_P_idx).1
    = nseq (size (@exec_procs oe_profile oe_execution x w0 oe_P_idx)) Finish ;
  (* oe_endpoints states that the executed endpoints are the static
     observation, at every run argument and every cut. *)
  oe_endpoints   : forall (x : ep_inputT oe_execution)
                          (w0 : pgg_gT (mp_M oe_profile)),
    @exec_endpoints oe_profile oe_execution x w0 oe_P_idx
    = @exec_static_endpoints oe_profile oe_execution oe_content_obs x w0 ;
  (* oe_static_recon states that decoding the static observation returns the
     expected value. It is the only field carrying the group-membership
     hypothesis on the cut: reconstruction is invariant under the group, so the
     equation is claimed for cuts drawn from pgg_G and for no others. *)
  oe_static_recon : forall (x : ep_inputT oe_execution)
                           (w0 : pgg_gT (mp_M oe_profile)),
    w0 \in pgg_G (mp_M oe_profile) ->
    forall sz_ep : size (@exec_static_endpoints oe_profile oe_execution
                         oe_content_obs x w0)
                 = (pi_T' (mp_PI oe_profile)).+1,
    @exec_decode oe_profile oe_execution
      (@exec_static_endpoints oe_profile oe_execution oe_content_obs x w0)
      sz_ep
    = oe_expected x ;
}.

(******************************************************************************)
(*     The derivations, each one application of a pgg_execution_plug theorem  *)
(******************************************************************************)

(* The observed run collects exactly one endpoint per seat: exec_endpoints_size
   applied to the record's own endpoint equation, kept as a transparent
   Definition rather than a Lemma so oe_run_recovers can name this term and
   stay convertible with it. *)
Definition oe_endpoints_size (oe : ObservedExecution)
    (x : ep_inputT (oe_execution oe))
    (w0 : pgg_gT (mp_M (oe_profile oe))) :
  size (@exec_endpoints (oe_profile oe) (oe_execution oe) x w0 (oe_P_idx oe))
  = (pi_T' (mp_PI (oe_profile oe))).+1
  := exec_endpoints_size (oe_endpoints oe x w0).

(* Decoding the observed run's actually-executed endpoints returns the
   expected value oe_expected oe x, for any cut w0 in the group: this is
   exec_run_recovers specialised to the record's own three run facts,
   packaging the profile-level correctness theorem as a fact about the
   ObservedExecution value itself. *)
Theorem oe_run_recovers (oe : ObservedExecution)
    (x : ep_inputT (oe_execution oe))
    (w0 : pgg_gT (mp_M (oe_profile oe))) :
  w0 \in pgg_G (mp_M (oe_profile oe)) ->
  @exec_decode (oe_profile oe) (oe_execution oe)
    (@exec_endpoints (oe_profile oe) (oe_execution oe) x w0 (oe_P_idx oe))
    (oe_endpoints_size oe x w0)
  = oe_expected oe x.
Proof.
move=> Hw0.
exact: (@exec_run_recovers (oe_profile oe) (oe_execution oe)
          (oe_content_obs oe) (oe_expected oe) x w0 (oe_P_idx oe)
          (oe_endpoints oe x w0) (oe_static_recon oe x w0 Hw0)).
Qed.

(* The observed run reaches Finish at every process, collects exactly one
   endpoint per seat, and decodes those endpoints to oe_expected oe x, for
   any cut w0 in the group: exec_run_correct specialised to the record's own
   three run facts, the single conjunction downstream users of an
   ObservedExecution actually need. *)
Theorem oe_run_correct (oe : ObservedExecution)
    (x : ep_inputT (oe_execution oe))
    (w0 : pgg_gT (mp_M (oe_profile oe))) :
  w0 \in pgg_G (mp_M (oe_profile oe)) ->
  [/\ (@exec_run (oe_profile oe) (oe_execution oe) x w0 (oe_P_idx oe)).1
        = nseq (size (@exec_procs (oe_profile oe) (oe_execution oe)
                        x w0 (oe_P_idx oe))) Finish,
      size (@exec_endpoints (oe_profile oe) (oe_execution oe)
              x w0 (oe_P_idx oe))
        = (pi_T' (mp_PI (oe_profile oe))).+1 &
      @exec_decode (oe_profile oe) (oe_execution oe)
        (@exec_endpoints (oe_profile oe) (oe_execution oe)
           x w0 (oe_P_idx oe))
        (oe_endpoints_size oe x w0)
      = oe_expected oe x].
Proof.
move=> Hw0.
exact: (@exec_run_correct (oe_profile oe) (oe_execution oe)
          (oe_content_obs oe) (oe_expected oe) x w0 (oe_P_idx oe)
          (oe_terminates oe x w0) (oe_endpoints oe x w0)
          (oe_static_recon oe x w0 Hw0)).
Qed.

(* Seat i's actually-executed endpoint is the static observation at seat i:
   exec_seat_endpointE specialised to the record's own endpoint equation. *)
Lemma oe_seat_endpointE (oe : ObservedExecution)
    (x : ep_inputT (oe_execution oe))
    (w0 : pgg_gT (mp_M (oe_profile oe)))
    (i : 'I_(pi_T' (mp_PI (oe_profile oe))).+1) :
  @exec_seat_endpoint (oe_profile oe) (oe_execution oe) x w0 (oe_P_idx oe) i
  = oe_content_obs oe x (w0, tnth (pi_starts (mp_PI (oe_profile oe))) i).
Proof.
exact: (@exec_seat_endpointE (oe_profile oe) (oe_execution oe)
          (oe_content_obs oe) x w0 (oe_P_idx oe) (oe_endpoints oe x w0) i).
Qed.

(* A coalition C's endpoint readings on the observed run are the static
   observation restricted to its seats: exec_coalition_endpointsE
   specialised to the record's own endpoint equation, letting a security
   argument reason purely about oe_content_obs on C's seats. *)
Lemma oe_coalition_endpointsE (oe : ObservedExecution)
    (x : ep_inputT (oe_execution oe))
    (w0 : pgg_gT (mp_M (oe_profile oe)))
    (C : {set 'I_(pi_T' (mp_PI (oe_profile oe))).+1}) :
  @exec_coalition_endpoints (oe_profile oe) (oe_execution oe)
    x w0 (oe_P_idx oe) C
  = [ffun i => if i \in C
               then oe_content_obs oe x
                      (w0, tnth (pi_starts (mp_PI (oe_profile oe))) i)
               else ord0].
Proof.
exact: (@exec_coalition_endpointsE (oe_profile oe) (oe_execution oe)
          (oe_content_obs oe) x w0 (oe_P_idx oe) (oe_endpoints oe x w0) C).
Qed.

(******************************************************************************)
(*     The raw-row extractors, specialised to the package                     *)
(******************************************************************************)

(* These five are definitions only. The package carries no field relating a raw
   trace row to a card content, so no semantic raw-row equation is stated at
   this generality; the instances state their own. *)

(* The executed trace of the observed run's seat-i player:
   exec_participant_trace at the record's own plug and process offset. This
   is one participant seat's own message log, not yet an endpoint list. *)
Definition oe_participant_trace (oe : ObservedExecution)
    (x : ep_inputT (oe_execution oe))
    (w0 : pgg_gT (mp_M (oe_profile oe)))
    (i : 'I_(pi_T' (mp_PI (oe_profile oe))).+1) :=
  @exec_participant_trace (oe_profile oe) (oe_execution oe)
    x w0 (oe_P_idx oe) i.

(* The executed trace of the observed run's committing party j:
   exec_input_trace at the record's own plug and process offset. Only
   indices j below the length of the plug's input-process list denote an
   actual committing party. *)
Definition oe_input_trace (oe : ObservedExecution)
    (x : ep_inputT (oe_execution oe))
    (w0 : pgg_gT (mp_M (oe_profile oe))) (j : nat) :=
  @exec_input_trace (oe_profile oe) (oe_execution oe)
    x w0 (oe_P_idx oe) j.

(* The executed trace of the observed run's dealer: exec_dealer_trace at the
   record's own plug and process offset. The dealer row belongs to no
   participant coalition unless a theorem adds it explicitly. *)
Definition oe_dealer_trace (oe : ObservedExecution)
    (x : ep_inputT (oe_execution oe))
    (w0 : pgg_gT (mp_M (oe_profile oe))) :=
  @exec_dealer_trace (oe_profile oe) (oe_execution oe) x w0 (oe_P_idx oe).

(* The executed trace of the observed run's verifier: exec_verifier_trace at
   the record's own plug and process offset. This is a raw message log,
   distinct from the endpoint list oe_run_recovers decodes from it. *)
Definition oe_verifier_trace (oe : ObservedExecution)
    (x : ep_inputT (oe_execution oe))
    (w0 : pgg_gT (mp_M (oe_profile oe))) :=
  @exec_verifier_trace (oe_profile oe) (oe_execution oe) x w0 (oe_P_idx oe).

(* The observed run's coalition raw traces: exec_coalition_trace at the
   record's own plug and process offset. The observation covers only the
   selected participant seats, with no dealer, verifier or input row. *)
Definition oe_coalition_trace (oe : ObservedExecution)
    (x : ep_inputT (oe_execution oe))
    (w0 : pgg_gT (mp_M (oe_profile oe)))
    (C : {set 'I_(pi_T' (mp_PI (oe_profile oe))).+1}) :=
  @exec_coalition_trace (oe_profile oe) (oe_execution oe)
    x w0 (oe_P_idx oe) C.

End OE.

(* Restore the file-level setting the module turned off. *)
Set Implicit Arguments.
