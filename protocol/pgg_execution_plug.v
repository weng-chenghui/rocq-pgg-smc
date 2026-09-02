(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* ExecutionPlug: the execution layer over a MonodromyProfile                 *)
(*                                                                            *)
(* An ExecutionPlug over a MonodromyProfile carries the seven data that       *)
(* turn an algebraic profile into an executable piSMC run: the run argument   *)
(* type, the seat/share count bridge, the participant list with its           *)
(* enumeration equation, the content readout, the input processes and the     *)
(* interpreter fuel. The profile itself is unchanged: an execution plug is a  *)
(* second value over an existing profile.                                     *)
(*                                                                            *)
(* Section execution_of_profile derives from a plug the dealer, the session-  *)
(* typed process list, the interpreter run, the verifier endpoints, the       *)
(* per-seat and per-input-party traces, the coalition readings and the        *)
(* endpoint decoder. Its inner section run_of_static_observation derives,     *)
(* from a termination equation, an endpoint equation and a static recovery    *)
(* equation, that the run reaches Finish at every process, collects one       *)
(* endpoint per seat and decodes to the expected value.                       *)
(*                                                                            *)
(* The two input modes of the framework are the two smart constructors:       *)
(* dealer_secret_plug, whose runs have no committing parties, and             *)
(* committed_input_plug, whose runs carry one commit process per committing   *)
(* party.                                                                     *)
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
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     The execution plug                                                     *)
(******************************************************************************)

(* The execution layer over a MonodromyProfile: the seven data that turn an
   algebraic profile into an executable piSMC run. A constructor supplies
   the run argument type ep_inputT, the seat/share bridge ep_players_bridge,
   the participant list ep_players with its enumeration equation
   ep_playersE, the content readout ep_content, the input processes
   ep_input_procs and the interpreter fuel ep_fuel. The profile itself is
   unchanged by this record: an execution plug is a second value layered
   over an existing profile, not a replacement for it. *)
Record ExecutionPlug (mp : MonodromyProfile) :=
  MkExecutionPlug {
    (* ep_inputT is the carrier of one run argument. It may differ from the
       reconstructed secret type mp_secretT mp. *)
    ep_inputT         : Type ;
    (* ep_players_bridge is the type-level coherence condition between the
       piSMC seat tuple and the reconstruction share tuple. exec_decode
       transports an endpoint list along it. *)
    ep_players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)) ;
    (* ep_players is the concrete ordered seat list used by executable
       reduction. The stored list reduces in milliseconds where the canonical
       enumeration reduces to a large term stuck behind an opaque idP. *)
    ep_players        : seq 'I_(pi_T' (mp_PI mp)).+1 ;
    (* ep_playersE certifies that the cached list is exactly the canonical seat
       enumeration, so storing it gives no freedom to omit or reorder seats. *)
    ep_playersE       : ep_players = enum 'I_(pi_T' (mp_PI mp)).+1 ;
    (* ep_content turns a run argument and the committed input payloads into
       the card content readout the dealer uses to build the deck. *)
    ep_content        : ep_inputT -> seq 'I_(pgg_N' (mp_M mp)).+1
                          -> ('I_(pgg_N' (mp_M mp)).+1
                              -> 'I_(pgg_N' (mp_M mp)).+1) ;
    (* ep_input_procs supplies the additional committing-party processes. It
       records the input mode of the protocol family: empty at every argument
       for a dealer-secret instance, nonempty for a committed-input one. *)
    ep_input_procs    : ep_inputT
                          -> seq (aproc pgg_dtype
                                    (pgg_data (pgg_N' (mp_M mp)).+1)) ;
    (* ep_fuel selects the interpreter evaluation budget used by exec_run.
       Replacing a sufficient fuel value by another sufficient one does not
       define a different algebraic profile. *)
    ep_fuel           : nat ;
  }.

(* The execution plug of a dealer-dealt secret: the plug whose runs have no
   committing party, with an empty input-process list at every run
   argument, so the dealt secret is the only input the run receives. *)
Definition dealer_secret_plug (mp : MonodromyProfile)
    (inputT : Type)
    (players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)))
    (players : seq 'I_(pi_T' (mp_PI mp)).+1)
    (playersE : players = enum 'I_(pi_T' (mp_PI mp)).+1)
    (content : inputT -> seq 'I_(pgg_N' (mp_M mp)).+1
                 -> ('I_(pgg_N' (mp_M mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1))
    (fuel : nat) : ExecutionPlug mp :=
  @MkExecutionPlug mp inputT players_bridge players playersE
    content (fun _ => [::]) fuel.

(* The execution plug of a committed input: the plug whose runs carry the
   committing parties as an argument, one commit process per party, so the
   run argument is the value the parties committed rather than a secret the
   dealer already held. *)
Definition committed_input_plug (mp : MonodromyProfile)
    (inputT : Type)
    (players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)))
    (players : seq 'I_(pi_T' (mp_PI mp)).+1)
    (playersE : players = enum 'I_(pi_T' (mp_PI mp)).+1)
    (content : inputT -> seq 'I_(pgg_N' (mp_M mp)).+1
                 -> ('I_(pgg_N' (mp_M mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1))
    (input_procs : inputT
                     -> seq (aproc pgg_dtype (pgg_data (pgg_N' (mp_M mp)).+1)))
    (fuel : nat) : ExecutionPlug mp :=
  @MkExecutionPlug mp inputT players_bridge players playersE
    content input_procs fuel.

(******************************************************************************)
(*     The run, the traces and the decoder derived from the plug              *)
(******************************************************************************)

Section execution_of_profile.

Variable mp : MonodromyProfile.
Variable e : ExecutionPlug mp.

(* The dealer occupies process identifier 0, the first entry of the run's
   process list. *)
Definition exec_dealer_id : nat := 0.

(* The verifier occupies process identifier 1, the entry following the
   dealer. *)
Definition exec_verifier_id : nat := 1.

(* Seat i occupies process identifier 2 + i: the seats fill the identifiers
   2 .. (pi_T' (mp_PI mp)).+2, immediately after the dealer and verifier. *)
Definition exec_seat_id (i : 'I_(pi_T' (mp_PI mp)).+1) : nat := 2 + i.

(* Committing party j occupies process identifier (pi_T' (mp_PI mp)).+3 + j,
   the identifiers following the dealer, the verifier and every seat. *)
Definition exec_input_id (j : nat) : nat := (pi_T' (mp_PI mp)).+3 + j.

(* The process identifiers of the run's input processes: exec_input_id read
   at each position of ep_input_procs e x, one identifier per committing
   party the plug's argument x actually supplies. *)
Definition exec_input_ids (x : ep_inputT e) : seq nat :=
  [seq exec_input_id j | j <- iota 0 (size (e.(ep_input_procs) x))].

(* The dealer of the run: dealer_with_input_encoding instantiated at mp_PI
   mp with the plug's content readout, the singleton deck [:: w0], the input
   identifiers exec_input_ids and the plug's participant list. *)
Definition exec_dealer (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) :=
  dealer_with_input_encoding (mp_PI mp) (e.(ep_content) x) [:: w0]
    (exec_input_ids x) e.(ep_players) P_idx.

(* The session-typed process list of the run, in process-identifier order:
   the dealer, the verifier, one player per participant seat, then the
   input processes. *)
Definition exec_saprocs (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat)
    : seq (aproc pgg_dtype (pgg_data (pgg_N' (mp_M mp)).+1)) :=
  mk_aproc (exec_dealer x w0 P_idx)
    :: mk_aproc (exchange_verifier (mp_PI mp) e.(ep_players))
    :: mk_player_aprocs (mp_PI mp) e.(ep_players)
       ++ e.(ep_input_procs) x.

(* The erased process list exec_saprocs is built as: the plain-proc image
   the interpreter run_interp actually consumes. *)
Definition exec_procs (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  erase_aprocs (exec_saprocs x w0 P_idx).

(* The interpreter's result on the run: run_interp at fuel ep_fuel e on
   exec_procs, a pair of the final process states and the per-process
   traces every downstream extractor reads from. *)
Definition exec_run (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  run_interp e.(ep_fuel) (exec_procs x w0 P_idx).

(* The verifier's collected endpoints: the endpoint reading of the
   verifier's row (process id exec_verifier_id) of exec_run's traces. *)
Definition exec_endpoints (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) :=
  endpoints_of_trace (nth [::] (exec_run x w0 P_idx).2 exec_verifier_id).

(* The executed trace of the verifier: the run's raw process-id
   exec_verifier_id row. This is a raw message log, distinct from the
   endpoint list exec_endpoints decodes from it below. *)
Definition exec_verifier_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) :=
  nth [::] (exec_run x w0 P_idx).2 exec_verifier_id.

(* exec_endpoints is the endpoint reading of exec_verifier_trace: the
   verifier's collected endpoints and the verifier's raw executed row are
   the same data viewed two ways, one decoded and one not. *)
Lemma exec_endpoints_verifier_traceE (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) :
  exec_endpoints x w0 P_idx
  = endpoints_of_trace (exec_verifier_trace x w0 P_idx).
Proof. by []. Qed.

(* The executed trace of the seat-i player: the run's process-id
   exec_seat_id i row. This is one participant seat's own message log, not
   yet a finite-distribution observable, since a raw sequence of session
   messages carries no probability structure by itself. *)
Definition exec_participant_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (i : 'I_(pi_T' (mp_PI mp)).+1) :=
  nth [::] (exec_run x w0 P_idx).2 (exec_seat_id i).

(* The executed trace of committing party j: the run's process-id
   exec_input_id j row, distinct from any dealer row. Only indices j below
   the length of ep_input_procs e x denote an actual committing party; a
   larger j falls outside the run and the default empty trace is returned. *)
Definition exec_input_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (j : nat) :=
  nth [::] (exec_run x w0 P_idx).2 (exec_input_id j).

(* The executed trace of the dealer: the run's process-id exec_dealer_id
   row. The dealer row belongs to no participant coalition unless a theorem
   adds it explicitly, since coalitions in this development range over
   participant seats, not over the dealer or verifier. *)
Definition exec_dealer_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) :=
  nth [::] (exec_run x w0 P_idx).2 exec_dealer_id.

(* The coalition's executed raw traces: the finfun sending a seat in C to
   its executed trace and a seat outside C to the empty trace. The
   observation is restricted to the selected participant seats, with no
   dealer, verifier or input row included, matching the coalition model of
   this development where only seats can be corrupted. *)
Definition exec_coalition_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (C : {set 'I_(pi_T' (mp_PI mp)).+1})
    : {ffun 'I_(pi_T' (mp_PI mp)).+1 -> seq (pgg_data (pgg_N' (mp_M mp)).+1)} :=
  [ffun i => if i \in C then exec_participant_trace x w0 P_idx i else [::]].

(* The endpoint recorded for seat i: entry i of exec_endpoints, the single
   card position the verifier collected from that seat. *)
Definition exec_seat_endpoint (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (i : 'I_(pi_T' (mp_PI mp)).+1) : 'I_(pgg_N' (mp_M mp)).+1 :=
  nth ord0 (exec_endpoints x w0 P_idx) i.

(* The coalition's endpoint readings: the finfun sending a seat in C to its
   recorded endpoint and a seat outside C to ord0, the endpoint-level
   counterpart of exec_coalition_trace. *)
Definition exec_coalition_endpoints (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (C : {set 'I_(pi_T' (mp_PI mp)).+1})
    : {ffun 'I_(pi_T' (mp_PI mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1} :=
  [ffun i => if i \in C then exec_seat_endpoint x w0 P_idx i else ord0].

(* The plug's stored participant list has exactly one entry per seat, the
   fact exec_static_endpoints_size below needs to match the static
   observation's length against the seat count. *)
Lemma exec_players_size : size e.(ep_players) = (pi_T' (mp_PI mp)).+1.
Proof. by rewrite e.(ep_playersE) size_enum_ord. Qed.

(* The seat/share bridge ep_players_bridge restated in successor form: the
   fact exec_run_recovers uses to cast an endpoint list of length seat-count
   into the tuple type run_recover expects, of length share-count. *)
Lemma exec_seat_share_count :
  (pi_T' (mp_PI mp)).+1 = (ts_T' (rp_scheme (mp_plug mp))).+1.
Proof. by rewrite e.(ep_players_bridge). Qed.

(* The plug's endpoint decoder: an endpoint list of one card per seat,
   transported along the seat/share bridge into the argument type of
   run_recover and reconstructed there. This is the single point where a
   raw endpoint list is turned back into the profile's secret carrier. *)
Definition exec_decode (ep : seq 'I_(pgg_N' (mp_M mp)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mp)).+1) : mp_secretT mp :=
  run_recover (tcast (etrans Hsz exec_seat_share_count) (in_tuple ep)).

(* The static group-action observation over the seats: content_obs x read at
   the cut w0 and each participant's starting position, computed with no
   reference to the interpreter. This is the value run_of_static_observation
   below equates the actual executed endpoints against. *)
Definition exec_static_endpoints
    (content_obs : ep_inputT e -> pgg_gT (mp_M mp) * 'I_(pgg_N' (mp_M mp)).+1
                     -> 'I_(pgg_N' (mp_M mp)).+1)
    (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) :=
  [seq content_obs x (w0, tnth (pi_starts (mp_PI mp)) i) | i <- e.(ep_players)].

(* The static observation has exactly one entry per seat, following directly
   from exec_players_size, the fact exec_endpoints_size below needs once the
   executed endpoints are identified with the static observation. *)
Lemma exec_static_endpoints_size content_obs x w0 :
  size (exec_static_endpoints content_obs x w0) = (pi_T' (mp_PI mp)).+1.
Proof. by rewrite size_map exec_players_size. Qed.

(******************************************************************************)
(*     The interpreter output against the static observation                  *)
(******************************************************************************)

Section run_of_static_observation.

Variable content_obs :
  ep_inputT e -> pgg_gT (mp_M mp) * 'I_(pgg_N' (mp_M mp)).+1
    -> 'I_(pgg_N' (mp_M mp)).+1.
Variable expected : ep_inputT e -> mp_secretT mp.
Variables (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat).

(* Termination: every process of the run reaches Finish. *)
Hypothesis Hterm : (exec_run x w0 P_idx).1
  = nseq (size (exec_procs x w0 P_idx)) Finish.

(* Endpoint equation: the executed endpoints are the static observation. *)
Hypothesis Hep : exec_endpoints x w0 P_idx
  = exec_static_endpoints content_obs x w0.

(* Static recovery: decoding the static observation returns the expected
   value. *)
Hypothesis Hrecon : forall Hsz : size (exec_static_endpoints content_obs x w0)
    = (pi_T' (mp_PI mp)).+1,
  @exec_decode (exec_static_endpoints content_obs x w0) Hsz = expected x.

(* Under the endpoint equation Hep, the run collects exactly one endpoint
   per seat: the count fact exec_run_recovers below needs to type-check its
   decode call against run_recover's expected tuple length. *)
Lemma exec_endpoints_size : size (exec_endpoints x w0 P_idx)
  = (pi_T' (mp_PI mp)).+1.
Proof. by rewrite Hep exec_static_endpoints_size. Qed.

(* Decoding the run's actually-executed endpoints returns the expected value
   expected x: the termination equation Hterm gets the run to a state where
   endpoints exist to decode, the endpoint equation Hep identifies them with
   the static observation, and the static-recovery hypothesis Hrecon decodes
   that observation to expected x, so the composite decode of the real run
   trace matches. *)
Theorem exec_run_recovers :
  @exec_decode (exec_endpoints x w0 P_idx) exec_endpoints_size = expected x.
Proof. by move: exec_endpoints_size; rewrite Hep; exact: Hrecon. Qed.

(* Seat i's actually-executed endpoint is the static observation
   content_obs x (w0, tnth (pi_starts (mp_PI mp)) i): the pointwise form of
   the endpoint equation Hep, giving one seat's value without needing the
   whole endpoint list. *)
Lemma exec_seat_endpointE (i : 'I_(pi_T' (mp_PI mp)).+1) :
  exec_seat_endpoint x w0 P_idx i
  = content_obs x (w0, tnth (pi_starts (mp_PI mp)) i).
Proof.
rewrite /exec_seat_endpoint Hep /exec_static_endpoints e.(ep_playersE).
by rewrite (nth_map i) ?size_enum_ord // nth_ord_enum.
Qed.

(* A coalition C's endpoint readings are the static observation restricted
   to its seats: exec_coalition_endpoints x w0 P_idx C equals the finfun
   giving content_obs x (w0, tnth (pi_starts (mp_PI mp)) i) on i \in C and
   ord0 elsewhere. This is what lets a security argument reason about what a
   coalition sees purely in terms of the group action, without touching
   interpreter state. *)
Lemma exec_coalition_endpointsE (C : {set 'I_(pi_T' (mp_PI mp)).+1}) :
  exec_coalition_endpoints x w0 P_idx C
  = [ffun i => if i \in C
               then content_obs x (w0, tnth (pi_starts (mp_PI mp)) i)
               else ord0].
Proof.
apply/ffunP => i; rewrite /exec_coalition_endpoints !ffunE.
by case: ifP => // _; exact: exec_seat_endpointE.
Qed.

(* The coalition's endpoints listed in seat order are the static observation
   over the same seats: the sequence form of exec_coalition_endpointsE, used
   where a coalition's readings are consumed as an ordered list (for
   instance, fed to a finite-distribution construction) rather than as a
   finfun. *)
Lemma exec_coalition_endpoints_seqE (C : {set 'I_(pi_T' (mp_PI mp)).+1}) :
  [seq exec_seat_endpoint x w0 P_idx i | i <- enum C]
  = [seq content_obs x (w0, tnth (pi_starts (mp_PI mp)) i) | i <- enum C].
Proof. by apply: eq_map => i; exact: exec_seat_endpointE. Qed.

(* One run satisfies all three correctness facts at once: it reaches Finish
   at every process (Hterm), it collects exactly one endpoint per seat
   (exec_endpoints_size), and decoding those endpoints returns expected x
   (exec_run_recovers). This packages the three separately-provable
   hypotheses of the section into the single conjunction downstream
   consumers of a plugged profile actually need. *)
Theorem exec_run_correct :
  [/\ (exec_run x w0 P_idx).1 = nseq (size (exec_procs x w0 P_idx)) Finish,
      size (exec_endpoints x w0 P_idx) = (pi_T' (mp_PI mp)).+1 &
      @exec_decode (exec_endpoints x w0 P_idx) exec_endpoints_size
      = expected x].
Proof.
by split;
  [exact: Hterm | exact: exec_endpoints_size | exact: exec_run_recovers].
Qed.

End run_of_static_observation.

End execution_of_profile.
