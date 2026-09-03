(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5_exec: the two ExecutionPlug values of the S_5 instance                  *)
(*                                                                            *)
(* The five-seat adjacent-transposition instance carries two execution plugs  *)
(* over the same profile s5_profile. The deterministic plug takes the dealt   *)
(* position 'I_5 as its run argument and reads the canonical shares           *)
(* ts_encode s5_scheme; the randomized plug takes the sampler tape            *)
(* 'rV['Z_5]_5 and reads the probability-free additive layout of that tape.   *)
(* Both use the participant list s5_run.s5_players and fuel 150. The two      *)
(* process lists are not equal: they share the profile and the seven-process  *)
(* session skeleton, and their dealt contents differ.                         *)
(*                                                                            *)
(* The run skeleton s5_aprocs_cut generalizes s5_trace.s5_aprocs_abs to an    *)
(* arbitrary cut, its identity cut giving s5_trace.s5_aprocs_abs back. Fed    *)
(* the layout of a tape it is s5_rprocs_cut, whose identity cut is            *)
(* s5_trace.s5_rprocs.                                                        *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   s5_exec_plug        == the deterministic execution plug over s5_profile  *)
(*   s5_content_obs      == the deterministic static observation: the share   *)
(*                          of the dealt position at the cut image of a       *)
(*                          starting position                                 *)
(*   s5_observed         == the ObservedExecution packing the deterministic   *)
(*                          plug, its static observation and its three run    *)
(*                          facts at process offset 0                         *)
(*   s5_rfree_share      == the j-th additive share of a tape, stated without *)
(*                          a realType                                        *)
(*   s5_rfree_layout     == the dealt layout of a tape                        *)
(*   s5_codec, s5_decodec == the identity codec between the 'Z_5 tape secret  *)
(*                          and the profile secret carrier 'I_5               *)
(*   s5_tape_secret      == coordinate 0 of a tape                            *)
(*   s5_aprocs_cut       == the seven-process skeleton at an abstract content *)
(*                          readout and an arbitrary cut                      *)
(*   s5_rprocs_cut       == that skeleton at the layout of a tape             *)
(*   s5_rand_exec_plug   == the randomized execution plug over s5_profile     *)
(*   s5_rcontent_obs     == the randomized static observation                 *)
(*   s5_rand_observed    == the ObservedExecution of the randomized plug      *)
(*                                                                            *)
(* Key results:                                                               *)
(*   s5_exec_endpoint_count == the deterministic run collects five endpoints  *)
(*   s5_exec_recovers    == the deterministic run decodes to the dealt        *)
(*                          position                                          *)
(*   s5_exec_correct     == termination, endpoint count and recovery of the   *)
(*                          deterministic run                                 *)
(*   s5_observed_recovers == the same recovery through the packaged           *)
(*                          observed execution                                *)
(*   s5_exec_seat_endpointE == seat i's endpoint is the share at the cut      *)
(*                          image of seat i's start                           *)
(*   s5_exec_coalition_endpointsE == a coalition's endpoint readings are the  *)
(*                          shares at the cut images of its seats             *)
(*   s5_exec_verifier_traceE == the derived verifier row is the verifier row  *)
(*                          of s5_procs                                       *)
(*   s5_exec_raw_traceE  == the derived raw seat trace is the trace of        *)
(*                          s5_procs at the seat's process identifier         *)
(*   s5_exec_seat_countE == the profile's seat index type is 'I_5             *)
(*   s5_codecK, s5_decodecK == the two carriers of the secret are identified  *)
(*                          by the codec                                      *)
(*   s5_tape_secretE     == the tape secret is the randomized sharing's       *)
(*                          secret                                            *)
(*   s5_rprocs_cut1      == the identity cut specializes to s5_rprocs         *)
(*   s5_rand_run_recovers == reconstruction returns the tape secret           *)
(*   s5_rand_endpoint_count == the randomized run collects five endpoints     *)
(*   s5_rand_exec_recovers == the randomized run decodes to the encoded tape  *)
(*                          secret                                            *)
(*   s5_rand_correct     == termination, endpoint count and recovery of the   *)
(*                          randomized run                                    *)
(*   s5_rand_observed_recovers == the same recovery through the packaged      *)
(*                          observed execution                                *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals zmodp matrix.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import pgg_raag_s5 pgg_raag_path s5_profile s5_run.
From pgg_smc Require Import pgg_leakage_witness pgg_randomized_sharing.
From pgg_smc Require Import pgg_canonical_sharing pgg_sharing_mechanism.
From pgg_smc Require Import pgg_trace_secrecy s5_trace.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(* Both s5_run and s5_trace declare a participant list named s5_players, so
   every occurrence below is written qualified. *)

Section s5_execution.

(** s5_M — the Gen_PGGTypes instantiation at N = 5 with the four adjacent
    transpositions of path_gen_tuple 3 as generators: the same monodromy
    template s5_PI and s5_plug already carry, respelled here because the
    instance files keep the notation section-local rather than exporting
    it. *)
Local Notation s5_M := (@Gen_PGGTypes 3 3 (path_gen_tuple 3)).

Let mpS : MonodromyProfile := s5_profile.

(* The participant list s5_run.s5_players is the five seats written as
   explicit ordinals. It is a reduction cache: the interpreter facts below are
   closed by vm_compute on the process list this literal builds, and enum
   'I_5 in its place leaves an unreduced enumeration inside the run. The fuel
   150 is pinned for the same reason, the termination and endpoint facts being
   computed at that fuel. *)

(** s5_players_enumE — the five-element participant list s5_run.s5_players
    equals the seat enumeration enum 'I_5. It bridges the concrete literal
    kept for vm_compute reduction (see the note above) with the abstract
    enumeration form the endpoint lemmas below are stated over. *)
Lemma s5_players_enumE :
  s5_run.s5_players = enum 'I_(pi_T' (mp_PI mpS)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(******************************************************************************)
(*     The deterministic correctness plug                                     *)
(******************************************************************************)

(** s5_exec_plug — the S_5 deterministic execution plug: the dealer-secret
    plug over s5_profile whose run argument is the dealt position 'I_5,
    whose content at position s is the canonical secret-sharing scheme's
    shares ts_encode s5_scheme s, and whose fuel is 150. The dealer-secret
    constructor leaves the input-process list empty, since this plug reads
    the dealt position directly rather than from an input commitment. This
    is the object s5_exec_correct and its neighbours below prove correct. *)
Definition s5_exec_plug : ExecutionPlug mpS :=
  @dealer_secret_plug mpS 'I_5 erefl s5_run.s5_players s5_players_enumE
    (fun s _ => tnth (ts_encode s5_scheme s)) 150.

(** s5_content_obs — the deterministic static observation: the share of
    position s at the cut image of a starting position,
    tnth (ts_encode s5_scheme s) (pgg_rho w0 p). This is the value the
    correctness theorems below show the executed endpoints equal, in place
    of interpreting the run. *)
Definition s5_content_obs (s : 'I_5)
    (p : pgg_gT (mp_M mpS) * 'I_(pgg_N' (mp_M mpS)).+1)
    : 'I_(pgg_N' (mp_M mpS)).+1 :=
  tnth (ts_encode s5_scheme s) (@pgg_rho (mp_M mpS) p.1 p.2).

(** s5_exec_procsE — the deterministic plug's derived process list unfolds to
    the instance's own process list s5_procs s w0. This and the next three
    lemmas rewrite the generic ExecutionPlug interface down to S5-native
    data (process list, fuel, participant list, process count); the
    termination and endpoint theorems below consume them by rewriting. *)
Lemma s5_exec_procsE (s : 'I_5) (w0 : pgg_gT s5_M) :
  @exec_procs mpS s5_exec_plug s w0 0 = s5_procs s w0.
Proof. by []. Qed.

(** s5_exec_fuelE — the plug's fuel ep_fuel s5_exec_plug is the instance's
    150, part of the same generic-to-native unfold cluster as
    s5_exec_procsE. *)
Lemma s5_exec_fuelE : ep_fuel s5_exec_plug = 150.
Proof. by []. Qed.

(** s5_exec_playersE — the plug's participant list ep_players s5_exec_plug is
    the instance's s5_run.s5_players, part of the same unfold cluster. *)
Lemma s5_exec_playersE : ep_players s5_exec_plug = s5_run.s5_players.
Proof. by []. Qed.

(** s5_exec_procs_size — the deterministic run's process list has seven
    entries (dealer, verifier, five players), completing the unfold
    cluster. *)
Lemma s5_exec_procs_size (s : 'I_5) (w0 : pgg_gT s5_M) :
  size (@exec_procs mpS s5_exec_plug s w0 0) = 7.
Proof. by []. Qed.

(** s5_exec_terminates — every process of the deterministic run reaches
    Finish after 150 fuel steps. This is the termination conjunct
    s5_exec_correct packages together with the endpoint-count and
    recovery facts below. *)
Lemma s5_exec_terminates (s : 'I_5) (w0 : pgg_gT s5_M) :
  (@exec_run mpS s5_exec_plug s w0 0).1
  = nseq (size (@exec_procs mpS s5_exec_plug s w0 0)) Finish.
Proof.
rewrite s5_exec_procs_size /exec_run s5_exec_fuelE s5_exec_procsE.
exact: s5_run_terminates.
Qed.

(** s5_exec_endpoints — the deterministic run's verifier endpoints equal the
    static observation s5_content_obs evaluated at each seat's start. This
    replaces "run the interpreter and read its trace" with "evaluate a pure
    function," which is what lets s5_exec_recon below prove recovery without
    touching the interpreter. *)
Lemma s5_exec_endpoints (s : 'I_5) (w0 : pgg_gT s5_M) :
  @exec_endpoints mpS s5_exec_plug s w0 0
  = @exec_static_endpoints mpS s5_exec_plug s5_content_obs s w0.
Proof.
rewrite /exec_endpoints /exec_run s5_exec_fuelE s5_exec_procsE
        /exec_verifier_id.
rewrite /exec_static_endpoints s5_exec_playersE s5_players_enumE.
exact: s5_endpoints.
Qed.

(** s5_exec_endpoint_count — the deterministic run collects exactly five
    endpoints, one per seat. *)
Lemma s5_exec_endpoint_count (s : 'I_5) (w0 : pgg_gT s5_M) :
  size (@exec_endpoints mpS s5_exec_plug s w0 0) = 5.
Proof. by rewrite (exec_endpoints_size (s5_exec_endpoints s w0)). Qed.

(** s5_exec_decodeE — the plug's decoder exec_decode s5_exec_plug agrees with
    the scheme's reconstruction function ts_recon s5_scheme on any endpoint
    list of the right length, feeding s5_exec_recon below. *)
Lemma s5_exec_decodeE (ep : seq 'I_(pgg_N' (mp_M mpS)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpS)).+1)
    (Hsz' : size ep = (ts_T' s5_scheme).+1) :
  @exec_decode mpS s5_exec_plug ep Hsz
  = ts_recon s5_scheme (tcast Hsz' (in_tuple ep)).
Proof.
by rewrite /exec_decode /run_recover (eq_irrelevance (etrans Hsz _) Hsz').
Qed.

(** s5_exec_recon — decoding the static-observation endpoints returns the
    dealt position s, for any cut w0 in the group and any proof of the
    endpoint count. This is the pure-function recovery fact that
    s5_exec_endpoints above lets s5_exec_recovers restate as a fact about
    the interpreted run. *)
Lemma s5_exec_recon (s : 'I_5) (w0 : pgg_gT s5_M) :
  w0 \in pgg_G s5_M ->
  forall Hsz : size (@exec_static_endpoints mpS s5_exec_plug
                       s5_content_obs s w0)
               = (pi_T' (mp_PI mpS)).+1,
  @exec_decode mpS s5_exec_plug
    (@exec_static_endpoints mpS s5_exec_plug s5_content_obs s w0) Hsz = s.
Proof.
move=> Gw0.
rewrite -s5_exec_endpoints /exec_endpoints /exec_run s5_exec_fuelE
        s5_exec_procsE /exec_verifier_id => Hsz.
rewrite (s5_exec_decodeE Hsz (s5_endpoints_size s w0)).
exact: (s5_run_recovers s Gw0).
Qed.

(* Recovery is exported in three forms per plug, as at the other instances:
   the standalone equation below, the third conjunct of the combined statement
   s5_exec_correct, and the same equation with the size proof taken from the
   observed-execution record in s5_observed_recovers. The three are convertible
   and each is the form one client layer expects. *)

(** s5_exec_recovers — the deterministic run decodes to the dealt position:
    exec_decode applied to the executed endpoints of s5_exec_plug at
    position s and cut w0 returns s, for any cut w0 in the group. The first
    of the three recovery forms noted above. *)
Theorem s5_exec_recovers (s : 'I_5) (w0 : pgg_gT s5_M)
    (Gw0 : w0 \in pgg_G s5_M) :
  @exec_decode mpS s5_exec_plug
    (@exec_endpoints mpS s5_exec_plug s w0 0)
    (exec_endpoints_size (s5_exec_endpoints s w0)) = s.
Proof.
exact: (@exec_run_recovers mpS s5_exec_plug s5_content_obs (fun s : 'I_5 => s)
          s w0 0 (s5_exec_endpoints s w0) (s5_exec_recon Gw0)).
Qed.

(** s5_exec_correct — the deterministic run of s5_exec_plug reaches Finish
    at each of its seven processes, collects one endpoint per seat, and
    decodes to the dealt position s, for any cut w0 in the group: the three
    correctness facts above (termination, endpoint count, recovery)
    packaged into one statement. *)
Theorem s5_exec_correct (s : 'I_5) (w0 : pgg_gT s5_M)
    (Gw0 : w0 \in pgg_G s5_M) :
  [/\ (@exec_run mpS s5_exec_plug s w0 0).1
        = nseq (size (@exec_procs mpS s5_exec_plug s w0 0)) Finish,
      size (@exec_endpoints mpS s5_exec_plug s w0 0)
        = (pi_T' (mp_PI mpS)).+1 &
      @exec_decode mpS s5_exec_plug
        (@exec_endpoints mpS s5_exec_plug s w0 0)
        (exec_endpoints_size (s5_exec_endpoints s w0)) = s].
Proof.
exact: (@exec_run_correct mpS s5_exec_plug s5_content_obs (fun s : 'I_5 => s)
          s w0 0 (s5_exec_terminates s w0) (s5_exec_endpoints s w0)
          (s5_exec_recon Gw0)).
Qed.

(** s5_observed — the ObservedExecution record packaging s5_profile with
    plug s5_exec_plug at process offset 0, static observation
    s5_content_obs, expected value the dealt position, and the three run
    facts s5_exec_terminates, s5_exec_endpoints and s5_exec_recon proved
    above. This is the uniform form the coalition-view and leakage
    analyses elsewhere in the instance consume, rather than the plug and
    its three facts separately. *)
Definition s5_observed : OE.ObservedExecution :=
  OE.MkObservedExecution mpS s5_exec_plug 0
    s5_content_obs (fun s : 'I_5 => s)
    s5_exec_terminates s5_exec_endpoints (@s5_exec_recon).

(** s5_observed_recovers — the packaged deterministic run decodes to the
    dealt position: exec_decode applied to the executed endpoints of
    s5_observed at position s and cut w0 returns s, for any cut w0 in the
    group. The second of the three recovery forms, restated through the
    ObservedExecution record. *)
Theorem s5_observed_recovers (s : 'I_5) (w0 : pgg_gT s5_M)
    (Gw0 : w0 \in pgg_G s5_M) :
  @exec_decode mpS s5_exec_plug
    (@exec_endpoints mpS s5_exec_plug s w0 0)
    (OE.oe_endpoints_size s5_observed s w0) = s.
Proof. exact: (OE.oe_run_recovers s5_observed s w0 Gw0). Qed.

(******************************************************************************)
(*     The observer types read off the deterministic plug                     *)
(******************************************************************************)

(** s5_exec_seat_endpointE — seat i's endpoint equals the static observation
    at the cut image of seat i's start,
    s5_content_obs s (w0, tnth (pi_starts (mp_PI mpS)) i). This is the
    per-seat reading a single coalition member sees, before any coalition
    view is assembled. *)
Lemma s5_exec_seat_endpointE (s : 'I_5) (w0 : pgg_gT s5_M)
    (i : 'I_(pi_T' (mp_PI mpS)).+1) :
  @exec_seat_endpoint mpS s5_exec_plug s w0 0 i
  = s5_content_obs s (w0, tnth (pi_starts (mp_PI mpS)) i).
Proof. exact: (exec_seat_endpointE (s5_exec_endpoints s w0) i). Qed.

(** s5_exec_coalition_endpointsE — a coalition C's endpoint readings are the
    finfun sending each seat in C to the share of s at the cut image of that
    seat's start, and every seat outside C to ord0. This is the object a
    secrecy statement conditions on: what a coalition can read is exactly
    this finfun, nothing outside C. *)
Lemma s5_exec_coalition_endpointsE (s : 'I_5) (w0 : pgg_gT s5_M)
    (C : {set 'I_(pi_T' (mp_PI mpS)).+1}) :
  @exec_coalition_endpoints mpS s5_exec_plug s w0 0 C
  = [ffun i => if i \in C
               then s5_content_obs s (w0, tnth (pi_starts (mp_PI mpS)) i)
               else ord0].
Proof. exact: (exec_coalition_endpointsE (s5_exec_endpoints s w0) C). Qed.

(** s5_exec_verifier_traceE — the derived verifier row exec_verifier_trace
    s5_exec_plug s w0 0 is the verifier row of the raw interpreter trace of
    s5_procs s w0, row index 1. *)
Lemma s5_exec_verifier_traceE (s : 'I_5) (w0 : pgg_gT s5_M) :
  @exec_verifier_trace mpS s5_exec_plug s w0 0
  = nth [::] (run_interp 150 (s5_procs s w0)).2 1.
Proof.
by rewrite /exec_verifier_trace /exec_run s5_exec_fuelE s5_exec_procsE.
Qed.

(** s5_exec_raw_traceE — seat i's derived raw trace exec_participant_trace
    s5_exec_plug s w0 0 i is the row of the raw interpreter trace of
    s5_procs s w0 at that seat's process identifier, row index 2 + i. *)
Lemma s5_exec_raw_traceE (s : 'I_5) (w0 : pgg_gT s5_M)
    (i : 'I_(pi_T' (mp_PI mpS)).+1) :
  @exec_participant_trace mpS s5_exec_plug s w0 0 i
  = nth [::] (run_interp 150 (s5_procs s w0)).2 (2 + i).
Proof.
by rewrite /exec_participant_trace /exec_seat_id /exec_run s5_exec_fuelE
   s5_exec_procsE.
Qed.

(** s5_exec_seat_countE — the profile's seat index cardinality
    (pi_T' (mp_PI mpS)).+1 is 5, the seat index type shared by the
    execution layer above and the five-seat coalition view elsewhere in
    the instance. *)
Lemma s5_exec_seat_countE : (pi_T' (mp_PI mpS)).+1 = 5.
Proof. by []. Qed.

(******************************************************************************)
(*     The probability-free additive layout                                   *)
(******************************************************************************)

(** s5_rfree_share — the j-th additive share of a sampler tape, stated
    without a realType: coordinate j+1 of the tape when j is below the last
    index, and the residue of coordinate 0 against the sum of the first
    four coordinates at the last index. Dropping the realType lets this
    definition and s5_rfree_layout below be shared by every realType
    instantiation of the randomized plug, rather than reproved at each
    one. *)
Definition s5_rfree_share (j : 'I_5) (u : 'rV['Z_5]_5) : 'Z_5 :=
  if unlift ord_max j is Some j' then u ord0 (lift ord0 j')
  else (u ord0 ord0 - \sum_(i < 4) u ord0 (lift ord0 i))%R.

(** s5_rfree_shareE — the probability-free share s5_rfree_share agrees with
    the randomized sharing's share rsh_share (unif_randomized_sharing R 3 4),
    at every realType. This is the bridge that lets the realType-free
    definition above stand in for the probabilistic one wherever only its
    value, not its distribution, is needed. *)
Lemma s5_rfree_shareE (R : realType) (j : 'I_5) :
  rsh_share (@unif_randomized_sharing R 3 4) j = s5_rfree_share j.
Proof.
apply: boolp.funext => u; rewrite /s5_rfree_share /rsh_share.
by case: (unlift ord_max j) => [k|] //=; rewrite sumrRVE.
Qed.

(** s5_rfree_layout — the dealt layout at a tape: position i carries share
    i, computed by s5_rfree_share without reference to a realType. The
    probability-free twin of s5_trace.s5_rlayout. *)
Definition s5_rfree_layout (u : 'rV['Z_5]_5) : 5.-tuple 'I_5 :=
  [tuple s5_rfree_share i u | i < 5].

(** s5_rfree_layoutE — the probability-free layout s5_rfree_layout agrees
    with the randomized layout s5_rlayout R, at every realType, by
    s5_rfree_shareE applied coordinatewise. *)
Lemma s5_rfree_layoutE (R : realType) (u : 'rV['Z_5]_5) :
  s5_rlayout R u = s5_rfree_layout u.
Proof.
apply: eq_from_tnth => i; rewrite /s5_rlayout /s5_rfree_layout !tnth_mktuple.
by rewrite /s5_rs s5_rfree_shareE.
Qed.

(** s5_rfree_sum — the five additive shares of a tape sum (as naturals
    before the mod-5 reduction) to the tape's secret coordinate u ord0
    ord0. This is the additive-sharing correctness fact before it is
    read mod 5. *)
Lemma s5_rfree_sum (u : 'rV['Z_5]_5) :
  (\sum_(i < 5) s5_rfree_share i u)%R = u ord0 ord0.
Proof.
have Hw : forall i : 'I_4, widen_ord (leqnSn 4) i = lift ord_max i.
  by move=> i; apply: val_inj; symmetry; exact: lift_max.
rewrite big_ord_recr /=.
under eq_bigr do rewrite Hw /s5_rfree_share liftK.
rewrite /s5_rfree_share unlift_none /=.
by rewrite GRing.addrC GRing.subrK.
Qed.

(** zp5_sum_val — for any finite family of Z/5 values, the residue mod 5 of
    the sum of their natural-number representatives equals the natural
    representative of their ring sum. This is the generic Z/5 fact
    s5_rfree_valid needs to move between the additive-sharing arithmetic
    (natural sums) and the scheme's validity predicate (ring sums mod 5). *)
Lemma zp5_sum_val (n : nat) (f : 'I_n -> 'Z_5) :
  (\sum_(i < n) (f i : nat)) %% 5 = ((\sum_(i < n) f i)%R : 'Z_5) :> nat.
Proof.
rewrite -(@val_Zp_nat 5 isT) GRing.natr_sum.
by under eq_bigr do rewrite natr_Zp.
Qed.

(** s5_rfree_valid — the probability-free layout s5_rfree_layout u satisfies
    the scheme's validity predicate ts_valid s5_scheme for the secret u ord0
    ord0: it is a genuine sum-mod-5 sharing, not merely a tuple of values.
    This is the hypothesis the reconstruction machinery below needs to
    recover the secret from the layout. *)
Lemma s5_rfree_valid (u : 'rV['Z_5]_5) :
  ts_valid s5_scheme (u ord0 ord0) (s5_rfree_layout u).
Proof.
rewrite /s5_scheme /sum_mod_scheme /ts_valid /sum_mod_valid_pred.
under eq_bigr do rewrite tnth_mktuple.
by rewrite zp5_sum_val s5_rfree_sum.
Qed.

(******************************************************************************)
(*     The ordinal codec between the randomized secret and the profile secret *)
(******************************************************************************)

(** s5_codec — the codec from the Z/5 tape secret to the profile secret
    carrier 'I_5: the identity, since the two carriers are definitionally
    the same ordinal type ('Z_5 = 'I_(Zp_trunc 5).+2 = 'I_5). It exists so
    the randomized-plug correctness theorems can state their conclusion in
    the profile's own secret type rather than leaking the tape
    representation. *)
Definition s5_codec (z : 'Z_5) : 'I_5 := z.

(** s5_decodec — the codec from the profile secret carrier back to Z/5: the
    identity in the other direction, s5_codec's inverse. *)
Definition s5_decodec (i : 'I_5) : 'Z_5 := i.

(** s5_codecK — cancel s5_codec s5_decodec: decoding cancels encoding, one
    half of witnessing that the two secret carriers are identified, not
    merely related. *)
Lemma s5_codecK : cancel s5_codec s5_decodec.
Proof. by []. Qed.

(** s5_decodecK — cancel s5_decodec s5_codec: encoding cancels decoding, the
    other half of the carrier identification. *)
Lemma s5_decodecK : cancel s5_decodec s5_codec.
Proof. by []. Qed.

(** s5_tape_secret — the secret coordinate of a sampler tape: coordinate 0,
    the value the additive sharing in s5_rfree_share splits into shares. *)
Definition s5_tape_secret (u : 'rV['Z_5]_5) : 'Z_5 := u ord0 ord0.

(** s5_tape_secretE — the probability-free tape secret s5_tape_secret agrees
    with the randomized sharing's secret rsh_secret (unif_randomized_sharing
    R 3 4), at every realType, identifying the run argument's secret
    coordinate with the secret the probabilistic scheme shares. *)
Lemma s5_tape_secretE (R : realType) :
  rsh_secret (@unif_randomized_sharing R 3 4) = s5_tape_secret.
Proof. by []. Qed.

(******************************************************************************)
(*     The cut-generalized run skeleton                                       *)
(******************************************************************************)

(** s5_aprocs_cut — the seven-process S_5 run skeleton (dealer, verifier,
    five players) at an abstract content readout g and an arbitrary cut w0:
    s5_trace.s5_aprocs_abs with the dealer's deck fixed to the singleton
    [:: w0] rather than the identity cut. Generalizing the cut is what lets
    the randomized plug below reuse this skeleton at every group element,
    not just at 1. *)
Definition s5_aprocs_cut (g : 'I_5 -> 'I_5) (w0 : pgg_gT s5_M) :=
  erase_aprocs
  [:: mk_aproc (dealer_with_input_encoding s5_PI
                  (fun _ => g) [:: w0] [::] s5_run.s5_players 0)
    , mk_aproc (exchange_verifier s5_PI s5_run.s5_players)
    & player_aprocs s5_PI s5_run.s5_players].

(** s5_aprocs_cut1 — at the identity cut, s5_aprocs_cut collapses to
    s5_aprocs_abs g, confirming the generalization above is conservative. *)
Lemma s5_aprocs_cut1 (g : 'I_5 -> 'I_5) :
  s5_aprocs_cut g 1%g = s5_aprocs_abs g.
Proof. by []. Qed.

(** s5_rprocs_cut — the randomized run at a sampler tape u and an arbitrary
    cut w0: s5_aprocs_cut fed the probability-free layout s5_rfree_layout u
    as its content readout. *)
Definition s5_rprocs_cut (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :=
  s5_aprocs_cut (tnth (s5_rfree_layout u)) w0.

(** s5_rprocs_cut1 — at the identity cut, s5_rprocs_cut u collapses to the
    landed randomized process list s5_rprocs R u, at every realType: the
    randomized counterpart of s5_aprocs_cut1. *)
Lemma s5_rprocs_cut1 (R : realType) (u : 'rV['Z_5]_5) :
  s5_rprocs_cut u 1%g = s5_rprocs R u.
Proof.
by rewrite /s5_rprocs_cut s5_aprocs_cut1 /s5_rprocs s5_rfree_layoutE.
Qed.

(** s5_aprocs_cut_terminates — every process of the cut-generalized run
    reaches Finish after 150 fuel steps, decided by vm_compute since the
    generator g and cut w0 do not affect which processes terminate, only
    what they output. *)
Lemma s5_aprocs_cut_terminates (g : 'I_5 -> 'I_5) (w0 : pgg_gT s5_M) :
  (run_interp 150 (s5_aprocs_cut g w0)).1 = nseq 7 Finish.
Proof. by vm_compute. Qed.

(** s5_aprocs_cut_endpoints — the cut-generalized run's verifier endpoints
    are the abstract readout g applied to the cut image of each seat's
    start, over the five players. This is the general fact both the
    deterministic and randomized endpoint lemmas below specialize, at
    g = the scheme's shares and g = the probability-free layout
    respectively. *)
Lemma s5_aprocs_cut_endpoints (g : 'I_5 -> 'I_5) (w0 : pgg_gT s5_M) :
  endpoints_of_trace (nth [::] (run_interp 150 (s5_aprocs_cut g w0)).2 1)
  = [seq g (@pgg_rho s5_M w0 (tnth (pi_starts s5_PI) i))
     | i <- s5_run.s5_players].
Proof.
rewrite /s5_aprocs_cut /dealer_with_input_encoding.
exact: (@s5_verifier_endpoints (fun=> g) w0 (ord_tuple 5) s5_starts_uniq).
Qed.

(******************************************************************************)
(*     The randomized security plug                                           *)
(******************************************************************************)

(** s5_recon_perm_invariant — sum-mod reconstruction is invariant under any
    group-element permutation of its coordinates: reconstructing from
    shares reindexed by g \in pgg_G s5_M returns the same secret as
    reconstructing from the unpermuted shares. This is what lets recovery
    hold at every cut w0, not only the identity cut, since a nontrivial cut
    is exactly a coordinate permutation applied to the shares. *)
Lemma s5_recon_perm_invariant :
  @ts_recon_perm_invariant _ (pgg_G s5_M) _ _ s5_scheme (@pgg_rho s5_M).
Proof.
move=> g s' shares Hg Hvalid.
rewrite /s5_scheme.
apply: sum_mod_scheme_correct.
rewrite /sum_mod_valid_pred in Hvalid *.
rewrite -Hvalid; congr (_ %% _).
under eq_bigr do rewrite tnth_mktuple.
symmetry; rewrite (reindex_inj (@perm_inj _ (@pgg_rho s5_M g))).
by apply: eq_bigr.
Qed.

(** s5_rand_endpoints_size — the randomized run collects one endpoint per
    share of the scheme, matching (ts_T' s5_scheme).+1, so the endpoint
    list can be cast into the tuple type ts_recon expects. *)
Lemma s5_rand_endpoints_size (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  size (endpoints_of_trace (nth [::] (run_interp 150 (s5_rprocs_cut u w0)).2 1))
  = (ts_T' s5_scheme).+1.
Proof. by rewrite /s5_rprocs_cut s5_aprocs_cut_endpoints size_map. Qed.

(** s5_rand_run_recovers — reconstructing the randomized run's endpoints
    returns the tape's secret coordinate: ts_recon s5_scheme applied to the
    cut-permuted endpoints of s5_rprocs_cut u w0 equals u ord0 ord0, for any
    cut w0 in the group. Correctness at an arbitrary cut, not only the
    identity, via s5_recon_perm_invariant. *)
Lemma s5_rand_run_recovers (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  w0 \in pgg_G s5_M ->
  ts_recon s5_scheme
    (tcast (s5_rand_endpoints_size u w0)
       (in_tuple (endpoints_of_trace
          (nth [::] (run_interp 150 (s5_rprocs_cut u w0)).2 1))))
  = u ord0 ord0.
Proof.
move=> Gw0.
have Hgoal : forall (ep : seq 'I_(pgg_N' s5_M).+1)
    (Hsz : size ep = (ts_T' s5_scheme).+1),
    ep = [seq tnth (s5_rfree_layout u)
                (pgg_rho w0 (tnth (pi_starts s5_PI) i))
          | i <- enum 'I_(pi_T' s5_PI).+1] ->
    ts_recon s5_scheme (tcast Hsz (in_tuple ep)) = u ord0 ord0.
  move=> ep Hsz Hep.
  rewrite -[u ord0 ord0](s5_recon_perm_invariant Gw0 (s5_rfree_valid u)).
  congr (ts_recon _ _).
  apply: eq_from_tnth => i.
  rewrite tcastE tnth_mktuple.
  rewrite (tnth_nth ord0) /= Hep.
  rewrite (nth_map i) ?nth_ord_enum ?tnth_ord_tuple;
    last by rewrite size_enum_ord ltn_ord.
  by [].
apply: Hgoal.
by rewrite /s5_rprocs_cut s5_aprocs_cut_endpoints s5_players_enumE.
Qed.

(** s5_rand_exec_plug — the S_5 randomized execution plug: the dealer-secret
    plug over s5_profile whose run argument is a sampler tape
    'rV['Z_5]_5, whose content is the probability-free additive layout
    s5_rfree_layout of that tape, and whose fuel is 150. The randomized
    counterpart of s5_exec_plug, replacing the encoder's deterministic
    shares with an additively-shared secret drawn from the tape. *)
Definition s5_rand_exec_plug : ExecutionPlug mpS :=
  @dealer_secret_plug mpS 'rV['Z_5]_5 erefl s5_run.s5_players s5_players_enumE
    (fun u _ => tnth (s5_rfree_layout u)) 150.

(** s5_rcontent_obs — the randomized static observation: the additive share
    at the cut image of a starting position,
    tnth (s5_rfree_layout u) (pgg_rho w0 p). The randomized counterpart of
    s5_content_obs. *)
Definition s5_rcontent_obs (u : 'rV['Z_5]_5)
    (p : pgg_gT (mp_M mpS) * 'I_(pgg_N' (mp_M mpS)).+1)
    : 'I_(pgg_N' (mp_M mpS)).+1 :=
  tnth (s5_rfree_layout u) (@pgg_rho (mp_M mpS) p.1 p.2).

(** s5_rand_procsE — the randomized plug's derived process list unfolds to
    s5_rprocs_cut u w0. This and the next three lemmas unfold the generic
    ExecutionPlug interface to randomized-plug data, the same role
    s5_exec_procsE and its neighbours play for the deterministic plug. *)
Lemma s5_rand_procsE (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  @exec_procs mpS s5_rand_exec_plug u w0 0 = s5_rprocs_cut u w0.
Proof. by []. Qed.

(** s5_rand_fuelE — the randomized plug's fuel ep_fuel s5_rand_exec_plug is
    150, part of the same unfold cluster as s5_rand_procsE. *)
Lemma s5_rand_fuelE : ep_fuel s5_rand_exec_plug = 150.
Proof. by []. Qed.

(** s5_rand_playersE — the randomized plug's participant list
    ep_players s5_rand_exec_plug is s5_run.s5_players, part of the same
    unfold cluster. *)
Lemma s5_rand_playersE : ep_players s5_rand_exec_plug = s5_run.s5_players.
Proof. by []. Qed.

(** s5_rand_procs_size — the randomized run's process list has seven
    entries, completing the unfold cluster. *)
Lemma s5_rand_procs_size (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  size (@exec_procs mpS s5_rand_exec_plug u w0 0) = 7.
Proof. by []. Qed.

(** s5_rand_terminates — every process of the randomized run reaches Finish
    after 150 fuel steps, the randomized counterpart of s5_exec_terminates. *)
Lemma s5_rand_terminates (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  (@exec_run mpS s5_rand_exec_plug u w0 0).1
  = nseq (size (@exec_procs mpS s5_rand_exec_plug u w0 0)) Finish.
Proof.
rewrite s5_rand_procs_size /exec_run s5_rand_fuelE s5_rand_procsE.
exact: s5_aprocs_cut_terminates.
Qed.

(** s5_rand_endpoints — the randomized run's verifier endpoints equal the
    static observation s5_rcontent_obs evaluated at each seat's start, the
    randomized counterpart of s5_exec_endpoints. *)
Lemma s5_rand_endpoints (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  @exec_endpoints mpS s5_rand_exec_plug u w0 0
  = @exec_static_endpoints mpS s5_rand_exec_plug s5_rcontent_obs u w0.
Proof.
rewrite /exec_endpoints /exec_run s5_rand_fuelE s5_rand_procsE
        /exec_verifier_id.
rewrite /exec_static_endpoints s5_rand_playersE.
by rewrite /s5_rprocs_cut s5_aprocs_cut_endpoints.
Qed.

(** s5_rand_endpoint_count — the randomized run collects exactly five
    endpoints, one per seat. *)
Lemma s5_rand_endpoint_count (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  size (@exec_endpoints mpS s5_rand_exec_plug u w0 0) = 5.
Proof. by rewrite (exec_endpoints_size (s5_rand_endpoints u w0)). Qed.

(** s5_rand_decodeE — the randomized plug's decoder exec_decode
    s5_rand_exec_plug agrees with ts_recon s5_scheme on any endpoint list of
    the right length, feeding s5_rand_recon below. *)
Lemma s5_rand_decodeE (ep : seq 'I_(pgg_N' (mp_M mpS)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpS)).+1)
    (Hsz' : size ep = (ts_T' s5_scheme).+1) :
  @exec_decode mpS s5_rand_exec_plug ep Hsz
  = ts_recon s5_scheme (tcast Hsz' (in_tuple ep)).
Proof.
by rewrite /exec_decode /run_recover (eq_irrelevance (etrans Hsz _) Hsz').
Qed.

(** s5_rand_recon — decoding the randomized static-observation endpoints
    returns the tape secret carried through s5_codec, for any cut w0 in the
    group and any proof of the endpoint count. The randomized counterpart
    of s5_exec_recon, proved via s5_rand_run_recovers rather than a direct
    reconstruction argument. *)
Lemma s5_rand_recon (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M) :
  w0 \in pgg_G s5_M ->
  forall Hsz : size (@exec_static_endpoints mpS s5_rand_exec_plug
                       s5_rcontent_obs u w0)
               = (pi_T' (mp_PI mpS)).+1,
  @exec_decode mpS s5_rand_exec_plug
    (@exec_static_endpoints mpS s5_rand_exec_plug s5_rcontent_obs u w0) Hsz
  = s5_codec (s5_tape_secret u).
Proof.
move=> Gw0.
rewrite -s5_rand_endpoints /exec_endpoints /exec_run s5_rand_fuelE
        s5_rand_procsE /exec_verifier_id => Hsz.
rewrite (s5_rand_decodeE Hsz (s5_rand_endpoints_size u w0)).
exact: (@s5_rand_run_recovers u w0 Gw0).
Qed.

(** s5_rand_exec_recovers — the randomized run decodes to the encoded tape
    secret: exec_decode applied to the executed endpoints of
    s5_rand_exec_plug at tape u and cut w0 returns s5_codec
    (s5_tape_secret u), for any cut w0 in the group. The randomized
    counterpart of s5_exec_recovers. *)
Theorem s5_rand_exec_recovers (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M)
    (Gw0 : w0 \in pgg_G s5_M) :
  @exec_decode mpS s5_rand_exec_plug
    (@exec_endpoints mpS s5_rand_exec_plug u w0 0)
    (exec_endpoints_size (s5_rand_endpoints u w0))
  = s5_codec (s5_tape_secret u).
Proof.
exact: (@exec_run_recovers mpS s5_rand_exec_plug s5_rcontent_obs
          (fun u => s5_codec (s5_tape_secret u)) u w0 0
          (s5_rand_endpoints u w0) (s5_rand_recon Gw0)).
Qed.

(** s5_rand_correct — the randomized run of s5_rand_exec_plug reaches Finish
    at each of its seven processes, collects one endpoint per seat, and
    decodes to the encoded tape secret, for any cut w0 in the group: the
    randomized counterpart of s5_exec_correct. *)
Theorem s5_rand_correct (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M)
    (Gw0 : w0 \in pgg_G s5_M) :
  [/\ (@exec_run mpS s5_rand_exec_plug u w0 0).1
        = nseq (size (@exec_procs mpS s5_rand_exec_plug u w0 0)) Finish,
      size (@exec_endpoints mpS s5_rand_exec_plug u w0 0)
        = (pi_T' (mp_PI mpS)).+1 &
      @exec_decode mpS s5_rand_exec_plug
        (@exec_endpoints mpS s5_rand_exec_plug u w0 0)
        (exec_endpoints_size (s5_rand_endpoints u w0))
      = s5_codec (s5_tape_secret u)].
Proof.
exact: (@exec_run_correct mpS s5_rand_exec_plug s5_rcontent_obs
          (fun u => s5_codec (s5_tape_secret u)) u w0 0
          (s5_rand_terminates u w0) (s5_rand_endpoints u w0)
          (s5_rand_recon Gw0)).
Qed.

(** s5_rand_observed — the ObservedExecution record packaging s5_profile with
    plug s5_rand_exec_plug at process offset 0, static observation
    s5_rcontent_obs, expected value the encoded tape secret, and the three
    run facts proved above. The randomized counterpart of s5_observed. *)
Definition s5_rand_observed : OE.ObservedExecution :=
  OE.MkObservedExecution mpS s5_rand_exec_plug 0
    s5_rcontent_obs (fun u => s5_codec (s5_tape_secret u))
    s5_rand_terminates s5_rand_endpoints (@s5_rand_recon).

(** s5_rand_observed_recovers — the packaged randomized run decodes to the
    encoded tape secret: exec_decode applied to the executed endpoints of
    s5_rand_observed at tape u and cut w0 returns s5_codec
    (s5_tape_secret u), for any cut w0 in the group. The randomized
    counterpart of s5_observed_recovers. *)
Theorem s5_rand_observed_recovers (u : 'rV['Z_5]_5) (w0 : pgg_gT s5_M)
    (Gw0 : w0 \in pgg_G s5_M) :
  @exec_decode mpS s5_rand_exec_plug
    (@exec_endpoints mpS s5_rand_exec_plug u w0 0)
    (OE.oe_endpoints_size s5_rand_observed u w0)
  = s5_codec (s5_tape_secret u).
Proof. exact: (OE.oe_run_recovers s5_rand_observed u w0 Gw0). Qed.

End s5_execution.
