(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_exec: the ExecutionPlug of the PGL(2,7) instance                     *)
(*                                                                            *)
(* The eight-card orbit instance carries an execution plug over its own       *)
(* MonodromyProfile pgl27_profile, built by the dealer-secret constructor:    *)
(* the run argument is the dealt orbit secret, both count bridges are erefl   *)
(* at 8 seats, 8 shares and 8 cards, the participant list is pgl27_players    *)
(* and the fuel is pgl27_fuel.                                                *)
(*                                                                            *)
(* The same instance is also written as a PGGAlgebraic, in the block surface  *)
(* of pgg_algebra_syntax.v, from which the framework of pgg_instance.v        *)
(* derives the profile, the plug and the observed execution. The two          *)
(* descriptions agree as terms, pgl27_profileE and pgl27_execE, and           *)
(* pgl27_observed is the derived value. Of its three run facts the instance   *)
(* decides two by reduction, termination at its own plug and the endpoint     *)
(* equation once at its profile with the content readout left a variable, and *)
(* owes no proof at all for the third: reconstruction follows from the        *)
(* coordinate law, which for an instance whose seats start at the deck        *)
(* positions in order is the framework's own ord_coordE.                      *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_exec_plug                 == the execution plug over               *)
(*                                      pgl27_profile                         *)
(*   pgl27_algebra                   == the algebraic data of the instance    *)
(*   pgl27_dealt_params              == the run-level data of the dealt run   *)
(*   pgl27_dealt_endpoints           == the endpoint obligation, from the     *)
(*                                      profile's abstract-readout equation   *)
(*   pgl27_dealt_recon               == the reconstruction obligation, from   *)
(*                                      the coordinate law                    *)
(*   pgl27_content_obs               == the direct computation: the share of  *)
(*                                      the secret at the cut image of a      *)
(*                                      starting position                     *)
(*   pgl27_exec_player_raw_trace     == seat i's raw executed trace           *)
(*   pgl27_exec_coalition_raw_trace  == a coalition's raw executed traces     *)
(*   pgl27_observed                  == the ObservedExecution the framework   *)
(*                                      derives from pgl27_algebra and the    *)
(*                                      three run facts                       *)
(*   pgl27_sample                    == the exact sample adapter: the sample  *)
(*                                      space bool * pgg_gT pgl27_M under     *)
(*                                      pgl27P                                *)
(*   pgl27_word_sample               == the finite-word sample adapter: a     *)
(*                                      secret prior times the word           *)
(*                                      distribution, the cut being the       *)
(*                                      evaluated word                        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_profileE == the derived profile is pgl27_profile                   *)
(*   pgl27_execE    == the derived plug is pgl27_exec_plug                    *)
(*   pgl27_dealt_terminates == every process of the dealt run reaches Finish  *)
(*   pgl27_profile_endpoints == at every readout the executed endpoints of a  *)
(*                              dealer-dealt run over this profile are its    *)
(*                              direct computation                            *)
(*   pgl27_exec_recovers == the derived run decodes to the dealt secret       *)
(*   pgl27_exec_correct  == termination, endpoint count and recovery of the   *)
(*                          derived run                                       *)
(*   pgl27_exec_seat_endpointE == seat i's endpoint is the share at the cut   *)
(*                                image of seat i's start                     *)
(*   pgl27_exec_coalition_endpointsE     == a coalition's endpoint readings   *)
(*                                          are the shares at the cut images  *)
(*                                          of its seats                      *)
(*   pgl27_exec_coalition_endpoints_seqE == the same reading in seat order    *)
(*   pgl27_exec_seat_countE == the profile's seat index type is 'I_8          *)
(*   pgl27_exec_raw_traceE  == the derived raw trace is the trace of          *)
(*                             pgl27_procs at the seat's process identifier   *)
(*   pgl27_observed_recovers == the packaged run decodes to the dealt secret  *)
(*   pgl27_sample_seat_distE      == the executed seat distribution at pgl27P *)
(*                                   is the distribution of the orbit share   *)
(*                                   at the cut image of the seat's start     *)
(*   pgl27_sample_coalition_distE == the same for a coalition's readings      *)
(*   pgl27_sample_witness_prodE   == the exact sample space is the uniform    *)
(*                                   secret prior times the marginal bound's  *)
(*                                   own shuffle distribution                 *)
(*   pgl27_sample_cut_distE       == the exact sample space's cut             *)
(*                                   distribution is the marginal bound's     *)
(*                                   own shuffle distribution                 *)
(*   pgl27_word_sample_seat_distE == the executed seat distribution under the *)
(*                                   word shuffle                             *)
(*   pgl27_word_sample_coalition_distE == the same for a coalition's          *)
(*                                        readings                            *)
(*   pgl27_word_cut_distE         == the word sample space's cut distribution *)
(*                                   is rho_word                              *)
(*   pgl27_word_sample_joint_distE == the joint distribution of the word      *)
(*                                   sample's secret and evaluated cut is     *)
(*                                   pgl27P_word_gen                          *)
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
From pgg_smc Require Import pgg_execution_plug pgg_weighted_words.
From pgg_smc Require Import pgg_observed_execution pgg_sample_adapter.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import pgg_instance pgg_algebra_syntax.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme.
From pgg_smc Require Import pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section pgl27_execution.

Variable R : realType.

Let mpP : MonodromyProfile := pgl27_profile.

(** pgl27_players_enumE — the eight-element participant list is the seat
    enumeration. *)
Lemma pgl27_players_enumE : pgl27_players = enum 'I_(pi_T' (mp_PI mpP)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** pgl27_exec_plug — the PGL(2,7) execution plug. The execution layer over
    pgl27_profile with run argument bool, the seat/share bridge erefl at 8
    seats and 8 shares, participant list pgl27_players, content the shares
    ts_encode orbit_scheme s of the dealt orbit secret s and fuel pgl27_fuel;
    the dealer-secret constructor fixes the input-process list to the empty
    list. *)
Definition pgl27_exec_plug : ExecutionPlug mpP :=
  @dealer_secret_plug mpP bool erefl pgl27_players pgl27_players_enumE
    (fun s _ => tnth (ts_encode orbit_scheme s)) pgl27_fuel.

(** pgl27_content_obs — the PGL(2,7) direct computation. The share of the
    secret s at the cut image of a starting position, namely tnth (ts_encode
    orbit_scheme s) (pgg_rho w0 p) at a cut w0 and a position p. *)
Definition pgl27_content_obs (s : bool)
    (p : pgg_gT (mp_M mpP) * 'I_(pgg_N' (mp_M mpP)).+1)
    : 'I_(pgg_N' (mp_M mpP)).+1 :=
  tnth (ts_encode orbit_scheme s) (@pgg_rho (mp_M mpP) p.1 p.2).

(** pgl27_exec_playersE — the plug's participant list is the instance's
    list. *)
Lemma pgl27_exec_playersE : ep_players pgl27_exec_plug = pgl27_players.
Proof. by []. Qed.

(** pgl27_exec_fuelE — the plug's fuel is the instance's fuel. *)
Lemma pgl27_exec_fuelE : ep_fuel pgl27_exec_plug = pgl27_fuel.
Proof. by []. Qed.

(** pgl27_exec_procsE — the derived process list is the instance's process
    list. *)
Lemma pgl27_exec_procsE (s : bool) (w0 : pgg_gT pgl27_M) :
  @exec_procs mpP pgl27_exec_plug s w0 0 = pgl27_procs s w0.
Proof. by []. Qed.

(** pgl27_exec_procs_size — the derived run has ten processes. *)
Lemma pgl27_exec_procs_size (s : bool) (w0 : pgg_gT pgl27_M) :
  size (@exec_procs mpP pgl27_exec_plug s w0 0) = 10.
Proof. by []. Qed.

(** pgl27_exec_terminates — every process of the derived run reaches
    Finish. *)
Lemma pgl27_exec_terminates (s : bool) (w0 : pgg_gT pgl27_M) :
  (@exec_run mpP pgl27_exec_plug s w0 0).1
  = nseq (size (@exec_procs mpP pgl27_exec_plug s w0 0)) Finish.
Proof.
rewrite pgl27_exec_procs_size /exec_run pgl27_exec_fuelE pgl27_exec_procsE.
exact: pgl27_run_terminates.
Qed.

(** pgl27_exec_endpoints — the derived verifier endpoints are the static
    observation over the seats. *)
Lemma pgl27_exec_endpoints (s : bool) (w0 : pgg_gT pgl27_M) :
  @exec_endpoints mpP pgl27_exec_plug s w0 0
  = @exec_static_endpoints mpP pgl27_exec_plug pgl27_content_obs s w0.
Proof.
rewrite /exec_endpoints /exec_run pgl27_exec_fuelE pgl27_exec_procsE.
rewrite /exec_verifier_id.
rewrite /exec_static_endpoints pgl27_exec_playersE pgl27_players_enumE.
exact: pgl27_endpoints.
Qed.

(** pgl27_exec_decodeE — the plug's decoder is the instance's
    reconstruction. *)
Lemma pgl27_exec_decodeE (ep : seq 'I_(pgg_N' (mp_M mpP)).+1)
    (sz_ep : size ep = (pi_T' (mp_PI mpP)).+1)
    (sz_ep' : size ep = (ts_T' orbit_scheme).+1) :
  @exec_decode mpP pgl27_exec_plug ep sz_ep
  = ts_recon orbit_scheme (tcast sz_ep' (in_tuple ep)).
Proof.
by rewrite /exec_decode /run_recover (eq_irrelevance (etrans sz_ep _) sz_ep').
Qed.

(** pgl27_exec_recon — decoding the direct computation returns the dealt
    secret, for any cut in the group and any proof of the endpoint count. *)
Lemma pgl27_exec_recon (s : bool) (w0 : pgg_gT pgl27_M) :
  w0 \in pgg_G pgl27_M ->
  forall sz_ep : size (@exec_static_endpoints mpP pgl27_exec_plug
                       pgl27_content_obs s w0) = (pi_T' (mp_PI mpP)).+1,
  @exec_decode mpP pgl27_exec_plug
    (@exec_static_endpoints mpP pgl27_exec_plug pgl27_content_obs s w0)
    sz_ep = s.
Proof.
move=> Gw0.
rewrite -pgl27_exec_endpoints /exec_endpoints /exec_run pgl27_exec_fuelE
        pgl27_exec_procsE /exec_verifier_id => sz_ep.
rewrite (pgl27_exec_decodeE sz_ep (pgl27_endpoints_size s w0)).
exact: (pgl27_run_recovers s Gw0).
Qed.

(** pgl27_exec_recovers — the derived PGL(2,7) run decodes to the dealt
    secret.  The decoder of the plug, applied to the endpoints the run
    collects at secret s and cut w0, returns s for every cut w0 in the
    group. *)
Theorem pgl27_exec_recovers (s : bool) (w0 : pgg_gT pgl27_M)
    (Gw0 : w0 \in pgg_G pgl27_M) :
  @exec_decode mpP pgl27_exec_plug
    (@exec_endpoints mpP pgl27_exec_plug s w0 0)
    (exec_endpoints_size (pgl27_exec_endpoints s w0)) = s.
Proof.
exact: (@exec_run_recovers mpP pgl27_exec_plug pgl27_content_obs (fun b => b)
          s w0 0 (pgl27_exec_endpoints s w0) (pgl27_exec_recon Gw0)).
Qed.

(** pgl27_exec_correct — termination, endpoint count and recovery of the
    derived PGL(2,7) run. The run of pgl27_exec_plug reaches Finish at each of
    its ten processes, collects one endpoint per seat, and decodes to the
    dealt secret s, for any cut w0 in the group. *)
Theorem pgl27_exec_correct (s : bool) (w0 : pgg_gT pgl27_M)
    (Gw0 : w0 \in pgg_G pgl27_M) :
  [/\ (@exec_run mpP pgl27_exec_plug s w0 0).1
        = nseq (size (@exec_procs mpP pgl27_exec_plug s w0 0)) Finish,
      size (@exec_endpoints mpP pgl27_exec_plug s w0 0)
        = (pi_T' (mp_PI mpP)).+1 &
      @exec_decode mpP pgl27_exec_plug
        (@exec_endpoints mpP pgl27_exec_plug s w0 0)
        (exec_endpoints_size (pgl27_exec_endpoints s w0)) = s].
Proof.
exact: (@exec_run_correct mpP pgl27_exec_plug pgl27_content_obs (fun b => b)
          s w0 0 (pgl27_exec_terminates s w0) (pgl27_exec_endpoints s w0)
          (pgl27_exec_recon Gw0)).
Qed.

(******************************************************************************)
(*     The endpoint and trace read-off at pgl27_profile                       *)
(******************************************************************************)

(** pgl27_exec_seat_endpointE — seat i's endpoint is the share at the cut
    image of seat i's start.  A seat's executed endpoint depends on the cut
    and on that seat's own start alone, so a coalition's endpoints carry
    nothing beyond the cards dealt at its own seats. *)
Lemma pgl27_exec_seat_endpointE (s : bool) (w0 : pgg_gT pgl27_M)
    (i : 'I_(pi_T' (mp_PI mpP)).+1) :
  @exec_seat_endpoint mpP pgl27_exec_plug s w0 0 i
  = pgl27_content_obs s (w0, tnth (pi_starts (mp_PI mpP)) i).
Proof. exact: (exec_seat_endpointE (pgl27_exec_endpoints s w0) i). Qed.

(** pgl27_exec_coalition_endpointsE — a coalition's endpoint readings are the
    shares at the cut images of its seats. The finfun sends a seat in C to the
    share of s at the cut image of that seat's start, and every seat outside C
    to ord0. *)
Lemma pgl27_exec_coalition_endpointsE (s : bool) (w0 : pgg_gT pgl27_M)
    (C : {set 'I_(pi_T' (mp_PI mpP)).+1}) :
  @exec_coalition_endpoints mpP pgl27_exec_plug s w0 0 C
  = [ffun i => if i \in C
               then pgl27_content_obs s (w0, tnth (pi_starts (mp_PI mpP)) i)
               else ord0].
Proof. exact: (exec_coalition_endpointsE (pgl27_exec_endpoints s w0) C). Qed.

(** pgl27_exec_coalition_endpoints_seqE — the coalition's endpoint readings in
    seat order are the shares at the cut images of its seats. Mapping the
    endpoint reading over enum C gives the same list as mapping the share of s
    at the cut image of the start over enum C. *)
Lemma pgl27_exec_coalition_endpoints_seqE (s : bool) (w0 : pgg_gT pgl27_M)
    (C : {set 'I_(pi_T' (mp_PI mpP)).+1}) :
  [seq @exec_seat_endpoint mpP pgl27_exec_plug s w0 0 i | i <- enum C]
  = [seq pgl27_content_obs s (w0, tnth (pi_starts (mp_PI mpP)) i)
     | i <- enum C].
Proof.
exact: (exec_coalition_endpoints_seqE (pgl27_exec_endpoints s w0) C).
Qed.

(** pgl27_exec_player_raw_trace — seat i's raw executed trace. The generic
    participant extractor exec_participant_trace at pgl27_exec_plug, secret s,
    cut w0 and process offset 0. *)
Definition pgl27_exec_player_raw_trace (s : bool) (w0 : pgg_gT pgl27_M)
    (i : 'I_(pi_T' (mp_PI mpP)).+1) :=
  @exec_participant_trace mpP pgl27_exec_plug s w0 0 i.

(** pgl27_exec_coalition_raw_trace — a coalition's raw executed traces. The
    generic coalition assembly exec_coalition_trace at pgl27_exec_plug, secret
    s, cut w0 and process offset 0. *)
Definition pgl27_exec_coalition_raw_trace (s : bool) (w0 : pgg_gT pgl27_M)
    (C : {set 'I_(pi_T' (mp_PI mpP)).+1}) :=
  @exec_coalition_trace mpP pgl27_exec_plug s w0 0 C.

(** pgl27_exec_seat_countE — the profile's seat index type is 'I_8, the index
    type the eight-seat coalition view already uses.  No transport stands
    between the execution layer and the coalition view. *)
Lemma pgl27_exec_seat_countE : (pi_T' (mp_PI mpP)).+1 = 8.
Proof. by []. Qed.

(** pgl27_exec_raw_traceE — the derived raw trace is the trace of pgl27_procs
    at the seat's process identifier.  The generic execution layer reads the
    same interpreter row the instance's own run produces, so a fact proved of
    pgl27_procs is a fact of the derived run. *)
Lemma pgl27_exec_raw_traceE (s : bool) (w0 : pgg_gT pgl27_M)
    (i : 'I_(pi_T' (mp_PI mpP)).+1) :
  pgl27_exec_player_raw_trace s w0 i
  = nth [::] (run_interp pgl27_fuel (pgl27_procs s w0)).2 (2 + i).
Proof.
by rewrite /pgl27_exec_player_raw_trace /exec_participant_trace /exec_seat_id
   /exec_run pgl27_exec_fuelE pgl27_exec_procsE.
Qed.

(******************************************************************************)
(*     The algebraic record of the eight-card orbit instance                  *)
(******************************************************************************)

(** pgl27_algebra — the algebraic data of the eight-card orbit instance:
    three generating permutations of eight card positions, the symmetrized
    five-letter walk alphabet with the proof that it generates the same group,
    the Boolean secret the orbit scheme deals with its encoding, its class
    readout and its privacy obligation, and the seat list the run reads
    because enum 'I_8 does not reduce.  The seats start at the eight positions
    in order and the shuffle acts on share indices as it acts on cards, so the
    coordinate law is the framework's ord_coordE and the instance writes none;
    the dealer readout is the identity, so a card carries the share dealt to
    its own position and no encoding stands between the two.  The record holds
    no run, no fuel and no probability model, so the seat interface, the
    reconstruction plug and the monodromy profile of this instance are all
    functions of this one value. *)
Definition pgl27_algebra : PGGAlgebraic := algebra {
  mount   << pgl27_gens >> ;
  walk    along pgl27_moves by pgl27_gen5_eq ;
  seat    players (ord_tuple 8) by pgl27_starts_uniq ;
  secret  bool ;
  deal    orbit_scheme
          encode orbit_encode
          read   orbit_class
          private by pgl27_private
          shuffled_by pgg_rho by orbit_recon_invariant ;
  cache   seats pgl27_players by pgl27_players_enumE }.

(** pgl27_dealt_params — the run-level data of a run that deals the orbit
    secret and recovers it: the run argument is the secret itself, no party
    commits an input, and the interpreter budget is pgl27_fuel.  The
    dealer-dealt mode is what leaves the instance owing termination alone
    among the three run facts. *)
Definition pgl27_dealt_params : ExecutionParams pgl27_algebra :=
  dealt_secret_params pgl27_algebra pgl27_fuel.

(** pgl27_profileE — the profile derived from the algebra is the instance's
    own monodromy profile.  The two are the same term, so every theorem about
    pgl27_profile is a theorem about the derived profile. *)
Lemma pgl27_profileE : instance_profile pgl27_algebra = pgl27_profile.
Proof. by []. Qed.

(** pgl27_execE — the plug derived from the run parameters is the instance's
    own execution plug.  The dealer-dealt readout of the algebra and the
    hand-written readout of pgl27_exec_plug are the same term, so the two
    plugs drive the same interpreter run. *)
Lemma pgl27_execE : instance_exec pgl27_dealt_params = pgl27_exec_plug.
Proof. by []. Qed.

(** pgl27_dealt_terminates — every process of the dealt run reaches Finish
    within pgl27_fuel.  The one run fact that has no route through the
    algebra: it depends on the interpreter and on the budget, and is decided
    by reduction.  The statement is convertible with pgl27_exec_terminates,
    which states the same reduction at the hand-written plug; both spend the
    instance's own vm_compute, and this one is stated on the plug the
    framework derives from pgl27_algebra. *)
Lemma pgl27_dealt_terminates : instance_terminates_stmt pgl27_dealt_params.
Proof. by vm_compute. Qed.

(** pgl27_profile_endpoints — at every content readout, the executed
    endpoints of a dealer-dealt run over this profile are its static
    group-action reading.  Keeping the readout a variable removes the dealt
    card from the reduction, so one decision at the profile serves every run
    driven over it. *)
Lemma pgl27_profile_endpoints :
  profile_endpoints_stmt pgl27_algebra pgl27_fuel.
Proof. by vm_compute. Qed.

(** pgl27_dealt_endpoints — the endpoint obligation of the dealt run.  The
    statement is convertible with pgl27_exec_endpoints, which proves it
    directly from the interpreter; this one instantiates the profile's
    abstract-readout equation at the dealt readout, so the instance pays no
    reduction of its own for it. *)
Definition pgl27_dealt_endpoints : instance_endpoints_stmt pgl27_dealt_params :=
  profile_endpointsE pgl27_profile_endpoints.

(** pgl27_dealt_recon — decoding the static endpoint reading at a shuffle in
    the group returns the dealt secret.  The statement is convertible with
    pgl27_exec_recon, which proves it through the interpreter; this one is
    dealt_static_recon, which the framework derives from the algebra's
    coordinate law alone, so reconstruction correctness of this instance is a
    consequence of that law and costs no further proof. *)
Definition pgl27_dealt_recon : instance_recon_stmt pgl27_dealt_params :=
  dealt_static_recon pgl27_algebra pgl27_fuel.

(******************************************************************************)
(*     The packaged observed execution at pgl27_profile                       *)
(******************************************************************************)

(** pgl27_observed — the eight-card orbit observed execution, derived by the
    framework from the algebraic record and the three run facts above.  Two of
    those facts are framework lemmas, the endpoint equation instantiated from
    the profile and the reconstruction derived from the coordinate law, and
    the third is the instance's own termination computation; the profile, the
    plug, the direct computation and the recovered value are all read off
    pgl27_algebra and pgl27_dealt_params. *)
Definition pgl27_observed : OE.ObservedExecution :=
  instance_observed pgl27_dealt_terminates pgl27_dealt_endpoints
    pgl27_dealt_recon.

(** pgl27_observed_recovers — the packaged eight-card orbit run decodes to the
    dealt secret.  The decoder applied to the endpoints pgl27_observed
    collects at secret s and cut w0 returns s, for every cut w0 in the
    group. *)
Theorem pgl27_observed_recovers (s : bool) (w0 : pgg_gT pgl27_M)
    (Gw0 : w0 \in pgg_G pgl27_M) :
  @exec_decode mpP pgl27_exec_plug
    (@exec_endpoints mpP pgl27_exec_plug s w0 0)
    (OE.oe_endpoints_size pgl27_observed s w0) = s.
Proof. exact: (OE.oe_run_recovers pgl27_observed s w0 Gw0). Qed.

(******************************************************************************)
(*     The exact sample space of the eight-card orbit instance                *)
(******************************************************************************)

(** pgl27_sample — the PGL(2,7) exact sample adapter. The sample layer over
    pgl27_exec_plug whose sample space is bool * pgg_gT pgl27_M under the
    distribution pgl27P of a uniform orbit secret and an independent uniform
    shuffle, the run argument being the first projection and the cut the
    second. *)
Definition pgl27_sample : SampleAdapter R pgl27_exec_plug :=
  @MkSampleAdapter R mpP pgl27_exec_plug
    [the finType of (bool * pgg_gT pgl27_M)%type] (pgl27P R) fst snd.

(** pgl27_sample_run — layer 1 at pgl27P: the run at a sample point.  This is
    sa_run at pgl27_sample and process offset 0, the run whose dealt secret is
    the sample's first component and whose cut is its second. *)
Definition pgl27_sample_run (u : sa_sampleT pgl27_sample) :=
  @sa_run R mpP pgl27_exec_plug pgl27_sample 0 u.

(** pgl27_sample_seat_view — layer 2 at pgl27P: seat i's endpoint.
    This is sa_seat_view at pgl27_sample, seat i's endpoint reader as a
    random variable on pgl27P. *)
Definition pgl27_sample_seat_view (i : 'I_(pi_T' (mp_PI mpP)).+1) :=
  @sa_seat_view R mpP pgl27_exec_plug pgl27_sample 0 i.

(** pgl27_sample_coalition_view — layer 2 at pgl27P: a coalition's readings.
    This is sa_coalition_view at pgl27_sample, the coalition endpoint reader
    as a random variable on pgl27P. *)
Definition pgl27_sample_coalition_view (C : {set 'I_(pi_T' (mp_PI mpP)).+1}) :=
  @sa_coalition_view R mpP pgl27_exec_plug pgl27_sample 0 C.

(** pgl27_sample_seat_dist — layer 3 at pgl27P: the distribution of seat i's
    endpoint. The pushforward of pgl27P along pgl27_sample_seat_view i. *)
Definition pgl27_sample_seat_dist (i : 'I_(pi_T' (mp_PI mpP)).+1) :=
  @sa_seat_dist R mpP pgl27_exec_plug pgl27_sample 0 i.

(** pgl27_sample_coalition_dist — layer 3 at pgl27P: the distribution of a
    coalition's readings. The pushforward of pgl27P along
    pgl27_sample_coalition_view C. *)
Definition pgl27_sample_coalition_dist (C : {set 'I_(pi_T' (mp_PI mpP)).+1}) :=
  @sa_coalition_dist R mpP pgl27_exec_plug pgl27_sample 0 C.

(** pgl27_sample_seat_distE — the executed seat distribution at pgl27P is the
    distribution of the orbit share at the cut image of the seat's start.  The
    executed reading has the law of the direct computation, so a bound proved
    about the static observable holds of what the run produces. *)
Lemma pgl27_sample_seat_distE (i : 'I_(pi_T' (mp_PI mpP)).+1) :
  pgl27_sample_seat_dist i
  = fdistmap (@sa_static_seat_view R mpP pgl27_exec_plug pgl27_sample
                pgl27_content_obs i) (pgl27P R).
Proof. by apply: sa_seat_distE => u; exact: pgl27_exec_endpoints. Qed.

(** pgl27_sample_coalition_distE — the executed coalition distribution at
    pgl27P is the distribution of the orbit shares at the cut images of the
    coalition's starts.  The coalition form of the same transfer from the
    direct computation to the executed one. *)
Lemma pgl27_sample_coalition_distE (C : {set 'I_(pi_T' (mp_PI mpP)).+1}) :
  pgl27_sample_coalition_dist C
  = fdistmap (@sa_static_coalition_view R mpP pgl27_exec_plug pgl27_sample
                pgl27_content_obs C) (pgl27P R).
Proof. by apply: sa_coalition_distE => u; exact: pgl27_exec_endpoints. Qed.

(** pgl27_sample_witness_prodE — the exact sample space is the product of the
    uniform secret prior with the marginal bound's own shuffle distribution.
    Secret and shuffle are independent in this model, which is what makes the
    coalition view's independence of the secret a statement about the shuffle
    alone. *)
Lemma pgl27_sample_witness_prodE :
  pgl27P R
  = ((fdist_uniform card_bool) `x (sw_rho_dist (pgl27_marginal_bound R)))%fdist.
Proof. by []. Qed.

(** pgl27_sample_cut_distE — the exact sample space's cut distribution is the
    marginal bound's own shuffle distribution.  The cut this model draws is
    the very law the certified marginal bound is stated at, so the certificate
    applies to the model without transport. *)
Lemma pgl27_sample_cut_distE :
  @sa_cut_dist R mpP pgl27_exec_plug pgl27_sample
  = sw_rho_dist (pgl27_marginal_bound R).
Proof.
rewrite /sa_cut_dist /pgl27_sample /=.
rewrite pgl27_sample_witness_prodE.
by rewrite -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

(******************************************************************************)
(*     The finite-word sample space of the eight-card orbit instance          *)
(******************************************************************************)

(* The secret prior of the word sample space, arbitrary where the exact sample
   space fixes the uniform one. *)
Variable secretP : R.-fdist bool.

(** pgl27_word_wordP — the two-hundred-letter word distribution over the
    symmetrized generator alphabet. The word_weighted distribution at length
    200 and uniform letters, the space rho_word is the image of. *)
Definition pgl27_word_wordP : R.-fdist (200.-tuple 'I_5) :=
  @word_weighted R 4 200 (pgl27_mixing.Wuni R).

(** pgl27_word_sampleT — the finite-word sample space. Pairs of an orbit
    secret and a two-hundred-letter generator word. *)
Definition pgl27_word_sampleT : finType :=
  [the finType of (bool * 200.-tuple 'I_5)%type].

(** pgl27_word_sampleP — the finite-word sample distribution. The product of
    the secret prior secretP with the word distribution pgl27_word_wordP. *)
Definition pgl27_word_sampleP : R.-fdist pgl27_word_sampleT :=
  (secretP `x pgl27_word_wordP)%fdist.

(** pgl27_word_cut — the finite-word cut map. The evaluation in PGL(2,7) of
    the sampled generator word. *)
Definition pgl27_word_cut (u : pgl27_word_sampleT) : pgg_gT (mp_M mpP) :=
  @word_eval pgl27_Msym 200 u.2.

(** pgl27_word_sample — the PGL(2,7) finite-word sample adapter. The sample
    layer over pgl27_exec_plug whose sample space is pgl27_word_sampleT under
    pgl27_word_sampleP, the run argument being the first projection and the
    cut the evaluated word. *)
Definition pgl27_word_sample : SampleAdapter R pgl27_exec_plug :=
  @MkSampleAdapter R mpP pgl27_exec_plug pgl27_word_sampleT pgl27_word_sampleP
    fst pgl27_word_cut.

(** pgl27_word_sample_run — layer 1 at the word space: the run at a sample
    point.  This is sa_run at pgl27_word_sample and process offset 0, the run
    whose cut is the evaluated word. *)
Definition pgl27_word_sample_run (u : pgl27_word_sampleT) :=
  @sa_run R mpP pgl27_exec_plug pgl27_word_sample 0 u.

(** pgl27_word_sample_seat_view — layer 2 at the word space: seat i's
    endpoint.  This is sa_seat_view at pgl27_word_sample, seat i's endpoint
    reader as a random variable on pgl27_word_sampleP. *)
Definition pgl27_word_sample_seat_view (i : 'I_(pi_T' (mp_PI mpP)).+1) :=
  @sa_seat_view R mpP pgl27_exec_plug pgl27_word_sample 0 i.

(** pgl27_word_sample_seat_dist — layer 3 at the word space: the distribution
    of seat i's endpoint. The pushforward of pgl27_word_sampleP along
    pgl27_word_sample_seat_view i. *)
Definition pgl27_word_sample_seat_dist (i : 'I_(pi_T' (mp_PI mpP)).+1) :=
  @sa_seat_dist R mpP pgl27_exec_plug pgl27_word_sample 0 i.

(** pgl27_word_sample_coalition_dist — layer 3 at the word space, coalition
    form. The pushforward of pgl27_word_sampleP along the coalition endpoint
    reader. *)
Definition pgl27_word_sample_coalition_dist
    (C : {set 'I_(pi_T' (mp_PI mpP)).+1}) :=
  @sa_coalition_dist R mpP pgl27_exec_plug pgl27_word_sample 0 C.

(** pgl27_word_sample_seat_distE — the executed seat distribution under the
    word shuffle is the distribution of the orbit share at the evaluated
    word's image of the seat's start.  The same transfer as at the exact
    model, now with the cut supplied by a two-hundred-letter word. *)
Lemma pgl27_word_sample_seat_distE (i : 'I_(pi_T' (mp_PI mpP)).+1) :
  pgl27_word_sample_seat_dist i
  = fdistmap (@sa_static_seat_view R mpP pgl27_exec_plug pgl27_word_sample
                pgl27_content_obs i) pgl27_word_sampleP.
Proof. by apply: sa_seat_distE => u; exact: pgl27_exec_endpoints. Qed.

(** pgl27_word_sample_coalition_distE — the executed coalition distribution
    under the word shuffle is the distribution of the orbit shares at the
    evaluated word's images of the coalition's starts.  The coalition form of
    the same transfer under the word shuffle. *)
Lemma pgl27_word_sample_coalition_distE
    (C : {set 'I_(pi_T' (mp_PI mpP)).+1}) :
  pgl27_word_sample_coalition_dist C
  = fdistmap (@sa_static_coalition_view R mpP pgl27_exec_plug
                pgl27_word_sample pgl27_content_obs C) pgl27_word_sampleP.
Proof. by apply: sa_coalition_distE => u; exact: pgl27_exec_endpoints. Qed.

(** pgl27_word_cut_distE — the word sample space's cut distribution is
    rho_word, the word shuffle distribution on PGL(2,7).  The randomness this
    model runs on is exactly the law the mixing certificate bounds against
    uniform. *)
Lemma pgl27_word_cut_distE :
  @sa_cut_dist R mpP pgl27_exec_plug pgl27_word_sample = rho_word R.
Proof.
rewrite /sa_cut_dist /pgl27_word_sample /= /pgl27_word_cut /pgl27_word_sampleP.
rewrite -(fdistmap_comp (@word_eval pgl27_Msym 200) snd).
by rewrite -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

(** pgl27_word_sample_joint_distE — the joint distribution of the word
    sample's secret and evaluated cut is the generic word-shuffle sample
    distribution.  The sample layer's joint law is the one the mixing theorems
    are stated at, so those bounds reach the executed word model with no
    further step. *)
Lemma pgl27_word_sample_joint_distE :
  sa_joint_dist (pgl27_word_sample.(sa_arg)) = pgl27P_word_gen secretP.
Proof.
rewrite /sa_joint_dist /pgl27_word_sample /= /pgl27_word_sampleP.
rewrite /pgl27P_word_gen /pgl27_word_cut /rho_word.
rewrite /rho_from_words_weighted /pgl27_word_wordP.
exact: fdistmap_prodr.
Qed.

End pgl27_execution.
