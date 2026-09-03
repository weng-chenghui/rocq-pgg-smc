(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* five_card_exec: the ExecutionPlug of the five-card instance                *)
(*                                                                            *)
(* The five-card instance carries an execution plug over its own              *)
(* MonodromyProfile five_card_profile at an arbitrary bias, built by the      *)
(* committed-input constructor: the run argument is the committed pair of     *)
(* bits, both count bridges are erefl at 5 seats, 5 shares and 5 cards, the   *)
(* participant list is den_boer_players, the input processes are the two      *)
(* commit processes of the committing parties and the fuel is 100.            *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   five_card_exec_plug   == the execution plug over five_card_profile       *)
(*   five_card_content_obs == the static observation: the den Boer layout of  *)
(*                            the committed pair at the cut image of a        *)
(*                            starting position                               *)
(*   five_card_exec_player_raw_trace == seat i's raw executed trace           *)
(*   five_card_exec_input_raw_trace  == committing party j's raw executed     *)
(*                                      trace                                 *)
(*   five_card_exec_trace  == seat i's executed trace as a random variable on *)
(*                            the leakage space                               *)
(*   five_card_observed    == the ObservedExecution packing the plug, the     *)
(*                            static observation and the three run facts at   *)
(*                            process offset 0                                *)
(*   den_boer_observed     == the same value, named for the den Boer member   *)
(*   five_card_sample      == the den Boer sample adapter: the leakage space  *)
(*                            Omega under P, the cut being the sampled        *)
(*                            rotation                                        *)
(*   five_card_exec_input_trace == committing party j's executed-row content  *)
(*                                 as a random variable on the leakage space  *)
(*   five_card_exec_dealer_raw_trace == the dealer's raw executed trace       *)
(*   five_card_exec_dealer_readout   == the committed pair decoded from a     *)
(*                                      dealer row                            *)
(*   five_card_exec_dealer_trace     == the dealer's executed row decoded as  *)
(*                                      a random variable on the leakage      *)
(*                                      space                                 *)
(*                                                                            *)
(* Key results:                                                               *)
(*   five_card_exec_recovers    == the derived run decodes to the conjunction *)
(*                                 of the two committed bits                  *)
(*   five_card_exec_correct     == termination, endpoint count and recovery   *)
(*                                 of the derived run                         *)
(*   five_card_exec_procs_biasE == the derived process list does not depend   *)
(*                                 on the bias                                *)
(*   five_card_exec_seat_endpointE == seat i's endpoint is the layout entry   *)
(*                                    at the cut image of seat i's start      *)
(*   five_card_exec_coalition_endpointsE     == a coalition's endpoint        *)
(*                                              readings are the layout       *)
(*                                              entries at the cut images of  *)
(*                                              its seats                     *)
(*   five_card_exec_coalition_endpoints_seqE == the same reading in seat      *)
(*                                              order                         *)
(*   five_card_exec_seat_countE == the profile's seat index type is 'I_5      *)
(*   five_card_exec_input_positions == the committing parties are read at     *)
(*                                     process identifiers 7 and 8            *)
(*   five_card_exec_raw_traceE == the derived raw trace is the trace of       *)
(*                                den_boer_procs at the seat's process        *)
(*                                identifier                                  *)
(*   five_card_exec_traceE == the execution layer's trace variable is         *)
(*                            denboer_player_trace                            *)
(*   five_card_observed_recovers == the packaged run decodes to the           *)
(*                                  conjunction of the two committed bits     *)
(*   den_boer_observed_core     == the den Boer wrapper is the five-card      *)
(*                                 observed execution                         *)
(*   five_card_sample_seat_distE == the executed seat distribution at the den *)
(*                                  Boer space is the distribution of the     *)
(*                                  layout entry at the rotation image of the *)
(*                                  seat's start                              *)
(*   five_card_sample_coalition_distE == the same for a coalition's readings  *)
(*   five_card_exec_trace_secrecy == one seat's executed trace leaves the     *)
(*                                   secret's conditional entropy equal to    *)
(*                                   its plain entropy                        *)
(*   five_card_sample_cut_distE == the sample space's cut distribution is the *)
(*                                 image of the uniform rotation distribution *)
(*                                 under k |-> fc_sigma ^+ k                  *)
(*   five_card_exec_input_trace_secrecy == conditioning the secret on a       *)
(*                                         committing party's executed-row    *)
(*                                         observable leaves its entropy      *)
(*                                         unchanged                          *)
(*   five_card_exec_dealer_pair_centropy0  == the dealer's decoded row        *)
(*                                            determines the committed pair   *)
(*   five_card_exec_dealer_trace_centropy0 == the dealer's decoded row        *)
(*                                            determines the secret           *)
(*   den_boer_sample_cut_witnessE == the sample space's cut distribution is   *)
(*                                   the den Boer member's witness            *)
(*                                   distribution                             *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg matrix.
From mathcomp Require Import boolp reals.
From infotheo Require Import ssralg_ext realType_ext realType_ln fdist proba.
From infotheo Require Import variation_dist entropy.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import proba_entropy_ext.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_weighted_words.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage denboer_trace.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section five_card_execution.

(* R is the section's only parameter: the execution half of the file is
   R-free (the profile and its plug carry no epsilon), and R enters only
   through the sample half's distribution P R on the den Boer leakage space. *)
Variable R : realType.

Let mpF : MonodromyProfile := five_card_profile.

(** five_card_players_enumE — the five-element participant list is the seat
    enumeration. *)
Lemma five_card_players_enumE :
  den_boer_players = enum 'I_(pi_T' (mp_PI mpF)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** five_card_exec_plug — the five-card execution plug: the execution layer
    over five_card_profile with run argument the committed pair (a, b) of
    bits, the seat/share bridge erefl at 5 seats and 5 shares, participant
    list den_boer_players, content the den Boer layout of the decoded
    committed cards and fuel 100. The committed-input constructor takes the
    two commit processes of the committing parties 7 and 8 as its
    input-process list. *)
Definition five_card_exec_plug : ExecutionPlug mpF :=
  @committed_input_plug mpF (bool * bool)%type erefl den_boer_players
    five_card_players_enumE
    (fun _ committed => tnth (den_boer_layout (den_boer_decode committed)))
    (fun ab => [:: mk_aproc (@pgg_commit FiveCardKim_M 7 (encode_bool ab.1))
                 ; mk_aproc (@pgg_commit FiveCardKim_M 8 (encode_bool ab.2))])
    100.

(** five_card_content_obs — the five-card static observation: the den Boer
    layout of the committed pair ab at the cut image of a starting position,
    namely tnth (den_boer_layout ab) (pgg_rho w0 p) at a cut w0 and a
    position p. *)
Definition five_card_content_obs (ab : bool * bool)
    (p : pgg_gT FiveCardKim_M * 'I_(pgg_N' FiveCardKim_M).+1)
    : 'I_(pgg_N' FiveCardKim_M).+1 :=
  tnth (den_boer_layout ab) (@pgg_rho FiveCardKim_M p.1 p.2).

(** five_card_exec_playersE — the plug's participant list is the instance's
    list. *)
Lemma five_card_exec_playersE :
  ep_players five_card_exec_plug = den_boer_players.
Proof. by []. Qed.

(** five_card_exec_fuelE — the plug's fuel is the instance's fuel. *)
Lemma five_card_exec_fuelE : ep_fuel five_card_exec_plug = 100.
Proof. by []. Qed.

(** five_card_exec_input_idsE — the derived input identifiers are those of the
    two committing parties: exec_input_id j = (pi_T' (mp_PI mpF)).+3 + j is
    the identifier 7 or 8 of the instance's own commit process, the
    definitional agreement five_card_exec_procsE rests on. *)
Lemma five_card_exec_input_idsE (ab : bool * bool) :
  @exec_input_ids mpF five_card_exec_plug ab = [:: 7; 8].
Proof. by []. Qed.

(** five_card_exec_procsE — the derived process list is the instance's process
    list. *)
Lemma five_card_exec_procsE (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (P_idx : nat) :
  @exec_procs mpF five_card_exec_plug (a, b) w0 P_idx
  = den_boer_procs a b w0 P_idx.
Proof. by []. Qed.

(** five_card_exec_procs_size — the derived run has nine processes. *)
Lemma five_card_exec_procs_size (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (P_idx : nat) :
  size (@exec_procs mpF five_card_exec_plug (a, b) w0 P_idx) = 9.
Proof. by []. Qed.

(** five_card_exec_terminates — every process of the derived run reaches
    Finish. *)
Lemma five_card_exec_terminates (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (P_idx : nat) :
  (@exec_run mpF five_card_exec_plug (a, b) w0 P_idx).1
  = nseq (size (@exec_procs mpF five_card_exec_plug (a, b) w0 P_idx)) Finish.
Proof.
rewrite five_card_exec_procs_size /exec_run five_card_exec_fuelE
        five_card_exec_procsE.
exact: den_boer_run_terminates.
Qed.

(** five_card_exec_endpoints — the derived verifier endpoints are the static
    observation over the seats. *)
Lemma five_card_exec_endpoints (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  @exec_endpoints mpF five_card_exec_plug (a, b) w0 0
  = @exec_static_endpoints mpF five_card_exec_plug five_card_content_obs
      (a, b) w0.
Proof.
rewrite /exec_endpoints /exec_run five_card_exec_fuelE five_card_exec_procsE.
rewrite /exec_verifier_id.
rewrite /exec_static_endpoints five_card_exec_playersE five_card_players_enumE.
exact: den_boer_endpoints.
Qed.

(** five_card_exec_decodeE — the plug's decoder is the instance's
    reconstruction. *)
Lemma five_card_exec_decodeE (ep : seq 'I_(pgg_N' (mp_M mpF)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpF)).+1)
    (Hsz' : size ep = (ts_T' fcI_scheme).+1) :
  @exec_decode mpF five_card_exec_plug ep Hsz
  = ts_recon fcI_scheme (tcast Hsz' (in_tuple ep)).
Proof.
by rewrite /exec_decode /run_recover (eq_irrelevance (etrans Hsz _) Hsz').
Qed.

(** five_card_exec_decode_seqE — the plug's decoder reads the endpoint list as
    the three-consecutive-cards predicate of the decoded endpoints. *)
Lemma five_card_exec_decode_seqE (ep : seq 'I_(pgg_N' (mp_M mpF)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpF)).+1) :
  @exec_decode mpF five_card_exec_plug ep Hsz
  = fc_three_consec [seq decode_bool x | x <- ep].
Proof.
rewrite (five_card_exec_decodeE Hsz Hsz).
by rewrite /ts_recon /fcI_scheme /fcI_recon val_tcast.
Qed.

(** five_card_exec_recon — decoding the static observation returns the
    conjunction of the two committed bits, for any cut in the group and any
    proof of the endpoint count. *)
Lemma five_card_exec_recon (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  w0 \in pgg_G FiveCardKim_M ->
  forall Hsz : size (@exec_static_endpoints mpF five_card_exec_plug
                       five_card_content_obs (a, b) w0)
               = (pi_T' (mp_PI mpF)).+1,
  @exec_decode mpF five_card_exec_plug
    (@exec_static_endpoints mpF five_card_exec_plug five_card_content_obs
       (a, b) w0) Hsz
  = (a, b).1 && (a, b).2.
Proof.
move=> Gw0 Hsz; rewrite five_card_exec_decode_seqE -five_card_exec_endpoints.
rewrite /exec_endpoints /exec_run five_card_exec_fuelE five_card_exec_procsE.
exact: (den_boer_run_recovers a b w0 Gw0).
Qed.

(** five_card_exec_recovers — the derived five-card run decodes to the
    conjunction of the two committed bits. *)
Theorem five_card_exec_recovers (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (Gw0 : w0 \in pgg_G FiveCardKim_M) :
  @exec_decode mpF five_card_exec_plug
    (@exec_endpoints mpF five_card_exec_plug (a, b) w0 0)
    (exec_endpoints_size (five_card_exec_endpoints a b w0)) = a && b.
Proof.
exact: (@exec_run_recovers mpF five_card_exec_plug five_card_content_obs
          (fun ab => ab.1 && ab.2) (a, b) w0 0
          (five_card_exec_endpoints a b w0) (five_card_exec_recon Gw0)).
Qed.

(** five_card_exec_correct — termination, endpoint count and recovery of the
    derived five-card run. *)
Theorem five_card_exec_correct (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (Gw0 : w0 \in pgg_G FiveCardKim_M) :
  [/\ (@exec_run mpF five_card_exec_plug (a, b) w0 0).1
        = nseq (size (@exec_procs mpF five_card_exec_plug (a, b) w0 0))
            Finish,
      size (@exec_endpoints mpF five_card_exec_plug (a, b) w0 0)
        = (pi_T' (mp_PI mpF)).+1 &
      @exec_decode mpF five_card_exec_plug
        (@exec_endpoints mpF five_card_exec_plug (a, b) w0 0)
        (exec_endpoints_size (five_card_exec_endpoints a b w0)) = a && b].
Proof.
exact: (@exec_run_correct mpF five_card_exec_plug five_card_content_obs
          (fun ab => ab.1 && ab.2) (a, b) w0 0
          (five_card_exec_terminates a b w0 0)
          (five_card_exec_endpoints a b w0) (five_card_exec_recon Gw0)).
Qed.

(******************************************************************************)
(*     The endpoint and trace read-off at five_card_profile                   *)
(******************************************************************************)

(** five_card_exec_seat_endpointE — seat i's endpoint is the layout entry at
    the cut image of seat i's start. *)
Lemma five_card_exec_seat_endpointE (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (i : 'I_(pi_T' (mp_PI mpF)).+1) :
  @exec_seat_endpoint mpF five_card_exec_plug (a, b) w0 0 i
  = five_card_content_obs (a, b) (w0, tnth (pi_starts (mp_PI mpF)) i).
Proof. exact: (exec_seat_endpointE (five_card_exec_endpoints a b w0) i). Qed.

(** five_card_exec_coalition_endpointsE — a coalition's endpoint readings are
    the layout entries at the cut images of its seats, reading ord0 for every
    seat outside the coalition. *)
Lemma five_card_exec_coalition_endpointsE (a b : bool)
    (w0 : pgg_gT FiveCardKim_M) (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :
  @exec_coalition_endpoints mpF five_card_exec_plug (a, b) w0 0 C
  = [ffun i => if i \in C
               then five_card_content_obs (a, b)
                      (w0, tnth (pi_starts (mp_PI mpF)) i)
               else ord0].
Proof.
exact: (exec_coalition_endpointsE (five_card_exec_endpoints a b w0) C).
Qed.

(** five_card_exec_coalition_endpoints_seqE — the coalition's endpoints in
    seat order are the layout entries at the cut images of its seats. *)
Lemma five_card_exec_coalition_endpoints_seqE (a b : bool)
    (w0 : pgg_gT FiveCardKim_M) (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :
  [seq @exec_seat_endpoint mpF five_card_exec_plug (a, b) w0 0 i
   | i <- enum C]
  = [seq five_card_content_obs (a, b) (w0, tnth (pi_starts (mp_PI mpF)) i)
     | i <- enum C].
Proof.
exact: (exec_coalition_endpoints_seqE (five_card_exec_endpoints a b w0) C).
Qed.

(** five_card_exec_player_raw_trace — seat i's raw executed trace: the generic
    participant extractor exec_participant_trace at five_card_exec_plug,
    committed pair ab, cut w0 and process offset 0. It agrees with
    denboer_player_trace. *)
Definition five_card_exec_player_raw_trace (ab : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) (i : 'I_(pi_T' (mp_PI mpF)).+1) :=
  @exec_participant_trace mpF five_card_exec_plug ab w0 0 i.

(** five_card_exec_coalition_raw_trace — a coalition's raw executed traces:
    the generic coalition assembly exec_coalition_trace at
    five_card_exec_plug, committed pair ab, cut w0 and process offset 0, the
    coalition twin of five_card_exec_player_raw_trace. *)
Definition five_card_exec_coalition_raw_trace (ab : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :=
  @exec_coalition_trace mpF five_card_exec_plug ab w0 0 C.

(** five_card_exec_input_raw_trace — committing party j's raw executed trace:
    the generic input extractor exec_input_trace at five_card_exec_plug,
    reading process identifier (pi_T' (mp_PI mpF)).+3 + j of the run, the
    committing-party twin of five_card_exec_player_raw_trace. *)
Definition five_card_exec_input_raw_trace (ab : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) (j : nat) :=
  @exec_input_trace mpF five_card_exec_plug ab w0 0 j.

(** five_card_exec_seat_countE — the profile's seat index type is 'I_5, the
    seat index type shared by the execution layer and the five-card coalition
    view. *)
Lemma five_card_exec_seat_countE : (pi_T' (mp_PI mpF)).+1 = 5.
Proof. by []. Qed.

(** five_card_exec_input_positions — the two committing parties are read at
    process identifiers 7 and 8: the unfolded identifier arithmetic behind
    the packaged exec_input_ids identifiers of five_card_exec_input_idsE. *)
Lemma five_card_exec_input_positions :
  [seq ((pi_T' (mp_PI mpF)).+3 + j)%N | j <- iota 0 2] = [:: 7; 8].
Proof. by []. Qed.

(** five_card_exec_raw_traceE — the derived raw trace is the trace of
    den_boer_procs at the seat's process identifier. *)
Lemma five_card_exec_raw_traceE (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (i : 'I_(pi_T' (mp_PI mpF)).+1) :
  five_card_exec_player_raw_trace (a, b) w0 i
  = nth [::] (run_interp 100 (den_boer_procs a b w0 0)).2 (2 + i).
Proof.
by rewrite /five_card_exec_player_raw_trace /exec_participant_trace
   /exec_seat_id /exec_run five_card_exec_fuelE five_card_exec_procsE.
Qed.

(******************************************************************************)
(*     The packaged observed execution at five_card_profile                   *)
(******************************************************************************)

(* The record quantifies over the committed pair, while the three execution
   lemmas take the pair split into two bits, so each field needs one case split
   on the pair and nothing else. *)

(** five_card_oe_terminates — every process of the five-card run reaches
    Finish at every committed pair and cut. *)
Lemma five_card_oe_terminates (x : bool * bool) (w0 : pgg_gT FiveCardKim_M) :
  (@exec_run mpF five_card_exec_plug x w0 0).1
  = nseq (size (@exec_procs mpF five_card_exec_plug x w0 0)) Finish.
Proof. by case: x => a b; exact: five_card_exec_terminates. Qed.

(** five_card_oe_endpoints — the five-card verifier endpoints are the static
    observation at every committed pair and cut. *)
Lemma five_card_oe_endpoints (x : bool * bool) (w0 : pgg_gT FiveCardKim_M) :
  @exec_endpoints mpF five_card_exec_plug x w0 0
  = @exec_static_endpoints mpF five_card_exec_plug five_card_content_obs x w0.
Proof. by case: x => a b; exact: five_card_exec_endpoints. Qed.

(** five_card_oe_static_recon — decoding the five-card static observation
    returns the conjunction of the committed pair. *)
Lemma five_card_oe_static_recon (x : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) :
  w0 \in pgg_G FiveCardKim_M ->
  forall Hsz : size (@exec_static_endpoints mpF five_card_exec_plug
                       five_card_content_obs x w0)
               = (pi_T' (mp_PI mpF)).+1,
  @exec_decode mpF five_card_exec_plug
    (@exec_static_endpoints mpF five_card_exec_plug five_card_content_obs x w0)
    Hsz
  = x.1 && x.2.
Proof. by case: x => a b; exact: five_card_exec_recon. Qed.

(* five_card_observed is the one value the den Boer and the Kim members of the
   family share. Neither its type nor its body can vary with the bias or the
   word length: five_card_profile and five_card_exec_plug are closed terms with
   no realType, no bias, no hypothesis pack and no word length, and the three
   proof fields quantify over the cut, not over a distribution on cuts. *)

(** five_card_observed — the five-card observed execution: five_card_profile
    with plug five_card_exec_plug at process offset 0, static observation
    five_card_content_obs and expected value the conjunction of the committed
    pair. *)
Definition five_card_observed : OE.ObservedExecution :=
  OE.MkObservedExecution mpF five_card_exec_plug 0
    five_card_content_obs (fun ab : bool * bool => ab.1 && ab.2)
    five_card_oe_terminates five_card_oe_endpoints five_card_oe_static_recon.

(** den_boer_observed — the den Boer observed execution: the five-card
    observed execution, since the den Boer member adds no execution data of
    its own to the five-card family. *)
Definition den_boer_observed : OE.ObservedExecution := five_card_observed.

(** den_boer_observed_core — the den Boer wrapper is the five-card observed
    execution. *)
Lemma den_boer_observed_core : den_boer_observed = five_card_observed.
Proof. by []. Qed.

(** five_card_observed_recovers — the packaged five-card run decodes to the
    conjunction of the committed pair. *)
Theorem five_card_observed_recovers (x : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) (Gw0 : w0 \in pgg_G FiveCardKim_M) :
  @exec_decode mpF five_card_exec_plug
    (@exec_endpoints mpF five_card_exec_plug x w0 0)
    (OE.oe_endpoints_size five_card_observed x w0) = x.1 && x.2.
Proof. exact: (OE.oe_run_recovers five_card_observed x w0 Gw0). Qed.

(******************************************************************************)
(*     The den Boer sample space of the five-card instance                    *)
(******************************************************************************)

(** five_card_sample_arg — the committed pair of a den Boer sample point: the
    first component of a point of bool * bool * 'I_5. *)
Definition five_card_sample_arg (u : five_card_leakage.Omega)
    : (bool * bool)%type := u.1.

(** five_card_sample_cut — the cut of a den Boer sample point: the rotation
    fc_sigma ^+ k realizing the sampled rotation k, the second component of a
    point of bool * bool * 'I_5. *)
Definition five_card_sample_cut (u : five_card_leakage.Omega)
    : pgg_gT (mp_M mpF) := (five_card_group.fc_sigma ^+ u.2)%g.

(** five_card_sample — the five-card sample adapter: the sample layer over
    five_card_exec_plug whose sample space is the den Boer leakage space
    Omega under its uniform distribution P, with the run argument the
    committed pair and the cut the realized rotation. *)
Definition five_card_sample : SampleAdapter R five_card_exec_plug :=
  @MkSampleAdapter R mpF five_card_exec_plug five_card_leakage.Omega (P R)
    five_card_sample_arg five_card_sample_cut.

(** five_card_sample_run — layer 1 at the den Boer space: the run at a sample
    point, sa_run at five_card_sample and process offset 0, the run at the
    sampled committed pair and the sampled rotation. *)
Definition five_card_sample_run (u : five_card_leakage.Omega) :=
  @sa_run R mpF five_card_exec_plug five_card_sample 0 u.

(** five_card_sample_seat_view — layer 2 at the den Boer space: seat i's
    endpoint, sa_seat_view at five_card_sample, seat i's endpoint reader as a
    random variable on P. *)
Definition five_card_sample_seat_view (i : 'I_(pi_T' (mp_PI mpF)).+1) :=
  @sa_seat_view R mpF five_card_exec_plug five_card_sample 0 i.

(** five_card_sample_coalition_view — layer 2 at the den Boer space: a
    coalition's readings, sa_coalition_view at five_card_sample, the
    coalition endpoint reader as a random variable on P. *)
Definition five_card_sample_coalition_view
    (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :=
  @sa_coalition_view R mpF five_card_exec_plug five_card_sample 0 C.

(** five_card_sample_seat_dist — layer 3 at the den Boer space: the
    distribution of seat i's endpoint, the pushforward of P along
    five_card_sample_seat_view i. *)
Definition five_card_sample_seat_dist (i : 'I_(pi_T' (mp_PI mpF)).+1) :=
  @sa_seat_dist R mpF five_card_exec_plug five_card_sample 0 i.

(** five_card_sample_coalition_dist — layer 3 at the den Boer space, coalition
    form: the pushforward of P along five_card_sample_coalition_view C. *)
Definition five_card_sample_coalition_dist
    (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :=
  @sa_coalition_dist R mpF five_card_exec_plug five_card_sample 0 C.

(** five_card_sample_cut_dist — the den Boer sample space's cut distribution:
    the pushforward of P along the rotation map five_card_sample_cut. *)
Definition five_card_sample_cut_dist :=
  @sa_cut_dist R mpF five_card_exec_plug five_card_sample.

(** five_card_sample_seat_distE — the executed seat distribution at the den
    Boer space is the distribution of the layout entry at the rotation image
    of the seat's start. *)
Lemma five_card_sample_seat_distE (i : 'I_(pi_T' (mp_PI mpF)).+1) :
  five_card_sample_seat_dist i
  = fdistmap (@sa_static_seat_view R mpF five_card_exec_plug five_card_sample
                five_card_content_obs i) (P R).
Proof.
by apply: sa_seat_distE => -[[a b] k]; exact: five_card_exec_endpoints.
Qed.

(** five_card_sample_coalition_distE — the executed coalition distribution at
    the den Boer space is the distribution of the layout entries at the
    rotation images of the coalition's starts. *)
Lemma five_card_sample_coalition_distE (C : {set 'I_(pi_T' (mp_PI mpF)).+1}) :
  five_card_sample_coalition_dist C
  = fdistmap (@sa_static_coalition_view R mpF five_card_exec_plug
                five_card_sample five_card_content_obs C) (P R).
Proof.
by apply: sa_coalition_distE => -[[a b] k]; exact: five_card_exec_endpoints.
Qed.

(******************************************************************************)
(*     Single-player executed-trace secrecy through the generic extractor     *)
(******************************************************************************)

Let dbP := P R.

(** five_card_exec_trace — seat i's executed trace as a random variable on the
    leakage space: content_of of five_card_exec_player_raw_trace at the
    committed pair (w.1.1, w.1.2) and the cut fc_sigma ^+ w.2 realizing
    rotation w.2, the plug-side twin of denboer_player_trace. *)
Definition five_card_exec_trace (i : 'I_(pi_T' (mp_PI mpF)).+1)
    : {RV dbP -> 'I_5} :=
  fun w => content_of (five_card_exec_player_raw_trace (w.1.1, w.1.2)
                         (five_card_group.fc_sigma ^+ w.2)%g i).

(** five_card_exec_traceE — the execution layer's trace variable is the den
    Boer trace variable of denboer_trace.v. *)
Lemma five_card_exec_traceE (i : 'I_(pi_T' (mp_PI mpF)).+1) :
  five_card_exec_trace i = denboer_player_trace R i.
Proof.
apply: funext => -[[a b] k].
rewrite /five_card_exec_trace /denboer_player_trace /denboer_rprocs.
by rewrite five_card_exec_raw_traceE.
Qed.

(** five_card_exec_trace_secrecy — one seat's executed trace, read through the
    generic extractor, leaves the secret's conditional entropy equal to its
    plain entropy: this transports denboer_trace_secrecy to the execution
    layer. *)
Corollary five_card_exec_trace_secrecy :
  `H( Secret R | five_card_exec_trace ord0 ) = `H `p_ (Secret R).
Proof. by rewrite five_card_exec_traceE; exact: denboer_trace_secrecy. Qed.

(******************************************************************************)
(*     The cut distribution of the den Boer sample space                      *)
(******************************************************************************)

(** five_card_card_bool2 — the pair of committed bits has four values. The
    identical certificate card_bool2 is declared at kim_input_privacy.v:51;
    this file keeps its own local copy under the five_card prefix rather than
    add an import edge to that file. *)
Lemma five_card_card_bool2 : #|{: bool * bool}| = 3.+1.
Proof. by rewrite card_prod card_bool. Qed.

(** five_card_sample_uniform_prodE — the den Boer leakage distribution is the
    product of the uniform distribution on the committed pair with the uniform
    distribution on the rotation. *)
Lemma five_card_sample_uniform_prodE :
  P R = ((fdist_uniform five_card_card_bool2)
         `x (fdist_uniform (card_ord 5)))%fdist.
Proof.
apply/fdist_ext => -[ab k].
rewrite fdist_prodE /P !fdist_uniformE.
rewrite card_Omega20 five_card_card_bool2 card_ord.
by rewrite -invfM -natrM.
Qed.

(** five_card_sample_snd_uniformE — the rotation marginal of the den Boer
    leakage distribution is uniform on 'I_5. *)
Lemma five_card_sample_snd_uniformE :
  fdistmap (fun u : five_card_leakage.Omega => u.2) (P R)
  = fdist_uniform (card_ord 5).
Proof.
rewrite five_card_sample_uniform_prodE.
by rewrite -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

(** five_card_sample_cut_distE — the den Boer sample space's cut distribution
    is the image of the uniform rotation distribution under the rotation
    realization k |-> fc_sigma ^+ k. *)
Lemma five_card_sample_cut_distE :
  five_card_sample_cut_dist
  = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
      (fdist_uniform (card_ord 5)).
Proof.
rewrite /five_card_sample_cut_dist /sa_cut_dist /five_card_sample /=.
rewrite /five_card_sample_cut -five_card_sample_snd_uniformE.
by rewrite fdistmap_comp.
Qed.

(******************************************************************************)
(*     The committing parties' executed rows                                  *)
(******************************************************************************)

(** five_card_exec_traces_size — the den Boer run has nine trace rows. *)
Lemma five_card_exec_traces_size (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  size (run_interp 100 (den_boer_procs a b w0 0)).2 = 9.
Proof. rewrite /den_boer_procs; vm_compute; reflexivity. Qed.

(** five_card_exec_input_raw_traceE — committing party j's executed row is
    empty, at every j. Rows 0 and 1, the rows of the two committing parties,
    are empty because a Send logs nothing to the sender's own row in this
    interpreter and the committing parties are pure senders. Rows j >= 2 are
    empty by the nth default past the nine-process run. *)
Lemma five_card_exec_input_raw_traceE (a b : bool)
    (w0 : pgg_gT FiveCardKim_M) (j : nat) :
  five_card_exec_input_raw_trace (a, b) w0 j = [::].
Proof.
rewrite /five_card_exec_input_raw_trace /exec_input_trace /exec_input_id
        /exec_run five_card_exec_fuelE five_card_exec_procsE.
case: j => [|[|j]];
  last by apply: nth_default; rewrite five_card_exec_traces_size.
all: by rewrite /den_boer_procs; vm_compute.
Qed.

(** five_card_exec_input_trace — committing party j's executed-row content as
    a random variable on the leakage space: content_of of
    five_card_exec_input_raw_trace at the committed pair (w.1.1, w.1.2) and
    the cut fc_sigma ^+ w.2 realizing rotation w.2, the committing-party twin
    of five_card_exec_trace. *)
Definition five_card_exec_input_trace (j : nat) : {RV dbP -> 'I_5} :=
  fun w => content_of (five_card_exec_input_raw_trace (w.1.1, w.1.2)
                         (five_card_group.fc_sigma ^+ w.2)%g j).

(** five_card_exec_input_trace_secrecy — conditioning the secret on committing
    party j's executed-row observable leaves its entropy unchanged, at every
    j. The rows are empty because in this interpreter model a Send logs
    nothing to the sender's own trace, so this is a constant-conditioning
    statement, not a commitment-privacy result: a committing party knows its
    own bit, so even a non-empty row would not make this a privacy statement
    about that party. The committed payloads travel to the dealer's row
    instead, which five_card_exec_dealer_pair_centropy0 and
    five_card_exec_dealer_trace_centropy0 show determines both bits. *)
Lemma five_card_exec_input_trace_secrecy (j : nat) :
  `H( Secret R | five_card_exec_input_trace j ) = `H `p_ (Secret R).
Proof.
have Hc : five_card_exec_input_trace j
        = (fun _ : unit => ord0) `o (unit_RV dbP).
  apply: funext => w.
  rewrite /five_card_exec_input_trace /comp_RV.
  by rewrite five_card_exec_input_raw_traceE.
rewrite Hc; apply: inde_cond_entropy.
apply: pgg_trace_secrecy.inde_RV_comp; exact: inde_unit_RV.
Qed.

(******************************************************************************)
(*     The dealer's executed row                                              *)
(******************************************************************************)

(** five_card_exec_dealer_raw_trace — the dealer's raw executed trace: the
    generic dealer extractor exec_dealer_trace at five_card_exec_plug,
    committed pair ab, cut w0 and process offset 0, the dealer twin of
    five_card_exec_input_raw_trace. *)
Definition five_card_exec_dealer_raw_trace (ab : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) :=
  @exec_dealer_trace mpF five_card_exec_plug ab w0 0.

(** five_card_exec_dealer_raw_traceE — the dealer's executed row is the deck
    index followed by the two committed card positions. The row is
    anti-chronological: the head PGG_idx 0 is the dealer's own Init of the
    deck index, which happens last, then party 8's card position
    PGG_sheet (encode_bool b), then party 7's PGG_sheet (encode_bool a). *)
Lemma five_card_exec_dealer_raw_traceE (a b : bool)
    (w0 : pgg_gT FiveCardKim_M) :
  five_card_exec_dealer_raw_trace (a, b) w0
  = [:: PGG_idx 0; PGG_sheet (encode_bool b); PGG_sheet (encode_bool a)].
Proof.
rewrite /five_card_exec_dealer_raw_trace /exec_dealer_trace /exec_dealer_id
        /exec_run five_card_exec_fuelE five_card_exec_procsE.
rewrite /den_boer_procs; vm_compute; reflexivity.
Qed.

(** five_card_exec_dealer_readout — the committed pair decoded from a dealer
    row: decode_bool of the two card positions of a three-entry row, the
    second bit
    at the head, and (false, false) elsewhere, the row-level companion of
    five_card_exec_dealer_trace. The (false, false) value returned on a
    malformed row coincides with a legitimate committed pair, so the readout
    is meaningful only through five_card_exec_dealer_raw_traceE. *)
Definition five_card_exec_dealer_readout
    (tr : seq (pgg_data (pgg_N' FiveCardKim_M).+1)) : (bool * bool)%type :=
  if tr is [:: _ ; PGG_sheet y ; PGG_sheet x]
  then (decode_bool x, decode_bool y) else (false, false).

(** five_card_exec_dealer_trace — the dealer's executed row decoded as a
    random variable on the leakage space: five_card_exec_dealer_readout of
    five_card_exec_dealer_raw_trace at the committed pair (w.1.1, w.1.2) and
    the cut fc_sigma ^+ w.2 realizing rotation w.2, the dealer twin of
    five_card_exec_trace. *)
Definition five_card_exec_dealer_trace : {RV dbP -> (bool * bool)%type} :=
  fun w => five_card_exec_dealer_readout
             (five_card_exec_dealer_raw_trace (w.1.1, w.1.2)
                (five_card_group.fc_sigma ^+ w.2)%g).

(** five_card_exec_dealer_traceE — the dealer's decoded row is the sampled
    committed pair. *)
Lemma five_card_exec_dealer_traceE :
  five_card_exec_dealer_trace = fun w => (w.1.1, w.1.2).
Proof.
apply: funext => w.
rewrite /five_card_exec_dealer_trace five_card_exec_dealer_raw_traceE.
by rewrite /five_card_exec_dealer_readout /= !decode_encode_bool.
Qed.

(** five_card_exec_dealer_pair_centropy0 — the dealer's decoded row determines
    the committed pair. *)
Lemma five_card_exec_dealer_pair_centropy0 :
  `H( (fun w : five_card_leakage.Omega => w.1)
      | five_card_exec_dealer_trace ) = 0.
Proof.
have -> : (fun w : five_card_leakage.Omega => w.1)
        = idfun `o five_card_exec_dealer_trace.
  by apply: funext => -[[a b] k]; rewrite /comp_RV five_card_exec_dealer_traceE.
exact: centropy_RV_comp0.
Qed.

(** five_card_exec_dealer_trace_centropy0 — the dealer's decoded row
    determines the secret. *)
Lemma five_card_exec_dealer_trace_centropy0 :
  `H( Secret R | five_card_exec_dealer_trace ) = 0.
Proof.
have -> : Secret R
        = (fun p : bool * bool => p.1 && p.2) `o five_card_exec_dealer_trace.
  by apply: funext => -[[a b] k]; rewrite /comp_RV five_card_exec_dealer_traceE.
exact: centropy_RV_comp0.
Qed.

End five_card_execution.

(* The bias-independence content of the former two-bias statement moved into
   the type: five_card_profile and five_card_exec_plug carry neither a bias nor
   a word length, so there is one process list, compared here with itself. *)

(** five_card_exec_procs_biasE — the executed program does not depend on the
    bias. *)
Lemma five_card_exec_procs_biasE (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (P_idx : nat) :
  @exec_procs five_card_profile five_card_exec_plug (a, b) w0 P_idx
  = @exec_procs five_card_profile five_card_exec_plug (a, b) w0 P_idx.
Proof. by []. Qed.

(******************************************************************************)
(*     The den Boer member's witness distribution                             *)
(******************************************************************************)

Section five_card_one_letter_words.
Local Open Scope vec_ext_scope.

Variable R : realType.
Variables (N'' m : nat).
Variable sigmas : m.+1.-tuple {perm 'I_N''.+2}.
Variable W : R.-fdist 'I_m.+1.

(** fdistmap_head1 — the head letter of a one-letter word is distributed as
    the letter itself. *)
Lemma fdistmap_head1 :
  fdistmap (fun v : 'rV['I_m.+1]_1 => v ``_ ord0) (W `^ 1) = W.
Proof.
apply/fdist_ext => k; rewrite fdistmapE big_mkcond /=.
under eq_bigr do rewrite fdist_rV1 inE /=.
apply: (bigop_ext.big_rV1_ord0 (f := fun j => if j == k then W j else 0)).
by rewrite -big_mkcond big_pred1_eq.
Qed.

(** rho_from_words_weighted1 — the word shuffle at word length 1 is the image
    of the letter distribution under the alphabet lookup. *)
Lemma rho_from_words_weighted1 :
  @rho_from_words_weighted R N'' m 1 sigmas W = fdistmap (tnth sigmas) W.
Proof.
rewrite /rho_from_words_weighted /word_weighted fdistmap_comp.
have -> : (@word_eval (Gen_PGGTypes sigmas) 1) \o (@tuple_of_row _ 1)
        = (tnth sigmas) \o (fun v : 'rV['I_m.+1]_1 => v ``_ ord0).
  apply: funext => v; rewrite /= /word_eval big_ord1.
  by congr (tnth sigmas _); rewrite tnth_mktuple.
by rewrite -fdistmap_comp fdistmap_head1.
Qed.

End five_card_one_letter_words.

Section den_boer_witness_distribution.

Variable R : realType.

(** kim_weight_uniform_at0 — the Kim weight distribution at bias 0 is uniform
    on 'I_5. *)
Lemma kim_weight_uniform_at0 :
  kim_weight_dist (den_boer_eps0_lt R) (den_boer_eps0_gt R)
  = fdist_uniform (card_ord 5).
Proof.
apply/fdist_ext => k; rewrite kim_weight_distE fdist_uniformE card_ord.
by case: ifP => _; [rewrite subr0 | rewrite mul0r addr0].
Qed.

(** den_boer_witness_rotationE — the den Boer marginal bound's distribution is
    the image of the uniform rotation distribution under the rotation
    realization k |-> fc_sigma ^+ k. *)
Lemma den_boer_witness_rotationE :
  sw_rho_dist (den_boer_marginal_bound R)
  = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
      (fdist_uniform (card_ord 5)).
Proof.
rewrite /den_boer_marginal_bound /= rho_from_words_weighted1
        kim_weight_uniform_at0.
by congr fdistmap; apply: funext => k; exact: fc_kim_sigmasE.
Qed.

End den_boer_witness_distribution.

(** den_boer_sample_cut_witnessE — the five-card sample's cut distribution is
    the den Boer marginal bound's own shuffle distribution. *)
Lemma den_boer_sample_cut_witnessE (R : realType) :
  five_card_sample_cut_dist R = sw_rho_dist (den_boer_marginal_bound R).
Proof. by rewrite five_card_sample_cut_distE den_boer_witness_rotationE. Qed.
