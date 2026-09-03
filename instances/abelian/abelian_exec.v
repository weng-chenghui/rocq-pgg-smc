(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* abelian_exec: the two ExecutionPlug values of the abelian instance         *)
(*                                                                            *)
(* The four-seat abelian instance carries two execution plugs over the same   *)
(* profile abel_profile. The secret-recovery plug takes the dealt secret 'I_4 *)
(* as its run argument and reads the shares ts_encode abel_ts of that secret; *)
(* the shuffle-analysis plug takes the unit as its run argument and reads the *)
(* identity content, so its endpoints record the cut permutation itself on   *)
(* all four starting positions. Both use the participant list abel_players    *)
(* and fuel 150.                                                             *)
(*                                                                            *)
(* The identity-content plug has no dealt secret, so it has no arbitrary-     *)
(* secret recovery statement. What it recovers is the constant                *)
(* abel_identity_recon_value, the sum-mod reconstruction of the identity      *)
(* layout, and that constant is the same for every cut permutation.           *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   abel_players        == the four seat ordinals as an explicit list        *)
(*   abel_exec_plug      == the secret-recovery execution plug                *)
(*   abel_content_obs    == the secret-recovery static observation: the share *)
(*                          of the dealt secret at the cut image of a        *)
(*                          starting position                                *)
(*   abel_det_observed   == the ObservedExecution packing the secret-recovery *)
(*                          plug, its static observation and its three run    *)
(*                          facts at process offset 0                         *)
(*   abel_shuffle_plug   == the identity-content execution plug               *)
(*   abel_id_obs         == the identity-content static observation: the cut  *)
(*                          image of a starting position                      *)
(*   abel_identity_recon_value == the constant 2 : 'I_4 it reconstructs       *)
(*   abel_shuffle_observed == the ObservedExecution of the identity-content   *)
(*                          plug                                              *)
(*   abel_reader         == the complete four-endpoint vector of a cut        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   abel_exec_endpoint_count == the secret-recovery run collects four        *)
(*                          endpoints                                         *)
(*   abel_exec_recovers  == the secret-recovery run decodes to the dealt      *)
(*                          secret                                            *)
(*   abel_exec_correct   == termination, endpoint count and recovery of the   *)
(*                          secret-recovery run                               *)
(*   abel_observed_recovers == the same recovery through the packaged         *)
(*                          observed execution                                *)
(*   abel_shuffle_endpoint_count == the identity-content run collects four    *)
(*                          endpoints                                         *)
(*   abel_shuffle_recovers == the identity-content run decodes to that        *)
(*                          constant                                          *)
(*   abel_shuffle_correct == termination, endpoint count and constant        *)
(*                          recovery of the identity-content run             *)
(*   abel_shuffle_observed_recovers == the same constant recovery through the *)
(*                          packaged observed execution                       *)
(*   abel_reader_inj     == the complete four-endpoint vector determines the  *)
(*                          cut                                               *)
(*   abel_shuffle_executed_readerE == the identity-content executed endpoints *)
(*                          are that vector                                   *)
(*   abel_exec_seat_endpointE == seat i's endpoint is the share at the cut    *)
(*                          image of seat i's start                           *)
(*   abel_shuffle_seat_endpointE == seat i's identity-content endpoint is the *)
(*                          cut image of seat i's start                       *)
(*   abel_exec_coalition_endpointsE == a coalition's endpoint readings are    *)
(*                          the shares at the cut images of its seats         *)
(*   abel_exec_verifier_traceE, abel_shuffle_verifier_traceE == the derived   *)
(*                          verifier rows are process row 1 of the run        *)
(*   abel_exec_raw_traceE, abel_shuffle_raw_traceE == the derived raw seat    *)
(*                          rows are process row 2 + i of the run            *)
(*   abel_seat_countE    == the profile's seat index type is 'I_4             *)
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
From pgg_smc Require Import rigidity_abelian_instance abel_profile.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* abel_M — the abelian two-generator monodromy template at N = 4, the
   Gen_PGGTypes form abel_profile is built over. *)
Local Notation abel_M := (@Gen_PGGTypes 1 2 abel_sigmas).

(******************************************************************************)
(*     The shared four-seat program flow                                      *)
(******************************************************************************)

(** abel_players — the four seats, listed one by one.  Spelled out rather
    than written as enum 'I_4 so that the dealer's fold_senv reduces under
    vm_compute; the interpreter facts of this file are settled by that
    reduction, and an unreduced enumeration would leave them stuck. *)
Definition abel_players : seq 'I_4 :=
  [:: @Ordinal 4 0 isT; @Ordinal 4 1 isT; @Ordinal 4 2 isT; @Ordinal 4 3 isT].

(** abel_players_enumE — the listed seats are the full seat enumeration, in
    order, so writing them out loses nothing and every seat takes part. *)
Lemma abel_players_enumE :
  abel_players = enum 'I_(pi_T' (mp_PI abel_profile)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** abel_verifier_endpoints — running the six-process abelian program leaves
    the verifier holding, for each seat, the dealt content read at the card
    the shuffle moved that seat's start to.  Stated for an arbitrary content
    function and an arbitrary starting layout, so that the two plugs below
    are two readings of this one execution and not two executions. *)
Lemma abel_verifier_endpoints
    (g : seq 'I_(pgg_N' abel_M).+1 -> ('I_4 -> 'I_4))
    (w0 : pgg_gT abel_M)
    (st : 4.-tuple 'I_4) (Hst : uniq st) :
  let PI' := @MkPGGI abel_M 3 st Hst in
  endpoints_of_trace (nth [::] (run_interp 150 (erase_aprocs
    [:: mk_aproc (pgg_commit_prologue (fun committed =>
           exchange_dealer PI' (g committed) abel_players [:: w0] 0) [::] [::])
      ; mk_aproc (exchange_verifier PI' abel_players)
      ; mk_aproc (exchange_player PI' (@Ordinal 4 0 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 4 1 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 4 2 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 4 3 isT))])).2 1)
  = [seq g [::] (@pgg_rho abel_M w0 (tnth st i)) | i <- abel_players].
Proof. move=> PI'; rewrite /PI'; vm_compute; reflexivity. Qed.

(** abel_rhoE — a group element acts on a card position as the permutation it
    already is: the abelian monodromy is the inclusion of a group of shuffles
    into the shuffles. *)
Lemma abel_rhoE (w0 : pgg_gT abel_M) (x : 'I_4) : @pgg_rho abel_M w0 x = w0 x.
Proof. by []. Qed.

(** abel_static_tnth — entry i of the observation tuple is what seat i sees,
    namely the observation taken at seat i's own starting card.  It is the
    step that makes the run's endpoint list addressable by seat. *)
Lemma abel_static_tnth (e : ExecutionPlug abel_profile)
    (obs : ep_inputT e -> pgg_gT (mp_M abel_profile)
             * 'I_(pgg_N' (mp_M abel_profile)).+1
             -> 'I_(pgg_N' (mp_M abel_profile)).+1)
    (x : ep_inputT e) (w0 : pgg_gT abel_M)
    (H : size (@exec_static_endpoints abel_profile e obs x w0) = 4)
    (i : 'I_4) :
  tnth (tcast H (in_tuple (@exec_static_endpoints abel_profile e obs x w0))) i
  = obs x (w0, tnth (pi_starts abel_PI) i).
Proof.
rewrite tcastE (tnth_nth ord0) /= /exec_static_endpoints (ep_playersE e).
by rewrite (nth_map i) ?nth_ord_enum // size_enum_ord ltn_ord.
Qed.

(** abel_decodeE — decoding a run's endpoints is the sum-mod reconstruction of
    the sharing scheme, the two proofs of size agreement being
    interchangeable.  It connects what the program does to what the sharing
    scheme promises. *)
Lemma abel_decodeE (e : ExecutionPlug abel_profile) (ep : seq 'I_4)
    (Hsz : size ep = (pi_T' (mp_PI abel_profile)).+1)
    (Hsz' : size ep = (ts_T' abel_ts).+1) :
  @exec_decode abel_profile e ep Hsz
  = ts_recon abel_ts (tcast Hsz' (in_tuple ep)).
Proof.
by rewrite /exec_decode /run_recover (eq_irrelevance (etrans Hsz _) Hsz').
Qed.

(******************************************************************************)
(*     The secret-recovery plug                                               *)
(******************************************************************************)

(** abel_exec_plug — the execution layer that deals a secret: its run
    argument is the secret in 'I_4, the content each card carries is that
    secret's share, and the four seats meet the four shares with no
    reindexing.  Fuel is 150 because the termination and endpoint facts below
    are settled by reduction at that fuel; a smaller number would leave them
    unproved and a larger one would slow the reduction without changing
    them. *)
Definition abel_exec_plug : ExecutionPlug abel_profile :=
  @dealer_secret_plug abel_profile 'I_4 erefl abel_players abel_players_enumE
    (fun s _ => tnth (ts_encode abel_ts s)) 150.

(** abel_content_obs — what a seat sees in the secret-recovery run: the share
    of the dealt secret sitting on the card the shuffle moved its start to.
    It is a closed form, independent of the interpreter, and the run is shown
    below to agree with it. *)
Definition abel_content_obs (s : 'I_4)
    (p : pgg_gT (mp_M abel_profile) * 'I_(pgg_N' (mp_M abel_profile)).+1)
    : 'I_(pgg_N' (mp_M abel_profile)).+1 :=
  tnth (ts_encode abel_ts s) (@pgg_rho (mp_M abel_profile) p.1 p.2).

(** abel_exec_procs_size — the run has six processes: the dealer, the
    verifier and one per seat. *)
Lemma abel_exec_procs_size (s : 'I_4) (w0 : pgg_gT abel_M) :
  size (@exec_procs abel_profile abel_exec_plug s w0 0) = 6.
Proof. by []. Qed.

(** abel_exec_terminates — every process of the run reaches Finish, so the
    protocol completes rather than deadlocking or running out of fuel. *)
Lemma abel_exec_terminates (s : 'I_4) (w0 : pgg_gT abel_M) :
  (@exec_run abel_profile abel_exec_plug s w0 0).1
  = nseq (size (@exec_procs abel_profile abel_exec_plug s w0 0)) Finish.
Proof. rewrite abel_exec_procs_size; vm_compute; reflexivity. Qed.

(** abel_exec_endpoints — what the run actually leaves the verifier holding is
    the closed-form observation, seat by seat.  From here every statement
    about the run can be made about a function of the shuffle instead of
    about an interpreter trace. *)
Lemma abel_exec_endpoints (s : 'I_4) (w0 : pgg_gT abel_M) :
  @exec_endpoints abel_profile abel_exec_plug s w0 0
  = @exec_static_endpoints abel_profile abel_exec_plug abel_content_obs s w0.
Proof.
have E : @exec_procs abel_profile abel_exec_plug s w0 0
  = erase_aprocs
    [:: mk_aproc (pgg_commit_prologue (fun committed =>
           exchange_dealer abel_PI
             ((fun _ => tnth (ts_encode abel_ts s)) committed)
             abel_players [:: w0] 0) [::] [::])
      ; mk_aproc (exchange_verifier abel_PI abel_players)
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 0 isT))
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 1 isT))
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 2 isT))
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 3 isT))] by [].
rewrite /exec_endpoints /exec_run E /exec_verifier_id.
rewrite (@abel_verifier_endpoints (fun _ => tnth (ts_encode abel_ts s))
           w0 (ord_tuple 4) abel_starts_uniq).
by [].
Qed.

(** abel_exec_endpoint_count — the run collects one endpoint per seat, four in
    all, so the endpoint list has the shape a four-share reconstruction can
    consume. *)
Lemma abel_exec_endpoint_count (s : 'I_4) (w0 : pgg_gT abel_M) :
  size (@exec_endpoints abel_profile abel_exec_plug s w0 0) = 4.
Proof. by rewrite (exec_endpoints_size (abel_exec_endpoints s w0)). Qed.

(** abel_exec_recon — decoding the closed-form observation returns the dealt
    secret, whatever the secret and whatever shuffle the group supplied.  The
    shuffle drops out because sum-mod reconstruction does not see the order of
    its shares. *)
Lemma abel_exec_recon (s : 'I_4) (w0 : pgg_gT abel_M) :
  w0 \in pgg_G abel_M ->
  forall Hsz : size (@exec_static_endpoints abel_profile abel_exec_plug
                       abel_content_obs s w0) = (pi_T' (mp_PI abel_profile)).+1,
  @exec_decode abel_profile abel_exec_plug
    (@exec_static_endpoints abel_profile abel_exec_plug abel_content_obs s w0)
    Hsz = s.
Proof.
move=> Gw0 Hsz.
rewrite (abel_decodeE abel_exec_plug Hsz Hsz).
rewrite -[RHS](abel_sum_mod_perm_compatible Gw0 (ts_encode_valid abel_ts s)).
congr (ts_recon _ _); apply: eq_from_tnth => i.
by rewrite abel_static_tnth tnth_mktuple /abel_content_obs /= tnth_ord_tuple.
Qed.

(** abel_exec_recovers — the executed run decodes to the dealt secret, for
    every secret in 'I_4 and every shuffle in the group.  It is correctness
    for an arbitrary secret, not for one fixed value, which is what
    distinguishes it from the constant recovery of the identity-content run
    below. *)
Theorem abel_exec_recovers (s : 'I_4) (w0 : pgg_gT abel_M)
    (Gw0 : w0 \in pgg_G abel_M) :
  @exec_decode abel_profile abel_exec_plug
    (@exec_endpoints abel_profile abel_exec_plug s w0 0)
    (exec_endpoints_size (abel_exec_endpoints s w0)) = s.
Proof.
exact: (@exec_run_recovers abel_profile abel_exec_plug abel_content_obs
          (fun s : 'I_4 => s) s w0 0 (abel_exec_endpoints s w0)
          (abel_exec_recon Gw0)).
Qed.

(** abel_exec_correct — the run terminates at each of its six processes,
    collects one endpoint per seat, and decodes to the dealt secret, for every
    secret and every shuffle in the group.  The three together are what it
    means for this instance to run correctly; none of them is a privacy
    claim. *)
Theorem abel_exec_correct (s : 'I_4) (w0 : pgg_gT abel_M)
    (Gw0 : w0 \in pgg_G abel_M) :
  [/\ (@exec_run abel_profile abel_exec_plug s w0 0).1
        = nseq (size (@exec_procs abel_profile abel_exec_plug s w0 0)) Finish,
      size (@exec_endpoints abel_profile abel_exec_plug s w0 0)
        = (pi_T' (mp_PI abel_profile)).+1 &
      @exec_decode abel_profile abel_exec_plug
        (@exec_endpoints abel_profile abel_exec_plug s w0 0)
        (exec_endpoints_size (abel_exec_endpoints s w0)) = s].
Proof.
exact: (@exec_run_correct abel_profile abel_exec_plug abel_content_obs
          (fun s : 'I_4 => s) s w0 0 (abel_exec_terminates s w0)
          (abel_exec_endpoints s w0) (abel_exec_recon Gw0)).
Qed.

(** abel_det_observed — the secret-recovery run packaged with what it
    observes and what it should recover: the plug, the closed-form observation
    and the identity as expected value, together with the three facts that
    the run terminates, matches the observation, and decodes.  Packaging is
    what lets later files quote the run without reopening the
    interpreter. *)
Definition abel_det_observed : OE.ObservedExecution :=
  OE.MkObservedExecution abel_profile abel_exec_plug 0
    abel_content_obs (fun s : 'I_4 => s)
    abel_exec_terminates abel_exec_endpoints (@abel_exec_recon).

(** abel_observed_recovers — the packaged run decodes to the dealt secret,
    the same statement as abel_exec_recovers read through the packaging rather
    than through the plug directly. *)
Theorem abel_observed_recovers (s : 'I_4) (w0 : pgg_gT abel_M)
    (Gw0 : w0 \in pgg_G abel_M) :
  @exec_decode abel_profile abel_exec_plug
    (@exec_endpoints abel_profile abel_exec_plug s w0 0)
    (OE.oe_endpoints_size abel_det_observed s w0) = s.
Proof. exact: (OE.oe_run_recovers abel_det_observed s w0 Gw0). Qed.

(******************************************************************************)
(*     The shuffle-analysis plug                                              *)
(******************************************************************************)

(** abel_shuffle_plug — the execution layer that deals nothing: its run
    argument is the unit and each card carries its own position as content, so
    the endpoints of a run record the shuffle itself and nothing else.  This
    is the plug the probability lives on, because it is the one whose
    observation is a function of the shuffle alone.  Fuel is 150 for the same
    reason as above. *)
Definition abel_shuffle_plug : ExecutionPlug abel_profile :=
  @dealer_secret_plug abel_profile unit erefl abel_players abel_players_enumE
    (fun _ _ => idfun) 150.

(** abel_id_obs — what a seat sees in the shuffle-analysis run: the card its
    start was moved to.  It ignores the run argument entirely, which is the
    point: no secret enters, so an observer of this run learns about the
    shuffle and about nothing else. *)
Definition abel_id_obs (x : unit)
    (p : pgg_gT (mp_M abel_profile) * 'I_(pgg_N' (mp_M abel_profile)).+1)
    : 'I_(pgg_N' (mp_M abel_profile)).+1 :=
  @pgg_rho (mp_M abel_profile) p.1 p.2.

(** abel_identity_recon_value — the card position 2, being the residue of
    0 + 1 + 2 + 3 modulo four.  Since a shuffle only permutes the summands,
    every shuffle reconstructs to this same value, which is why the
    identity-content run has a constant to recover instead of a secret. *)
Definition abel_identity_recon_value : 'I_4 := @Ordinal 4 2 isT.

(** abel_shuffle_procs_size — the run has six processes, the same shape as the
    secret-recovery run. *)
Lemma abel_shuffle_procs_size (x : unit) (w0 : pgg_gT abel_M) :
  size (@exec_procs abel_profile abel_shuffle_plug x w0 0) = 6.
Proof. by []. Qed.

(** abel_shuffle_terminates — every process of the run reaches Finish. *)
Lemma abel_shuffle_terminates (x : unit) (w0 : pgg_gT abel_M) :
  (@exec_run abel_profile abel_shuffle_plug x w0 0).1
  = nseq (size (@exec_procs abel_profile abel_shuffle_plug x w0 0)) Finish.
Proof. rewrite abel_shuffle_procs_size; vm_compute; reflexivity. Qed.

(** abel_shuffle_endpoints — what the run leaves the verifier holding is the
    list of cards the four starts were moved to.  The executed observation is
    therefore a function of the shuffle, which is what the distance
    computations later read. *)
Lemma abel_shuffle_endpoints (x : unit) (w0 : pgg_gT abel_M) :
  @exec_endpoints abel_profile abel_shuffle_plug x w0 0
  = @exec_static_endpoints abel_profile abel_shuffle_plug abel_id_obs x w0.
Proof.
have E : @exec_procs abel_profile abel_shuffle_plug x w0 0
  = erase_aprocs
    [:: mk_aproc (pgg_commit_prologue (fun committed =>
           exchange_dealer abel_PI ((fun _ => @idfun 'I_4) committed)
             abel_players [:: w0] 0) [::] [::])
      ; mk_aproc (exchange_verifier abel_PI abel_players)
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 0 isT))
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 1 isT))
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 2 isT))
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 3 isT))] by [].
rewrite /exec_endpoints /exec_run E /exec_verifier_id.
rewrite (@abel_verifier_endpoints (fun _ => @idfun 'I_4)
           w0 (ord_tuple 4) abel_starts_uniq).
by [].
Qed.

(** abel_shuffle_endpoint_count — the run collects one endpoint per seat,
    four in all. *)
Lemma abel_shuffle_endpoint_count (x : unit) (w0 : pgg_gT abel_M) :
  size (@exec_endpoints abel_profile abel_shuffle_plug x w0 0) = 4.
Proof. by rewrite (exec_endpoints_size (abel_shuffle_endpoints x w0)). Qed.

(** abel_shuffle_recon — decoding the identity-content observation returns
    card position 2 whatever the shuffle, since permuting the summands of a
    sum leaves it alone. *)
Lemma abel_shuffle_recon (x : unit) (w0 : pgg_gT abel_M) :
  w0 \in pgg_G abel_M ->
  forall Hsz : size (@exec_static_endpoints abel_profile abel_shuffle_plug
                       abel_id_obs x w0) = (pi_T' (mp_PI abel_profile)).+1,
  @exec_decode abel_profile abel_shuffle_plug
    (@exec_static_endpoints abel_profile abel_shuffle_plug abel_id_obs x w0)
    Hsz = abel_identity_recon_value.
Proof.
move=> Gw0 Hsz; rewrite (abel_decodeE abel_shuffle_plug Hsz Hsz).
apply: val_inj => /=.
under eq_bigr do rewrite (abel_static_tnth (e:=abel_shuffle_plug)).
under eq_bigr do rewrite /abel_id_obs /= tnth_ord_tuple abel_rhoE.
have E : (\sum_(i < 4) (w0 i : nat)) = \sum_(i < 4) (i : nat).
  by rewrite [RHS](reindex_perm w0).
by rewrite E !big_ord_recl big_ord0.
Qed.

(** abel_shuffle_recovers — the executed identity-content run decodes to the
    constant, for every shuffle in the group.  No secret is dealt on this
    path, so this is recovery of one fixed value and not the arbitrary-secret
    correctness of abel_exec_recovers; reading it as the latter would
    overstate what the identity-content path establishes. *)
Theorem abel_shuffle_recovers (x : unit) (w0 : pgg_gT abel_M)
    (Gw0 : w0 \in pgg_G abel_M) :
  @exec_decode abel_profile abel_shuffle_plug
    (@exec_endpoints abel_profile abel_shuffle_plug x w0 0)
    (exec_endpoints_size (abel_shuffle_endpoints x w0))
  = abel_identity_recon_value.
Proof.
exact: (@exec_run_recovers abel_profile abel_shuffle_plug abel_id_obs
          (fun _ : unit => abel_identity_recon_value) x w0 0
          (abel_shuffle_endpoints x w0) (abel_shuffle_recon Gw0)).
Qed.

(** abel_shuffle_correct — the identity-content run terminates at each of its
    six processes, collects one endpoint per seat, and decodes to the
    constant, for every shuffle in the group. *)
Theorem abel_shuffle_correct (x : unit) (w0 : pgg_gT abel_M)
    (Gw0 : w0 \in pgg_G abel_M) :
  [/\ (@exec_run abel_profile abel_shuffle_plug x w0 0).1
        = nseq (size (@exec_procs abel_profile abel_shuffle_plug x w0 0))
                Finish,
      size (@exec_endpoints abel_profile abel_shuffle_plug x w0 0)
        = (pi_T' (mp_PI abel_profile)).+1 &
      @exec_decode abel_profile abel_shuffle_plug
        (@exec_endpoints abel_profile abel_shuffle_plug x w0 0)
        (exec_endpoints_size (abel_shuffle_endpoints x w0))
      = abel_identity_recon_value].
Proof.
exact: (@exec_run_correct abel_profile abel_shuffle_plug abel_id_obs
          (fun _ : unit => abel_identity_recon_value) x w0 0
          (abel_shuffle_terminates x w0) (abel_shuffle_endpoints x w0)
          (abel_shuffle_recon Gw0)).
Qed.

(** abel_shuffle_observed — the identity-content run packaged with its
    observation and the constant it recovers, together with the three facts
    that it terminates, matches the observation, and decodes.  It is the
    execution the two shuffle models of the next file are attached to. *)
Definition abel_shuffle_observed : OE.ObservedExecution :=
  OE.MkObservedExecution abel_profile abel_shuffle_plug 0
    abel_id_obs (fun _ : unit => abel_identity_recon_value)
    abel_shuffle_terminates abel_shuffle_endpoints (@abel_shuffle_recon).

(** abel_shuffle_observed_recovers — the packaged identity-content run decodes
    to the constant, for every shuffle in the group. *)
Theorem abel_shuffle_observed_recovers (x : unit) (w0 : pgg_gT abel_M)
    (Gw0 : w0 \in pgg_G abel_M) :
  @exec_decode abel_profile abel_shuffle_plug
    (@exec_endpoints abel_profile abel_shuffle_plug x w0 0)
    (OE.oe_endpoints_size abel_shuffle_observed x w0)
  = abel_identity_recon_value.
Proof. exact: (OE.oe_run_recovers abel_shuffle_observed x w0 Gw0). Qed.

(******************************************************************************)
(*     The complete four-endpoint observer                                    *)
(******************************************************************************)

(** abel_reader — the whole of what a shuffle shows: the four cards its four
    starts were moved to, as a tuple.  It is the observation the abelian
    mixing statements are measured at, and it withholds nothing about the
    shuffle, which is what makes those statements about the shuffle rather
    than about a coarse view of it. *)
Definition abel_reader (sigma : {perm 'I_4}) : 4.-tuple 'I_4 :=
  [tuple sigma (tnth (pi_starts abel_PI) i) | i < 4].

(** abel_reader_inj — the four-endpoint vector determines the shuffle, and on
    all of the permutations of four cards rather than only on the four the
    group reaches.  Because the reader loses nothing, any distance between two
    shuffle distributions survives it unchanged, so the mixing statements read
    at the endpoints are the same numbers as the ones read at the
    shuffles. *)
Lemma abel_reader_inj : injective abel_reader.
Proof.
move=> x y H; apply/permP => z.
have Hz : tnth (abel_reader x) z = tnth (abel_reader y) z by rewrite H.
by move: Hz; rewrite /abel_reader !tnth_mktuple tnth_ord_tuple.
Qed.

(** abel_shuffle_static_readerE — the identity-content observation is exactly
    the four-endpoint vector, so the plug's own notion of what a seat sees
    coincides with the complete observation. *)
Lemma abel_shuffle_static_readerE (x : unit) (w0 : pgg_gT abel_M) :
  @exec_static_endpoints abel_profile abel_shuffle_plug abel_id_obs x w0
  = val (abel_reader w0).
Proof.
rewrite /exec_static_endpoints /abel_reader (ep_playersE abel_shuffle_plug).
by rewrite /=; apply: eq_map => i; rewrite tnth_ord_tuple.
Qed.

(** abel_shuffle_executed_readerE — what the run leaves the verifier holding
    is the four-endpoint vector of the shuffle.  It is the join between the
    interpreter side and the probability side: a statement proved about the
    reader is a statement about the executed protocol. *)
Lemma abel_shuffle_executed_readerE (x : unit) (w0 : pgg_gT abel_M) :
  @exec_endpoints abel_profile abel_shuffle_plug x w0 0 = val (abel_reader w0).
Proof. by rewrite abel_shuffle_endpoints abel_shuffle_static_readerE. Qed.

(******************************************************************************)
(*     The remaining observer types read off the two plugs                    *)
(******************************************************************************)

(** abel_exec_seat_endpointE — one seat of the secret-recovery run sees the
    share sitting on the card its start was moved to.  It is the individual
    view, from which any coalition's view is assembled. *)
Lemma abel_exec_seat_endpointE (s : 'I_4) (w0 : pgg_gT abel_M)
    (i : 'I_(pi_T' (mp_PI abel_profile)).+1) :
  @exec_seat_endpoint abel_profile abel_exec_plug s w0 0 i
  = abel_content_obs s (w0, tnth (pi_starts (mp_PI abel_profile)) i).
Proof. exact: (exec_seat_endpointE (abel_exec_endpoints s w0) i). Qed.

(** abel_shuffle_seat_endpointE — one seat of the identity-content run sees
    the card its start was moved to, and no more. *)
Lemma abel_shuffle_seat_endpointE (x : unit) (w0 : pgg_gT abel_M)
    (i : 'I_(pi_T' (mp_PI abel_profile)).+1) :
  @exec_seat_endpoint abel_profile abel_shuffle_plug x w0 0 i
  = abel_id_obs x (w0, tnth (pi_starts (mp_PI abel_profile)) i).
Proof. exact: (exec_seat_endpointE (abel_shuffle_endpoints x w0) i). Qed.

(** abel_exec_coalition_endpointsE — a coalition of seats sees the shares on
    the cards its own starts were moved to, and a fixed default at every seat
    outside it.  The default is what makes the coalition view a total function
    while still holding nothing about the seats the coalition does not
    occupy. *)
Lemma abel_exec_coalition_endpointsE (s : 'I_4) (w0 : pgg_gT abel_M)
    (C : {set 'I_(pi_T' (mp_PI abel_profile)).+1}) :
  @exec_coalition_endpoints abel_profile abel_exec_plug s w0 0 C
  = [ffun i => if i \in C
               then abel_content_obs s
                      (w0, tnth (pi_starts (mp_PI abel_profile)) i)
               else ord0].
Proof. exact: (exec_coalition_endpointsE (abel_exec_endpoints s w0) C). Qed.

(** abel_exec_verifier_traceE — the verifier's row of the secret-recovery run
    is row 1 of the interpreter output.  The row is a list of messages, which
    is a navigation aid and not a finite random variable, so no distance or
    entropy statement can be attached to it. *)
Lemma abel_exec_verifier_traceE (s : 'I_4) (w0 : pgg_gT abel_M) :
  @exec_verifier_trace abel_profile abel_exec_plug s w0 0
  = nth [::] (@exec_run abel_profile abel_exec_plug s w0 0).2 1.
Proof. by []. Qed.

(** abel_exec_raw_traceE — seat i's row of the secret-recovery run is row
    2 + i of the interpreter output, the dealer and verifier occupying the
    first two.  The row is a list of messages, a navigation aid and not a
    finite random variable. *)
Lemma abel_exec_raw_traceE (s : 'I_4) (w0 : pgg_gT abel_M)
    (i : 'I_(pi_T' (mp_PI abel_profile)).+1) :
  @exec_participant_trace abel_profile abel_exec_plug s w0 0 i
  = nth [::] (@exec_run abel_profile abel_exec_plug s w0 0).2 (2 + i).
Proof. by []. Qed.

(** abel_shuffle_verifier_traceE — the verifier's row of the identity-content
    run is row 1 of the interpreter output.  The row is a list of messages, a
    navigation aid and not a finite random variable. *)
Lemma abel_shuffle_verifier_traceE (x : unit) (w0 : pgg_gT abel_M) :
  @exec_verifier_trace abel_profile abel_shuffle_plug x w0 0
  = nth [::] (@exec_run abel_profile abel_shuffle_plug x w0 0).2 1.
Proof. by []. Qed.

(** abel_shuffle_raw_traceE — seat i's row of the identity-content run is row
    2 + i of the interpreter output.  The row is a list of messages, a
    navigation aid and not a finite random variable. *)
Lemma abel_shuffle_raw_traceE (x : unit) (w0 : pgg_gT abel_M)
    (i : 'I_(pi_T' (mp_PI abel_profile)).+1) :
  @exec_participant_trace abel_profile abel_shuffle_plug x w0 0 i
  = nth [::] (@exec_run abel_profile abel_shuffle_plug x w0 0).2 (2 + i).
Proof. by []. Qed.

(** abel_seat_countE — the profile seats four players.  It is the number the
    seat/share bridge of both plugs rests on, four seats meeting the four
    shares of the sum-mod scheme. *)
Lemma abel_seat_countE : (pi_T' (mp_PI abel_profile)).+1 = 4.
Proof. by []. Qed.
