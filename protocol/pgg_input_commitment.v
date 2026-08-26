(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
Require Import pgg_interface pgg_session_types card_exchange_pismc.

(******************************************************************************)
(* PGG: Input-Commitment Stage                                                *)
(*                                                                            *)
(* A pre-protocol stage in which M input parties each commit one card value   *)
(* (a position in 'I_N) to the dealer before the dealing phase begins. The    *)
(* committed values are assembled into the dealer's word table and the        *)
(* unchanged exchange_dealer body runs as before; players and the verifier    *)
(* see exactly the same wire as without the prologue.                         *)
(*                                                                            *)
(* The den Boer commit primitives FCCommit/FCRecvCommit are typed over       *)
(* fc_dtype/fc_data, a different session alphabet from pgg_dtype/pgg_data,    *)
(* so they cannot be reused here. The wrappers below are built directly       *)
(* over pgg_dtype/pgg_data instead, with the committed payload reusing        *)
(* PGG_sheet, so the dealer/player/verifier wire of the dealing phase is      *)
(* unchanged and only the dealer gains a prologue.                            *)
(*                                                                            *)
(*   pgg_commit i v               == input party i sends PGG_sheet v to       *)
(*                                   the dealer, then finishes                 *)
(*   pgg_recv_commit from         == dealer receives one PGG_sheet from        *)
(*                                   [from], then finishes (dual of commit)    *)
(*   pgg_commit_prologue cont acc inputs                                       *)
(*                                == dealer receives one PGG_sheet from each    *)
(*                                   party in [inputs], accumulating the        *)
(*                                   committed values, then runs cont          *)
(*   exchange_dealer_with_commit PI inputs assemble content players P_idx      *)
(*                                == the dealer prologue (one recv per input    *)
(*                                   party) followed by the existing            *)
(*                                   exchange_dealer body, with the word table  *)
(*                                   built from the committed values           *)
(*                                                                            *)
(* The empty prologue degenerates definitionally to the plain dealer          *)
(* (exchange_dealer_with_commit_nil), so the position-model instances that     *)
(* take no committed inputs are unaffected.                                   *)
(*                                                                            *)
(* Session-type duality between the committed dealer and every counterpart     *)
(* (each input party, every player, the verifier) is verified by              *)
(* native_compute for a concrete two-input instance in the idealized section. *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section pgg_input_commitment.

Variable M : MonodromyReprType.

Let N := (pgg_N' M).+1.
Let data := pgg_data N.

(* Types an input party's commit send: deliver one card value as a PGG_sheet
   to the dealer, then finish. The payload reuses PGG_sheet rather than a
   dedicated commit tag, so the committed value enters the protocol through
   the same session alphabet the dealing phase already uses. *)
Definition pgg_commit (i : nat) (v : 'I_N)
    : @sproc pgg_dtype data i 2 (senv_send senv_end dealer_idx DT_Sheet) :=
  SSend dealer_idx DT_Sheet (PGG_sheet v) SFinish.

(* Types the dealer's standalone single-party commit receive: receive one
   PGG_sheet from party [from], failing closed on a malformed payload, then
   finish. This is the session dual of pgg_commit, checked independently of
   the prologue so the commit/recv pair is certified well typed before being
   threaded into the multi-party prologue below. *)
Definition pgg_recv_commit (from : nat)
    : @sproc pgg_dtype data dealer_idx 2 (senv_recv senv_end from DT_Sheet) :=
  SRecv from DT_Sheet (fun d =>
    match from_sheet d with
    | Some _ => SFinish
    | None => SFail
    end).

(* Types the dealer's commit-collection prologue: receive one PGG_sheet from
   each party in [inputs] in order, accumulate the committed values, then
   hand the collected list to the continuation. The dealing-phase body
   exchange_dealer has a fixed session type of its own, so this prologue
   prepends one senv_recv layer per input party ahead of it, threading the
   dependent session environment by computation on the length of [inputs]
   rather than by a separate proof obligation. *)
Fixpoint pgg_commit_prologue {dn : nat} {denv : senv pgg_dtype}
    (cont : seq 'I_N -> @sproc pgg_dtype data dealer_idx dn denv)
    (acc : seq 'I_N) (inputs : seq nat) {struct inputs}
    : @sproc pgg_dtype data dealer_idx
        (iter (size inputs) succn dn)
        (fold_senv (fun from e => senv_recv e from DT_Sheet) inputs denv) :=
  match inputs return
    @sproc pgg_dtype data dealer_idx
      (iter (size inputs) succn dn)
      (fold_senv (fun from e => senv_recv e from DT_Sheet) inputs denv)
  with
  | [::] => cont acc
  | from :: rest =>
      SRecv from DT_Sheet (fun d =>
        match from_sheet d with
        | Some v => pgg_commit_prologue cont (acc ++ [:: v]) rest
        | None => SFail
        end)
  end.

(* Types the dealer program with an input-commitment prologue: collect one
   committed card value from each party in [inputs] via pgg_commit_prologue,
   assemble them into the word table via [assemble], then run the existing
   dealing body exchange_dealer unchanged. Routing committed inputs through
   the prologue rather than through the dealing body itself is what keeps
   the dealer/player/verifier wire of the dealing phase identical to the
   uncommitted protocol; the prologue is the only addition. *)
Definition exchange_dealer_with_commit
    (PI : PGGInterface M) (inputs : seq nat)
    (assemble : seq 'I_N -> seq (pgg_gT M))
    (content : 'I_N -> 'I_N)
    (players : seq 'I_(pi_T' PI).+1) (P_idx : nat)
    : @sproc pgg_dtype data dealer_idx _ _ :=
  pgg_commit_prologue
    (fun committed => exchange_dealer PI content players (assemble committed) P_idx)
    [::] inputs.

(* With no input parties, the committed dealer degenerates by computation
   (pgg_commit_prologue matching on [::]) to the plain exchange_dealer on
   the word table assembled from the empty list. Position-model instances
   commit no inputs, so this equation is what lets them keep the unchanged
   dealing program and every duality proof already established for it. *)
Lemma exchange_dealer_with_commit_nil
    (PI : PGGInterface M)
    (assemble : seq 'I_N -> seq (pgg_gT M))
    (content : 'I_N -> 'I_N)
    (players : seq 'I_(pi_T' PI).+1) (P_idx : nat) :
  exchange_dealer_with_commit [::] assemble content players P_idx
  = exchange_dealer PI content players (assemble [::]) P_idx.
Proof. by []. Qed.

End pgg_input_commitment.

Arguments pgg_commit {M}.
Arguments pgg_recv_commit {M}.
Arguments pgg_commit_prologue {M dn denv}.
Arguments exchange_dealer_with_commit {M} PI.

(******************************************************************************)
(** * Two-Input Duality Verification (Idealized)                              *)
(*                                                                            *)
(* Concrete check that the dealer-with-commit prologue is dual to each input  *)
(* party's commit AND that the dealing phase stays dual to every player and   *)
(* the verifier. Reuses the idealized fully symmetric S_N instance from        *)
(* card_exchange_pismc.v (two players, T = 2). Two input parties commit at     *)
(* process ids 4 and 5 (above dealer 0, verifier 1, players 2 and 3).         *)
(******************************************************************************)

Section pgg_commit_idealized_duality.

Variable n : nat.
Let N := n.+2.
Let M := Idealized_MonodromyRepr n.
Let PI := Test_PGG_2 n.
Let data := pgg_data (pgg_N' M).+1.

(* Concrete player list for the T = 2 idealized instance *)
Let players_2 : seq 'I_2 :=
  [:: @Ordinal 2 0 isT; @Ordinal 2 1 isT].

(* The two input parties commit at process ids 4 and 5 *)
Let input_ids : seq nat := [:: 4; 5].

Variables (W : seq {perm 'I_N}) (P_idx : nat).

Local Open Scope sproc_scope.

(* The two-input committed dealer, wrapped as an aproc for the duality check
   below. The assemble map is held constant, since committed values change
   only the word payloads the dealer sends and never the dealing-phase
   session type, so this instance exercises the prologue's session
   structure without needing a nonconstant word assembly. *)
Definition ap_dealer_commit_2 :=
  mk_aproc (exchange_dealer_with_commit PI input_ids
    (fun _ => W) id players_2 P_idx).

(* Input party 0, at process id 4, wrapped as an aproc for the duality
   checks below. *)
Definition ap_input0_commit :=
  mk_aproc (pgg_commit 4 (@Ordinal (pgg_N' M).+1 0 isT)).

(* Input party 1, at process id 5, wrapped as an aproc for the duality
   checks below. *)
Definition ap_input1_commit :=
  mk_aproc (pgg_commit 5 (@Ordinal (pgg_N' M).+1 0 isT)).

(* The dealer's standalone single-commit receive from party 4, wrapped as an
   aproc for the duality check below. *)
Definition ap_recv_commit_2 := mk_aproc (@pgg_recv_commit M 4).

(* pgg_commit and pgg_recv_commit are session duals independently of the
   prologue: this certifies the commit/recv pair is well typed on its own
   before the prologue's use of pgg_commit_prologue is trusted to compose
   several such pairs correctly. *)
Lemma commit_recv_dual_2 : channels_dual ap_recv_commit_2 ap_input0_commit.
Proof. by native_compute. Qed.

(* The committed dealer's first prologue receive is dual to input party 0's
   commit send: the dependent session-environment threading through
   pgg_commit_prologue, discharged by native computation on a concrete
   two-input instance. *)
Lemma dealer_commit_input0_dual_2 :
  channels_dual ap_dealer_commit_2 ap_input0_commit.
Proof. by native_compute. Qed.

(* The committed dealer's second prologue receive is dual to input party 1's
   commit send, the second link in the same dependent-senv chain. *)
Lemma dealer_commit_input1_dual_2 :
  channels_dual ap_dealer_commit_2 ap_input1_commit.
Proof. by native_compute. Qed.

(* The committed dealer stays dual to player 0 after the prologue is
   prepended: the prologue only adds receives ahead of the dealing-phase
   sends, so the dealer's session with each player is unaffected. *)
Lemma dealer_commit_player0_dual_2 :
  channels_dual ap_dealer_commit_2 (ap_player0_2 n).
Proof. by native_compute. Qed.

(* The committed dealer stays dual to player 1, the second player-side
   instance of the same unaffected-dealing-phase fact. *)
Lemma dealer_commit_player1_dual_2 :
  channels_dual ap_dealer_commit_2 (ap_player1_2 n).
Proof. by native_compute. Qed.

(* The committed dealer stays dual to the verifier, completing the check
   that the commit prologue leaves every non-input counterpart's session
   unaffected. *)
Lemma dealer_commit_verifier_dual_2 :
  channels_dual ap_dealer_commit_2 (ap_verifier_2 n).
Proof. by native_compute. Qed.

End pgg_commit_idealized_duality.

