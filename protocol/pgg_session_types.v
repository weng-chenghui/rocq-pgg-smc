(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism.
From pgg_smc Require Import smc_session_types.
Require Import pgg_interface.

(******************************************************************************)
(* PGG: Session-Typed Wrappers                                                *)
(*                                                                            *)
(* Session-typed wrappers for the PGG protocol, following the pattern         *)
(* of dsdp_session_types.v. Each action variant has a fixed dtype.            *)
(*                                                                            *)
(*   PGGReveal_pos dst i p    == reveal card position i (DT_Sheet)             *)
(*   PGGDeal_hand dst s p     == deal hand s to player (DT_Hand)               *)
(*   PGGAnnounce_idx dst k p  == announce selection index k (DT_Idx)           *)
(*   PGGObserve_pos src f     == observe card position, extract 'I_N, apply f  *)
(*   PGGReceive_hand src f    == receive dealt hand, extract seq 'I_N, apply f *)
(*   PGGReceive_idx src f     == receive announcement, extract nat, apply f    *)
(*   PGGInit x p              == store local data x, continue with p           *)
(*   PGGRet x                 == return data x                                 *)
(*   PGGFinish                == terminal state                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section pgg_session_wrappers.

Variable M : MonodromyReprType.

Let N := (pgg_N' M).+1.
Let data := pgg_data N.

(* Types the dealer's reveal move: sending a card position as a DT_Sheet
   payload. The session environment records the send, so the party at the
   other end of dst is statically committed to a matching receive of the
   same shape before either process can close. *)
Definition PGGReveal_pos {party n env} (dst : nat) (i : 'I_N)
    (p : @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_send env dst DT_Sheet) :=
  SSend dst DT_Sheet (PGG_sheet i) p.

(* Types the dealer's deal move: sending a whole hand of card positions as a
   DT_Hand payload, distinct in the session environment from a send of a
   single card position, so a hand can never be mistaken for a lone
   revealed card at type-checking time. *)
Definition PGGDeal_hand {party n env} (dst : nat) (s : seq ('I_N))
    (p : @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_send env dst DT_Hand) :=
  SSend dst DT_Hand (PGG_hand s) p.

(* Types the dealer's shuffle-selection move: sending the chosen word index
   as a DT_Idx payload, the third and last session-typed alphabet letter, so
   the three protocol moves (card position, hand, index) stay mutually
   distinguishable in every session environment they appear in. *)
Definition PGGAnnounce_idx {party n env} (dst : nat) (k : nat)
    (p : @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_send env dst DT_Idx) :=
  SSend dst DT_Idx (@PGG_idx N k) p.

(* Types the verifier's observe move: receiving a DT_Sheet payload and
   continuing with the extracted card position, failing closed on a
   malformed payload. The session discipline guarantees this receive is
   matched by exactly one PGGReveal_pos on the sender's side. *)
Definition PGGObserve_pos {party n env} (src : nat)
    (f : 'I_N -> @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_recv env src DT_Sheet) :=
  SRecv src DT_Sheet (fun d =>
    match from_sheet d with
    | Some i => f i
    | None => SFail
    end).

(* Types a player's receive-hand move: receiving a DT_Hand payload and
   continuing with the extracted card sequence, failing closed on a
   malformed payload. The session discipline guarantees this is matched by
   the dealer's PGGDeal_hand and no other send. *)
Definition PGGReceive_hand {party n env} (src : nat)
    (f : seq ('I_N) -> @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_recv env src DT_Hand) :=
  SRecv src DT_Hand (fun d =>
    match from_hand d with
    | Some s => f s
    | None => SFail
    end).

(* Types a player's receive-announcement move: receiving a DT_Idx payload
   and continuing with the extracted index, failing closed on a malformed
   payload. The session discipline guarantees this is matched by the
   dealer's PGGAnnounce_idx and no other send. *)
Definition PGGReceive_idx {party n env} (src : nat)
    (f : nat -> @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 (senv_recv env src DT_Idx) :=
  SRecv src DT_Idx (fun d =>
    match from_idx d with
    | Some k => f k
    | None => SFail
    end).

(* Types a purely local step: storing data x for a process's own later use
   without touching the session environment, since no message crosses a
   process boundary. *)
Definition PGGInit {party n env} (x : data) (p : @sproc pgg_dtype data party n env)
    : @sproc pgg_dtype data party n.+1 env :=
  SInit x p.

(* Types a process's final return of data x under the empty session
   environment: every send this process owed has already been matched, so
   nothing remains to type-check downstream of it. *)
Definition PGGRet {party : nat} (x : data)
    : @sproc pgg_dtype data party 2 senv_end :=
  SRet x.

(* Types the terminal state under the empty session environment with no
   returned data, the shape every PGG protocol program closes with once its
   session obligations are discharged. *)
Definition PGGFinish {party : nat}
    : @sproc pgg_dtype data party 1 senv_end :=
  SFinish.

End pgg_session_wrappers.

Arguments PGGReveal_pos {M party n env}.
Arguments PGGDeal_hand {M party n env}.
Arguments PGGAnnounce_idx {M party n env}.
Arguments PGGObserve_pos {M party n env}.
Arguments PGGReceive_hand {M party n env}.
Arguments PGGReceive_idx {M party n env}.
Arguments PGGInit {M party n env}.
Arguments PGGRet {M party}.
Arguments PGGFinish {M party}.
