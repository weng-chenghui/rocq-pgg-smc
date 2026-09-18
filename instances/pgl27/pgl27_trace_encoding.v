(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_trace_encoding: the executed trace of the eight-card run at a deck   *)
(*                       pair                                                 *)
(*                                                                            *)
(* pgl27_trace.v builds the executed trace of the run that deals the orbit    *)
(* encoder, and pgl27_encoding.v makes the deck pair a parameter. This file   *)
(* joins the two: it runs the same ten-process program on the deck that an    *)
(* arbitrary deck pair deals to the sampled secret, and identifies what the   *)
(* run leaves in the coalition's trace with the coalition view the leakage    *)
(* theorems are stated about.                                                 *)
(*                                                                            *)
(* The identification is what makes a leakage value a statement about an      *)
(* execution. The coalition view is defined from the deck and the shuffle     *)
(* directly, without reference to the protocol; the coalition trace is what   *)
(* the interpreter actually writes at the eight player processes. They are    *)
(* equal as random variables on the joint secret-and-shuffle sampler, so      *)
(* every mutual information proved about the view is the mutual information   *)
(* between the secret and what the coalition observes when the program runs.  *)
(*                                                                            *)
(* Deck validity enters nowhere in that identification: the seat equality,    *)
(* the full-trace shape and the coalition equality hold at every deck pair    *)
(* and at every deck. It enters at the privacy statement, where distinctness  *)
(* of the eight cards is what sharp 3-transitivity of PGL(2,7) needs, and at  *)
(* class recovery, where the decoder must return the secret the deck was      *)
(* dealt for.                                                                 *)
(*                                                                            *)
(* At the deck pair the scheme deals (pgl27_encoding_r5.v) the definitions    *)
(* below are the pgl27_trace.v ones, so the executed-trace results of the two *)
(* files are results about one object.                                        *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_enc_player_trace R e i    == seat i executed-trace content of the  *)
(*                                      run dealing the deck of e             *)
(*   pgl27_enc_coalition_trace R e C == the coalition joint executed trace    *)
(*                                      of that run                           *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_enc_player_traceE == seat i sees the card the deck puts at its     *)
(*     cut-permuted position                                                  *)
(*   pgl27_enc_player_trace_full == the whole seat trace is the index marker  *)
(*     and a one-card hand                                                    *)
(*   pgl27_enc_coalition_traceE == the coalition executed trace is the        *)
(*     coalition view                                                         *)
(*   pgl27_enc_coalition_trace_secrecy == a coalition of at most three seats  *)
(*     learns nothing about the secret from its executed trace                *)
(*   pgl27_enc_endpoints_size == the run collects eight endpoints at the      *)
(*     verifier, the arity the decoder reads                                  *)
(*   pgl27_enc_run_recovers_class == the run recovers the dealt secret from   *)
(*     the verifier's endpoints                                               *)
(*   pgl27_enc_run_terminates == every process of that run reaches Finish     *)
(*   pgl27_aprocs_abs_terminates == every process of the run over an          *)
(*     abstract card readout reaches Finish                                   *)
(*   pgl27_r5_player_traceE, pgl27_r5_coalition_traceE == at the deck pair    *)
(*     the scheme deals these are the traces of pgl27_trace.v                 *)
(*                                                                            *)
(* The statements concern the pre-reveal execution: after the public reveal   *)
(* every player learns the secret by design.                                  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
Require Import pgg_interface.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment pgg_run.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_reconstruct Require Import covering_scheme pgg_sharing_framework.
From pgg_reconstruct Require Import transitivity_privacy.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme pgl27_profile.
From pgg_smc Require Import pgl27_run pgl27_secrecy pgl27_trace.
From pgg_smc Require Import pgg_trace_secrecy.
From pgg_smc Require Import pgl27_encoding pgl27_encoding_r5.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section pgl27_trace_encoding.
Variable R : realType.
Variable e : pgl27_encoding.

(** pgl27_enc_player_trace — seat i's executed-trace content in the run that
    deals the deck the pair e assigns to the sampled secret, at the sampled
    shuffle. It is the single-seat observable of an execution, read off the
    interpreter's own output at process index 2 + i. *)
Definition pgl27_enc_player_trace (i : 'I_8) : {RV (pgl27P R) -> 'I_8} :=
  fun u =>
    content_of
      (nth [::] (run_interp pgl27_fuel
                   (pgl27_procs_deck (enc_deck e u.1) u.2)).2 (2 + i)).

(** pgl27_enc_player_traceE — seat i's executed-trace content is the card the
    dealt deck holds at the cut-permuted position of seat i. The shuffle
    reaches a seat only through that position, so the deck pair and the cut
    together fix what the seat reads, at every deck pair. *)
Lemma pgl27_enc_player_traceE (i : 'I_8) :
  pgl27_enc_player_trace i
  = (fun u => tnth (enc_deck e u.1) (@pgg_rho pgl27_M u.2 i)).
Proof.
apply: boolp.funext => u.
rewrite /pgl27_enc_player_trace pgl27_procs_deck_abs.
case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi.
- rewrite (pgl27_abs_p0 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc_deck e u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p1 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc_deck e u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p2 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc_deck e u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p3 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc_deck e u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p4 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc_deck e u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p5 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc_deck e u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p6 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc_deck e u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p7 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc_deck e u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
Qed.

(** pgl27_enc_player_trace_full — the whole executed trace of seat i is the
    index marker and the one-card hand holding its dealt card. The seat's
    trace carries no residue of the shuffle beyond that card, which is why
    projecting it to its content loses nothing a coalition could use. *)
Lemma pgl27_enc_player_trace_full (i : 'I_8)
    (u : bool * pgg_gT pgl27_M) :
  nth [::] (run_interp pgl27_fuel
              (pgl27_procs_deck (enc_deck e u.1) u.2)).2 (2 + i)
  = [:: PGG_idx 0; PGG_hand [:: pgl27_enc_player_trace i u]].
Proof.
rewrite pgl27_procs_deck_abs pgl27_enc_player_traceE.
case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi.
- have -> : (@Ordinal 8 0 Hi) = (@Ordinal 8 0 isT) by apply: val_inj.
  by rewrite (pgl27_full_p0 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 1 Hi) = (@Ordinal 8 1 isT) by apply: val_inj.
  by rewrite (pgl27_full_p1 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 2 Hi) = (@Ordinal 8 2 isT) by apply: val_inj.
  by rewrite (pgl27_full_p2 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 3 Hi) = (@Ordinal 8 3 isT) by apply: val_inj.
  by rewrite (pgl27_full_p3 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 4 Hi) = (@Ordinal 8 4 isT) by apply: val_inj.
  by rewrite (pgl27_full_p4 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 5 Hi) = (@Ordinal 8 5 isT) by apply: val_inj.
  by rewrite (pgl27_full_p5 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 6 Hi) = (@Ordinal 8 6 isT) by apply: val_inj.
  by rewrite (pgl27_full_p6 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 7 Hi) = (@Ordinal 8 7 isT) by apply: val_inj.
  by rewrite (pgl27_full_p7 (tnth (enc_deck e u.1)) u.2) tnth_ord_tuple.
Qed.

(** pgl27_enc_coalition_trace — the joint executed trace of a coalition C: the
    card each member observes in the run, and ord0 outside C. It is the
    coalition's whole pre-reveal knowledge at its seat processes, and it
    refuses to hold the shuffle that produced those cards. *)
Definition pgl27_enc_coalition_trace (C : {set 'I_8}) :
    {RV (pgl27P R) -> {ffun 'I_8 -> 'I_8}} :=
  fun u => [ffun i => if i \in C then pgl27_enc_player_trace i u else ord0].

(** pgl27_enc_coalition_traceE — the coalition's executed trace and the
    coalition view are the same random variable, at every deck pair. This is
    what makes every leakage value of the deck pair a value of the running
    protocol rather than of a separate model of it. *)
Lemma pgl27_enc_coalition_traceE (C : {set 'I_8}) :
  pgl27_enc_coalition_trace C = pgl27_enc_view R e C.
Proof.
apply: boolp.funext => u; apply/ffunP => i.
rewrite /pgl27_enc_coalition_trace /pgl27_enc_view /coalition_view !ffunE.
case: ifP => // _.
by rewrite (pgl27_enc_player_traceE i).
Qed.

(** pgl27_enc_coalition_trace_secrecy — a coalition of at most three seats
    leaves the secret's conditional entropy equal to its prior entropy. Three
    is the privacy threshold of the eight-card scheme at every deck pair, and
    the statement is about what the coalition reads out of an execution and
    not about a view defined outside the protocol. *)
Lemma pgl27_enc_coalition_trace_secrecy (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  `H( pgl27_secret R | pgl27_enc_coalition_trace C )
  = `H `p_ (pgl27_secret R).
Proof.
move=> HC.
apply: (trace_secrecy_of_view (view := pgl27_enc_view R e C)
          (trace_of := id) (view_of := id)).
- by rewrite pgl27_enc_coalition_traceE.
- by [].
- exact: pgl27_enc_view_indep.
Qed.

(* -------------------------------------------------------------------------- *)
(* The verifier's endpoints of the same run, and the dealt class.             *)
(* -------------------------------------------------------------------------- *)

(** pgl27_enc_endpoints_size — the run dealing the deck of e collects eight
    endpoints at the verifier. The count is the arity of the decoder, so it is
    what lets the endpoint list be read as a deck again. *)
Lemma pgl27_enc_endpoints_size (s : bool) (w0 : pgg_gT pgl27_M) :
  size (endpoints_of_trace
          (nth [::] (run_interp pgl27_fuel
                       (pgl27_procs_deck (enc_deck e s) w0)).2 1)) = 8.
Proof.
by rewrite pgl27_procs_deck_abs pgl27_aprocs_endpoints_size.
Qed.

(** pgl27_enc_run_recovers_class — the run dealing the deck that e assigns to
    the secret s recovers s from the verifier's endpoints, for every shuffle
    in the group. It is correctness of the scheme at the deck pair e, read off
    an execution: the decoder is invariant under the shuffle, so it returns
    the class of the dealt deck, which is s by the record's recovery field. *)
Lemma pgl27_enc_run_recovers_class (s : bool) (w0 : pgg_gT pgl27_M) :
  w0 \in pgg_G pgl27_M ->
  orbit_class (tcast (pgl27_enc_endpoints_size s w0)
     (in_tuple (endpoints_of_trace
        (nth [::] (run_interp pgl27_fuel
                     (pgl27_procs_deck (enc_deck e s) w0)).2 1)))) = s.
Proof.
move=> Hw0.
have Hgoal : forall (ep : seq 'I_(pgg_N' pgl27_M).+1) (H8 : size ep = 8),
    ep = [seq tnth (enc_deck e s)
              (@pgg_rho pgl27_M w0 (tnth (pi_starts pgl27_PI) i))
            | i <- enum 'I_(pi_T' pgl27_PI).+1] ->
    orbit_class (tcast H8 (in_tuple ep)) = s.
  move=> ep H8 Hep.
  have -> : tcast H8 (in_tuple ep)
          = [tuple tnth (enc_deck e s) (@pgg_rho pgl27_M w0 j) | j < 8].
    apply: eq_from_tnth => j.
    rewrite tcastE tnth_mktuple (tnth_nth ord0) /= Hep.
    rewrite (nth_map j) ?nth_ord_enum ?tnth_ord_tuple;
      last by rewrite size_enum_ord ltn_ord.
    by [].
  by rewrite (orbit_class_invariant w0 (enc_deck e s) Hw0) enc_classK.
apply: Hgoal.
by rewrite pgl27_procs_deck_abs pgl27_aprocs_endpoints.
Qed.

End pgl27_trace_encoding.

(* pgl27_aprocs_abs_terminates is encoding-free and would sit in pgl27_trace.v
   if that file were open for edit; it is proved here because it is not. *)

(* -------------------------------------------------------------------------- *)
(* Termination of the same run, at an abstract card readout.                  *)
(* -------------------------------------------------------------------------- *)

(** pgl27_aprocs_abs_terminates — every one of the ten processes of the run
    over an abstract card readout reaches Finish. The card values play no part
    in the control flow, so the run of every deck pair terminates, and the
    endpoint and trace statements above are statements about a completed
    execution. *)
Lemma pgl27_aprocs_abs_terminates (g : 'I_8 -> 'I_8)
    (w0 : pgg_gT pgl27_M) :
  (run_interp pgl27_fuel (pgl27_aprocs_abs g w0)).1 = nseq 10 Finish.
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(** pgl27_enc_run_terminates — the run dealing the deck that e assigns to the
    secret s terminates at every process. It is the abstract-readout statement
    read at one deck pair. *)
Lemma pgl27_enc_run_terminates (e : pgl27_encoding) (s : bool)
    (w0 : pgg_gT pgl27_M) :
  (run_interp pgl27_fuel (pgl27_procs_deck (enc_deck e s) w0)).1
  = nseq 10 Finish.
Proof.
by rewrite pgl27_procs_deck_abs pgl27_aprocs_abs_terminates.
Qed.

(* -------------------------------------------------------------------------- *)
(* The deck pair the scheme deals: the traces of pgl27_trace.v.               *)
(* -------------------------------------------------------------------------- *)

(** pgl27_r5_player_traceE — at the deck pair the scheme deals the seat trace
    above is the seat trace of pgl27_trace.v. The generic executed trace
    therefore extends the one the rest of the development runs instead of
    modelling it a second time. *)
Lemma pgl27_r5_player_traceE (R : realType) (i : 'I_8) :
  pgl27_enc_player_trace R pgl27_encoding_r5 i = pgl27_player_trace R i.
Proof.
by rewrite /pgl27_enc_player_trace /pgl27_player_trace.
Qed.

(** pgl27_r5_coalition_traceE — at the deck pair the scheme deals the
    coalition executed trace above is the coalition executed trace of
    pgl27_trace.v, the one the manifest pins. It is the bridge along which a
    leakage value of that pair is a value of the published run. *)
Lemma pgl27_r5_coalition_traceE (R : realType) (C : {set 'I_8}) :
  pgl27_enc_coalition_trace R pgl27_encoding_r5 C
  = pgl27_coalition_trace R C.
Proof.
by rewrite /pgl27_enc_coalition_trace /pgl27_coalition_trace
           /pgl27_enc_player_trace /pgl27_player_trace.
Qed.
