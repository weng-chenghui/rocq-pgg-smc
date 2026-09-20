(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* r_marginals: the two one-position marginal bounds of the tree, stated as   *)
(* what they are                                                             *)
(*                                                                            *)
(* PROBE FILE. Nothing permanent requires it. Ledger row R8 of                *)
(* notes/20260920-readers-and-marginal-bounds-probe-design.md.                *)
(*                                                                            *)
(* Two theorems of the tree compare one position's law with one named ideal   *)
(* law. Neither mentions a coalition, a second run argument or a secret, so   *)
(* neither is evidence for any of the three security properties, and neither  *)
(* is restated here as one. They are instances of two propositions of their   *)
(* own, and the two propositions differ in which law is compared: the five-   *)
(* seat instance compares one seat's executed reading, the five-card instance *)
(* one position of the cut.                                                   *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.
From pgg_smc Require Import s5_profile s5_run s5_mixing s5_exec s5_models.
From pgg_smc Require Import five_card_group five_card_program five_card_kim.
From pgg_smc Require Import five_card_exec five_card_models five_card_mixing.
From pgg_smc Require Import five_card_tableau_sampled.
From readersprobe Require Import r_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.


(******************************************************************************)
(*     The five-seat instance: one seat's executed reading                    *)
(******************************************************************************)

(* One seat's executed reading under the finite-word model sits within
   sqrt 5 times alpha to the L of the encoder-image law, as a one-seat
   marginal bound. The ideal law is neither uniform nor independent of the
   secret, so the number bounds the distance to a named law and no coalition,
   privacy or secrecy conclusion follows from it. *)
Theorem s5_exec_endpoint_bound_as_marginal (R : realType)
    (secretP : R.-fdist 'I_5) (L : nat)
    (i : 'I_(pi_T' (mp_PI (instance_profile s5_algebra))).+1) :
  @SeatMarginalPropAt R s5_algebra s5_dealt_params
    (s5_word_sample secretP L) i (s5_ideal_reading secretP)
    (Num.sqrt 5%:R * (s5_alpha_R R) ^+ L).
Proof. exact: (s5_exec_endpoint_bound secretP L i). Qed.


(******************************************************************************)
(*     The five-card instance: one position of the cut                        *)
(******************************************************************************)

(* One starting position's marginal of the repeated-cut model's own cut law
   sits within 2^-40 of the uniform law, as a one-position marginal bound on
   the cut. The reading is a function of the shuffle alone: it is the position
   the cut sends one starting position to, and not what any seat holds, so
   this states less than the five-seat bound above and again nothing about a
   coalition. *)
Theorem five_card_repeated_endpoint_as_marginal (R : realType) (s : 'I_5) :
  @CutMarginalPropAt R five_card_algebra five_card_params
    (amf_sample kim_centi_family R tt) _
    (fun sigma : {perm 'I_5} => sigma s) (fdist_uniform (card_ord 5))
    (2%:R^-40).
Proof.
exact: (Order.POrderTheory.ltW (five_card_repeated_endpoint_lt R s)).
Qed.


(******************************************************************************)
(*     Neither definition covers the other                                    *)
(******************************************************************************)

(* The five-card bound is refused in the seat form. The seat form compares the
   law of what a seat holds, a card value read through the instance's encoder,
   and the five-card bound compares the law of a position of the shuffle, so
   the two propositions are about two different readings of one run. *)
Fail Check (fun (R : realType) (s : 'I_5) =>
  (five_card_repeated_endpoint_as_marginal R s
     : @SeatMarginalPropAt R five_card_algebra five_card_params
         (amf_sample kim_centi_family R tt) s (fdist_uniform (card_ord 5))
         (2%:R^-40))).
