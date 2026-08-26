(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* kim executed-trace secrecy (instance of the executed-trace bridge).        *)
(* kim_procs is den_boer_procs definitionally and the kim instance shares the *)
(* five-card leakage space, so kim's executed trace is den Boer's executed    *)
(* trace and the single-card colour view is the same. kim's independence fact *)
(* kim_indep feeds the same trace_secrecy_of_view bridge with the             *)
(* encode_bool/decode_bool codec to obtain single-player trace secrecy.       *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg boolp reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
Require Import pgg_interface.
From pgg_smc Require Import five_card_group five_card_program five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment pgg_run.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme input_encoding.
From pgg_smc Require Import five_card_leakage kim_secrecy denboer_trace.
From pgg_smc Require Import pgg_leakage_witness pgg_trace_secrecy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section kim_trace_sec.
Variable R : realType.

(* kim_player_trace is denboer_player_trace R: Kim's family shares
   FiveCardKim_M and the five-card layout with den Boer, so the two
   instances trace the same executed random variable and every den Boer
   trace fact transfers to Kim without a new proof. *)
Definition kim_player_trace := denboer_player_trace R.

(* A single corrupted player's executed Kim trace leaves the secret's
   conditional entropy equal to its unconditional entropy: trace-level
   secrecy, strictly stronger than the single-card view secrecy of
   kim_secrecy.v. The proof reuses den Boer's trace_secrecy_of_view bridge,
   instantiated with Kim's independence fact kim_indep in place of
   den Boer's. *)
Lemma kim_trace_secrecy :
  `H( Secret R | kim_player_trace ord0 ) = `H `p_ (Secret R).
Proof.
apply: (trace_secrecy_of_view (view := (@thead 0 bool) `o (ViewA R [:: 0%N]))
          (trace_of := encode_bool) (view_of := decode_bool)).
- exact: denboer_player_trace_ok R ord0.
- exact: decode_encode_bool.
- exact: (inde_RV_comp (@thead 0 bool) (kim_indep R)).
Qed.

End kim_trace_sec.
