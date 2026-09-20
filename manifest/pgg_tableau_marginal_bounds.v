(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgg_tableau_marginal_bounds: one seat's law and one position's law         *)
(*                              against a named ideal                         *)
(*                                                                            *)
(* Two propositions compare one law a model gives with one law that is named  *)
(* beside it. The seat form compares the law of one seat's executed endpoint; *)
(* the cut form compares the law of one finite function of the model's cut.   *)
(* Neither mentions a coalition, a second run argument or a secret, so        *)
(* neither is one of the three propositions the security evidence proves.     *)
(*                                                                            *)
(* Both numbers bound a sum of absolute differences, twice the total          *)
(* variation distance of the literature, so a distinguisher's advantage       *)
(* against the compared pair is at most half of the number. Two is the        *)
(* largest such sum on a finite carrier, so a marginal bound at two holds of  *)
(* every model and every ideal and says nothing: a published number says      *)
(* something exactly in so far as it is below two.                            *)
(*                                                                            *)
(* It does not require manifest/pgg_tableau_reading.v: a marginal bound is    *)
(* not a statement at a reading, the seat form reading one seat and the cut   *)
(* form one position of the shuffle.                                          *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   SeatMarginalPropAt         == one seat's executed endpoint law is        *)
(*                                 within c of a named ideal law              *)
(*   CutMarginalPropAt          == one finite function of the cut has a law   *)
(*                                 within c of a named ideal law              *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   seat_marginal_prop_at2     == every model and ideal satisfy the seat     *)
(*                                 form at two                                *)
(*   cut_marginal_prop_at2      == the same at the cut form                   *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import var_dist_supp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     One seat's law and one position's law against a named ideal            *)
(******************************************************************************)

Section marginal_bounds.

Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.

(* A one-seat marginal bound: the law of seat i's executed endpoint, at the
   selection index zero every statement of the framework fixes, the single
   entry of the run's one-element deck and so the cut itself, is within c of a
   named ideal law. It mentions no coalition, no second run argument and no
   secret, so it is not a statement about what an adversary distinguishes; it
   compares one model's one-seat law with one named law and says nothing more.
   The number bounds a sum of absolute differences, twice the total variation
   distance of the literature. *)
Definition SeatMarginalPropAt (i : seats)
    (ideal : R.-fdist 'I_(pgg_N' (mp_M (instance_profile A))).+1) (c : R)
    : Prop :=
  var_dist (@sa_seat_dist R (instance_profile A) (instance_exec E) sa 0 i)
           ideal
  <= c.

(* A one-position marginal bound on the cut: the law of one finite function of
   the model's cut is within c of a named ideal law. That function is of the
   shuffle alone and not of the run argument, so it speaks of the model's
   randomness and not of what any seat sees. Like the seat form it mentions no
   coalition, no second run argument and no secret, and its number is a sum of
   absolute differences. *)
Definition CutMarginalPropAt (T : finType)
    (read : pgg_gT (mp_M (instance_profile A)) -> T)
    (ideal : R.-fdist T) (c : R) : Prop :=
  var_dist (fdistmap read (sa_cut_dist sa)) ideal <= c.


(******************************************************************************)
(*     The scale a marginal bound is read against                             *)
(******************************************************************************)

(* Every model and every ideal law satisfy the one-seat marginal bound at two,
   a sum of absolute differences between two laws on a finite carrier never
   exceeding two. The number a one-seat marginal bound publishes is therefore
   the whole of what it says, and a bound at or above two rules nothing out. *)
Lemma seat_marginal_prop_at2 (i : seats)
    (ideal : R.-fdist 'I_(pgg_N' (mp_M (instance_profile A))).+1) :
  SeatMarginalPropAt i ideal 2%:R.
Proof. exact: var_dist_le2. Qed.

(* The same at the cut form, for the same reason and at the same scale. *)
Lemma cut_marginal_prop_at2 (T : finType)
    (read : pgg_gT (mp_M (instance_profile A)) -> T) (ideal : R.-fdist T) :
  CutMarginalPropAt read ideal 2%:R.
Proof. exact: var_dist_le2. Qed.

End marginal_bounds.

Arguments SeatMarginalPropAt {R A E} sa i ideal c.
Arguments CutMarginalPropAt {R A E} sa {T} read ideal c.
Arguments seat_marginal_prop_at2 {R A E} sa i ideal.
Arguments cut_marginal_prop_at2 {R A E} sa {T} read ideal.
