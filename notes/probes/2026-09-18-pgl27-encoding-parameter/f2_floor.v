(* Premise check for ruling T1. After the delta-unfolding proofs landed, the
   two pgl27_r7_* trace bridges still print the three boolp axioms. This probe
   asks whether that triple is the floor of any statement mentioning the
   sampler pgl27P, in which case no proof route could have removed it. Both
   lemmas below are closed by reflexivity and cite nothing. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba entropy.
From pgg_smc Require Import pgl27_secrecy pgl27_encoding pgl27_encoding_r7.
From pgg_smc Require Import pgl27_trace_encoding.

Lemma f2_floor_sampler (R : realType) : pgl27P R = pgl27P R.
Proof. by []. Qed.

Print Assumptions f2_floor_sampler.

Lemma f2_floor_trace (R : realType) (i : 'I_8) :
  pgl27_enc_player_trace R pgl27_encoding_r7 i
  = pgl27_enc_player_trace R pgl27_encoding_r7 i.
Proof. by []. Qed.

Print Assumptions f2_floor_trace.
