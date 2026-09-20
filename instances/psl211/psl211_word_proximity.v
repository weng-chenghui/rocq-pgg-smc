(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_word_proximity: how far the twelve-card word cut is from the        *)
(*                        uniform one                                         *)
(*                                                                            *)
(* The word model psl211_word_family names and the all-decks model of         *)
(* psl211_models.v run one execution over one sample space and differ in the  *)
(* law of the cut alone. This file measures that difference and nothing else: *)
(* it carries the bound the proximity arm of this instance takes as its       *)
(* distance field, and the two arithmetic facts about the number that field   *)
(* names. The certificate built on them, the program certified over it and    *)
(* the statements about that program are at AnalysisBridged,                  *)
(* in instances/psl211/tableau/.                                              *)
(*                                                                            *)
(* Every number below bounds a sum of absolute differences, which is twice    *)
(* the total variation distance of the literature, so a bound of 2^-40 here   *)
(* is a distinguishing advantage of at most 2^-41 wherever it is used.        *)
(*                                                                            *)
(* Six is the threshold the derived profile declares, and this bound is       *)
(* proved at every coalition of the twelve seats and not only below it, the   *)
(* threshold entering the arm's proposition and not the bound.                *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_word_proximity_close                                              *)
(*                              == the two models' joint laws of a            *)
(*                                 coalition's reading and the chirality are  *)
(*                                 within 2^-40                               *)
(*   psl211_pow2_40_ge1         == two to the fortieth is at least one        *)
(*   psl211_pow2_40_gt0         == two to the fortieth is positive            *)
(*   psl211_word_law_le2        == the two models' laws are within two, the   *)
(*                                 bound var_dist_le2 gives for any pair of   *)
(*                                 laws on one finite sample space            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import var_dist_supp var_dist_joint_law.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import psl211_group psl211_closure psl211_profile.
From pgg_smc Require Import psl211_mixing.
From pgg_smc Require Import psl211_exec psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_word_model.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(** seatT — a seat of the instance's starting interface, the index a coalition
    is a set of. *)
Local Notation seatT :=
  ('I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1).

(******************************************************************************)
(*     The distance between the two models' joint laws                        *)
(******************************************************************************)

(** At every coalition of the twelve seats, the joint law of
    that coalition's reading with the chirality under the 584-letter word
    shuffle is within 2^-40 of the same joint law under the uniform shuffle.
    It is the distance field of this instance's proximity certificate: the two
    models differ in the law of the cut alone, and the pair of a reading and
    the chirality is a deterministic function of the sample point, so the
    distance between the two cuts carries down to that pair unchanged. The
    claim is an average over the deck description and the cut. The bound holds
    at every coalition and not only below the threshold; the threshold enters
    the arm's proposition and not this distance. *)
Lemma psl211_word_proximity_close (R : realType) (C : {set seatT}) :
  (#|C| < profile_k (instance_profile psl211_algebra))%N ->
  var_dist
    (fdistmap (fun u => (@static_coalition_obs psl211_algebra
                           psl211_alldecks_params C
                           ((psl211_word_sample R).(sa_arg) u)
                           ((psl211_word_sample R).(sa_cut) u),
                         psl211_alldecks_secret R u))
       (sa_sampleP (psl211_word_sample R)))
    (fdistmap (fun u => (@static_coalition_obs psl211_algebra
                           psl211_alldecks_params C
                           ((psl211_alldecks_sample R).(sa_arg) u)
                           ((psl211_alldecks_sample R).(sa_cut) u),
                         psl211_alldecks_secret R u))
       (sa_sampleP (psl211_alldecks_sample R)))
  <= 2%:R^-40.
Proof.
(* The two maps are one term, the two adapters reading a sample point by the
   same two projections, so var_dist_fdistmap_pair applies with no pointwise
   rewriting of either reader. *)
move=> _.
apply: var_dist_fdistmap_pair.
rewrite psl211_word_sampleP_E psl211_alldecks_sampleP_E.
exact: psl211_word_law_le40.
Qed.

(******************************************************************************)
(*     The number                                                             *)
(******************************************************************************)

(** Two to the fortieth is at least one, at every real field. *)
Fact psl211_pow2_40_ge1 (R : realType) : (1:R) <= 2%:R^+40.
Proof. by apply: exprn_ege1; rewrite ler1n. Qed.

(** Two to the fortieth is positive, at every real field. *)
Fact psl211_pow2_40_gt0 (R : realType) : (0:R) < 2%:R^+40.
Proof. by rewrite exprn_gt0 // ltr0n. Qed.

(** The two models' laws are within two of each other by the bound every pair of
    laws on one finite sample space meets, with no fact about the twelve-card
    instance and no fact about the 584-letter walk. A proximity certificate
    carrying two would be a certificate about nothing, which is why the number a
    program publishes is what a reader of the arm must read. *)
Lemma psl211_word_law_le2 (R : realType) :
  var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2%:R.
Proof. exact: var_dist_le2. Qed.

(** The same bound does not reach 2^-40. The rejection is a failure to unify
    the two numbers:

      The term "var_dist_le2 ?P ?Q" has type "is_true (var_dist ?P ?Q <= 2)"
      while it is expected to have type
       "is_true (var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2 ^- 40)".

    So the bound var_dist_le2 gives for an arbitrary pair of laws does not
    reach this number: the term that proves the distance at two is rejected at
    2^-40. What carries the number psl211_word_law_le40 proves is
    psl211_word_mixing. *)
Fail Definition psl211_word_law_by_var_dist_le2 (R : realType) :
  var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2%:R^-40
  := var_dist_le2 _ _.
