(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P6, first half: the word model of the twelve-card instance           *)
(*                                                                            *)
(* The twelve-card chirality instance has two probability models over one     *)
(* execution. The all-decks model of psl211_models.v draws its cut uniformly  *)
(* from the 660 elements of the shuffle group. The model below draws it by    *)
(* evaluating a word of 584 letters drawn uniformly from the three            *)
(* generators, which is the shuffle a dealer performs by hand. The two models *)
(* share the sample space, the deck description and the law it is drawn from, *)
(* and differ in the law of the cut alone.                                    *)
(*                                                                            *)
(* Word gloss of this instance. A deck description is the whole run argument, *)
(* a chirality bit together with a deal. A deal is the block line of that     *)
(* chirality's Steiner system, the labelling of the heart codes and the       *)
(* labelling of the club codes, the three coordinates other than the secret.  *)
(* The secret is the chirality bit.                                           *)
(*                                                                            *)
(* Both models put a deck description and a cut in one sample point, so the   *)
(* model below is the all-decks adapter with the law of the cut coordinate    *)
(* replaced, and the chirality of one model is the chirality of the other as  *)
(* one term rather than two readings of one bit.                              *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_word_cutP     == the law of the cut a dealer performs by hand     *)
(*   psl211_wordP         == the law of the word model, decks times words     *)
(*   psl211_word_sample   == the word model as a sample adapter               *)
(*   psl211_word_family   == that adapter as a unit-indexed family            *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_word_sampleP_E == the adapter's law is the word model's law       *)
(*   psl211_word_cut_distE == the model's cut is the 584-letter word law      *)
(*   psl211_word_lawE      == the two models' laws are within 2^-40           *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_instance pgg_analysis_status.
From pgg_smc Require Import psl211_group psl211_closure psl211_profile.
From pgg_smc Require Import psl211_mixing.
From pgg_smc Require Import psl211_exec psl211_alldecks psl211_models.
From tableau_ext_probe Require Import p1_joint_law_distance.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     The law of the word model                                              *)
(******************************************************************************)

(** The law of the cut a dealer performs by hand: the image in the shuffle
    group of a word of 584 letters, each letter drawn uniformly and
    independently from the three generators, block reversal and the two Monge
    letters. It is the one coordinate in which this model departs from the
    all-decks model, and psl211_word_mixing is the whole price of the
    departure. *)
Definition psl211_word_cutP (R : realType) : R.-fdist (pgg_gT psl211_M) :=
  @rho_from_words_weighted R 10 2 584 psl211_moves (psl211_Wuni R).

(** The law of the word model: the deck description uniform over the
    136857600 of them, the cut the 584-letter word law, the two independent.
    It differs from psl211_alldecksP in the cut factor alone, so a coalition
    reads a deck laid by the same dealer under a different shuffle. *)
Definition psl211_wordP (R : realType)
  : R.-fdist (psl211_inputT * pgg_gT psl211_M)%type :=
  (`U psl211_alldecks_gt0) `x (psl211_word_cutP R).

(** The word model as a sample adapter over the execution the all-decks row
    runs: one sample point is a deck description together with a cut, the run
    argument the deck description and the cut the group element the run is
    dealt at. Its sample space is the carrier psl211_alldecks_sample uses, so
    the chirality is one random variable for the two models. *)
Definition psl211_word_sample (R : realType)
  : SampleAdapter R (instance_exec psl211_alldecks_params) :=
  @MkSampleAdapter R (instance_profile psl211_algebra)
    (instance_exec psl211_alldecks_params)
    ((psl211_inputT * pgg_gT psl211_M)%type : finType)
    (psl211_wordP R) fst snd.

(** The adapter's law is the model's law. *)
Lemma psl211_word_sampleP_E (R : realType) :
  sa_sampleP (psl211_word_sample R) = psl211_wordP R.
Proof. exact: erefl. Qed.

(** The cut this model draws is the 584-letter word law. That law is the one
    psl211_word_mixing bounds against uniform, so the distance the proximity
    arm spends is a distance between the two cuts of one execution and not a
    distance between two executions. *)
Lemma psl211_word_cut_distE (R : realType) :
  @sa_cut_dist R (instance_profile psl211_algebra)
    (instance_exec psl211_alldecks_params) (psl211_word_sample R)
  = psl211_word_cutP R.
Proof. exact: fdist_prod_snd. Qed.

(** The word model as a unit-indexed family: one member at every real field,
    the model having no parameter to range over. Its index type is the one
    psl211_exact_family carries, so a row over this model and the all-decks
    row are read at one index. *)
Definition psl211_word_family : AnalysisModelFamily psl211_alldecks_observed :=
  @MkAnalysisModelFamily psl211_alldecks_observed (fun _ => unit)
    (fun R _ => psl211_word_sample R).

(******************************************************************************)
(*     The distance between the two models' laws                              *)
(******************************************************************************)

(** The two models' laws are within 2^-40 of each other in the sum of
    absolute differences, which is 9.094947017729282e-13. The deck
    description is drawn from one law in both models and independently of the
    cut in both, so the distance between the two joint laws of description
    and cut is the distance between the two cuts, which psl211_word_mixing
    bounds. The bound is unconditional and information-theoretic: it counts
    the 3^584 words and assumes nothing about an adversary's resources. *)
Lemma psl211_word_lawE (R : realType) :
  var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2%:R^-40.
Proof.
rewrite /psl211_wordP /psl211_alldecksP /psl211_word_cutP var_dist_prodR.
exact: psl211_word_mixing.
Qed.
