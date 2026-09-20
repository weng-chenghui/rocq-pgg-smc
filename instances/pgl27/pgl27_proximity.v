(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_proximity: the instance's reading of a coalition, and the distances  *)
(* between its two laws of the cut                                            *)
(*                                                                            *)
(* The eight-card orbit instance runs one execution under two laws of the     *)
(* cut: the exact shuffle, which draws it uniformly from PGL(2,7), and the    *)
(* two-hundred-letter word walk, which draws it by evaluating a sampled       *)
(* generator word. This file holds the mathematics that separates the two,    *)
(* with no program in it, published or not.                                   *)
(*                                                                            *)
(* One bound is the closeness field of the proximity certificate: below the   *)
(* four-seat threshold, the joint law of a coalition's reading with the dealt *)
(* secret under the walk is within 2^-40 of the same joint law under the      *)
(* uniform cut at the same law of the secret. The number is the walk's        *)
(* single-card marginal number, and it rests on pgl27_word_mixing, the bound  *)
(* by that same number on the distance between the walk and the uniform cut   *)
(* on the group.                                                              *)
(*                                                                            *)
(* Every number below bounds a sum of absolute differences, which is twice    *)
(* the total variation distance of the literature, so a bound of 2^-40 here   *)
(* is a distinguishing advantage of at most 2^-41 wherever it is used.        *)
(*                                                                            *)
(* The other distance runs the other way. A proximity certificate holds its   *)
(* ideal at the same index as the model it is about, so the two have to be    *)
(* read at one law of the dealt secret. pgl27_prior_exact_family of           *)
(* pgl27_models.v carries that law as its index, where pgl27_exact_family is  *)
(* indexed by the unit type and its one member fixes the uniform law. An      *)
(* ideal taken from the unit-indexed family can therefore only be the ideal   *)
(* of a word model at the uniform law, and the distance of a word model at    *)
(* another law to it is at least the distance between the two laws of the     *)
(* secret, which pgl27_word_uniform_ideal_close_false exhibits at a point     *)
(* mass.                                                                      *)
(*                                                                            *)
(* The identification of the framework's static reading of a coalition with   *)
(* pgl27_view opens the file, because the distance proof rewrites with it     *)
(* twice and because its subject is the run parameter record and no program   *)
(* value. The two sides are not the same term, the framework reading seat i   *)
(* at tnth (pi_starts _) i and the instance at i, and they agree because this *)
(* instance's seats start at the eight card positions in order. A             *)
(* coalition's content trace is that same finite map again, so the trace      *)
(* theorems and the reading theorems of this instance are one statement each. *)
(*                                                                            *)
(* The certificate itself, the program published over it and the statements   *)
(* about them are in instances/pgl27/tableau/, whose AnalysisBridged file     *)
(* requires this one. This file requires no tableau module, so the arrow      *)
(* between the mathematics and the tableau runs one way, upward.              *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_word_secret       == the dealt secret on the word sample space     *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_static_obsE       == the framework's reading is the instance's     *)
(*   pgl27_static_obs_funE   == the same with the cut left free               *)
(*   pgl27_coalition_trace_static_obsE                                        *)
(*                           == a coalition's content trace is its static     *)
(*                              reading                                       *)
(*   pgl27_word_proximity_close                                               *)
(*                           == below the four-seat threshold, the two        *)
(*                              models' joint laws of reading and secret are  *)
(*                              within 2^-40                                  *)
(*   pgl27_pow2_40_ge1       == two to the fortieth is at least one           *)
(*   pgl27_pow2_40_gt0       == two to the fortieth is positive               *)
(*   pgl27_word_uniform_ideal_close_false                                     *)
(*                           == the closeness field is false at every         *)
(*                              coalition, with the uniform-secret exact      *)
(*                              model as the ideal of the word model at a     *)
(*                              point-mass prior                              *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_trace pgl27_models.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.


(******************************************************************************)
(*     The instance-side reading of a coalition                               *)
(******************************************************************************)

(** Seat i's entry of the framework's static coalition reading is seat i's
    entry of the instance's coalition view. The two are not the same term: the
    framework reads seat i at tnth (pi_starts _) i and the instance reads it at
    i, and they agree because this instance's seats start at the eight card
    positions in order. Every security statement of a program is made about the
    left-hand side and every theorem of this instance about the right, so this
    equation is the whole of what carries one to the other. *)
Lemma pgl27_static_obsE (R : realType) (C : {set 'I_8}) (s : bool)
    (g : pgg_gT pgl27_M) :
  @static_coalition_obs pgl27_algebra pgl27_dealt_params C s g
  = pgl27_view R C (s, g).
Proof.
apply/ffunP => i.
rewrite /static_coalition_obs /pgl27_view [LHS]ffunE [RHS]ffunE.
by case: ifP => // _; rewrite tnth_ord_tuple.
Qed.

(** The same identification with the cut left free, as an equality of
    functions of the cut. The input-indistinguishability proposition compares
    two laws obtained by pushing a reading forward along a distribution on
    cuts, so it needs the reading as one function and not as its values. *)
Lemma pgl27_static_obs_funE (R : realType) (C : {set 'I_8}) (s : bool) :
  @static_coalition_obs pgl27_algebra pgl27_dealt_params C s
  = (fun g => pgl27_view R C (s, g)).
Proof. by apply: boolp.funext => g; exact: pgl27_static_obsE. Qed.

(** A coalition's content trace at this instance is its static coalition
    reading, at every dealt secret and every cut. The trace records the card
    each member's interpreter row carries and the reading records the card
    each member's seat holds after the shuffle, and at this instance's eight
    seats the two are one finite map. Every theorem this instance publishes
    about the trace and every theorem it publishes about the reading are
    therefore one statement each, and the two numbers 2^-39 the tree
    publishes, one at the trace and one at the reading, are one number. *)
Lemma pgl27_coalition_trace_static_obsE (R : realType) (C : {set 'I_8})
    (s : bool) (g : pgg_gT pgl27_M) :
  pgl27_coalition_trace R C (s, g)
  = @static_coalition_obs pgl27_algebra pgl27_dealt_params C s g.
Proof.
by rewrite (pgl27_coalition_trace_E R C) (pgl27_static_obsE R C s g).
Qed.


(******************************************************************************)
(*     The dealt secret on the word sample space                              *)
(******************************************************************************)

(** The dealt secret as a random variable on the word sample space. The word
    space is the pair of the secret and the sampled generator word, so the
    secret is its first projection, and it is typed at the carrier the ideal's
    witness names so that the two models speak of one secret. *)
Definition pgl27_word_secret (R : realType) (secretP : R.-fdist bool)
  : {RV (sa_sampleP (pgl27_word_sample secretP)) -> bool} := fun u => u.1.
Arguments pgl27_word_secret [R] secretP.


(******************************************************************************)
(*     The distance between the two models' joint laws                        *)
(******************************************************************************)

(** At every coalition of fewer than four seats and at every prior, the joint
    law of that coalition's reading with the dealt secret under the
    two-hundred-letter word walk is within 2^-40 of the same joint law under
    the uniform cut at the same prior. It is the closeness field of the
    proximity certificate at this instance: the two models differ in the law of
    the cut alone, the secret is drawn from the same prior and independently of
    the cut in both, and the pair of a reading and the secret is a
    deterministic function of the pair of the secret and the cut. The premise is
    the ideal-proximity proposition's threshold at this instance, four seats.
    pgl27_word_mixing, the bound on the cut group's own distance, carries no
    coalition premise, so the same bound is reachable at every coalition by a
    route this proof does not take. *)
Lemma pgl27_word_proximity_close (R : realType) (secretP : R.-fdist bool)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  (#|C| < profile_k (instance_profile pgl27_algebra))%N ->
  var_dist
    (fdistmap (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params
                           C ((pgl27_word_sample secretP).(sa_arg) u)
                           ((pgl27_word_sample secretP).(sa_cut) u),
                         pgl27_word_secret secretP u))
       (sa_sampleP (pgl27_word_sample secretP)))
    (fdistmap (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params
                           C ((pgl27_prior_sample secretP).(sa_arg) u)
                           ((pgl27_prior_sample secretP).(sa_cut) u),
                         pgl27_secret R u))
       (sa_sampleP (pgl27_prior_sample secretP)))
  <= 2%:R^-40.
Proof.
(* The word side is rewritten as a reading of the pair of the secret and the
   evaluated cut, which is the carrier pgl27_view_mixing is stated on; the
   ideal side is that same reading under the uniform cut, turned into the
   product of its marginals by the ideal witness's own independence. The
   threshold is used twice, once for the ideal witness's independence and
   once for pgl27_view_mixing. *)
move=> HC.
have H3 : (#|C| <= 3)%N := HC.
have Hact :
  (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params C
               ((pgl27_word_sample secretP).(sa_arg) u)
               ((pgl27_word_sample secretP).(sa_cut) u),
             pgl27_word_secret secretP u))
  = [% pgl27_view R C, pgl27_secret R]
      \o (fun u => ((pgl27_word_sample secretP).(sa_arg) u,
                    (pgl27_word_sample secretP).(sa_cut) u)).
  by apply: boolp.funext => u /=; rewrite (pgl27_static_obsE R).
rewrite Hact -fdistmap_comp.
rewrite -/(sa_joint_dist (sa_arg (s := pgl27_word_sample secretP))).
rewrite pgl27_word_sample_joint_distE.
have Hid :
  (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params C
               ((pgl27_prior_sample secretP).(sa_arg) u)
               ((pgl27_prior_sample secretP).(sa_cut) u),
             pgl27_secret R u))
  = [% pgl27_view R C, pgl27_secret R].
  by apply: boolp.funext; case=> s g; rewrite /= (pgl27_static_obsE R).
rewrite Hid.
have Hprod :
  fdistmap [% pgl27_view R C, pgl27_secret R]
    (sa_sampleP (pgl27_prior_sample secretP))
  = (fdistmap (pgl27_view R C) (pgl27P_gen secretP))
    `x (fdistmap (pgl27_secret R) (pgl27P_gen secretP)).
  exact: (inde_dist_of_RV2 (pgl27_view_indep_gen secretP H3)).
rewrite Hprod.
exact: (pgl27_view_mixing secretP H3).
Qed.


(******************************************************************************)
(*     The number                                                             *)
(******************************************************************************)

(** Two to the fortieth is at least one, at every real field.                 *)
Fact pgl27_pow2_40_ge1 (R : realType) : (1:R) <= 2%:R^+40.
Proof. by apply: exprn_ege1; rewrite ler1n. Qed.

(** Two to the fortieth is positive, at every real field.                     *)
Fact pgl27_pow2_40_gt0 (R : realType) : (0:R) < 2%:R^+40.
Proof. by rewrite exprn_gt0 // ltr0n. Qed.


(******************************************************************************)
(*     What refutes a distance bound                                          *)
(******************************************************************************)

Section pgl27_word_uniform_ideal.
Variable R : realType.

Let P1 : R.-fdist bool := fdist1 true.

(** The closeness field of a proximity certificate is false, and not merely
    unwritable, when the ideal is the uniform-secret member of the tree's exact
    family and the actual model is the word walk at the point-mass prior.
    Pushing both joint laws forward along the secret coordinate leaves the two
    priors themselves, one apart, and 2^-40 is below that, so the two models are
    separated by their secrets alone and no reading of the cut can bring them
    together. It says nothing at a prior near the uniform one, where the same
    lower bound is small. It is stated at every coalition and not only below
    four seats, so it refutes more than the field asks. *)
Lemma pgl27_word_uniform_ideal_close_false
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  ~ (var_dist
       (fdistmap (fun u => (@static_coalition_obs pgl27_algebra
                              pgl27_dealt_params C
                              ((pgl27_word_sample P1).(sa_arg) u)
                              ((pgl27_word_sample P1).(sa_cut) u),
                            pgl27_word_secret P1 u))
          (sa_sampleP (pgl27_word_sample P1)))
       (fdistmap (fun u => (@static_coalition_obs pgl27_algebra
                              pgl27_dealt_params C
                              ((pgl27_sample R).(sa_arg) u)
                              ((pgl27_sample R).(sa_cut) u),
                            pgl27_secret R u))
          (sa_sampleP (pgl27_sample R)))
     <= 2%:R^-40).
Proof.
move=> Hle.
have Hdp := var_dist_fdistmap (@snd _ _)
  (fdistmap (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params C
                         ((pgl27_word_sample P1).(sa_arg) u)
                         ((pgl27_word_sample P1).(sa_cut) u),
                       pgl27_word_secret P1 u))
     (sa_sampleP (pgl27_word_sample P1)))
  (fdistmap (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params C
                         ((pgl27_sample R).(sa_arg) u)
                         ((pgl27_sample R).(sa_cut) u),
                       pgl27_secret R u))
     (sa_sampleP (pgl27_sample R))).
rewrite !fdistmap_comp in Hdp.
have Hw : fdistmap ((@snd _ _) \o
            (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params C
                         ((pgl27_word_sample P1).(sa_arg) u)
                         ((pgl27_word_sample P1).(sa_cut) u),
                       pgl27_word_secret P1 u)))
            (sa_sampleP (pgl27_word_sample P1))
          = P1.
  exact: fdist_prod1.
have Hi : fdistmap ((@snd _ _) \o
            (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params C
                         ((pgl27_sample R).(sa_arg) u)
                         ((pgl27_sample R).(sa_cut) u),
                       pgl27_secret R u)))
            (sa_sampleP (pgl27_sample R))
          = fdist_uniform (R := R) card_bool.
  exact: fdist_prod1.
rewrite Hw Hi var_dist_fdist1_uniform in Hdp.
have Hge : (1:R) <= 2%:R^+39 by apply: exprn_ege1; rewrite ler1n.
have Hpos : (0:R) < 2%:R^+40 by rewrite exprn_gt0 // ltr0n.
have Hgt1 : (1:R) < 2%:R^+40 by rewrite exprS; lra.
have Hlt : (2%:R : R)^-40 < 1 by rewrite invf_lt1.
lra.
Qed.

End pgl27_word_uniform_ideal.
