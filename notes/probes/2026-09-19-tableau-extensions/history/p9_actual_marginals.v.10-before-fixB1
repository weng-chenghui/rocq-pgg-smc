(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P9: what the proximity arm says about the actual model alone         *)
(*                                                                            *)
(* The proximity arm compares the actual model with a named ideal one, so a   *)
(* reader who has no interest in that ideal is told nothing directly. This    *)
(* file removes the ideal from the statement. A joint law within c of some    *)
(* product law is within three times c of the product of its own two          *)
(* marginals, so a coalition below the threshold has, under the actual model  *)
(* by itself, an advantage of at most three times the published number in     *)
(* telling its reading and the secret apart from two quantities drawn         *)
(* independently. The factor is three and not one: the ideal's two marginals  *)
(* are within the number of the actual model's two marginals, once for each,  *)
(* and the comparison with the actual product spends the number a third time. *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   var_dist_own_marginals    == a joint law close to a product law is close *)
(*                                to the product of its own marginals         *)
(*                                                                            *)
(* Key results:                                                               *)
(*   five_card_biased_view_own_marginals                                      *)
(*                             == Kim's one-cut row's claim about that model  *)
(*                                alone, at three twenty-fifths               *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_collusion_bound.
From pgg_smc Require Import five_card_group five_card_family.
From pgg_smc Require Import five_card_exec five_card_models five_card_leakage.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.
From tableau_ext_probe Require Import p1_joint_law_distance.
From tableau_ext_probe Require Import p4_kim_biased_proximity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     A joint law against the product of its own marginals                   *)
(******************************************************************************)

(** A joint law within d of a product of two laws is within three times d of
    the product of its own two marginals. Each marginal of the joint law is
    within d of the corresponding factor by data processing, and replacing the
    two factors one at a time costs d each, so the number is spent three
    times. It is what turns a statement comparing two models into a statement
    about one, at a constant no reader has to trace back to the ideal. *)
Lemma var_dist_own_marginals (R : realType) (V W : finType)
    (J : R.-fdist (V * W)) (Mr : R.-fdist V) (Ms : R.-fdist W) (d : R) :
  var_dist J (Mr `x Ms) <= d ->
  var_dist J ((fdistmap fst J) `x (fdistmap snd J)) <= 3%:R * d.
Proof.
move=> H.
have Hfst : fdistmap fst (Mr `x Ms) = Mr by exact: fdist_prod1.
have Hsnd : fdistmap snd (Mr `x Ms) = Ms by exact: fdist_prod_snd.
have Hr : var_dist Mr (fdistmap fst J) <= d.
  rewrite symmetric_var_dist -Hfst.
  exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) H).
have Hs : var_dist Ms (fdistmap snd J) <= d.
  rewrite symmetric_var_dist -Hsnd.
  exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) H).
have H3 : (3%:R : R) * d = d + (d + d) by lra.
rewrite H3.
apply: (Order.POrderTheory.le_trans (var_dist_triangle _ (Mr `x Ms) _)).
apply: lerD; first exact: H.
apply: (Order.POrderTheory.le_trans
          (var_dist_triangle _ (Mr `x (fdistmap snd J)) _)).
by apply: lerD; [rewrite var_dist_prodR | rewrite var_dist_prodL].
Qed.

(******************************************************************************)
(*     The corollary at Kim's one-cut row                                     *)
(******************************************************************************)

(** Kim's one-cut row, read as a statement about that model alone: at fewer
    than two colluding seats, the joint law of the coalition's executed view
    with the conjunction of the committed bits is within three twenty-fifths
    of the product of its own two marginals. The den Boer uniform model has
    left the statement, and what remains is a bound on how far the one-cut run
    is from making a coalition's reading and the secret independent. *)
Theorem five_card_biased_view_own_marginals (R : realType) (C : {set 'I_5})
    (HC : (#|C| < 2)%N) :
  var_dist
    (fdistmap (fun u => (@sa_coalition_view R five_card_profile
                           five_card_exec_plug
                           (amf_sample kim_biased_family R tt) 0 C u,
                         five_card_leakage.Secret R u))
       (sa_sampleP (amf_sample kim_biased_family R tt)))
    ((fdistmap fst
        (fdistmap (fun u => (@sa_coalition_view R five_card_profile
                               five_card_exec_plug
                               (amf_sample kim_biased_family R tt) 0 C u,
                             five_card_leakage.Secret R u))
           (sa_sampleP (amf_sample kim_biased_family R tt))))
     `x (fdistmap snd
           (fdistmap (fun u => (@sa_coalition_view R five_card_profile
                                  five_card_exec_plug
                                  (amf_sample kim_biased_family R tt) 0 C u,
                                five_card_leakage.Secret R u))
              (sa_sampleP (amf_sample kim_biased_family R tt)))))
  <= 3%:R * (1 / 25).
Proof.
exact: (var_dist_own_marginals (@five_card_biased_view_proximity R C HC)).
Qed.
