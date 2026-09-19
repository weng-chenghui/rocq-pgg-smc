(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P5, the rejections: which ideals the proximity arm refuses           *)
(*                                                                            *)
(* A proximity certificate names the model it calls ideal, and the strength   *)
(* of the arm rests on that model being the one the actual model should be    *)
(* compared with. This file records the two ways of naming the wrong one at   *)
(* PGL(2,7) and the failure that rejects each, and the cross-arm rejection    *)
(* that keeps a proximity certificate off the exact model's branch point.     *)
(*                                                                            *)
(* The first two rejections are about the prior. The exact family of          *)
(* pgl27_models.v is indexed by the unit type, so it cannot be read at the    *)
(* prior a word row carries, and its one member fixes the uniform secret.     *)
(* Each Fail rejects the one term written under it, the first on a mismatch   *)
(* of index types and the second on a mismatch in the distance field. Beside  *)
(* the second, one compiled lemma refutes that field itself at the            *)
(* point-mass prior fdist1 true: the two joint laws push forward along the    *)
(* secret coordinate to the point mass and to the uniform law, which are one  *)
(* apart in the sum of absolute differences, while 2^-40 is not. At a prior   *)
(* within 2^-40 of the uniform one the same lower bound is small and nothing  *)
(* is claimed there. This is why the ideal of a word row is the               *)
(* prior-indexed family and not the one the tree already carries.             *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   var_dist_fdist1_uniform   == a point mass and the uniform law on the     *)
(*                                booleans are one apart                      *)
(*   pgl27_word_uniform_ideal_not_close                                       *)
(*                             == the distance field is false with the        *)
(*                                uniform-secret exact model as the ideal of  *)
(*                                the word model at a point-mass prior        *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_collusion_bound.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.
From tableau_ext_probe Require Import pgl27_rows t0_sampled_branch_pgl27.
From tableau_ext_probe Require Import p5_pgl27_prior_ideal.
From tableau_ext_probe Require Import p5_pgl27_word_proximity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(** The unit-indexed exact family cannot be read at the prior the word model
    carries. The index of an analysis model family is a type depending on the
    real field alone, and amf_sample asks for an inhabitant of it, so a
    distribution on the booleans is offered where the unit type is expected
    and the two sample adapters are never reached. A proximity certificate
    over a prior-indexed actual model therefore cannot take the tree's exact
    family as its ideal, whatever the two models' distance is. *)
Fail Definition pgl27_word_proximity_cert_unit_ideal (R : realType)
    (secretP : R.-fdist bool)
  : IdealProximityCert (amf_sample pgl27_word_family R secretP) :=
  @MkIdealProximityCert R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP)
    (amf_sample pgl27_exact_family R secretP)
    (@pgl27_exact_witness R secretP)
    (pgl27_word_secret secretP)
    (sw_bound_eps (pgl27_word_marginal_bound R))
    (fun C HC => pgl27_word_proximity_close secretP HC).

(******************************************************************************)
(*     The uniform-secret ideal, refuted at a point-mass prior                *)
(******************************************************************************)

(** The distance between a point mass on the booleans and the uniform law on
    the booleans, in the sum of absolute differences: one. This is the
    quantity a proximity bound between two models whose secrets are drawn
    from those two laws has to beat, whatever the rest of the two executions
    does. *)
Lemma var_dist_fdist1_uniform (R : realType) :
  var_dist (fdist1 true : R.-fdist bool) (fdist_uniform (R := R) card_bool)
  = 1.
Proof.
have Hu : forall b : bool, (fdist_uniform (R := R) card_bool) b = 2%:R^-1.
  by move=> b; rewrite fdist_uniformE card_bool.
have H2 : (0:R) < 2%:R by rewrite ltr0n.
have Hhalf : (0:R) <= 2%:R^-1 by rewrite invr_ge0 ler0n.
have Hle1 : 2%:R^-1 <= (1:R) by rewrite invf_le1 // ler1n.
have Ht : (fdist1 true : R.-fdist bool) true = 1 by rewrite fdist1E eqxx.
have Hf : (fdist1 true : R.-fdist bool) false = 0.
  by first [by rewrite fdist1E | by rewrite fdist1E /= mul0rn
           | by rewrite fdist1E mul0rn | by rewrite fdist1E /=].
have E1 : `|(1:R) - 2%:R^-1| = 1 - 2%:R^-1 by rewrite ger0_norm ?subr_ge0.
have E2 : `|(0:R) - 2%:R^-1| = 2%:R^-1 by rewrite sub0r normrN ger0_norm.
rewrite /var_dist big_bool /= !Hu Ht Hf E1 E2.
by lra.
Qed.

Section pgl27_word_uniform_ideal.
Variable R : realType.

Let P1 : R.-fdist bool := fdist1 true.

(** The distance field of a proximity certificate is false, and not merely
    unwritable, when the ideal is the uniform-secret member of the tree's
    exact family and the actual model is the word walk at the point-mass
    prior. Pushing both joint laws forward along the secret coordinate leaves
    the two priors themselves, one apart, and 2^-40 is below that, so the two
    models are separated by their secrets alone and no reading of the cut can
    bring them together. It says nothing at a prior near the uniform one,
    where the same lower bound is small. *)
Lemma pgl27_word_uniform_ideal_not_close
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

(** The one member of the unit-indexed exact family fixes the uniform secret,
    and it is a well-typed ideal for a word model at any prior: the index is
    supplied as tt and both adapters live over the same execution. What the
    kernel rejects is the distance field, whose proof is stated between the
    word model at secretP and the exact model at secretP and not between the
    word model at secretP and the exact model at the uniform prior. The Fail
    rejects the one term written here, on that mismatch of types, and rules
    out no other term. What refutes the field itself is
    pgl27_word_uniform_ideal_not_close above, at the point-mass prior, where
    the two secret marginals are one apart and 2^-40 is not; at a prior near
    the uniform one that lower bound is small and nothing is claimed. *)
Fail Definition pgl27_word_proximity_cert_uniform_ideal (R : realType)
    (secretP : R.-fdist bool)
  : IdealProximityCert (amf_sample pgl27_word_family R secretP) :=
  @MkIdealProximityCert R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP)
    (amf_sample pgl27_exact_family R tt)
    (@pgl27_exact_witness R tt)
    (pgl27_word_secret secretP)
    (sw_bound_eps (pgl27_word_marginal_bound R))
    (fun C HC => pgl27_word_proximity_close secretP HC).

(** The word model's proximity certificate does not continue the exact model's
    branch point. The payload type is IdealProximityPayload at the coordinate
    the name holds, so the clause is checked first against the index type that
    coordinate's family carries, unit against a distribution on the booleans.
    Two models of one instance are separated here as they are for the exact
    and the spectral payloads at pgl27_exact_sampled. *)
Fail Definition pgl27_cross_model_proximity : Tableau AnalysisBridged :=
  pgl27_exact_sampled certify IdealProximity pgl27_word_proximity_cert.
