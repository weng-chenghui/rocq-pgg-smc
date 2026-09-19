(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P5, the rejections: which ideals the proximity arm refuses           *)
(*                                                                            *)
(* A proximity certificate names the model it calls ideal, and the strength   *)
(* of the arm rests on that model being the one the actual model should be    *)
(* compared with. This file records the two ways of naming the wrong one at   *)
(* PGL(2,7) and the discrimination that rejects each, and the cross-arm       *)
(* rejection that keeps a proximity certificate off the exact model's branch  *)
(* point.                                                                     *)
(*                                                                            *)
(* The first two rejections are about the prior. The exact family of          *)
(* pgl27_models.v is indexed by the unit type, so it cannot be read at the    *)
(* prior a word row carries, and its one member fixes the uniform secret, so  *)
(* it is not within 2^-40 of a word model at another prior. The kernel        *)
(* rejects the first for the index type and the second for the distance,      *)
(* which is why the ideal of a word row has to be the prior-indexed family    *)
(* and not the one the tree already carries.                                  *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter pgg_weighted_words.
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

(** The one member of the unit-indexed exact family fixes the uniform secret,
    and it is a well-typed ideal for a word model at any prior: the index is
    supplied as tt and both adapters live over the same execution. What the
    kernel rejects is the distance field, whose proof is stated between the
    word model at secretP and the exact model at secretP and not between the
    word model at secretP and the exact model at the uniform prior. The
    rejection is the arm refusing to compare two models whose secrets are
    drawn from different laws, which is what a distance of 2^-40 could not
    bound: pushing both joint laws forward along the secret coordinate leaves
    the two priors themselves, and those are one apart in the sum of absolute
    differences when the prior is a point mass. *)
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
    and the spectral payloads of t0_sampled_branch_pgl27.v. *)
Fail Definition pgl27_cross_model_proximity : Tableau AnalysisBridged :=
  pgl27_exact_sampled certify IdealProximity pgl27_word_proximity_cert.
