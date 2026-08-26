(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5x5_profile: the S_5 x S_5 plug of the shared MonodromyProfile program     *)
(*                                                                            *)
(* Mirrors s5_profile but for the two-pile-of-five product instance. The plug *)
(* reuses the product covering plug (cs_plug s5x5_covering): the product       *)
(* sum-mod scheme on 'I_10, identity content readout, the S_5 x S_5 monodromy  *)
(* pgg_rho, and the proven full-group reconstruction invariance               *)
(* s5x5_perm_compatible.                                                       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_raag.
From pgg_smc Require Import pgg_s5x5 s5x5_pile.
From pgg_smc Require Import card_exchange_pismc pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import rigidity_s5x5_instance.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** s5x5_plug — the S_5 x S_5 [ReconPlug]: the product covering plug (the
    product sum-mod scheme on ['I_10], identity content readout, the S_5 x
    S_5 monodromy [pgg_rho], and the proven full-group reconstruction
    invariance [s5x5_perm_compatible]) specialized via [cs_plug]. Supplying
    this plug is what routes the two-pile product instance through the
    shared [MonodromyProfile] program rather than re-deriving reconstruction
    for S_5 x S_5 from scratch. *)
Definition s5x5_plug : ReconPlug (@Gen_PGGTypes 7 8 s5x5_gen_tuple) 'I_10 :=
  cs_plug s5x5_covering.

(** s5x5_profile — the [MonodromyProfile] for S_5 x S_5: the product
    two-pile generator action, secret type ['I_10], interface [s5x5_PI], and
    plug [s5x5_plug]. The S_5 x S_5 instance's mixing and secrecy results
    are obtained by specializing the shared [MonodromyProfile] program at
    this profile; its privacy threshold is k = 5 per pile
    ([profile_k_s5x5] below), read off the per-pile sum-mod scheme. *)
Definition s5x5_profile : MonodromyProfile :=
  @MkMonodromyProfile (@Gen_PGGTypes 7 8 s5x5_gen_tuple) 'I_10 s5x5_PI
    s5x5_plug.

(** profile_k_s5x5 — the S_5 x S_5 plug's privacy threshold, [profile_k
    s5x5_profile], is 5: reconstructing the secret within either pile needs
    the full five-seat coalition for that pile, so a coalition of fewer than
    five seats in a pile learns nothing about that pile's content. This is
    the same per-pile threshold as the single-pile S_5 instance
    ([profile_k_s5]), since the product plug's sum-mod scheme is per-pile. *)
Lemma profile_k_s5x5 : profile_k s5x5_profile = 5.
Proof. by []. Qed.
