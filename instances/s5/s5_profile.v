(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5_profile: the S_5 plug of the shared MonodromyProfile program            *)
(*                                                                            *)
(* The plug reuses Bring's covering plug (cs_plug s5_brings_covering): the    *)
(* sum-mod scheme on 'I_5, identity content readout, the S_5 monodromy        *)
(* pgg_rho, and the proven full-group reconstruction invariance               *)
(* s5_sum_mod_perm_compatible.                                                *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_raag pgg_raag_path pgg_raag_s5.
From pgg_smc Require Import card_exchange_pismc pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import rigidity_s5_instance.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** s5_starts_uniq — the five starting seats of the S_5 deck, [ord_tuple 5],
    are pairwise distinct. A [PGGInterface] must certify uniqueness of its
    start tuple, and this is exactly that certificate for [s5_PI]. *)
Lemma s5_starts_uniq : uniq (ord_tuple 5).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.

(** s5_PI — the [PGGInterface] for the S_5 plug: five sheets, the identity
    start tuple [ord_tuple 5], certified distinct by [s5_starts_uniq]. Fixing
    this interface is what lets the shared card-exchange program run at
    S_5 instead of an abstract N. *)
Definition s5_PI : PGGInterface (@Gen_PGGTypes 3 3 (path_gen_tuple 3)) :=
  @MkPGGI (@Gen_PGGTypes 3 3 (path_gen_tuple 3)) 4 (ord_tuple 5) s5_starts_uniq.

(** s5_plug — the S_5 [ReconPlug]: Bring's covering plug (the sum-mod
    content scheme, identity content readout, the S_5 monodromy action, and
    the proven full-group reconstruction invariance
    [s5_sum_mod_perm_compatible]) specialized via [cs_plug]. Supplying this
    plug is what routes S_5 through the shared [MonodromyProfile] program
    rather than re-deriving reconstruction for S_5 from scratch. *)
Definition s5_plug : ReconPlug (@Gen_PGGTypes 3 3 (path_gen_tuple 3)) 'I_5 :=
  cs_plug s5_brings_covering.

(** s5_profile — the [MonodromyProfile] for S_5: the adjacent-transposition
    group action, secret type ['I_5], interface [s5_PI], and plug [s5_plug].
    The S_5 instance's mixing and secrecy results are obtained by
    specializing the shared [MonodromyProfile] program at this profile; its
    privacy threshold is k = 5 ([profile_k_s5] below). *)
Definition s5_profile : MonodromyProfile :=
  @MkMonodromyProfile (@Gen_PGGTypes 3 3 (path_gen_tuple 3)) 'I_5 s5_PI
    s5_plug.

(** profile_k_s5 — the S_5 plug's privacy threshold, [profile_k s5_profile],
    is 5: reconstructing the secret at S_5 needs the full five-seat
    coalition, the maximal threshold on this deck size and a sharper bound
    than the den Boer plug's k = 2. *)
Lemma profile_k_s5 : profile_k s5_profile = 5.
Proof. by []. Qed.
