(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_profile: the PSL(2,11) plug of the shared MonodromyProfile program  *)
(*                                                                            *)
(* The twelve-card chirality scheme (psl211_scheme) is packaged as a         *)
(* MonodromyProfile, a program-layer value carrying no epsilon, together with *)
(* a separate marginal bound at epsilon = 0: the single-card pushforward of   *)
(* the uniform shuffle over PSL(2,11) is exactly uniform, by the              *)
(* transitivity marginal ttrans_point_uniform at two-transitivity.            *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_PI       == the starting interface on twelve card positions       *)
(*                      (ord_tuple 12)                                        *)
(*   psl211_rho_dist == the uniform distribution over the shuffle group       *)
(*   psl211_marginal_bound == the ShuffleMarginalBound at epsilon = 0         *)
(*   psl211_certificate_bundle == that bound with the exact certificate       *)
(*   psl211_profile  == the MonodromyProfile bundling PI and plug             *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_point_uniform == the single-card pushforward is exactly uniform   *)
(*   profile_k_psl211     == the plug's privacy threshold is six              *)
(*   profile_eps_psl211   == the marginal bound's epsilon is zero             *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_reconstruct Require Import transitivity_privacy algebraic_rigidity.
From pgg_smc Require Import psl211_group psl211_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Order.Theory GRing.Theory Num.Theory.

Local Open Scope fdist_scope.

(** psl211_starts_uniq — the twelve starting card positions are distinct. *)
Lemma psl211_starts_uniq : uniq (ord_tuple 12).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.

(** psl211_PI — the starting interface on twelve card positions for the
    PSL(2,11) plug. The identity start tuple driving the shared exchange
    program. *)
Definition psl211_PI : PGGInterface psl211_M :=
  @MkPGGI psl211_M 11 (ord_tuple 12) psl211_starts_uniq.

Section witness.
Variable R : realType.

(** psl211_rho_dist — the uniform distribution over the PSL(2,11) shuffle
    group. The shuffle law of the twelve-card chirality scheme. *)
Definition psl211_rho_dist : R.-fdist {perm 'I_12} := `U psl211_G_pos.

(** psl211_point_uniform — the single-card pushforward of the uniform
    shuffle is exactly uniform, via the transitivity marginal at
    two-transitivity. *)
Lemma psl211_point_uniform (s : 'I_12) :
  fdistmap (fun sigma : {perm 'I_12} => sigma s) psl211_rho_dist
  = fdist_uniform (card_ord 12).
Proof.
exact: (@ttrans_point_uniform (pgg_N' psl211_M) (pgg_gT psl211_M)
  (pgg_G psl211_M) (@pgg_rho psl211_M) 2 psl211_2transitive R
  psl211_G_pos s isT).
Qed.

(** psl211_se_exact — the single-card pushforward of the uniform shuffle is
    at variation distance zero from uniform, not merely close to it.  This is
    the exact certificate the bundle below carries: at one card position the
    idealised shuffle has no error to price, so every epsilon in this
    instance's marginal layer is zero and the only price paid anywhere is the
    2^-40 of psl211_word_mixing for the realistic word shuffle. *)
Lemma psl211_se_exact (s : 'I_12) :
  var_dist (fdistmap (fun sigma : {perm 'I_12} => sigma s) psl211_rho_dist)
           (fdist_uniform (card_ord 12)) = 0%R.
Proof.
rewrite psl211_point_uniform /var_dist.
by apply: big1 => a _; rewrite subrr normr0.
Qed.

(** psl211_sw_bound — the single-card pushforward meets the bound at
    epsilon = 0.  The inequality form of psl211_se_exact, which is the shape
    the ShuffleMarginalBound field takes; the record stores a bound, and this
    instance's bound happens to be met with equality. *)
Lemma psl211_sw_bound (s : 'I_12) :
  (var_dist (fdistmap (fun sigma : {perm 'I_12} => sigma s) psl211_rho_dist)
            (fdist_uniform (card_ord 12)) <= 0%R)%O.
Proof. rewrite psl211_se_exact; exact: lexx. Qed.

(** psl211_marginal_bound — the marginal bound at epsilon = 0: single-card
    perfect uniformity of the PSL(2,11) shuffle, carrying word length 0,
    the uniform shuffle distribution and its per-position bound. Word
    length 0 records that this model does no word shuffling at all: the
    cut is drawn from the group itself, and the price of that idealisation
    is paid by psl211_word_mixing, not here. *)
Definition psl211_marginal_bound : ShuffleMarginalBound R psl211_M :=
  @MkShuffleMarginalBound R psl211_M 0 0%R psl211_rho_dist psl211_sw_bound.

(** psl211_certificate_bundle — the marginal bound above with the
    exact-equality certificate attached and no asymptotic certificate. The
    exact slot carries the closed-form equality, distance zero rather than
    a bound, so nothing about this instance rests on an asymptotic
    argument. *)
Definition psl211_certificate_bundle : ShuffleCertificateBundle R psl211_M :=
  @MkShuffleCertificateBundle R psl211_M psl211_marginal_bound
    (Some (@MkSecurityExact R psl211_M psl211_rho_dist 0%R psl211_se_exact))
    None.

End witness.

(** psl211_profile — the PSL(2,11) plug of the shared MonodromyProfile: the
    group, the secret type, PI and the plug of psl211_scheme.v. The secret
    type is bool because the secret is the chirality bit, which of the two
    Steiner systems S(5,6,12) the dealt heart positions form a block of. *)
Definition psl211_profile : MonodromyProfile :=
  @MkMonodromyProfile psl211_M bool psl211_PI psl211_plug.

(** profile_k_psl211 — the PSL(2,11) plug's privacy threshold is six:
    coalitions of at most five card positions are private. The threshold
    is the scheme's and not the group's. PSL(2,11) is only 2-transitive
    on the twelve positions, so it fixes no arbitrary five-set; the bound
    comes from the two Steiner systems meeting every five-set in the same
    block patterns with the same multiplicities (psl211_count_okT).
    Two-transitivity buys the single-card marginal above and nothing
    about this threshold. *)
Lemma profile_k_psl211 : profile_k psl211_profile = 6.
Proof. by []. Qed.

(** profile_eps_psl211 — the PSL(2,11) marginal bound's epsilon is zero.
    The epsilon field of psl211_marginal_bound is 0: the single-card
    pushforward of the uniform-over-the-group shuffle is exactly uniform. *)
Lemma profile_eps_psl211 (R : realType) :
  sw_bound_eps (psl211_marginal_bound R) = 0%R.
Proof. by []. Qed.
