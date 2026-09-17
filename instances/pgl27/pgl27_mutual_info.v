(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_mutual_info: the information a PGL(2,7) coalition view carries about *)
(*                    the orbit secret                                        *)
(*                                                                            *)
(* The orbit secret is a uniform bit, the shuffle is uniform on PGL(2,7), and *)
(* for each secret the dealt arrangement is the corresponding deck of a deck  *)
(* pair. A coalition sees the masked card values at its own positions before  *)
(* the reveal. When the two census view lists of a coalition are              *)
(* repetition-free, every view that occurs comes from at most one shuffle per *)
(* secret, so it leaves one or two compatible secrets and its posterior       *)
(* entropy is the indicator of that ambiguity. The mutual information between *)
(* the secret and the view is then one minus the census collision ratio,      *)
(* exactly, with no inequality.                                               *)
(*                                                                            *)
(* Everything here holds at every deck pair. The collision counts that turn   *)
(* the ratio into a number are facts of the pair, established in              *)
(* pgl27_encoding_r7.v and pgl27_encoding_r5.v, and the closed forms they     *)
(* give are in pgl27_leakage_r7.v and pgl27_leakage_r5.v.                     *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_noncollision_ratio R e S == one minus the census collision count   *)
(*                                     of S at the deck pair e, over 336      *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_secret_uniform == the dealt orbit secret is uniform on the two     *)
(*     orbit classes                                                          *)
(*   pgl27_reachable_view_entropy_ambiguousE == a reachable coalition view    *)
(*     has posterior entropy equal to the indicator of its ambiguity          *)
(*   pgl27_view_mutual_info_ambiguityE == a coalition with repetition-free    *)
(*     census view lists shares pgl27_noncollision_ratio bits with the orbit  *)
(*     secret                                                                 *)
(*                                                                            *)
(* The statements concern the pre-reveal execution: after the public reveal   *)
(* every player learns the secret by design. The all-decks dealer of          *)
(* pgl27_view_indep_alldecks is not covered.                                  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset fingroup.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import boolp ring lra reals.
From infotheo Require Import realType_ext fdist proba entropy.
From pgg_smc Require Import proba_entropy_ext support_posterior.
From pgg_smc Require Import pgg_interface pgl27_group pgl27_orbit.
From pgg_smc Require Import pgl27_profile pgl27_secrecy pgl27_leakage_census.
From pgg_smc Require Import pgl27_encoding pgl27_view_census.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** The proportion of shuffles whose view of S under one secret is not also a
    view of S under the other, at the deck pair e. When both census view
    lists are repetition-free, it is the probability that one pre-reveal view
    is compatible with only one secret, hence the exact number of bits the
    view carries about the secret. *)
Definition pgl27_noncollision_ratio (R : realType) (e : pgl27_encoding)
    (S : seq nat) : R :=
  1 - (pgl27_collisions (enc_code e) S)%:R / 336%:R.

Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.

(** The support-set source specializes definitionally to the PGL(2,7) source,
    so the generic posterior theorems apply to the protocol's own joint law of
    secret and shuffle. *)
Local Lemma support_posteriorP_pgl27E (R : realType) :
  @support_posteriorP R (pgg_gT pgl27_M) (pgg_G pgl27_M)
    pgl27_G_pos = pgl27P R.
Proof. by []. Qed.

(** The ambiguous views of a coalition are the views the generic posterior
    theory calls ambiguous for the pair of per-secret view maps. It is the
    step that lets the support-posterior results of support_posterior.v speak
    about this scheme. *)
Local Lemma pgl27_ambiguous_viewsE
    (R : realType) (e : pgl27_encoding) (S : seq nat)
    (v : {ffun 'I_8 -> 'I_8}) :
  (v \in pgl27_ambiguous_views R e S) =
  support_ambiguous_view (pgg_G pgl27_M)
    (fun b g => pgl27_enc_view R e (pgl27_code_coalition S) (b, g)) v.
Proof.
by rewrite /pgl27_ambiguous_views /support_ambiguous_view inE.
Qed.

(** A reachable coalition view has one bit of posterior entropy precisely when
    both secrets can produce it, and zero bits otherwise. It is the residual
    uncertainty a coalition retains about the orbit secret after one
    pre-reveal view, and it is an indicator rather than a general quantity
    because the secret is one bit and each secret produces a reachable view at
    most once. *)
Lemma pgl27_reachable_view_entropy_ambiguousE
    (R : realType) (e : pgl27_encoding) (S : seq nat)
    (Hinj : forall b,
      {in pgg_G pgl27_M &,
        injective
          (fun g => pgl27_enc_view R e (pgl27_code_coalition S) (b, g))})
    (v : {ffun 'I_8 -> 'I_8}) :
  `Pr[(pgl27_enc_view R e (pgl27_code_coalition S)) = v] != 0 ->
  `H[(pgl27_secret R) |
     (pgl27_enc_view R e (pgl27_code_coalition S)) = v] =
  (v \in pgl27_ambiguous_views R e S)%:R.
Proof.
move=> Hv.
rewrite pgl27_ambiguous_viewsE.
exact: (@support_posterior_entropy_ambiguousE
  R (pgg_gT pgl27_M) {ffun 'I_8 -> 'I_8}
  (pgg_G pgl27_M) pgl27_G_pos
  (fun b g => pgl27_enc_view R e (pgl27_code_coalition S) (b, g))
  Hinj v Hv).
Qed.

(** The secret marginal of the protocol distribution is uniform on the two
    orbit classes. It fixes the prior entropy of the secret at one bit, which
    is the quantity every coalition's information is measured against. *)
Lemma pgl27_secret_uniform (R : realType) :
  `p_(pgl27_secret R) = fdist_uniform card_bool.
Proof.
rewrite /dist_of_RV /pgl27_secret.
exact: fdist_prod1.
Qed.

(** A coalition whose two census view lists are repetition-free shares with
    the orbit secret exactly the proportion of views that only one secret
    produces. The equality is exact and unconditional on any computational
    assumption, so the leakage of this scheme is a number rather than a bound,
    and the number is fixed by the deck pair through its collision count. *)
Lemma pgl27_view_mutual_info_ambiguityE (R : realType) (e : pgl27_encoding)
    (S : seq nat) :
  all (fun x => (x < 8)%N) S ->
  uniq (code_views (enc_code e) false S) ->
  uniq (code_views (enc_code e) true S) ->
  `I(pgl27_secret R ; pgl27_enc_view R e (pgl27_code_coalition S)) =
  pgl27_noncollision_ratio R e S.
Proof.
move=> HS Hfalse Htrue.
have Hinj : forall b,
    {in pgg_G pgl27_M &,
      injective
        (fun g => pgl27_enc_view R e (pgl27_code_coalition S) (b, g))}.
  case.
  - exact: (@pgl27_conditional_view_inj R e S true HS Htrue).
  - exact: (@pgl27_conditional_view_inj R e S false HS Hfalse).
rewrite /pgl27_noncollision_ratio.
rewrite -(pgl27_ambiguous_probabilityE R HS Hfalse Htrue).
apply: mutual_info_binary_ambiguityE; first exact: pgl27_secret_uniform.
move=> v Hv.
exact: (@pgl27_reachable_view_entropy_ambiguousE R e S Hinj v Hv).
Qed.
