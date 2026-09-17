(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_mutual_info: the information a PGL(2,7) coalition view carries about *)
(*                    the orbit secret                                        *)
(*                                                                            *)
(* The dealt orbit secret is a uniform bit and a coalition observes the       *)
(* masked card values at its own positions before the reveal. When the two    *)
(* census view lists of a coalition are repetition-free, every observation    *)
(* that occurs comes from at most one shuffle per secret, so it leaves one or *)
(* two compatible secrets and its posterior entropy is the indicator of that  *)
(* ambiguity. The mutual information between the secret and the view is then  *)
(* one minus the census collision ratio, exactly, with no inequality. At the  *)
(* four representative coalitions this value is five sevenths, eleven         *)
(* fourteenths, twenty-five twenty-eighths and twenty-seven twenty-eighths of *)
(* a bit.                                                                     *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_noncollision_ratio S == one minus the census collision count of S  *)
(*                                 over 336                                   *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_secret_uniform == the dealt orbit secret is uniform on the two     *)
(*     orbit classes                                                          *)
(*   pgl27_reachable_view_entropy_ambiguousE == a reachable coalition view    *)
(*     has posterior entropy equal to the indicator of its ambiguity          *)
(*   pgl27_mutual_info_ambiguityE == a coalition with repetition-free census  *)
(*     view lists shares pgl27_noncollision_ratio bits with the orbit secret  *)
(*   pgl27_mutual_info_harmonicE, pgl27_mutual_info_equianharmonicE,          *)
(*   pgl27_mutual_info_fiveE, pgl27_mutual_info_sixE == that information at   *)
(*     the four representative coalitions, as closed rational values          *)
(*                                                                            *)
(* The statements concern the pre-reveal execution: after the public reveal   *)
(* every player learns the secret by design.                                  *)
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
From pgg_smc Require Import pgl27_view_census.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section pgl27_noncollision_ratio.
Variable R : realType.

(** This quantity is one minus the overlap count between the two 336-entry
    restricted-view lists, normalized by 336. When both lists are injective,
    it is the proportion of views compatible with only one secret. *)
Definition pgl27_noncollision_ratio (S : seq nat) : R :=
  1 - (pgl27_collisions S)%:R / 336%:R.

(** The harmonic four-position representative has complementary collision
    ratio five sevenths. *)
Lemma pgl27_noncollision_ratio_harmonic :
  pgl27_noncollision_ratio rep_harmonic = 5%:R / 7%:R.
Proof.
by rewrite /pgl27_noncollision_ratio pgl27_collisions_harmonic; lra.
Qed.

(** The equianharmonic four-position representative has complementary
    collision ratio eleven fourteenths. *)
Lemma pgl27_noncollision_ratio_equianharmonic :
  pgl27_noncollision_ratio rep_equianharmonic = 11%:R / 14%:R.
Proof.
by rewrite /pgl27_noncollision_ratio pgl27_collisions_equianharmonic; lra.
Qed.

(** The five-position representative has complementary collision ratio
    twenty-five twenty-eighths. *)
Lemma pgl27_noncollision_ratio_five :
  pgl27_noncollision_ratio rep_five = 25%:R / 28%:R.
Proof.
by rewrite /pgl27_noncollision_ratio pgl27_collisions_five; lra.
Qed.

(** The six-position representative has complementary collision ratio
    twenty-seven twenty-eighths. *)
Lemma pgl27_noncollision_ratio_six :
  pgl27_noncollision_ratio rep_six = 27%:R / 28%:R.
Proof.
by rewrite /pgl27_noncollision_ratio pgl27_collisions_six; lra.
Qed.

End pgl27_noncollision_ratio.

Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.

(** The support-set source specializes definitionally to the PGL(2,7) source,
    so the generic posterior theorems apply to the protocol's own joint law of
    secret and shuffle. *)
Lemma support_posteriorP_pgl27E (R : realType) :
  @support_posteriorP R (pgg_gT pgl27_M) (pgg_G pgl27_M)
    pgl27_G_pos = pgl27P R.
Proof. by []. Qed.

Local Lemma pgl27_ambiguous_viewsE
    (R : realType) (S : seq nat) (v : {ffun 'I_8 -> 'I_8}) :
  (v \in pgl27_ambiguous_views R S) =
  support_ambiguous_view (pgg_G pgl27_M)
    (fun b g => pgl27_view R (pgl27_code_coalition S) (b, g)) v.
Proof.
by rewrite /pgl27_ambiguous_views /support_ambiguous_view inE.
Qed.

(** A reachable PGL protocol view has one bit of posterior entropy precisely
    when both secrets can produce it, and zero bits otherwise. It is the
    residual uncertainty a coalition retains about the orbit secret after one
    pre-reveal observation. *)
Lemma pgl27_reachable_view_entropy_ambiguousE
    (R : realType) (S : seq nat)
    (Hinj : forall b,
      {in pgg_G pgl27_M &,
        injective
          (fun g => pgl27_view R (pgl27_code_coalition S) (b, g))})
    (v : {ffun 'I_8 -> 'I_8}) :
  `Pr[(pgl27_view R (pgl27_code_coalition S)) = v] != 0 ->
  `H[(pgl27_secret R) |
     (pgl27_view R (pgl27_code_coalition S)) = v] =
  (v \in pgl27_ambiguous_views R S)%:R.
Proof.
move=> Hv.
rewrite pgl27_ambiguous_viewsE.
exact: (@support_posterior_entropy_ambiguousE
  R (pgg_gT pgl27_M) {ffun 'I_8 -> 'I_8}
  (pgg_G pgl27_M) pgl27_G_pos
  (fun b g => pgl27_view R (pgl27_code_coalition S) (b, g))
  Hinj v Hv).
Qed.

(** Every reachable harmonic four-position view has zero or one bit of
    posterior entropy, according to whether both secrets produce it. *)
Lemma pgl27_reachable_view_entropy_harmonicE (R : realType)
    (v : {ffun 'I_8 -> 'I_8}) :
  `Pr[(pgl27_view R (pgl27_code_coalition rep_harmonic)) = v] != 0 ->
  `H[(pgl27_secret R) |
     (pgl27_view R (pgl27_code_coalition rep_harmonic)) = v] =
  (v \in pgl27_ambiguous_views R rep_harmonic)%:R.
Proof.
apply: pgl27_reachable_view_entropy_ambiguousE.
exact: pgl27_conditional_view_inj_harmonic.
Qed.

(** Every reachable equianharmonic four-position view has zero or one bit of
    posterior entropy, according to whether both secrets produce it. *)
Lemma pgl27_reachable_view_entropy_equianharmonicE (R : realType)
    (v : {ffun 'I_8 -> 'I_8}) :
  `Pr[(pgl27_view R (pgl27_code_coalition rep_equianharmonic)) = v] != 0 ->
  `H[(pgl27_secret R) |
     (pgl27_view R (pgl27_code_coalition rep_equianharmonic)) = v] =
  (v \in pgl27_ambiguous_views R rep_equianharmonic)%:R.
Proof.
apply: pgl27_reachable_view_entropy_ambiguousE.
exact: pgl27_conditional_view_inj_equianharmonic.
Qed.

(** Every reachable five-position view has zero or one bit of posterior
    entropy, according to whether both secrets produce it. *)
Lemma pgl27_reachable_view_entropy_fiveE (R : realType)
    (v : {ffun 'I_8 -> 'I_8}) :
  `Pr[(pgl27_view R (pgl27_code_coalition rep_five)) = v] != 0 ->
  `H[(pgl27_secret R) |
     (pgl27_view R (pgl27_code_coalition rep_five)) = v] =
  (v \in pgl27_ambiguous_views R rep_five)%:R.
Proof.
apply: pgl27_reachable_view_entropy_ambiguousE.
exact: pgl27_conditional_view_inj_five.
Qed.

(** Every reachable six-position view has zero or one bit of posterior
    entropy, according to whether both secrets produce it. *)
Lemma pgl27_reachable_view_entropy_sixE (R : realType)
    (v : {ffun 'I_8 -> 'I_8}) :
  `Pr[(pgl27_view R (pgl27_code_coalition rep_six)) = v] != 0 ->
  `H[(pgl27_secret R) |
     (pgl27_view R (pgl27_code_coalition rep_six)) = v] =
  (v \in pgl27_ambiguous_views R rep_six)%:R.
Proof.
apply: pgl27_reachable_view_entropy_ambiguousE.
exact: pgl27_conditional_view_inj_six.
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
    assumption. *)
Lemma pgl27_mutual_info_ambiguityE (R : realType) (S : seq nat) :
  all (fun x => (x < 8)%N) S ->
  uniq (code_views false S) ->
  uniq (code_views true S) ->
  `I(pgl27_secret R ; pgl27_view R (pgl27_code_coalition S)) =
  pgl27_noncollision_ratio R S.
Proof.
move=> HS Hfalse Htrue.
have Hinj : forall b,
    {in pgg_G pgl27_M &,
      injective
        (fun g => pgl27_view R (pgl27_code_coalition S) (b, g))}.
  case.
  - exact: (@pgl27_conditional_view_inj R S true HS Htrue).
  - exact: (@pgl27_conditional_view_inj R S false HS Hfalse).
rewrite /pgl27_noncollision_ratio.
rewrite -(pgl27_ambiguous_probabilityE R HS Hfalse Htrue).
apply: mutual_info_binary_ambiguityE; first exact: pgl27_secret_uniform.
move=> v Hv.
exact: (@pgl27_reachable_view_entropy_ambiguousE R S Hinj v Hv).
Qed.

(** The harmonic four-position coalition shares five sevenths of a bit with
    the orbit secret. It is the exact leakage of the smallest coalition above
    the privacy threshold in its orbit class. *)
Lemma pgl27_mutual_info_harmonicE (R : realType) :
  `I(pgl27_secret R ;
     pgl27_view R (pgl27_code_coalition rep_harmonic)) = 5%:R / 7%:R.
Proof.
move/andP: pgl27_views_uniq_harmonic => [Hfalse Htrue].
rewrite -pgl27_noncollision_ratio_harmonic.
apply: pgl27_mutual_info_ambiguityE;
  [by vm_compute | exact: Hfalse | exact: Htrue].
Qed.

(** The equianharmonic four-position coalition shares eleven fourteenths of a
    bit with the orbit secret. Its leakage exceeds the harmonic one, so the
    two four-card orbit classes are not interchangeable. *)
Lemma pgl27_mutual_info_equianharmonicE (R : realType) :
  `I(pgl27_secret R ;
     pgl27_view R (pgl27_code_coalition rep_equianharmonic)) =
  11%:R / 14%:R.
Proof.
move/andP: pgl27_views_uniq_equianharmonic => [Hfalse Htrue].
rewrite -pgl27_noncollision_ratio_equianharmonic.
apply: pgl27_mutual_info_ambiguityE;
  [by vm_compute | exact: Hfalse | exact: Htrue].
Qed.

(** The five-position coalition shares twenty-five twenty-eighths of a bit
    with the orbit secret. *)
Lemma pgl27_mutual_info_fiveE (R : realType) :
  `I(pgl27_secret R ;
     pgl27_view R (pgl27_code_coalition rep_five)) = 25%:R / 28%:R.
Proof.
move/andP: pgl27_views_uniq_five => [Hfalse Htrue].
rewrite -pgl27_noncollision_ratio_five.
apply: pgl27_mutual_info_ambiguityE;
  [by vm_compute | exact: Hfalse | exact: Htrue].
Qed.

(** The six-position coalition shares twenty-seven twenty-eighths of a bit
    with the orbit secret. Its leakage is below one bit, so six of the eight
    cards still leave the orbit secret undetermined on some executions. *)
Lemma pgl27_mutual_info_sixE (R : realType) :
  `I(pgl27_secret R ;
     pgl27_view R (pgl27_code_coalition rep_six)) = 27%:R / 28%:R.
Proof.
move/andP: pgl27_views_uniq_six => [Hfalse Htrue].
rewrite -pgl27_noncollision_ratio_six.
apply: pgl27_mutual_info_ambiguityE;
  [by vm_compute | exact: Hfalse | exact: Htrue].
Qed.
