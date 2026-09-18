From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order boolp reals Rstruct.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface pgl27_group pgl27_orbit.
From pgg_smc Require Import pgl27_profile pgl27_secrecy.
From pgg_smc Require Import psl211_group psl211_alldecks psl211_models.
From pgg_reconstruct Require Import transitivity_privacy.
From general_dealer_law_probe Require Import dealer_kernel_probe.
From general_dealer_law_probe Require Import pgl27_deterministic_bridge.
From general_dealer_law_probe Require Import psl211_alldecks_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

(* Every statement below is the conclusion of a bridge, ascribed at the
   standard real line instead of at an abstract realType.  Nothing is
   re-derived: each proof is one application of the bridge's own theorem. *)
Local Notation Rc := Rdefinitions.R.

(** pgl27_view_indep_at_R — over the standard real line, a coalition of at
    most three card positions has a view of the shuffled deck independent of
    the
    orbit secret, under the exact PGL(2,7) row's law.  This is the statement
    pgl27_secrecy proves at an abstract field, reached here through the dealer
    model, and it witnesses that the model's hypotheses have a solution over a
    field the reader can compute in. *)
Lemma pgl27_view_indep_at_R (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  pgl27P Rc |= pgl27_view Rc C _|_ pgl27_secret Rc.
Proof. exact: (@pgl27_view_indep_via_dealer Rc C). Qed.

(** pgl27_view_indep_alldecks_at_R — the same over the standard real line for
    the dealer that lays a uniform valid deck of the secret's class.  The
    dealer model reaches this one through its per-deck premise, so the
    conclusion is not an artefact of averaging over decks. *)
Lemma pgl27_view_indep_alldecks_at_R (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  alldecksP (fdist_uniform card_bool) pgl27_G_pos
    (R := Rc) pgl27_class_decks_pos
  |= alldecks_view (@pgg_rho pgl27_M) (fdist_uniform card_bool)
       pgl27_G_pos pgl27_class_decks_pos C
  _|_ alldecks_secret (fdist_uniform card_bool) pgl27_G_pos
       pgl27_class_decks_pos.
Proof. exact: (@pgl27_view_indep_alldecks_via_dealer Rc C). Qed.

(** psl211_alldecks_view_indep_at_R — over the standard real line, a
    coalition of at most five of the twelve seats reads card codes
    independent of the chirality, under the PSL(2,11) all-decks dealer.  Here
    the dealer model reaches the conclusion through its mixed-law condition and
    not through its per-deck one, which is the difference from the two PGL rows
    above. *)
Lemma psl211_alldecks_view_indep_at_R (C : {set 'I_12}) :
  (#|C| <= 5)%N ->
  psl211_alldecksP Rc |= (fun u => psl211_alldecks_view C u.1 u.2)
                     _|_ psl211_alldecks_secret Rc.
Proof. exact: (@psl211_alldecks_view_indep_via_dealer Rc C). Qed.

(** psl211_dealerPE_at_R — the dealer model's pointwise factorization at
    the PSL(2,11) data over the standard real line: the mass of one chirality,
    deal and cut is the product of the chirality prior, the deal law and the
    cut law.  It is the paper's dealer equation with every symbol a concrete
    object. *)
Lemma psl211_dealerPE_at_R (b : bool) (d : psl211_deal)
    (g : pgg_gT psl211_M) :
  psl211_dealerP Rc (b, (d, g)) =
  (fdist_uniform card_bool : Rc.-fdist bool) b *
    (psl211_dealer_delta Rc b d * psl211_dealer_nu Rc g).
Proof. by rewrite /psl211_dealerP dealer_shufflePE. Qed.

Print Assumptions pgl27_view_indep_at_R.
Print Assumptions pgl27_view_indep_alldecks_at_R.
Print Assumptions psl211_alldecks_view_indep_at_R.
Print Assumptions psl211_dealerPE_at_R.
