From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_reconstruct Require Import transitivity_privacy.

Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section DealerKernel.

Variables (R : realType) (secretT deckT cutT viewT : finType).
Variable secretP : R.-fdist secretT.
Variable delta : secretT -> R.-fdist deckT.
Variable nu : R.-fdist cutT.

Definition dealer_shuffleP :
    R.-fdist (secretT * (deckT * cutT)) :=
  secretP `X (fun s => (delta s) `x nu).

Definition dealer_secret : {RV dealer_shuffleP -> secretT} :=
  fun u => u.1.

Definition dealer_view
    (view : secretT -> deckT -> cutT -> viewT) :
    {RV dealer_shuffleP -> viewT} :=
  fun u => view u.1 u.2.1 u.2.2.

Lemma dealer_shufflePE s d g :
  dealer_shuffleP (s, (d, g)) =
    secretP s * (delta s d * nu g).
Proof. by rewrite /dealer_shuffleP !fdist_prodE. Qed.

Lemma dealer_view_indep
    (view : secretT -> deckT -> cutT -> viewT)
    (mu : R.-fdist viewT) :
  (forall s, secretP s != 0 ->
     fdistmap (fun dg => view s dg.1 dg.2) ((delta s) `x nu) = mu) ->
  dealer_shuffleP |= dealer_view view _|_ dealer_secret.
Proof.
move=> Hview.
rewrite /dealer_shuffleP /dealer_view /dealer_secret.
apply: (inde_prod_kernel_fst (mu := mu)) => s Hs.
exact: Hview Hs.
Qed.

Lemma dealer_view_indep_of_deck
    (valid : secretT -> deckT -> bool)
    (view : secretT -> deckT -> cutT -> viewT)
    (mu : R.-fdist viewT) :
  (forall s d, delta s d != 0 -> valid s d) ->
  (forall s d, secretP s != 0 -> valid s d ->
     fdistmap (view s d) nu = mu) ->
  dealer_shuffleP |= dealer_view view _|_ dealer_secret.
Proof.
move=> Hvalid Hdeck; apply: dealer_view_indep => s Hs.
apply: (@fdistmap_prod_const R deckT cutT
          (delta s) (fun _ => nu) viewT
          (fun dg => view s dg.1 dg.2) mu) => d Hd.
by apply: Hdeck => //; exact: Hvalid Hd.
Qed.

End DealerKernel.

Section Mutations.

Variables (R : realType) (secretT deckT cutT viewT : finType).
Variable secretP : R.-fdist secretT.
Variable delta : secretT -> R.-fdist deckT.
Variable nu : R.-fdist cutT.
Variable view : secretT -> deckT -> cutT -> viewT.
Variable x : viewT.

Fail Definition dealer_shuffleP_missing_cut :
    R.-fdist (secretT * (deckT * cutT)) :=
  secretP `X delta.

Fail Definition dealer_view_indep_without_common_law :
  @dealer_shuffleP R secretT deckT cutT secretP delta nu
  |= @dealer_view R secretT deckT cutT viewT secretP delta nu view
     _|_ @dealer_secret R secretT deckT cutT secretP delta nu :=
  dealer_view_indep (view := view) (mu := fdist1 x).

End Mutations.

Print Assumptions dealer_shufflePE.
Print Assumptions dealer_view_indep.
Print Assumptions dealer_view_indep_of_deck.
