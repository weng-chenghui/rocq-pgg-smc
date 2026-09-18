From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_reconstruct Require Import transitivity_privacy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section DealerKernel.

Variables (R : realType) (secretT deckT shuffleT viewT : finType).
Variable secretP : R.-fdist secretT.
Variable delta : secretT -> R.-fdist deckT.
Variable nu : R.-fdist shuffleT.

(** dealer_shuffleP — the joint law of a secret, the deck a dealer lays for
    that secret, and the shuffle applied to the laid deck: the secret is drawn
    from secretP, the deck from delta at the drawn secret, and the shuffle from
    nu independently of both.  Every privacy statement of the development is an
    average over this space, and the order of the three draws is the modelling
    decision it fixes: the deck may depend on the secret, the shuffle may
    not. *)
Definition dealer_shuffleP : R.-fdist (secretT * (deckT * shuffleT)) :=
  secretP `X (fun s => (delta s) `x nu).

(** dealer_shuffle_secret — the secret coordinate of a sample, read as a
    random variable.  It is the quantity a coalition must not learn, and the
    second argument of every independence statement below. *)
Definition dealer_shuffle_secret : {RV dealer_shuffleP -> secretT} :=
  fun u => u.1.

(** dealer_shuffle_view view — what a coalition observes at a sample, for an
    observation function view of the secret, the deck and the shuffle.  Letting
    view read the secret directly is deliberate: independence proved for this
    observation also covers every observation that reaches the secret only
    through the dealt cards, which is the case an instance supplies. *)
Definition dealer_shuffle_view
    (view : secretT -> deckT -> shuffleT -> viewT) :
    {RV dealer_shuffleP -> viewT} :=
  fun u => view u.1 u.2.1 u.2.2.

(** dealer_shufflePE — the pointwise factorization of the joint law into the
    secret prior, the dealer kernel at that secret, and the shuffle law.  It is
    the equation the dealer model is written by, and the form an instance
    needs when it identifies its own sample law with this one. *)
Lemma dealer_shufflePE s d g :
  dealer_shuffleP (s, (d, g)) =
    secretP s * (delta s d * nu g).
Proof. by rewrite /dealer_shuffleP !fdist_prodE. Qed.

(** dealer_shuffle_view_indep — when every secret of positive mass sends the
    pair of deck and shuffle to one and the same law on observations, the
    observation is independent of the secret.  The statement is exact and
    information-theoretic: no computational premise, no approximation.  Its
    premise is the whole of what an instance must supply, and is the point at
    which an instance's counting argument enters the general model. *)
Lemma dealer_shuffle_view_indep
    (view : secretT -> deckT -> shuffleT -> viewT)
    (mu : R.-fdist viewT) :
  (forall s, secretP s != 0 ->
     fdistmap (fun dg => view s dg.1 dg.2) ((delta s) `x nu) = mu) ->
  dealer_shuffleP |= dealer_shuffle_view view _|_ dealer_shuffle_secret.
Proof.
move=> Hview.
rewrite /dealer_shuffleP /dealer_shuffle_view /dealer_shuffle_secret.
apply: (inde_prod_kernel_fst (mu := mu)) => s Hs.
exact: Hview Hs.
Qed.

(** dealer_shuffle_view_indep_of_deck — the same conclusion from a per-deck
    premise: every deck of positive mass is valid, and every valid deck sends
    the shuffle law alone to one law on observations, uniformly in the secret.
    This is the form a transitivity argument produces, where the shuffle already
    erases the secret at each fixed deck.  It is strictly stronger than what
    dealer_shuffle_view_indep needs, so an instance whose symmetry appears only
    after averaging over decks cannot reach its conclusion this way. *)
Lemma dealer_shuffle_view_indep_of_deck
    (valid : secretT -> deckT -> bool)
    (view : secretT -> deckT -> shuffleT -> viewT)
    (mu : R.-fdist viewT) :
  (forall s d, delta s d != 0 -> valid s d) ->
  (forall s d, secretP s != 0 -> valid s d ->
     fdistmap (view s d) nu = mu) ->
  dealer_shuffleP |= dealer_shuffle_view view _|_ dealer_shuffle_secret.
Proof.
move=> Hvalid Hdeck.
apply: (@dealer_shuffle_view_indep view mu) => s Hs.
apply: (@fdistmap_prod_const R deckT shuffleT
          (delta s) (fun _ => nu) viewT
          (fun dg => view s dg.1 dg.2) mu) => d Hd.
by apply: Hdeck => //; exact: Hvalid Hd.
Qed.

End DealerKernel.

Section Mutations.

Variables (R : realType) (secretT deckT shuffleT viewT : finType).
Variable secretP : R.-fdist secretT.
Variable delta : secretT -> R.-fdist deckT.
Variable nu : R.-fdist shuffleT.
Variable view : secretT -> deckT -> shuffleT -> viewT.
Variable x : viewT.
Hypothesis Hmix : forall s, secretP s != 0 ->
  fdistmap (fun dg => view s dg.1 dg.2) ((delta s) `x nu) =
    fdist1 x.

(* Expected failure: a dealer law with no shuffle.  The ascribed type is a law
   on secretT * (deckT * shuffleT), while secretP `X delta is a law on secretT *
   deckT, so the two types do not unify. *)
Fail Definition dealer_shuffleP_missing_shuffle :
    R.-fdist (secretT * (deckT * shuffleT)) :=
  secretP `X delta.

(** dealer_shuffle_view_indep_with_common_law — the positive control for the
    mutation below: with the common mixed law supplied, the same spelling of
    dealer_shuffle_view_indep is the independence statement. *)
Definition dealer_shuffle_view_indep_with_common_law :
  @dealer_shuffleP R secretT deckT shuffleT secretP delta nu
  |= @dealer_shuffle_view R secretT deckT shuffleT viewT secretP delta nu view
     _|_ @dealer_shuffle_secret R secretT deckT shuffleT secretP delta nu :=
  @dealer_shuffle_view_indep R secretT deckT shuffleT viewT secretP delta nu
    view (fdist1 x) Hmix.

(* Expected failure: the common mixed law premise dropped.  Without Hmix the
   term still has the premise as an arrow in its type, so what is ascribed a
   bare independence statement is a function into one. *)
Fail Definition dealer_shuffle_view_indep_without_common_law :
  @dealer_shuffleP R secretT deckT shuffleT secretP delta nu
  |= @dealer_shuffle_view R secretT deckT shuffleT viewT secretP delta nu view
     _|_ @dealer_shuffle_secret R secretT deckT shuffleT secretP delta nu :=
  @dealer_shuffle_view_indep R secretT deckT shuffleT viewT secretP delta nu
    view (fdist1 x).

End Mutations.

Print Assumptions dealer_shufflePE.
Print Assumptions dealer_shuffle_view_indep.
Print Assumptions dealer_shuffle_view_indep_of_deck.
