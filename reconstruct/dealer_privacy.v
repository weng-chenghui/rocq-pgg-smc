(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: The Dealer Law and Privacy                                            *)
(*                                                                            *)
(* A privacy statement of this development is an average over three draws: a  *)
(* secret, the deck a dealer lays for that secret, and the shuffle applied to *)
(* the laid deck. This file names that sample space and gives two sufficient  *)
(* conditions on the dealer law under which a coalition's observation is      *)
(* independent of the secret. The conditions are on the dealer, not on the    *)
(* protocol: the shuffle group, the design and the coalition are parameters   *)
(* here, and only the law of the deck given the secret is constrained.        *)
(*                                                                            *)
(* The mixed-law condition asks that every secret of positive mass send the   *)
(* pair of deck and shuffle to one and the same law on observations. The      *)
(* per-deck condition asks more, that every deck of positive mass be valid    *)
(* and every valid deck send the shuffle law alone to one law on              *)
(* observations, uniformly in the secret; it is what a transitivity argument  *)
(* produces and it implies the mixed-law one. An instance whose symmetry      *)
(* appears only after averaging over decks meets the first and not the        *)
(* second.                                                                    *)
(*                                                                            *)
(* An instance keeps its own sample carrier. inde_RV_fdistmap transports an   *)
(* independence statement across a reindexing of the sample space, which      *)
(* moves no mass, so an instance supplies one law equation and two reader     *)
(* equations and reads its own theorem off the model's.                       *)
(*                                                                            *)
(* Section 1 -- dealer_shuffleP, dealer_shuffle_secret, dealer_shuffle_view,  *)
(*   dealer_shufflePE, dealer_shuffle_view_indep,                             *)
(*   dealer_shuffle_view_indep_of_deck == the dealer model and its two        *)
(*   sufficient conditions for privacy.                                       *)
(* Section 2 -- inde_RV_fdistmap == independence transported across a         *)
(*   reindexing of the sample space.                                          *)
(* Section 3 -- fdistmap_prod_sectionE == section-wise equality of laws       *)
(*   lifted to the pair.                                                      *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   dealer_shuffleP        == the joint law of secret, deck and shuffle      *)
(*   dealer_shuffle_secret  == the secret coordinate as a random variable     *)
(*   dealer_shuffle_view    == an observation of all three coordinates        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   dealer_shufflePE       == the pointwise factorization of the joint law   *)
(*   dealer_shuffle_view_indep == a common mixed law implies independence     *)
(*   dealer_shuffle_view_indep_of_deck == a per-deck law and validity imply   *)
(*     independence                                                           *)
(*   inde_RV_fdistmap      == independence transports across a reindexing,    *)
(*     as an equivalence                                                      *)
(*   fdistmap_prod_sectionE == two observations of an independent pair agree  *)
(*     in law as soon as they agree on every section                          *)
(******************************************************************************)

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

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Section dealer_kernel.

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

End dealer_kernel.

Section carrier_transport.

Variables (R : realType) (A B TA TB : finType).
Variable P : R.-fdist A.
Variable f : A -> B.
Variable X : B -> TA.
Variable Y : B -> TB.

(** inde_RV_fdistmap — two observations of a pushed-forward law are
    independent exactly when their composites with the map are independent
    under the law before it.  Reindexing a sample space is not a probabilistic
    step: it changes the coordinates a sample is written in and nothing else,
    so no mass is moved and the equivalence is an equality of the same three
    probabilities read twice.  This is what lets an instance keep its own
    sample carrier while the privacy argument runs on the dealer model's
    carrier. *)
Lemma inde_RV_fdistmap :
  fdistmap f P |= X _|_ Y <-> P |= (X \o f) _|_ (Y \o f).
Proof.
by split => H x y; move: (H x y);
   rewrite -!dist_of_RVE /dist_of_RV !fdistmap_comp.
Qed.

End carrier_transport.

Section product_sections.

Variable R : realType.

(** fdistmap_prod_sectionE — two observations of an independent pair agree in
    law on the pair as soon as they agree in law on every section through a
    section of positive mass.  It is the section form of fdistmap_prod_const,
    with observation in place of a constant target law, and it is what carries
    a per-section count up to the law of the whole sample. *)
Lemma fdistmap_prod_sectionE (D G V : finType)
    (PD : R.-fdist D) (PG : R.-fdist G)
    (f h : D -> G -> V) :
  (forall g, PG g != 0 ->
     fdistmap (fun d => f d g) PD =
     fdistmap (fun d => h d g) PD) ->
  fdistmap (fun dg => f dg.1 dg.2) (PD `x PG) =
  fdistmap (fun dg => h dg.1 dg.2) (PD `x PG).
Proof.
move=> H; apply: fdist_ext => v; rewrite !fdistmapE.
rewrite !(partition_big snd xpredT) //=.
apply: eq_bigr => g _.
rewrite (reindex_onto (fun d : D => (d, g)) (fun i => i.1));
  last by move=> [d g'] /= /andP[_ /eqP ->].
under eq_bigl => d do rewrite /= !inE eqxx andbT.
under eq_bigr => d _ do rewrite fdist_prodE /=.
rewrite [in RHS](reindex_onto (fun d : D => (d, g)) (fun i => i.1));
  last by move=> [d g'] /= /andP[_ /eqP ->].
under [in RHS]eq_bigl => d do rewrite /= !inE eqxx andbT.
under [in RHS]eq_bigr => d _ do rewrite fdist_prodE /=.
under [in LHS]eq_bigl => d do rewrite /= eqxx andbT.
under [in RHS]eq_bigl => d do rewrite /= eqxx andbT.
rewrite -!big_distrl /=.
(* a section of zero mass contributes zero to both sums, so the premise is
   needed only where the second law is supported *)
have [->|Hg] := eqVneq (PG g) 0; first by rewrite !mulr0.
move: (congr1 (fun q : R.-fdist V => q v) (H g Hg)).
rewrite !fdistmapE => Heq; congr (_ * _).
transitivity (\sum_(a in D | a \in preim (f^~ g) (pred1 v)) PD a).
- by apply: eq_bigl => i; rewrite inE.
- by rewrite Heq; apply: eq_bigl => i; rewrite inE.
Qed.

End product_sections.
