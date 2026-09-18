From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order boolp reals.
From infotheo Require Import realType_ext fdist proba.

Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section CarrierTransport.

Variables (R : realType) (A B TA TB : finType).
Variable P : R.-fdist A.
Variable f : A -> B.
Variable X : B -> TA.
Variable Y : B -> TB.

Lemma inde_RV_fdistmap_pullback :
  fdistmap f P |= X _|_ Y ->
  P |= (X \o f) _|_ (Y \o f).
Proof.
move=> H x y; move: (H x y).
rewrite -!dist_of_RVE /dist_of_RV !fdistmap_comp.
by [].
Qed.

End CarrierTransport.

Section Mutation.

Variables (R : realType) (A B TA TB : finType).
Variable P : R.-fdist A.
Variables (f : A -> B) (X : B -> TA) (Y : B -> TB).
Variable Ybad : A -> TB.

Fail Definition inde_RV_fdistmap_bad_reader :
  fdistmap f P |= X _|_ Y ->
  P |= (X \o f) _|_ Ybad :=
  @inde_RV_fdistmap_pullback R A B TA TB P f X Y.

End Mutation.

Print Assumptions inde_RV_fdistmap_pullback.
