From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order boolp reals.
From infotheo Require Import realType_ext fdist proba.

Set Implicit Arguments.
Unset Strict Implicit.
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

End CarrierTransport.

Section Mutation.

Variables (R : realType) (A B TA TB : finType).
Variable P : R.-fdist A.
Variables (f : A -> B) (X : B -> TA) (Y : B -> TB).
Variable Ybad : A -> TB.

(* Expected failure: a reader that is not a composite with f.  The transported
   statement concludes with Y \o f, and Ybad is an unrelated function out of A,
   so the ascribed type does not unify with the type of the transport. *)
Fail Definition inde_RV_fdistmap_bad_reader :
  fdistmap f P |= X _|_ Y -> P |= (X \o f) _|_ Ybad :=
  proj1 (@inde_RV_fdistmap R A B TA TB P f X Y).

End Mutation.

Print Assumptions inde_RV_fdistmap.
