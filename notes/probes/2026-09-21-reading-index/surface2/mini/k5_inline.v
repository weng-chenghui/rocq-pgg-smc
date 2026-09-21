(* Item 1(a): the obstruction published inline, with its reading and its
   number, measured in a miniature.

   The decided rule is

     s |> publish Obstruction InputDistinguishability of r at c by pf
          assuming a

   and this file declares it beside the three other publish rules, so that
   the factoring question is asked of the four together.  The stand-ins are
   small: a stage is a natural number, a reading is a natural number, a
   proof is a boolean.  The number is not a stand-in: c has the type the
   expansion needs, forall R : realType, R, which is the shape
   ConcludedBound has at manifest/pgg_tableau.v:649 with the option
   dropped, because an obstruction's number is not optional.  The reading
   and the number travel in one record, as the kind's two arguments will.

   Nothing here is a claim about security. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import ssralg reals.

Set Implicit Arguments.
Unset Strict Implicit.

Definition Stage := nat.
Definition Reading := nat.
Definition Proofish := bool.

Definition stage0 : Stage := 0.

Variant TransferStatus := IdealFinite | StaticExecutedOnly.
Variant TransferWithoutTheorem := SampledStaticExecutedOnly.
Variant AssumeStatus := BaselineClassicalOnly.

(* The bind of pgg_tableau.v in miniature, at the same level and
   associativity, and polymorphic in the payload as the real one is. *)
Definition mini_bind (P : Type) (s : Stage) (f : Stage -> P -> Stage)
    (p : P) : Stage := f s p.

Notation "s ;;; f 'of' p" := (mini_bind s f p)
  (at level 90, left associativity).

(* The obstruction kind, with the reading it is about and the number the
   model is distinguishable at, one number per real field. *)
Record ObstructionKind := MkObstructionKind {
  ok_reading : Reading ;
  ok_number  : forall R : realType, R }.

(* k occurs in no other field's type, but ok_number returns an arrow-free
   dependent type and Unset Strict Implicit takes a record for something to
   infer, so the projections are pinned as the real file pins tg_f. *)
Arguments ok_number : clear implicits.

Record Carried := MkCarried { c_kind : ObstructionKind ; c_proof : Proofish }.

Definition mk_obstruction (o : ObstructionKind) (pf : Proofish) : Carried :=
  MkCarried o pf.

Definition publish (a : AssumeStatus) (s : Stage) (t : TransferStatus)
  : Stage := s.
Definition publish_observed (s : Stage) (a : AssumeStatus) : Stage := s.
Definition publish_sampled (a : AssumeStatus) (s : Stage)
    (t : TransferWithoutTheorem) : Stage := s.
Definition publish_obstruction (a : AssumeStatus) (s : Stage)
    (p : Carried) : Stage := s.

Notation "s |> 'publish' t 'assuming' a" := (s ;;; publish a of t)
  (at level 90, left associativity, t at level 0, a at level 0).

Notation "s |> 'publish' 'Observed' 'assuming' a" :=
  (s ;;; publish_observed of a)
  (at level 90, left associativity, a at level 0).

Notation "s |> 'publish' 'Sampled' t 'assuming' a" :=
  (s ;;; publish_sampled a of t)
  (at level 90, left associativity, t at level 0, a at level 0).

Notation "s |> 'publish' 'Obstruction' 'InputDistinguishability' 'of' r 'at' c 'by' pf 'assuming' a" :=
  (s ;;; publish_obstruction a of (mk_obstruction (MkObstructionKind r c) pf))
  (at level 90, left associativity, r at level 0, c at level 0,
   pf at level 0, a at level 0).

(* The number of the PSL(2,11) obstruction has this shape: a term in the
   real field and in nothing else. *)
Definition mini_number : forall R : realType, R := fun R => 1%R.

Definition k5_obstruction : Stage :=
  stage0 |> publish Obstruction InputDistinguishability of 7 at mini_number
            by true assuming BaselineClassicalOnly.

Definition k5_three_payload : Stage :=
  stage0 |> publish IdealFinite assuming BaselineClassicalOnly.

Definition k5_observed : Stage :=
  stage0 |> publish Observed assuming BaselineClassicalOnly.

Definition k5_sampled : Stage :=
  stage0 |> publish Sampled SampledStaticExecutedOnly
            assuming BaselineClassicalOnly.

(* Each rule reaches the bind form it is meant to reach. *)
Lemma k5_obstructionE :
  k5_obstruction
  = (stage0 ;;; publish_obstruction BaselineClassicalOnly
       of (mk_obstruction (MkObstructionKind 7 mini_number) true)).
Proof. exact: erefl. Qed.

Lemma k5_three_payloadE :
  k5_three_payload
  = (stage0 ;;; publish BaselineClassicalOnly of IdealFinite).
Proof. exact: erefl. Qed.

Lemma k5_observedE :
  k5_observed = (stage0 ;;; publish_observed of BaselineClassicalOnly).
Proof. exact: erefl. Qed.

Lemma k5_sampledE :
  k5_sampled
  = (stage0 ;;; publish_sampled BaselineClassicalOnly
       of SampledStaticExecutedOnly).
Proof. exact: erefl. Qed.

(* The reading and the number are readable off the published term. *)
Lemma k5_obstruction_readingE :
  ok_reading (c_kind (mk_obstruction (MkObstructionKind 7 mini_number) true))
  = 7.
Proof. exact: erefl. Qed.
