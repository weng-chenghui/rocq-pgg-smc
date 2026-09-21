(* K4(a) of the claim ledger: the reading clause of a certify statement.

   Four rules stand together here: the statement with the reading omitted
   and the statement with of r, each with and without the tightness
   annotation.  The question the file answers is whether they factor, at
   which levels their slots have to sit, and whether the of of a reading
   clause collides with the of of the bind, which is copied from
   pgg_tableau.v into k4_core.v at the same level and associativity.

   Every spelling is parsed and then put against the bind form by
   exact: erefl, so a rule that parsed but reached a different term would
   be caught here and not at the framework. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From surface_mini Require Import k4_core.

Set Implicit Arguments.
Unset Strict Implicit.

(* The tightness annotation in miniature: a number checked against a proof
   and then dropped, as exact_leaks does. *)
Definition annotate (w : Evidence) (k : nat)
    (H : (0 < k)%N = true) : Evidence := w.

(* k occurs in the type of H, so Unset Strict Implicit would infer it and
   the annotation's number would have no slot, exactly as
   Arguments exact_leaks : clear implicits guards against in the real
   file. *)
Arguments annotate : clear implicits.

Notation "s 'certify' 'ExactIndependence' 'by' w" :=
  (s ;;; cert_exact of w)
  (at level 90, left associativity, w at level 0).

Notation "s 'certify' 'ExactIndependence' 'of' r 'by' w" :=
  (s ;;; cert_exact of (at_reading r w))
  (at level 90, left associativity, r at level 0, w at level 0).

Notation "s 'certify' 'ExactIndependence' 'by' w 'leaks' 'at' k 'by' H" :=
  (s ;;; cert_exact of (annotate w k H))
  (at level 90, left associativity, w at level 0, k at level 0, H at level 0,
   only parsing).

Notation "s 'certify' 'ExactIndependence' 'of' r 'by' w 'leaks' 'at' k 'by' H" :=
  (s ;;; cert_exact of (annotate (at_reading r w) k H))
  (at level 90, left associativity, r at level 0, w at level 0, k at level 0,
   H at level 0, only parsing).

Lemma one_pos : (0 < 1)%N = true. Proof. exact: erefl. Qed.

Definition k4a_default : Stage := stage0 certify ExactIndependence by 3.
Definition k4a_reading : Stage := stage0 certify ExactIndependence of 1 by 3.
Definition k4a_default_leaks : Stage :=
  stage0 certify ExactIndependence by 3 leaks at 1 by one_pos.
Definition k4a_reading_leaks : Stage :=
  stage0 certify ExactIndependence of 1 by 3 leaks at 1 by one_pos.

(* The bind's own of still parses beside the four rules. *)
Definition k4a_bind : Stage := stage0 ;;; cert_exact of 3.

Lemma k4a_defaultE : k4a_default = k4a_bind.
Proof. exact: erefl. Qed.

Lemma k4a_readingE :
  k4a_reading = (stage0 ;;; cert_exact of (at_reading 1 3)).
Proof. exact: erefl. Qed.

Lemma k4a_default_leaksE :
  k4a_default_leaks = (stage0 ;;; cert_exact of (annotate 3 1 one_pos)).
Proof. exact: erefl. Qed.

Lemma k4a_reading_leaksE :
  k4a_reading_leaks
  = (stage0 ;;; cert_exact of (annotate (at_reading 1 3) 1 one_pos)).
Proof. exact: erefl. Qed.

(* The reading clause and the omitted one reach different terms, so the
   default is a choice the rule makes and not a coincidence of parsing. *)
Lemma k4a_reading_not_default : k4a_reading <> k4a_default.
Proof. by []. Qed.

(* The omitted reading is the default reading written out. *)
Lemma k4a_default_is_default_reading :
  k4a_default
  = (stage0 ;;; cert_exact of (at_reading default_reading 3)).
Proof. exact: erefl. Qed.
