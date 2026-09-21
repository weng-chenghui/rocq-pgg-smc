(* K4 of the claim ledger, shared miniature.

   Stand-ins for the objects a Tableau statement connects, small enough that
   the grammar questions of the reading clause are answered by this file and
   its siblings alone and do not depend on the framework.  The bind and its
   of are copied from pgg_tableau.v, at the same level and associativity, so
   that a clash between the of of a reading clause and the of of the bind
   would show here.

   Nothing in this file is a claim about security: Stage, Evidence and
   Reading are natural numbers under other names. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.

Definition Stage := nat.
Definition Evidence := nat.
Definition Reading := nat.

Definition stage0 : Stage := 0.

(* The bind of pgg_tableau.v in miniature: a statement f applied to the
   program so far and to its payload. *)
Definition mini_bind (s : Stage) (f : Stage -> Evidence -> Stage)
    (p : Evidence) : Stage := f s p.

Notation "s ;;; f 'of' p" := (mini_bind s f p)
  (at level 90, left associativity).

(* The statement a certify rule expands to. *)
Definition cert_exact (s : Stage) (w : Evidence) : Stage := s + w.

(* The evidence of a certify statement, indexed by the reading it is about.
   In the framework this is the index of the three evidence records; here it
   is enough that the clause of r reaches a slot the elaborated term uses. *)
Definition at_reading (r : Reading) (w : Evidence) : Evidence := r * 10 + w.

(* The default reading, which an omitted of clause means. *)
Definition default_reading : Reading := 0.

(* The obstruction kind, as a constructor with the reading and the number as
   its two arguments. *)
Inductive ObstructionKind :=
  | InputDistinguishabilityObstruction of Reading & nat.

(* A second identifier sharing the same prefix, so that a keyword test can
   tell a reserved token from a reserved prefix. *)
Definition InputDistinguishabilityPropAt (r : Reading) (c : nat) : Prop :=
  (0 < r + c)%N = true.
