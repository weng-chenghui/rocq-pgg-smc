(* The same question as f1a, with the break taken before the space.

   Result: exit 1, "y is unbound in the notation", the message f1a gives.
   Neither break works, so a notation string occupies one source line
   whatever its length, and the two rules of the landed surface whose
   string passes eighty bytes stand on one line each.  The message is in
   f1b_notation_break_nospace.msg. *)

From mathcomp Require Import ssreflect.

Notation "x 'oneline' 'by' y 'and' 'by' z" := (pair x (pair y z))
  (at level 90, y at level 0, z at level 0).

Definition f1_a := 1 oneline by 2 and by 3.

Notation "x 'broken' 'by' y
    'and' 'by' z" := (pair x (pair y z))
  (at level 90, y at level 0, z at level 0).

Definition f1_b := 1 broken by 2 and by 3.
