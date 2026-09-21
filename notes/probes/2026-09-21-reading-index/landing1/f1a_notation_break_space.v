(* Can a notation string sit on two source lines, broken after a space?

   Two rules of the landed surface are longer than eighty bytes in their
   string alone, and the layout of the tree allows no line over eighty.
   The question is whether the lexer of a notation string takes a newline
   as the whitespace that separates two tokens, so that a long rule may be
   written over two lines and still be the one rule.  Here the break comes
   after a space, the space being the last byte of its line.

   Result: exit 1, "y is unbound in the notation".  The newline is not a
   separator, so the rule the declaration builds is not the rule its text
   spells.  The message is in f1a_notation_break_space.msg. *)

From mathcomp Require Import ssreflect.

Notation "x 'oneline' 'by' y 'and' 'by' z" := (pair x (pair y z))
  (at level 90, y at level 0, z at level 0).

Definition f1_a := 1 oneline by 2 and by 3.

Notation "x 'spaced' 'by' y
    'and' 'by' z" := (pair x (pair y z))
  (at level 90, y at level 0, z at level 0).

Definition f1_c := 1 spaced by 2 and by 3.
