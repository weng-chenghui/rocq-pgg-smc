(* Does Fail catch the rejection the new surface gives an old spelling?

   Every one of the four spellings the landing removes is refused by the
   parser, and a parse error is raised while the sentence is read, before
   anything of it is executed, so a Fail guard around it may not catch it.
   A miniature with one rule of the same shape asks the question with no
   framework behind it: a keyword between two slots, then a sentence that
   omits the keyword, under a Fail.  A run that prints "The command has
   failed with" and exits 0 would say Fail catches such a rejection, and
   the four boundaries could then be written as Fail sentences in the
   instances' checks files.

   Result: exit 1, the parser's message, and no file.  Fail does not catch
   a parse error, so a spelling the parser refuses cannot be recorded as a
   compiled Fail sentence in any production file.  The message is in
   f0_fail_catches_parse.msg. *)

From mathcomp Require Import ssreflect.

Notation "x 'stepping' 'by' y" := (pair x y)
  (at level 90, y at level 0).

Definition f0_ok := 1 stepping by 2.

Fail Definition f0_no_by := 1 stepping 2.
