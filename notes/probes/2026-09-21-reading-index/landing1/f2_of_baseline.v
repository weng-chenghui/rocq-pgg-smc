(* Does of reserve anything?

   The bind of pgg_tableau.v is s ;;; f 'of' p, so of follows the slot f,
   the position that reserves a token.  The header of the surface says of
   reserves nothing because it is a keyword of Rocq independently of this
   development, and that claim is measured here the way the same claim was
   measured for at and for by: a binder named of, in a file whose only
   Require is ssreflect.  The message is in f2_of_baseline.msg. *)

From mathcomp Require Import ssreflect.

Definition f2_of_binder (of : nat) : nat := of.
