(* PROBE, not production. The keyword measurement row T8 asks for: a file     *)
(* whose imports are ssreflect and the syntax file under test, binding the    *)
(* two level tokens as identifiers. If either token were reserved as a global *)
(* keyword by the two new terminal rules, each line below would be a syntax   *)
(* error at that token.                                                       *)

From mathcomp Require Import ssreflect.
From belowprobe Require Import t_syntax.

Definition keyword_check_observed_binder (observed : nat) : nat := observed.
Definition keyword_check_sampled_binder (sampled : nat) : nat := sampled.

Check (fun observed : nat => observed).
Check (fun sampled : nat => sampled).

Definition observed : nat := 0.
Definition sampled : nat := 1.

Check observed.
Check sampled.
