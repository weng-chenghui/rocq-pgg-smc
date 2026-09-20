(* PROBE, not production. The keyword measurement at the capitalised tokens: *)
(* a file whose Require lines are ssreflect and the probe syntax file,       *)
(* binding Observed and Sampled as identifiers. If either token were         *)
(* reserved as a global keyword by the two new terminal rules, each line     *)
(* below would be a syntax error at that token. Measured in the full         *)
(* environment: the syntax file under test transitively loads the manifest,  *)
(* which is where the two constructors live, and a lexer keyword is global.  *)

From mathcomp Require Import ssreflect.
From belowprobe Require Import t_syntax_two_records.

Definition keyword_check_Observed_binder (Observed : nat) : nat := Observed.
Definition keyword_check_Sampled_binder (Sampled : nat) : nat := Sampled.

Check (fun Observed : nat => Observed).
Check (fun Sampled : nat => Sampled).

Definition Observed : nat := 0.
Definition Sampled : nat := 1.

Check Observed.
Check Sampled.
