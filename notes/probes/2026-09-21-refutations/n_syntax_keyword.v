(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* n_syntax_keyword: the keyword cost of the refuting rule, measured in a     *)
(*                   second file (probe, ledger row N7)                       *)
(*                                                                            *)
(* The measured rule of manifest/pgg_tableau_syntax.v says a token of a       *)
(* notation becomes a global keyword when it follows a slot, and stays an     *)
(* identifier when it follows a literal. refute follows the literal |>. This  *)
(* file requires nothing but ssreflect and the rule, and uses refute as a     *)
(* term, as a binder name and as a name to locate.                            *)
(******************************************************************************)

(* Require Import is not transitive in this tree, so the framework file is
   named beside the rule: without it refute is an unknown reference and the
   measurement says nothing about the lexer. *)
From mathcomp Require Import ssreflect.
From refuteprobe Require Import n_framework n_syntax.

(* A term: the constant the framework declares is still lexed as a name. *)
Check refute.

(* A name to locate. *)
Locate refute.

(* A binder name, shadowing the constant inside one statement. *)
Lemma refute_is_a_binder_name (refute : nat) : refute = refute.
Proof. by []. Qed.

(* The other identifiers the rule mentions are slots, not tokens, and the two
   remaining tokens of the rule are |> and by, which
   manifest/pgg_tableau_syntax.v already carries. *)
Check mk_obstruction.
Check obstruction_of.
