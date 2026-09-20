(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* landing_draft_keyword: the keyword measurement for the token Obstruction,  *)
(* 2026-09-21. Requires are ssreflect and the surface alone, as the           *)
(* measurement of Observed and Sampled was taken.                             *)
(******************************************************************************)

From mathcomp Require Import ssreflect.
From refuteprobe Require Import landing_draft_syntax.

(* Obstruction is still a binder name. *)
Definition obstruction_binder_check (Obstruction : nat) : nat := Obstruction.

(* And still an identifier that can be bound at the top level. *)
Definition Obstruction : nat := 0.

(* The nineteen reserved identifiers are unaffected: the token follows the
   literal publish, as Observed and Sampled do. *)
Check Obstruction.
