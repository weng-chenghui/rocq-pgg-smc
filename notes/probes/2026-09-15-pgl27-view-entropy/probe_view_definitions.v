From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface pgl27_group pgl27_secrecy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Prenex Implicits.

(** The positions listed by [S] form the coalition whose masked card values
    constitute the protocol observation. *)
Definition pgl27_code_coalition (S : seq nat) : {set 'I_8} :=
  [set i | val i \in S].

(** Reading the positions listed by [S] converts a masked protocol view to
    the sequence representation used by the collision census. *)
Definition pgl27_view_codes
    (S : seq nat) (v : {ffun 'I_8 -> 'I_8}) : seq nat :=
  [seq val (v (inord x)) | x <- S].

(** An ambiguous view is reachable under both orbit-class secrets. Such a
    view leaves the Boolean secret undetermined by the coalition. *)
Definition pgl27_ambiguous_views
    (R : realType) (S : seq nat) : {set {ffun 'I_8 -> 'I_8}} :=
  [set v |
     [exists g in pgg_G pgl27_M,
        pgl27_view R (pgl27_code_coalition S) (false, g) == v] &&
     [exists g in pgg_G pgl27_M,
        pgl27_view R (pgl27_code_coalition S) (true, g) == v]].
