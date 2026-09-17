(* PROBE Q2b (task P0): the no-Fail copy of q2_record's negative claim, so
   the actual error of the direct computation is on the record.  This file is
   EXPECTED TO FAIL to compile. *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From pgg_smc Require Import pgg_interface.
From pgg_smc Require Import pgl27_group pgl27_orbit.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition deck_r5_true : 8.-tuple 'I_8 :=
  [tuple @Ordinal 8 0 isT; @Ordinal 8 1 isT; @Ordinal 8 2 isT;
         @Ordinal 8 4 isT; @Ordinal 8 3 isT; @Ordinal 8 5 isT;
         @Ordinal 8 7 isT; @Ordinal 8 6 isT].

Lemma q2b_direct : orbit_class deck_r5_true = true.
Proof. vm_compute. Show. Abort.

