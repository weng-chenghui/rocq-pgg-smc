(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: D_5 Dihedral Instance on 5 Cards                                     *)
(*                                                                            *)
(* Group presentation: <r, s | r^5 = s^2 = 1, s r s^-1 = r^-1>                *)
(*                                                                            *)
(* Two generators on five sheets ('I_5):                                      *)
(*   cycle_r = (0 1 2 3 4)        the 5-cycle rotation, reused from           *)
(*                                  pgg_abelian.ncycle                        *)
(*   cycle_s = (1 4)(2 3)         the reflection fixing 0                     *)
(*                                                                            *)
(* The dihedral group D_5 has order 10 and preserves the cyclic adjacency on  *)
(* 5 positions. It is the natural deck-group choice for the cycle5 protocol   *)
(* where 5 cards are arranged in a cycle and shuffles must preserve cycle     *)
(* adjacency (rotations + reflections of the necklace).                       *)
(*                                                                            *)
(* This file equips the dihedral generators as a [Gen_PGGTypes 1 3] instance, *)
(* which automatically inherits the [isMonodromyRepr] and [hasGenerators] HB  *)
(* mixins from the generic [Gen_PGGTypes] factory in pgg_interface.v.         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop.
From pgg_smc Require Import pgg_interface pgg_abelian.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     D_5 generators on 'I_5                                                *)
(******************************************************************************)

Section cycle5_generators.

Let N := 5%N.

(** cycle_r — the 5-cycle rotation [(0 1 2 3 4)] on 'I_5.
    Kind: instance.
    Why: order-5 rotation, first generator of D_5. Reuses
    [ncycle] from [pgg_abelian.v]. *)
Definition cycle_r : {perm 'I_5} := @ncycle 3.

(** cycle_s — the reflection [(1 4)(2 3)] fixing 0 on 'I_5.
    Kind: instance.
    Why: order-2 involution, second generator of D_5. Together with
    [cycle_r] it satisfies the dihedral relation
    [cycle_s * cycle_r * cycle_s = cycle_r^-1]. *)
Definition cycle_s : {perm 'I_5} :=
  (tperm (@Ordinal 5 1 isT) (@Ordinal 5 4 isT) *
   tperm (@Ordinal 5 2 isT) (@Ordinal 5 3 isT))%g.

(** dihedral_sigmas — generator tuple [(cycle_r, cycle_s)] for D_5.
    Kind: instance.
    Why: 2-element tuple consumed by [Gen_PGGTypes 1 3] to instantiate
    the D_5 deck-group MonodromyReprWithGeneratorType. *)
Definition dihedral_sigmas : 2.-tuple {perm 'I_5} :=
  [tuple cycle_r; cycle_s].

End cycle5_generators.

(******************************************************************************)
(*     Cycle5 deck group via the generic Gen_PGGTypes factory                *)
(******************************************************************************)

(** Cycle5_PGGTypes — D_5 deck-group MonodromyReprWithGeneratorType on 5 cards.
    Kind: instance.
    Why: feeds the rigidity / threshold / dropout pipeline downstream. The
    underlying HB instances [Gen_isMonodromyRepr] and [Gen_hasGenerators]
    are inherited from the generic [Gen_PGGTypes] factory in
    [pgg_interface.v]. The explicit type annotation forces HB to resolve
    the canonical structure at this declaration site, matching the uniform
    pattern used by all other concrete instances in the codebase. *)
Definition Cycle5_PGGTypes : MonodromyReprWithGeneratorType :=
  @Gen_PGGTypes 1 3 dihedral_sigmas.
