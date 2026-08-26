(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: D_5 Dihedral Instance on 5 Cards                                     *)
(*                                                                            *)
(* Intended presentation: <r, s | r^5 = s^2 = 1, s r s^-1 = r^-1>, the       *)
(* dihedral group of order 10.  The file declares the two generators and     *)
(* registers them; none of these relations, and no statement about the       *)
(* order of the group they span, is discharged in the kernel here.           *)
(*                                                                            *)
(* Two generators on five card positions ('I_5):                             *)
(*   cycle_r = (0 1 2 3 4)        the 5-cycle rotation, reused from           *)
(*                                  pgg_abelian.ncycle                        *)
(*   cycle_s = (1 4)(2 3)         the reflection fixing 0                     *)
(*                                                                            *)
(* D_5 is the symmetry group of a five-card necklace: the shuffles that       *)
(* leave cyclic adjacency intact are exactly the rotations and reflections    *)
(* of the cycle.  A deck group cut down to it is the setting in which a       *)
(* player's observation carries only the position of a card around the        *)
(* cycle, never its absolute index.                                           *)
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

(** Rotation of the five-card necklace: the 5-cycle [(0 1 2 3 4)] on 'I_5,
    carrying position i to i+1 mod 5.  First of the two generators the
    cycle5 deck group is spanned by. *)
Definition cycle_r : {perm 'I_5} := @ncycle 3.

(** Reflection of the five-card necklace: the involution [(1 4)(2 3)] on
    'I_5, fixing position 0.  Second of the two generators, and the reason
    the deck group is bigger than the rotations alone -- a shuffle that
    keeps cards cyclically adjacent may still reverse the sense in which
    the cycle is read. *)
(* Remark, asserted here and proved nowhere in this development: cycle_s
   acts as i |-> -i mod 5, so cycle_s * cycle_r * cycle_s = cycle_r^-1;
   together with cycle_r^5 = cycle_s^2 = 1 that presents the group spanned
   below as D_5, of order 10.  No relation is discharged in the kernel. *)
Definition cycle_s : {perm 'I_5} :=
  (tperm (@Ordinal 5 1 isT) (@Ordinal 5 4 isT) *
   tperm (@Ordinal 5 2 isT) (@Ordinal 5 3 isT))%g.

(** The generator tuple (rotation, reflection) of the cycle5 deck group.
    Two generators is the whole of the dealer's alphabet here: every deck
    permutation a word can reach is a product of rotations and reflections
    of the necklace. *)
Definition dihedral_sigmas : 2.-tuple {perm 'I_5} :=
  [tuple cycle_r; cycle_s].

End cycle5_generators.

(******************************************************************************)
(*     Cycle5 deck group via the generic Gen_PGGTypes factory                *)
(******************************************************************************)

(** The cycle5 deck group as a monodromy representation with generators:
    the subgroup of [{perm 'I_5}] spanned by the rotation and the
    reflection, acting on the five card positions.  Packaging it this way
    is what lets the generic PGG machinery read a dealer's word over the
    two generators as a deck permutation, and read a player's observation
    as an endpoint of that permutation. *)
(* The explicit type annotation forces HB to resolve the canonical
   structure at this declaration site; [Gen_isMonodromyRepr] and
   [Gen_hasGenerators] come from the [Gen_PGGTypes] factory in
   [pgg_interface.v]. *)
Definition Cycle5_PGGTypes : MonodromyReprWithGeneratorType :=
  @Gen_PGGTypes 1 3 dihedral_sigmas.
