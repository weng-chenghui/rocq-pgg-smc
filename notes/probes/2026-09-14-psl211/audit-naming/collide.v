(* audit-naming scratch: does a second instance's top-level `orbit_class`
   silently shadow the pgl27 one in the same pgg_smc namespace? *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp reals.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme.

Set Implicit Arguments.

(* Baseline: the pgl27 names are top-level and in scope unqualified. *)
Locate orbit_class.
Locate subset_class.
Locate deck_ok.
Locate heart_set.
Locate is_heart.
Locate orbit_encode.
Locate orbit_valid.
Locate orbit_scheme.
Locate orbit_recon_invariant.

Check orbit_class : 8.-tuple 'I_8 -> bool.
Check orbit_valid : bool -> 8.-tuple 'I_8 -> Prop.

(* Now the psl211 shapes, declared in the same (flat) namespace. *)
Definition is_heart12 (c : 'I_12) : bool := (val c < 6)%N.

Definition deck_ok (sh : 12.-tuple 'I_12) : bool := uniq sh.
Definition heart_set (sh : 12.-tuple 'I_12) : {set 'I_12} :=
  [set i | is_heart12 (tnth sh i)].

(* After the redefinition the pgl27 meaning is unreachable by short name. *)
Locate deck_ok.
Check deck_ok : 12.-tuple 'I_12 -> bool.

(* The eight-card one now needs a qualified name. *)
Check pgl27_orbit.deck_ok : 8.-tuple 'I_8 -> bool.

(* And the pgl27 lemmas that mention it still speak of the old constant,
   so a reader of the file sees two different `deck_ok` in one goal. *)
Check orbit_valid.
Print orbit_valid.
