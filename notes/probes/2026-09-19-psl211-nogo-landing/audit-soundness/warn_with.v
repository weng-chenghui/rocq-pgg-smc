(* Audit probe: does the notation-incompatible-prefix warning follow the
   import of infotheo's variation_dist next to mathcomp's fingroup?
   Import prefix copied from instances/psl211/psl211_profile.v lines 26-32. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.

Definition audit_marker_with : nat := 0.
