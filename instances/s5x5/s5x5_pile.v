(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Pile preservation for the S_5 x S_5 generator tuple                        *)
(*                                                                            *)
(* The eight generators of S_5 x S_5 (four adjacent transpositions on         *)
(* pile-1 = {0..4}, four on pile-2 = {5..9}) all preserve pile-1 setwise.     *)
(* By subgroup closure (astabs is a group), the full generated group          *)
(* pgg_G also preserves pile-1. This discharges the previous                  *)
(* Axiom s5x5_preserves_pile1_ax in rigidity_s5x5_instance.v.                 *)
(*                                                                            *)
(* Proof structure:                                                           *)
(*   1. pile1 := {x : 'I_10 | val x < 5}.                                     *)
(*   2. H := setwise-stabiliser of pile1 under the natural permutation        *)
(*      action ('N(pile1 | 'P)%g). By group_set_astabs, H is a group.         *)
(*   3. Each of the eight generators lies in H: a finite case split on        *)
(*      (gen_index, element_index) = 8 * 10 = 80 cases, each decided by       *)
(*      s5x5_gens_agree + computation.                                        *)
(*   4. By gen_subG, the generated group pgg_G is a subset of H.              *)
(*   5. By astabsP, every g in pgg_G satisfies                                *)
(*      val i < 5 -> val (g i) < 5.                                           *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop.
From pgg_smc Require Import pgg_interface pgg_weval_inj pgg_raag pgg_s5x5.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     Pile preservation lemma                                                *)
(******************************************************************************)

(** [s5x5_pile1_stab] — every element of the generated group [pgg_G] for the
    S_5 x S_5 eight-generator tuple fixes pile-1 (the indices with
    [val i < 5]) setwise under the [pgg_rho] permutation action.  Generator-
    level pile preservation lifts to the whole group because the setwise
    stabiliser of pile-1 is itself a group (astabs). *)
Lemma s5x5_pile1_stab :
  forall g, g \in pgg_G (@Gen_PGGTypes 7 8 s5x5_gen_tuple) ->
  forall i : 'I_10, (val i < 5)%N ->
  (val (@pgg_rho (@Gen_PGGTypes 7 8 s5x5_gen_tuple) g i) < 5)%N.
Proof.
move=> g HgG i Hi.
have Hrho : pgg_rho g i = g i by [].
rewrite Hrho.
pose pile1 := [set x : 'I_10 | (val x < 5)%N].
pose HH := astabs_group (perm_action _) pile1.
have Hgensub : [set tnth s5x5_gen_tuple j | j : 'I_8] \subset HH.
  apply/subsetP => x /imsetP[j _ ->].
  apply/astabsP => y.
  rewrite /= apermE !inE -s5x5_gens_agree.
  by case: j => [[|[|[|[|[|[|[|[|?]]]]]]]] Hj];
     case: y => [[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]] Hy].
have HGsub : pgg_G (@Gen_PGGTypes 7 8 s5x5_gen_tuple) \subset HH.
  rewrite /pgg_G /= gen_subG. exact: Hgensub.
have HginHg : g \in HH by move/subsetP: HGsub => /(_ g HgG).
move/astabsP: HginHg => /(_ i).
rewrite /= apermE !inE Hi.
by move=> ->.
Qed.

(** [s5x5_preserves_pile2_proved] — every element of [pgg_G] also fixes
    pile-2 (the indices with [val i >= 5]) setwise under the [pgg_rho]
    action, the mirror of [s5x5_pile1_stab] on the upper half of ['I_10].
    Together the two lemmas give the pile-decomposition invariance the
    S_5 x S_5 rigidity development needs. *)
Lemma s5x5_preserves_pile2_proved :
  forall g, g \in pgg_G (@Gen_PGGTypes 7 8 s5x5_gen_tuple) ->
  forall i : 'I_10, ~~ (val i < 5)%N ->
  ~~ (val (@pgg_rho (@Gen_PGGTypes 7 8 s5x5_gen_tuple) g i) < 5)%N.
Proof.
move=> g HgG i Hi.
have Hrho : pgg_rho g i = g i by [].
rewrite Hrho.
pose pile2 := [set x : 'I_10 | ~~ (val x < 5)%N].
pose HH := astabs_group (perm_action _) pile2.
have Hgensub : [set tnth s5x5_gen_tuple j | j : 'I_8] \subset HH.
  apply/subsetP => x /imsetP[j _ ->].
  apply/astabsP => y.
  rewrite /= apermE !inE -s5x5_gens_agree.
  by case: j => [[|[|[|[|[|[|[|[|?]]]]]]]] Hj];
     case: y => [[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]] Hy].
have HGsub : pgg_G (@Gen_PGGTypes 7 8 s5x5_gen_tuple) \subset HH.
  rewrite /pgg_G /= gen_subG. exact: Hgensub.
have HginHg : g \in HH by move/subsetP: HGsub => /(_ g HgG).
move/astabsP: HginHg => /(_ i).
rewrite /= apermE !inE Hi.
by move=> ->.
Qed.
