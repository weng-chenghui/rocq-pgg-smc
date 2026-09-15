From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp boolp ring lra reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Prenex Implicits.

Local Definition uneven_view_of (b g : bool) : bool :=
  if b then g else true.

Local Definition uneven_compatible (v : bool) : {set bool} :=
  [set b | [exists g : bool, uneven_view_of b g == v]].

(** Without injectivity, a compatible secret can have a view fibre with more
    than one point, so compatibility alone does not determine the fibre size. *)
Local Lemma injectivity_mutation_witness :
  #|[set g : bool | uneven_view_of false g == true]| !=
    if false \in uneven_compatible true then 1 else 0.
Proof.
have HF : [set g : bool | uneven_view_of false g == true] = [set: bool].
  apply/setP => g.
  by rewrite !inE /uneven_view_of.
rewrite HF cardsT card_bool.
have Hmem : false \in uneven_compatible true.
  rewrite /uneven_compatible inE; apply/existsP.
  by exists false.
by rewrite Hmem.
Qed.

Local Definition absent_view_of (b : bool) (g : unit) : bool := false.

Local Definition absent_compatible (v : bool) : {set bool} :=
  [set b | [exists g : unit, absent_view_of b g == v]].

Local Definition absent_ambiguous (v : bool) : bool :=
  [exists g : unit, absent_view_of false g == v] &&
  [exists g : unit, absent_view_of true g == v].

(** Without reachability, a view can have no compatible secret, so its
    compatible-secret count is neither the one-secret nor two-secret case. *)
Local Lemma reachability_mutation_witness :
  #|absent_compatible true| !=
    if absent_ambiguous true then 2 else 1.
Proof.
have Hempty : absent_compatible true = set0.
  apply/setP => b.
  rewrite !inE /absent_compatible /absent_view_of.
  case: (boolP [exists g : unit, false == true]) => // /existsP[[]].
  by [].
rewrite Hempty cards0 /absent_ambiguous /absent_view_of /=.
have -> : [exists g : unit, false == true] = false.
  case: (boolP [exists g : unit, false == true]) => // /existsP[[]].
  by [].
by [].
Qed.

Print Assumptions injectivity_mutation_witness.
Print Assumptions reachability_mutation_witness.
