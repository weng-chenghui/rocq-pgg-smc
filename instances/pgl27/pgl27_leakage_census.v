(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_leakage_census: reveal-set census and collision counts of the        *)
(* eight-card PGL(2,7) scheme                                                 *)
(*                                                                            *)
(* The secret of the scheme is the PGL(2,7) orbit class of the four heart     *)
(* positions (pgl27_orbit.v) and a coalition sees the cards at the positions  *)
(* it holds. Two combinatorial data fix what such a coalition observes: the   *)
(* orbit census of the reveal set, which depends on the shuffle group alone,  *)
(* and the number of shuffles that produce the same view under the two decks  *)
(* of a deck pair, which depends on the deck pair too.                        *)
(*                                                                            *)
(* Census. On four-subsets the shuffle group has two orbits, of sizes 42 and  *)
(* 28 (orbit_class_split, subset_class_orbitE). On five-, six- and            *)
(* seven-subsets it has a single orbit, obtained here from 3-, 2- and         *)
(* 1-transitivity by complementation: complementation is equivariant for a    *)
(* permutation, and the complement of a k-subset of the projective line is an *)
(* (8 - k)-subset.                                                            *)
(*                                                                            *)
(* Collisions. A deck pair enters here as its code table, the map from the    *)
(* secret bit to the eight card codes in position order. For a reveal set S,  *)
(* the collision count of a code table is the number of restrictions to S     *)
(* shared by its two decks. Which counts a particular deck pair has, and      *)
(* whether its two view lists repeat an entry, are facts of that pair and are *)
(* established in its own file, pgl27_encoding_r7.v and pgl27_encoding_r5.v.  *)
(* Both are nat-table arithmetic on the 336 tables, as in pgl27_group.v       *)
(* (word_bfs), pgl27_orbit.v (code_bfs) and pgl27_mixing.v (elem_table):      *)
(* PGL(2,7) permutations do not reduce under vm_compute, tables do. The       *)
(* real-valued mutual information read off these counts is computed outside   *)
(* the kernel by pgl_leakage_targets.py.                                      *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_group_table  == the 336 group elements as permutation tables       *)
(*   code_subsets k     == the k-subsets of the eight codes                   *)
(*   code_orbit S       == the orbit of a code subset under the group table   *)
(*   code_views code b S == the restrictions to S of the deck that the code   *)
(*                          table gives to the secret bit b                   *)
(*   pgl27_collisions code S == the number of views of S shared by the two    *)
(*                              decks of the code table                       *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_five_subset_orbitE  == the fifty-six five-subsets form one orbit   *)
(*   pgl27_six_subset_orbitE   == the twenty-eight six-subsets form one orbit *)
(*   pgl27_seven_subset_orbitE == the eight seven-subsets form one orbit      *)
(*   pgl27_orbit_four_cover    == the two four-subset orbits, of sizes 42 and *)
(*                                28, are disjoint and cover the seventy      *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From pgg_smc Require Import pgg_interface.
From pgg_smc Require Import pgl27_group pgl27_recovery.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* -------------------------------------------------------------------------- *)
(* Single orbits on five- and six-subsets, by equivariant complementation.    *)
(* -------------------------------------------------------------------------- *)

(* The image of a complement under a permutation is the complement of the
   image. *)
Local Lemma perm_imsetC (g : {perm 'I_8}) (A : {set 'I_8}) :
  g @: (~: A) = ~: (g @: A).
Proof.
have E (B : {set 'I_8}) : g @: B = (g^-1)%g @^-1: B.
  apply/setP => x; rewrite inE.
  apply/imsetP/idP => [[y yB ->]|Hx]; first by rewrite permK.
  by exists (g^-1 x)%g; rewrite ?permKV.
by rewrite (E (~: A)) (E A) preimsetC.
Qed.

(* A subset of the projective line and its complement have eight elements
   between them. *)
Local Lemma cardsC8 (C : {set 'I_8}) : (#|C| + #|~: C|)%N = 8.
Proof. by rewrite cardsC card_ord. Qed.

(* An n-transitive action on the points is transitive on the n-subsets. *)
Local Lemma ntransitive_subset_orbit (n : nat) (A B : {set 'I_8}) :
  ntransitive n (@pgg_rho pgl27_M @* pgg_G pgl27_M) [set: 'I_8] 'P ->
  #|A| = n -> #|B| = n ->
  exists2 g : pgg_gT pgl27_M, g \in pgg_G pgl27_M & B = g @: A.
Proof.
move=> Htr HA HB.
rewrite /ntransitive pgl27_rho_im in Htr.
have szA : size (enum A) == n by rewrite -cardE HA.
have szB : size (enum B) == n by rewrite -cardE HB.
have dtup (C : {set 'I_8}) (sz : size (enum C) == n) :
    Tuple sz \in n.-dtuple([set: 'I_8]).
  rewrite inE; apply/andP; split; first exact: enum_uniq.
  by apply/subsetP => u _; rewrite inE.
have [g gG Hg] := atransP2 Htr (dtup A szA) (dtup B szB).
have Hval : enum B = [seq g x | x <- enum A].
  by rewrite -[LHS]/(val (Tuple szB)) Hg.
exists g => //; apply/setP => y.
apply/idP/imsetP => [yB|[x xA ->]]; last first.
  by rewrite -mem_enum Hval; apply/mapP; exists x; rewrite // mem_enum.
move: yB; rewrite -mem_enum Hval => /mapP[x xA ->].
by exists x; rewrite // -mem_enum.
Qed.

(** pgl27_five_subset_orbit — any two five-subsets of the projective line are
    shuffle images of one another. The shuffle group is transitive on
    five-subsets. *)
Lemma pgl27_five_subset_orbit (S T : {set 'I_8}) :
  #|S| = 5 -> #|T| = 5 ->
  exists2 g : pgg_gT pgl27_M, g \in pgg_G pgl27_M & T = g @: S.
Proof.
move=> HS HT.
have Hc (C : {set 'I_8}) : #|C| = 5 -> #|~: C| = 3.
  by move=> HC; apply: (@addnI 5); rewrite -{1}HC cardsC8.
have [g gG Hg] :=
  ntransitive_subset_orbit pgl27_3transitive (Hc S HS) (Hc T HT).
by exists g => //; rewrite -[T]setCK Hg perm_imsetC setCK.
Qed.

(** pgl27_six_subset_orbit — any two six-subsets of the projective line are
    shuffle images of one another. The shuffle group is transitive on
    six-subsets. *)
Lemma pgl27_six_subset_orbit (S T : {set 'I_8}) :
  #|S| = 6 -> #|T| = 6 ->
  exists2 g : pgg_gT pgl27_M, g \in pgg_G pgl27_M & T = g @: S.
Proof.
move=> HS HT.
have Hc (C : {set 'I_8}) : #|C| = 6 -> #|~: C| = 2.
  by move=> HC; apply: (@addnI 6); rewrite -{1}HC cardsC8.
have [g gG Hg] :=
  ntransitive_subset_orbit pgl27_2transitive (Hc S HS) (Hc T HT).
by exists g => //; rewrite -[T]setCK Hg perm_imsetC setCK.
Qed.

(** pgl27_seven_subset_orbit — any two seven-subsets of the projective line
    are shuffle images of one another. The shuffle group is transitive on
    seven-subsets. *)
Lemma pgl27_seven_subset_orbit (S T : {set 'I_8}) :
  #|S| = 7 -> #|T| = 7 ->
  exists2 g : pgg_gT pgl27_M, g \in pgg_G pgl27_M & T = g @: S.
Proof.
move=> HS HT.
have Hc (C : {set 'I_8}) : #|C| = 7 -> #|~: C| = 1.
  by move=> HC; apply: (@addnI 7); rewrite -{1}HC cardsC8.
have H1 : ntransitive 1 (@pgg_rho pgl27_M @* pgg_G pgl27_M) [set: 'I_8] 'P :=
  ntransitive_weak (isT : (1 <= 3)%N) pgl27_3transitive.
have [g gG Hg] := ntransitive_subset_orbit H1 (Hc S HS) (Hc T HT).
by exists g => //; rewrite -[T]setCK Hg perm_imsetC setCK.
Qed.

(** pgl27_five_subset_orbitE — the orbit of a five-subset of the projective
    line under the shuffle group is the set of all five-subsets. The
    five-subsets are a single orbit, so no reveal pattern of five positions is
    distinguished from another. *)
Lemma pgl27_five_subset_orbitE (S : {set 'I_8}) :
  #|S| = 5 ->
  orbit 'P^* (pgg_G pgl27_M) S = [set T : {set 'I_8} | #|T| == 5].
Proof.
move=> HS; apply/setP => T; rewrite inE.
apply/orbitP/idP => [[g gG <-]|/eqP HT].
  by rewrite (card_imset _ perm_inj) HS.
by have [g gG ->] := pgl27_five_subset_orbit HS HT; exists g.
Qed.

(** pgl27_six_subset_orbitE — the orbit of a six-subset of the projective line
    under the shuffle group is the set of all six-subsets. The six-subsets are
    a single orbit, so no reveal pattern of six positions is distinguished
    from another. *)
Lemma pgl27_six_subset_orbitE (S : {set 'I_8}) :
  #|S| = 6 ->
  orbit 'P^* (pgg_G pgl27_M) S = [set T : {set 'I_8} | #|T| == 6].
Proof.
move=> HS; apply/setP => T; rewrite inE.
apply/orbitP/idP => [[g gG <-]|/eqP HT].
  by rewrite (card_imset _ perm_inj) HS.
by have [g gG ->] := pgl27_six_subset_orbit HS HT; exists g.
Qed.

(** pgl27_seven_subset_orbitE — the orbit of a seven-subset of the projective
    line under the shuffle group is the set of all seven-subsets. The
    seven-subsets are a single orbit, so no reveal pattern of seven positions
    is distinguished from another. *)
Lemma pgl27_seven_subset_orbitE (S : {set 'I_8}) :
  #|S| = 7 ->
  orbit 'P^* (pgg_G pgl27_M) S = [set T : {set 'I_8} | #|T| == 7].
Proof.
move=> HS; apply/setP => T; rewrite inE.
apply/orbitP/idP => [[g gG <-]|/eqP HT].
  by rewrite (card_imset _ perm_inj) HS.
by have [g gG ->] := pgl27_seven_subset_orbit HS HT; exists g.
Qed.

(* -------------------------------------------------------------------------- *)
(* The group as a table closure, self-validated.                              *)
(* -------------------------------------------------------------------------- *)

(** code_tr — the translation z |-> z + 1 as a table of the eight codes. The
    first PGL(2,7) generator at the code level. *)
Definition code_tr : seq nat := [:: 1; 2; 3; 4; 5; 6; 0; 7].

(** code_sc — the scaling z |-> 3 z as a table of the eight codes. The second
    PGL(2,7) generator at the code level. *)
Definition code_sc : seq nat := [:: 0; 3; 6; 2; 5; 1; 4; 7].

(** code_inv — the inversion z |-> -1 / z as a table of the eight codes. The
    third PGL(2,7) generator at the code level. *)
Definition code_inv : seq nat := [:: 7; 6; 3; 2; 5; 4; 1; 0].

(** code_id — the identity table of the eight codes. The code-level neutral
    element, and the seed the group table closes from. *)
Definition code_id : seq nat := [:: 0; 1; 2; 3; 4; 5; 6; 7].

(** code_gens — the three generator tables. The code-level generating set of
    the shuffle group. *)
Definition code_gens : seq (seq nat) := [:: code_tr; code_sc; code_inv].

(** code_comp — the table of t2 after t1, that is i |-> t2 (t1 i). Composition
    of code tables, the code-level group law. *)
Definition code_comp (t1 t2 : seq nat) : seq nat := [seq nth 0 t2 x | x <- t1].

(* Fueled closure of a table set under right multiplication by the generators.
   The code-level generation of pgl27_group_table. *)
Local Fixpoint code_closure (fuel : nat) (seen : seq (seq nat)) :
    seq (seq nat) :=
  match fuel with
  | 0 => seen
  | f.+1 =>
      let nxt :=
        flatten [seq [seq code_comp t g | g <- code_gens] | t <- seen] in
      let add :=
        foldl (fun acc t => if t \in seen ++ acc then acc else rcons acc t)
              [::] nxt in
      if nilp add then seen else code_closure f (seen ++ add)
  end.

(** pgl27_group_table — the closure of the identity table under the three
    generators, with thirty rounds of fuel. The 336 elements of PGL(2,7) as
    permutation tables of the eight codes. *)
Definition pgl27_group_table : seq (seq nat) := code_closure 30 [:: code_id].

(** pgl27_group_table_size — the table list has 336 entries. The tabulated
    shuffle group has the order of PGL(2,7). *)
Lemma pgl27_group_table_size : size pgl27_group_table = 336.
Proof. by vm_compute. Qed.

(** pgl27_group_table_uniq — the table list repeats no entry. The tabulated
    shuffle group lists each element once, so its size is its cardinality. *)
Lemma pgl27_group_table_uniq : uniq pgl27_group_table.
Proof. by vm_compute. Qed.

(** pgl27_group_table_id — the identity table is listed. The tabulated shuffle
    group contains the neutral element. *)
Lemma pgl27_group_table_id : code_id \in pgl27_group_table.
Proof. by vm_compute. Qed.

(** pgl27_group_table_closed — every listed table composed with every
    generator is listed. The tabulated shuffle group is closed under the
    generators, hence is the group they generate. *)
Lemma pgl27_group_table_closed :
  all (fun t => all (fun g => code_comp t g \in pgl27_group_table) code_gens)
      pgl27_group_table.
Proof. by vm_compute. Qed.

(** pgl27_order_neq_335 — the table list does not have 335 entries. The
    tabulated order is 336 and not the neighbouring 335, so the closure does
    not stop one element short. *)
Lemma pgl27_order_neq_335 : size pgl27_group_table != 335.
Proof. by vm_compute. Qed.

(* -------------------------------------------------------------------------- *)
(* The orbit census on four-, five- and six-subsets, at the code level.       *)
(* -------------------------------------------------------------------------- *)

(* All sublists of a list of codes. The enumeration that code_subsets filters
   by length. *)
Local Fixpoint code_powerset (l : seq nat) : seq (seq nat) :=
  match l with
  | [::] => [:: [::]]
  | x :: l' => let p := code_powerset l' in p ++ [seq x :: s | s <- p]
  end.

(** code_subsets — the sublists of the eight codes that have length k. The
    k-subsets of the projective line, in ascending code form. *)
Definition code_subsets (k : nat) : seq (seq nat) :=
  [seq s <- code_powerset (iota 0 8) | size s == k].

(** code_restrict — the codes that the table t places at the positions S. The
    view of the position set S under the shuffle t. *)
Definition code_restrict (S t : seq nat) : seq nat := [seq nth 0 t x | x <- S].

(** code_image — the image of a code subset under a table, sorted. The action
    of a shuffle on a subset, in ascending code form. *)
Definition code_image (t S : seq nat) : seq nat := sort leq (code_restrict S t).

(** code_orbit — the distinct images of a code subset under the group table.
    The orbit of a subset of the projective line under the shuffle group, in
    ascending code form. *)
Definition code_orbit (S : seq nat) : seq (seq nat) :=
  undup [seq code_image t S | t <- pgl27_group_table].

(** rep_harmonic — the four-subset {0, 1, 2, 3}. The representative of the
    harmonic orbit on four-subsets. *)
Definition rep_harmonic : seq nat := [:: 0; 1; 2; 3].

(** rep_equianharmonic — the four-subset {0, 1, 2, 4}. The representative of
    the equianharmonic orbit. *)
Definition rep_equianharmonic : seq nat := [:: 0; 1; 2; 4].

(** rep_five — the five-subset {0, 1, 2, 3, 4}. The representative of the
    single orbit on five-subsets. *)
Definition rep_five : seq nat := [:: 0; 1; 2; 3; 4].

(** rep_six — the six-subset {0, 1, 2, 3, 4, 5}. The representative of the
    single orbit on six-subsets. *)
Definition rep_six : seq nat := [:: 0; 1; 2; 3; 4; 5].

(** rep_seven — the seven-subset {0, 1, 2, 3, 4, 5, 6}. The representative of
    the single orbit on seven-subsets, the largest reveal set a coalition can
    hold without holding the whole deck. *)
Definition rep_seven : seq nat := [:: 0; 1; 2; 3; 4; 5; 6].

(** pgl27_subsets_four — the projective line has seventy four-subsets. The
    seventy four-subsets are the domain that the harmonic and equianharmonic
    orbits partition. *)
Lemma pgl27_subsets_four : size (code_subsets 4) = 70.
Proof. by vm_compute. Qed.

(** pgl27_subsets_five — the projective line has fifty-six five-subsets. The
    fifty-six five-subsets are the domain that the single five-subset orbit
    exhausts. *)
Lemma pgl27_subsets_five : size (code_subsets 5) = 56.
Proof. by vm_compute. Qed.

(** pgl27_subsets_six — the projective line has twenty-eight six-subsets. The
    twenty-eight six-subsets are the domain that the single six-subset orbit
    exhausts. *)
Lemma pgl27_subsets_six : size (code_subsets 6) = 28.
Proof. by vm_compute. Qed.

(** pgl27_orbit_harmonic_size — the orbit of {0, 1, 2, 3} has 42 elements. The
    harmonic orbit on four-subsets has size 42. *)
Lemma pgl27_orbit_harmonic_size : size (code_orbit rep_harmonic) = 42.
Proof. by vm_compute. Qed.

(** pgl27_orbit_equianharmonic_size — the orbit of {0, 1, 2, 4} has 28
    elements. The equianharmonic orbit on four-subsets has size 28. *)
Lemma pgl27_orbit_equianharmonic_size :
  size (code_orbit rep_equianharmonic) = 28.
Proof. by vm_compute. Qed.

(** pgl27_orbit_four_disjoint — no four-subset lies in both orbits. The
    harmonic and equianharmonic orbits are disjoint. *)
Lemma pgl27_orbit_four_disjoint :
  ~~ has (fun S => S \in code_orbit rep_equianharmonic)
         (code_orbit rep_harmonic).
Proof. by vm_compute. Qed.

(** pgl27_orbit_four_cover — every four-subset lies in one of the two orbits.
    Every four-subset lies in the harmonic or the equianharmonic orbit. *)
Lemma pgl27_orbit_four_cover :
  all (fun S => (S \in code_orbit rep_harmonic)
             || (S \in code_orbit rep_equianharmonic)) (code_subsets 4).
Proof. by vm_compute. Qed.

(** pgl27_orbit_five_size — the orbit of {0, 1, 2, 3, 4} has 56 elements. The
    single orbit on five-subsets has size 56. *)
Lemma pgl27_orbit_five_size : size (code_orbit rep_five) = 56.
Proof. by vm_compute. Qed.

(** pgl27_orbit_five_cover — every five-subset lies in the orbit of {0, 1, 2,
    3, 4}. The five-subsets are a single orbit, at the code level. *)
Lemma pgl27_orbit_five_cover :
  all (fun S => S \in code_orbit rep_five) (code_subsets 5).
Proof. by vm_compute. Qed.

(** pgl27_orbit_six_size — the orbit of {0, 1, 2, 3, 4, 5} has 28 elements.
    The single orbit on six-subsets has size 28. *)
Lemma pgl27_orbit_six_size : size (code_orbit rep_six) = 28.
Proof. by vm_compute. Qed.

(** pgl27_orbit_six_cover — every six-subset lies in the orbit of {0, 1, 2, 3,
    4, 5}. The six-subsets are a single orbit, at the code level. *)
Lemma pgl27_orbit_six_cover :
  all (fun S => S \in code_orbit rep_six) (code_subsets 6).
Proof. by vm_compute. Qed.

(** pgl27_four_not_transitive — some four-subset lies outside the orbit of {0,
    1, 2, 3}. The four-subsets are not a single orbit, unlike the five-subsets
    and the six-subsets. *)
Lemma pgl27_four_not_transitive :
  ~~ all (fun S => S \in code_orbit rep_harmonic) (code_subsets 4).
Proof. by vm_compute. Qed.

(* -------------------------------------------------------------------------- *)
(* The collision count of a reveal set, at a deck pair given as a code table. *)
(* -------------------------------------------------------------------------- *)

(** code_views — for each group element t, the codes that the deck dealt to b
    places at the positions S. The list of views of the reveal set S under the
    secret bit b, one entry per shuffle. *)
Definition code_views (code : bool -> seq nat) (b : bool) (S : seq nat) :
    seq (seq nat) :=
  [seq code_restrict S (code_comp t (code b)) | t <- pgl27_group_table].

(** pgl27_collisions — the number of shuffles whose view of S under the secret
    true is also a view of S under the secret false. It is the cardinality of
    the intersection of the two view sets of the reveal set S whenever the two
    lists are repetition-free, and the count of ambiguous executions a
    coalition holding S can face. *)
Definition pgl27_collisions (code : bool -> seq nat) (S : seq nat) : nat :=
  count (fun v => v \in code_views code false S) (code_views code true S).
