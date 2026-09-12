(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop.
From pgg_smc Require Import pgg_interface pgg_raag.

(******************************************************************************)
(* PGG: Path-Graph RAAG Instance                                             *)
(* Commutation graph: the path on T = m+1 vertices, so g_i and g_j are        *)
(* declared to commute exactly when |i-j| >= 2.                               *)
(*                                                                            *)
(* T = m+1 generators acting on N = m+2 card positions, generator i being     *)
(* the adjacent transposition tperm i (i+1).  Generators at distance >= 2     *)
(* have disjoint supports and do commute; adjacent generators do not, which   *)
(* is established here for the pair (0,1) and is what makes the deck group    *)
(* non-abelian.                                                               *)
(*                                                                            *)
(* The deck group spanned by these generators is not the path RAAG.  Adjacent *)
(* transpositions are the Coxeter generators of the symmetric group, so       *)
(* pgg_G is all of Sym('I_(m+2)), and the path RAAG only surjects onto it.    *)
(* What the file supplies is a monodromy realization of the path commutation  *)
(* graph inside {perm 'I_(m+2)}: the generator tuple satisfies the path       *)
(* commutations, which is what the RAAG mixin asks for.  Consequently         *)
(* path_traces_lb bounds the number of trace classes of length-L words below, *)
(* not the number of distinct deck permutations they reach -- traces are      *)
(* counted from the commutation graph alone, and the symmetric group          *)
(* collapses many of them.                                                    *)
(*                                                                            *)
(*   path_gen i == tperm (ordinal i) (ordinal (i+1))                          *)
(*   path_comm i j == |i-j| >= 2                                              *)
(*   path_gen_inj == generators are injective                                 *)
(*   path_gen_comm == generators at path distance >= 2 commute                *)
(*   path_adj_noncommute == generators 0 and 1 do not commute (m >= 1)        *)
(*   path_G_nonabelian == non-abelian for m >= 1 (via gen_nonabelian)         *)
(*   path_traces_lb == 2^L <= n_traces (adjacent pair forms indep set)        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section path_instance.

Variable m : nat.

(* T = m+1 generators acting on N = m+2 card positions: generator i
   transposes positions i and i+1, so T adjacent transpositions need one more
   position than there are of them. *)
Let T := m.+1.
Let N := m.+2.
Let gT : finGroupType := {perm 'I_N}.

(* Lower endpoint i of the i-th path-graph transposition, read as a card
   position.  The generator indices 'I_T sit inside the card positions 'I_N
   by i |-> i, and path_hi carries the same index to i+1. *)
Definition path_lo (i : 'I_T) : 'I_N :=
  Ordinal (ltn_trans (ltn_ord i) (ltnSn _)).

(** Upper endpoint i+1 of the i-th path-graph transposition, as a card
    position.  With path_lo this embeds a vertex of the path into the pair
    of positions that generator moves. *)
Definition path_hi (i : 'I_T) : 'I_N :=
  Ordinal (ltn_ord i : (val i).+1 < N).

(* Generator i is the transposition of the adjacent card positions i and
   i+1.  These are the Coxeter generators of Sym('I_N), so the group they
   span is the whole symmetric group; what the path graph describes is which
   pairs of them commute, not a presentation of that group. *)
Definition path_gen (i : 'I_T) : gT := tperm (path_lo i) (path_hi i).

(* The T = m+1 generators as a tuple: the alphabet a dealer's word is
   written over. *)
Definition path_gen_tuple : T.-tuple gT := gen_tuple_of path_gen.

(** Reading the generator tuple at index i returns path_gen i. *)
Lemma path_gen_tupleE (i : 'I_T) : tnth path_gen_tuple i = path_gen i.
Proof. exact: gen_tuple_ofE. Qed.

(* --- Generator injectivity --- *)

(* Distinct indices give distinct transpositions, since a tperm is determined
   by the pair of positions it moves.  The injectivity half of the RAAG
   mixin: were two generators equal, the alphabet would be smaller than T and
   every trace count below would over-count it. *)
Lemma path_gen_inj : injective path_gen.
Proof.
move=> i j; rewrite /path_gen => /permP Heq.
(* Evaluate at path_lo i: tperm maps i to i+1 *)
have H1 := Heq (path_lo i).
rewrite tpermL in H1.
(* Evaluate at path_hi i: tperm maps i+1 to i *)
have H2 := Heq (path_hi i).
rewrite tpermR in H2.
(* From H1: tperm j (j+1) (i) = i+1
   From H2: tperm j (j+1) (i+1) = i
   The tperm j (j+1) permutation moves exactly {j, j+1}.
   If i is not in {j, j+1}, H1 gives i = i+1, contradiction.
   So i = j or i = j+1. Similarly i+1 = j or i+1 = j+1. *)
have [Hlo_eq | Hne1] := eqVneq (path_lo i) (path_lo j).
  by apply: val_inj; have /= := congr1 val Hlo_eq.
have [Heq1 | Hne2] := eqVneq (path_lo i) (path_hi j).
  (* path_lo i = path_hi j, so val i = (val j).+1 *)
  rewrite -Heq1 tpermR in H1.
  (* Now H1 : path_lo j = path_hi i *)
  exfalso.
  have /= V1 : val i = (val j).+1 := congr1 val Heq1.
  have /= V2 : (val i).+1 = val j := congr1 val H1.
  suff Habs : (val j).+2 = val j.
    by have : val j < (val j).+2 by []; rewrite Habs ltnn.
  by rewrite -V1 V2.
(* i not in {j, j+1}: tperm fixes i, so H1 gives i = i+1, absurd *)
exfalso.
have Hne1' : path_lo j != path_lo i by rewrite eq_sym.
have Hne2' : path_hi j != path_lo i by rewrite eq_sym.
rewrite (tpermD Hne1' Hne2') in H1.
have : path_hi i != path_lo i by rewrite -val_eqE /= gtn_eqF // ltnSn.
by rewrite H1 eqxx.
Qed.

(* --- PGGTypes instance --- *)

Local Notation Path_PGGTypes := (@Gen_PGGTypes m m path_gen_tuple).
Let M_path : MonodromyReprWithGeneratorType := Path_PGGTypes.

(* --- Commutativity relation --- *)

(* The path commutation graph on the generator indices: i and j are declared
   to commute exactly when |i - j| >= 2, written with truncated subtraction
   in both directions so no ordering hypothesis is needed.
   This edge relation is the sole input to the trace count: its cliques give
   the clique polynomial and its independent sets give lower bounds.  It is
   a statement about the graph and not about the group.  The generators do
   satisfy it, by path_gen_comm below, but Sym('I_N) satisfies further relations
   as well, so trace classes counted from this graph bound the number of
   words up to commutation rather than the number of deck permutations
   reached. *)
Definition path_comm : rel 'I_T :=
  fun i j => (1 < (val i - val j) + (val j - val i))%N.

(** The path relation is symmetric.
    One of the two conditions the RAAG mixin puts on a commutation graph:
    it must be undirected, since commutation of two permutations is. *)
Lemma path_comm_sym : symmetric path_comm.
Proof. by move=> i j; rewrite /path_comm addnC. Qed.

(** No index is path-related to itself.
    The mixin's second condition on the graph.  A self-loop would license a
    trace-equivalence swap inside a repeated letter, merging words the count
    has to keep apart. *)
Lemma path_comm_irrefl : irreflexive path_comm.
Proof. by move=> i; rewrite /path_comm subnn. Qed.

(** The path relation unpacked to its numeric content, |i - j| >= 2. *)
Lemma path_comm_dist2 (i j : 'I_T) :
  path_comm i j ->
  (val i - val j) + (val j - val i) >= 2.
Proof. by []. Qed.

(** Symmetric distance at least 2 forces a != b. *)
Lemma path_dist_neq (a b : nat) : (a - b) + (b - a) >= 2 -> a != b.
Proof. by case: (a =P b) => [-> | //]; rewrite subnn. Qed.

(** Symmetric distance at least 2 also forces a != b+1.
    With path_dist_neq this rules out every way the position pairs {i,i+1}
    and {j,j+1} could meet. *)
Lemma path_dist_neqS (a b : nat) : (a - b) + (b - a) >= 2 -> a != b.+1.
Proof.
move=> Hge; apply/eqP => Hab; rewrite Hab in Hge.
have H1 : b.+1 - b = 1 by rewrite subSn ?leqnn // subnn.
have H2 : b - b.+1 = 0 by apply/eqP; rewrite subn_eq0.
by rewrite H1 H2 addn0 in Hge.
Qed.

(** Generators at path distance at least 2 commute in Sym('I_N).
    Distance 2 separates the position pairs {i,i+1} and {j,j+1}, and
    transpositions with disjoint supports commute.  This discharges the
    commutation field of the RAAG mixin, so every relation the path graph
    declares does hold of the permutations, which is what licenses reading
    the trace count of the graph as a count of distinct dealer words. *)
Lemma path_gen_comm : forall i j : 'I_T,
  path_comm i j ->
  (tnth path_gen_tuple i * tnth path_gen_tuple j =
   tnth path_gen_tuple j * tnth path_gen_tuple i)%g.
Proof.
move=> i j Hc; rewrite !path_gen_tupleE /path_gen.
have Hdist := path_comm_dist2 Hc.
have Hdist' : (val j - val i) + (val i - val j) >= 2 by rewrite addnC.
apply: tperm_disjoint_comm; rewrite -val_eqE /=.
- exact: path_dist_neq Hdist.
- exact: path_dist_neqS Hdist.
- by rewrite eq_sym; exact: path_dist_neqS Hdist'.
- by rewrite eqSS; exact: path_dist_neq Hdist.
Qed.

(* --- RAAG instance wrapper lemmas --- *)

(* path_gen_inj restated through the abstract pgg_sigmas accessor, the shape
   the mixin field is stated in. *)
Lemma path_gen_inj_sigmas :
  injective (fun i : 'I_T => tnth (@pgg_sigmas M_path) i).
Proof. by move=> i j; rewrite !path_gen_tupleE; exact: path_gen_inj. Qed.

(** path_gen_comm restated through the abstract pgg_sigmas accessor. *)
Lemma path_gen_comm_sigmas : forall i j : 'I_T,
  path_comm i j ->
  (tnth (@pgg_sigmas M_path) i * tnth (@pgg_sigmas M_path) j =
   tnth (@pgg_sigmas M_path) j * tnth (@pgg_sigmas M_path) i)%g.
Proof. by move=> i j; exact: path_gen_comm. Qed.

(* --- Non-abelianity (via generic) --- *)

(* Generators 0 and 1 fail to commute once m >= 1: their position pairs {0,1}
   and {1,2} share position 1, and the two products disagree there.  This is
   the converse direction of the commutation graph, and the file proves it
   for this pair only: commutation exactly at distance 2 or more is
   established here in one direction generally and in the other at (0,1). *)
Lemma path_adj_noncommute (Hm : 0 < m) :
  let i0 : 'I_T := Ordinal (isT : 0 < T) in
  let i1 : 'I_T := Ordinal (Hm : 1 < T) in
  (path_gen i0 * path_gen i1 != path_gen i1 * path_gen i0)%g.
Proof.
rewrite /=.
set i0 : 'I_T := Ordinal (isT : 0 < T).
set i1 : 'I_T := Ordinal (Hm : 1 < T).
rewrite /path_gen.
apply/eqP => /permP /(_ (path_lo i0)).
rewrite !permM.
have H01 : path_lo i0 != path_lo i1 by rewrite -val_eqE.
have H02 : path_lo i0 != path_hi i1 by rewrite -val_eqE.
have Hne01' : path_lo i1 != path_lo i0 by rewrite eq_sym.
have Hne02' : path_hi i1 != path_lo i0 by rewrite eq_sym.
rewrite (tpermD Hne01' Hne02') !tpermL.
have H_hi0_lo1 : path_hi i0 = path_lo i1 by apply: val_inj.
rewrite H_hi0_lo1 tpermL.
by move/(congr1 val).
Qed.

(** The group spanned by the path generators is non-abelian as soon as
    m >= 1.
    A graph declaring every pair to commute yields the abelian trace count
    'C(L+T-1, T-1), which is polynomial in L.  The failure of commutation at
    one adjacent pair is what leaves room for the exponential lower bound
    below. *)
Lemma path_G_nonabelian : 0 < m ->
  ~~ abelian (pgg_G Path_PGGTypes).
Proof.
move=> Hm.
set i0 : 'I_T := Ordinal (isT : 0 < T).
set i1 : 'I_T := Ordinal (Hm : 1 < T).
have Hij : i0 != i1 by rewrite -val_eqE.
have Hnc : (tnth (@pgg_sigmas M_path) i0 * tnth (@pgg_sigmas M_path) i1 !=
            tnth (@pgg_sigmas M_path) i1 * tnth (@pgg_sigmas M_path) i0)%g.
  by rewrite !path_gen_tupleE; exact: path_adj_noncommute.
exact: (gen_nonabelian Hij Hnc).
Qed.

(* --- Independent set: the adjacent pair {0, 1} --- *)

(* {0, 1} is an independent set of the path graph, its two members being at
   distance 1 and so not declared to commute.  Over an independent set no
   two letters may be swapped past each other, so distinct words over it stay
   in distinct trace classes. *)
Lemma path_indep_pair (Hm : 0 < m) :
  let I : {set 'I_T} := [set Ordinal (isT : 0 < T); Ordinal (Hm : 1 < T)] in
  forall i j : 'I_T, i \in I -> j \in I -> i != j -> ~~ path_comm i j.
Proof.
move=> /= i j; rewrite !inE => /orP [] /eqP -> /orP [] /eqP -> // _ /=;
  rewrite /path_comm /=;
  by rewrite (eqP (subn_eq0 (isT : 0 <= 1))) add0n addn0.
Qed.

(* --- RAAG instance registration --- *)

(* The path instance as a RAAG: the generator tuple, the path graph, its
   symmetry and irreflexivity, and the proofs that the declared commutations
   hold and that distinct indices give distinct generators.  From here the
   generic trace theory of pgg_raag.v applies to this instance. *)
HB.instance Definition Path_isRAAG :=
  @isRAAG0.Build Path_PGGTypes
    path_comm path_comm_sym path_comm_irrefl
    path_gen_comm_sigmas path_gen_inj_sigmas.

(* The same instance seen as a RAAG, the form the trace theory consumes. *)
Let R_path : RAAGType := Path_PGGTypes.

(** For m >= 1 there are at least 2^L trace classes among words of length L.
    The adjacent pair {0,1} is an independent set of the path graph, so no
    reordering relates two distinct words over those two letters and all 2^L
    of them lie in different classes.  The bound is unconditional and
    combinatorial: it counts classes of words modulo the declared
    commutations, so the collapse of the generated group onto Sym('I_N)
    noted in the file header leaves it intact as a statement about traces,
    and equally forbids reading it as a count of distinct deck
    permutations. *)
Lemma path_traces_lb (L : nat) : 0 < m ->
  2 ^ L <= @n_traces R_path L.
Proof.
move=> Hm.
set I : {set 'I_T} := [set Ordinal (isT : 0 < T); Ordinal (Hm : 1 < T)].
have Hcard : #|I| = 2.
  by rewrite cards2 -val_eqE.
rewrite -Hcard.
apply: (@indep_set_traces_lb R_path I L).
move=> i j Hi Hj Hij.
change (~~ path_comm i j).
exact: (@path_indep_pair Hm i j Hi Hj Hij).
Qed.

End path_instance.
