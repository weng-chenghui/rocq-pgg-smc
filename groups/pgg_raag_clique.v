(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop binomial.
From pgg_smc Require Import pgg_raag.

(******************************************************************************)
(* PGG: Clique Polynomial of the RAAG Commutation Graph                      *)
(*                                                                            *)
(* In trace monoid theory (Cartier-Foata), the number of traces of length L   *)
(* is determined by the clique polynomial of the commutation graph:           *)
(*                                                                            *)
(*   P_Gamma(z) = Sum_{k=0}^{alpha} (-1)^k c_k z^k                          *)
(*                                                                            *)
(* where c_k = number of k-cliques.  The generating function for traces is:  *)
(*   Sum_L m_L z^L = 1 / P_Gamma(z)                                          *)
(*                                                                            *)
(* This gives the recurrence:                                                 *)
(*   m_0 = 1                                                                  *)
(*   m_L = Sum_{k=1}^{min(L,alpha)} (-1)^{k+1} c_k m_{L-k}                  *)
(*       = Sum_{k odd} c_k m_{L-k} - Sum_{k even, k>=2} c_k m_{L-k}         *)
(*                                                                            *)
(* Part 1: Nat-level clique enumeration (for vm_compute)                      *)
(*   subseqs_k k s == all subsequences of s of size k (strictly increasing    *)
(*                    order inherited from s)                                  *)
(*   all_pairs_comm_sorted comm s == all pairs pairwise commute or are equal  *)
(*   cliques_of_size Tg k comm == k-cliques in the commutation graph         *)
(*   clique_count Tg k comm == c_k = number of k-cliques                     *)
(*                                                                            *)
(* Part 2: Clique recurrence for trace counts                                *)
(*   clique_step Tg comm memo == one step of the clique recurrence           *)
(*   clique_traces Tg L comm == m_L computed via the clique recurrence       *)
(*                                                                            *)
(* Part 3: vm_compute verification for concrete instances                     *)
(*   star, free, abelian, path graphs                                         *)
(*                                                                            *)
(* Part 4: Growth rate formulas                                               *)
(*   clique_traces_free : free case gives Tg^L                               *)
(*   clique_traces_abelian : abelian case gives C(L+Tg-1, Tg-1)             *)
(*                                                                            *)
(* Part 5: Cross-checks against the abstract trace count                      *)
(*   clique_traces Tg L comm = n_traces_natB Tg L comm is the Cartier-Foata   *)
(*   theorem for a symmetric irreflexive comm.  It is proved as               *)
(*   cartier_foata in legacy/groups/pgg_raag_cartier_foata.v, which imports   *)
(*   this file, so it is not available here; this part holds vm_compute       *)
(*   evidence pinning the two sides against each other at the graphs and      *)
(*   lengths this development uses.                                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Part 1: Nat-level clique enumeration                                       *)
(* ========================================================================== *)

(* Every length-k subsequence of s, in the order s lists them.  Applied to
   iota 0 Tg it enumerates the k-element vertex sets of the commutation
   graph, each sorted, which is where the clique search starts. *)
Fixpoint subseqs_k (k : nat) (s : seq nat) : seq (seq nat) :=
  match k with
  | 0 => [:: [::]]
  | k'.+1 =>
    match s with
    | [::] => [::]
    | x :: s' =>
      (* either include x (and choose k' from s') or skip x *)
      [seq x :: t | t <- subseqs_k k' s'] ++ subseqs_k k'.+1 s'
    end
  end.

(* All elements of s pairwise commute, an element being allowed to meet
   itself.  On a duplicate-free s this is exactly the condition that s spans
   a clique of the commutation graph. *)
Definition all_pairs_comm_sorted (comm : nat -> nat -> bool) (s : seq nat)
    : bool :=
  all (fun i =>
    all (fun j => (i == j) || comm i j) s) s.

(* The k-cliques of the commutation graph: the k-element subsets of the
   generator indices all of whose pairs commute.  A clique is a set of
   generators that may be freely reordered among themselves, which is why the
   Cartier-Foata count depends on the graph only through these. *)
Definition cliques_of_size (Tg k : nat) (comm : nat -> nat -> bool)
    : seq (seq nat) :=
  [seq s <- subseqs_k k (iota 0 Tg)
  | all_pairs_comm_sorted comm s].

(* c_k, the number of k-cliques: the k-th coefficient of the clique
   polynomial P(z) = sum_k (-1)^k c_k z^k. *)
Definition clique_count (Tg k : nat) (comm : nat -> nat -> bool) : nat :=
  size (cliques_of_size Tg k comm).

(* ========================================================================== *)
(* Part 2: Clique recurrence for trace counts                                 *)
(* ========================================================================== *)

(* One step of the recurrence that 1/P(z) imposes on the trace counts:
   m_L = sum_{k=1}^{min(L,Tg)} (-1)^{k+1} c_k m_{L-k}, read off the memo
   table of earlier values.
   Since nat has no subtraction below zero, the alternating sum is split into
   its odd-k part and its even-k part and the difference taken at the end.
   That difference is the intended value only when the odd part dominates,
   which the Cartier-Foata theorem guarantees but nothing in this definition
   enforces. *)

Definition clique_step (Tg : nat) (comm : nat -> nat -> bool)
    (memo : seq nat) : nat :=
  let L := size memo in
  let pos := sumn [seq clique_count Tg k comm * nth 0 memo (L - k)
                   | k <- iota 1 L & odd k] in
  let neg := sumn [seq clique_count Tg k comm * nth 0 memo (L - k)
                   | k <- iota 1 L & ~~ odd k] in
  pos - neg.

(* Extend a memo table [m_0, ..., m_j] by one entry per unit of fuel.  The
   recurrence reaches back up to Tg steps, so the whole table has to be
   carried rather than a fixed window. *)
Fixpoint clique_traces_aux (Tg : nat) (comm : nat -> nat -> bool)
    (fuel : nat) (memo : seq nat) : seq nat :=
  match fuel with
  | 0 => memo
  | fuel'.+1 =>
    let mL := clique_step Tg comm memo in
    clique_traces_aux Tg comm fuel' (rcons memo mL)
  end.

(* The number of traces of length L predicted by the clique polynomial of the
   commutation graph.
   This is a count computed from the graph alone, with no word ever
   enumerated.  Its agreement with the enumerative count n_traces_natB is the
   Cartier-Foata theorem, and it is what makes trace counts tractable at
   lengths where enumerating Tg^L words is not. *)
Definition clique_traces (Tg L : nat) (comm : nat -> nat -> bool) : nat :=
  nth 0 (clique_traces_aux Tg comm L [:: 1]) L.

(* ========================================================================== *)
(* Part 3: vm_compute verification for concrete instances                     *)
(* ========================================================================== *)

(* --- Star graph with m leaves: center 0 commutes with leaves 1..m --- *)

(* Generator 0 commutes with every other generator and no two others commute:
   the star K_{1,m}.  Its cliques are the empty set, the m+1 vertices and the
   m centre-leaf edges, so P(z) = 1 - (m+1)z + m z^2. *)
Definition star_comm_nat (m : nat) (i j : nat) : bool :=
  ((i == 0) || (j == 0)) && (i != j).

(* --- Complete graph: all distinct pairs commute --- *)

(* Every pair of distinct generators commutes: the abelian extreme, whose
   k-cliques are all 'C(Tg,k) vertex subsets and whose clique polynomial is
   (1-z)^Tg. *)
Definition complete_comm_nat (i j : nat) : bool := i != j.

(* --- Path graph on Tg generators: |i-j| >= 2 --- *)

(* Generators commute exactly when their indices differ by at least 2: the
   commutation graph of the adjacent transpositions realised in
   pgg_raag_path.v. *)
Definition path_comm_nat (i j : nat) : bool :=
  (2 <= (maxn i j - minn i j)) && (i != j).

(* ---- Clique counts for star K_{1,3} (4 generators) ---- *)

(* The empty set, the four vertices, and the three centre-leaf edges are all
   the cliques: no triangle exists because no two leaves commute.  So
   P(z) = 1 - 4z + 3z^2 = (1-z)(1-3z). *)
Lemma star3_cc0 : clique_count 4 0 (star_comm_nat 3) = 1.
Proof. by vm_compute. Qed.

Lemma star3_cc1 : clique_count 4 1 (star_comm_nat 3) = 4.
Proof. by vm_compute. Qed.

Lemma star3_cc2 : clique_count 4 2 (star_comm_nat 3) = 3.
Proof. by vm_compute. Qed.

Lemma star3_cc3 : clique_count 4 3 (star_comm_nat 3) = 0.
Proof. by vm_compute. Qed.

Lemma star3_cc4 : clique_count 4 4 (star_comm_nat 3) = 0.
Proof. by vm_compute. Qed.

(* ---- Clique counts for complete graph on 3 generators ---- *)

(* Every vertex subset of K_3 is a clique, so c_k = 'C(3,k) = 1, 3, 3, 1 and
   P(z) = (1-z)^3. *)
Lemma complete3_cc0 : clique_count 3 0 complete_comm_nat = 1.
Proof. by vm_compute. Qed.

Lemma complete3_cc1 : clique_count 3 1 complete_comm_nat = 3.
Proof. by vm_compute. Qed.

Lemma complete3_cc2 : clique_count 3 2 complete_comm_nat = 3.
Proof. by vm_compute. Qed.

Lemma complete3_cc3 : clique_count 3 3 complete_comm_nat = 1.
Proof. by vm_compute. Qed.

(* ---- Clique counts for empty graph on 3 generators ---- *)

(* With no edges the only cliques are the empty set and the three vertices,
   so P(z) = 1 - 3z and 1/P(z) is the generating function of 3^L. *)
Lemma empty3_cc0 : clique_count 3 0 (fun _ _ => false) = 1.
Proof. by vm_compute. Qed.

Lemma empty3_cc1 : clique_count 3 1 (fun _ _ => false) = 3.
Proof. by vm_compute. Qed.

Lemma empty3_cc2 : clique_count 3 2 (fun _ _ => false) = 0.
Proof. by vm_compute. Qed.

(* ---- Clique counts for path on 3 generators ---- *)

(* On three generators the only commuting pair is {0,2}, so the cliques are
   the empty set, three vertices and one edge, and P(z) = 1 - 3z + z^2. *)
Lemma path3_cc0 : clique_count 3 0 path_comm_nat = 1.
Proof. by vm_compute. Qed.

Lemma path3_cc1 : clique_count 3 1 path_comm_nat = 3.
Proof. by vm_compute. Qed.

Lemma path3_cc2 : clique_count 3 2 path_comm_nat = 1.
Proof. by vm_compute. Qed.

Lemma path3_cc3 : clique_count 3 3 path_comm_nat = 0.
Proof. by vm_compute. Qed.

(* ---- Trace counts: star K_{1,3} ---- *)

(* P(z) = (1-z)(1-3z) gives 1/P(z) = sum_L ((3^{L+1}-1)/2) z^L, so the trace
   counts run 1, 4, 13, 40: a coalition facing four generators with a star
   commutation graph searches 40 classes at length 3 rather than the 64 words.
   The predicted values, from the clique polynomial. *)
Lemma star3_ct0 : clique_traces 4 0 (star_comm_nat 3) = 1.
Proof. by vm_compute. Qed.

Lemma star3_ct1 : clique_traces 4 1 (star_comm_nat 3) = 4.
Proof. by vm_compute. Qed.

Lemma star3_ct2 : clique_traces 4 2 (star_comm_nat 3) = 13.
Proof. by vm_compute. Qed.

Lemma star3_ct3 : clique_traces 4 3 (star_comm_nat 3) = 40.
Proof. by vm_compute. Qed.

(* The same four numbers obtained by enumerating words and counting distinct
   normal forms, with no clique polynomial involved.  Agreement of the two
   columns is Cartier-Foata at these lengths. *)
Lemma star3_ntB0 : n_traces_natB 4 0 (star_comm_nat 3) = 1.
Proof. by vm_compute. Qed.

Lemma star3_ntB1 : n_traces_natB 4 1 (star_comm_nat 3) = 4.
Proof. by vm_compute. Qed.

Lemma star3_ntB2 : n_traces_natB 4 2 (star_comm_nat 3) = 13.
Proof. by vm_compute. Qed.

Lemma star3_ntB3 : n_traces_natB 4 3 (star_comm_nat 3) = 40.
Proof. by vm_compute. Qed.

(* ---- Trace counts: free group (3 generators) ---- *)

(* No edges means no word may be reordered, so each class is a single word and
   the counts are 3^L.  The free extreme, where the trace count gives a
   coalition no reduction at all. *)
Lemma free3_ct0 : clique_traces 3 0 (fun _ _ => false) = 1.
Proof. by vm_compute. Qed.

Lemma free3_ct1 : clique_traces 3 1 (fun _ _ => false) = 3.
Proof. by vm_compute. Qed.

Lemma free3_ct2 : clique_traces 3 2 (fun _ _ => false) = 9.
Proof. by vm_compute. Qed.

Lemma free3_ct3 : clique_traces 3 3 (fun _ _ => false) = 27.
Proof. by vm_compute. Qed.

(* The enumerative count agrees at L = 2. *)
Lemma free3_ntB2 : n_traces_natB 3 2 (fun _ _ => false) = 9.
Proof. by vm_compute. Qed.

(* ---- Trace counts: abelian (3 generators) ---- *)

(* Everything commutes, so a class is a multiset of L letters and the counts
   are 'C(L+2,2) = 1, 3, 6, 10.  Polynomial in L against the free case's 3^L:
   the abelian extreme is where a commutation graph gives a coalition the
   most. *)
Lemma abelian3_ct0 : clique_traces 3 0 complete_comm_nat = 1.
Proof. by vm_compute. Qed.

Lemma abelian3_ct1 : clique_traces 3 1 complete_comm_nat = 3.
Proof. by vm_compute. Qed.

Lemma abelian3_ct2 : clique_traces 3 2 complete_comm_nat = 6.
Proof. by vm_compute. Qed.

Lemma abelian3_ct3 : clique_traces 3 3 complete_comm_nat = 10.
Proof. by vm_compute. Qed.

(* The enumerative count agrees at L = 2 and L = 3. *)
Lemma abelian3_ntB2 : n_traces_natB 3 2 complete_comm_nat = 6.
Proof. by vm_compute. Qed.

Lemma abelian3_ntB3 : n_traces_natB 3 3 complete_comm_nat = 10.
Proof. by vm_compute. Qed.

(* ---- Trace counts: path (3 generators) ---- *)

(* P(z) = 1 - 3z + z^2 makes the counts satisfy m_L = 3 m_{L-1} - m_{L-2},
   giving 1, 3, 8, 21, with growth rate (3+sqrt 5)/2, strictly between the
   abelian polynomial and the free 3^L. *)
Lemma path3_ct0 : clique_traces 3 0 path_comm_nat = 1.
Proof. by vm_compute. Qed.

Lemma path3_ct1 : clique_traces 3 1 path_comm_nat = 3.
Proof. by vm_compute. Qed.

Lemma path3_ct2 : clique_traces 3 2 path_comm_nat = 8.
Proof. by vm_compute. Qed.

Lemma path3_ct3 : clique_traces 3 3 path_comm_nat = 21.
Proof. by vm_compute. Qed.

(* The enumerative count agrees at L = 2 and L = 3. *)
Lemma path3_ntB2 : n_traces_natB 3 2 path_comm_nat = 8.
Proof. by vm_compute. Qed.

Lemma path3_ntB3 : n_traces_natB 3 3 path_comm_nat = 21.
Proof. by vm_compute. Qed.

(* ========================================================================== *)
(* Part 4: Growth rate formulas                                               *)
(* ========================================================================== *)

(* --- Helper lemma: size of elements in subseqs_k --- *)

(* Everything subseqs_k k enumerates has length k. *)
Lemma subseqs_k_size k s t : t \in subseqs_k k s -> size t = k.
Proof.
elim: s k t => [|a s IHs] [|k] t //=.
- by rewrite mem_seq1 => /eqP ->.
- by rewrite mem_seq1 => /eqP ->.
- rewrite mem_cat => /orP [/mapP [t' Ht' ->] | Ht].
  + by rewrite /= (IHs _ _ Ht').
  + exact: IHs Ht.
Qed.

(* --- Empty graph: clique_count Tg 0 = 1, clique_count Tg 1 = Tg --- *)

(** Filtering a singleton by a predicate its element satisfies keeps it. *)
Lemma filter_pred1T (T : Type) (p : pred T) (x : T) :
  p x -> [seq s <- [:: x] | p s] = [:: x].
Proof. by move=> /= ->. Qed.

(** The empty set is a clique of any graph. *)
Lemma all_pairs_comm_nil comm : all_pairs_comm_sorted comm [::] = true.
Proof. by []. Qed.

(** The empty sequence is the only subsequence of length 0. *)
Lemma subseqs_k0 s : subseqs_k 0 s = [:: [::]].
Proof. by case: s. Qed.

(** Every commutation graph has exactly one 0-clique.
    c_0 = 1 is the constant term of the clique polynomial, which is what makes
    P(z) invertible as a power series and the recurrence solvable for m_L. *)
Lemma clique_count0 Tg comm : clique_count Tg 0 comm = 1.
Proof.
by rewrite /clique_count /cliques_of_size subseqs_k0
           (filter_pred1T (all_pairs_comm_nil comm)).
Qed.

(** The length-1 subsequences of s are the singletons of its elements. *)
Lemma subseqs_k1 s : subseqs_k 1 s = [seq [:: x] | x <- s].
Proof.
elim: s => [|a s IH] //=.
by rewrite subseqs_k0 /= IH.
Qed.

(** The edgeless graph on Tg vertices has Tg singleton cliques.
    The coefficient c_1 = Tg, which with c_k = 0 for k >= 2 makes P(z) = 1-Tgz
    and the recurrence collapse to m_L = Tg m_{L-1}. *)
Lemma empty_clique_count1 Tg :
  clique_count Tg 1 (fun _ _ => false) = Tg.
Proof.
rewrite /clique_count /cliques_of_size subseqs_k1.
rewrite (eq_in_filter (a2 := predT)); first by rewrite filter_predT size_map size_iota.
by move=> s /mapP [x _ ->]; rewrite /all_pairs_comm_sorted /= eqxx.
Qed.

(** Everything subseqs_k enumerates really is a subsequence of s, so entries
    of a clique are vertices of the graph and a clique inherits
    duplicate-freeness from iota. *)
Lemma subseqs_k_subseq k s t : t \in subseqs_k k s -> subseq t s.
Proof.
elim: s k t => [|a s IHs] [|k] t //=.
- by rewrite mem_seq1 => /eqP ->.
- by rewrite mem_seq1 => /eqP ->.
- rewrite mem_cat => /orP [/mapP [t' Ht' ->] | Ht].
  + by rewrite /= eqxx; exact: IHs Ht'.
  + exact: subseq_trans (IHs _ _ Ht) (subseq_cons _ _).
Qed.

(** Every length-k subsequence of s is enumerated: completeness of the clique
    search. *)
Lemma mem_subseqs_k k s t :
  subseq t s -> size t = k -> t \in subseqs_k k s.
Proof.
elim: s k t => [|a s IHs] [|k] t.
- by rewrite subseq0 => /eqP ->.
- by rewrite subseq0 => /eqP ->.
- move=> _ /size0nil ->.
  by rewrite subseqs_k0 mem_seq1.
- case: t => [// | b t] /=.
  case Hba : (b == a) => Hsub [Hsz].
  + (* b = a: (b :: t) \in subseqs_k k.+1 (a :: s) via left *)
    (* Hsub : subseq t s, Hsz : size t = k *)
    rewrite mem_cat; apply/orP; left; apply/mapP.
    have -> : b = a by move/eqP: Hba.
    by exists t => //; exact: IHs Hsub Hsz.
  + (* b != a: (b :: t) \in subseqs_k k.+1 (a :: s) via right *)
    (* Hsub : subseq (b :: t) s *)
    rewrite mem_cat; apply/orP; right.
    apply: IHs Hsub _; by rewrite /= Hsz.
Qed.

(** Under the everywhere-false relation, two distinct members already break
    the clique condition. *)
Lemma all_pairs_false_neq (s : seq nat) (a b : nat) :
  a \in s -> b \in s -> a != b ->
  all_pairs_comm_sorted (fun _ _ => false) s = false.
Proof.
move=> Ha Hb Hab.
apply/negbTE/negP.
rewrite /all_pairs_comm_sorted => /allP /(_ a Ha) /allP /(_ b Hb).
by rewrite (negbTE Hab).
Qed.

(** The edgeless graph has no clique of size 2 or more.
    The clique polynomial is therefore linear, and every term of the
    recurrence beyond k = 1 vanishes. *)
Lemma empty_clique_countk Tg k :
  2 <= k -> clique_count Tg k (fun _ _ => false) = 0.
Proof.
move=> Hk.
rewrite /clique_count /cliques_of_size.
rewrite (eq_in_filter (a2 := pred0)); first by rewrite filter_pred0.
move=> s Hs /=.
have Hsz := subseqs_k_size Hs.
have Huniq := subseq_uniq (subseqs_k_subseq Hs) (iota_uniq 0 Tg).
have Hsz2 : 2 <= size s by rewrite Hsz.
suff [a [b [Ha [Hb Hab]]]] : exists a b, a \in s /\ b \in s /\ a != b.
  exact: all_pairs_false_neq Ha Hb Hab.
case: s {Hs Hsz} Hsz2 Huniq => [|a [|b s]] // _ /andP [Ha Huniq'].
exists a, b; split; first by exact: mem_head.
split; first by rewrite in_cons mem_head orbT.
by move: Ha; rewrite in_cons negb_or => /andP [].
Qed.

(* --- Free case: clique_traces Tg L (fun _ _ => false) = Tg^L --- *)
(* With c_0 = 1, c_1 = Tg and c_k = 0 beyond, the recurrence reads
   m_L = Tg * m_{L-1} with m_0 = 1, whose solution is Tg^L. *)

(* A sum of terms that all vanish is zero. *)
Lemma sumn_map_0 {A : eqType} (f : A -> nat) (s : seq A) :
  (forall x, x \in s -> f x = 0) -> sumn [seq f x | x <- s] = 0.
Proof.
elim: s => [|a s IH] //= Hf.
rewrite Hf ?IH // ?mem_head //.
by move=> x Hx; apply: Hf; rewrite in_cons Hx orbT.
Qed.

(* On the edgeless graph a recurrence step multiplies the last entry by Tg:
   the only surviving term is k = 1. *)
Lemma clique_step_free Tg memo :
  0 < size memo ->
  clique_step Tg (fun _ _ => false) memo = Tg * nth 0 memo (size memo - 1).
Proof.
move=> Hpos.
rewrite /clique_step.
have Hneg : sumn [seq clique_count Tg k (fun _ _ => false) *
                       nth 0 memo (size memo - k)
                  | k <- [seq k <- iota 1 (size memo) | ~~ odd k]] = 0.
  apply: sumn_map_0 => k.
  rewrite mem_filter => /andP [Heven Hk_iota].
  have Hk2 : 2 <= k.
    rewrite mem_iota in Hk_iota.
    by case: k Heven Hk_iota => [|[|k']] //=.
  by rewrite empty_clique_countk // mul0n.
rewrite Hneg subn0.
case: (size memo) Hpos => [|n] // _.
rewrite //=.
rewrite empty_clique_count1.
have Hrest : sumn [seq clique_count Tg k (fun _ _ => false) *
                        nth 0 memo (n.+1 - k)
                   | k <- [seq k <- iota 2 n | odd k]] = 0.
  apply: sumn_map_0 => k.
  rewrite mem_filter => /andP [_ Hk_iota].
  have Hk2 : 2 <= k.
    by rewrite mem_iota in Hk_iota; case/andP: Hk_iota.
  by rewrite empty_clique_countk // mul0n.
by rewrite Hrest addn0.
Qed.

(* Run on the edgeless graph from a memo table of powers of Tg, the recursion
   appends the next powers of Tg. *)
Lemma clique_traces_aux_inv Tg n memo :
  0 < size memo ->
  (forall i, i < size memo -> nth 0 memo i = Tg ^ i) ->
  clique_traces_aux Tg (fun _ _ => false) n memo =
  memo ++ [seq Tg ^ (size memo + i) | i <- iota 0 n].
Proof.
elim: n memo => [|n IH] memo Hpos Hmemo /=.
  by rewrite cats0.
rewrite IH.
- rewrite size_rcons -cats1 -catA /=.
  congr (memo ++ _); congr cons.
  + rewrite clique_step_free // Hmemo;
      last by rewrite ltn_subrL Hpos.
    by rewrite addn0 -expnS subn1 (prednK Hpos).
  + rewrite -[1]addn0 iotaDl -map_comp /=.
    by apply: eq_map => i /=; rewrite addSn addnS.
- by rewrite size_rcons.
- move=> i.
  rewrite size_rcons nth_rcons ltnS.
  case: (ltnP i (size memo)) => Hi Hi2.
    exact: Hmemo.
  have -> : i = size memo by apply/anti_leq/andP; split.
  rewrite eqxx.
  rewrite clique_step_free // Hmemo;
    last by rewrite ltn_subrL Hpos.
  by rewrite -expnS subn1 prednK.
Qed.

(** On the edgeless graph the clique recurrence gives Tg^L.
    The free extreme: no word can be reordered, so trace classes are words and
    the count is the raw alphabet power.  Together with clique_traces_abelian
    this brackets what any commutation graph can produce. *)
Lemma clique_traces_free Tg L :
  clique_traces Tg L (fun _ _ => false) = Tg ^ L.
Proof.
rewrite /clique_traces.
rewrite clique_traces_aux_inv //; last by move=> [|i].
case: L => [|L] //.
have -> : nth 0 ([:: 1] ++ [seq Tg ^ (1 + i) | i <- iota 0 L.+1]) L.+1 =
          nth 0 [seq Tg ^ (1 + i) | i <- iota 0 L.+1] L by [].
by rewrite (nth_map 0) ?size_iota // nth_iota ?add1n.
Qed.

(* --- Abelian case: clique_traces Tg L (i != j) = C(L+Tg-1, Tg-1) --- *)
(* For complete graph: c_k = C(Tg,k), P(z) = (1-z)^Tg.
   1/P(z) = Sum C(L+Tg-1,Tg-1) z^L. *)

(* In the complete graph any duplicate-free set is a clique. *)
Lemma all_pairs_complete (s : seq nat) :
  uniq s -> all_pairs_comm_sorted complete_comm_nat s.
Proof.
move=> Huniq.
apply/allP => i Hi; apply/allP => j Hj; apply/orP.
case Heq: (i == j); first by left.
by right; rewrite /complete_comm_nat Heq.
Qed.

(** A duplicate-free list of n elements has 'C(n,k) subsequences of length
    k. *)
Lemma size_subseqs_k k s :
  uniq s -> size (subseqs_k k s) = 'C(size s, k).
Proof.
elim: s k => [|a s IHs] k //=.
  by case: k => [|k] //=; rewrite bin_small.
case/andP => _ Hu; case: k => [|k] //=.
by rewrite size_cat size_map IHs // IHs // addnC -binS.
Qed.

(** The complete graph on Tg vertices has 'C(Tg,k) cliques of size k.
    So P(z) = (1-z)^Tg, whose reciprocal expands with coefficients
    'C(L+Tg-1, Tg-1): the abelian trace count. *)
Lemma complete_clique_count Tg k :
  clique_count Tg k complete_comm_nat = 'C(Tg, k).
Proof.
rewrite /clique_count /cliques_of_size.
rewrite (eq_in_filter (a2 := predT)).
  rewrite filter_predT size_subseqs_k ?iota_uniq // size_iota //.
move=> s Hs /=.
apply: all_pairs_complete.
exact: subseq_uniq (subseqs_k_subseq Hs) (iota_uniq 0 Tg).
Qed.

(* The alternating sum sum_k (-1)^k 'C(n,k) 'C(L-k+r, r) has no nat form, so
   it is carried as the pair of its even-index and odd-index halves, spos and
   sneg.  That the two halves are equal at n = r+1 is the binomial inversion
   behind the abelian case, and it is stated over nat without ever forming a
   negative quantity. *)

(* Even-index half: sum over even k <= L of 'C(n,k) * 'C(L-k+r, r). *)
Definition spos (n r L : nat) : nat :=
  sumn [seq 'C(n, k) * 'C(L - k + r, r)
       | k <- [seq k <- iota 0 L.+1 | ~~ odd k]].

(** Odd-index half: sum over odd k <= L of 'C(n,k) * 'C(L-k+r, r). *)
Definition sneg (n r L : nat) : nat :=
  sumn [seq 'C(n, k) * 'C(L - k + r, r)
       | k <- [seq k <- iota 0 L.+1 | odd k]].

Arguments spos : simpl never.
Arguments sneg : simpl never.

(** The even filter of iota 0 L.+1 keeps its leading 0. *)
Lemma filter_iota_head_even L :
  [seq k <- iota 0 L.+1 | ~~ odd k] = 0 :: [seq k <- iota 1 L | ~~ odd k].
Proof. by case: L. Qed.

(** The odd filter of iota 0 L.+1 drops the leading 0. *)
Lemma filter_iota_head_odd L :
  [seq k <- iota 0 L.+1 | odd k] = [seq k <- iota 1 L | odd k].
Proof. by case: L. Qed.

(** A filtered sum equals the unfiltered sum of a summand guarded by the
    predicate. *)
Lemma sumn_filter_map {A : eqType} (p : pred A) (f : A -> nat) (s : seq A) :
  sumn [seq f x | x <- [seq x <- s | p x]] =
  sumn [seq (if p x then f x else 0) | x <- s].
Proof. by elim: s => [|a s IH] //=; case: (p a) => /=; rewrite IH. Qed.

(** spos with its filter turned into a guard on the summand. *)
Lemma spos_unfold n r L :
  spos n r L = sumn [seq (if ~~ odd k then 'C(n, k) * 'C(L - k + r, r) else 0)
                     | k <- iota 0 L.+1].
Proof. by rewrite /spos sumn_filter_map. Qed.

(** sneg with its filter turned into a guard on the summand. *)
Lemma sneg_unfold n r L :
  sneg n r L = sumn [seq (if odd k then 'C(n, k) * 'C(L - k + r, r) else 0)
                     | k <- iota 0 L.+1].
Proof. by rewrite /sneg sumn_filter_map. Qed.

(** The k = 0 term of spos, namely 'C(L+r,r), split off from the rest.
    That term is the one the clique recurrence isolates as m_L itself, c_0
    being 1. *)
Lemma spos_split n r L :
  spos n r L =
  'C(L + r, r) +
  sumn [seq (if ~~ odd k then 'C(n, k) * 'C(L - k + r, r) else 0)
       | k <- iota 1 L].
Proof.
by rewrite spos_unfold /sumn /= -/(sumn _) bin0 mul1n subn0.
Qed.

(** sneg has no k = 0 term, so it is already a sum over iota 1 L. *)
Lemma sneg_eq_tail n r L :
  sneg n r L =
  sumn [seq (if odd k then 'C(n, k) * 'C(L - k + r, r) else 0)
       | k <- iota 1 L].
Proof.
by rewrite sneg_unfold /sumn /= -/(sumn _).
Qed.

Arguments sumn : simpl never.

(** sumn is additive in its summand. *)
Lemma sumn_map_add {A : Type} (f g : A -> nat) (s : seq A) :
  sumn [seq f x + g x | x <- s] =
  sumn [seq f x | x <- s] + sumn [seq g x | x <- s].
Proof. by elim: s => [|a s IH] //; rewrite /sumn /= -/(sumn _) IH addnACA. Qed.

(** A summand that splits pointwise on the range splits the sum. *)
Lemma sumn_map_split (f g h : nat -> nat) m M :
  (forall k, m <= k -> f k = g k + h k) ->
  sumn [seq f k | k <- iota m M] =
  sumn [seq g k | k <- iota m M] + sumn [seq h k | k <- iota m M].
Proof.
move=> H; elim: M m H => [|M IH] m H //.
rewrite /sumn /= -/(sumn _) -/(sumn _) -/(sumn _).
by rewrite H // (IH _ (fun k Hk => H k (ltnW Hk))) addnACA.
Qed.

(** Summands equal on the range give equal sums. *)
Lemma sumn_map_eq (f g : nat -> nat) m M :
  (forall k, m <= k -> f k = g k) ->
  sumn [seq f k | k <- iota m M] = sumn [seq g k | k <- iota m M].
Proof.
move=> H; elim: M m H => [|M IH] m H //.
rewrite /sumn /= -/(sumn _) -/(sumn _).
by rewrite H // IH // => k /ltnW /H.
Qed.

(** Shifting the index down by one turns a sum restricted to even indices
    into one restricted to odd indices.  Parity alternates under k |-> k-1,
    which is how the second summand produced by Pascal's rule lands in the
    opposite half. *)
Lemma sumn_shift_even_to_odd_gen (g : nat -> nat) m M :
  sumn [seq (if ~~ odd k then g k.-1 else 0) | k <- iota m.+1 M] =
  sumn [seq (if odd j then g j else 0) | j <- iota m M].
Proof.
by elim: M m => [|M IH] m //;
  rewrite /sumn /= -/(sumn _) -/(sumn _) (IH m.+1) negbK.
Qed.

(** The same index shift in the other direction, from odd indices to
    even ones. *)
Lemma sumn_shift_odd_to_even_gen (g : nat -> nat) m M :
  sumn [seq (if odd k then g k.-1 else 0) | k <- iota m.+1 M] =
  sumn [seq (if ~~ odd j then g j else 0) | j <- iota m M].
Proof.
by elim: M m => [|M IH] m //;
  rewrite /sumn /= -/(sumn _) -/(sumn _) (IH m.+1).
Qed.

(** A summand vanishing on the range gives a zero sum. *)
Lemma sumn_iota_map0 (f : nat -> nat) m M :
  (forall k, m <= k -> f k = 0) -> sumn [seq f k | k <- iota m M] = 0.
Proof.
move=> Hf; elim: M m Hf => [|M IH] m Hf //.
rewrite /sumn /= -/(sumn _).
rewrite Hf // IH // => k Hk.
by apply: Hf; exact: ltnW.
Qed.

(** At L = 0 only the k = 0 term remains, so spos n r 0 = 'C(r,r) = 1. *)
Lemma spos_L0 n r : spos n r 0 = 'C(r, r).
Proof. by rewrite /spos /sumn /= bin0 mul1n subn0 add0n addn0. Qed.

(** At L = 0 the odd half is empty. *)
Lemma sneg_L0 n r : sneg n r 0 = 0.
Proof. by rewrite /sneg /sumn. Qed.

(** At n = 0 every term with k > 0 has a vanishing binomial factor, leaving
    spos 0 r L = 'C(L+r,r). *)
Lemma spos0 r L : spos 0 r L = 'C(L + r, r).
Proof.
rewrite spos_unfold /sumn /= -/(sumn _) mul1n subn0.
suff -> : sumn [seq (if ~~ odd k then 'C(0, k) * 'C(L - k + r, r) else 0)
               | k <- iota 1 L] = 0 by rewrite addn0.
apply: sumn_iota_map0 => k Hk.
by case: (~~ odd k) => //=; rewrite (bin_small Hk) mul0n.
Qed.

(** At n = 0 the odd half vanishes entirely. *)
Lemma sneg0 r L : sneg 0 r L = 0.
Proof.
rewrite sneg_unfold /=.
apply: sumn_iota_map0 => k Hk.
by case: (odd k) => //=; rewrite (bin_small Hk) mul0n.
Qed.

(** Pascal's rule with the decrement on k: 'C(n+1,k) = 'C(n,k) + 'C(n,k-1)
    for k > 0. *)
Lemma binSn n k : 0 < k ->
  'C(n.+1, k) = 'C(n, k) + 'C(n, k.-1).
Proof. by case: k => // k _; rewrite binS addnC. Qed.

(* Pascal's rule splits each b-guarded term in two, the second piece landing
   in the opposite-parity half at one lower L; spos_pascal_core and
   sneg_pascal_core instantiate b at true and false respectively. *)
Local Notation pguard b k := (if b then ~~ odd k else odd k).

Local Lemma pascal_core_gen (b : bool) n r L :
  sumn [seq (if pguard b k then 'C(n.+1, k) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1] =
  sumn [seq (if pguard b k then 'C(n, k) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1] +
  sumn [seq (if pguard (~~ b) k then 'C(n, k) * 'C(L - k + r, r) else 0)
       | k <- iota 0 L.+1].
Proof.
transitivity (
  sumn [seq (if pguard b k then 'C(n, k) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1] +
  sumn [seq (if pguard b k then 'C(n, k.-1) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1]).
  apply: sumn_map_split => k Hk /=.
  case: (pguard b k) => //=.
  by rewrite binSn // -mulnDl.
suff -> :
  sumn [seq (if pguard b k then 'C(n, k.-1) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1] =
  sumn [seq (if pguard (~~ b) k then 'C(n, k) * 'C(L - k + r, r) else 0)
       | k <- iota 0 L.+1] by [].
case: b.
  rewrite -(sumn_shift_even_to_odd_gen
              (fun j => 'C(n, j) * 'C(L - j + r, r)) 0 L.+1).
  apply: sumn_map_eq => k Hk /=.
  case: (~~ odd k) => //=.
  congr (_ * _).
  by case: k Hk => // k _; rewrite subSS.
rewrite -(sumn_shift_odd_to_even_gen
            (fun j => 'C(n, j) * 'C(L - j + r, r)) 0 L.+1).
apply: sumn_map_eq => k Hk /=.
case: (odd k) => //=.
congr (_ * _).
by case: k Hk => // k _; rewrite subSS.
Qed.

(* Pascal's rule splits each even-index term in two; the second piece
   reindexes into the odd half at one lower L. *)
Lemma spos_pascal_core n r L :
  sumn [seq (if ~~ odd k then 'C(n.+1, k) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1] =
  sumn [seq (if ~~ odd k then 'C(n, k) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1] +
  sumn [seq (if odd k then 'C(n, k) * 'C(L - k + r, r) else 0)
       | k <- iota 0 L.+1].
Proof. exact: pascal_core_gen true n r L. Qed.

(* The same split for the odd half, its second piece landing in the even half
   at one lower L. *)
Lemma sneg_pascal_core n r L :
  sumn [seq (if odd k then 'C(n.+1, k) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1] =
  sumn [seq (if odd k then 'C(n, k) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1] +
  sumn [seq (if ~~ odd k then 'C(n, k) * 'C(L - k + r, r) else 0)
       | k <- iota 0 L.+1].
Proof. exact: pascal_core_gen false n r L. Qed.

(** Raising n by one adds the opposite half at one lower L:
    spos n+1 r (L+1) = spos n r (L+1) + sneg n r L. *)
Lemma spos_pascal n r L :
  spos n.+1 r L.+1 = spos n r L.+1 + sneg n r L.
Proof.
rewrite (spos_split n.+1) (spos_split n r L.+1) (sneg_unfold n r L).
by rewrite spos_pascal_core addnA.
Qed.

(** The companion recurrence, with the halves exchanged. *)
Lemma sneg_pascal n r L :
  sneg n.+1 r L.+1 = sneg n r L.+1 + spos n r L.
Proof.
rewrite (sneg_eq_tail n.+1 r L.+1) (sneg_eq_tail n r L.+1) (spos_unfold n r L).
by rewrite sneg_pascal_core addnA.
Qed.

(** For n <= r the two halves differ by a single binomial:
    spos n r L = 'C(L+r-n, r-n) + sneg n r L.
    The nat-safe form of the binomial inversion identity, the gap shrinking as
    n climbs towards r. *)
Lemma spos_inv n r L : n <= r ->
  spos n r L = 'C(L + r - n, r - n) + sneg n r L.
Proof.
elim: n r L => [|n IHn] r L Hrn.
  by rewrite spos0 sneg0 addn0 subn0 subn0.
case: L => [|L].
  by rewrite spos_L0 sneg_L0 addn0 add0n binn binn.
rewrite spos_pascal sneg_pascal.
rewrite (IHn r L.+1 (ltnW Hrn)) (IHn r L (ltnW Hrn)).
(* Goal: 'C(L.+1+r-n, r-n) + sneg n r L.+1 + sneg n r L =
         'C(L.+1+r-n.+1, r-n.+1) + (sneg n r L.+1 + ('C(L+r-n, r-n) + sneg n r L)) *)
set a := 'C(L.+1 + r - n, r - n).
set b := sneg n r L.+1.
set c := sneg n r L.
set d := 'C(L.+1 + r - n.+1, r - n.+1).
set e := 'C(L + r - n, r - n).
(* Goal: a + b + c = d + (b + (e + c)) *)
suff -> : a = d + e.
  (* d + e + b + c = d + (b + (e + c)) *)
  by rewrite [d + e + b]addnAC addnA addnA.
subst a d e.
(* Goal: 'C(L.+1+r-n, r-n) = 'C(L.+1+r-n.+1, r-n.+1) + 'C(L+r-n, r-n) *)
have Hrn' : n <= L + r by apply: (leq_trans (ltnW Hrn)); exact: leq_addl.
have Heq1 : L.+1 + r - n.+1 = L + r - n by rewrite addSn subSS.
have Heq2 : r - n = (r - n.+1).+1 by rewrite subnS prednK // subn_gt0.
have Heq3 : L.+1 + r - n = (L + r - n).+1 by rewrite addSn (subSn Hrn').
by rewrite Heq1 Heq2 Heq3 binS addnC.
Qed.

(** At n = r+1 the two halves are equal.
    The alternating sum sum_k (-1)^k 'C(r+1,k) 'C(L+1-k+r, r) is therefore
    zero, which is exactly the clique recurrence for the complete graph and is
    what makes the abelian trace count come out as a single binomial. *)
Lemma spos_eq_sneg n L :
  spos n.+1 n L.+1 = sneg n.+1 n L.+1.
Proof.
rewrite spos_pascal sneg_pascal.
rewrite (@spos_inv n n L.+1 (leqnn n)) (@spos_inv n n L (leqnn n)).
by rewrite (subnn n) addnK addnK bin0 bin0 addnCA.
Qed.

(** The odd part of a recurrence step, written in the sneg notation. *)
Lemma pos_eq_sneg_range Tg r L :
  sumn [seq 'C(Tg, k) * 'C(L - k + r, r)
       | k <- [seq k <- iota 1 L | odd k]] =
  sneg Tg r L.
Proof. by rewrite sneg_eq_tail sumn_filter_map. Qed.

(** The even part of a recurrence step, written as spos with its k = 0 term
    removed. *)
Lemma neg_eq_spos_sub Tg r L :
  sumn [seq 'C(Tg, k) * 'C(L - k + r, r)
       | k <- [seq k <- iota 1 L | ~~ odd k]] =
  spos Tg r L - 'C(L + r, r).
Proof. by rewrite spos_split sumn_filter_map addKn. Qed.

(** On the complete graph, a recurrence step run on a memo table of binomials
    produces the next binomial.
    The alternating sum collapses by spos_eq_sneg, leaving only the k = 0
    term. *)
Lemma clique_step_abelian Tg memo :
  0 < Tg -> 0 < size memo ->
  (forall i, i < size memo -> nth 0 memo i = 'C(i + Tg.-1, Tg.-1)) ->
  clique_step Tg complete_comm_nat memo = 'C(size memo + Tg.-1, Tg.-1).
Proof.
move=> HTg Hpos Hmemo.
rewrite /clique_step.
set L := size memo.
set r := Tg.-1.
have Hmap_eq : forall (p : pred nat),
  [seq clique_count Tg k complete_comm_nat * nth 0 memo (L - k)
      | k <- [seq k <- iota 1 L | p k]] =
  [seq 'C(Tg, k) * 'C(L - k + r, r)
      | k <- [seq k <- iota 1 L | p k]].
  move=> p; apply/eq_in_map => k Hk.
  rewrite complete_clique_count.
  suff -> : nth 0 memo (L - k) = 'C(L - k + r, r) by [].
  apply: Hmemo.
  rewrite mem_filter mem_iota in Hk.
  case/andP: Hk => _ /andP [Hk1 Hk2].
  by rewrite /L ltn_subrL Hk1 Hpos.
have Hpos_eq := congr1 sumn (Hmap_eq odd).
have Hneg_eq := congr1 sumn (Hmap_eq (fun k => ~~ odd k)).
rewrite Hpos_eq Hneg_eq pos_eq_sneg_range neg_eq_spos_sub.
subst r; case: Tg HTg {Hpos_eq Hneg_eq Hmap_eq Hmemo} => // Tg _ /=.
rewrite /L; case: (size memo) Hpos => [|L'] // _.
by rewrite spos_eq_sneg subKn // -spos_eq_sneg spos_split leq_addr.
Qed.

(** Run on the complete graph from a memo table of binomials, the recursion
    appends the next binomials. *)
Lemma clique_traces_aux_inv_abelian Tg n memo :
  0 < Tg -> 0 < size memo ->
  (forall i, i < size memo -> nth 0 memo i = 'C(i + Tg.-1, Tg.-1)) ->
  clique_traces_aux Tg complete_comm_nat n memo =
  memo ++ [seq 'C(size memo + i + Tg.-1, Tg.-1) | i <- iota 0 n].
Proof.
elim: n memo => [|n IH] memo HTg Hpos Hmemo /=.
  by rewrite cats0.
rewrite IH.
- rewrite size_rcons -cats1 -catA /=.
  congr (memo ++ _); congr cons.
  + by rewrite clique_step_abelian // addn0.
  + rewrite -[1]addn0 iotaDl -map_comp /=.
    by apply: eq_map => i /=; rewrite addSn addnS.
- done.
- by rewrite size_rcons.
- move=> i; rewrite size_rcons nth_rcons ltnS.
  case: (ltnP i (size memo)) => Hi Hi2.
    exact: Hmemo.
  have -> : i = size memo by apply/anti_leq/andP; split.
  by rewrite eqxx clique_step_abelian // addn0.
Qed.

(** On the complete graph the clique recurrence gives 'C(L+Tg-1, Tg-1).
    The abelian extreme: a trace class is a multiset of L letters, so the
    count is polynomial in L of degree Tg-1.  Against Tg^L in the free case,
    this is the whole range a commutation graph can move the search space
    across. *)
Lemma clique_traces_abelian Tg L :
  0 < Tg ->
  clique_traces Tg L complete_comm_nat = 'C(L + Tg.-1, Tg.-1).
Proof.
move=> HTg.
rewrite /clique_traces.
rewrite clique_traces_aux_inv_abelian //; last first.
  move=> [|i] _ //=.
  by rewrite add0n binn.
case: L => [|L].
  by rewrite /= add0n binn.
have -> : nth 0 ([:: 1] ++ [seq 'C(1 + i + Tg.-1, Tg.-1)
            | i <- iota 0 L.+1]) L.+1 =
          nth 0 [seq 'C(1 + i + Tg.-1, Tg.-1) | i <- iota 0 L.+1] L by [].
by rewrite (nth_map 0) ?size_iota // nth_iota // add0n addnC addnA.
Qed.

(* --- The four growth rates side by side, on three or four generators --- *)

(* The free case: 3^L. *)
Lemma free_growth_check : [seq clique_traces 3 L (fun _ _ => false) | L <- iota 0 5]
  = [:: 1; 3; 9; 27; 81].
Proof. by vm_compute. Qed.

(* The abelian case: 'C(L+2,2), quadratic in L. *)
Lemma abelian_growth_check : [seq clique_traces 3 L complete_comm_nat | L <- iota 0 5]
  = [:: 1; 3; 6; 10; 15].
Proof. by vm_compute. Qed.

(* The star K_{1,3} on four generators: (3^{L+1}-1)/2, exponential with base
   3 against the free case's 4. *)
Lemma star3_growth_check :
  [seq clique_traces 4 L (star_comm_nat 3) | L <- iota 0 6]
  = [:: 1; 4; 13; 40; 121; 364].
Proof. by vm_compute. Qed.

(* The path P_3: m_L = 3 m_{L-1} - m_{L-2}, growth rate (3+sqrt 5)/2. *)
Lemma path3_growth_check :
  [seq clique_traces 3 L path_comm_nat | L <- iota 0 6]
  = [:: 1; 3; 8; 21; 55; 144].
Proof. by vm_compute. Qed.

(* ========================================================================== *)
(* Part 5: Reflection to abstract n_traces                                    *)
(* ========================================================================== *)

(* Cartier-Foata at the nat level: for a commutation relation symmetric and
   irreflexive on the Tg generators,
     clique_traces Tg L comm = n_traces_natB Tg L comm,
   the generating function for the traces of a partially commutative monoid
   being the reciprocal of the clique polynomial of its commutation graph.

   Both hypotheses are load-bearing rather than customary: without symmetry
   the identity already fails at L = 3.

   The proof is cartier_foata in legacy/groups/pgg_raag_cartier_foata.v,
   which imports this file, so the identity reaches consumers of the clique
   polynomial but is not itself available here.  The checks below instead
   pin the two sides
   against each other at the commutation graphs this development uses --
   free, abelian, star and path, Tg up to 4 and L up to 5 -- which is the
   range every concrete instance of the trace bound falls in.  From the nat
   level, n_traces_of_natB carries the identity to the abstract n_traces of
   a RAAGType. *)

(* The predicted and the enumerated counts, compared pointwise at each graph
   this development uses.  Each list is nseq true, so the two agree
   everywhere in range. *)
Lemma cartier_foata_check_free3 :
  [seq (clique_traces 3 L (fun _ _ => false) ==
        n_traces_natB 3 L (fun _ _ => false)) | L <- iota 0 5]
  = nseq 5 true.
Proof. by vm_compute. Qed.

Lemma cartier_foata_check_abelian3 :
  [seq (clique_traces 3 L complete_comm_nat ==
        n_traces_natB 3 L complete_comm_nat) | L <- iota 0 5]
  = nseq 5 true.
Proof. by vm_compute. Qed.

Lemma cartier_foata_check_path3 :
  [seq (clique_traces 3 L path_comm_nat ==
        n_traces_natB 3 L path_comm_nat) | L <- iota 0 5]
  = nseq 5 true.
Proof. by vm_compute. Qed.

Lemma cartier_foata_check_star3 :
  [seq (clique_traces 4 L (star_comm_nat 3) ==
        n_traces_natB 4 L (star_comm_nat 3)) | L <- iota 0 4]
  = nseq 4 true.
Proof. by vm_compute. Qed.

Lemma cartier_foata_check_abelian4 :
  [seq (clique_traces 4 L complete_comm_nat ==
        n_traces_natB 4 L complete_comm_nat) | L <- iota 0 4]
  = nseq 4 true.
Proof. by vm_compute. Qed.


(* ========================================================================== *)
(* Growth rate comparison table (summary)                                     *)
(* ========================================================================== *)

(*
   T=4 generators, growth rate comparison:

   L | Free (4^L) | Star K_{1,3} / Path P_4 | Abelian C(L+3,3)
   --+------------+-------------------------+-----------------
   0 |          1 |                        1 |               1
   1 |          4 |                        4 |               4
   2 |         16 |                       13 |              10
   3 |         64 |                       40 |              20
   4 |        256 |                      121 |              35
   5 |       1024 |                      364 |              56

   Star K_{1,3} and Path P_4 have the same clique polynomial
   P(z) = 1 - 4z + 3z^2 = (1-z)(1-3z), hence the same trace counts
   by the Cartier-Foata theorem.

   Ordering: abelian <= star/path <= free

   T=3 generators:

   L | Free (3^L) | Path P_3   | Abelian C(L+2,2)
   --+------------+------------+-----------------
   0 |          1 |          1 |               1
   1 |          3 |          3 |               3
   2 |          9 |          8 |               6
   3 |         27 |         21 |              10
   4 |         81 |         55 |              15
   5 |        243 |        144 |              21

   Path P_3 has P(z) = 1 - 3z + z^2.  Growth rate = (3+sqrt(5))/2.
*)

(* The rows of the table above, each checked by computation. *)
Lemma table_T4_free :
  [seq clique_traces 4 L (fun _ _ => false) | L <- iota 0 6]
  = [:: 1; 4; 16; 64; 256; 1024].
Proof. by vm_compute. Qed.

(** The path P_4 on four generators: indices commute when they differ by at
    least 2.  Its cliques are the empty set, four vertices and three edges
    ({0,2}, {0,3}, {1,3}), the same profile as the star K_{1,3}, which is why
    the two rows of the table coincide. *)
Definition path4_comm_nat (i j : nat) : bool :=
  (2 <= (maxn i j - minn i j)) && (i != j).

Lemma table_T4_path :
  [seq clique_traces 4 L path4_comm_nat | L <- iota 0 6]
  = [:: 1; 4; 13; 40; 121; 364].
Proof. by vm_compute. Qed.

(* Non-isomorphic graphs with equal clique polynomials give equal trace
   counts: by Cartier-Foata the generating function depends on the graph only
   through P(z).  Path P_4 and star K_{1,3} both have
   P(z) = 1 - 4z + 3z^2 = (1-z)(1-3z), and the two rows agree.
   For the search-space reading this means the choice between two graphs with
   the same clique polynomial leaves the deck designer's trace counts equal. *)

Lemma table_T4_star3 :
  [seq clique_traces 4 L (star_comm_nat 3) | L <- iota 0 6]
  = [:: 1; 4; 13; 40; 121; 364].
Proof. by vm_compute. Qed.

Lemma table_T4_abelian :
  [seq clique_traces 4 L complete_comm_nat | L <- iota 0 6]
  = [:: 1; 4; 10; 20; 35; 56].
Proof. by vm_compute. Qed.

(* The enumerated counts for both graphs, matching the predicted rows. *)
Lemma path4_ntB_check :
  [seq n_traces_natB 4 L path4_comm_nat | L <- iota 0 4]
  = [:: 1; 4; 13; 40].
Proof. by vm_compute. Qed.

Lemma star3_ntB_check :
  [seq n_traces_natB 4 L (star_comm_nat 3) | L <- iota 0 4]
  = [:: 1; 4; 13; 40].
Proof. by vm_compute. Qed.

(* Path P_4 and star K_{1,3} share a clique polynomial and share trace counts
   at every length checked.  The general statement is cartier_foata in
   legacy/groups/pgg_raag_cartier_foata.v; what stands here is agreement at
   these lengths. *)
