(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop binomial.
From pgg_smc Require Import pgg_interface.

(******************************************************************************)
(* PGG: Abelian Word Collapse (Theorem 8, items (1)-(2))                     *)
(* Group presentation: <s_1,...,s_Tg | s_i s_j = s_j s_i for all i,j> (abelian) *)
(*                                                                           *)
(* In an abelian group with r generators, any word of length L evaluates to  *)
(* a product that depends only on the frequency vector (c_1,...,c_r) where   *)
(* c_j counts how often generator j appears. This collapses the exponential  *)
(* search space r^L to at most 'C(L+r-1,r-1) distinct frequency vectors.    *)
(*                                                                           *)
(* The collapse is the negative result of the abelian instances: an          *)
(* adversary enumerating shuffles faces a count polynomial in the number of  *)
(* rounds, of degree the generator count, so rounds buy no exponential       *)
(* growth.  The RAAG instances sit on the other side of this, where a        *)
(* commutation graph with an independent set keeps the count exponential.    *)
(*                                                                           *)
(*   freq_vec w j   == number of positions in word w that use generator j    *)
(*   freq_vecs L    == set of frequency vectors {f : 'I_Tg -> nat | sum=L}  *)
(*   abelian_word_eval  == word evaluation depends only on frequency vector  *)
(*   freq_vec_sum       == sum of frequencies equals word length             *)
(*   abelian_search_space_le == search_space L <= #|freq_vecs L|            *)
(*   card_freq_vecs == #|freq_vecs L| = 'C(L + Tg.-1, Tg.-1)              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Section 1: Frequency vector and abelian word evaluation                    *)
(* ========================================================================== *)

Section freq_vector.

Variable M : MonodromyReprWithGeneratorType.

Let gT := pgg_gT M.
Let G := pgg_G M.
Let Tg := (@pgg_ngens' M).+1.
Let sigmas := @pgg_sigmas M.

Variable L : nat.

(* The frequency vector of a word: how often each generator index occurs in
   it.  It is the whole of what an abelian group can see of a word, since the
   order of the letters is exactly what commutativity erases. *)
Definition freq_vec (w : pgg_word M L) (j : 'I_Tg) : nat :=
  #|[set i : 'I_L | tnth w i == j]|.

(* The frequencies sum to the word length: every position of the word is
   counted once, under the letter it carries.  This is the constraint that
   makes the set of reachable frequency vectors finite and countable by
   stars and bars. *)
Lemma freq_vec_sum (w : pgg_word M L) :
  \sum_(j < Tg) freq_vec w j = L.
Proof.
rewrite /freq_vec -[RHS]card_ord -sum1_card.
transitivity (\sum_(j < Tg) \sum_(i < L | tnth w i == j) 1).
  by apply: eq_bigr => j _; rewrite -sum1_card; apply: eq_bigl => i; rewrite inE.
symmetry; exact: partition_big.
Qed.

(* -- Helper lemmas for abelian group bigop manipulation --------------- *)
(* MathComp's bigID / partition_big require Monoid.com_law but mulg is   *)
(* only Monoid.law.  We reprove them under a runtime abelian hypothesis. *)

(* A product of group elements stays in the group.  Stated with the abelian
   hypothesis in scope because the reproved bigop lemmas below carry it
   throughout, not because commutativity is used. *)
Lemma abelian_prod_in (Habel : abelian G)
    (I : Type) (r : seq I) (P : pred I) (F : I -> gT) :
  (forall i, P i -> F i \in G) ->
  (\prod_(i <- r | P i) F i)%g \in G.
Proof.
move=> HF; elim: r => [|a s IHs]; first by rewrite big_nil; exact: group1.
rewrite big_cons; case HPa: (P a) => //.
by apply: groupM; [exact: HF|exact: IHs].
Qed.

(** abelian_bigID — a group product over a predicate splits into the product
    over the elements satisfying a second predicate times the product over
    those failing it, in an abelian group.  Splitting a product this way needs
    the two halves to be interchangeable, which is exactly commutativity. *)
Lemma abelian_bigID (Habel : abelian G)
    (I : Type) (r : seq I) (P Q : pred I) (F : I -> gT) :
  (forall i, P i -> F i \in G) ->
  (\prod_(i <- r | P i) F i =
   \prod_(i <- r | P i && Q i) F i * \prod_(i <- r | P i && ~~ Q i) F i)%g.
Proof.
move=> HF.
elim: r => [|a s IHs]; first by rewrite !big_nil mulg1.
rewrite !big_cons /=.
case HPa: (P a) => //=.
case HQa: (Q a) => /=.
- by rewrite IHs mulgA.
- rewrite IHs !mulgA; congr (_ * _)%g.
  apply: (centP (subsetP Habel _ (HF _ HPa))).
  apply: (abelian_prod_in Habel) => i /andP [HPi _]; exact: HF.
Qed.

(** abelian_big_union — a group product over a disjoint union of two
    predicates is the product over one times the product over the other. *)
Lemma abelian_big_union (Habel : abelian G)
    (I : finType) (A B : pred I) (F : I -> gT) :
  (forall i, A i || B i -> F i \in G) ->
  (forall i, A i -> B i -> false) ->
  (\prod_(i | A i || B i) F i =
   \prod_(i | A i) F i * \prod_(i | B i) F i)%g.
Proof.
move=> HF Hdisj.
have := @abelian_bigID Habel _ (index_enum I) (fun i => A i || B i) A F HF.
rewrite /= => ->.
congr (_ * _)%g; apply: eq_bigl => i.
- case HAi: (A i) => //=; by case: (B i).
- case HAi: (A i) => /=.
  + by case HBi: (B i) => //=; move: (Hdisj i HAi HBi).
  + by case: (B i).
Qed.

(** abelian_partition_big — a group product over a predicate regroups as an
    iterated product over the fibers of any map out of the index type.  This
    is the move that turns a word read left to right into a product organised
    by which generator each position carries. *)
Lemma abelian_partition_big (Habel : abelian G)
    (I J : finType) (P : pred I) (p : I -> J) (F : I -> gT) :
  (forall i, P i -> F i \in G) ->
  (\prod_(i | P i) F i = \prod_(j : J) \prod_(i | P i && (p i == j)) F i)%g.
Proof.
move=> HF.
suff Hind : forall sJ : seq J, uniq sJ ->
  (\prod_(i | P i && (p i \in sJ)) F i =
   \prod_(j <- sJ) \prod_(i | P i && (p i == j)) F i)%g.
  rewrite -Hind; last exact: index_enum_uniq.
  apply: eq_bigl => i; case: (P i) => //=.
  by rewrite mem_index_enum.
elim=> [|j sJ IHsJ].
  move=> _; rewrite big_nil.
  by apply: big1 => i; rewrite in_nil andbF.
move=> /andP [Hjnin HsJuniq].
rewrite big_cons -IHsJ //.
have Hin : forall i, P i && (p i \in j :: sJ) -> F i \in G.
  by move=> i /andP [HPi _]; exact: HF.
have := @abelian_bigID Habel _ (index_enum I)
  (fun i => P i && (p i \in j :: sJ)) (fun i => p i == j) F Hin.
rewrite /= => ->.
congr (_ * _)%g; apply: eq_bigl => i;
  rewrite in_cons; case: (P i) => //=.
- by case: (p i == j); rewrite /= ?andbF.
- by case: eqP => [->|_]; rewrite /= ?(negbTE Hjnin) ?andbT.
Qed.

(** big_const_expg — a group product whose factors are all the same element
    is that element raised to the number of factors.  Applied to one fiber of
    the regrouping above, it replaces the repetitions of a single generator by
    its multiplicity, which is the entry of the frequency vector. *)
Lemma big_const_expg (n : nat) (P : pred 'I_n) (g : gT) :
  (\prod_(i < n | P i) g = g ^+ #|[set i : 'I_n | P i]|)%g.
Proof.
rewrite -sum1_card.
elim: (index_enum _) => [|a s IHs]; first by rewrite !big_nil expg0.
rewrite !big_cons inE.
by case HPa: (P a) => /=; rewrite ?add1n ?expgS IHs.
Qed.

(* A word evaluates to the product of the generators raised to their
   frequencies.  Commutativity lets the letters be regrouped by generator and
   each group collapse to a power, so the word's order of letters leaves no
   trace in the result.  Everything the file proves about the size of the
   abelian search space follows from this one equation. *)
Lemma abelian_word_eval (w : pgg_word M L) :
  abelian G ->
  word_eval w = (\prod_(j < Tg) tnth sigmas j ^+ freq_vec w j)%g.
Proof.
move=> Habel.
rewrite /word_eval /freq_vec.
have Hpart := @abelian_partition_big Habel _ _ predT
  (fun i : 'I_L => tnth w i)
  (fun i : 'I_L => tnth sigmas (tnth w i))
  (fun i (_ : predT i) => sigmas_in_G (tnth w i)).
rewrite /= in Hpart; rewrite Hpart; clear Hpart.
apply: eq_bigr => j _.
transitivity (\prod_(i < L | tnth w i == j) tnth sigmas j)%g.
  by apply: eq_bigr => i /eqP ->.
exact: big_const_expg.
Qed.

(* Two words with the same frequency vector evaluate to the same shuffle.
   The word-to-shuffle map therefore factors through the frequency vector,
   which is why counting frequency vectors bounds the search space. *)
Lemma freq_vec_det (w1 w2 : pgg_word M L) :
  abelian G ->
  (forall j, freq_vec w1 j = freq_vec w2 j) ->
  word_eval w1 = word_eval w2.
Proof.
move=> Habel Hfreq.
rewrite (abelian_word_eval _ Habel) (abelian_word_eval _ Habel).
by apply: eq_bigr => j _; rewrite Hfreq.
Qed.

End freq_vector.

(* ========================================================================== *)
(* Section 2: Frequency vector counting (stars-and-bars)                      *)
(* ========================================================================== *)

Section freq_counting.

Variable M : MonodromyReprWithGeneratorType.

Let gT := pgg_gT M.
Let G := pgg_G M.
Let Tg := (@pgg_ngens' M).+1.
Let sigmas := @pgg_sigmas M.

Variable L : nat.

(* The set of frequency vectors of length-L words: assignments of a
   multiplicity to each generator whose total is L.  Bounded above by L in
   each coordinate so that the carrier is finite and its size can be counted. *)
Definition freq_vecs : {set {ffun 'I_Tg -> 'I_L.+1}} :=
  [set f : {ffun 'I_Tg -> 'I_L.+1} |
     \sum_(j < Tg) val (f j) == L].

(* The frequency vector of a word, as a bounded function *)
(* No generator occurs more often than the word is long. *)
Lemma freq_vec_lt (w : pgg_word M L) (j : 'I_Tg) :
  freq_vec w j < L.+1.
Proof.
rewrite ltnS /freq_vec.
by apply: leq_trans (max_card _) _; rewrite card_ord.
Qed.

(** freq_vec_ffun — the frequency vector of a word as a bounded function from
    generator indices to counts.  The counting argument needs the frequency
    vectors to form a finite type, which unbounded natural-valued counts do
    not. *)
Definition freq_vec_ffun (w : pgg_word M L) : {ffun 'I_Tg -> 'I_L.+1} :=
  [ffun j => Ordinal (freq_vec_lt w j)].

(** freq_vec_ffun_val — the bounded frequency vector carries the same counts
    as the raw one. *)
Lemma freq_vec_ffun_val (w : pgg_word M L) (j : 'I_Tg) :
  val (freq_vec_ffun w j) = freq_vec w j.
Proof. by rewrite /freq_vec_ffun ffunE. Qed.

(** freq_vec_ffun_in — every word's frequency vector is one of the vectors
    summing to the word length, so the word space maps into freq_vecs. *)
Lemma freq_vec_ffun_in (w : pgg_word M L) :
  freq_vec_ffun w \in freq_vecs.
Proof.
rewrite inE; apply/eqP.
under eq_bigr do rewrite freq_vec_ffun_val.
exact: freq_vec_sum.
Qed.

(* The shuffle a frequency vector names: each generator raised to its
   multiplicity, multiplied together.  It is the map through which word
   evaluation factors in the abelian case. *)
Definition freq_eval (f : {ffun 'I_Tg -> 'I_L.+1}) : gT :=
  (\prod_(j < Tg) tnth sigmas j ^+ val (f j))%g.

(** abelian_word_eval_freq — evaluating a word is the same as evaluating its
    frequency vector.  It states the factorization of word evaluation through
    freq_vecs in the finite-type form the counting argument works in. *)
Lemma abelian_word_eval_freq (w : pgg_word M L) :
  abelian G ->
  word_eval w = freq_eval (freq_vec_ffun w).
Proof.
move=> Habel.
rewrite /freq_eval (abelian_word_eval _ Habel).
by apply: eq_bigr => j _; rewrite freq_vec_ffun_val.
Qed.

(* Every shuffle a length-L word can produce is the image of some frequency
   vector.  The reachable set is thus contained in the image of a set whose
   size is combinatorial rather than exponential. *)
Lemma abelian_achievable_sub :
  abelian G ->
  achievable M L \subset [set freq_eval f | f in freq_vecs].
Proof.
move=> Habel.
apply/subsetP => g /imsetP [w _ ->].
apply/imsetP; exists (freq_vec_ffun w); last by rewrite -abelian_word_eval_freq.
exact: freq_vec_ffun_in.
Qed.

(** abelian_search_space_le — in an abelian group the number of reachable
    shuffles at length L is at most the number of frequency vectors summing to
    L.  This is the collapse itself, stated before the frequency vectors are
    counted. *)
Lemma abelian_search_space_le :
  abelian G ->
  search_space M L <= #|freq_vecs|.
Proof.
move=> Habel.
rewrite /search_space.
apply: leq_trans (leq_imset_card _ _).
exact: subset_leq_card (abelian_achievable_sub Habel).
Qed.

End freq_counting.

(* ========================================================================== *)
(* Section 3: Stars-and-bars counting                                         *)
(* ========================================================================== *)

(* Stars-and-bars theorem: the number of ways to write L as an ordered sum   *)
(* of Tg non-negative integers is 'C(L + Tg - 1, Tg - 1).                   *)
(*                                                                           *)
(* This is a classical combinatorial identity. The proof transports          *)
(* MathComp's card_ord_partitions (on tuples) to finite functions via        *)
(* a bijection between {ffun 'I_r.+1 -> 'I_L.+1} and r.+1.-tuple 'I_L.+1.  *)

Section stars_and_bars.

Variable r : nat.  (* number of bins = r.+1 *)
Variable L : nat.  (* total sum *)

(* The compositions of L into r+1 ordered nonnegative parts, as bounded
   functions.  Frequency vectors are compositions under another name; this
   section counts them without reference to groups. *)
Definition compositions : {set {ffun 'I_r.+1 -> 'I_L.+1}} :=
  [set f : {ffun 'I_r.+1 -> 'I_L.+1} | \sum_(j < r.+1) val (f j) == L].

(** ffun_to_tuple — a composition read as a tuple of its parts.  The classical
    count is available on tuples, and the four lemmas that follow move the
    counting question there and back. *)
Definition ffun_to_tuple (f : {ffun 'I_r.+1 -> 'I_L.+1}) : r.+1.-tuple 'I_L.+1 :=
  [tuple f i | i < r.+1].

(** tuple_to_ffun — a tuple of parts read as a composition. *)
Definition tuple_to_ffun (t : r.+1.-tuple 'I_L.+1) : {ffun 'I_r.+1 -> 'I_L.+1} :=
  [ffun i => tnth t i].

(** ffun_to_tupleK — reading a composition as a tuple and back returns the
    composition. *)
Lemma ffun_to_tupleK : cancel ffun_to_tuple tuple_to_ffun.
Proof. move=> f; apply/ffunP => i; by rewrite ffunE tnth_mktuple. Qed.

(** tuple_to_ffunK — reading a tuple as a composition and back returns the
    tuple, so the two readings are inverse and the two carriers have the same
    size. *)
Lemma tuple_to_ffunK : cancel tuple_to_ffun ffun_to_tuple.
Proof. move=> t; apply: eq_from_tnth => i; by rewrite tnth_mktuple ffunE. Qed.

(** sum_ffun_to_tuple — the parts sum to the same total on either reading, so
    the constraint defining a composition is preserved by the correspondence
    and not only the carrier. *)
Lemma sum_ffun_to_tuple (f : {ffun 'I_r.+1 -> 'I_L.+1}) :
  \sum_(i <- ffun_to_tuple f) val i = \sum_(j < r.+1) val (f j).
Proof.
rewrite /ffun_to_tuple big_tuple.
by apply: eq_bigr => i _; rewrite tnth_mktuple.
Qed.

(** card_compositions — the number of ways to write L as an ordered sum of
    r+1 nonnegative parts is 'C(L + r, r).  This is stars and bars, and it is
    where the polynomial in L enters: for fixed r the count grows as L^r. *)
Lemma card_compositions :
  #|compositions| = 'C(L + r, r).
Proof.
have Hinj : injective ffun_to_tuple by exact: can_inj ffun_to_tupleK.
rewrite -(card_imset _ Hinj).
suff -> : [set ffun_to_tuple f | f in compositions] =
          [set t : r.+1.-tuple 'I_L.+1 | \sum_(i <- t) i == L].
  by rewrite card_ord_partitions addnC.
apply/setP => t; rewrite inE.
apply/imsetP/idP.
- move=> [f]; rewrite inE => /eqP Hf ->.
  by rewrite sum_ffun_to_tuple Hf.
- move=> /eqP Ht.
  exists (tuple_to_ffun t); last by rewrite tuple_to_ffunK.
  by rewrite inE -sum_ffun_to_tuple tuple_to_ffunK Ht.
Qed.

End stars_and_bars.

Section stars_and_bars_application.

Variable M : MonodromyReprWithGeneratorType.

Let Tg := (@pgg_ngens' M).+1.

Variable L : nat.

(** freq_vecs_eq_compositions — the frequency vectors of length-L words are
    the compositions of L into as many parts as there are generators. *)
Lemma freq_vecs_eq_compositions :
  freq_vecs M L = compositions (@pgg_ngens' M) L.
Proof. by []. Qed.

(** card_freq_vecs — there are 'C(L + r, r) frequency vectors of length-L
    words over r+1 generators. *)
Lemma card_freq_vecs :
  #|freq_vecs M L| = 'C(L + (@pgg_ngens' M), (@pgg_ngens' M)).
Proof.
by rewrite freq_vecs_eq_compositions card_compositions.
Qed.

(** abelian_search_space_bound — in an abelian group with r+1 generators, the
    number of shuffles reachable by words of length L is at most
    'C(L + r, r).  This is the abelian collapse in full: the generic ceiling
    is (r+1)^L, exponential in the number of rounds, and commutativity brings
    it down to a polynomial of degree r.  An abelian instance therefore cannot
    make an adversary work harder by shuffling longer, which is what places
    every abelian instance on the negative side of the family. *)
Theorem abelian_search_space_bound :
  abelian (pgg_G M) ->
  search_space M L <= 'C(L + (@pgg_ngens' M), (@pgg_ngens' M)).
Proof.
move=> Habel.
by rewrite -card_freq_vecs; exact: abelian_search_space_le.
Qed.

End stars_and_bars_application.
