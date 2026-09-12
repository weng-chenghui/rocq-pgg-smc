(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj pgg_raag.
From pgg_smc Require Import pgg_raag_path pgg_raag_s5.
From pgg_smc Require Import pgg_collusion_bound pgg_schreier.
From pgg_reconstruct Require Import algebraic_rigidity.

(******************************************************************************)
(* PGG: The Free-Words Security Layer                                         *)
(*                                                                            *)
(* Everything a PGG security statement can say once the deck group is assumed *)
(* to look free up to word length L, that is, once word_eval is injective on  *)
(* L-words (weval_inj L, legacy/groups/pgg_weval_inj.v).  Under that          *)
(* assumption the uniform law on L-words pushes forward to the uniform law on *)
(* the achievable permutations, each word-eval fiber is a singleton, the      *)
(* search space attains Tg^L, and the endpoint marginal at a card position    *)
(* sits at variation distance 2(N - Tg^L)/N from uniform when the endpoint    *)
(* map is injective on the achievable set.                                    *)
(*                                                                            *)
(* The layer is legacy because no alphabet of a retained instance is free     *)
(* beyond length 1.  Every retained alphabet contains an involution or an     *)
(* inverse pair, so weval_inj fails from L = 2 or L = 3 on, and the all-L     *)
(* security statements those instances do carry are Schreier spectral bounds, *)
(* which assume nothing about freeness.  What still reads this file is the    *)
(* Monster and overlapping-3-cycles symbolic route and the retired L = 1      *)
(* S_5 fiber witness, all of them under legacy/.                              *)
(*                                                                            *)
(* Provenance of each block, in order:                                        *)
(*   groups/pgg_raag.v, Section raag_theory                                   *)
(*     raag_weval_inj, raag_weval_inj_search_space,                           *)
(*     indep_set_word_eval_inj                                                *)
(*   groups/pgg_raag.v, Section raag_derived                                  *)
(*     raag_weval_inj1, raag_search_space_1                                   *)
(*   instances/s5/pgg_raag_s5.v                                               *)
(*     s5_weval_inj1                                                          *)
(*   security/pgg_collusion_bound.v, Section weval_inj_collusion              *)
(*     achievable_pos, rho_from_words_uniform_supp                            *)
(*   security/pgg_collusion_bound.v, Section fiber_equidistribution           *)
(*   security/pgg_collusion_bound.v, Section direct_endpoint_epsilon          *)
(*   security/pgg_collusion_bound.v, Section endpoint_image_bound_unbalanced  *)
(*   security/pgg_collusion_bound.v, Section endpoint_image_bound             *)
(*   reconstruct/algebraic_rigidity.v, Section fiber_security                 *)
(*   reconstruct/algebraic_rigidity.v, Section direct_endpoint_security       *)
(*   reconstruct/algebraic_rigidity.v, Section security_profile               *)
(*   security/pgg_schreier.v, Section schreier_certificate                    *)
(*     security_witness_schreier                                              *)
(*                                                                            *)
(* Section contexts are recreated with the variable names the relocated       *)
(* declarations were written against, so every statement is the statement it  *)
(* was before the move.                                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(* ========================================================================== *)
(* From groups/pgg_raag.v, Section raag_theory                                *)
(* ========================================================================== *)

Section raag_theory.

Variable R : RAAGType.
Let gT := pgg_gT R.
Let M : MonodromyReprWithGeneratorType := R.
Let Tg := (@pgg_ngens' R).+1.
Let sigmas := @pgg_sigmas R.
Let comm : rel 'I_Tg := @raag_comm R.

Local Notation n_traces := (n_traces R).

(* The hypothesis that word_eval separates trace classes: two length-L words
   reaching the same deck permutation are already related by commuting swaps.
   This is the RAAG analogue of word-eval injectivity for free generators.
   It says the deck group satisfies no relation beyond those the commutation
   graph declares, up to length L, and it is exactly what upgrades the
   inequality search_space <= n_traces to an equality. *)
Definition raag_weval_inj (L : nat) : Prop :=
  forall w1 w2 : pgg_word M L, word_eval w1 = word_eval w2 -> trace_equiv w1 w2.

(** Under raag_weval_inj at length L, the search space equals the trace count.
    The commutation graph then accounts for every collision among length-L
    words, so counting words modulo commutation counts deck permutations
    exactly.  Drop the hypothesis and only the inequality of
    search_space_le_traces survives. *)
Lemma raag_weval_inj_search_space L :
  raag_weval_inj L -> @search_space M L = n_traces L.
Proof.
move=> Hraag.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  exact: search_space_le_traces.
(* n_traces <= search_space: word_eval is injective on roots *)
rewrite /search_space /achievable /n_traces.
set e := adj_swap_sym (L:=L).
have Hsym := sym_connect_sym (@adj_swap_sym_sym R L).
set D := predI (roots e) (mem {: pgg_word M L}).
suff Hinj : {in D &, injective (@word_eval M L)}.
  have <- : #|[set word_eval r | r in D]| = n_comp e {: pgg_word M L}.
    by rewrite (card_in_imset Hinj).
  apply: subset_leq_card.
  apply/subsetP => b /imsetP [r Hr ->].
  by apply/imsetP; exists r => //; move: Hr; rewrite !inE andbT.
move=> r1 r2 Hr1 Hr2 Heq.
move: Hr1 Hr2; rewrite /D !inE !andbT => /eqP Hr1 /eqP Hr2.
have Hconn := Hraag _ _ Heq.
rewrite /trace_equiv /e in Hconn.
by move/(fingraph.rootP Hsym) in Hconn; rewrite Hr1 Hr2 in Hconn.
Qed.

(* Over an independent set, and assuming word_eval separates trace classes,
   distinct words reach distinct deck permutations.
   The |I|^L words of indep_set_traces_lb then reach |I|^L distinct deck
   permutations, moving the lower bound from trace classes to the search
   space itself.  raag_weval_inj is the price of that move; without it the
   bound stays a statement about words modulo commutation. *)
Lemma indep_set_word_eval_inj (I : {set 'I_Tg}) (L : nat) :
  (forall i j : 'I_Tg, i \in I -> j \in I -> i != j -> ~~ comm i j) ->
  raag_weval_inj L ->
  forall (w1 w2 : pgg_word M L),
    (forall k : 'I_L, tnth w1 k \in I) ->
    (forall k : 'I_L, tnth w2 k \in I) ->
    word_eval w1 = word_eval w2 -> w1 = w2.
Proof.
move=> Hindep Hrl w1 w2 H1 H2 Heval.
apply: (indep_set_singleton_traces Hindep H1 H2).
exact: Hrl.
Qed.

End raag_theory.

(* ========================================================================== *)
(* From groups/pgg_raag.v, Section raag_derived                               *)
(* ========================================================================== *)

Section raag_derived.
Variable R : RAAGType.
Let Tg := (@pgg_ngens' R).+1.

(** Distinct generators give distinct deck permutations, so word_eval is
    injective on words of length 1.
    Directly the raag_gen_inj field of the mixin.  No commutation acts on a
    one-letter word, so at length 1 words, trace classes and deck
    permutations coincide. *)
Lemma raag_weval_inj1 : @weval_inj R 1.
Proof. exact: gen_inj_weval_inj1 (@raag_gen_inj R). Qed.

(** At length 1 the search space is the number of generators.
    The base case of every growth statement, and the one length at which the
    three counts of search_space_chain agree. *)
Lemma raag_search_space_1 : @search_space R 1 = Tg.
Proof. exact: weval_inj_search_space raag_weval_inj1. Qed.
End raag_derived.

(* ========================================================================== *)
(* From instances/s5/pgg_raag_s5.v                                            *)
(* ========================================================================== *)

(** s5_weval_inj1 — word evaluation is injective at length 1 for the S_5
    path-RAAG generators: two single-generator words that evaluate to the
    same permutation are the same generator. This is the shortest length at
    which injectivity can hold at all, since length 2 already collapses
    words like [i,i] to the identity because every generator is an
    involution (noted below). *)
Lemma s5_weval_inj1 : @weval_inj (@Gen_PGGTypes 3 3 (path_gen_tuple 3)) 1.
Proof. apply: (weval_inj_of_natB s5_gens_agree). by vm_compute. Qed.

(* Note: word-eval injectivity at L=2 fails because adjacent transpositions
   are involutions (s_i^2 = 1 for all i), so words [i,i] all evaluate to
   the identity. *)

(* ========================================================================== *)
(* From security/pgg_collusion_bound.v, Section weval_inj_collusion           *)
(* ========================================================================== *)

Section weval_inj_collusion.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable T' : nat.
Let T := T'.+1.
Hypothesis TN : (T <= N)%N.

(* Distinct starting card positions *)
Variable starts : T.-tuple 'I_N.
Hypothesis starts_uniq : uniq starts.

(* Generator parameters *)
Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

(* Word-eval injectivity *)
Hypothesis lfree : @weval_inj M L.

Local Notation rho_from_words := (rho_from_words L sigmas).

(* achievable(L) has positive cardinality *)
Lemma achievable_pos : (0 < #|@achievable M L|)%N.
Proof.
rewrite /achievable -/M.
have -> : #|[set word_eval w | w : pgg_word M L]| = @search_space M L by [].
rewrite weval_inj_search_space //.
by rewrite expn_gt0.
Qed.

(** rho_from_words_uniform_supp — conditional on word-eval injectivity
    (lfree), the group-element law induced by a uniformly random length-L
    word is exactly uniform on achievable(L), the set of permutations some
    length-L word reaches. This turns generator-word sampling into an
    idealized Assumption-1 input with epsilon = 0 exactly, not merely
    bounded, for the collusion bound above. *)
Lemma rho_from_words_uniform_supp :
  rho_from_words = @fdist_uniform_supp R _ (@achievable M L) achievable_pos.
Proof.
apply/fdist_ext => g.
rewrite /rho_from_words /word_uniform fdistmapE.
case/boolP: (g \in @achievable M L) => Hg.
  (* g in achievable: exactly one preimage *)
  rewrite fdist_uniform_supp_in //.
  move/imsetP: Hg => [w _ Hgw].
  rewrite (bigD1 w) /=; last by rewrite !inE Hgw eqxx.
  rewrite fdist_uniformE big1 ?addr0; last first.
    move=> w' /andP [Hw' Hneq].
    rewrite inE in Hw'; move/eqP in Hw'.
    rewrite Hgw in Hw'; move/lfree in Hw'.
    by rewrite Hw' eqxx in Hneq.
  congr (_ ^-1).
  have -> : #|@achievable M L| = @search_space M L by [].
  rewrite weval_inj_search_space //.
  by rewrite card_tuple card_ord.
(* g not in achievable: no preimage *)
rewrite fdist_uniform_supp_notin //.
apply: big1 => w; rewrite inE => /eqP Hfw.
exfalso; move/negP: Hg; apply.
by apply/imsetP; exists w.
Qed.

End weval_inj_collusion.

(* ========================================================================== *)
(* From security/pgg_collusion_bound.v: the fiber count, the direct          *)
(* endpoint epsilon, and the two endpoint image bounds                        *)
(* ========================================================================== *)

(******************************************************************************)
(*   Section 7: Fiber equidistribution                                       *)
(*                                                                            *)
(*   Defines fibers (preimages of word_eval) and proves that under uniform   *)
(*   word distribution, the probability of each achievable group element is  *)
(*   proportional to its fiber size. Under word-eval injectivity, fibers    *)
(*   are singletons                                                         *)
(*   and the induced distribution is uniform over achievable(L).             *)
(******************************************************************************)

Section fiber_equidistribution.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

(** card_word_L' — the number of length-L words over Tg generators is
    Tg ^ L, the cardinality witness this section's uniform word law is
    built on. *)
Lemma card_word_L' :
  #|{: L.-tuple 'I_Tg}| = (Tg ^ L).-1.+1.
Proof.
by rewrite card_tuple card_ord prednK // expn_gt0.
Qed.

Let word_unif : R.-fdist (L.-tuple 'I_Tg) := fdist_uniform card_word_L'.

(* Fiber: set of words evaluating to a given group element *)
Definition fiber (g : {perm 'I_N}) : {set L.-tuple 'I_Tg} :=
  [set w | @word_eval M L w == g].

(* The probability of g under rho_from_words equals |fiber g| / Tg^L *)
Lemma fiber_prob (g : {perm 'I_N}) :
  fdistmap (@word_eval M L) word_unif g =
  #|fiber g|%:R / (Tg ^ L)%:R.
Proof.
rewrite fdistmapE.
rewrite (eq_bigl (fun a => a \in fiber g)); last first.
  by move=> w; rewrite !inE.
rewrite (eq_bigr (fun _ => (Tg ^ L)%:R^-1)); last first.
  by move=> w _; rewrite fdist_uniformE card_tuple card_ord.
by rewrite big_const iter_addr addr0 -mulr_natr mulrC mulr1 mulrC mulr_natr.
Qed.

(* Under word-eval injectivity, each fiber has at most one element *)
Lemma weval_inj_fiber_le1 (lfree : @weval_inj M L) (g : {perm 'I_N}) :
  (#|fiber g| <= 1)%N.
Proof.
apply/card_le1_eqP => w1 w2.
rewrite !inE => /eqP Hw1 /eqP Hw2.
by apply: lfree; rewrite Hw1 Hw2.
Qed.

(* Under word-eval injectivity, fibers of achievable elements are singletons *)
Lemma weval_inj_fiber_card1 (lfree : @weval_inj M L) (g : {perm 'I_N}) :
  g \in @achievable M L -> #|fiber g| = 1%N.
Proof.
move=> /imsetP [w _ Hw].
apply/eqP; rewrite eqn_leq weval_inj_fiber_le1 //=.
apply/card_gt0P; exists w.
by rewrite inE Hw.
Qed.

End fiber_equidistribution.

(******************************************************************************)
(*  Section 10: Direct endpoint epsilon for groups with injective perm_endpoint     *)
(*                                                                            *)
(*  When word_eval is injective (weval_inj L) AND perm_endpoint is injective on    *)
(*  achievable(L), the endpoint distribution is uniform_supp over            *)
(*  perm_endpoint(achievable(L)), giving epsilon = 2*(N - Tg^L)/N.                 *)
(*  This is tighter than the DPI bound 2*(N! - Tg^L)/N!.                    *)
(******************************************************************************)

Section direct_endpoint_epsilon.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Hypothesis lfree : @weval_inj M L.

(* The endpoint evaluation function *)
Let eval_at (s : 'I_N) : {perm 'I_N} -> 'I_N :=
  fun sigma => sigma s.

(* eval_at s is injective on achievable(L) for each starting card position s *)
Hypothesis pe_inj :
  forall s : 'I_N,
  {in @achievable M L &, injective (eval_at s)}.

(* The key bound: epsilon = 2*(N - Tg^L)/N with denominator N, not N! *)
Let direct_eps : R := 2%:R * (N - Tg ^ L)%:R / N%:R.

(** direct_eps_ge0 — the direct endpoint epsilon 2(N - Tg^L)/N is
    non-negative, as an upper bound on a TV distance must be. *)
Lemma direct_eps_ge0 : 0 <= direct_eps.
Proof.
rewrite /direct_eps.
apply: divr_ge0; last by rewrite ler0n.
by rewrite mulr_ge0 // ler0n.
Qed.

(** achievable_card_TgL — conditional on word-eval injectivity (lfree),
    the set of permutations reachable by some length-L word has exactly
    Tg ^ L elements: every word gives a distinct permutation, so counting
    achievable permutations reduces to counting words. *)
Lemma achievable_card_TgL : #|@achievable M L| = (Tg ^ L)%N.
Proof.
have -> : #|@achievable M L| = @search_space M L by [].
by rewrite weval_inj_search_space.
Qed.

(** achievable_pos' — the achievable-permutation set is non-empty, the
    positivity witness fdist_uniform_supp requires to put a law on it. *)
Lemma achievable_pos' : (0 < #|@achievable M L|)%N.
Proof. by rewrite achievable_card_TgL expn_gt0. Qed.

(* The image of achievable through eval_at s has cardinality Tg^L *)
Lemma perm_endpoint_image_card (s : 'I_N) :
  #|(eval_at s) @: @achievable M L| = (Tg ^ L)%N.
Proof.
rewrite card_in_imset; last first.
  have Hs : {in @achievable M L &, injective (eval_at s)}.
    exact: pe_inj.
  exact: Hs.
exact: achievable_card_TgL.
Qed.

(** perm_endpoint_image_pos — the endpoint image of achievable permutations
    at card position s is non-empty, the positivity witness needed to put
    a uniform-on-image law on it. *)
Lemma perm_endpoint_image_pos (s : 'I_N) :
  (0 < #|(eval_at s) @: @achievable M L|)%N.
Proof. by rewrite perm_endpoint_image_card expn_gt0. Qed.

(** TgL_leq_N — the number of achievable endpoint values never exceeds N:
    an image of a subset of 'I_N cannot outgrow the carrier, the bound the
    epsilon formulas below simplify against. *)
Lemma TgL_leq_N : (Tg ^ L <= N)%N.
Proof.
rewrite -(perm_endpoint_image_card ord0).
apply: (leq_trans (max_card _)).
by rewrite card_ord.
Qed.

(* Direct endpoint bound: for each card position s, the marginal endpoint
   distribution is at distance 2*(N-Tg^L)/N from uniform.
   This is TIGHTER than the DPI bound 2*(N!-Tg^L)/N!. *)
Theorem var_dist_endpoint_direct (s : 'I_N) :
  var_dist (fdistmap (eval_at s) (rho_from_words L sigmas))
           (fdist_uniform (card_ord N)) <= direct_eps.
Proof.
rewrite (rho_from_words_uniform_supp lfree).
have Hs : {in @achievable M L &, injective (eval_at s)}.
  exact: pe_inj.
rewrite (fdistmap_uniform_supp_inj _ Hs).
rewrite var_dist_uniform_supp.
rewrite perm_endpoint_image_card card_ord /direct_eps.
exact: Order.POrderTheory.lexx.
Qed.

End direct_endpoint_epsilon.

(* Unbalanced endpoint image bound: when |C| <= N (e.g., Tg^L < N),
   the bound 2*(N - img_min)/N still holds. *)
Section endpoint_image_bound_unbalanced.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Hypothesis lfree : @weval_inj M L.

(** var_dist_endpoint_unbalanced — in the unbalanced regime Tg^L <= N, the
    coalition's endpoint marginal at card position s is at TV distance
    exactly
    2(N - |image_s|)/N from uniform, where image_s is the endpoint's image
    of the achievable-permutation set. *)
Lemma var_dist_endpoint_unbalanced
    (HCleN : (Tg ^ L <= N)%N) (s : 'I_N) :
  var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
                     (@rho_from_words R N'' m L sigmas))
           (fdist_uniform (card_ord N)) =
  2%:R * (N - #|(fun sigma : {perm 'I_N} => sigma s) @: @achievable M L|)%:R / N%:R.
Proof.
rewrite (rho_from_words_uniform_supp lfree).
rewrite (@var_dist_fdistmap_unbalanced R _ _ _ _ _ N' (card_ord N)) //.
  by rewrite !card_ord.
rewrite card_ord.
have -> : #|@achievable M L| = @search_space M L by [].
by rewrite weval_inj_search_space.
Qed.

(** var_dist_endpoint_image_bound_unbalanced — a lower bound img_min on
    |image_s| yields the upper bound 2(N - img_min)/N on the coalition's
    endpoint TV distance from uniform in the unbalanced regime, letting a
    concrete instance certify security from a single nat-level cardinality
    computation instead of the exact image size. *)
Lemma var_dist_endpoint_image_bound_unbalanced
    (HCleN : (Tg ^ L <= N)%N) (img_min : nat) (s : 'I_N)
    (Himg : (img_min <= #|(fun sigma : {perm 'I_N} => sigma s) @: @achievable M L|)%N) :
  (var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
                     (@rho_from_words R N'' m L sigmas))
           (fdist_uniform (card_ord N)) <= 2%:R * (N - img_min)%:R / N%:R)%O.
Proof.
rewrite var_dist_endpoint_unbalanced //.
apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
apply: ler_wpM2l; first by rewrite ler0n.
by rewrite ler_nat leq_sub2l.
Qed.

End endpoint_image_bound_unbalanced.

(******************************************************************************)
(*  Section 12: Image size bound via nat-level computation                   *)
(*                                                                            *)
(*  For concrete instances, |perm_endpoint @: achievable| can be computed at the    *)
(*  nat level using eval_word_nat, then reflected to the type level.          *)
(******************************************************************************)

Section endpoint_image_bound.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Hypothesis lfree : @weval_inj M L.

(* When Tg^L = N (balanced), the fiber-counted var_dist reduces to
   the image-size formula 2*(N - |image_s|)/N. *)
Lemma var_dist_endpoint_balanced
    (card_C : (Tg ^ L = N)%N) (s : 'I_N) :
  var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
                     (@rho_from_words R N'' m L sigmas))
           (fdist_uniform (card_ord N)) =
  2%:R * (N - #|(fun sigma : {perm 'I_N} => sigma s) @: @achievable M L|)%:R / N%:R.
Proof.
rewrite (rho_from_words_uniform_supp lfree).
rewrite (@var_dist_fdistmap_balanced R _ _ _ _ _ N' (card_ord N)).
  by rewrite card_ord /M.
have -> : #|@achievable M L| = @search_space M L by [].
by rewrite weval_inj_search_space // card_C.
Qed.

(** var_dist_endpoint_image_bound — the balanced-regime (Tg^L = N) analogue
    of var_dist_endpoint_image_bound_unbalanced: a lower bound img_min on
    |image_s| yields the endpoint TV bound 2(N - img_min)/N from a
    nat-level cardinality computation rather than the exact image size. *)
Lemma var_dist_endpoint_image_bound
    (card_C : (Tg ^ L = N)%N) (img_min : nat) (s : 'I_N)
    (Himg : (img_min <= #|(fun sigma : {perm 'I_N} => sigma s) @: @achievable M L|)%N) :
  (var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
                     (@rho_from_words R N'' m L sigmas))
           (fdist_uniform (card_ord N)) <= 2%:R * (N - img_min)%:R / N%:R)%O.
Proof.
rewrite var_dist_endpoint_balanced //.
apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
apply: ler_wpM2l; first by rewrite ler0n.
by rewrite ler_nat leq_sub2l.
Qed.

End endpoint_image_bound.

(* ========================================================================== *)
(* From reconstruct/algebraic_rigidity.v                                      *)
(* ========================================================================== *)

(******************************************************************************)
(*     Fiber-Counted ShuffleMarginalBound Constructor                         *)
(*                                                                            *)
(* For groups where perm_endpoint is NOT injective on achievable(L), the direct      *)
(* endpoint bound is invalid. Instead, each instance proves its own           *)
(* var_dist bound by fiber counting (case analysis, vm_compute, or            *)
(* parametric algebra). The constructor accepts epsilon + proof directly.      *)
(*                                                                            *)
(* Applicable to: OC (eps=1), S5 (eps=6/5), Star (eps=2(m+1)/(m+3))       *)
(******************************************************************************)

Section fiber_security.

Variable R : realType.
Variable m n' : nat.
Variable sigmas : m.+1.-tuple {perm 'I_n'.+2}.
Let M := Gen_PGGTypes sigmas.

(** The ShuffleMarginalBound assembled directly from a caller-supplied
    epsilon and its per-position var_dist proof, independent of how that
    proof was derived. Groups where perm_endpoint fails to be injective on
    achievable(L) have no uniform closed-form epsilon and must fall back to
    fiber counting (case analysis, vm_compute, parametric algebra); this
    constructor is the common landing point for whatever proof that fiber
    count produces. *)
Definition security_witness_fiber (L : nat)
    (Hlfree : @weval_inj M L)
    (epsilon : R)
    (Hbound : forall s : 'I_n'.+2,
      (var_dist (fdistmap (fun sigma : {perm 'I_n'.+2} => sigma s)
                         (rho_from_words L sigmas))
               (fdist_uniform (card_ord n'.+2)) <= epsilon)%O)
    : ShuffleMarginalBound R M :=
  @MkShuffleMarginalBound R M L epsilon
    (rho_from_words L sigmas) Hbound.

End fiber_security.

(******************************************************************************)
(*     Direct Endpoint ShuffleMarginalBound Constructor                       *)
(*                                                                            *)
(* When perm_endpoint is injective on achievable(L) for each starting card   *)
(* position s,                                                               *)
(* the endpoint distribution is closer to uniform than the DPI bound gives.  *)
(* Epsilon = 2*(N - Tg^L)/N (denominator N, not N!).                         *)
(*                                                                            *)
(* Applicable to: Cyclic (Tg=1, perm_endpoint trivially injective),                 *)
(*                Abelian (Tg=2, N=4, perm_endpoint injective on achievable(1))     *)
(* NOT applicable to: Star, S5, OC, Monster (perm_endpoint not injective on  *)
(*                    achievable for all card positions)                     *)
(******************************************************************************)

Section direct_endpoint_security.

Variable R : realType.
Variable m n' : nat.
Variable sigmas : m.+1.-tuple {perm 'I_n'.+2}.
Let M := Gen_PGGTypes sigmas.

(** The ShuffleMarginalBound built when perm_endpoint is injective on
    achievable(L): the epsilon improves from a generic fiber estimate to the
    closed form 2*(N - Tg^L)/N (denominator N, not N!), since injectivity
    lets the endpoint distribution be counted exactly rather than merely
    bounded. *)
Definition security_witness_endpoint_inj (L : nat)
    (Hlfree : @weval_inj M L)
    (Hinj_s : forall s : 'I_n'.+2,
      {in @achievable M L &,
       injective (fun sigma : {perm 'I_n'.+2} => sigma s)})
    : ShuffleMarginalBound R M :=
  @MkShuffleMarginalBound R M L _
    (rho_from_words L sigmas)
    (var_dist_endpoint_direct Hlfree Hinj_s).

End direct_endpoint_security.

(******************************************************************************)
(*     SecurityProfile: ShuffleMarginalBound + L* + nontriviality             *)
(*                                                                            *)
(* A SecurityProfile bundles a ShuffleMarginalBound with a specific word      *)
(* length sp_Lstar, the turning point at which the bound was established,    *)
(* and a nontriviality witness sp_nontrivial that epsilon < 2, strictly       *)
(* better than the trivial full-variation-distance bound.                    *)
(*                                                                            *)
(* The threshold is 2 rather than 1 because the DPI epsilon is always < 2    *)
(* once Tg^L >= 1, which holds trivially, while epsilon < 1 needs the        *)
(* direct endpoint bound that only some instances can supply; fixing the     *)
(* threshold at 2 lets every existing instance build a SecurityProfile       *)
(* immediately.                                                              *)
(*                                                                            *)
(* The bound is required only at L*, not at every length, because weval_inj  *)
(* is not monotone in L: OC satisfies weval_inj(2) but not weval_inj(3),     *)
(* since its generator cubes collide there.                                  *)
(******************************************************************************)

Section security_profile.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.

Local Open Scope ring_scope.

Let eps_bound := (2%:R : R).

(** A ShuffleMarginalBound at a distinguished word length sp_Lstar, together
    with a proof that its epsilon is strictly below the trivial bound of 2.
    Existence at one length is deliberate: weval_inj need not hold beyond
    sp_Lstar, so the profile makes no monotonicity claim about longer
    words. *)
Record SecurityProfile := MkSecurityProfile {
  sp_Lstar : nat ;
  sp_witness : ShuffleMarginalBound R M ;
  sp_at_Lstar : sw_L sp_witness = sp_Lstar ;
  sp_nontrivial : is_true (Num.lt (sw_bound_eps sp_witness) eps_bound)
}.

(* Builds a SecurityProfile from an AlgebraicRigidity instance once its
   security bound's epsilon is shown below 2: the profile's word length is
   read off the bound's own sw_L, so no new length choice is introduced. *)
Definition ar_security_profile (ar : AlgebraicRigidity R M)
    (Hlt2 : is_true
      (Num.lt (sw_bound_eps (scb_bound (ar_security ar))) eps_bound))
    : SecurityProfile :=
  @MkSecurityProfile
    (sw_L (scb_bound (ar_security ar)))
    (scb_bound (ar_security ar))
    erefl
    Hlt2.

End security_profile.

Arguments SecurityProfile R M : clear implicits.

(* ========================================================================== *)
(* From security/pgg_schreier.v, Section schreier_certificate                 *)
(* ========================================================================== *)

Section schreier_certificate.

Variable R : realType.
Variable m n' : nat.
Let Tg := m.+1.
Let N := n'.+2.

Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.
Let G := pgg_G M.

Local Notation SchreierCertificate := (SchreierCertificate R m n' sigmas).

(* The PGG certificate bundle at word length L: the marginal bound
   sw_bound_eps = sqrt(N) * (1 - sc_lambda_gap sc)^L against
   rho_from_words L sigmas, with the certificate's L-free asymptotic bound
   attached as the optional convergence witness.  Hlfree, weval_inj at L,
   is required of the caller: the spectral bound sc_convergence itself does
   not need it, but the bundle is valid PGG security evidence only once
   rho_from_words L sigmas is known to range over achievable permutations
   without collision. *)
Definition security_witness_schreier (sc : SchreierCertificate)
    (L : nat) (Hlfree : @weval_inj M L) : ShuffleCertificateBundle R M :=
  @MkShuffleCertificateBundle R M
    (@MkShuffleMarginalBound R M L
      (Num.sqrt (N%:R) * (1 - sc_lambda_gap sc) ^+ L)
      (rho_from_words L sigmas)
      (sc_convergence sc L))
    None
    (Some (security_witness_schreier_asymptotic sc)).

End schreier_certificate.
