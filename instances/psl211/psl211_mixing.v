(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_mixing: the binary-N random walk of the PSL(2,11) shuffle and the   *)
(*                variation-distance certificate of its length-584 word       *)
(*                                                                            *)
(* The realistic word shuffle draws letters from the inverse-closed           *)
(* three-letter alphabet of psl211_group.v: reversal of the three             *)
(* four-position segments, the half-Monge shuffle, and the inverse of the     *)
(* half-Monge shuffle. Its state space is the 660-element shuffle group that  *)
(* file enumerates as permutation tables of 'I_12. A binary-N walk of length  *)
(* L = 584 tabulates how many letter words carry the identity to each of the  *)
(* 660 states, and a scalar checker certifies the total-variation bound those *)
(* counts satisfy. Everything after that single kernel computation is exact   *)
(* rewriting.                                                                 *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   walkN L  == the length-L walk distribution over the 660 states           *)
(*   weval w  == the shuffle a length-L letter word evaluates to              *)
(*   fibc L g == the number of length-L letter words whose product is g       *)
(*   Wuni     == the uniform letter law of the realistic word shuffle         *)
(*                                                                            *)
(* Key results:                                                               *)
(*   mixing_bound_okT   == the length-584 walk meets the 2^-40 mixing bound   *)
(*   psl211_word_mixing == the 584-letter word law is within 2^-40 of the     *)
(*                         uniform shuffle in variation distance              *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From Stdlib Require Import BinNat Nnat.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface.
From pgg_smc Require Import psl211_blocks psl211_group psl211_closure.
From pgg_smc Require Import pgg_collusion_bound pgg_weighted_words.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* -------------------------------------------------------------------------- *)
(* The binary-N random walk of length L over the 660 states.                  *)
(* -------------------------------------------------------------------------- *)

(* walkN L s counts the length-L letter words carrying the identity to s. *)
Local Fixpoint walkN (L : nat) : seq N :=
  match L with
  | 0 => 1%num :: nseq 659 0%num
  | L'.+1 =>
    let v := walkN L' in
    [seq foldl (fun acc i => (acc + nth 0%num v i)%num) 0%num preds
    | preds <- psl211_pred_table]
  end.

(* Absolute difference of two binary naturals. *)
Local Definition absdiffN (a b : N) : N :=
  if (a <? b)%num then (b - a)%num else (a - b)%num.

(* The integer form of the mixing bound: 2^40 times the total absolute
   deviation of the 660 walk counts from the uniform value 3^584 / 660, taken
   over the common denominator, is at most 660 * 3^584. *)
Local Definition mixing_bound_ok : bool :=
  let D := (3 ^ 584)%num in
  ((2 ^ 40) * foldl (fun acc c => (acc + absdiffN (660 * c) D)%num) 0%num
                    (walkN 584)
   <=? 660 * D)%num.
(* The length-584 walk meets that integer bound.  It is the only quantitative
   input to the mixing theorem; everything after it is exact rewriting. *)
Local Lemma mixing_bound_okT : mixing_bound_ok.
Proof. Time by vm_compute. Qed.

(* -------------------------------------------------------------------------- *)
(* Binary-N to nat bridges for decoding the walk certificate.                 *)
(* -------------------------------------------------------------------------- *)

Local Lemma powE (n m : nat) : Nat.pow n m = (n ^ m)%N.
Proof. by elim: m => //= m ->; rewrite expnS multE. Qed.
Local Lemma NtoNat_pow (a b : N) :
  N.to_nat (a ^ b)%num = (N.to_nat a ^ N.to_nat b)%N.
Proof. by rewrite N2Nat.inj_pow powE. Qed.
Local Lemma Nle_nat (a b : N) : (a <= b)%num -> (N.to_nat a <= N.to_nat b)%N.
Proof.
move=> Hle.
have Hadd := congr1 N.to_nat (N.sub_add _ _ Hle).
rewrite N2Nat.inj_add plusE in Hadd.
by rewrite -Hadd leq_addl.
Qed.
Local Lemma foldlN_addsum (I : Type) (g : I -> N) (s : seq I) (a0 : N) :
  N.to_nat (foldl (fun acc i => (acc + g i)%num) a0 s)
  = (N.to_nat a0 + \sum_(i <- s) N.to_nat (g i))%N.
Proof.
elim: s a0 => [|x s IH] a0 /=; first by rewrite big_nil addn0.
by rewrite IH big_cons N2Nat.inj_add plusE addnA.
Qed.

(* -------------------------------------------------------------------------- *)
(* The fibre of a length-L word over the three letters, counted by the walk.  *)
(* -------------------------------------------------------------------------- *)

(* The shuffle a length-L letter word evaluates to: the ordered product of its
   letters. *)
Local Definition weval (L : nat) (w : L.-tuple 'I_3) : {perm 'I_12} :=
  (\prod_(i < L) tnth psl211_moves (tnth w i))%g.

(* The fibre count of g at length L: how many of the 3^L letter words have
   product g.  Under the uniform letter law every word carries probability
   3^-L, so fibc L g / 3^L is the word-shuffle law at g exactly.  The whole
   certificate is a statement about this one integer sequence. *)
Local Definition fibc (L : nat) (g : {perm 'I_12}) : nat :=
  #|[set w : L.-tuple 'I_3 | weval w == g]|.

(* A word with one further letter appended. *)
Local Definition rc (L : nat) (p : L.-tuple 'I_3 * 'I_3) : L.+1.-tuple 'I_3 :=
  [tuple of rcons p.1 p.2].

(* Appending a letter multiplies the evaluation on the right by that letter.
   The last letter of a word is the last factor of the product, which is why
   the fibre recursion below walks backwards through inverse letters. *)
Local Lemma weval_last (L : nat) (w : L.-tuple 'I_3) (j : 'I_3) :
  weval (rc (w, j)) = (weval w * tnth psl211_moves j)%g.
Proof.
rewrite /weval big_ord_recr /=; congr (_ * _)%g.
- apply: eq_bigr => i _; congr (tnth psl211_moves _).
  by rewrite !(tnth_nth ord0) /= nth_rcons size_tuple ltn_ord.
- congr (tnth psl211_moves _).
  by rewrite (tnth_nth ord0) /= nth_rcons size_tuple ltnn eqxx.
Qed.

(* Appending a letter is a bijection from word-and-letter pairs onto words one
   letter longer, so a sum over the longer words may be reindexed as a double
   sum over shorter words and letters. *)
Local Lemma rc_bij (L : nat) : bijective (@rc L).
Proof.
exists (fun w : L.+1.-tuple 'I_3 =>
  ([tuple tnth w (widen_ord (leqnSn L) i) | i < L], tnth w ord_max)).
- move=> [w j]; rewrite /rc /=; congr (_, _).
  + apply: eq_from_tnth => i; rewrite tnth_mktuple.
    by rewrite !(tnth_nth ord0) /= nth_rcons size_tuple ltn_ord.
  + by rewrite (tnth_nth ord0) /= nth_rcons size_tuple ltnn eqxx.
- move=> w; apply: val_inj => /=.
  apply: (@eq_from_nth _ ord0).
    by rewrite size_rcons size_map size_enum_ord size_tuple.
  move=> i; rewrite size_rcons size_map size_enum_ord => Hi.
  rewrite nth_rcons size_map size_enum_ord.
  case: (ltnP i L) => HiL.
    rewrite (nth_map (Ordinal HiL)) ?size_enum_ord //.
    by rewrite (tnth_nth ord0) /= nth_enum_ord.
  have -> : i = L by apply/eqP; rewrite eqn_leq HiL andbT -ltnS.
  by rewrite eqxx (tnth_nth ord0).
Qed.

(* fibc L.+1 g is the sum over the three letters j of fibc L (g * sigma_j^-1).
   This is the backward recursion the certificate runs: the words reaching g
   in L+1 steps are the words reaching each of g's three predecessors in L.
   It is stated on the group; walk_step is its image on the 660 state
   indices. *)
Local Lemma fibc_rec (L : nat) (g : {perm 'I_12}) :
  fibc L.+1 g = \sum_(j < 3) fibc L (g * (tnth psl211_moves j)^-1)%g.
Proof.
rewrite /fibc -sum1dep_card.
rewrite (reindex (@rc L)); last exact: (onW_bij _ (rc_bij L)).
have Hpred : (fun p : L.-tuple 'I_3 * 'I_3 => weval (rc p) == g)
          =1 (fun p => weval p.1 == g * (tnth psl211_moves p.2)^-1)%g.
  move=> p; case: p => w j /=.
  by rewrite weval_last; apply/idP/idP => /eqP H; apply/eqP;
     [rewrite -H mulgK | rewrite H mulgVK].
rewrite (eq_bigl _ _ Hpred) big_mkcond /=.
rewrite -(pair_bigA _ (fun (i : L.-tuple 'I_3) (j : 'I_3) =>
  if weval i == (g * (tnth psl211_moves j)^-1)%g then 1 else 0)) /=.
rewrite exchange_big /=.
apply: eq_bigr => j _.
by rewrite -big_mkcond /= sum1dep_card.
Qed.

(* At length zero the only word is empty, so the fibre count is one at the
   identity and zero elsewhere.  This is the initial condition walkN 0 encodes
   as 1 :: nseq 659 0. *)
Local Lemma fibc0 (g : {perm 'I_12}) : fibc 0 g = (g == 1%g).
Proof.
rewrite /fibc.
have -> : [set w : 0.-tuple 'I_3 | weval w == g]
        = if (g == 1%g) then setT else set0.
  apply/setP => w; rewrite inE /weval big_ord0 eq_sym.
  by case: (g == 1%g); rewrite inE.
by case: (g == 1%g); rewrite ?cardsT ?cards0 ?card_tuple ?card_ord ?expn0.
Qed.

(* -------------------------------------------------------------------------- *)
(* The predecessor index and the entry-permutation reverse step.              *)
(* -------------------------------------------------------------------------- *)

(* Every letter of the alphabet lies in the shuffle group. *)
Local Lemma sym_in_G (j : 'I_3) : tnth psl211_moves j \in pgg_G psl211_M.
Proof. by move: (psl211_gen3_of_mem (val j)); rewrite /psl211_gen3_of inord_val.
Qed.

(* The index of the jn-th reverse-walk predecessor of state k: the key at k
   composed with the table of the inverse of letter jn, looked up again. *)
Local Definition predk (k jn : nat) : nat :=
  psl211_tbl_index (psl211_mcomp (nth [::] (unzip1 psl211_elem_table) k)
                                 (psl211_mtbl (psl211_inv_letter jn))).

(* The letter inverting a letter of the alphabet is again a letter. *)
Local Lemma inv_letter_mem (jn : nat) :
  (jn < 3)%N -> psl211_inv_letter jn \in [:: 0; 1; 2].
Proof. by move: jn => [|[|[|]]]. Qed.

Local Lemma predk_mem (k jn : nat) : (k < 660)%N -> (jn < 3)%N ->
  psl211_mcomp (nth [::] (unzip1 psl211_elem_table) k)
               (psl211_mtbl (psl211_inv_letter jn))
    \in unzip1 psl211_elem_table.
Proof.
move=> Hk Hjn; apply: psl211_keys_closed; last exact: inv_letter_mem.
by apply: mem_nth; rewrite psl211_size_keys.
Qed.

Local Lemma predk_lt (k jn : nat) :
  (k < 660)%N -> (jn < 3)%N -> (predk k jn < 660)%N.
Proof. by move=> Hk Hjn; apply: psl211_tbl_index_lt; exact: predk_mem. Qed.

(* entry_perm k * sigma_j^-1 is entry_perm (predk k j), for k below 660.  The
   index arithmetic of psl211_pred_table is right multiplication by the
   inverse letter on the group, so the three predecessor slots the walk reads
   at k name the three group predecessors of the shuffle entry_perm k. *)
Local Lemma entry_pred (k : nat) (j : 'I_3) : (k < 660)%N ->
  (psl211_entry_perm k * (tnth psl211_moves j)^-1)%g
  = psl211_entry_perm (predk k (val j)).
Proof.
move=> Hk.
have Hpred : (predk k (val j) < 660)%N by apply: predk_lt => //; exact: ltn_ord.
apply: psl211_ptbl_inj.
rewrite (psl211_ptbl_entry Hpred) /predk.
rewrite (psl211_tbl_index_key (predk_mem Hk (ltn_ord j))).
by rewrite psl211_ptbl_morph (psl211_ptbl_entry Hk) (psl211_ptbl_inv_letter j).
Qed.

(* -------------------------------------------------------------------------- *)
(* One walk step reads the three reverse-walk predecessors.                   *)
(* -------------------------------------------------------------------------- *)

Local Lemma size_pred_table : size psl211_pred_table = 660.
Proof. by rewrite /psl211_pred_table size_map psl211_size_elem_table. Qed.

(* Row k of psl211_pred_table lists the three predecessor indices of state
   k. *)
Local Lemma nth_pred_table (k : nat) : (k < 660)%N ->
  nth [::] psl211_pred_table k = [seq predk k j | j <- [:: 0; 1; 2]].
Proof.
move=> Hk.
have Hk' : (k < size psl211_elem_table)%N by rewrite psl211_size_elem_table.
rewrite /psl211_pred_table (nth_map ([::], [::]) _ _ Hk').
apply: eq_map => j; rewrite /predk.
by rewrite /unzip1 (nth_map ([::], [::]) _ _ Hk').
Qed.

(* One step of the walk rereads psl211_pred_table: each new entry is the sum
   of the previous vector over that state's three predecessor slots. *)
Local Lemma walkS (L : nat) :
  walkN L.+1
  = [seq foldl (fun acc i => (acc + nth 0%num (walkN L) i)%num) 0%num preds
    | preds <- psl211_pred_table].
Proof. by []. Qed.

(* The walk vector has one entry per state at every length. *)
Local Lemma size_walkN (L : nat) : size (walkN L) = 660.
Proof.
case: L => [|L']; first by [].
by rewrite walkS size_map size_pred_table.
Qed.

(* Read in nat, walkN L.+1 at k is the sum of walkN L over the three entries
   of row k of psl211_pred_table.  This is fibc_rec transported to the state
   indices, with the walk's binary-N additions read as nat sums. *)
Local Lemma walk_step (L k : nat) : (k < 660)%N ->
  N.to_nat (nth 0%num (walkN L.+1) k)
  = \sum_(j < 3) N.to_nat (nth 0%num (walkN L) (predk k (val j))).
Proof.
move=> Hk.
have Hkp : (k < size psl211_pred_table)%N by rewrite size_pred_table.
rewrite walkS (nth_map [::] _ _ Hkp) (nth_pred_table Hk) foldlN_addsum.
rewrite [N.to_nat 0%num]/= add0n big_map.
rewrite -[ [:: 0; 1; 2] ]/(index_iota 0 3) big_mkord.
exact: erefl.
Qed.

(* fibc L (entry_perm k) is the k-th entry of walkN L, for every k below 660.
   This is the bridge between the two layers: the binary-N vector the kernel
   computes is the fibre-count function of the shuffle group, so the 660
   numbers vm_compute produced at L = 584 are the unnormalized word-shuffle
   law. *)
Local Lemma fiber_count (L k : nat) : (k < 660)%N ->
  fibc L (psl211_entry_perm k) = N.to_nat (nth 0%num (walkN L) k).
Proof.
elim: L k => [|L IH] k Hk.
- rewrite fibc0.
  have Hek : (psl211_entry_perm k == 1%g) = (k == 0).
    apply/idP/idP.
    - move/eqP => H1k.
      have H0 : (0 < size psl211_elem_table)%N
        by rewrite psl211_size_elem_table.
      have Hp : nth [::] (unzip1 psl211_elem_table) k
              = nth [::] (unzip1 psl211_elem_table) 0.
        rewrite -(psl211_ptbl_entry Hk) H1k psl211_ptbl_id.
        by rewrite /unzip1 (nth_map ([::], [::]) _ _ H0) psl211_elem_table0.
      have Hks : (k < size (unzip1 psl211_elem_table))%N
        by rewrite psl211_size_keys.
      have H0s : (0 < size (unzip1 psl211_elem_table))%N
        by rewrite psl211_size_keys.
      move: Hp => /eqP.
      rewrite (nth_uniq _ Hks H0s psl211_keys_uniq).
      by move/eqP => ->.
    - move/eqP => ->.
      by rewrite /psl211_entry_perm psl211_elem_table0 /psl211_word3_perm.
  rewrite Hek.
  case: k {Hek} Hk => [|k'] Hk; first by [].
  rewrite -[walkN 0]/(1%num :: nseq 659 0%num).
  rewrite -[nth 0%num (1%num :: nseq 659 0%num) k'.+1]
           /(nth 0%num (nseq 659 0%num) k').
  by rewrite nth_nseq if_same.
- rewrite fibc_rec (@walk_step L k Hk).
  apply: eq_bigr => j _.
  rewrite (@entry_pred k j Hk) (IH _ (predk_lt Hk (ltn_ord j))).
  exact: erefl.
Qed.

(* -------------------------------------------------------------------------- *)
(* Words evaluate inside the shuffle group; the certificate in nat.           *)
(* -------------------------------------------------------------------------- *)

(* Every letter word evaluates inside the shuffle group, so the word shuffle
   puts no mass outside the support of the uniform law it is compared with. *)
Local Lemma word_eval_in_G (L : nat) (w : L.-tuple 'I_3) :
  weval w \in pgg_G psl211_M.
Proof. by apply: group_prod => i _; exact: sym_in_G. Qed.

(* A 660-vector meeting the binary-N certificate inequality meets it in nat:
   2^40 times the total absolute deviation of its entries from the uniform
   value, over the common denominator, is at most 660 * 3^584. *)
Local Lemma cert_decode (v : seq N) :
  size v = 660 ->
  ((2 ^ 40) * foldl (fun acc c => (acc + absdiffN (660 * c) (3 ^ 584)%num)%num)
     0%num v <=? 660 * (3 ^ 584))%num ->
  (2 ^ 40 * (\sum_(k < 660)
       N.to_nat (absdiffN (660 * nth 0%num v k) (3 ^ 584)%num))
   <= 660 * 3 ^ 584)%N.
Proof.
(* The vector v is kept abstract: with v free the numeral rewrites' match
   attempts fail fast instead of forcing the walk through lazy kernel
   reduction. *)
move=> Hsz /N.leb_le/Nle_nat H.
have e2 : N.to_nat 2 = 2 by [].
have e3 : N.to_nat 3 = 3 by [].
have e40 : N.to_nat 40 = 40 by [].
have e584 : N.to_nat 584 = 584 by [].
have e660 : N.to_nat 660 = 660 by [].
move: H.
rewrite !N2Nat.inj_mul !multE !NtoNat_pow e2 e3 e40 e584 e660.
rewrite foldlN_addsum [N.to_nat 0%num]/= add0n.
rewrite (big_nth 0%num) Hsz big_mkord.
move=> H; exact: H.
Qed.

(* The length-584 walk vector meets the nat certificate.  This is the only
   fact about the 660 computed numbers that the real-valued argument uses. *)
Local Lemma mixing_cert_nat :
  (2 ^ 40 * (\sum_(k < 660)
       N.to_nat (absdiffN (660 * nth 0%num (walkN 584) k) (3 ^ 584)%num))
   <= 660 * 3 ^ 584)%N.
Proof.
exact: (cert_decode (size_walkN 584) mixing_bound_okT).
Qed.

(* -------------------------------------------------------------------------- *)
(* The realistic-shuffle mixing bound at L = 584.                             *)
(* -------------------------------------------------------------------------- *)

Section psl211_mixing_sec.
Variable R : realType.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(** Wuni — the uniform law on the three letters.  The dealer draws each
    letter of the word independently and uniformly, so the word shuffle is
    the L-step random walk on the shuffle group along the inverse-closed
    alphabet psl211_moves, and that walk is symmetric. *)
Definition Wuni : R.-fdist 'I_3 := fdist_uniform (card_ord 3).

(* The nat image of a binary-N absolute difference is the real absolute
   difference of the two images.  It carries the certificate's absolute values
   into the variation-distance sum. *)
Local Lemma absN_toR (a b : N) :
  (N.to_nat (absdiffN a b))%:R = `|(N.to_nat a)%:R - (N.to_nat b)%:R| :> R.
Proof.
rewrite /absdiffN; case: ifPn => H.
- move/N.ltb_lt/N.lt_le_incl: H => Hle.
  have Hadd := congr1 N.to_nat (N.sub_add _ _ Hle).
  rewrite N2Nat.inj_add plusE in Hadd.
  have Hsub : (N.to_nat (b - a) = N.to_nat b - N.to_nat a)%N
    by rewrite -Hadd addnK.
  have Hle2 : (N.to_nat a <= N.to_nat b)%N by rewrite -Hadd leq_addl.
  by rewrite Hsub natrB // ler0_norm ?subr_le0 ?ler_nat // opprB.
- move/negbTE: H => /N.ltb_ge Hle.
  have Hadd := congr1 N.to_nat (N.sub_add _ _ Hle).
  rewrite N2Nat.inj_add plusE in Hadd.
  have Hsub : (N.to_nat (a - b) = N.to_nat a - N.to_nat b)%N
    by rewrite -Hadd addnK.
  have Hle2 : (N.to_nat b <= N.to_nat a)%N by rewrite -Hadd leq_addl.
  by rewrite Hsub natrB // ger0_norm ?subr_ge0 ?ler_nat.
Qed.

(* c / D - 1 / 660 = (660 c - D) / (660 D).  Each of the 660 deviations from
   uniform is put over the single denominator 660 * 3^584, so their sum is the
   one integer the certificate bounds. *)
Local Lemma frac_diff (c D : nat) : (0 < D)%N ->
  c%:R / D%:R - 660%:R^-1 = ((660 * c)%:R - D%:R) / (660 * D)%:R :> R.
Proof.
move=> DP.
have HD : (D%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
have H660 : (660%:R : R) != 0 by rewrite pnatr_eq0.
have HDD : ((660 * D)%:R : R) != 0
  by rewrite pnatr_eq0 muln_eq0 negb_or -!lt0n DP.
apply: (mulIf HDD).
rewrite divfK // natrM mulrBl natrM; congr (_ - _).
  by rewrite mulrCA divfK // mulrC.
by rewrite mulrA mulVf // mul1r.
Qed.

(* A numerator meeting 2^40 * SN <= 660 * D has SN / (660 D) <= 2^-40.  The
   last step of the chain, turning the integer certificate into the stated
   real bound. *)
Local Lemma final_bound_gen (SN D : nat) :
  (0 < D)%N -> (2 ^ 40 * SN <= 660 * D)%N ->
  SN%:R / (660 * D)%:R <= 2%:R^-40 :> R.
Proof.
move=> DP Hc.
have HDD : (0 < (660 * D)%:R :> R) by rewrite ltr0n muln_gt0 DP.
rewrite ler_pdivrMr //.
have -> : 2%:R^-40 * (660 * D)%:R = (660 * D)%:R / (2 ^ 40)%:R :> R.
  by rewrite natrX -exprVn mulrC.
rewrite ler_pdivlMr ?ltr0n ?expn_gt0 //.
by rewrite -natrM ler_nat mulnC.
Qed.

(* The word-shuffle law at g is fibc 584 g / 3^584: under the uniform letter
   law each of the 3^584 words has the same probability, so the law of the
   product is the fibre count divided by the number of words.  This is where
   the counting layer meets the probability layer. *)
Local Lemma rho_valE (g : {perm 'I_12}) :
  @rho_from_words_weighted R 10 2 584 psl211_moves Wuni g
  = (fibc 584 g)%:R / (3 ^ 584)%:R.
Proof.
rewrite fiber_prob_weighted.
rewrite (eq_bigr (fun=> (3 ^ 584)%:R^-1)); last first.
  move=> w _.
  rewrite word_weightedE.
  under eq_bigr => i _ do rewrite /Wuni fdist_uniformE card_ord.
  by rewrite prodr_const card_ord exprVn natrX.
by rewrite sumr_const [X in _ = X]mulrC mulr_natr; congr (_ *+ _).
Qed.

(* The word-shuffle law is within 2^-40 of the uniform law on Gg in variation
   distance, given that Gg has 660 elements injectively enumerated by ep, that
   every word evaluates inside Gg, that the fibre count of ep k is the k-th
   entry of vN, and that vN meets the nat certificate.  The bound is
   unconditional and information-theoretic: no computational assumption enters
   at any point.  Stated over abstract Gg, ep and vN so that the single
   vm_compute of the 660 counts is all the real-valued argument depends on;
   psl211_word_mixing supplies the four PSL(2,11) witnesses. *)
Local Lemma mixing_bound_gen
  (Gg : {group {perm 'I_12}}) (ep : nat -> {perm 'I_12}) (vN : nat -> N)
  (GposH : (0 < #|Gg|)%N) :
  #|Gg| = 660 ->
  (forall g, g \in Gg -> g \in [seq ep k | k <- iota 0 660]) ->
  {in iota 0 660 &, injective ep} ->
  (forall k, ep k \in Gg) ->
  (forall k, (k < 660)%N -> fibc 584 (ep k) = N.to_nat (vN k)) ->
  (forall w : 584.-tuple 'I_3, weval w \in Gg) ->
  (2 ^ 40 * (\sum_(k < 660) N.to_nat (absdiffN (660 * vN k) (3 ^ 584)%num))
   <= 660 * 3 ^ 584)%N ->
  var_dist (@rho_from_words_weighted R 10 2 584 psl211_moves Wuni) (`U GposH)
  <= 2%:R^-40.
Proof.
move=> Hcard mem_Gg ep_inj ep_mem fibcnt word_in_G Hcert.
rewrite /var_dist (bigID (fun g => g \in Gg)) /=.
rewrite [X in _ + X]big1 ?addr0; last first.
  move=> g Hg.
  have Hf0 : fibc 584 g = 0.
    rewrite /fibc; apply/eqP; rewrite cards_eq0; apply/eqP; apply/setP => w.
    rewrite !inE; apply/negbTE; apply: contra Hg => /eqP <-; exact: word_in_G.
  by rewrite rho_valE Hf0 mul0r fdist_uniform_supp_notin // subr0 normr0.
have Hperm : perm_eq (enum Gg) [seq ep k | k <- iota 0 660].
  apply: uniq_perm; first exact: enum_uniq.
    by rewrite (map_inj_in_uniq ep_inj); exact: iota_uniq.
  move=> g; rewrite mem_enum.
  apply/idP/idP; first exact: mem_Gg.
  by move=> /mapP[k _ ->]; exact: ep_mem.
rewrite -big_enum (perm_big _ Hperm) big_map.
rewrite -[iota 0 660]/(index_iota 0 660) big_mkord.
rewrite (eq_bigr (fun i : 'I_660 =>
  (N.to_nat (absdiffN (660 * vN i) (3 ^ 584)%num))%:R / (660 * 3 ^ 584)%:R));
    last first.
  move=> i _.
  rewrite rho_valE (fibcnt _ (ltn_ord i)) fdist_uniform_supp_in ?ep_mem //.
  rewrite Hcard frac_diff ?expn_gt0 // normrM normfV.
  rewrite (absN_toR (660 * vN i)%num (3 ^ 584)%num).
  rewrite N2Nat.inj_mul multE NtoNat_pow.
  by rewrite [`|(660 * 3 ^ 584)%:R|]ger0_norm ?ler0n.
rewrite -mulr_suml -natr_sum.
by apply: final_bound_gen; [rewrite expn_gt0 | exact: Hcert].
Qed.

(** psl211_word_mixing — the law of a uniform 584-letter generator word is
    within 2^-40 of the uniform shuffle in variation distance.  The bound is
    unconditional and information-theoretic, a counting fact about the 3^584
    words with no computational assumption anywhere, so any statement proved
    of the idealised uniform shuffle transfers to the shuffle a dealer can
    actually perform at a cost of 2^-40. *)
Lemma psl211_word_mixing :
  var_dist (@rho_from_words_weighted R 10 2 584 psl211_moves Wuni)
           (`U psl211_G_pos)
  <= 2%:R^-40.
Proof.
apply: (@mixing_bound_gen (pgg_G psl211_M)%G psl211_entry_perm
  (fun k => nth 0%num (walkN 584) k) psl211_G_pos psl211_card psl211_mem_entry_perm
  psl211_entry_perm_inj psl211_entry_perm_mem
  (fun k : nat => @fiber_count 584 k)
  (@word_eval_in_G 584) mixing_cert_nat).
Qed.

End psl211_mixing_sec.
