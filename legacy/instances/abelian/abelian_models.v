(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* abelian_models: the two abelian shuffle models and their exact distance    *)
(*                                                                            *)
(* Two probability models sit on the identity-content plug abel_shuffle_plug. *)
(* The ideal one is the uniform distribution on the four-element generated    *)
(* group; the actual one is the pushforward of the uniform distribution on    *)
(* generator words of length L + 1 through the abelian word evaluator.        *)
(*                                                                            *)
(* Both generators are involutions and they commute, so a word evaluates to a *)
(* group element determined by the parity of its count of the first letter. A *)
(* word of positive length therefore reaches exactly one parity class of two  *)
(* elements, each carrying mass one half, and never the other two elements of *)
(* the group. The full-L1 distance from the group uniform is 1 at every       *)
(* positive length. The complete four-endpoint reader abel_reader is globally *)
(* injective, so that distance is unchanged at the executed observation.      *)
(*                                                                            *)
(* Every distance below is stated in the repository's full-L1 convention:     *)
(* var_dist P Q is the sum over the carrier of the absolute differences, with *)
(* no factor one half.                                                        *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   abel_group_uniform  == the ideal model, uniform on the generated group   *)
(*   abel_word_dist      == the actual model at word length L + 1             *)
(*   abel_parity_mass    == the word mass of the odd first-letter class       *)
(*   abel_letter_flip    == the swap of the two generator indices             *)
(*   abel_flip           == the word map swapping the first letter            *)
(*   abel_ideal_adapter  == the SampleAdapter of the ideal model              *)
(*   abel_actual_adapter == the SampleAdapter of the actual model             *)
(*   abel_sample_reader  == the endpoint vector read at a sample point        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   abel_word_evalE     == a word's value from its two letter parities       *)
(*   abel_word_eval_odd, abel_word_eval_even == the parity class at each      *)
(*                          length parity                                     *)
(*   abel_flip_freq      == the first-letter flip inverts the class           *)
(*   abel_word_group_dist == full-L1 distance 1 at every positive length      *)
(*   abel_executed_distance == the same distance after the endpoint reader    *)
(*   abel_executed_observation_distance == the same distance at the two       *)
(*                          models' own sample spaces                         *)
(*   abel_word_group_dist0 == the length-zero distance is 1 + 1/2, not 1      *)
(*   abel_ideal_cut_dist, abel_actual_cut_dist == the two cut distributions   *)
(*   abel_sample_reader_dist == the reader pushforward of the cut             *)
(*                          distribution                                      *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals zmodp matrix.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From infotheo Require Import variation_dist.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import rigidity_abelian_instance abelian_word_collapse.
From pgg_smc Require Import abel_profile abelian_exec.
From pgg_smc Require Import pgg_analysis_status.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

(* abel_M — the abelian two-generator monodromy template at N = 4, the
   Gen_PGGTypes form abel_profile is built over. *)
Local Notation abel_M := (@Gen_PGGTypes 1 2 abel_sigmas).

(******************************************************************************)
(*     The parity invariant of an abelian word                                *)
(******************************************************************************)

(** expg_invol — a power of an involution is the element itself at odd
    exponents and the identity at even ones, so only the parity of the
    exponent survives.  This is the arithmetic behind the collapse of the
    abelian word space to two classes. *)
Lemma expg_invol (gT : finGroupType) (g : gT) : (g * g = 1)%g ->
  forall n, (g ^+ n)%g = (if odd n then g else 1)%g.
Proof.
move=> Hg; elim=> [|n IHn]; first by rewrite expg0.
by rewrite expgS IHn /=; case: (odd n); rewrite ?Hg ?mulg1.
Qed.

(** abel_sigma0 — index 0 of the generator tuple is the transposition
    (0 1). *)
Lemma abel_sigma0 : tnth (@pgg_sigmas abel_M) ord0 = abel_s1.
Proof. by rewrite (tnth_nth abel_s1). Qed.

(** abel_sigma1 — index 1 of the generator tuple is the transposition
    (2 3). *)
Lemma abel_sigma1 : tnth (@pgg_sigmas abel_M) (lift ord0 ord0) = abel_s2.
Proof. by rewrite (tnth_nth abel_s1). Qed.

(** abel_word_evalE — a word evaluates to s1 or not according to the parity of
    its count of the first letter, times s2 or not according to the parity of
    its count of the second.  Commutativity collapses the word to a product of
    powers and each generator being an involution collapses each power to a
    parity, so a word of any length carries exactly two bits of information
    about the shuffle it produces. *)
Lemma abel_word_evalE (n : nat) (w : pgg_word abel_M n) :
  @word_eval abel_M n w
  = ((if odd (@freq_vec abel_M n w ord0) then abel_s1 else 1)
     * (if odd (@freq_vec abel_M n w (lift ord0 ord0)) then abel_s2 else 1))%g.
Proof.
rewrite (abelian_word_eval w abel_G_abelian).
rewrite big_ord_recl big_ord_recl big_ord0 mulg1.
by rewrite abel_sigma0 abel_sigma1 (expg_invol abel_s1K) (expg_invol abel_s2K).
Qed.

(** abel_freq_parity — the parities of the two letter counts add up to the
    parity of the word length.  The word length being fixed, the two bits of
    the previous lemma are not independent: one determines the other, which is
    why a word of given length reaches only two of the four group
    elements. *)
Lemma abel_freq_parity (n : nat) (w : pgg_word abel_M n) :
  odd (@freq_vec abel_M n w (lift ord0 ord0))
  = odd n (+) odd (@freq_vec abel_M n w ord0).
Proof.
have H := freq_vec_sum w.
move: H; rewrite big_ord_recl big_ord_recl big_ord0 addn0 => H.
have K : odd (@freq_vec abel_M n w ord0)
         (+) odd (@freq_vec abel_M n w (lift ord0 ord0)) = odd n
  by rewrite -oddD H.
by rewrite -K addbAC addbb.
Qed.

(** abel_word_eval_odd — a word of odd length evaluates to s1 or to s2 and to
    nothing else, according to the parity of its count of the first letter.
    Half the group is unreachable at odd lengths, and that is the source of
    the fixed distance from uniform proved below. *)
Lemma abel_word_eval_odd (n : nat) (w : pgg_word abel_M n) : odd n ->
  @word_eval abel_M n w
  = if odd (@freq_vec abel_M n w ord0) then abel_s1 else abel_s2.
Proof.
move=> Hn; rewrite abel_word_evalE abel_freq_parity Hn.
by case: (odd (@freq_vec abel_M n w ord0)); rewrite /= ?mulg1 ?mul1g.
Qed.

(** abel_word_eval_even — a word of even length evaluates to the identity or
    to s1 s2 and to nothing else.  It is the complementary half of the group
    to the odd case, so no length reaches all four. *)
Lemma abel_word_eval_even (n : nat) (w : pgg_word abel_M n) : ~~ odd n ->
  @word_eval abel_M n w
  = if odd (@freq_vec abel_M n w ord0) then (abel_s1 * abel_s2)%g else 1%g.
Proof.
move/negbTE => Hn; rewrite abel_word_evalE abel_freq_parity Hn.
by case: (odd (@freq_vec abel_M n w ord0)); rewrite /= ?mulg1 ?mul1g.
Qed.

(******************************************************************************)
(*     The first-letter flip, an involution inverting the class               *)
(******************************************************************************)

(** abel_letter_flip — exchanging the two generator indices.  It is the atom
    of the pairing that shows the two parity classes equinumerous. *)
Definition abel_letter_flip (x : 'I_2) : 'I_2 :=
  if x == ord0 then Ordinal (isT : (1 < 2)%N) else ord0.

(** abel_letter_flipK — swapping the two indices twice returns each. *)
Lemma abel_letter_flipK : involutive abel_letter_flip.
Proof. by move=> x; apply: val_inj; move: x => [[|[|x]] Hx]. Qed.

(** abel_flip — replacing a word's first letter by the other generator and
    leaving the rest alone.  It needs the word to have a first letter, which
    is why it is defined only at positive lengths, and that is the same
    hypothesis the distance theorem carries. *)
Definition abel_flip (n : nat) (w : pgg_word abel_M n.+1)
    : pgg_word abel_M n.+1 :=
  [tuple (if i == ord0 then abel_letter_flip (tnth w i) else tnth w i)
   | i < n.+1].

(** abel_flipK — flipping a word's first letter twice returns the word. *)
Lemma abel_flipK (n : nat) : involutive (@abel_flip n).
Proof.
move=> w; apply: eq_from_tnth => i; rewrite !tnth_mktuple.
by case Hi : (i == ord0); rewrite ?Hi ?abel_letter_flipK.
Qed.

(** abel_flip_inj — the first-letter flip is a bijection of the word space,
    so summing over words is unchanged by applying it. *)
Lemma abel_flip_inj (n : nat) : injective (@abel_flip n).
Proof. exact: can_inj (@abel_flipK n). Qed.

(** abel_flip_freq — flipping the first letter inverts the parity of the count
    of the first letter.  Paired with injectivity, this exhibits a bijection
    between the two parity classes, so each carries exactly half the words and
    the actual model puts mass one half on each of its two reachable
    shuffles. *)
Lemma abel_flip_freq (n : nat) (w : pgg_word abel_M n.+1) :
  odd (@freq_vec abel_M n.+1 (abel_flip w) ord0)
  = ~~ odd (@freq_vec abel_M n.+1 w ord0).
Proof.
rewrite /freq_vec (cardsD1 ord0) [in RHS](cardsD1 ord0).
have Hd : [set i : 'I_n.+1 | tnth (abel_flip w) i == ord0] :\ ord0
        = [set i : 'I_n.+1 | tnth w i == ord0] :\ ord0.
  apply/setP => i; rewrite !in_setD1 !inE tnth_mktuple.
  by case Hi : (i == ord0) => /=; rewrite ?Hi ?Hi //=.
have H0 : (ord0 \in [set i : 'I_n.+1 | tnth (abel_flip w) i == ord0])
        = ~~ (ord0 \in [set i : 'I_n.+1 | tnth w i == ord0]).
  rewrite !inE tnth_mktuple eqxx /abel_letter_flip.
  by case: (tnth w ord0 == ord0).
rewrite Hd H0.
by case: (ord0 \in [set i : 'I_n.+1 | tnth w i == ord0]) => /=; rewrite ?negbK.
Qed.

(******************************************************************************)
(*     The four group elements, as inequations and memberships                *)
(******************************************************************************)

(* The six inequations and four memberships below place the four group
   elements apart from one another and inside the group.  They are what turn
   the distance computation into arithmetic on four named masses. *)

(** abel_s2_neq_s1E — the second generator differs from the first. *)
Lemma abel_s2_neq_s1E : (abel_s2 == abel_s1) = false.
Proof. by rewrite eq_sym abel_s1_neq_s2E. Qed.

(** abel_s1s2_neq_s1 — the generator product differs from the first generator. *)
Lemma abel_s1s2_neq_s1 : ((abel_s1 * abel_s2)%g == abel_s1) = false.
Proof. by rewrite eq_sym abel_s1_neq_s1s2. Qed.

(** abel_s1s2_neq_s2 — the generator product differs from the second generator. *)
Lemma abel_s1s2_neq_s2 : ((abel_s1 * abel_s2)%g == abel_s2) = false.
Proof. by rewrite eq_sym abel_s2_neq_s1s2. Qed.

(** abel_s1s2_neq_1 — the generator product differs from the identity. *)
Lemma abel_s1s2_neq_1 : ((abel_s1 * abel_s2)%g == 1%g) = false.
Proof. by rewrite eq_sym abel_1_neq_s1s2. Qed.

(** abel_s1_neq_1 — the first generator differs from the identity. *)
Lemma abel_s1_neq_1 : (abel_s1 == 1%g) = false.
Proof. by rewrite eq_sym abel_1_neq_s1. Qed.

(** abel_s2_neq_1 — the second generator differs from the identity. *)
Lemma abel_s2_neq_1 : (abel_s2 == 1%g) = false.
Proof. by rewrite eq_sym abel_1_neq_s2. Qed.

(** abel_in_G4_1 — the identity lies in the generated group. *)
Lemma abel_in_G4_1 : (1%g : {perm 'I_4}) \in abel_G4.
Proof. by rewrite !inE eqxx. Qed.

(** abel_in_G4_s1 — the first generator lies in the generated group. *)
Lemma abel_in_G4_s1 : abel_s1 \in abel_G4.
Proof. by rewrite !inE eqxx ?orbT. Qed.

(** abel_in_G4_s2 — the second generator lies in the generated group. *)
Lemma abel_in_G4_s2 : abel_s2 \in abel_G4.
Proof. by rewrite !inE eqxx ?orbT. Qed.

(** abel_in_G4_s1s2 — the generator product lies in the generated group. *)
Lemma abel_in_G4_s1s2 : (abel_s1 * abel_s2)%g \in abel_G4.
Proof. by rewrite !inE eqxx ?orbT. Qed.

(******************************************************************************)
(*     The two shuffle models and their exact distance                        *)
(******************************************************************************)

Section abel_models.

Variable R : realType.

(** abel_group_uniform — the ideal shuffle model: uniform on the four
    permutations the generators reach.  Taking the ideal inside the generated
    group rather than over all of S_4 is what makes the distance below a
    statement about failure to mix, since a target uniform on S_4 would be
    unreachable for trivial reasons of group size and the number would say
    nothing about the shuffling. *)
Definition abel_group_uniform : R.-fdist {perm 'I_4} :=
  @fdist_uniform_supp R _ _ abel_G4_card_gt0.

(** abel_word_dist — the actual shuffle model: the law of the permutation a
    uniformly random generator word of length L+1 evaluates to.  The length is
    positive by construction, the parameter counting the letters after the
    first, because the length-zero model is a point mass and behaves
    differently. *)
Definition abel_word_dist (L : nat) : R.-fdist {perm 'I_4} :=
  @rho_from_words R 2 1 L.+1 abel_sigmas.

(** abel_word_distE — the mass the actual model gives a permutation is the
    total word mass of the words evaluating to it. *)
Lemma abel_word_distE (L : nat) (g : {perm 'I_4}) :
  abel_word_dist L g
  = \sum_(w : pgg_word abel_M L.+1 | @word_eval abel_M L.+1 w == g)
      (@word_uniform R 1 L.+1) w.
Proof.
rewrite /abel_word_dist /rho_from_words fdistmapE.
by apply: eq_bigl => w; rewrite inE.
Qed.

(** abel_parity_mass — the total word mass of the words whose count of the
    first letter is odd.  By the two evaluation lemmas this is also the mass
    the actual model puts on one of its two reachable permutations. *)
Definition abel_parity_mass (L : nat) : R :=
  \sum_(w : pgg_word abel_M L.+1 | odd (@freq_vec abel_M L.+1 w ord0))
    (@word_uniform R 1 L.+1) w.

(** abel_parity_mass_flip — the odd and the even parity classes carry the same
    word mass, the flip carrying one onto the other. *)
Lemma abel_parity_mass_flip (L : nat) :
  \sum_(w : pgg_word abel_M L.+1 | ~~ odd (@freq_vec abel_M L.+1 w ord0))
    (@word_uniform R 1 L.+1) w = abel_parity_mass L.
Proof.
rewrite (reindex_inj (@abel_flip_inj L)) /abel_parity_mass.
rewrite (eq_bigl (fun w => odd (@freq_vec abel_M L.+1 w ord0)));
  last by move=> w; rewrite abel_flip_freq negbK.
by apply: eq_bigr => w _; rewrite /word_uniform !fdist_uniformE.
Qed.

(** abel_parity_split — the two parity classes together carry all the word
    mass, since every word has a first-letter count of one parity or the
    other. *)
Lemma abel_parity_split (L : nat) :
  abel_parity_mass L
  + \sum_(w : pgg_word abel_M L.+1 | ~~ odd (@freq_vec abel_M L.+1 w ord0))
      (@word_uniform R 1 L.+1) w = 1.
Proof.
rewrite /abel_parity_mass -[RHS](FDist.f1 (@word_uniform R 1 L.+1)).
by rewrite [RHS](bigID (fun w => odd (@freq_vec abel_M L.+1 w ord0))).
Qed.

(** abel_parity_mass_half — each parity class carries mass one half, being
    equal and summing to one. *)
Lemma abel_parity_mass_half (L : nat) : abel_parity_mass L = 2%:R^-1.
Proof.
have h2 : (2%:R : R) != 0 by rewrite pnatr_eq0.
have H := abel_parity_split L.
rewrite abel_parity_mass_flip in H.
have Hx : abel_parity_mass L * 2%:R = 1 by rewrite mulr_natr mulr2n.
by apply: (mulIf h2); rewrite Hx mulVf.
Qed.

(** abel_word_dist_class — when a word's value is one of two permutations
    according to its first-letter parity, the actual model puts a half on each
    and nothing anywhere else.  This is the shape of the actual model at every
    positive length, the two permutations depending on the length's parity. *)
Lemma abel_word_dist_class (L : nat) (a b : {perm 'I_4}) :
  (forall w : pgg_word abel_M L.+1,
     @word_eval abel_M L.+1 w
     = if odd (@freq_vec abel_M L.+1 w ord0) then a else b) ->
  a != b ->
  [/\ abel_word_dist L a = 2%:R^-1, abel_word_dist L b = 2%:R^-1 &
      forall c : {perm 'I_4}, c != a -> c != b -> abel_word_dist L c = 0].
Proof.
move=> Hw Hab; split.
- rewrite abel_word_distE -(abel_parity_mass_half L); apply: eq_bigl => w.
  by rewrite Hw; case: (odd _); rewrite ?eqxx // eq_sym (negbTE Hab).
- rewrite abel_word_distE -(abel_parity_mass_half L) -(abel_parity_mass_flip L).
  apply: eq_bigl => w.
  by rewrite Hw; case: (odd _); rewrite ?eqxx // (negbTE Hab).
- move=> c Hca Hcb; rewrite abel_word_distE big_pred0 // => w.
  by rewrite Hw; case: (odd _); rewrite eq_sym ?(negbTE Hca) ?(negbTE Hcb).
Qed.

(******************************************************************************)
(*     The full-L1 sum over the four-element group                            *)
(******************************************************************************)

(** abel_G4_sum — a sum over the group is the sum of its four named terms. *)
Lemma abel_G4_sum (F : {perm 'I_4} -> R) :
  \sum_(a in abel_G4) F a
  = F 1%g + (F abel_s1 + (F abel_s2 + F (abel_s1 * abel_s2)%g)).
Proof.
rewrite /abel_G4 -!setUA !big_setU1 ?big_set1 //.
- by rewrite inE abel_s2_neq_s1s2.
- by rewrite !inE abel_s1_neq_s2E abel_s1_neq_s1s2.
- by rewrite !inE abel_1_neq_s1 abel_1_neq_s2 abel_1_neq_s1s2.
Qed.

(* The five arithmetic facts below are the numbers the distance computation
   needs, at the masses a four-element uniform and a two-point half-half
   distribution produce. *)

(** abel_two_halves — two halves make one. *)
Lemma abel_two_halves : (2%:R:R)^-1 + 2%:R^-1 = 1.
Proof.
have h2 : (2%:R:R) != 0 by rewrite pnatr_eq0.
by rewrite -mulr2n -(mulr_natl (2%:R^-1 : R) 2) mulfV.
Qed.

(** abel_two_quarters — two quarters make one half. *)
Lemma abel_two_quarters : (4%:R:R)^-1 + 4%:R^-1 = 2%:R^-1.
Proof.
have h4 : (4%:R:R) = 2%:R * 2%:R by rewrite -natrM.
by rewrite h4 invfM -mulrDl abel_two_halves mul1r.
Qed.

(** abel_four_quarters — four quarters make one. *)
Lemma abel_four_quarters :
  (4%:R:R)^-1 + ((4%:R:R)^-1 + ((4%:R:R)^-1 + (4%:R:R)^-1)) = 1.
Proof. by rewrite addrA !abel_two_quarters abel_two_halves. Qed.

(** abel_norm_zero_quarter — the gap between no mass and a quarter. *)
Lemma abel_norm_zero_quarter : `|(0:R) - 4%:R^-1| = 4%:R^-1.
Proof. by rewrite sub0r normrN ger0_norm // invr_ge0 ler0n. Qed.

(** abel_norm_half_quarter — the gap between a half and a quarter. *)
Lemma abel_norm_half_quarter : `|(2%:R:R)^-1 - 4%:R^-1| = 4%:R^-1.
Proof. by rewrite -abel_two_quarters addrK ger0_norm // invr_ge0 ler0n. Qed.

(** abel_quarter_le1 — a quarter is at most one. *)
Lemma abel_quarter_le1 : (4%:R : R)^-1 <= 1.
Proof. by rewrite invf_le1 ?ler1n // ltr0n. Qed.

(** abel_group_uniform_in — the ideal model gives each of the four group
    elements mass one quarter. *)
Lemma abel_group_uniform_in (g : {perm 'I_4}) :
  g \in abel_G4 -> abel_group_uniform g = 4%:R^-1.
Proof.
move=> Hg; rewrite /abel_group_uniform.
by rewrite (@fdist_uniform_supp_in R _ _ abel_G4_card_gt0 g Hg) abel_G4_card.
Qed.

(** abel_group_uniform_out — the ideal model gives no mass to a permutation
    outside the group, so it and the actual model share a four-element
    support. *)
Lemma abel_group_uniform_out (g : {perm 'I_4}) :
  g \notin abel_G4 -> abel_group_uniform g = 0.
Proof. exact: (@fdist_uniform_supp_notin R _ _ abel_G4_card_gt0 g). Qed.

(** abel_var_distE — for any distribution supported in the group, the full-L1
    distance to the ideal model is the sum of the four gaps at the group's own
    elements.  The rest of the symmetric group contributes nothing because
    both distributions vanish there. *)
Lemma abel_var_distE (P : R.-fdist {perm 'I_4}) :
  (forall g, g \notin abel_G4 -> P g = 0) ->
  var_dist P abel_group_uniform
  = `|P 1%g - 4%:R^-1|
    + (`|P abel_s1 - 4%:R^-1|
       + (`|P abel_s2 - 4%:R^-1| + `|P (abel_s1 * abel_s2)%g - 4%:R^-1|)).
Proof.
move=> HP.
rewrite /var_dist (bigID (fun a : {perm 'I_4} => a \in abel_G4)) /=.
rewrite [X in _ + X]big1; last first.
  by move=> g Hg; rewrite HP // abel_group_uniform_out // subrr normr0.
rewrite addr0 (abel_G4_sum (fun a => `|P a - abel_group_uniform a|)).
by rewrite !abel_group_uniform_in // !inE eqxx ?orbT.
Qed.

(******************************************************************************)
(*     The exact distance                                                     *)
(******************************************************************************)

(** abel_word_group_dist — the actual and ideal shuffle models sit at full-L1
    distance exactly one, at every positive word length, out of a maximum of
    two.  The distance is an equality rather than a bound and it does not
    depend on the length, so no number of rounds brings this instance closer
    to its own ideal.  It is a mixing limitation and not a privacy statement:
    it speaks about the law of the shuffle, and about no observer's view.  It
    is not commutativity alone that gives it, but the parity invariant of two
    commuting involutions, which confines the actual model to two of the four
    group elements with a half on each. *)
Theorem abel_word_group_dist (L : nat) :
  var_dist (abel_word_dist L) abel_group_uniform = 1.
Proof.
case HL : (odd L.+1).
- case: (abel_word_dist_class (fun w => abel_word_eval_odd w HL)
            (negbT abel_s1_neq_s2E)) => H1 H2 H0.
  have Hsupp : forall g, g \notin abel_G4 -> abel_word_dist L g = 0.
    move=> g Hg; apply: H0.
      by apply/eqP => Habs; move: Hg; rewrite Habs abel_in_G4_s1.
    by apply/eqP => Habs; move: Hg; rewrite Habs abel_in_G4_s2.
  rewrite (abel_var_distE Hsupp) H1 H2.
  rewrite (H0 1%g (negbT abel_1_neq_s1) (negbT abel_1_neq_s2)).
  rewrite (H0 (abel_s1 * abel_s2)%g (negbT abel_s1s2_neq_s1)
              (negbT abel_s1s2_neq_s2)).
  by rewrite !abel_norm_zero_quarter !abel_norm_half_quarter abel_four_quarters.
- case: (abel_word_dist_class (fun w => abel_word_eval_even w (negbT HL))
            (negbT abel_s1s2_neq_1)) => H1 H2 H0.
  have Hsupp : forall g, g \notin abel_G4 -> abel_word_dist L g = 0.
    move=> g Hg; apply: H0.
      by apply/eqP => Habs; move: Hg; rewrite Habs abel_in_G4_s1s2.
    by apply/eqP => Habs; move: Hg; rewrite Habs abel_in_G4_1.
  rewrite (abel_var_distE Hsupp) H1 H2.
  rewrite (H0 abel_s1 (negbT abel_s1_neq_s1s2) (negbT abel_s1_neq_1)).
  rewrite (H0 abel_s2 (negbT abel_s2_neq_s1s2) (negbT abel_s2_neq_1)).
  by rewrite !abel_norm_zero_quarter !abel_norm_half_quarter abel_four_quarters.
Qed.

(** abel_executed_distance — reading the four endpoints of the two shuffle
    models leaves them at full-L1 distance exactly one, the same number as
    before the reading.  The reader is injective, so it loses none of the
    distance; the limitation is therefore visible to the protocol's own
    observer and is not an artefact of measuring the shuffle directly. *)
Theorem abel_executed_distance (L : nat) :
  var_dist (fdistmap abel_reader (abel_word_dist L))
           (fdistmap abel_reader abel_group_uniform) = 1.
Proof.
by rewrite (var_dist_fdistmap_inj _ _ abel_reader_inj) abel_word_group_dist.
Qed.

(******************************************************************************)
(*     The length-zero exclusion witness                                      *)
(******************************************************************************)

(** abel_word_dist0E — the empty word evaluates to the identity, so at length
    zero the actual model puts all its mass on the identity. *)
Lemma abel_word_dist0E (g : {perm 'I_4}) :
  (@rho_from_words R 2 1 0 abel_sigmas) g = if g == 1%g then 1 else 0.
Proof.
rewrite /rho_from_words fdistmapE.
have Hwe : forall w : pgg_word abel_M 0, @word_eval abel_M 0 w = 1%g.
  by move=> w; rewrite /word_eval big_ord0.
case Hg : (g == 1%g).
  rewrite -[RHS](FDist.f1 (@word_uniform R 1 0)); apply: eq_bigl => w.
  by rewrite !inE /= Hwe eq_sym Hg.
by rewrite big_pred0 // => w; rewrite !inE /= Hwe eq_sym Hg.
Qed.

(** abel_word_group_dist0 — at word length zero the distance is 1 + 1/2 and
    not 1.  It is the witness that the positive-length hypothesis of
    abel_word_group_dist is load-bearing rather than decorative: at length
    zero the model is a point mass on the identity rather than a half on each
    of two permutations, and the distance is strictly larger. *)
Theorem abel_word_group_dist0 :
  var_dist (@rho_from_words R 2 1 0 abel_sigmas) abel_group_uniform
  = 1 + 2%:R^-1.
Proof.
have Hsupp : forall g, g \notin abel_G4 ->
    (@rho_from_words R 2 1 0 abel_sigmas) g = 0.
  move=> g Hg; rewrite abel_word_dist0E.
  by case Hg1 : (g == 1%g) => //; move: Hg; rewrite (eqP Hg1) abel_in_G4_1.
rewrite (abel_var_distE Hsupp) !abel_word_dist0E eqxx.
rewrite abel_s1_neq_1 abel_s2_neq_1 abel_s1s2_neq_1.
rewrite !abel_norm_zero_quarter ger0_norm;
  last by rewrite subr_ge0 abel_quarter_le1.
by rewrite addrA subrK abel_two_quarters.
Qed.

(******************************************************************************)
(*     The two sample adapters on the shuffle-analysis plug                   *)
(******************************************************************************)

(** abel_ideal_adapter — the ideal model presented as a sampler over the
    identity-content run: the sample is a permutation, drawn uniformly from
    the group, and it is used as the shuffle directly.  Presenting it this way
    lets the ideal and the actual model be compared at the running protocol
    rather than only as distributions. *)
Definition abel_ideal_adapter : SampleAdapter R abel_shuffle_plug :=
  @MkSampleAdapter R abel_profile abel_shuffle_plug
    {perm 'I_4} abel_group_uniform (fun _ => tt) idfun.

(** abel_actual_adapter — the actual model presented as a sampler over the
    same run: the sample is a generator word of length L+1, drawn uniformly,
    and the shuffle is what that word evaluates to.  The randomness sits in
    the word, which is where a real dealer's choice sits. *)
Definition abel_actual_adapter (L : nat) : SampleAdapter R abel_shuffle_plug :=
  @MkSampleAdapter R abel_profile abel_shuffle_plug
    (pgg_word abel_M L.+1) (@word_uniform R 1 L.+1)
    (fun _ => tt) (@word_eval abel_M L.+1).

(** abel_fdistmap_id — pushing a distribution through the identity map leaves
    it unchanged. *)
Lemma abel_fdistmap_id (P : R.-fdist {perm 'I_4}) : fdistmap idfun P = P.
Proof. by apply/fdist_ext => g; rewrite fdistmapE (big_pred1 g). Qed.

(** abel_ideal_cut_dist — the shuffle the ideal sampler produces is
    distributed as the group uniform, its sample being used unchanged. *)
Lemma abel_ideal_cut_dist : sa_cut_dist abel_ideal_adapter = abel_group_uniform.
Proof. exact: abel_fdistmap_id. Qed.

(** abel_actual_cut_dist — the shuffle the word sampler produces is
    distributed as the actual model.  It is what makes the exact distance
    proved above a statement about the distribution this sampler really
    draws. *)
Lemma abel_actual_cut_dist (L : nat) :
  sa_cut_dist (abel_actual_adapter L) = abel_word_dist L.
Proof. by []. Qed.

(** abel_sample_reader — the four endpoints seen when the shuffle is the one a
    given sample selects.  It is the same list the run's verifier collects, so
    a distance measured here is a distance between two things the protocol
    actually exposes. *)
Definition abel_sample_reader (sa : SampleAdapter R abel_shuffle_plug)
    (u : sa_sampleT sa) : 4.-tuple 'I_4 :=
  abel_reader (sa_cut u).

(** abel_sample_reader_dist — the law of the observed endpoints equals the law
    of the shuffle pushed through the reader, whichever sampler is used.  It is
    the equality that carries a distance proved about shuffles down to a
    distance about what is observed. *)
Lemma abel_sample_reader_dist (sa : SampleAdapter R abel_shuffle_plug) :
  fdistmap (@abel_sample_reader sa) (sa_sampleP sa)
  = fdistmap abel_reader (sa_cut_dist sa).
Proof. by rewrite /sa_cut_dist fdistmap_comp. Qed.

(** abel_executed_observation_distance — what the two samplers actually show
    the verifier stays at full-L1 distance exactly one at every word length.
    This is the limitation in its final form, stated over the samplers' own
    sample spaces rather than over shuffles, and it is where the abelian
    negative chain ends.  It is a failure to mix, not a failure of privacy:
    no coalition, no view and no secret appears in it. *)
Theorem abel_executed_observation_distance (L : nat) :
  var_dist
    (fdistmap (@abel_sample_reader (abel_actual_adapter L))
              (sa_sampleP (abel_actual_adapter L)))
    (fdistmap (@abel_sample_reader abel_ideal_adapter)
              (sa_sampleP abel_ideal_adapter)) = 1.
Proof.
rewrite !abel_sample_reader_dist abel_actual_cut_dist abel_ideal_cut_dist.
exact: abel_executed_distance.
Qed.

End abel_models.

(******************************************************************************)
(*     The typed model family of the abelian limitation path                  *)
(******************************************************************************)

(** abel_word_family — the actual model as a family indexed by word length,
    over the identity-content run.  Indexing by length is what makes the
    limitation quantifiable over rounds: the family is the object the
    statement that no length helps is made about. *)
Definition abel_word_family : AnalysisModelFamily abel_shuffle_observed :=
  @MkAnalysisModelFamily abel_shuffle_observed (fun _ => nat)
    (fun R L => @abel_actual_adapter R L).
