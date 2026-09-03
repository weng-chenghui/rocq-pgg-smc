(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(* PGG Collusion Bound (Theorem 5)                                            *)
(*                                                                             *)
(* Sections 1-5: Generic collusion bound with Assumption 1 as hypothesis.      *)
(*   Main result: d(adversary_posterior, uniform) <= epsilon + 2(T-1)/N        *)
(*   where epsilon = var_dist(rho_dist, uniform(S_N)) is the gap between the   *)
(*   real protocol distribution and the idealized uniform permutation.         *)
(*                                                                             *)
(* Section 6: Word-eval injective instantiation — rho_from_words is           *)
(*   uniform over achievable(L) when word_eval is injective.                   *)
(*   Provides rho_from_words, rho_from_words_uniform_supp, fiber counting.     *)
(*   Concrete epsilon is computed per-instance (not here).                     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*                  Section 1: Triangle inequality for var_dist               *)
(******************************************************************************)

Section var_dist_extra.

Context {R : realType}.
Variable A : finType.

(** var_dist_triangle — total variation distance satisfies the triangle
    inequality. *)
Lemma var_dist_triangle (P Q M : R.-fdist A) :
  var_dist P M <= var_dist P Q + var_dist Q M.
Proof.
rewrite /var_dist -big_split /=.
apply: ler_sum => a _.
have -> : P a - M a = (P a - Q a) + (Q a - M a).
  set p := P a; set q := Q a; set m := M a.
  by rewrite -addrA [- q + _]addrA addNr add0r.
exact: ler_normD.
Qed.

End var_dist_extra.

(******************************************************************************)
(*     Section 1b: Exact transport of var_dist along an injective map         *)
(******************************************************************************)

Section var_dist_inj.

(* R is bound by Variable, not by Context, so that the discharged constant
   keeps the non-maximal implicit R of its former home in s5x5_mixing.v. *)
Variable R : realType.

(** var_dist_fdistmap_inj — an injective reader transports the total variation
    distance exactly: for injective [f],
    [var_dist (fdistmap f P) (fdistmap f Q) = var_dist P Q], the equality case
    of the data processing inequality [var_dist_fdistmap] below. Shared by the
    instance mixing developments, which read a shuffle distribution through an
    injective endpoint reader. *)
Lemma var_dist_fdistmap_inj (A B : finType) (f : A -> B) (P Q : R.-fdist A) :
  injective f -> var_dist (fdistmap f P) (fdistmap f Q) = var_dist P Q.
Proof.
move=> Hinj.
rewrite /var_dist (partition_big f xpredT) //=.
apply: eq_bigr => b _.
rewrite !fdistmapE.
have Hsimp : forall (R' : R.-fdist A),
  \sum_(a in A | a \in preim f (pred1 b)) R' a = \sum_(a | f a == b) R' a.
  by move=> R'; apply: eq_bigl => a /=; rewrite inE.
rewrite !Hsimp -sumrB.
case Hb : [exists a, f a == b]; last first.
  move/negbT/negP: Hb => Hb.
  have Hempty : (fun i : A => f i == b) =1 xpred0.
    move=> a /=. apply/negP => /eqP H. apply: Hb.
    by apply/existsP; exists a; rewrite H.
  by rewrite (eq_bigl _ _ Hempty) (eq_bigl _ _ Hempty) !big_pred0_eq normr0.
move: Hb => /existsP [a /eqP Heq].
rewrite (bigD1 a) /=; last by apply/eqP.
rewrite big1; last first.
  move=> a' /andP [Ha' Hne].
  move/eqP in Ha'. rewrite -Heq in Ha'. move/Hinj in Ha'.
  by rewrite Ha' eqxx in Hne.
rewrite addr0.
rewrite [in RHS](bigD1 a) /=; last by apply/eqP.
rewrite big1 ?addr0 // => a' /andP [Ha' Hne].
move/eqP in Ha'. rewrite -Heq in Ha'. move/Hinj in Ha'.
by rewrite Ha' eqxx in Hne.
Qed.

End var_dist_inj.

(******************************************************************************)
(*          Section 2: Data processing inequality for var_dist                *)
(******************************************************************************)

Section var_dist_dpi.

Context {R : realType}.
Variables (A B : finType).

(* Pushing two distributions forward through the same map never increases
   their TV distance: the data-processing inequality Assumption 1's
   reduction relies on to move a bound on the group-level distribution to
   a bound on an observed coalition endpoint. The reduction is lossy
   through a non-injective f: the group-level spectral bound this
   reduction forces you into carries a sqrt(|G|)-type prefactor that the
   spectral SchreierCertificate route (pgg_schreier.v) avoids by bounding
   var_dist on 'I_N directly with prefactor sqrt(N); DPI should not be
   used in place of that route to derive spectral endpoint bounds.
   It is exact when f is injective (var_dist_fdistmap_inj) and remains the
   right tool for collusion_bound_unconditional below, whose argument does
   not need that tightness. *)
Lemma var_dist_fdistmap (f : A -> B) (P Q : R.-fdist A) :
  var_dist (fdistmap f P) (fdistmap f Q) <= var_dist P Q.
Proof.
rewrite /var_dist.
(* RHS = Σ_a |P a - Q a| = Σ_b Σ_{a : f a = b} |P a - Q a| by partition *)
rewrite (partition_big f xpredT) //=.
(* Now RHS = Σ_b Σ_{a | f a = b} |P a - Q a| *)
apply: ler_sum => b _.
(* LHS summand: |fdistmap f P b - fdistmap f Q b| *)
rewrite fdistmapE [fdistmap _ Q _]fdistmapE -sumrB.
(* |Σ_{a : f a = b} (P a - Q a)| ≤ Σ_{a : f a = b} |P a - Q a| *)
apply: (Order.POrderTheory.le_trans (ler_norm_sum _ _ _)).
apply: ler_sum => a _.
exact: Order.PreorderTheory.lexx.
Qed.

End var_dist_dpi.

(******************************************************************************)
(*     Section 3: Distance between restricted-uniform and full-uniform       *)
(******************************************************************************)

Section var_dist_uniform_supp.

Context {R : realType}.
Variable A : finType.
Variable C : {set A}.
Variable n : nat.
Hypothesis card_A : #|A| = n.+1.
Hypothesis card_C_gt0 : (0 < #|C|)%N.

Let k := (#|A| - #|C|)%N.

(** var_dist_uniform_supp — the TV distance from uniform-on-a-support-C to
    the fully uniform distribution on A is 2k / |A|, where k = |A| - |C| is
    the size of the excluded complement. This is the generic price, in TV
    distance, of shrinking a uniform distribution's support by k elements;
    the file's coalition bounds cash it in wherever a coalition narrows an
    ideal posterior's support. *)
Lemma var_dist_uniform_supp :
  var_dist (@fdist_uniform_supp R A C card_C_gt0) (fdist_uniform card_A) =
  2%:R * k%:R / #|A|%:R.
Proof.
rewrite /var_dist (bigID (fun a => a \in C)) /=.
have HAnz : (#|A|%:R : R) != 0 by rewrite pnatr_eq0 card_A.
have HCnz : (#|C|%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
have HCA : (#|C| <= #|A|)%N by exact: max_card.
(* Sum over a in C: |1/|C| - 1/|A|| *)
have HS1 : \sum_(a | a \in C) `| @fdist_uniform_supp R A C card_C_gt0 a - fdist_uniform card_A a | =
  #|C|%:R * `| #|C|%:R^-1 - #|A|%:R^-1 |.
  rewrite (eq_bigr (fun _ => `| #|C|%:R^-1 - #|A|%:R^-1 |)); last first.
    by move=> a Ha; rewrite fdist_uniform_supp_in // fdist_uniformE.
  by rewrite sumr_const mulr_natl.
(* Sum over a not in C: |0 - 1/|A|| = 1/|A| *)
have HS2 : \sum_(a | a \notin C) `| @fdist_uniform_supp R A C card_C_gt0 a - fdist_uniform card_A a | =
  k%:R * #|A|%:R^-1.
  rewrite (eq_bigr (fun _ => #|A|%:R^-1)); last first.
    move=> a Ha; rewrite fdist_uniform_supp_notin ?Ha // fdist_uniformE.
    by rewrite sub0r normrN ger0_norm // invr_ge0 ler0n.
  rewrite sumr_const mulr_natl.
  suff -> : #|[pred a | a \notin C]| = k by [].
  rewrite /k; have -> : #|[pred a | a \notin C]| = #|~: C|.
    by apply: eq_card => a; rewrite inE inE.
  by rewrite cardsCs setCK.
rewrite HS1 HS2.
(* |1/|C| - 1/|A|| = 1/|C| - 1/|A| since |C| <= |A| *)
have Hge : #|C|%:R^-1 >= #|A|%:R^-1 :> R.
  rewrite lef_pV2 ?posrE ?ltr0n -?lt0n ?card_A //.
  by rewrite -card_A ler_nat; exact: max_card.
rewrite ger0_norm; last by rewrite subr_ge0.
rewrite mulrBr mulfV //.
(* goal: 1 - #|C|%:R * #|A|%:R^-1 + k%:R * #|A|%:R^-1 = 2%:R * k%:R / #|A|%:R *)
set x := k%:R * #|A|%:R^-1.
have -> : #|C|%:R * #|A|%:R^-1 = 1 - x.
  rewrite /x /k natrB // mulrBl mulfV //.
  by rewrite opprB addrC subrK.
by rewrite opprB addrCA subrr addr0 /x -mulrDl -mulr2n mulr_natl.
Qed.

End var_dist_uniform_supp.

(******************************************************************************)
(*  Section 3b: Mixture bound and support lower bound for var_dist            *)
(******************************************************************************)

Section var_dist_mixture_supp.

Variable R : realType.
Import Order.POrderTheory.

(** fdistmap_prod_curryE — the pointwise mass of a product pushforward along
    a curried map is the prior-weighted mixture of the conditional
    pushforwards. *)
Lemma fdistmap_prod_curryE (A B C : finType) (P : R.-fdist A) (Q : R.-fdist B)
    (h : A -> B -> C) (c : C) :
  fdistmap (fun ab : A * B => h ab.1 ab.2) (P `x Q) c
  = \sum_(a : A) P a * fdistmap (h a) Q c.
Proof.
transitivity (\sum_(a : A) \sum_(b : B | h a b == c) P a * Q b).
  rewrite pair_big_dep /= fdistmapE.
  by apply: eq_big => [ab|ab _]; [rewrite inE | rewrite fdist_prodE].
apply: eq_bigr => a _.
rewrite fdistmapE big_distrr /=.
by apply: eq_big => [b|b _]; [rewrite inE|].
Qed.

(** var_dist_fdistmap_prod_mix — the mixture bound: if for every first
    coordinate the two conditional pushforwards are within delta, the two
    product pushforwards are within delta, the two right factors possibly
    on different carriers: var_dist (fdistmap (uncurry h) (P `x Q))
    (fdistmap (uncurry h') (P `x Q')) <= delta from the per-coordinate
    bounds, by joint convexity of the total variation distance. *)
Lemma var_dist_fdistmap_prod_mix (A B B' C : finType) (P : R.-fdist A)
    (Q : R.-fdist B) (Q' : R.-fdist B')
    (h : A -> B -> C) (h' : A -> B' -> C) (delta : R) :
  (forall a : A,
     var_dist (fdistmap (h a) Q) (fdistmap (h' a) Q') <= delta) ->
  var_dist (fdistmap (fun ab : A * B => h ab.1 ab.2) (P `x Q))
           (fdistmap (fun ab : A * B' => h' ab.1 ab.2) (P `x Q')) <= delta.
Proof.
move=> Hd.
rewrite /var_dist.
under eq_bigr do rewrite !fdistmap_prod_curryE -sumrB.
apply: (@le_trans _ _ (\sum_(c : C) \sum_(a : A)
          P a * `|fdistmap (h a) Q c - fdistmap (h' a) Q' c|)).
  apply: ler_sum => c _.
  apply: (le_trans (ler_norm_sum _ _ _)).
  apply: ler_sum => a _.
  by rewrite -mulrBr normrM ger0_norm.
rewrite exchange_big /=.
under eq_bigr do rewrite -big_distrr /=.
apply: (@le_trans _ _ (\sum_(a : A) P a * delta)).
  by apply: ler_sum => a _; rewrite ler_wpM2l //; exact: Hd.
by rewrite -big_distrl /= FDist.f1 mul1r.
Qed.

(** var_dist_supp_ge — a distribution supported on a set of size k among
    n.+1 values is at total variation distance at least 2 (1 - k / n.+1)
    from the uniform distribution: 2%:R * (1 - #|S|%:R / n.+1%:R) <=
    var_dist P (fdist_uniform _) whenever P vanishes outside S. *)
Lemma var_dist_supp_ge (n : nat) (S : {set 'I_n.+1}) (P : R.-fdist 'I_n.+1) :
  (forall v : 'I_n.+1, v \notin S -> P v = 0) ->
  2%:R * (1 - #|S|%:R / n.+1%:R)
  <= var_dist P (fdist_uniform (card_ord n.+1)).
Proof.
move=> HS.
set u := (n.+1%:R^-1 : R).
have Hu0 : (0 : R) <= u by rewrite /u invr_ge0 ler0n.
have HuE : forall v : 'I_n.+1, fdist_uniform (R := R) (card_ord n.+1) v = u.
  by move=> v; rewrite fdist_uniformE card_ord.
have Htot : \sum_(v : 'I_n.+1) u = 1.
  by rewrite sumr_const card_ord -mulr_natl /u mulfV // pnatr_eq0.
have Hblk : \sum_(v in S) u = #|S|%:R * u.
  by rewrite sumr_const mulr_natl.
have Hmass : \sum_(v in S) P v = 1.
  rewrite -(FDist.f1 P) [RHS](bigID (fun v => v \in S)) /=.
  by rewrite [X in _ = _ + X]big1 ?addr0 // => v Hv; exact: HS.
have Hgap : 1 - #|S|%:R * u <= \sum_(v in S) `|P v - u|.
  apply: (le_trans (ler_norm _)).
  have <- : \sum_(v in S) (P v - u) = 1 - #|S|%:R * u.
    by rewrite sumrB Hmass Hblk.
  exact: ler_norm_sum.
have Hcomp : \sum_(v : 'I_n.+1 | v \notin S) u = 1 - #|S|%:R * u.
  have H := Htot.
  rewrite (bigID (fun v => v \in S)) /= Hblk addrC in H.
  exact: (canRL (addrK _) H).
have Hout : \sum_(v : 'I_n.+1 | v \notin S) `|P v - u| = 1 - #|S|%:R * u.
  rewrite -Hcomp; apply: eq_bigr => v Hv.
  by rewrite (HS _ Hv) sub0r normrN ger0_norm.
rewrite /var_dist.
under eq_bigr do rewrite HuE.
rewrite (bigID (fun v => v \in S)) /= Hout.
rewrite mulr_natl mulr2n.
by apply: lerD; [exact: Hgap | exact: lexx].
Qed.

End var_dist_mixture_supp.

(******************************************************************************)
(*                 Section 4: Collusion bound (Theorem 5)                    *)
(******************************************************************************)

Section collusion_bound.

Context {R : realType}.
Variable N' : nat.
Let N := N'.+1.

Variable T' : nat.
Let T := T'.+1.
Hypothesis TN : (T <= N)%N.

(* Distinct starting card positions *)
Variable starts : T.-tuple 'I_N.
Hypothesis starts_uniq : uniq starts.

(* The coalition is {0, ..., T-2}; the unobserved party is T-1 = ord_max *)
Let s_target : 'I_N := tnth starts ord_max.

(* Assumption 1: distribution of rho(P) over S_N *)
Variable rho_dist : R.-fdist {perm 'I_N}.
Variable epsilon : R.
Hypothesis epsilon_ge0 : 0 <= epsilon.

Let card_perm_N : #|{perm 'I_N}| = (N`!.-1).+1 := card_permT_N N'.

Hypothesis assumption1 :
  var_dist rho_dist (fdist_uniform card_perm_N) <= epsilon.

(* The adversary's marginal: push rho_dist through sigma |-> sigma(s_target) *)
Definition adversary_marginal : R.-fdist 'I_N :=
  fdistmap (fun sigma : {perm 'I_N} => sigma s_target) rho_dist.

(* The ideal marginal: same pushforward from the truly uniform distribution *)
Definition ideal_marginal : R.-fdist 'I_N :=
  fdistmap (fun sigma : {perm 'I_N} => sigma s_target) (fdist_uniform card_perm_N).

(* Full uniform over 'I_N *)
Let card_IN : #|'I_N| = N'.+1 := card_ord N.

(** target_uniform — the fully uniform law on 'I_N against which the
    coalition's endpoint marginal is measured. *)
Definition target_uniform : R.-fdist 'I_N := fdist_uniform card_IN.

(* Key lemma: the pushforward of uniform(S_N) through evaluation is uniform(I_N) *)
Lemma ideal_marginal_uniform : ideal_marginal = target_uniform.
Proof.
apply/fdist_ext => a.
rewrite /ideal_marginal /target_uniform /fdistmap fdistbindE fdist_uniformE.
under eq_bigr do rewrite fdist_uniformE fdist1E.
(* goal: Σ_sigma #|perm|^-1 * (a == sigma s_target)%:R = #|I_N|^-1 *)
rewrite -big_distrr /=.
(* goal: #|perm|^-1 * Σ_sigma (a == sigma s_target)%:R = #|I_N|^-1 *)
(* Count: #{sigma | sigma(s_target) = a} = N'! *)
have Hcount : #|[set sigma : {perm 'I_N} | sigma s_target == a]| = N'`!.
  set s1 := fun _ : 'I_1 => s_target.
  set v1 := fun _ : 'I_1 => a.
  have -> : [set sigma : {perm 'I_N} | sigma s_target == a] =
    prescribed s1 v1.
    apply/setP => sigma.
    rewrite /prescribed inE inE.
    apply/eqP/forallP.
      by move=> H i; apply/eqP; rewrite /s1 /v1.
    by move=> /(_ ord0) /eqP.
  have s1_inj : injective s1.
    by move=> i j _; rewrite (ord1 i); rewrite (ord1 j).
  have v1_inj : injective v1.
    by move=> i j _; rewrite (ord1 i); rewrite (ord1 j).
  by rewrite card_prescribed //; rewrite subn1.
have -> : \sum_(i : {perm 'I_N}) (a == i s_target)%:R = N'`!%:R :> R.
  under eq_bigr do rewrite eq_sym.
  rewrite (bigID (fun sigma : {perm 'I_N} => sigma s_target == a)) /=.
  rewrite [X in _ + X]big1; last by move=> sigma /negbTE ->.
  rewrite addr0 (eq_bigr (fun _ => 1)); last by move=> sigma ->.
  rewrite sumr_const; congr (_%:R).
  transitivity #|[set sigma : {perm 'I_N} | sigma s_target == a]|.
    by apply: eq_card => sigma; rewrite !inE.
  exact: Hcount.
rewrite card_permT_N prednK; last exact: fact_gt0.
by rewrite card_ord factS natrM invfM divfK // pnatr_eq0 -lt0n fact_gt0.
Qed.

(* The unconditional bound: pushing Assumption 1's group-level gap epsilon
   through the endpoint-evaluation map (the data processing inequality
   above) gives the same epsilon for the coalition's marginal at a single
   card position, with no overhead from the coalition's other
   observations. *)
Theorem collusion_bound_unconditional :
  var_dist adversary_marginal target_uniform <= epsilon.
Proof.
rewrite -ideal_marginal_uniform /adversary_marginal /ideal_marginal.
exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) assumption1).
Qed.

(* The T-1-slack bound: collusion_bound_unconditional's epsilon, loosened by
   the unconditional additive term 2(T-1)/N so the bound has the same shape
   as collusion_bound_conditional's (Section 5), which does derive that
   term from the coalition's T-1 observed card positions via the triangle
   inequality through the restricted-uniform ideal posterior. *)
Theorem collusion_bound :
  var_dist adversary_marginal target_uniform <= epsilon + 2%:R * T'%:R / N%:R.
Proof.
apply: (Order.POrderTheory.le_trans collusion_bound_unconditional).
rewrite -{1}[epsilon]addr0.
apply: lerD => //.
by rewrite divr_ge0 // ?ler0n // mulr_ge0 // ler0n.
Qed.

End collusion_bound.

(******************************************************************************)
(*     Section 5: Conditional collusion bound with restricted uniform        *)
(******************************************************************************)

(* The conditional version: when the adversary conditions on T-1 observed
   values, the ideal posterior is uniform over N-(T-1) remaining values.
   We axiomatize the adversary's conditional posterior and prove the bound
   using the DPI + restricted-uniform distance calculation. *)

Section collusion_bound_conditional.

Context {R : realType}.
Variable N' : nat.
Let N := N'.+1.

Variable T' : nat.
Let T := T'.+1.
Hypothesis TN : (T <= N)%N.

Let card_IN : #|'I_N| = N'.+1 := card_ord N.
Let full_uniform : R.-fdist 'I_N := fdist_uniform card_IN.

(* Observed values *)
Variable v_obs : 'I_T' -> 'I_N.
Hypothesis v_obs_inj : injective v_obs.

Let remaining := remaining_values v_obs.

Hypothesis card_remaining_gt0 : (0 < #|remaining|)%N.

(* The ideal conditional posterior: uniform over remaining values (from Prop 4) *)
Let ideal_posterior : R.-fdist 'I_N :=
  @fdist_uniform_supp R _ remaining card_remaining_gt0.

(* Adversary's conditional posterior (axiomatized) *)
Variable adversary_posterior : R.-fdist 'I_N.

(* The DPI bound: distance between adversary's and ideal's posteriors *)
Variable epsilon : R.
Hypothesis epsilon_ge0 : 0 <= epsilon.
Hypothesis dpi_bound :
  var_dist adversary_posterior ideal_posterior <= epsilon.

(** card_remaining — the set of card positions the coalition has not
    observed has exactly N - T' elements. *)
Lemma card_remaining : #|remaining| = (N - T')%N.
Proof. exact: card_remaining_values. Qed.

(** collusion_bound_conditional — the coalition's conditional posterior over
    the unobserved card position's value is within epsilon + 2T'/N of
    fully uniform, where epsilon is the DPI-derived distance to the ideal
    posterior conditional on dpi_bound, and
    2T'/N is the unconditional TV price of that ideal posterior itself
    being uniform only over the N - T' card positions the coalition has
    not observed. *)
Theorem collusion_bound_conditional :
  var_dist adversary_posterior full_uniform <= epsilon + 2%:R * T'%:R / N%:R.
Proof.
apply: (Order.POrderTheory.le_trans (var_dist_triangle adversary_posterior ideal_posterior full_uniform)).
apply: lerD => //.
(* var_dist(ideal_posterior, full_uniform) = 2*T'/N *)
rewrite /ideal_posterior /full_uniform.
rewrite var_dist_uniform_supp /=.
rewrite card_remaining card_ord subnBA; last by exact: ltnW.
by rewrite addnC addnK.
Qed.

End collusion_bound_conditional.

(******************************************************************************)
(*  Section 5b: Pushforward of uniform(S_N) through evaluation = uniform(I_N)*)
(*                                                                            *)
(*  Standalone version of ideal_marginal_uniform (Section 4), extracted from  *)
(*  the collusion bound section to make it usable in other contexts.          *)
(******************************************************************************)

Section fdistmap_eval_uniform_section.

Variable R : realType.
Variable N' : nat.
Let N := N'.+1.

Let card_perm_N : #|{perm 'I_N}| = (N`!.-1).+1 := card_permT_N N'.

(** fdistmap_eval_uniform — evaluating a uniformly random permutation of
    'I_N at one fixed card position yields the uniform law on 'I_N: the
    idealized
    endpoint marginal a coalition would see if the protocol realized the
    truly uniform permutation, standalone from the collusion bound's
    Assumption 1 hypothesis. *)
Lemma fdistmap_eval_uniform (s : 'I_N) :
  fdistmap (fun sigma : {perm 'I_N} => sigma s)
           (fdist_uniform card_perm_N : R.-fdist _) =
  (fdist_uniform (card_ord N) : R.-fdist _).
Proof.
apply/fdist_ext => a.
rewrite /fdistmap fdistbindE fdist_uniformE.
under eq_bigr do rewrite fdist_uniformE fdist1E.
rewrite -big_distrr /=.
have Hcount : #|[set sigma : {perm 'I_N} | sigma s == a]| = N'`!.
  set s1 := fun _ : 'I_1 => s.
  set v1 := fun _ : 'I_1 => a.
  have -> : [set sigma : {perm 'I_N} | sigma s == a] =
    prescribed s1 v1.
    apply/setP => sigma.
    rewrite /prescribed inE inE.
    apply/eqP/forallP.
      by move=> H i; apply/eqP; rewrite /s1 /v1.
    by move=> /(_ ord0) /eqP.
  have s1_inj : injective s1.
    by move=> i j _; rewrite (ord1 i); rewrite (ord1 j).
  have v1_inj : injective v1.
    by move=> i j _; rewrite (ord1 i); rewrite (ord1 j).
  by rewrite card_prescribed //; rewrite subn1.
have -> : \sum_(i0 : {perm 'I_N}) (a == i0 s)%:R = N'`!%:R :> R.
  under eq_bigr do rewrite eq_sym.
  rewrite (bigID (fun sigma : {perm 'I_N} => sigma s == a)) /=.
  rewrite [X in _ + X]big1; last by move=> sigma /negbTE ->.
  rewrite addr0 (eq_bigr (fun _ => 1)); last by move=> sigma ->.
  rewrite sumr_const; congr (_%:R).
  transitivity #|[set sigma : {perm 'I_N} | sigma s == a]|.
    by apply: eq_card => sigma; rewrite !inE.
  exact: Hcount.
rewrite card_permT_N prednK; last exact: fact_gt0.
by rewrite card_ord factS natrM invfM divfK // pnatr_eq0 -lt0n fact_gt0.
Qed.

End fdistmap_eval_uniform_section.

(******************************************************************************)
(*  Section 6: Word-eval injective instantiation — concrete epsilon for     *)
(*  Assumption 1                                                             *)
(******************************************************************************)

(* General lemma: fdistmap of uniform through an injective function
   produces fdist_uniform_supp over the image. *)

Section fdistmap_inj_uniform.

Context {R : realType}.
Variables (A B : finType).
Variable f : A -> B.
Hypothesis f_inj : injective f.

Variable Hcard_A : #|A| = #|A|.-1.+1.

Let img := f @: [set: A].
Let Himg_pos : (0 < #|img|)%N.
Proof.
rewrite card_imset ?cardsT //.
by case: #|A| Hcard_A.
Qed.

(** fdistmap_inj_uniform — pushing a uniform law forward through an
    injective map yields the law uniform on the image: the general shape
    behind every injective-word-evaluation argument in this file that turns
    a count of achievable permutations into an exact uniform posterior. *)
Lemma fdistmap_inj_uniform :
  fdistmap f (fdist_uniform Hcard_A) =
  @fdist_uniform_supp R B img Himg_pos.
Proof.
apply/fdist_ext => b.
rewrite fdistmapE.
case/boolP: (b \in img) => Hb.
  (* b in image: exactly one preimage *)
  rewrite fdist_uniform_supp_in //.
  move/imsetP: Hb => [a _ Hab].
  rewrite (bigD1 a) /=; last by rewrite !inE Hab eqxx.
  rewrite fdist_uniformE big1 ?addr0; last first.
    move=> a' /andP [Ha' Hneq].
    rewrite !inE in Ha'.
    move/eqP in Ha'.
    rewrite Hab in Ha'.
    by move/f_inj in Ha'; rewrite Ha' eqxx in Hneq.
  congr (_ ^-1).
  by rewrite card_imset ?cardsT.
(* b not in image: no preimage *)
rewrite fdist_uniform_supp_notin //.
apply: big1 => a.
rewrite inE => /eqP Hfa.
exfalso; move/negP: Hb; apply.
by apply/imsetP; exists a; rewrite ?inE.
Qed.

End fdistmap_inj_uniform.

(* Word-eval injective groups have concrete epsilon for Assumption 1 *)

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

(* Cardinality of word space *)
Lemma card_word_L :
  #|{: L.-tuple 'I_Tg}| = (Tg ^ L).-1.+1.
Proof.
by rewrite card_tuple card_ord prednK // expn_gt0.
Qed.

(* The word distribution: uniform over all L-words *)
Definition word_uniform : R.-fdist (L.-tuple 'I_Tg) :=
  fdist_uniform card_word_L.

(* The induced group element distribution *)
Definition rho_from_words : R.-fdist {perm 'I_N} :=
  fdistmap (@word_eval M L) word_uniform.

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
(*   Section 8: Generalized collusion bound for arbitrary coalition size k  *)
(******************************************************************************)

(* Generalization of the collusion bound to arbitrary coalition size k.
   Instead of observing T-1 out of T endpoints (with 1 unobserved),
   the adversary observes k out of N endpoints. DPI (var_dist_fdistmap)
   gives the bound for ANY number of observed points. *)

Section collusion_bound_k.

Context {R : realType}.
Variable N' : nat.
Let N := N'.+1.

(* Coalition size k (the number of parties the adversary controls) *)
Variable k : nat.
Hypothesis k_pos : (0 < k)%N.
Hypothesis kN : (k <= N)%N.

(* k distinct starting card positions observed by the coalition *)
Variable obs_starts : k.-tuple 'I_N.
Hypothesis obs_starts_uniq : uniq obs_starts.

(* Assumption 1: distribution of rho(P) over S_N *)
Variable rho_dist : R.-fdist {perm 'I_N}.
Variable epsilon : R.
Hypothesis epsilon_ge0 : 0 <= epsilon.

Let card_perm_N : #|{perm 'I_N}| = (N`!.-1).+1 := card_permT_N N'.

Hypothesis assumption1 :
  var_dist rho_dist (fdist_uniform card_perm_N) <= epsilon.

(* The joint observation function: sigma |-> (sigma(s_1), ..., sigma(s_k)) *)
Definition joint_observation (sigma : {perm 'I_N}) : k.-tuple 'I_N :=
  [tuple sigma (tnth obs_starts i) | i < k].

(* The adversary's joint marginal *)
Definition adversary_joint : R.-fdist (k.-tuple 'I_N) :=
  fdistmap joint_observation rho_dist.

(* The ideal joint distribution *)
Definition ideal_joint : R.-fdist (k.-tuple 'I_N) :=
  fdistmap joint_observation (fdist_uniform card_perm_N).

(* Main theorem: DPI gives the bound for joint observations *)
Theorem collusion_bound_k :
  var_dist adversary_joint ideal_joint <= epsilon.
Proof.
rewrite /adversary_joint /ideal_joint.
exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) assumption1).
Qed.

End collusion_bound_k.

(******************************************************************************)
(*   Section 9: Pushforward of uniform_supp through support-injective f     *)
(*                                                                            *)
(*   When f is injective on C, fdistmap f (uniform_supp C) = uniform_supp   *)
(*   (f @: C). Combined with var_dist_uniform_supp, this gives a direct     *)
(*   endpoint epsilon = 2*(N - |f @: C|)/N without going through the DPI.   *)
(******************************************************************************)

Section fdistmap_uniform_supp_inj.

Context {R : realType}.
Variables (A B : finType).
Variable C : {set A}.
Hypothesis card_C_gt0 : (0 < #|C|)%N.
Variable f : A -> B.
Hypothesis f_inj : {in C &, injective f}.

Let img := f @: C.
Let Himg_pos : (0 < #|img|)%N.
Proof. by rewrite card_in_imset. Qed.

(* When f is injective on C, the pushforward of uniform_supp(C) through f
   is uniform_supp(f(C)); combined with var_dist_uniform_supp this gives
   Section 10's direct endpoint epsilon = 2*(N - |f @: C|)/N, avoiding the
   DPI's looser bound through the group order. *)
Lemma fdistmap_uniform_supp_inj :
  fdistmap f (@fdist_uniform_supp R A C card_C_gt0) =
  @fdist_uniform_supp R B img Himg_pos.
Proof.
apply/fdist_ext => b.
rewrite fdistmapE.
case/boolP: (b \in img) => Hb.
  (* b in image: exactly one preimage in C *)
  rewrite fdist_uniform_supp_in //.
  move/imsetP: Hb => [a Ha Hab].
  rewrite (bigD1 a) /=; last by rewrite !inE Hab eqxx.
  rewrite fdist_uniform_supp_in // big1 ?addr0; last first.
    move=> a' /andP [/eqP Ha' Hneq].
    case/boolP: (a' \in C) => Ha'C; last by rewrite fdist_uniform_supp_notin.
    have Habs : a' = a by apply: f_inj Ha'C Ha _; rewrite Ha' Hab.
    by rewrite Habs eqxx in Hneq.
  congr (_ ^-1).
  by rewrite card_in_imset.
(* b not in image: no preimage in C *)
rewrite fdist_uniform_supp_notin //.
apply: big1 => a /eqP Hfa.
case/boolP: (a \in C) => HaC.
  exfalso; move/negP: Hb; apply.
  by rewrite -Hfa; apply/imsetP; exists a.
by rewrite fdist_uniform_supp_notin.
Qed.

End fdistmap_uniform_supp_inj.

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

(******************************************************************************)
(*  Section 11: Balanced-case var_dist for non-injective perm_endpoint              *)
(*                                                                            *)
(*  When |achievable(L)| = N (balanced case, i.e., Tg^L = N), the var_dist  *)
(*  of fdistmap perm_endpoint (uniform_supp achievable) against uniform depends     *)
(*  ONLY on the image size, not the fiber distribution. Specifically:         *)
(*    var_dist = 2*(N - |image_s|)/N                                         *)
(*  This equals the var_dist that uniform_supp(image_s) has from uniform.    *)
(*                                                                            *)
(*  Applicable to: OC (Tg^L = 2^2 = 4 = N)                                  *)
(******************************************************************************)

Section balanced_var_dist.

Context {R : realType}.
Variables (A B : finType).
Variable C : {set A}.
Hypothesis card_C_gt0 : (0 < #|C|)%N.
Variable f : A -> B.
Variable n : nat.
Hypothesis card_B : #|B| = n.+1.
Hypothesis card_C : #|C| = n.+1.

Let img := f @: C.

Let Himg_pos : (0 < #|img|)%N.
Proof.
rewrite card_gt0; apply/set0Pn.
have /card_gt0P [a Ha] := card_C_gt0.
by exists (f a); apply/imsetP; exists a.
Qed.

(* The balanced-case var_dist formula.
   When |C| = |B|, fibers partition C into |B| groups summing to |C| = |B|.
   The var_dist only depends on how many groups are empty (= |B| - |image|). *)
Lemma var_dist_fdistmap_balanced :
  var_dist (fdistmap f (@fdist_uniform_supp R _ C card_C_gt0))
           (fdist_uniform card_B) =
  2%:R * (#|B| - #|img|)%:R / #|B|%:R.
Proof.
rewrite /var_dist.
have HBnz : (#|B|%:R : R) != 0 by rewrite pnatr_eq0 card_B.
have HCnz : (#|C|%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
have HCB : #|C| = #|B| by rewrite card_C card_B.
rewrite (bigID (fun b => b \in img)) /=.
(* For b not in image, fdistmap = 0 *)
have Hnoimg : forall b0 : B, b0 \notin img -> @fdistmap R _ _ f (`U card_C_gt0) b0 = 0.
  move=> b0 Hb0.
  rewrite fdistmapE big1 //.
  move=> a; rewrite inE => /eqP Hfa.
  apply: fdist_uniform_supp_notin; apply/negP => HaC.
  move/negP: Hb0; apply; apply/imsetP; exists a => //.
(* Sum over b not in img: |0 - 1/|B|| = 1/|B|, count = |B| - |img| *)
have HS2 : \sum_(i | i \notin img)
    `|@fdistmap R _ _ f (`U card_C_gt0) i - fdist_uniform card_B i| =
  (#|B| - #|img|)%:R / #|B|%:R.
  under eq_bigr => b0 Hb0.
    rewrite Hnoimg // sub0r normrN ger0_norm ?FDist.ge0 // fdist_uniformE.
    over.
  rewrite sumr_const mulr_natl.
  suff -> : #|[pred i | i \notin img]| = (#|B| - #|img|)%N by [].
  have -> : #|[pred i | i \notin img]| = #|~: img|.
    by apply: eq_card => b0; rewrite inE inE.
  by rewrite cardsCs setCK.
rewrite HS2.
(* Reduce to showing the img-sum also equals (|B|-|img|)/|B| *)
suff HS1 : \sum_(i in img)
    `|@fdistmap R _ _ f (`U card_C_gt0) i - fdist_uniform card_B i| =
  (#|B| - #|img|)%:R / #|B|%:R.
  by rewrite HS1 -mulrDl -mulr2n mulr_natl.
(* Use: Σ_b P(b) = 1 = Σ_b Q(b), so Σ_b (P(b)-Q(b)) = 0 *)
have Hsum0 : \sum_(i : B)
    (@fdistmap R _ _ f (`U card_C_gt0) i - fdist_uniform card_B i) = 0.
  by rewrite sumrB !FDist.f1 subrr.
(* Signed sum over b not in img *)
have Hnoimg_signed : \sum_(i | i \notin img)
    (@fdistmap R _ _ f (`U card_C_gt0) i - fdist_uniform card_B i) =
  - ((#|B| - #|img|)%:R / #|B|%:R).
  rewrite (eq_bigr (fun b0 => - fdist_uniform card_B b0)); last first.
    by move=> b0 Hb0; rewrite Hnoimg // sub0r.
  rewrite sumrN (eq_bigr (fun _ => #|B|%:R^-1)); last first.
    by move=> b0 _; rewrite fdist_uniformE.
  rewrite sumr_const mulr_natl.
  have -> : #|[pred i | i \notin img]| = (#|B| - #|img|)%N.
    have -> : #|[pred i | i \notin img]| = #|~: img|.
      by apply: eq_card => b0; rewrite inE inE.
    by rewrite cardsCs setCK.
  by [].
(* Signed sum over img = (|B|-|img|)/|B| (from Σ=0 and complement) *)
have Hdiff : \sum_(i in img)
    (@fdistmap R _ _ f (`U card_C_gt0) i - fdist_uniform card_B i) =
  (#|B| - #|img|)%:R / #|B|%:R.
  move: Hsum0.
  rewrite (bigID (fun b => b \in img)) /= Hnoimg_signed.
  by move/eqP; rewrite addr_eq0 => /eqP ->; rewrite opprK.
(* Each term in img-sum is non-negative (fiber >= 1 implies P(b) >= Q(b)),
   so |P(b)-Q(b)| = P(b)-Q(b) and the abs-sum equals the signed sum *)
rewrite -Hdiff.
apply: eq_bigr => b0 Hb0.
rewrite ger0_norm //; rewrite subr_ge0.
rewrite fdist_uniformE fdistmapE.
have [a0 Ha0C Hfa0] : exists2 a0, a0 \in C & f a0 = b0.
  by move/imsetP: Hb0 => [a0 Ha0C Hfa0]; exists a0.
rewrite (bigD1 a0) /=; last first.
  by rewrite inE; apply/eqP.
apply: ler_wpDr; first by apply: sumr_ge0 => a _; exact: FDist.ge0.
by rewrite fdist_uniform_supp_in // HCB.
Qed.

End balanced_var_dist.

(* Unbalanced case: when |C| <= |B|, the var_dist formula still holds.
   This applies e.g. to S_5 where |achievable(1)| = 4 < 5 = N. *)
Section unbalanced_var_dist.

Context {R : realType}.
Variables (A B : finType).
Variable C : {set A}.
Hypothesis card_C_gt0 : (0 < #|C|)%N.
Variable f : A -> B.
Variable n : nat.
Hypothesis card_B : #|B| = n.+1.
Hypothesis le_card_CB : (#|C| <= #|B|)%N.

Let img := f @: C.

(** var_dist_fdistmap_unbalanced — pushing the law uniform on a support C
    forward through f and comparing to full uniform on B gives TV distance
    2(|B| - |f @: C|)/|B|, the same closed form as the balanced case,
    without assuming |C| = |B|. *)
Lemma var_dist_fdistmap_unbalanced :
  var_dist (fdistmap f (@fdist_uniform_supp R _ C card_C_gt0))
           (fdist_uniform card_B) =
  2%:R * (#|B| - #|img|)%:R / #|B|%:R.
Proof.
rewrite /var_dist.
have HBnz : (#|B|%:R : R) != 0 by rewrite pnatr_eq0 card_B.
have HCnz : (#|C|%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
rewrite (bigID (fun b => b \in img)) /=.
(* For b not in image, fdistmap = 0 *)
have Hnoimg : forall b0 : B, b0 \notin img -> @fdistmap R _ _ f (`U card_C_gt0) b0 = 0.
  move=> b0 Hb0.
  rewrite fdistmapE big1 //.
  move=> a; rewrite inE => /eqP Hfa.
  apply: fdist_uniform_supp_notin; apply/negP => HaC.
  move/negP: Hb0; apply; apply/imsetP; exists a => //.
(* Sum over b not in img: |0 - 1/|B|| = 1/|B|, count = |B| - |img| *)
have HS2 : \sum_(i | i \notin img)
    `|@fdistmap R _ _ f (`U card_C_gt0) i - fdist_uniform card_B i| =
  (#|B| - #|img|)%:R / #|B|%:R.
  under eq_bigr => b0 Hb0.
    rewrite Hnoimg // sub0r normrN ger0_norm ?FDist.ge0 // fdist_uniformE.
    over.
  rewrite sumr_const mulr_natl.
  suff -> : #|[pred i | i \notin img]| = (#|B| - #|img|)%N by [].
  have -> : #|[pred i | i \notin img]| = #|~: img|.
    by apply: eq_card => b0; rewrite inE inE.
  by rewrite cardsCs setCK.
rewrite HS2.
(* Reduce to showing the img-sum also equals (|B|-|img|)/|B| *)
suff HS1 : \sum_(i in img)
    `|@fdistmap R _ _ f (`U card_C_gt0) i - fdist_uniform card_B i| =
  (#|B| - #|img|)%:R / #|B|%:R.
  by rewrite HS1 -mulrDl -mulr2n mulr_natl.
(* Use: Σ_b P(b) = 1 = Σ_b Q(b), so Σ_b (P(b)-Q(b)) = 0 *)
have Hsum0 : \sum_(i : B)
    (@fdistmap R _ _ f (`U card_C_gt0) i - fdist_uniform card_B i) = 0.
  by rewrite sumrB !FDist.f1 subrr.
(* Signed sum over b not in img *)
have Hnoimg_signed : \sum_(i | i \notin img)
    (@fdistmap R _ _ f (`U card_C_gt0) i - fdist_uniform card_B i) =
  - ((#|B| - #|img|)%:R / #|B|%:R).
  rewrite (eq_bigr (fun b0 => - fdist_uniform card_B b0)); last first.
    by move=> b0 Hb0; rewrite Hnoimg // sub0r.
  rewrite sumrN (eq_bigr (fun _ => #|B|%:R^-1)); last first.
    by move=> b0 _; rewrite fdist_uniformE.
  rewrite sumr_const mulr_natl.
  have -> : #|[pred i | i \notin img]| = (#|B| - #|img|)%N.
    have -> : #|[pred i | i \notin img]| = #|~: img|.
      by apply: eq_card => b0; rewrite inE inE.
    by rewrite cardsCs setCK.
  by [].
(* Signed sum over img = (|B|-|img|)/|B| (from Σ=0 and complement) *)
have Hdiff : \sum_(i in img)
    (@fdistmap R _ _ f (`U card_C_gt0) i - fdist_uniform card_B i) =
  (#|B| - #|img|)%:R / #|B|%:R.
  move: Hsum0.
  rewrite (bigID (fun b => b \in img)) /= Hnoimg_signed.
  by move/eqP; rewrite addr_eq0 => /eqP ->; rewrite opprK.
(* Each term in img-sum is non-negative (fiber >= 1, |C| <= |B| implies
   P(b) = fiber/|C| >= 1/|C| >= 1/|B| = Q(b)) *)
rewrite -Hdiff.
apply: eq_bigr => b0 Hb0.
rewrite ger0_norm //; rewrite subr_ge0.
rewrite fdist_uniformE fdistmapE.
have [a0 Ha0C Hfa0] : exists2 a0, a0 \in C & f a0 = b0.
  by move/imsetP: Hb0 => [a0 Ha0C Hfa0]; exists a0.
rewrite (bigD1 a0) /=; last first.
  by rewrite inE; apply/eqP.
apply: ler_wpDr; first by apply: sumr_ge0 => a _; exact: FDist.ge0.
rewrite fdist_uniform_supp_in //.
rewrite -div1r -[_^-1 in X in _ <= X]div1r.
rewrite ler_pdivlMr ?ltr0n -?lt0n //.
by rewrite mulrC div1r ler_pdivrMr ?mul1r ?ler_nat // ltr0n card_B.
Qed.

End unbalanced_var_dist.

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

(******************************************************************************)
(*     Section 8: Transfer of a pushforward equality along a close prior      *)
(*                                                                            *)
(* Two readers of a distribution P that agree on a nearby ideal               *)
(* distribution Q stay close on P itself. The bound is a triangle             *)
(* inequality through the ideal distribution with a data-processing step      *)
(* on each half.                                                              *)
(******************************************************************************)

(** var_dist_refl — the variation distance of a distribution to itself is
    zero. *)
Lemma var_dist_refl (R : realType) (A : finType) (P : R.-fdist A) :
  var_dist P P = 0.
Proof. by rewrite /var_dist big1 // => a _; rewrite subrr normr0. Qed.

Section var_dist_transfer.
Variables (R : realType) (A B : finType) (P Q : R.-fdist A).
Variables (fx fy : A -> B) (delta : R).
Hypothesis PQ_close : var_dist P Q <= delta.
Hypothesis ideal_eq : fdistmap fx Q = fdistmap fy Q.

(** var_dist_fdistmap_transfer — two readers of a distribution P within delta
    of Q, whose pushforwards along Q are equal, have pushforwards along P
    within delta + delta: var_dist (fdistmap fx P) (fdistmap fy P) <= delta
    + delta, for var_dist P Q <= delta and fdistmap fx Q = fdistmap fy Q. *)
Lemma var_dist_fdistmap_transfer :
  var_dist (fdistmap fx P) (fdistmap fy P) <= delta + delta.
Proof.
apply: (Order.POrderTheory.le_trans (var_dist_triangle _ (fdistmap fx Q) _)).
apply: lerD.
- apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)); exact: PQ_close.
- rewrite ideal_eq symmetric_var_dist.
  apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)); exact: PQ_close.
Qed.

End var_dist_transfer.

Arguments var_dist_fdistmap_transfer : clear implicits.

Check collusion_bound.
Check collusion_bound_unconditional.
Check collusion_bound_conditional.
Check collusion_bound_k.
Check fdistmap_uniform_supp_inj.
Check var_dist_endpoint_direct.
