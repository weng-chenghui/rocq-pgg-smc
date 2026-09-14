(* probe_orbit: ledger rows L3-L7 of the PSL(2,11) twelve-card chirality spec.
   All ground checks are vm_compute on nat code lists, as in pgl27_orbit.v.
   PROVER: replace every Admitted by a Qed; keep every statement; report the
   wall-clock time of count_okT and of design5_okT. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From pgg_smc Require Import pgg_interface.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Load "psl211_tables.v".

(* ------------------------------------------------------------------------ *)
(* Ascending code lists of a given size below 12.                           *)
(* ------------------------------------------------------------------------ *)

Local Fixpoint asc_lists (k lo : nat) : seq (seq nat) :=
  match k with
  | 0 => [:: [::]]
  | k'.+1 =>
    flatten [seq [seq a :: L | L <- asc_lists k' a.+1] | a <- iota lo (12 - lo)]
  end.

(* All ascending lists of size exactly k. *)
Local Definition subsets (k : nat) : seq (seq nat) := asc_lists k 0.

Local Lemma size_subsets5 : size (subsets 5) = 792.
Proof. by vm_compute. Qed.

Local Lemma size_subsets6 : size (subsets 6) = 924.
Proof. by vm_compute. Qed.

(* Sublist test on sorted lists (S subset of R). *)
Local Definition subl (S R : seq nat) : bool := all (fun x => x \in R) S.

(* ------------------------------------------------------------------------ *)
(* L3: both tables are 5-designs.                                            *)
(* ------------------------------------------------------------------------ *)

Local Definition design5_ok (tbl : seq (seq nat)) : bool :=
  all (fun S => count (fun R => subl S R) tbl == 1) (subsets 5).

Local Lemma design5_okA : design5_ok tblA. Proof. by vm_compute. Qed.
Local Lemma design5_okB : design5_ok tblB. Proof. by vm_compute. Qed.

(* Mutation: replacing the first row of tblB by the first row of tblA breaks
   the design property (a 5-subset now lies in two rows or in none). *)
Local Definition tblB_mut : seq (seq nat) := behead tblB ++ [:: head [::] tblA].
Local Lemma design5_mut : design5_ok tblB_mut = false. Proof. by vm_compute. Qed.

(* ------------------------------------------------------------------------ *)
(* L4: each generator maps each table to itself.                             *)
(* ------------------------------------------------------------------------ *)

Local Definition map_row (g : seq nat) (R : seq nat) : seq nat :=
  sort leq [seq nth 0 g x | x <- R].

Local Definition stable_ok (g : seq nat) (tbl : seq (seq nat)) : bool :=
  all (fun R => map_row g R \in tbl) tbl.

Local Lemma stable_r4A : stable_ok r4_tbl tblA. Proof. by vm_compute. Qed.
Local Lemma stable_r4B : stable_ok r4_tbl tblB. Proof. by vm_compute. Qed.
Local Lemma stable_m6A : stable_ok m6_tbl tblA. Proof. by vm_compute. Qed.
Local Lemma stable_m6B : stable_ok m6_tbl tblB. Proof. by vm_compute. Qed.

(* Mutation: the non-square scaling of P^1(F_11) transported to this
   labelling would swap the tables; here a cheaper witness: the plain
   reversal of the whole pile is NOT in the group and must move some row of
   tblA outside tblA. *)
Local Definition rev12_tbl : seq nat := [:: 11; 10; 9; 8; 7; 6; 5; 4; 3; 2; 1; 0].
Local Lemma stable_rev12A_false : stable_ok rev12_tbl tblA = false.
Proof. by vm_compute. Qed.

(* ------------------------------------------------------------------------ *)
(* L6, L7: pattern counts.                                                   *)
(* ------------------------------------------------------------------------ *)

(* Intersection of a sorted row with a coalition list. *)
Local Definition inter (R C : seq nat) : seq nat := [seq x <- R | x \in C].

(* Number of rows whose intersection with C is exactly A. *)
Local Definition pcount (tbl : seq (seq nat)) (C A : seq nat) : nat :=
  count (fun R => inter R C == A) tbl.

(* All sublists of an ascending list (patterns A subset C), ascending. *)
Local Fixpoint sublists (C : seq nat) : seq (seq nat) :=
  match C with
  | [::] => [:: [::]]
  | a :: C' => let S := sublists C' in S ++ [seq a :: L | L <- S]
  end.

(* All coalitions of size k, every pattern: equal counts in both tables. *)
Local Definition count_ok_k (k : nat) : bool :=
  all (fun C => all (fun A => pcount tblA C A == pcount tblB C A) (sublists C))
      (subsets k).

Local Definition count_ok : bool :=
  count_ok_k 1 && count_ok_k 2 && count_ok_k 3 && count_ok_k 4 && count_ok_k 5.

(* L6. PROVER: time this one; the spec targets < 5 min. *)
Local Lemma count_okT : count_ok. Proof. by vm_compute. Qed.

(* Mutation: the perturbed table fails already at size 5. *)
Local Definition count_ok5_mut : bool :=
  all (fun C => all (fun A => pcount tblA C A == pcount tblB_mut C A) (sublists C))
      (subsets 5).
Local Lemma count_ok5_mut_false : count_ok5_mut = false. Proof. by vm_compute. Qed.

(* L7: at size 6 the counts differ (the leak): the coalition equal to the
   first row of tblA, pattern the whole coalition: one row in tblA, zero in
   tblB (the two systems are disjoint). *)
Local Lemma leak6 :
  pcount tblA (head [::] tblA) (head [::] tblA) = 1 /\
  pcount tblB (head [::] tblA) (head [::] tblA) = 0.
Proof. by vm_compute. Qed.

(* ------------------------------------------------------------------------ *)
(* L5: from row-wise stability to invariance under the generated group.     *)
(* The shape of pgl27_orbit.v: a stabilising subgroup containing the         *)
(* generators contains pgg_G.  Stated on finsets of 'I_12.                   *)
(* ------------------------------------------------------------------------ *)

Local Definition Imod (k : nat) : 'I_12 := Ordinal (ltn_pmod k (ltn0Sn 11)).
Local Definition tbl_fun (tbl : seq nat) (i : 'I_12) : 'I_12 := Imod (nth 0 tbl i).
Lemma r4_inj : injective (tbl_fun r4_tbl).
Proof.
apply: (can_inj (g := tbl_fun r4_tbl)).
by move=> x; apply: val_inj; case: x => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.
Lemma m6_inj : injective (tbl_fun m6_tbl).
Proof.
apply: (can_inj (g := tbl_fun m6i_tbl)).
by move=> x; apply: val_inj; case: x => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.
Definition psl211_gens : 2.-tuple {perm 'I_12} := [tuple perm r4_inj; perm m6_inj].
Notation psl211_M := (@Gen_PGGTypes 1 10 psl211_gens).

(* A row as a finset of positions. *)
Local Definition list_to_set (L : seq nat) : {set 'I_12} :=
  [set x : 'I_12 | val x \in L].

(* The set of sets of a table. *)
Local Definition sets_of (tbl : seq (seq nat)) : {set {set 'I_12}} :=
  [set S | has (fun R => list_to_set R == S) tbl].

Definition setsA := sets_of tblA.
Definition setsB := sets_of tblB.

Local Definition rows_lt12 (tbl : seq (seq nat)) : bool :=
  all (fun R => all (fun x => (x < 12)%N) R) tbl.
Local Lemma rows_lt12A : rows_lt12 tblA. Proof. by vm_compute. Qed.
Local Lemma rows_lt12B : rows_lt12 tblB. Proof. by vm_compute. Qed.

Local Lemma r4_valE (x : 'I_12) : val ((perm r4_inj) x) = nth 0 r4_tbl (val x).
Proof.
rewrite permE /tbl_fun /Imod /=.
by case: x => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

Local Lemma m6_valE (x : 'I_12) : val ((perm m6_inj) x) = nth 0 m6_tbl (val x).
Proof.
rewrite permE /tbl_fun /Imod /=.
by case: x => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

Local Lemma imset_list_to_set (g : {perm 'I_12}) (t : seq nat) (R : seq nat) :
  (forall x : 'I_12, val (g x) = nth 0 t (val x)) ->
  all (fun x => (x < 12)%N) R ->
  g @: list_to_set R = list_to_set (map_row t R).
Proof.
move=> Hg HR; apply/setP => y; rewrite inE /map_row mem_sort.
apply/imsetP/idP => [[x]|].
  rewrite inE => Hx ->; rewrite Hg.
  by apply/mapP; exists (val x).
case/mapP => v Hv Hy.
have Hv12 : (v < 12)%N by move/allP: HR => /(_ v Hv).
exists (Ordinal Hv12); first by rewrite inE.
by apply: val_inj; rewrite Hg.
Qed.

Local Lemma sets_of_gen_sub (tbl : seq (seq nat)) (g : {perm 'I_12}) (t : seq nat) :
  (forall x : 'I_12, val (g x) = nth 0 t (val x)) ->
  rows_lt12 tbl -> stable_ok t tbl ->
  forall S, S \in sets_of tbl -> (g @: S) \in sets_of tbl.
Proof.
move=> Hg Hlt Hst S; rewrite !inE => /hasP[R Rtbl /eqP <-].
have HR : all (fun x => (x < 12)%N) R by move/allP: Hlt => /(_ R Rtbl).
apply/hasP; exists (map_row t R); first by move/allP: Hst => /(_ R Rtbl).
by rewrite -(imset_list_to_set Hg HR).
Qed.

Local Lemma stab_of_sub (T : finType) (F : T -> T) (A : {set T}) :
  injective F -> (forall x, x \in A -> F x \in A) ->
  forall x, (F x \in A) = (x \in A).
Proof.
move=> Finj Hsub x; apply/idP/idP; last exact: Hsub.
have HFA : F @: A = A.
  apply/eqP; rewrite eqEcard (card_imset _ Finj) leqnn andbT.
  by apply/subsetP => y /imsetP[z zA ->]; exact: Hsub.
by rewrite -{1}HFA => /imsetP[z zA /Finj ->].
Qed.

Local Definition stab_of (A : {set {set 'I_12}}) : {set {perm 'I_12}} :=
  [set g : {perm 'I_12} |
     [forall S : {set 'I_12}, ((g @: S) \in A) == (S \in A)]].

Local Lemma stab_ofP (A : {set {set 'I_12}}) (g : {perm 'I_12}) :
  reflect (forall S : {set 'I_12}, ((g @: S) \in A) = (S \in A))
          (g \in stab_of A).
Proof.
rewrite inE; apply: (iffP forallP) => H S; by [apply/eqP | apply/eqP].
Qed.

Local Lemma group_set_stab_of (A : {set {set 'I_12}}) : group_set (stab_of A).
Proof.
apply/group_setP; split.
  apply/stab_ofP => S.
  have -> : (1%g : {perm 'I_12}) @: S = S.
    apply/setP => x; apply/imsetP/idP => [[y yS ->]|xS]; first by rewrite perm1.
    by exists x => //; rewrite perm1.
  by [].
move=> g h /stab_ofP Hg /stab_ofP Hh; apply/stab_ofP => S.
have -> : ((g * h)%g) @: S = h @: (g @: S).
  by rewrite -imset_comp; apply: eq_imset => x; rewrite permM.
by rewrite Hh Hg.
Qed.

Local Canonical stab_of_group A := Group (group_set_stab_of A).

Local Lemma gens_sub_stab (A : {set {set 'I_12}}) :
  (forall S : {set 'I_12}, (((perm r4_inj) @: S) \in A) = (S \in A)) ->
  (forall S : {set 'I_12}, (((perm m6_inj) @: S) \in A) = (S \in A)) ->
  [set tnth psl211_gens i | i : 'I_2] \subset stab_of A.
Proof.
move=> H1 H2; apply/subsetP => x /imsetP[i _ ->]; apply/stab_ofP.
by case: i => -[|[|//]] Hlt.
Qed.

Local Lemma r4_stabA (S : {set 'I_12}) : (((perm r4_inj) @: S) \in setsA) = (S \in setsA).
Proof.
apply: (stab_of_sub (F := fun S0 : {set 'I_12} => (perm r4_inj) @: S0)).
  exact/imset_inj/perm_inj.
exact: (sets_of_gen_sub r4_valE rows_lt12A stable_r4A).
Qed.

Local Lemma m6_stabA (S : {set 'I_12}) : (((perm m6_inj) @: S) \in setsA) = (S \in setsA).
Proof.
apply: (stab_of_sub (F := fun S0 : {set 'I_12} => (perm m6_inj) @: S0)).
  exact/imset_inj/perm_inj.
exact: (sets_of_gen_sub m6_valE rows_lt12A stable_m6A).
Qed.

Local Lemma r4_stabB (S : {set 'I_12}) : (((perm r4_inj) @: S) \in setsB) = (S \in setsB).
Proof.
apply: (stab_of_sub (F := fun S0 : {set 'I_12} => (perm r4_inj) @: S0)).
  exact/imset_inj/perm_inj.
exact: (sets_of_gen_sub r4_valE rows_lt12B stable_r4B).
Qed.

Local Lemma m6_stabB (S : {set 'I_12}) : (((perm m6_inj) @: S) \in setsB) = (S \in setsB).
Proof.
apply: (stab_of_sub (F := fun S0 : {set 'I_12} => (perm m6_inj) @: S0)).
  exact/imset_inj/perm_inj.
exact: (sets_of_gen_sub m6_valE rows_lt12B stable_m6B).
Qed.

Local Lemma G_sub_stabA : pgg_G psl211_M \subset stab_of setsA.
Proof. by rewrite gen_subG; apply: gens_sub_stab; [exact: r4_stabA | exact: m6_stabA]. Qed.

Local Lemma G_sub_stabB : pgg_G psl211_M \subset stab_of setsB.
Proof. by rewrite gen_subG; apply: gens_sub_stab; [exact: r4_stabB | exact: m6_stabB]. Qed.

(** L5 — membership in the A-system is invariant under the shuffle group. *)
Lemma setsA_invariant (g : pgg_gT psl211_M) (S : {set 'I_12}) :
  g \in pgg_G psl211_M -> ((g @: S) \in setsA) = (S \in setsA).
Proof.
move=> gG.
have /stab_ofP H : g \in stab_of setsA by exact: (subsetP G_sub_stabA).
exact: H.
Qed.

Lemma setsB_invariant (g : pgg_gT psl211_M) (S : {set 'I_12}) :
  g \in pgg_G psl211_M -> ((g @: S) \in setsB) = (S \in setsB).
Proof.
move=> gG.
have /stab_ofP H : g \in stab_of setsB by exact: (subsetP G_sub_stabB).
exact: H.
Qed.

(* Both classes populated, disjoint. *)
Local Definition tables_distinct : bool :=
  all (fun R => all (fun R' => ~~ all (fun n => (n \in R) == (n \in R')) (iota 0 12))
                    tblB) tblA.
Local Lemma tables_distinctT : tables_distinct. Proof. by vm_compute. Qed.

Lemma setsA_B_disjoint : [disjoint setsA & setsB].
Proof.
rewrite -setI_eq0; apply/eqP/setP => S; rewrite !inE.
apply/negbTE; apply/negP => /andP[/hasP[R RA /eqP HR] /hasP[R' RB /eqP HR']].
move/allP: tables_distinctT => /(_ R RA)/allP/(_ R' RB)/negP; apply.
apply/allP => n; rewrite mem_iota add0n /= => Hn.
have E : (n \in R) = (Ordinal Hn \in list_to_set R) by rewrite inE.
have E' : (n \in R') = (Ordinal Hn \in list_to_set R') by rewrite inE.
by rewrite E E' HR HR'.
Qed.

(* ---- assumption audit ---- *)
Print Assumptions r4_inj.
Print Assumptions m6_inj.
Print Assumptions setsA_invariant.
Print Assumptions setsB_invariant.
Print Assumptions setsA_B_disjoint.
