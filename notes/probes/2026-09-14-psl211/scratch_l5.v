(* scratch_l5: development file for the L5 (setsA_invariant) block of
   probe_orbit.v.  Same statements, none of the 70 seconds of design/count
   vm_compute, so the proof script can be iterated cheaply.  Kept as probe
   evidence; the proved block is transcribed verbatim into probe_orbit.v. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From pgg_smc Require Import pgg_interface.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Load "psl211_tables.v".

Local Definition map_row (g : seq nat) (R : seq nat) : seq nat :=
  sort leq [seq nth 0 g x | x <- R].

Local Definition stable_ok (g : seq nat) (tbl : seq (seq nat)) : bool :=
  all (fun R => map_row g R \in tbl) tbl.

Local Lemma stable_r4A : stable_ok r4_tbl tblA. Proof. by vm_compute. Qed.
Local Lemma stable_r4B : stable_ok r4_tbl tblB. Proof. by vm_compute. Qed.
Local Lemma stable_m6A : stable_ok m6_tbl tblA. Proof. by vm_compute. Qed.
Local Lemma stable_m6B : stable_ok m6_tbl tblB. Proof. by vm_compute. Qed.

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

Local Definition list_to_set (L : seq nat) : {set 'I_12} :=
  [set x : 'I_12 | val x \in L].

Local Definition sets_of (tbl : seq (seq nat)) : {set {set 'I_12}} :=
  [set S | has (fun R => list_to_set R == S) tbl].

Definition setsA := sets_of tblA.
Definition setsB := sets_of tblB.

(* ---- new material for L5 ---- *)

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
