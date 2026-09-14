(* probe_group: ledger rows L1, L2 of the PSL(2,11) twelve-card chirality spec.
   Carrier pin: psl211_M := @Gen_PGGTypes 1 10 psl211_gens on 'I_12.
   Compile from the repo root with the project's -R flags (see run.sh).
   PROVER: replace every Admitted by a Qed; keep every statement. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From pgg_smc Require Import pgg_interface.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Load "psl211_tables.v".

Local Definition Imod (k : nat) : 'I_12 := Ordinal (ltn_pmod k (ltn0Sn 11)).
Local Definition tbl_fun (tbl : seq nat) (i : 'I_12) : 'I_12 :=
  Imod (nth 0 tbl i).

(** r4_inj — the quarter-reversal table is an involution, hence injective. *)
Lemma r4_inj : injective (tbl_fun r4_tbl).
Proof.
apply: (can_inj (g := tbl_fun r4_tbl)).
by move=> x; apply: val_inj;
   case: x => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

(** m6_inj — the half-Monge table is cancelled by the half-milk table. *)
Lemma m6_inj : injective (tbl_fun m6_tbl).
Proof.
apply: (can_inj (g := tbl_fun m6i_tbl)).
by move=> x; apply: val_inj;
   case: x => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

Definition r4_perm : {perm 'I_12} := perm r4_inj.
Definition m6_perm : {perm 'I_12} := perm m6_inj.

(** psl211_gens — reverse each quarter, Monge-shuffle each half. *)
Definition psl211_gens : 2.-tuple {perm 'I_12} := [tuple r4_perm; m6_perm].

(* L1: the monodromy template at T = 2 generators, N = 12 positions. *)
Notation psl211_M := (@Gen_PGGTypes 1 10 psl211_gens).

Lemma psl211_N' : pgg_N' psl211_M = 11.
Proof. by []. Qed.

(* Force elaboration of the carrier projections at this instance. *)
Definition psl211_G : {set {perm 'I_12}} := pgg_G psl211_M.
Definition psl211_rho (g : pgg_gT psl211_M) : {perm 'I_12} := @pgg_rho psl211_M g.

Lemma psl211_gens_in_G (i : 'I_2) : tnth psl211_gens i \in pgg_G psl211_M.
Proof. by apply: mem_gen; apply/imsetP; exists i. Qed.

(* Mutation checks: the wrong N parameter and the wrong T parameter fail. *)
Fail Definition bad_N := (@Gen_PGGTypes 1 9 psl211_gens).
Definition bad_T := (@Gen_PGGTypes 2 10 psl211_gens).

(* The generator permutations act as the tables (pgl27_group gfwd shape). *)
Lemma r4_permE (x : 'I_12) : val (r4_perm x) = nth 0 r4_tbl (val x).
Proof.
rewrite permE /tbl_fun /Imod /=.
by case: x => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

Lemma m6_permE (x : 'I_12) : val (m6_perm x) = nth 0 m6_tbl (val x).
Proof.
rewrite permE /tbl_fun /Imod /=.
by case: x => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

(* m6^-1 is the milk table. *)
Lemma m6_inv_permE (x : 'I_12) : val ((m6_perm^-1)%g x) = nth 0 m6i_tbl (val x).
Proof.
have K : cancel (tbl_fun m6i_tbl) (tbl_fun m6_tbl).
  by move=> y; apply: val_inj;
     case: y => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
have -> : (m6_perm^-1)%g x = tbl_fun m6i_tbl x.
  by apply: (@perm_inj _ m6_perm); rewrite permKV permE K.
by rewrite /tbl_fun /Imod /=;
   case: x => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.
