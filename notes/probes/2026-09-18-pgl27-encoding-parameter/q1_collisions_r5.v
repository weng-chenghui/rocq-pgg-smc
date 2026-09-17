(* PROBE Q1 (task P0, plan 2026-09-18-pgl27-encoding-parameter).
   Generalise code_views / pgl27_collisions over the deal function and
   vm_compute the numbers at the _r7 deal (sanity) and the _r5 deal.

   Cost note.  The agreement of the generalised definitions with the source
   ones must NOT be closed by "by []": ssreflect's done drives conversion
   into the 336-row table closure and diverges (measured: Timeout at 30 s,
   see q1c_conv_bisect.v).  The delta-only route "rewrite /gen_views
   /deal_r7 /code_views" closes it in well under a second. *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From pgg_smc Require Import pgl27_leakage_census.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ------------------------------------------------------------------ *)
(* The generalised census definitions: the deal is a parameter.        *)
(* ------------------------------------------------------------------ *)

Definition gen_views (deal : bool -> seq nat) (b : bool) (S : seq nat) :
    seq (seq nat) :=
  [seq code_restrict S (code_comp t (deal b)) | t <- pgl27_group_table].

Definition gen_collisions (deal : bool -> seq nat) (S : seq nat) : nat :=
  count (fun v => v \in gen_views deal false S) (gen_views deal true S).

(* ------------------------------------------------------------------ *)
(* The two deals.                                                      *)
(* ------------------------------------------------------------------ *)

(* _r7: the repository's pair, orbit_encode. *)
Definition deal_r7 : bool -> seq nat := code_deal.

(* _r5: false 0 1 2 3 4 5 6 7, true 0 1 2 4 3 5 7 6. *)
Definition code_tau_r5 : seq nat := [:: 0; 1; 2; 4; 3; 5; 7; 6].
Definition deal_r5 (b : bool) : seq nat := if b then code_tau_r5 else code_id.

(* ------------------------------------------------------------------ *)
(* Sanity: the generalised definitions agree with the source ones.     *)
(* ------------------------------------------------------------------ *)

Lemma gen_views_r7E (b : bool) (S : seq nat) :
  gen_views deal_r7 b S = code_views b S.
Proof. by rewrite /gen_views /deal_r7 /code_views. Qed.

Lemma gen_collisions_r7E (S : seq nat) :
  gen_collisions deal_r7 S = pgl27_collisions S.
Proof. by rewrite /gen_collisions /pgl27_collisions !gen_views_r7E. Qed.

(* ------------------------------------------------------------------ *)
(* Q1a: the r7 numbers 96, 72, 36, 12, 0 out of the generalised defs.  *)
(* ------------------------------------------------------------------ *)

Lemma q1_r7_harmonic : gen_collisions deal_r7 rep_harmonic = 96.
Proof. by vm_compute. Qed.

Lemma q1_r7_equianharmonic : gen_collisions deal_r7 rep_equianharmonic = 72.
Proof. by vm_compute. Qed.

Lemma q1_r7_five : gen_collisions deal_r7 rep_five = 36.
Proof. by vm_compute. Qed.

Lemma q1_r7_six : gen_collisions deal_r7 rep_six = 12.
Proof. by vm_compute. Qed.

Lemma q1_r7_seven : gen_collisions deal_r7 rep_seven = 0.
Proof. by vm_compute. Qed.

Lemma q1_r7_three : gen_collisions deal_r7 [:: 0; 1; 2] = 336.
Proof. by vm_compute. Qed.

(* ------------------------------------------------------------------ *)
(* Q1b: the r5 numbers 48, 72, 0, 0, 0 and 336 at three positions.     *)
(* ------------------------------------------------------------------ *)

Lemma q1_r5_harmonic : gen_collisions deal_r5 rep_harmonic = 48.
Proof. by vm_compute. Qed.

Lemma q1_r5_equianharmonic : gen_collisions deal_r5 rep_equianharmonic = 72.
Proof. by vm_compute. Qed.

Lemma q1_r5_five : gen_collisions deal_r5 rep_five = 0.
Proof. by vm_compute. Qed.

Lemma q1_r5_six : gen_collisions deal_r5 rep_six = 0.
Proof. by vm_compute. Qed.

Lemma q1_r5_seven : gen_collisions deal_r5 rep_seven = 0.
Proof. by vm_compute. Qed.

Lemma q1_r5_three : gen_collisions deal_r5 [:: 0; 1; 2] = 336.
Proof. by vm_compute. Qed.

(* ------------------------------------------------------------------ *)
(* Q1c: both r5 view lists are uniq at all five representatives.       *)
(* ------------------------------------------------------------------ *)

Lemma q1_r5_uniq_harmonic :
  uniq (gen_views deal_r5 false rep_harmonic)
  && uniq (gen_views deal_r5 true rep_harmonic).
Proof. by vm_compute. Qed.

Lemma q1_r5_uniq_equianharmonic :
  uniq (gen_views deal_r5 false rep_equianharmonic)
  && uniq (gen_views deal_r5 true rep_equianharmonic).
Proof. by vm_compute. Qed.

Lemma q1_r5_uniq_five :
  uniq (gen_views deal_r5 false rep_five)
  && uniq (gen_views deal_r5 true rep_five).
Proof. by vm_compute. Qed.

Lemma q1_r5_uniq_six :
  uniq (gen_views deal_r5 false rep_six)
  && uniq (gen_views deal_r5 true rep_six).
Proof. by vm_compute. Qed.

Lemma q1_r5_uniq_seven :
  uniq (gen_views deal_r5 false rep_seven)
  && uniq (gen_views deal_r5 true rep_seven).
Proof. by vm_compute. Qed.

(* The three-position view lists are repetition-free too: sharp
   3-transitivity makes g |-> (g0, g1, g2) a bijection onto the 336 ordered
   triples of distinct points.  With 336 collisions the ambiguity route then
   gives 1 - 336/336 = 0 bits at three positions, matching the independence
   route. *)
Lemma q1_r5_uniq_three :
  uniq (gen_views deal_r5 false [:: 0; 1; 2])
  && uniq (gen_views deal_r5 true [:: 0; 1; 2]).
Proof. by vm_compute. Qed.

(* ------------------------------------------------------------------ *)
(* Q1d: the r5 exact ratios needed downstream.                         *)
(*   (336 - 48) / 336 = 6/7 ; (336 - 72) / 336 = 11/14 ;               *)
(*   (336 - 0) / 336 = 1.                                              *)
(* ------------------------------------------------------------------ *)

Lemma q1_r5_ratio_harmonic :
  ((336 - gen_collisions deal_r5 rep_harmonic) * 7)%N = (6 * 336)%N.
Proof. by vm_compute. Qed.

Lemma q1_r5_ratio_equianharmonic :
  ((336 - gen_collisions deal_r5 rep_equianharmonic) * 14)%N = (11 * 336)%N.
Proof. by vm_compute. Qed.

(* ------------------------------------------------------------------ *)
(* Q1e: the deck-level facts the encoding record will need for r5.     *)
(*   both nat tables are permutations of 0..7 (distinct cards),        *)
(*   and the heart positions {0,1,2,4} agree with the r7 true deck.    *)
(* ------------------------------------------------------------------ *)

Lemma q1_r5_tau_uniq : uniq code_tau_r5.
Proof. by vm_compute. Qed.

Lemma q1_r5_tau_perm : perm_eq code_tau_r5 (iota 0 8).
Proof. by vm_compute. Qed.

Lemma q1_r5_hearts_agree :
  [seq i <- iota 0 8 | nth 0 code_tau_r5 i < 4]
  = [seq i <- iota 0 8 | nth 0 code_tau i < 4].
Proof. by vm_compute. Qed.

Print Assumptions q1_r5_harmonic.
Print Assumptions q1_r5_five.
Print Assumptions q1_r5_uniq_seven.
Print Assumptions gen_collisions_r7E.
