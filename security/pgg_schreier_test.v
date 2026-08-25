From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import matrix.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj
                            pgg_collusion_bound.
From pgg_reconstruct Require Import algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

Section test_proofs.

Variable R : realType.
Variable m n' : nat.
Let Tg := m.+1.
Let N := n'.+2.

Variable sigmas : Tg.-tuple {perm 'I_N}.

Local Notation M := (Gen_PGGTypes sigmas).

Lemma word_eval_cons (L : nat) (i : 'I_Tg) (w : L.-tuple 'I_Tg) :
  @word_eval M L.+1 [tuple of i :: w] =
  (tnth sigmas i * @word_eval M L w)%g.
Proof.
Admitted.

End test_proofs.
