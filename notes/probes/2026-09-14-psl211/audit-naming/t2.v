From mathcomp Require Import all_ssreflect all_fingroup.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Local Open Scope fdist_scope.
Local Open Scope ring_scope.

Section fibres.
Variables (R : realType) (X : finType) (A : {set X}) (HA : (0 < #|A|)%N).
Variable T : finType.

Lemma uniform_fdistmap_fibre_ratio (f : X -> T) (v : T) :
  fdistmap f (`U HA) v = #|[set x in A | f x == v]|%:R / #|A|%:R :> R.
Proof.
rewrite fdistmapE (bigID (fun x : X => x \in A)) /=.
rewrite [in X in _ + X]big1 ?addr0; last first.
  by move=> x /andP[_ xA]; rewrite fdist_uniform_supp_notin.
rewrite (eq_bigr (fun=> (#|A|%:R^-1 : R))); last first.
  by move=> x /andP[_ xA]; rewrite fdist_uniform_supp_in.
rewrite sumr_const.
have -> : #|(fun i : X => (i \in preim f (pred1 v)) && (i \in A))|
        = #|[set x in A | f x == v]|.
  by apply: eq_card => x; rewrite !inE /= andbC.
by rewrite mulr_natl.
Qed.

Lemma uniform_fdistmap_of_fibres (f0 f1 : X -> T) :
  (forall v, #|[set x in A | f0 x == v]| = #|[set x in A | f1 x == v]|) ->
  fdistmap f0 (`U HA) = fdistmap f1 (`U HA) :> R.-fdist T.
Proof.
by move=> Hfib; apply/fdist_ext => v; rewrite !uniform_fdistmap_fibre_ratio Hfib.
Qed.

End fibres.
Print Assumptions uniform_fdistmap_of_fibres.
