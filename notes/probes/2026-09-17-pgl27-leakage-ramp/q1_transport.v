From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba entropy.
From pgg_reconstruct Require Import transitivity_privacy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory Order.POrderTheory.

Local Open Scope fdist_scope.

Check @permM.
Check @morphM.
Check @groupMl.

Section transport.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Variables (N' : nat) (gT : finGroupType) (G : {group gT}).
Variable rho : {morphism G >-> {perm 'I_N'.+1}}.
Variable R : realType.
Variable secretP : R.-fdist bool.
Hypothesis card_G_gt0 : (0 < #|G|)%N.
Variable encode : bool -> N'.+1.-tuple 'I_N'.+1.

Let P : R.-fdist (bool * gT)%type := secretP `x (`U card_G_gt0).

(* generic support-congruence for fdistmap *)
Lemma fdistmap_eq_supp (A B : finType) (d : R.-fdist A) (f g : A -> B) :
  (forall a, d a != 0 -> f a = g a) -> fdistmap f d = fdistmap g d.
Proof.
move=> Hfg; apply: fdist_ext => b.
rewrite /fdistmap !fdistbindE.
apply: eq_bigr => a _.
have [->|Hda] := eqVneq (d a) 0; first by rewrite !mul0r.
by rewrite (Hfg a Hda).
Qed.

(* mutual information is invariant under injective post-processing *)
Lemma mutual_info_RV_inj (U TS TV TW : finType) (Q : R.-fdist U)
    (S : {RV Q -> TS}) (V : {RV Q -> TV}) (f : TV -> TW) (f' : TW -> TV) :
  cancel f f' -> `I(S ; f `o V) = `I(S ; V).
Proof.
move=> fK; apply: le_anti; apply/andP; split; first exact: view_mutual_info_le.
set W : {RV Q -> TW} := f `o V.
have HV : V = f' `o W by apply: boolp.funext => u; rewrite /comp_RV /W /= fK.
rewrite [X in `I(S ; X) <= _]HV.
exact: view_mutual_info_le.
Qed.

Let psi (h : gT) (v : {ffun 'I_N'.+1 -> 'I_N'.+1})
  : {ffun 'I_N'.+1 -> 'I_N'.+1} := [ffun i => v (((rho h)^-1)%g i)].
Let psi' (h : gT) (v : {ffun 'I_N'.+1 -> 'I_N'.+1})
  : {ffun 'I_N'.+1 -> 'I_N'.+1} := [ffun i => v (rho h i)].

Lemma psiK (h : gT) : cancel (psi h) (psi' h).
Proof.
move=> v; apply/ffunP => i; rewrite /psi' /psi !ffunE.
by rewrite permK.
Qed.

(* P vanishes off bool * G *)
Lemma P_supp (b : bool) (g : gT) : P (b, g) != 0 -> g \in G.
Proof.
apply: contraNT => gG.
rewrite /P fdist_prodE /= (fdist_uniform_supp_notin R card_G_gt0 gG) mulr0.
by rewrite eqxx.
Qed.

(* left translation by h in G preserves P *)
Lemma P_transl (h : gT) : h \in G ->
  fdistmap (fun u : bool * gT => (u.1, (h * u.2)%g)) P = P.
Proof.
move=> hG; apply: fdist_ext => -[b g].
rewrite fdistmapE.
rewrite (eq_bigl (fun u : bool * gT => u == (b, (h^-1 * g)%g))); last first.
  move=> [b0 g0]; rewrite !inE /= !xpair_eqE /=.
  by rewrite (can2_eq (mulKg h) (mulKVg h)).
rewrite big_pred1_eq /P !fdist_prodE /=; congr (_ * _).
case: (boolP (g \in G)) => gG.
  have hgG : (h^-1 * g)%g \in G by rewrite groupM ?groupV.
  by rewrite (fdist_uniform_supp_in R card_G_gt0 hgG)
             (fdist_uniform_supp_in R card_G_gt0 gG).
have hgG : (h^-1 * g)%g \notin G.
  apply: contra gG => H; by rewrite -(mulKVg h g) groupM.
by rewrite (fdist_uniform_supp_notin R card_G_gt0 hgG)
           (fdist_uniform_supp_notin R card_G_gt0 gG).
Qed.

(* the transport *)
Theorem coalition_view_transport (h : gT) (C : {set 'I_N'.+1}) : h \in G ->
  `I(dealt_secret secretP card_G_gt0 ;
       coalition_view rho secretP card_G_gt0 encode (rho h @: C))
  = `I(dealt_secret secretP card_G_gt0 ;
       coalition_view rho secretP card_G_gt0 encode C).
Proof.
move=> hG.
set S := dealt_secret secretP card_G_gt0.
set V := coalition_view rho secretP card_G_gt0 encode C.
set V1 := coalition_view rho secretP card_G_gt0 encode (rho h @: C).
have key : `p_[% S, V1] = `p_[% S, psi h `o V].
  rewrite /dist_of_RV.
  transitivity (fdistmap
      ((fun z : bool * {ffun 'I_N'.+1 -> 'I_N'.+1} => (z.1, psi h z.2))
        \o ([% S, V] \o (fun u : bool * gT => (u.1, (h * u.2)%g)))) P).
    apply: fdistmap_eq_supp => -[b g] Hbg.
    have gG := P_supp Hbg.
    rewrite /comp /=; congr (_, _).
    apply/ffunP => i.
    rewrite /V1 /V /psi /coalition_view /= !ffunE.
    have Hmem : (i \in rho h @: C) = (((rho h)^-1)%g i \in C).
      apply/idP/idP => [/imsetP[x xC ->]|Hx]; first by rewrite permK.
      by apply/imsetP; exists (((rho h)^-1)%g i) => //; rewrite permKV.
    rewrite Hmem.
    case: ifP => // _.
    by rewrite morphM // permM permKV.
  rewrite -fdistmap_comp -fdistmap_comp (P_transl hG).
  by rewrite fdistmap_comp.
by rewrite /mutual_info_RV key -/(mutual_info_RV S (psi h `o V))
  (mutual_info_RV_inj S V (psiK h)).
Qed.

End transport.
