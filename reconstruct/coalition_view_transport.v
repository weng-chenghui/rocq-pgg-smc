(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: Coalition View Transport                                              *)
(*                                                                            *)
(* Moving a coalition from the positions C to the positions rho g C, for g in *)
(* the monodromy group, leaves the mutual information between the dealt       *)
(* secret and the coalition view unchanged: what a set of colluding players   *)
(* learns depends on the set only through its orbit under the group. The      *)
(* equality carries no transitivity premise, so it also holds above the       *)
(* privacy threshold, where the view already depends on the secret.           *)
(*                                                                            *)
(* Section 1 -- Pushforward congruence and injective recoding:                *)
(*   eq_in_fdistmap == two maps agreeing on the support of a law push that    *)
(*     law forward to the same law.                                           *)
(*   mutual_info_RV_comp_inj == an injective recoding of a random variable    *)
(*     shares the same mutual information with every other random variable.   *)
(*                                                                            *)
(* Section 2 -- Position relabelling:                                         *)
(*   fdistmap_mulgl_prod_uniform == the joint law of the dealt secret and a   *)
(*     uniform group element is invariant under left translation of the       *)
(*     group component by an element of the group.                            *)
(*   coalition_view_mutual_info_imset == the coalition at the relabelled      *)
(*     positions rho g C shares the same mutual information with the dealt    *)
(*     secret as the coalition at C.                                          *)
(******************************************************************************)

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

Section mutual_info_recoding.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Variable R : realType.

(** Two maps that agree wherever a law charges push that law forward to the
    same law: fdistmap f d = fdistmap g d as soon as f and g agree on
    fdist_supp d. The coalition view identity below holds only at samples
    whose shuffle lies in the monodromy group, so it is available in this
    support-restricted form and in no pointwise one. *)
Lemma eq_in_fdistmap (A B : finType) (d : R.-fdist A) (f g : A -> B) :
  {in fdist_supp d, f =1 g} -> fdistmap f d = fdistmap g d.
Proof.
move=> Hfg; apply: fdist_ext => b.
rewrite /fdistmap !fdistbindE.
apply: eq_bigr => a _.
have [->|Hda] := eqVneq (d a) 0; first by rewrite !mul0r.
have Ha : a \in fdist_supp d by rewrite inE.
by rewrite (Hfg a Ha).
Qed.

(** Recoding a random variable by an injective map preserves the mutual
    information it shares with another random variable:
    `I(X ; f `o Y) = `I(X ; Y) for injective f. Reading a coalition's view at
    relabelled positions is such a recoding, so relabelling turns the
    data-processing inequality into an equality and neither creates nor
    destroys leakage. *)
Lemma mutual_info_RV_comp_inj (U TX TY TZ : finType) (P : R.-fdist U)
    (X : {RV P -> TX}) (Y : {RV P -> TY}) (f : TY -> TZ) :
  injective f -> `I(X ; f `o Y) = `I(X ; Y).
Proof.
move=> f_inj.
(* an injective map out of a nonempty finite type has a left inverse, and
   the sample space of a law is nonempty *)
have /card_gt0P[u _] := fdist_card_neq0 P.
pose f' (z : TZ) := odflt (Y u) [pick y | f y == z].
have fK : cancel f f'.
  move=> y; rewrite /f'; case: pickP => [y' /eqP /f_inj -> //|Hno].
  by move: (Hno y); rewrite eqxx.
apply: le_anti; apply/andP; split; first exact: view_mutual_info_le.
have HY : Y = f' `o (f `o Y).
  by apply: boolp.funext => u0; rewrite /comp_RV /= fK.
rewrite [W in `I(_ ; W) <= _]HY.
exact: view_mutual_info_le.
Qed.

End mutual_info_recoding.

Section coalition_view_transport.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Variables (N' : nat) (gT : finGroupType) (G : {group gT}).
Variable rho : {morphism G >-> {perm 'I_N'.+1}}.
Variable R : realType.
Variable secretP : R.-fdist bool.
Hypothesis card_G_gt0 : (0 < #|G|)%N.
Variable encode : bool -> N'.+1.-tuple 'I_N'.+1.

(** The joint law of the dealt secret and a uniform group element is
    invariant under left translation of the group component by an element h
    of the group: the pushforward of secretP `x `U card_G_gt0 along
    (b, g) |-> (b, h * g) is that same law. The dealer draws its shuffle
    uniformly from the whole group, so premultiplying the shuffle by a fixed
    group element changes no sample probability, which is what lets a
    relabelling of the coalition's positions be absorbed into the shuffle. *)
Lemma fdistmap_mulgl_prod_uniform (h : gT) : h \in G ->
  fdistmap (fun u : bool * gT => (u.1, (h * u.2)%g))
    (secretP `x (`U card_G_gt0)) = secretP `x (`U card_G_gt0).
Proof.
move=> hG; apply: fdist_ext => -[b g].
rewrite fdistmapE.
rewrite (eq_bigl (fun u : bool * gT => u == (b, (h^-1 * g)%g))); last first.
  move=> [b0 g0]; rewrite !inE /= !xpair_eqE /=.
  by rewrite (can2_eq (mulKg h) (mulKVg h)).
rewrite big_pred1_eq !fdist_prodE /=; congr (_ * _).
have HG : ((h^-1 * g)%g \in G) = (g \in G) by rewrite groupMl // groupV.
have [gG|gG] := boolP (g \in G).
  have hgG : (h^-1 * g)%g \in G by rewrite HG.
  by rewrite (fdist_uniform_supp_in R card_G_gt0 hgG)
             (fdist_uniform_supp_in R card_G_gt0 gG).
have hgG : (h^-1 * g)%g \notin G by rewrite HG.
by rewrite (fdist_uniform_supp_notin R card_G_gt0 hgG)
           (fdist_uniform_supp_notin R card_G_gt0 gG).
Qed.

(** A coalition seated at the relabelled positions rho g C shares exactly the
    same mutual information with the dealt secret as the coalition seated at
    C, for every g in the monodromy group. Which positions a coalition
    occupies therefore matters only up to the shuffle group: relabelling the
    positions by a group element is absorbed by the uniform shuffle, so
    leakage about the secret is a function of the orbit of the coalition
    rather than of the coalition. The statement is an exact
    information-theoretic equality and assumes no transitivity of the group,
    so it transports leakage values at coalition sizes at and above the
    privacy threshold as well as below it. *)
Theorem coalition_view_mutual_info_imset (g : gT) (C : {set 'I_N'.+1}) :
  g \in G ->
  `I(dealt_secret secretP card_G_gt0 ;
       coalition_view rho secretP card_G_gt0 encode (rho g @: C))
  = `I(dealt_secret secretP card_G_gt0 ;
       coalition_view rho secretP card_G_gt0 encode C).
Proof.
move=> gG.
set S := dealt_secret secretP card_G_gt0.
set V := coalition_view rho secretP card_G_gt0 encode C.
set V' := coalition_view rho secretP card_G_gt0 encode (rho g @: C).
pose relabel (v : {ffun 'I_N'.+1 -> 'I_N'.+1}) :=
  [ffun i => v (((rho g)^-1)%g i)].
have relabelK : cancel relabel (fun v => [ffun i => v (rho g i)]).
  by move=> v; apply/ffunP => i; rewrite !ffunE permK.
have key : `p_[% S, V'] = `p_[% S, relabel `o V].
  rewrite /dist_of_RV.
  transitivity (fdistmap
      ((fun z : bool * {ffun 'I_N'.+1 -> 'I_N'.+1} => (z.1, relabel z.2))
         \o ([% S, V] \o (fun u : bool * gT => (u.1, (g * u.2)%g))))
      (secretP `x (`U card_G_gt0))).
    (* the two views agree only where the sampled shuffle lies in G, since
       morphM is available inside G alone *)
    apply: eq_in_fdistmap => -[b g0]; rewrite inE => Hbg.
    have g0G : g0 \in G.
      move: Hbg; apply: contraNT => g0G.
      rewrite fdist_prodE /= (fdist_uniform_supp_notin R card_G_gt0 g0G).
      by rewrite mulr0 eqxx.
    rewrite /comp /=; congr (_, _).
    apply/ffunP => i.
    rewrite /V' /V /relabel /coalition_view /= !ffunE.
    have Hmem : (i \in rho g @: C) = (((rho g)^-1)%g i \in C).
      apply/idP/idP => [/imsetP[x xC ->]|Hx]; first by rewrite permK.
      by apply/imsetP; exists (((rho g)^-1)%g i) => //; rewrite permKV.
    rewrite Hmem; case: ifP => // _.
    by rewrite morphM // permM permKV.
  rewrite -fdistmap_comp -fdistmap_comp (fdistmap_mulgl_prod_uniform gG).
  by rewrite fdistmap_comp.
rewrite /mutual_info_RV key -/(mutual_info_RV S (relabel `o V)).
exact: (mutual_info_RV_comp_inj S V (can_inj relabelK)).
Qed.

End coalition_view_transport.
