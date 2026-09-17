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
(* Key results:                                                               *)
(*   coalition_view_mutual_info_imset == the coalition at the relabelled      *)
(*     positions rho g C shares the same mutual information with the dealt    *)
(*     secret as the coalition at C                                           *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba entropy.
From pgg_smc Require Import mutual_info_recoding.
From pgg_reconstruct Require Import transitivity_privacy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Order.POrderTheory.

Local Open Scope fdist_scope.

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

(** The view of a coalition seated at the relabelled positions rho g C shares
    exactly the same mutual information with the dealt secret as the view of
    the coalition seated at C, for every g in the monodromy group. Which
    positions a coalition occupies therefore matters only up to the monodromy
    group: relabelling the positions by a group element is absorbed by the
    uniform shuffle, so leakage about the secret is a function of the orbit of
    the coalition rather than of the coalition. The equality is exact and
    assumes no transitivity, so it transports leakage values at coalition
    sizes at and above the privacy threshold as well as below it. *)
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
  rewrite -fdistmap_comp -fdistmap_comp
    (fdistmap_prod_uniform_Ml card_G_gt0 secretP gG).
  by rewrite fdistmap_comp.
rewrite /mutual_info_RV key -/(mutual_info_RV S (relabel `o V)).
exact: (mutual_info_RV_comp_inj S V (can_inj relabelK)).
Qed.

End coalition_view_transport.
