(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* mutual_info_recoding: pushforward congruence and injective recoding        *)
(*                                                                            *)
(* Three facts about a law transported along a map. Two maps that agree on    *)
(* the support of a law push it forward to the same law; recoding a random    *)
(* variable by an injective map leaves the mutual information it shares with  *)
(* any other random variable unchanged; and the product of a law with the     *)
(* uniform law on a group is invariant under left translation of the group    *)
(* component. Together they let a relabelling of the positions a coalition    *)
(* holds be absorbed into the group element the dealer samples, so an         *)
(* adversary's information about the secret is unchanged by the relabelling.  *)
(*                                                                            *)
(* Key results:                                                               *)
(*   eq_in_fdistmap == two maps agreeing on the support of a law push that    *)
(*     law forward to the same law                                            *)
(*   mutual_info_RV_comp_inj == an injective recoding of a random variable    *)
(*     shares the same mutual information with every other random variable    *)
(*   fdistmap_prod_uniform_Ml == the product of a law with the uniform law on *)
(*     a group is invariant under left translation of the group component     *)
(*                                                                            *)
(* The carrier of the first component is an arbitrary finite type, so the     *)
(* statements hold for a secret of any type and not for a Boolean one alone.  *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset fingroup bigop.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba entropy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

(** Two maps that agree wherever a law charges push that law forward to the
    same law: fdistmap f d = fdistmap g d as soon as f and g agree on
    fdist_supp d. A coalition view identity that holds only at samples whose
    shuffle lies in the monodromy group is available in this
    support-restricted form and in no pointwise one. *)
Lemma eq_in_fdistmap (R : realType) (A B : finType) (d : R.-fdist A)
    (f g : A -> B) :
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
Lemma mutual_info_RV_comp_inj (R : realType) (U TX TY TZ : finType)
    (P : R.-fdist U) (X : {RV P -> TX}) (Y : {RV P -> TY}) (f : TY -> TZ) :
  injective f -> `I(X ; f `o Y) = `I(X ; Y).
Proof.
move=> f_inj.
rewrite /mutual_info_RV !mutual_infoEjoint_entropy !fst_RV2 !snd_RV2.
congr (_ + _ - _); first by rewrite /dist_of_RV -fdistmap_comp entropy_fdistmap.
by rewrite [LHS]joint_entropy_RVC [RHS]joint_entropy_RVC
  injective_joint_entropy.
Qed.

(** The product of a law on a finite type with the uniform law on a group is
    invariant under left translation of the group component by an element of
    the group. A dealer that draws its group element uniformly from the whole
    monodromy group charges every sample exactly as it charges the
    premultiplied one, which is what lets a relabelling of the positions a
    coalition holds be absorbed into that group element. *)
Lemma fdistmap_prod_uniform_Ml (R : realType) (gT : finGroupType)
    (G : {group gT}) (HG : (0 < #|G|)%N) (T : finType) (P : R.-fdist T)
    (h : gT) : h \in G ->
  fdistmap (fun u : T * gT => (u.1, (h * u.2)%g)) (P `x (`U HG))
    = P `x (`U HG).
Proof.
move=> hG; apply: fdist_ext => -[b g].
rewrite fdistmapE.
rewrite (eq_bigl (fun u : T * gT => u == (b, (h^-1 * g)%g))); last first.
  move=> [b0 g0]; rewrite !inE /= !xpair_eqE /=.
  by rewrite (can2_eq (mulKg h) (mulKVg h)).
rewrite big_pred1_eq !fdist_prodE /=; congr (_ * _).
have HG' : ((h^-1 * g)%g \in G) = (g \in G) by rewrite groupMl // groupV.
have [gG|gG] := boolP (g \in G).
  have hgG : (h^-1 * g)%g \in G by rewrite HG'.
  by rewrite (fdist_uniform_supp_in R HG hgG)
             (fdist_uniform_supp_in R HG gG).
have hgG : (h^-1 * g)%g \notin G by rewrite HG'.
by rewrite (fdist_uniform_supp_notin R HG hgG)
           (fdist_uniform_supp_notin R HG gG).
Qed.
