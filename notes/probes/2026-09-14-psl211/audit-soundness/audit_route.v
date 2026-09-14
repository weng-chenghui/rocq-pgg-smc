(* audit_route: does the framework's existing transitivity route reach the
   coalition size the spec wants?  Compile with
     sh run.sh audit-soundness/audit_route.v
   from notes/probes/2026-09-14-psl211. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import primitive_action.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_reconstruct Require Import transitivity_privacy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope group_scope.

(* ------------------------------------------------------------------------ *)
(* The transitivity premise of transitivity_privacy.v cannot be met at the   *)
(* coalition size the PSL(2,11) spec claims.                                 *)
(* ------------------------------------------------------------------------ *)

(** transitivity_route_floor - every privacy result of
    transitivity_privacy.v (ttrans_private, ttrans_view_indep_gen,
    ttrans_view_indep_alldecks, ttrans_view_indep_deck, profile_view_indep)
    carries ntransitive t as a section hypothesis, and that hypothesis costs
    at least one group element per ordered triple of distinct positions.
    Twelve positions carry 12 * 11 * 10 = 1320 such triples, so a shuffle
    group of order 660 admits no such premise for t >= 3: the existing route
    stops at coalitions of size 2, whatever the dealer, and the spec's
    design-count bridge is necessary rather than a convenience. *)
Lemma transitivity_route_floor (aT : finGroupType)
    (to : {action aT &-> 'I_12}) (A : {group aT}) (t : nat) :
  (3 <= t)%N -> ntransitive t A [set: 'I_12] to ->
  (#|3.-dtuple([set: 'I_12])| <= #|A|)%N.
Proof.
move=> t3 Hnt; apply: ntransitive_card_le.
exact: ntransitive_weak Hnt.
Qed.

(* The same at the spec's own degree. *)
Lemma transitivity_route_floor5 (aT : finGroupType)
    (to : {action aT &-> 'I_12}) (A : {group aT}) :
  ntransitive 5 A [set: 'I_12] to -> (#|3.-dtuple([set: 'I_12])| <= #|A|)%N.
Proof. exact: transitivity_route_floor (isT : (3 <= 5)%N). Qed.

(* ------------------------------------------------------------------------ *)
(* The colour-collapsed content is not a deck.                               *)
(* ------------------------------------------------------------------------ *)

Definition is_heart (c : 'I_12) : bool := (val c < 6)%N.
Definition colour_content (c : 'I_12) : 'I_12 :=
  if is_heart c then ord0 else Ordinal (isT : (1 < 12)%N).

(** colour_content_not_uniq - the colour collapse is six-to-one, so the
    content tuple of any distinct-card deck repeats.  Every framework lemma
    that asks for ts_valid of the content tuple (pgg_recon_monodromy_correct,
    pgg_sharing_framework.v) is therefore unusable with this content, because
    orbit_valid's deck_ok field demands uniqueness. *)
Lemma colour_content_not_uniq (sh : 12.-tuple 'I_12) :
  uniq sh -> ~~ uniq [tuple colour_content (tnth sh i) | i < 12].
Proof.
move=> /tuple_uniqP shinj; have [g _ gc] := injF_bij shinj.
apply/negP => /tuple_uniqP Hinj.
have Hne : g ord0 <> g (Ordinal (isT : (1 < 12)%N)).
  by move=> /(congr1 (tnth sh)); rewrite !gc.
by apply: Hne; apply: Hinj; rewrite !tnth_mktuple !gc.
Qed.
