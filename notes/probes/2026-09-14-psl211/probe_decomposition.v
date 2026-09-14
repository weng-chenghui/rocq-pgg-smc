(* probe_decomposition: ledger rows L11, L12, L13, L16, L17 of the PSL(2,11)
   spec.  The one legitimate use of Admitted: every supporting statement is
   Admitted, the headline records and the record-level privacy statement
   are derived to Qed.  This checks statement shapes and composition only.
   PROVER: make the file compile with the supporting lemmas Admitted and the
   headline definitions/lemmas Qed; do not prove the Admitted ones here. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import transitivity_privacy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Load "psl211_tables.v".

Local Definition Imod (k : nat) : 'I_12 := Ordinal (ltn_pmod k (ltn0Sn 11)).
Local Definition tbl_fun (tbl : seq nat) (i : 'I_12) : 'I_12 := Imod (nth 0 tbl i).
Lemma r4_inj : injective (tbl_fun r4_tbl). Admitted.
Lemma m6_inj : injective (tbl_fun m6_tbl). Admitted.
Definition psl211_gens : 2.-tuple {perm 'I_12} := [tuple perm r4_inj; perm m6_inj].
Notation psl211_M := (@Gen_PGGTypes 1 10 psl211_gens).

(* ---- Deck vocabulary (pgl27_orbit shape) ---- *)
Definition is_heart (c : 'I_12) : bool := (val c < 6)%N.
Definition deck_ok (sh : 12.-tuple 'I_12) : bool := uniq sh.
Definition heart_set (sh : 12.-tuple 'I_12) : {set 'I_12} :=
  [set i | is_heart (tnth sh i)].
Local Definition list_to_set (L : seq nat) : {set 'I_12} := [set x : 'I_12 | val x \in L].
Definition setsA : {set {set 'I_12}} := [set S | has (fun R => list_to_set R == S) tblA].
Definition setsB : {set {set 'I_12}} := [set S | has (fun R => list_to_set R == S) tblB].

(** subset_valid — S is a block of one of the two Steiner systems. *)
Definition subset_valid (S : {set 'I_12}) : bool := (S \in setsA) || (S \in setsB).
(** subset_class — true on the A-system (the mirror), false on the B-system
    (the M12 hexads); arbitrary outside. *)
Definition subset_class (S : {set 'I_12}) : bool := S \in setsA.
Definition orbit_class (sh : 12.-tuple 'I_12) : bool := subset_class (heart_set sh).

(** orbit_valid — a distinct-card deck whose heart set is a block of the
    system named by s. *)
Definition orbit_valid (s : bool) (sh : 12.-tuple 'I_12) : Prop :=
  deck_ok sh /\ subset_valid (heart_set sh) /\ orbit_class sh = s.

(* ---- Supporting statements (Admitted here by design) ---- *)

Lemma setsA_invariant (g : pgg_gT psl211_M) (S : {set 'I_12}) :
  g \in pgg_G psl211_M -> ((g @: S) \in setsA) = (S \in setsA). Admitted.
Lemma setsB_invariant (g : pgg_gT psl211_M) (S : {set 'I_12}) :
  g \in pgg_G psl211_M -> ((g @: S) \in setsB) = (S \in setsB). Admitted.
Lemma deck_stable (g : pgg_gT psl211_M) (sh : 12.-tuple 'I_12) :
  g \in pgg_G psl211_M ->
  deck_ok [tuple tnth sh (@pgg_rho psl211_M g i) | i < 12] = deck_ok sh. Admitted.
Lemma heart_set_act (g : pgg_gT psl211_M) (sh : 12.-tuple 'I_12) :
  heart_set [tuple tnth sh (@pgg_rho psl211_M g i) | i < 12]
  = (g^-1)%g @: heart_set sh. Admitted.

Definition orbit_encode (b : bool) : 12.-tuple 'I_12. Admitted.
Lemma orbit_encode_valid (s : bool) : orbit_valid s (orbit_encode s). Admitted.

(* L12: the re-deal from equal pattern counts. *)
Lemma psl211_private (s1 s2 : bool) (sh : 12.-tuple 'I_12) (C : {set 'I_12}) :
  (#|C| < 5.+1)%N -> orbit_valid s1 sh ->
  exists sh', orbit_valid s2 sh' /\
    (forall i : 'I_12, i \in C -> tnth sh' i = tnth sh i). Admitted.

(* L16: recovery. *)
Lemma psl211_eleven_reveal_class (sh sh' : 12.-tuple 'I_12) (j : 'I_12) :
  deck_ok sh -> deck_ok sh' ->
  (forall i, i != j -> tnth sh' i = tnth sh i) -> orbit_class sh' = orbit_class sh.
Admitted.
Lemma psl211_ten_reveal_ambiguous (p q : 'I_12) :
  p != q ->
  exists sh sh', orbit_valid true sh /\ orbit_valid false sh' /\
    (forall i, i != p -> i != q -> tnth sh' i = tnth sh i). Admitted.

(* L17. *)
Lemma psl211_card : #|pgg_G psl211_M| = 660. Admitted.

(* L11: orbit of a block is its system (subset_class_orbitE shape). *)
Lemma setsA_orbitE (S : {set 'I_12}) :
  S \in setsA -> orbit 'P^* (pgg_G psl211_M) S = setsA. Admitted.

(* ---- Headline records, derived to Qed ---- *)

Lemma orbit_correct (s : bool) (sh : 12.-tuple 'I_12) :
  orbit_valid s sh -> orbit_class sh = s.
Proof. by move=> [_ [_ ->]]. Qed.

(** orbit_scheme — the twelve-card chirality ThresholdScheme, secret bool,
    shares 'I_12, privacy threshold five. *)
Definition orbit_scheme : ThresholdScheme bool 'I_12 :=
  @MkThresholdScheme bool 'I_12 (pgg_N' psl211_M) 5
    orbit_valid orbit_class orbit_encode
    orbit_correct psl211_private orbit_encode_valid.

Lemma orbit_recon_invariant :
  @ts_recon_perm_invariant _ (pgg_G psl211_M) bool 'I_12
    orbit_scheme (fun g => @pgg_rho psl211_M g).
Proof.
move=> g s shares gG [_ [_ <-]].
rewrite /orbit_scheme /= /orbit_class heart_set_act.
by rewrite /subset_class (setsA_invariant _ (groupVr gG)).
Qed.

(** colour_content — the content map collapsing codes to two colour
    representatives: hearts to ord0, clubs to the code 1. *)
Definition colour_content (c : 'I_12) : 'I_12 :=
  if is_heart c then ord0 else Ordinal (isT : (1 < 12)%N).

(** psl211_plug — the reconstruction plug with colour-only content. *)
Definition psl211_plug : ReconPlug psl211_M bool :=
  @MkReconPlug psl211_M bool orbit_scheme colour_content
    (fun g => @pgg_rho psl211_M g) orbit_recon_invariant.

(* L13: the profile.  The PGGInterface needs no piSMC program: it is the
   starting layout alone, exactly as pgl27_profile.v builds pgl27_PI. *)

(** psl211_starts_uniq — the twelve starting card positions are distinct. *)
Lemma psl211_starts_uniq : uniq (ord_tuple 12).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.

(** psl211_PI — the starting interface on twelve card positions for the
    twelve-card chirality plug: the identity start tuple driving the shared
    exchange program. *)
Definition psl211_PI : PGGInterface psl211_M :=
  @MkPGGI psl211_M 11 (ord_tuple 12) psl211_starts_uniq.

Definition psl211_profile : MonodromyProfile :=
  @MkMonodromyProfile psl211_M bool psl211_PI psl211_plug.

(* ---- Record-level privacy statement, the sibling of profile_view_indep:
   same profile in, design-count premise instead of ntransitive, colour
   observer out.  Derived to Qed from the bridge (Admitted here). ---- *)

Section record_level.
Variables (R : realType) (secretP : R.-fdist bool).
Hypothesis card_G_gt0 : (0 < #|pgg_G psl211_M|)%N.

Definition colour_view (C : {set 'I_12}) :
    {RV (secretP `x (`U card_G_gt0)) -> {ffun 'I_12 -> bool}} :=
  fun u => [ffun i => if i \in C
                      then is_heart (tnth (orbit_encode u.1) (@pgg_rho psl211_M u.2 i))
                      else false].

Lemma colour_view_indep_of_fibres (C : {set 'I_12}) :
  (forall v : {ffun 'I_12 -> bool},
     #|[set g in pgg_G psl211_M | colour_view C (true, g) == v]|
     = #|[set g in pgg_G psl211_M | colour_view C (false, g) == v]|) ->
  secretP `x (`U card_G_gt0) |= colour_view C _|_
    (@dealt_secret _ (pgg_G psl211_M) R secretP card_G_gt0).
Admitted.

Lemma psl211_fibres_eq (C : {set 'I_12}) (v : {ffun 'I_12 -> bool}) :
  (#|C| <= 5)%N ->
  #|[set g in pgg_G psl211_M | colour_view C (true, g) == v]|
  = #|[set g in pgg_G psl211_M | colour_view C (false, g) == v]|.
Admitted.

(** psl211_colour_view_indep — the headline: every coalition of at most
    five positions has a colour view independent of the dealt secret. *)
Lemma psl211_colour_view_indep (C : {set 'I_12}) :
  (#|C| <= 5)%N ->
  secretP `x (`U card_G_gt0) |= colour_view C _|_
    (@dealt_secret _ (pgg_G psl211_M) R secretP card_G_gt0).
Proof. by move=> HC; apply: colour_view_indep_of_fibres => v; exact: psl211_fibres_eq. Qed.

End record_level.

(* ---- assumption audit ---- *)
Print Assumptions orbit_correct.
Print Assumptions orbit_scheme.
Print Assumptions orbit_recon_invariant.
Print Assumptions psl211_plug.
Print Assumptions psl211_starts_uniq.
Print Assumptions psl211_PI.
Print Assumptions psl211_profile.
Print Assumptions psl211_colour_view_indep.
