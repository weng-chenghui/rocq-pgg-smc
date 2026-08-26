(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: Abstract Reconstruction Framework                                     *)
(*                                                                            *)
(* The PGG framework has two orthogonal layers: security (monodromy walk)     *)
(* and threshold (reconstruction). This file makes the threshold layer        *)
(* abstract via a ThresholdScheme interface and a compatibility predicate that *)
(* links it to the monodromy representation.                                  *)
(*                                                                            *)
(* Design rationale — why axiomatize:                                         *)
(*   The reconstruction correctness theorem and the security-threshold        *)
(*   tradeoff (in cover_tradeoff.v) depend only on three properties of the   *)
(*   sharing scheme: correctness (ts_correct), privacy (ts_private), and     *)
(*   compatibility with monodromy (ts_recon_perm_invariant). These properties     *)
(*   hold for any AG code on any curve of any genus, so the proofs are       *)
(*   parametric in ThresholdScheme. Concrete curve arithmetic is unnecessary.*)
(*                                                                            *)
(* Section 1 -- Abstract interface:                                           *)
(*   ThresholdScheme secretT shareT == record bundling:                       *)
(*     - T players, k threshold                                               *)
(*     - validity predicate, reconstruction function                          *)
(*     - correctness and privacy axioms                                        *)
(*                                                                            *)
(* Section 2 -- Compatibility:                                                *)
(*   ts_recon_perm_invariant perm ts == reordering dealt hands by perm g preserves*)
(*     reconstruction. Satisfiable for monodromy groups (coordinate perm).   *)
(*                                                                            *)
(* Section 3 -- Sum-mod-N instance:                                           *)
(*   sum_mod_scheme N' T' == ThresholdScheme wrapping existing sum-mod-N      *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_sum_mod.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     Section 1: Abstract Secret Sharing Scheme                              *)
(******************************************************************************)

Record ThresholdScheme (secretT shareT : Type) := MkThresholdScheme {
  ts_T' : nat ;
  ts_k' : nat ;
  ts_valid : secretT -> ts_T'.+1.-tuple shareT -> Prop ;
  ts_recon : ts_T'.+1.-tuple shareT -> secretT ;
  ts_encode : secretT -> ts_T'.+1.-tuple shareT ;
  ts_correct : forall (s : secretT) (shares : ts_T'.+1.-tuple shareT),
    ts_valid s shares ->
    ts_recon shares = s ;
  ts_private : forall (s1 s2 : secretT) (shares : ts_T'.+1.-tuple shareT)
    (C : {set 'I_ts_T'.+1}),
    #|C| < ts_k'.+1 ->
    ts_valid s1 shares ->
    exists shares' : ts_T'.+1.-tuple shareT,
      ts_valid s2 shares' /\
      (forall i : 'I_ts_T'.+1, i \in C -> tnth shares' i = tnth shares i) ;
  ts_encode_valid : forall s, ts_valid s (ts_encode s) ;
}.

Arguments ts_T' {secretT shareT}.
Arguments ts_k' {secretT shareT}.
Arguments ts_valid {secretT shareT}.
Arguments ts_recon {secretT shareT}.
Arguments ts_encode {secretT shareT}.
Arguments ts_correct {secretT shareT}.
Arguments ts_private {secretT shareT}.
Arguments ts_encode_valid {secretT shareT}.

(** ts_recon ts (ts_encode ts s) = s for any secret s: reconstructing ts's
    own encoding recovers it, the ts_correct/ts_encode_valid round-trip
    packaged as one rewrite that composed-scheme correctness proofs can
    apply directly instead of re-deriving it. *)
Lemma ts_recon_encode {sT shT : Type} (ts : ThresholdScheme sT shT) (s : sT) :
  ts_recon ts (ts_encode ts s) = s.
Proof. exact: ts_correct (ts_encode_valid ts s). Qed.

(** The total share count T = (ts_T' ts).+1 of a ThresholdScheme, the
    carrier size that threshold inequalities such as ts_T <= ts_k compare
    against the reconstruction threshold. *)
Definition ts_T {sT shT : Type} (ts : ThresholdScheme sT shT) : nat :=
  (ts_T' ts).+1.

(** The reconstruction threshold k = (ts_k' ts).+1 of a ThresholdScheme:
    the coalition size at which ts_private's secrecy guarantee stops
    applying. *)
Definition ts_k {sT shT : Type} (ts : ThresholdScheme sT shT) : nat :=
  (ts_k' ts).+1.

(******************************************************************************)
(*     Section 2: Coordinate-Permutation Compatibility                        *)
(******************************************************************************)

Section compatibility.

Variables (gT : finGroupType) (G : {group gT}).
Variables (secretT shareT : Type).
Variable ts : ThresholdScheme secretT shareT.

Let T := (ts_T' ts).+1.

(** ts_recon_perm_invariant perm ts holds when reordering a valid share
    tuple by [perm g] before reconstruction yields the same secret, for
    every g in G. This is the compatibility contract between an abstract
    ThresholdScheme and a monodromy representation: a monodromy action
    satisfies it because it only permutes coordinates, so the contract is
    stated on coordinate permutations rather than on value-transformations
    of the shares, which a monodromy walk need not respect. *)
Definition ts_recon_perm_invariant (perm : gT -> {perm 'I_T}) : Prop :=
  forall (g : gT) (s : secretT) (shares : T.-tuple shareT),
    g \in G ->
    ts_valid ts s shares ->
    ts_recon ts [tuple tnth shares (perm g i) | i < T] = s.

End compatibility.

Arguments ts_recon_perm_invariant {gT G secretT shareT}.

(******************************************************************************)
(*     Section 3: Sum-mod-N Instance                                          *)
(******************************************************************************)

Section sum_mod_instance.

Variable N' : nat.
Let N := N'.+2.

Variable T' : nat.
Let T := T'.+1.

(* Reconstruction: compute the sum of all share values mod N *)
Definition sum_mod_recon (shares : T.-tuple 'I_N) : 'I_N :=
  Ordinal (ltn_pmod (\sum_(i < T) (tnth shares i : nat)) (isT : 0 < N)).

(* Validity: the sum of share values mod N equals the secret *)
Definition sum_mod_valid_pred (s : 'I_N) (shares : T.-tuple 'I_N) : Prop :=
  (\sum_(i < T) (tnth shares i : nat)) %% N = s :> nat.

(** sum_mod_recon returns exactly the secret encoded by a valid share
    tuple: sum_mod_valid_pred s shares gives sum_mod_recon shares = s.
    This is sum-mod-N's correctness property, the ts_correct field of the
    ThresholdScheme built below. *)
Lemma sum_mod_scheme_correct (s : 'I_N) (shares : T.-tuple 'I_N) :
  sum_mod_valid_pred s shares ->
  sum_mod_recon shares = s.
Proof.
rewrite /sum_mod_valid_pred /sum_mod_recon => Hvalid.
by apply: val_inj.
Qed.

(** For any coalition C smaller than the threshold T and any two secrets
    s1 s2, a share tuple valid for s1 has a share tuple valid for s2 that
    agrees with it on C's coordinates: sum-mod-N's privacy property, the
    ts_private field of the ThresholdScheme built below. *)
Lemma sum_mod_scheme_private (s1 s2 : 'I_N)
    (shares : T.-tuple 'I_N) (C : {set 'I_T}) :
  #|C| < T ->
  sum_mod_valid_pred s1 shares ->
  exists shares' : T.-tuple 'I_N,
    sum_mod_valid_pred s2 shares' /\
    (forall i : 'I_T, i \in C -> tnth shares' i = tnth shares i).
Proof.
move=> HC Hvalid.
have Hpsni := @partial_sum_no_info N' T' shares (1 : {perm 'I_N}) C s1 s2 HC.
have Hvalid' : sum_mod_valid shares s1 by rewrite /sum_mod_valid /sheets_sum.
have [shares' [Hv' [Hagree _]]] := Hpsni Hvalid'.
exists shares'; split; last exact: Hagree.
by rewrite /sum_mod_valid_pred /sheets_sum.
Qed.

(* Encoding: [0, 0, ..., 0, s] — sum = s mod N *)
Definition sum_mod_encode (s : 'I_N) : T.-tuple 'I_N :=
  mktuple (fun i : 'I_T => if i == ord_max then s else ord0).

(** sum_mod_encode s, the tuple [0,...,0,s], is a valid sharing of s: its
    entries sum to s modulo N. This is the ts_encode_valid field of the
    ThresholdScheme built below. *)
Lemma sum_mod_encode_valid (s : 'I_N) :
  sum_mod_valid_pred s (sum_mod_encode s).
Proof.
rewrite /sum_mod_valid_pred /sum_mod_encode.
under eq_bigr do rewrite tnth_mktuple.
rewrite big_ord_recr /= eqxx.
have Hwiden : forall i : 'I_T', widen_ord (leqnSn T') i == (ord_max : 'I_T) = false.
  move=> i; apply/negbTE.
  by rewrite -val_eqE /=; move: (ltn_ord i); rewrite ltn_neqAle => /andP[].
under eq_bigr do rewrite Hwiden.
by rewrite big1 // add0n modn_small //; exact: ltn_ord.
Qed.

(** sum_mod_scheme is the ThresholdScheme built from sum_mod_valid_pred,
    sum_mod_recon and sum_mod_encode with the three lemmas above as its
    correctness, privacy and encoding-validity fields: the sum-mod-N
    realization of the abstract Section 1 interface, letting the
    framework's generic theorems apply to sum-mod-N without re-deriving
    them. *)
Definition sum_mod_scheme : ThresholdScheme 'I_N 'I_N :=
  @MkThresholdScheme 'I_N 'I_N T' T'
    sum_mod_valid_pred
    sum_mod_recon
    sum_mod_encode
    sum_mod_scheme_correct
    sum_mod_scheme_private
    sum_mod_encode_valid.

End sum_mod_instance.

Arguments sum_mod_scheme {N' T'}.

(******************************************************************************)
(*     Section 4: Protocol Integration                                        *)
(******************************************************************************)

(* Helper: cast a tuple when the size index changes *)
Definition cast_tuple {A : Type} {n m : nat} (H : n = m)
    (t : n.-tuple A) : m.-tuple A :=
  eq_rect n (fun k => k.-tuple A) t m H.

(** tnth (cast_tuple H t) i = tnth t (cast_ord (esym H) i): a tuple cast
    along a length equality H composes with the matching index cast on
    'I_m. Section 4 below reindexes protocol endpoints through casts of
    this kind whenever the scheme's declared length and the protocol's
    coordinate count are only propositionally, not definitionally, equal. *)
Lemma tnth_cast_tuple {A : Type} {n m : nat} (H : n = m)
    (t : n.-tuple A) (i : 'I_m) :
  tnth (cast_tuple H t) i = tnth t (cast_ord (esym H) i).
Proof.
subst m.
by rewrite /cast_tuple /= cast_ord_id.
Qed.

Section pgg_protocol_secret.

Variable M : MonodromyReprType.
Variable PI : PGGInterface M.

Let gT := pgg_gT M.
Let N := (pgg_N' M).+1.
Let T := (pi_T' PI).+1.
Let rho := @pgg_rho M.
Let starts := pi_starts PI.

(* The SHARES live on 'I_N (the card positions); the SECRET is an arbitrary
   [secretT]. For the position-model instances secretT = 'I_N; den Boer plugs in
   secretT = bool. *)
Variable secretT : Type.
Variable ts : ThresholdScheme secretT 'I_N.
Hypothesis HT : ts_T' ts = pi_T' PI.

(* A fixed content readout applied to each shuffled start before reconstruction.
   With [content = id] every statement below collapses definitionally to the
   original position model. *)
Variable content : 'I_N -> 'I_N.

Let sT := (ts_T' ts).+1.

(* Cast endpoints to the scheme's tuple type *)
Definition pgg_recon (eps : T.-tuple 'I_N) : secretT :=
  ts_recon ts (cast_tuple (esym (congr1 S HT)) eps).

(* The secret reconstructed from endpoints, read through the content map *)
Definition pgg_recon_endpoints (P : gT) : secretT :=
  pgg_recon [tuple content (rho P (tnth starts i)) | i < T].

(* Main theorem: coordinate-permutation compatible scheme + G-stable starts
   + valid starting shares ⟹ reconstruction of endpoints recovers the secret.
   The reconstruction-invariance and start-stability hypotheses are only needed
   on the recon-symmetry subgroup [H] that actually contains the hidden element
   [P]; [H] is required to be a subgroup of [pgg_G M] so the morphism action of
   [rho] applies. *)
Lemma pgg_recon_monodromy_correct (H : {group gT}) (s : secretT) (P : gT)
    (perm : gT -> {perm 'I_sT})
    (HsubG : H \subset pgg_G M)
    (G_stable : forall g, g \in H ->
       forall i : 'I_sT,
         content (rho g (tnth (cast_tuple (esym (congr1 S HT)) starts) i)) =
         tnth [tuple content (tnth (cast_tuple (esym (congr1 S HT)) starts) j)
              | j < sT] (perm g i)) :
  P \in H ->
  ts_valid ts s [tuple content (tnth (cast_tuple (esym (congr1 S HT)) starts) j)
                | j < sT] ->
  @ts_recon_perm_invariant gT H _ _ ts perm ->
  pgg_recon_endpoints P = s.
Proof.
move=> PG Hvalid Hperm.
rewrite /pgg_recon_endpoints /pgg_recon.
have -> : cast_tuple (esym (congr1 S HT))
            [tuple content (rho P (tnth starts i)) | i < T] =
          [tuple tnth [tuple content
              (tnth (cast_tuple (esym (congr1 S HT)) starts) j) | j < sT]
              (perm P i) | i < sT].
  apply: eq_from_tnth => i.
  rewrite tnth_cast_tuple tnth_mktuple tnth_mktuple -tnth_cast_tuple.
  by rewrite (G_stable P PG i).
exact: Hperm PG Hvalid.
Qed.

End pgg_protocol_secret.
