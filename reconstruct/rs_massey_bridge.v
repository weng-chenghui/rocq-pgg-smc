(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* RS-Massey Bridge: Concrete ThresholdScheme from Reed-Solomon Codes        *)
(*                                                                            *)
(* Connects RS codes (reed_solomon.v, rs_privacy.v) to Massey's secret       *)
(* sharing (massey.v), yielding a concrete ThresholdScheme for the genus-0   *)
(* covering (cover_genus0.v).                                                 *)
(*                                                                            *)
(*   transport_scheme f g == transport ThresholdScheme A A to B B via bij.   *)
(*   rs_massey            == ThresholdScheme F F from RS codes (d=1)         *)
(*   rs_massey_exact      == ts_T rs_massey = ts_k rs_massey                *)
(*   rs_genus0_scheme     == ThresholdScheme 'I_N 'I_N via transport        *)
(*   rs_genus0_exact      == ts_T rs_genus0_scheme = ts_k rs_genus0_scheme  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg finalg zmodp.
From mathcomp Require Import matrix mxalgebra vector poly polydiv cyclic.
From mathcomp Require Import perm.
From infotheo Require Import ssr_ext ssralg_ext hamming linearcode dft reed_solomon.
From pgg_reconstruct Require Import pgg_sharing_framework massey lagrange
  rs_privacy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(******************************************************************************)
(*     Section 1: ThresholdScheme Transport along Bijection                   *)
(******************************************************************************)

Section transport.

Variables (A B : Type).
Variable (f : A -> B) (g : B -> A).
Hypothesis gK : cancel g f.
Hypothesis fK : cancel f g.

Variable ts : ThresholdScheme A A.

Let T' := ts_T' ts.
Let k' := ts_k' ts.

(** transport_valid s shares holds exactly when g s and the g-image of
    shares are valid in the original scheme ts on A: validity pulled back
    through the bijection. This is the ts_valid field of transport_scheme
    below, letting a scheme built on A be reused on B without reproving
    anything. *)
Definition transport_valid (s : B) (shares : T'.+1.-tuple B) : Prop :=
  ts_valid ts (g s) [tuple g (tnth shares i) | i < T'.+1].

(** transport_recon shares = f (ts_recon ts (g-image of shares)):
    reconstruct in A after mapping shares back with g, then push the
    result forward to B with f. This is the ts_recon field of
    transport_scheme below. *)
Definition transport_recon (shares : T'.+1.-tuple B) : B :=
  f (ts_recon ts [tuple g (tnth shares i) | i < T'.+1]).

(** transport_valid s shares implies transport_recon shares = s: the
    ts_correct field of transport_scheme below, obtained by applying ts's
    correctness in A and closing the round trip with gK : cancel g f. *)
Lemma transport_correct (s : B) (shares : T'.+1.-tuple B) :
  transport_valid s shares -> transport_recon shares = s.
Proof.
rewrite /transport_valid /transport_recon => Hv.
by rewrite (@ts_correct _ _ ts _ _ Hv) gK.
Qed.

(** For any coalition C smaller than the threshold and any two secrets s1
    s2 in B, a transport_valid share tuple for s1 has one for s2 agreeing
    with it on C's coordinates: privacy pulled back to A via g, applied
    there, and pushed forward to B via f. This is the ts_private field of
    transport_scheme below. *)
Lemma transport_private (s1 s2 : B) (shares : T'.+1.-tuple B)
    (C : {set 'I_T'.+1}) :
  #|C| < k'.+1 ->
  transport_valid s1 shares ->
  exists shares' : T'.+1.-tuple B,
    transport_valid s2 shares' /\
    (forall i : 'I_T'.+1, i \in C -> tnth shares' i = tnth shares i).
Proof.
move=> HC Hv.
set shares_g := [tuple g (tnth shares i) | i < T'.+1].
have Hv' : ts_valid ts (g s1) shares_g := Hv.
have [shares_a [HvA Hagree]] :=
  @ts_private _ _ ts (g s1) (g s2) shares_g C HC Hv'.
exists [tuple f (tnth shares_a i) | i < T'.+1]; split.
- rewrite /transport_valid.
  have -> : [tuple g (tnth [tuple f (tnth shares_a i0) | i0 < T'.+1] i)
            | i < T'.+1] = shares_a.
    apply: eq_from_tnth => i.
    by rewrite !tnth_mktuple fK.
  exact: HvA.
- move=> i Hi.
  rewrite tnth_mktuple.
  have := Hagree _ Hi; rewrite /shares_g tnth_mktuple => ->.
  by rewrite gK.
Qed.

(** transport_encode s = f-image of (ts_encode ts (g s)): encode g s in
    A, then push the resulting share-tuple forward to B with f. This is
    the ts_encode field of transport_scheme below. *)
Definition transport_encode (s : B) : T'.+1.-tuple B :=
  [tuple f (tnth (ts_encode ts (g s)) i) | i < T'.+1].

(** transport_valid s (transport_encode s): the transported encoding is
    valid by construction, the ts_encode_valid field of transport_scheme
    below, since fK : cancel f g restores ts_encode ts (g s) inside the
    transported validity predicate. *)
Lemma transport_encode_valid (s : B) :
  transport_valid s (transport_encode s).
Proof.
rewrite /transport_valid /transport_encode.
have -> : [tuple g (tnth [tuple f (tnth (ts_encode ts (g s)) i0)
          | i0 < T'.+1] i) | i < T'.+1] = ts_encode ts (g s).
  apply: eq_from_tnth => i.
  by rewrite !tnth_mktuple fK.
exact: ts_encode_valid.
Qed.

(** transport_scheme is the ThresholdScheme on B built by transporting ts
    along the bijection f/g: it packages the six transport_* fields above,
    delegating every proof obligation to ts on A so a scheme need only be
    proved once, on whichever of A or B is more convenient. *)
Definition transport_scheme : ThresholdScheme B B :=
  @MkThresholdScheme B B T' k'
    transport_valid transport_recon transport_encode
    transport_correct transport_private transport_encode_valid.

(** Transport preserves T = k exactness: if ts_T ts = ts_k ts then
    ts_T transport_scheme = ts_k transport_scheme, because transport_scheme
    reuses ts's own T' and k' unchanged. rs_genus0_exact below applies this
    to push RS-Massey's exactness onto 'I_N. *)
Lemma transport_exact :
  ts_T ts = ts_k ts -> ts_T transport_scheme = ts_k transport_scheme.
Proof. by []. Qed.

End transport.

(******************************************************************************)
(*     Section 2: RS -> Massey Instantiation (d = 1, genus-0)                 *)
(******************************************************************************)

Section rs_massey_sect.

Variables (q m' : nat).
Hypothesis primeq : prime q.
Let F := GF m' primeq.

Variable n'' : nat.
Variable a : F.

Hypothesis qn : ~~ (q %| n''.+3)%nat.
Hypothesis an : (n''.+3).-primitive_root a.

Let n := n''.+3.

(* RS code of length n with d = 1: an [n, n-1, 2] MDS code *)
Let dn : RS.redundancy_ub 1 n := isT.
Let C := RS.code a n 1.
Let C_nt : not_trivial C := RS_not_trivial a dn.

Let rs_md : min_dist C_nt = 2 := RS_min_dist dn qn an.

Let Hd2 : 1 < min_dist C_nt.
Proof. by rewrite rs_md. Qed.

(* Privacy from rs_privacy_surj (strong version): |S| < (n-1)+1 = n *)
Let rs_priv := rs_privacy_surj dn an.

(* The Massey threshold scheme from RS codes with d = 1.
   ts_T' = n''.+1 (= n - 2), ts_k' = n''.+1 (= d_perp') *)
Definition rs_massey : ThresholdScheme F F :=
  massey_scheme C_nt Hd2 rs_priv.

(* With d = 1 and the strong privacy bound, ts_T' = ts_k' = n''.+1 *)
Lemma rs_massey_exact : ts_T rs_massey = ts_k rs_massey.
Proof. by []. Qed.

End rs_massey_sect.

(******************************************************************************)
(*     Section 3: Transport to 'I_N for CoveringScheme Integration           *)
(******************************************************************************)

Section rs_genus0.

Variables (q m' : nat).
Hypothesis primeq : prime q.
Let F := GF m' primeq.

Variable n'' : nat.
Variable a : F.

Hypothesis qn : ~~ (q %| n''.+3)%nat.
Hypothesis an : (n''.+3).-primitive_root a.

Variable N : nat.
Hypothesis defN : N = #|F|.

(** toF x = enum_val (cast_ord defN x), reading a value of F off the index
    x : 'I_N after recasting along N = #|F|: one half of the 'I_N <-> F
    bijection the transport construction of rs_genus0_scheme runs along. *)
Definition toF (x : 'I_N) : F := enum_val (cast_ord defN x).
(** ofF x = cast_ord (esym defN) (enum_rank x), the inverse reading of a
    value of F back to an index of 'I_N: the other half of the 'I_N <-> F
    bijection the transport construction of rs_genus0_scheme runs along. *)
Definition ofF (x : F) : 'I_N := cast_ord (esym defN) (enum_rank x).

(** cancel ofF toF: toF undoes ofF, half of the 'I_N <-> F bijection
    rs_genus0_scheme transports the RS-Massey scheme along. *)
Lemma ofFK : cancel ofF toF.
Proof. by move=> x; rewrite /ofF /toF cast_ordKV enum_rankK. Qed.

(** cancel toF ofF: ofF undoes toF, the other half of the 'I_N <-> F
    bijection rs_genus0_scheme transports the RS-Massey scheme along. *)
Lemma toFK : cancel toF ofF.
Proof. by move=> x; rewrite /toF /ofF enum_valK cast_ordK. Qed.

(* ThresholdScheme 'I_N 'I_N from RS-Massey via transport *)
Definition rs_genus0_scheme : ThresholdScheme 'I_N 'I_N :=
  transport_scheme toFK ofFK (rs_massey qn an).

(** ts_T rs_genus0_scheme = ts_k rs_genus0_scheme: the RS-Massey scheme's
    exact (T = k) threshold survives transport from F to 'I_N, obtained by
    pushing rs_massey_exact through toFK/ofFK. This is the file's final
    genus-0 exactness statement, feeding the CoveringScheme integration
    named in Section 3's header. *)
Lemma rs_genus0_exact :
  ts_T rs_genus0_scheme = ts_k rs_genus0_scheme.
Proof. exact: transport_exact (rs_massey_exact qn an). Qed.

End rs_genus0.

Arguments rs_genus0_scheme {q m'} primeq {n''} a qn an {N} defN.
Arguments rs_genus0_exact {q m'} primeq {n''} a qn an {N} defN.
