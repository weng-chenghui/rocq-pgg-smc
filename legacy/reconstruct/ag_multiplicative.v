(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* AG Code Multiplicative Property (Issue #41)                                *)
(*                                                                            *)
(* The Hadamard (coordinatewise) product of two AG codewords from C(D,G)      *)
(* and C(D,G') lies in C(D,G+G'). This is the algebraic foundation for       *)
(* multiplicative secret sharing: multiplying shares locally corresponds to   *)
(* evaluating the product of the underlying functions, yielding a codeword   *)
(* in a code with doubled degree parameter.                                   *)
(*                                                                            *)
(*   hadamard c1 c2  == coordinatewise product of row vectors                 *)
(*   ag_multiplicative == axiomatized: C(D,k) * C(D,k) \subset C(D,2k)      *)
(*   MultiplicativeScheme == record bundling base/doubled ThresholdSchemes   *)
(*     with proof that Hadamard of valid shares produces valid doubled shares *)
(*   ag_mult_scheme  == MultiplicativeScheme from AG codes via Massey         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg finalg zmodp.
From mathcomp Require Import fingroup matrix mxalgebra vector.
From infotheo Require Import ssr_ext ssralg_ext hamming linearcode.
From pgg_reconstruct Require Import pgg_sharing_framework massey
  ag_code ag_massey_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(******************************************************************************)
(*     Section 1: Hadamard (Coordinatewise) Product                           *)
(******************************************************************************)

Section hadamard.

Variable F : fieldType.
Variable n : nat.

(** The coordinatewise (Hadamard) product of two row vectors: index i of the
    result is the product of index i of each argument. This is the algebraic
    operation underlying multiplicative secret sharing: multiplying two
    players' shares locally corresponds to evaluating the pointwise product
    of the underlying encoded functions. *)
Definition hadamard (c1 c2 : 'rV[F]_n) : 'rV[F]_n :=
  \row_(i < n) (c1 ord0 i * c2 ord0 i).

(** The Hadamard product is commutative, so downstream rewrites may swap its
    arguments freely. *)
Lemma hadamard_comm (c1 c2 : 'rV[F]_n) :
  hadamard c1 c2 = hadamard c2 c1.
Proof. by apply/rowP => i; rewrite !mxE mulrC. Qed.

(** The defining coordinatewise equation: (hadamard c1 c2) at index i equals
    c1 at i times c2 at i. Stated once so later coordinatewise arguments in
    the Hadamard-Massey bridge can rewrite by this equation instead of
    unfolding mxE by hand. *)
Lemma hadamardE (c1 c2 : 'rV[F]_n) (i : 'I_n) :
  (hadamard c1 c2) ord0 i = c1 ord0 i * c2 ord0 i.
Proof. by rewrite mxE. Qed.

End hadamard.

(******************************************************************************)
(*     Section 2: Multiplicative Property for AG Codes (axiomatized)          *)
(******************************************************************************)

Section ag_multiplicative_sect.

Variable F : finFieldType.
Variable n : nat.

(* Two AG codes: C(D,k) and C(D,2k) from degree-k and degree-2k divisors *)
Variables (k_1 k_2 : nat).
Variable ev_k : 'M[F]_(k_1, n).
Variable ev_2k : 'M[F]_(k_2, n).

(* The Hadamard product of two codewords of C(D,k) lands in C(D,2k): if
   f \in L(G) and g \in L(G'), then fg \in L(G+G'), and evaluation commutes
   with the coordinatewise product, ev(f)*ev(g) = ev(fg). Proving this from
   the generator-matrix definition of ag_code alone needs the function-field
   interpretation of AG codes, which is why it is axiomatized here rather
   than derived; it is the algebraic fact that makes multiplying shares
   locally implement multiplying secrets. *)
Hypothesis ag_mult :
  forall c1 c2 : 'rV[F]_n,
    c1 \in ag_code ev_k -> c2 \in ag_code ev_k ->
    hadamard c1 c2 \in ag_code ev_2k.

End ag_multiplicative_sect.

(******************************************************************************)
(*     Section 3: MultiplicativeScheme Record                                 *)
(******************************************************************************)

(* A multiplicative secret sharing scheme: two Massey-based threshold schemes
   (base from C(D,k) and doubled from C(D,2k)) such that the Hadamard product
   of valid base shares yields valid doubled shares with secret = product. *)

Section mult_scheme_def.

Variable F : finFieldType.

(** A multiplicative secret-sharing scheme: two Massey ThresholdSchemes over
    the same threshold ts_T' (a base scheme and a doubled scheme), together
    with a proof that coordinatewise-multiplying two valid share tuples of
    the base scheme produces a valid share tuple of the doubled scheme
    carrying the product secret. This is the interface a BGW-style secure
    multiplication protocol needs: local share multiplication that provably
    tracks a global secret multiplication. *)
Record MultiplicativeScheme := {
  ms_base : ThresholdScheme F F ;
  ms_doubled : ThresholdScheme F F ;
  ms_T_eq : ts_T' ms_base = ts_T' ms_doubled ;
  ms_mult : forall (s1 s2 : F)
    (shares1 shares2 : (ts_T' ms_base).+1.-tuple F),
    ts_valid ms_base s1 shares1 ->
    ts_valid ms_base s2 shares2 ->
    ts_valid ms_doubled (s1 * s2)
      (cast_tuple (congr1 S ms_T_eq)
        [tuple tnth shares1 i * tnth shares2 i | i < (ts_T' ms_base).+1]) ;
}.

End mult_scheme_def.

Arguments MultiplicativeScheme {F}.

(******************************************************************************)
(*     Section 4: Hadamard-Massey Bridge                                      *)
(******************************************************************************)

(* The Hadamard product of massey_codewords is itself a massey_codeword,
   with secret equal to the product of the two secrets. *)

Section hadamard_massey.

Variable F : finFieldType.
Variable n' : nat.
Let n := n'.+2.

(** Applying hadamard to two massey_codeword outputs equals applying
    massey_codeword to the product secret and the coordinatewise-multiplied
    share vectors. This identifies "multiply the encoded codewords" with
    "encode the multiplied secret and shares", which is what lets
    multiplicative security reduce to the AG-code product property ag_mult
    rather than to a separate argument about Massey encoding. *)
Lemma hadamard_massey_codeword (s1 s2 : F)
    (sh1 sh2 : 'rV[F]_n'.+1) :
  hadamard (massey_codeword s1 sh1) (massey_codeword s2 sh2) =
  massey_codeword (s1 * s2) (hadamard sh1 sh2).
Proof.
apply/rowP => i; rewrite hadamardE.
case: (unliftP ord0 i) => [j ->|->].
- by rewrite !massey_codewordS hadamardE.
- by rewrite !massey_codeword0.
Qed.

End hadamard_massey.

(******************************************************************************)
(*     Section 5: AG Multiplicative Scheme Construction                       *)
(******************************************************************************)

Section ag_mult_scheme_sect.

Variable F : finFieldType.
Variable n'' : nat.
Let n := n''.+2.

(* Base code C(D,k) parameters *)
Variables (k g : nat).
Variable ev : 'M[F]_(k, n).

Hypothesis ev_rank : \rank ev = k.
Hypothesis k_gt0 : 0 < k.
Hypothesis le_kn : k <= n.
Hypothesis lt_gk : g < k.
Hypothesis lt_kgn : k + g < n.
Hypothesis goppa_wt :
  forall m : 'rV[F]_k, m != 0 -> n - (k + g - 1) <= wH (m *m ev).
(* For any coordinate set S smaller than (k - g).-1.+2 and any target
   vector, some codeword of the base code ev agrees with target on S: a
   coalition observing too few base shares cannot rule out any secret. *)
Hypothesis ag_priv_surj :
  forall (S : {set 'I_n}) (target : 'rV[F]_n),
    #|S| < (k - g).-1.+2 ->
    exists c : 'rV[F]_n, c \in ag_code ev /\ vproj c S = vproj target S.

(* Doubled code C(D,2k) parameters *)
Variable k2 : nat.
Variable ev_2k : 'M[F]_(k2, n).

Hypothesis ev_2k_rank : \rank ev_2k = k2.
Hypothesis k2_gt0 : 0 < k2.
Hypothesis le_k2n : k2 <= n.
Variable g2 : nat.
Hypothesis lt_g2k2 : g2 < k2.
Hypothesis lt_k2g2n : k2 + g2 < n.
Hypothesis goppa_2k_wt :
  forall m : 'rV[F]_k2, m != 0 -> n - (k2 + g2 - 1) <= wH (m *m ev_2k).
(* The same local-surjectivity property for the doubled code ev_2k: a
   coalition observing fewer than (k2 - g2).-1.+2 doubled shares cannot rule
   out any secret. *)
Hypothesis ag_2k_priv_surj :
  forall (S : {set 'I_n}) (target : 'rV[F]_n),
    #|S| < (k2 - g2).-1.+2 ->
    exists c : 'rV[F]_n, c \in ag_code ev_2k /\ vproj c S = vproj target S.

(* Multiplicative property: C(D,k) * C(D,k) ⊆ C(D,2k) *)
Hypothesis ag_mult :
  forall c1 c2 : 'rV[F]_n,
    c1 \in ag_code ev -> c2 \in ag_code ev ->
    hadamard c1 c2 \in ag_code ev_2k.

(* Equal code lengths means equal ts_T' values *)
Hypothesis eq_T' : ts_T' (ag_massey ev_rank k_gt0 le_kn lt_kgn goppa_wt ag_priv_surj) =
  ts_T' (ag_massey ev_2k_rank k2_gt0 le_k2n lt_k2g2n goppa_2k_wt ag_2k_priv_surj).

Let base := ag_massey ev_rank k_gt0 le_kn lt_kgn goppa_wt ag_priv_surj.
Let doubled := ag_massey ev_2k_rank k2_gt0 le_k2n lt_k2g2n goppa_2k_wt ag_2k_priv_surj.

(** Multiplying two valid base-scheme share tuples coordinatewise, and
    casting across the ts_T' base = ts_T' doubled equality, gives a valid
    doubled-scheme share tuple for the product secret s1 * s2. This is the
    multiplicative correctness property MultiplicativeScheme packages:
    local share multiplication implements secret multiplication. *)
(* The Hadamard product of two massey_codewords is a massey_codeword with
   secret = product (hadamard_massey_codeword), and ag_mult places that
   codeword's coordinates in the doubled code; cast_tuple only bridges the
   type-level equality ts_T' base = ts_T' doubled. *)
Lemma ag_massey_mult (s1 s2 : F)
    (shares1 shares2 : (ts_T' base).+1.-tuple F) :
  ts_valid base s1 shares1 ->
  ts_valid base s2 shares2 ->
  ts_valid doubled (s1 * s2)
    (cast_tuple (congr1 S eq_T')
      [tuple tnth shares1 i * tnth shares2 i | i < (ts_T' base).+1]).
Proof.
move=> Hv1 Hv2.
rewrite /ts_valid /= /massey_valid_tuple.
have -> : congr1 S eq_T' = erefl _ by exact: eq_irrelevance.
rewrite /cast_tuple /=.
have -> : tuple_to_rV [tuple tnth shares1 i * tnth shares2 i | i < n''.+1]
          = hadamard (tuple_to_rV shares1) (tuple_to_rV shares2).
  by apply/rowP => i; rewrite !mxE tnth_mktuple.
rewrite -hadamard_massey_codeword.
exact: ag_mult Hv1 Hv2.
Qed.

(** The MultiplicativeScheme built from a base AG code ev and a doubled AG
    code ev_2k satisfying ag_mult: base and doubled Massey ThresholdSchemes
    at equal ts_T', paired with ag_massey_mult as the proof that
    coordinatewise share multiplication tracks secret multiplication. This
    is the concrete instance a BGW-style secure-multiplication protocol runs
    against. *)
Definition ag_mult_scheme : MultiplicativeScheme :=
  {| ms_base := base ;
     ms_doubled := doubled ;
     ms_T_eq := eq_T' ;
     ms_mult := ag_massey_mult |}.

End ag_mult_scheme_sect.

(******************************************************************************)
(*     Section 6: Strong Multiplication Threshold (axiomatized)               *)
(******************************************************************************)

Section strong_mult.

Variable F : finFieldType.

Variable ms : @MultiplicativeScheme F.

(* Strong multiplication condition (BGW88): the base threshold satisfies
   T <= 2*k + k', equivalently t < n/3 - 4g/3 for genus g.
   This ensures that T parties hold enough shares for both base and
   doubled scheme reconstruction, enabling secure multiplication. *)
Hypothesis strong_mult_threshold :
  ts_T (ms_base ms) <= 2 * ts_k (ms_base ms) + ts_k (ms_doubled ms).

End strong_mult.
