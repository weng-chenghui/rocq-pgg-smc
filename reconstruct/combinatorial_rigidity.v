(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Combinatorial rigidity: the non-curve dual of AlgebraicRigidity            *)
(*                                                                            *)
(* AlgebraicRigidity carries a ThresholdWitness whose tw_genus0_klein field      *)
(* asserts #|G| <= klein_genus0_bound M when the genus is zero. For a combinatorial,    *)
(* curve-free group such as the pile-scramble wreath Z_n wr S_m, that field    *)
(* would force a false inequality (e.g. 98 <= 60 for Z_7 wr S_2). So a         *)
(* different record is needed.                                                *)
(*                                                                            *)
(* CombinatorialRigidity drops the curve/pgl-cap field and instead asserts     *)
(* the two facts together that s5_nogo (reconstruct/s5_nogo.v) proves no       *)
(* genus-zero curve can satisfy: the group order EXCEEDS the curve-rigidity    *)
(* bound (cr_klein_lt_card : klein_genus0_bound M < #|pgg_G M|) WHILE the recovery gap is  *)
(* positive (cr_genus_gt0 : 0 < cd_genus). It still bundles a shuffle         *)
(* certificate bundle (anonymity) and a CoveringScheme (the recovery scheme   *)
(* and its gap).                                                             *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finset fingroup order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext.
Require Import pgg_interface.
From pgg_reconstruct Require Import covering_scheme cover_tradeoff
                                    algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section combinatorial_rigidity.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.

(** CombinatorialRigidity: the curve-free analogue of AlgebraicRigidity,
    bundling the same security certificate and covering-scheme content but
    replacing the curve-rigidity cap tw_genus0_klein with the order
    inequality cr_klein_lt_card. A curve-free group such as the wreath
    product Z_n wr S_m can have #|G| exceed the Klein genus-0 bound while
    the recovery gap stays positive, exactly the conjunction tw_genus0_klein
    would force to be false; CombinatorialRigidity certifies that
    conjunction directly instead. *)
Record CombinatorialRigidity := MkCombinatorialRigidity {
  cr_security : ShuffleCertificateBundle R M ;
  cr_covering : CoveringScheme M ;
  cr_genus_gt0 : 0 < cd_genus (cs_data cr_covering) ;
  cr_klein_lt_card : klein_genus0_bound M < #|pgg_G M|
}.

(** Every CombinatorialRigidity instance realises the group order exceeding
    the curve-rigidity bound together with a positive recovery gap: exactly
    the conjunction s5_nogo proves no genus-zero curve can satisfy. This is
    CombinatorialRigidity's separation result, a witness lying outside what
    curve-based AlgebraicRigidity instances can reach. *)
Lemma cr_large_group_with_gap (cr : CombinatorialRigidity) :
  (klein_genus0_bound M < #|pgg_G M|) /\ (0 < cd_genus (cs_data (cr_covering cr))).
Proof. by split; [exact: cr_klein_lt_card | exact: cr_genus_gt0]. Qed.

End combinatorial_rigidity.

Arguments CombinatorialRigidity R M : clear implicits.
