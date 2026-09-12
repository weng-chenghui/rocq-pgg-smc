(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Input encoding: inputs determine the starting layout                       *)
(*                                                                            *)
(* InputEncoding is the deterministic half of a randomized encoding of a       *)
(* function f over an existing ReconPlug: assemble maps inputs to a valid      *)
(* share layout (ie_assemble_valid), and equal-output inputs lie in one cut    *)
(* orbit (ie_orbit). The cut supplies the randomness.                          *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_raag.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** InputEncoding: inputs determine a valid share layout for the plug via
    ie_assemble, with the layout's secret ie_output, and equal-output inputs
    related by a monodromy permutation of that layout (ie_orbit). This is
    the deterministic half of a randomized encoding of a function: the
    input fixes the layout and its secret, while the acting group element
    (the cut) supplies the randomness that moves between layouts sharing
    the same output. *)
Record InputEncoding (M : MonodromyReprType) (secretT : Type)
    (plug : ReconPlug M secretT) (inputT : Type) := MkInputEncoding {
  ie_assemble : inputT -> (ts_T' (rp_scheme plug)).+1.-tuple 'I_(pgg_N' M).+1 ;
  ie_output      : inputT -> secretT ;
  ie_assemble_valid : forall x,
      ts_valid (rp_scheme plug) (ie_output x) (ie_assemble x) ;
  ie_orbit : forall x x', ie_output x = ie_output x' ->
      exists g : pgg_gT M, g \in pgg_G M /\
        ie_assemble x' =
          [tuple tnth (ie_assemble x) (rp_monodromy plug g i)
                | i < (ts_T' (rp_scheme plug)).+1] ;
}.

Arguments InputEncoding M secretT plug inputT.
Arguments MkInputEncoding {M secretT plug inputT}.

(** Reconstructing from ie_assemble ie x permuted by any cut g0 in the group
    returns ie_output ie x. This is the InputEncoding's self-consistency:
    whichever group element supplies the randomness, the plug's
    reconstruction recovers exactly the secret the input encodes. *)
Lemma ie_output_correct (M : MonodromyReprType) (secretT : Type)
    (plug : ReconPlug M secretT) (inputT : Type)
    (ie : InputEncoding plug inputT) (x : inputT) (g0 : pgg_gT M) :
  g0 \in pgg_G M ->
  ts_recon (rp_scheme plug)
    [tuple tnth (ie_assemble ie x) (rp_monodromy plug g0 i)
          | i < (ts_T' (rp_scheme plug)).+1] = ie_output ie x.
Proof.
move=> Hg0. apply: (rp_recon_invariant Hg0). exact: ie_assemble_valid.
Qed.

(** Reads a layout's coordinates through the monodromy action of cut P and
    reconstructs via the plug's scheme. This is the generic
    reindex-then-reconstruct operation any layout, encoded or not, is read
    through, the shape ie_output_correct proves self-consistent for
    InputEncoding's own layouts. *)
Definition recon_from_layout (M : MonodromyReprType) (secretT : Type)
    (plug : ReconPlug M secretT)
    (layout : (ts_T' (rp_scheme plug)).+1.-tuple 'I_(pgg_N' M).+1)
    (P : pgg_gT M) : secretT :=
  ts_recon (rp_scheme plug)
    [tuple tnth layout (rp_monodromy plug P i)
          | i < (ts_T' (rp_scheme plug)).+1].

(** recon_from_layout applied to an InputEncoding's own assembled layout
    returns ie_output ie x, for every cut P. This restates
    ie_output_correct in terms of the generic recon_from_layout operation,
    so reasoning phrased at that operation inherits the same
    self-consistency without unfolding the tuple comprehension by hand. *)
Lemma recon_from_layout_output (M : MonodromyReprType) (secretT : Type)
    (plug : ReconPlug M secretT) (inputT : Type)
    (ie : InputEncoding plug inputT) (x : inputT) (P : pgg_gT M) :
  P \in pgg_G M ->
  recon_from_layout (ie_assemble ie x) P = ie_output ie x.
Proof. exact: ie_output_correct. Qed.
