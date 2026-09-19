(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_tableau_checks: what the twelve-card instance's phases reject       *)
(*                                                                            *)
(* Each recorded failure below is one written term the kernel refuses, kept   *)
(* beside the term it is the near miss of. A boundary a reader can only be    *)
(* told about is a boundary a reader has to take on trust; a boundary written *)
(* out and refused is one the kernel decides. The file declares nothing and   *)
(* nothing depends on it.                                                     *)
(*                                                                            *)
(* Three boundaries are recorded. The first is that an obligation built where *)
(* the statement is written is not the named lemma: the inline-reduction      *)
(* prefix and the named prefix drive the same run, and the equation between   *)
(* the two prefixes is still refused, because an opaque lemma is convertible  *)
(* with nothing. The second is what that fork costs, that the model is typed  *)
(* over the observed execution the named prefix builds and is refused over    *)
(* the inline one, so no typed evidence crosses between them. The third is    *)
(* which ideal the proximity arm admits: a certificate's ideal is a sample    *)
(* adapter over the row's own execution, so the eight-card orbit instance's   *)
(* model is refused at its type, and the word model itself is refused as its  *)
(* own ideal, a certificate naming its own model holding its distance field   *)
(* at zero.                                                                   *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals lra.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import var_dist_supp var_dist_joint_law.
From pgg_smc Require Import smc_interpreter pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_weighted_words.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import psl211_group psl211_orbit psl211_closure.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_mixing.
From pgg_smc Require Import psl211_exec psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_word_model psl211_word_proximity.
From pgg_smc Require Import pgl27_models.
From pgg_smc Require Import psl211_tableau_observed psl211_tableau_sampled.
From pgg_smc Require Import psl211_tableau_analysis_bridged.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     An inline obligation is not the named lemma                            *)
(******************************************************************************)

(** The two prefixes are not the same term. The rejection is a conversion
    failure between the two prefixes themselves:

      The term "erefl" has type
       "psl211_alldecks_prefix_vm = psl211_alldecks_prefix_vm"
      while it is expected to have type
       "psl211_alldecks_prefix_vm = psl211_alldecks_prefix"
      (cannot unify "psl211_alldecks_prefix_vm" and "psl211_alldecks_prefix").
*)
Fail Definition psl211_alldecks_prefix_vm_neq :
  psl211_alldecks_prefix_vm = psl211_alldecks_prefix := erefl.

(******************************************************************************)
(*     A model belongs to the run it was built over                           *)
(******************************************************************************)

(** The analysis model family is typed against the observed execution the
    named prefix builds, and is rejected over the inline-reduction one: the
    two prefixes hold different termination proofs, so their observed
    executions are different terms and no typed evidence crosses between them.
    This is the fork made visible, and the reason the row names its
    termination lemma. *)
Fail Definition psl211_row_vm_reuse : Tableau Sampled :=
  psl211_alldecks_prefix_vm sample psl211_exact_family.

(******************************************************************************)
(*     Which ideal the arm refuses                                            *)
(******************************************************************************)

(** The eight-card orbit instance's exact family cannot be the ideal of a
    twelve-card word row. A certificate's ideal is a sample adapter over the
    row's own execution, and the two instances run different executions, so
    the field is rejected at its type and no distance is reached. The
    rejection is a failure to unify the two executions:

      The term "amf_sample pgl27_exact_family R tt" has type
       "SampleAdapter R (OE.oe_execution pgl27_exec.pgl27_observed)"
      while it is expected to have type
       "SampleAdapter R (instance_exec psl211_alldecks_params)".
*)
Fail Definition psl211_word_proximity_cert_pgl27_ideal (R : realType)
    (idx : unit)
  : IdealProximityCert (amf_sample psl211_word_family R idx) :=
  @MkIdealProximityCert R psl211_algebra psl211_alldecks_params
    (amf_sample psl211_word_family R idx)
    (amf_sample pgl27_exact_family R tt)
    (psl211_exact_witness R idx)
    (psl211_alldecks_secret R)
    (2%:R^-40)
    (fun C HC => @psl211_word_proximity_close R C HC).

(** The certificate's ideal is not convertible with the word model it is
    about. A certificate naming its own model as the ideal holds its distance
    field at zero, the two sides of that field being one term, so the number
    it publishes bounds a distance from the model to itself. The rejection is
    a failure to unify the two models:

      The term "erefl" has type
       "ipc_ideal (psl211_word_proximity_cert R idx) =
        ipc_ideal (psl211_word_proximity_cert R idx)"
      while it is expected to have type
       "ipc_ideal (psl211_word_proximity_cert R idx) =
        amf_sample psl211_word_family R idx".
*)
Fail Definition psl211_word_proximity_cert_ideal_self (R : realType)
    (idx : unit) :
  ipc_ideal (psl211_word_proximity_cert R idx)
  = amf_sample psl211_word_family R idx := erefl.
