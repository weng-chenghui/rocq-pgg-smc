(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* five_card_tableau_checks: the terms the kernel refuses at the five-card    *)
(* instance                                                                   *)
(*                                                                            *)
(* Each entry below is one written term that the kernel rejects, recorded so  *)
(* that the rejection is compiled rather than described. A recorded rejection *)
(* says what it says about the one term written under it and about no other   *)
(* term: it fixes a spelling that does not typecheck, and states no general   *)
(* impossibility.                                                             *)
(*                                                                            *)
(* Seven groups of rejections, and one positive statement. The first is what  *)
(* a model may be sampled over: a family typed against another instance's     *)
(* observed execution is refused where it is written. The second is the level *)
(* a program reaches against the level the manifest records for its row,      *)
(* which the one-cut Sampled program does not meet and its certified sibling  *)
(* does. The third is a row equation written for another path, the repeated   *)
(* certified row against the uniform row, which differ in two of their five   *)
(* coordinates.                                                               *)
(*                                                                            *)
(* The fourth is the terminal's index binder: a conclude payload with the     *)
(* right relation but no index binder is refused, which is what keeps a row   *)
(* from publishing a bound that holds only at the index a reader happened to  *)
(* pick. The fifth is the ideal function: a different Boolean function of the *)
(* same two bits is refused where it is written, so the function a row names  *)
(* is decided by the kernel.                                                  *)
(*                                                                            *)
(* The sixth is the proof: the proximity arm's proposition is a bound between *)
(* two laws on a real field and not a Boolean the kernel reduces, so neither  *)
(* conversion nor done reaches it, and both spellings are refused.            *)
(*                                                                            *)
(* The seventh is what a certificate may hold, and its four rejections have   *)
(* two causes. One is about the ideal, whose adapter is typed over the row's  *)
(* own execution parameters, so another instance's model and the witness      *)
(* proved about it are refused there. Three are about the sample adapter      *)
(* every certificate type is indexed by, which separates the two Kim models   *)
(* although their families carry one index type, and which refuses a          *)
(* certificate of either arm where the other model's is required.             *)
(*                                                                            *)
(* The one positive statement of this file is a comparison of two rows rather *)
(* than a statement about one, which is what puts it here: the two rows over  *)
(* the one-cut model carry different arms, so the pair is two statements      *)
(* about one probability model and not one statement published twice.         *)
(*                                                                            *)
(* Key results:                                                               *)
(*   five_card_row_biased_arm_neq                                             *)
(*                           == the two rows over the one-cut model carry     *)
(*                              different arms                                *)
(******************************************************************************)

Require Import Lia.
From mathcomp Require Import zify.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter pgg_trace_secrecy.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import var_dist_joint_law.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage five_card_exec five_card_models.
From pgg_smc Require Import kim_input_privacy.
From pgg_smc Require Import five_card_mixing.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import s5_models.
From pgg_smc Require Import s5_tableau_analysis_bridged.
From pgg_smc Require Import five_card_proximity.
From pgg_smc Require Import five_card_tableau_observed.
From pgg_smc Require Import five_card_tableau_sampled.
From pgg_smc Require Import five_card_tableau_analysis_bridged.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.


(******************************************************************************)
(*     What a model may be sampled over                                       *)
(******************************************************************************)

(** A model built over one run does not sample another. The two models named
    at Sampled are typed over this prefix's observed execution, so the two
    statements hold; a family typed over a different instance's observed
    execution is rejected where it is written. *)
Fail Definition five_card_row_s5_family : Tableau Sampled :=
  five_card_committed
    sample S5Analysis.rand_family.


(******************************************************************************)
(*     The level a program reaches                                            *)
(******************************************************************************)

(** five_card_row_biased_tableau admits no ascription at the manifest's
    level: that program reaches Sampled and the manifest records
    AnalysisBridged for the row. The two levels differ, and the difference is
    rejected by the kernel here rather than asserted in prose. It is a fact
    about this one program and not about the biased path, which
    five_card_row_biased_indistinguishability_tableau carries to
    AnalysisBridged. *)
Fail Definition five_card_row_biased_at_manifest_level
  : Tableau (apr_completion five_card_row_biased) :=
  five_card_row_biased_tableau.


(******************************************************************************)
(*     A row equation written for another path                                *)
(******************************************************************************)

(** What a row equation does reject is a program written for another path.
    The repeated row's certified program publishes the seven-cut model at
    IdealFinite and the uniform row holds the uniform family at
    StaticExecutedOnly, so the two rows differ in two of their five fields
    and the equation is refused. *)
Fail Definition five_card_row_repeated_indistinguishability_uniform_rowE
  : published_row five_card_row_repeated_indistinguishability_tableau
    = five_card_row_uniform
  := erefl.


(******************************************************************************)
(*     The terminal's index binder                                            *)
(******************************************************************************)

(** The terminal's obligation is one inequality per real field and per index
    of the family. A payload with the right relation but no index binder is
    rejected, which is what keeps a row from publishing a bound that holds
    only at the index a reader happened to pick. *)
Fail Definition five_card_row_repeated39_unindexed
  : PublishedRowAt five_card_reprice39 :=
  five_card_committed
    sample  kim_centi_family
    certify InputIndistinguishability kim_centi_cert
    |> conclude five_card_reprice39
       by (fun R => Order.POrderTheory.ltW (kim_centi_cert_eps_lt R tt))
    |> publish IdealFinite BaselineClassicalOnly.


(******************************************************************************)
(*     The ideal function                                                     *)
(******************************************************************************)

(** A different Boolean function of the same two bits is rejected where it is
    written, so the function a row names is decided by the kernel rather than
    by the reader. *)
Fail Definition five_card_F_or
  : fn_f five_card_F = (fun ab : bool * bool => ab.1 || ab.2) := erefl.


(******************************************************************************)
(*     The conclusion does not hold by computation                            *)
(******************************************************************************)

(** The arm's proposition at Kim's one-cut certificate is not closed by
    conversion. A variation distance between two laws on a real field is not a
    Boolean a kernel reduces, so a proof of the row's claim has to be the
    mathematics and cannot be the computation. *)
Fail Definition five_card_biased_proximity_by_computation (R : realType)
    (idx : unit)
  : IdealProximityPropAt (kim_biased_proximity_cert R idx)
      (ipc_eps (kim_biased_proximity_cert R idx))
  := ltac:(move=> C HC; reflexivity).

(** Nor by done, which is what a clause left to a tactic in a row would
    reach. *)
Fail Definition five_card_biased_proximity_by_done (R : realType) (idx : unit)
  : IdealProximityPropAt (kim_biased_proximity_cert R idx)
      (ipc_eps (kim_biased_proximity_cert R idx))
  := ltac:(by []).


(******************************************************************************)
(*     What a certificate may name as its ideal                               *)
(******************************************************************************)

(** Another instance's model is not an ideal for this one. The ideal adapter
    is typed over the row's own execution parameters, so a model of the S5
    instance and the witness proved about it are rejected where they are
    written and not deep inside the proposition. *)
Fail Definition kim_biased_cert_s5_ideal (R : realType) (idx : unit)
  : IdealProximityCert (amf_sample kim_biased_family R idx) :=
  @MkIdealProximityCert R five_card_algebra five_card_params
    (amf_sample kim_biased_family R idx)
    (amf_sample s5_rand_family R idx)
    (s5_rand_exact_witness R idx)
    (five_card_leakage.Secret R)
    (1 / 50)
    (fun C _ => @kim_biased_proximity_close R C).

(** Two models of one instance whose families carry one index type are still
    two adapters. The one-cut model's proximity certificate is rejected where
    the seven-cut model's is required: a certificate is typed over the sample
    adapter, and the two adapters differ in their sample space as well as in
    their law. *)
Fail Definition kim_centi_proximity_from_biased (R : realType) (idx : unit)
  : IdealProximityCert (amf_sample kim_centi_family R idx) :=
  kim_biased_proximity_cert R idx.

(** The same rejection where it is written in a row: the seven-cut model's
    named Sampled value does not take the one-cut model's certificate. *)
Fail Definition five_card_row_repeated_proximity : Tableau AnalysisBridged :=
  five_card_row_repeated_tableau
    certify IdealProximity kim_biased_proximity_cert.

(** The converse direction, at the arm the tree already carries: the
    seven-cut model's input-indistinguishability certificate is rejected
    where the one-cut model's is required. The proximity arm and the
    input-indistinguishability arm are rejected at the same argument, the
    sample adapter each certificate type is indexed by, so a certificate of
    either arm is rejected where the other model's is required. *)
Fail Definition kim_biased_indistinguishability_from_centi
  (R : realType) (idx : unit)
  : IndistinguishabilityCert (amf_sample kim_biased_family R idx) :=
  kim_centi_cert R idx.


(******************************************************************************)
(*     The arm two rows over one model carry                                  *)
(******************************************************************************)

(** The two rows over the one model carry different arms, so the pair is two
    statements about one probability model and not one statement published
    twice. *)
Lemma five_card_row_biased_arm_neq (R : realType)
    (idx : amf_index (ab_f (published_at five_card_row_biased_proximity)) R) :
  security_arm_of five_card_row_biased_proximity R idx
  <> security_arm_of five_card_row_biased_branch_indistinguishability R idx.
Proof. by []. Qed.
