(* PROBE, not production. Row T7 and the instance half of row T6 of           *)
(* notes/20260920-terminals-below-analysis-bridged-probe-design.md.           *)
(*                                                                            *)
(* The eight-card word model is named at Sampled and two programs continue    *)
(* from it to AnalysisBridged. Published at Sampled instead, the program      *)
(* carries the link lemma and no security evidence, and its path is not the   *)
(* manifest's word path, which is at AnalysisBridged.                         *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finset reals boolp.
From infotheo Require Import fdist.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import pgl27_tableau_sampled.
From belowprobe Require Import t_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     T7: the word model published at Sampled                                *)
(******************************************************************************)

(* The eight-card word model handed over at the level its own program reaches
   before any certify statement: run correctness and the identification of the
   executed coalition reader with the direct computation, and no security
   evidence. The transfer status is the refusal to compare, the value standing
   for a program that names a model and proves nothing about an idealized
   one. *)
Definition pgl27_word_published_sampled : PublishedSampled :=
  publish_sampled BaselineClassicalOnly NoModelComparison pgl27_word_sampled.

(* The level of the path this terminal builds. *)
Lemma pgl27_word_published_completionE :
  ap_completion (published_level_path pgl27_word_published_sampled) = Sampled.
Proof. exact: erefl. Qed.

(* The level of the manifest's word path, which the two programs over this
   model reach by certifying security evidence. The two levels differ, so the
   value above is not a second description of the manifest's path. *)
Lemma pgl27_word_path_completionE :
  ap_completion pgl27_word_path = AnalysisBridged.
Proof. exact: erefl. Qed.

(* The two paths are therefore not the same term. *)
Fail Definition pgl27_word_published_pathE_false :
  published_level_path pgl27_word_published_sampled = pgl27_word_path := erefl.

(* The model slot of the published path is the family the program named. *)
Lemma pgl27_word_published_modelE :
  ap_model (published_level_path pgl27_word_published_sampled)
  = sp_f (tableau_at pgl27_word_sampled).
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     T6 at the instance: a transfer status is data                          *)
(******************************************************************************)

(* The unrestricted terminal accepts IdealFinite at a program that has proved
   no transfer theorem, a status being data the terminal copies. *)
Definition pgl27_word_published_idealfinite : PublishedSampled :=
  publish_sampled BaselineClassicalOnly IdealFinite pgl27_word_sampled.

(* The restricted terminal refuses it. *)
Fail Check (publish_sampled_restricted BaselineClassicalOnly IdealFinite
              pgl27_word_sampled).

(* The restricted terminal at the status a program with no model comparison
   writes. *)
Definition pgl27_word_published_restricted : PublishedSampled :=
  publish_sampled_restricted BaselineClassicalOnly SampledNoModelComparison
    pgl27_word_sampled.

(* The restricted and the unrestricted spellings agree at that status. *)
Lemma pgl27_word_published_restrictedE :
  pgl27_word_published_restricted = pgl27_word_published_sampled.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     T5 at this instance: no security reader applies                        *)
(******************************************************************************)

Fail Check (view_secrecy_of pgl27_word_published_sampled).
Fail Check (pgl27_word_published_sampled : Published).

Print Assumptions pgl27_word_published_sampled.
