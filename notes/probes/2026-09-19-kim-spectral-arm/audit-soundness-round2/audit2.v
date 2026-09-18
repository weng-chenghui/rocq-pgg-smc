(* Round-2 soundness audit scratch file. NOT part of the probe. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import morphism.
From mathcomp Require Import boolp reals.
From mathcomp Require Import lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import perm_uniform pgg_interface pgg_collusion_bound.
From pgg_smc Require Import pgg_weighted_words.
From pgg_smc Require Import pgg_monodromy_profile.
From pgg_smc Require Import pgg_instance pgg_functionality pgg_sample_adapter.
From pgg_smc Require Import pgg_trace_secrecy.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_encoding den_boer_run den_boer_profile.
From pgg_smc Require Import five_card_leakage five_card_exec five_card_models.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import five_card_rows.
From pgg_reconstruct Require Import algebraic_rigidity.
From kim_spectral_arm_probe Require Import var_dist_injective_probe.
From kim_spectral_arm_probe Require Import five_card_rotation_probe.
From kim_spectral_arm_probe Require Import kim_sc_close_probe.
From kim_spectral_arm_probe Require Import five_card_sc_const_probe.
From kim_spectral_arm_probe Require Import kim_spectral_rows_probe.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope ring_scope.

(* A1. The one-cut program's published row is the manifest's biased row with
   apr_transfer replaced by IdealFinite, and nothing else replaced. If this
   erefl closes, the recorded Fail fails on the transfer status alone. *)
Definition A1_biased_only_transfer
  : published_row five_card_row_biased_ideal_tableau
  = @MkAnalysisPathRow (apr_observed five_card_row_biased)
      (apr_completion five_card_row_biased)
      (apr_model five_card_row_biased)
      IdealFinite
      (apr_assumptions five_card_row_biased)
  := erefl.

(* A1b. The same for the repriced one-cut program. *)
Definition A1b_inv25_only_transfer
  : published_row five_card_row_biased_inv25
  = @MkAnalysisPathRow (apr_observed five_card_row_biased)
      (apr_completion five_card_row_biased)
      (apr_model five_card_row_biased)
      IdealFinite
      (apr_assumptions five_card_row_biased)
  := erefl.

(* A2. The repeated program's published row is the manifest's repeated row
   with apr_completion at AnalysisBridged and apr_transfer at IdealFinite.
   The model slot is ascribed at the new level because AnalysisModelSlot
   reduces to the same type at Sampled and at AnalysisBridged. *)
Definition A2_repeated_two_fields
  : published_row five_card_row_repeated_spectral_tableau
  = @MkAnalysisPathRow (apr_observed five_card_row_repeated)
      AnalysisBridged
      (apr_model five_card_row_repeated
        : AnalysisModelSlot (apr_observed five_card_row_repeated)
            AnalysisBridged)
      IdealFinite
      (apr_assumptions five_card_row_repeated)
  := erefl.

(* A2b. The repriced repeated program publishes the same row. *)
Definition A2b_repeated39_same_row
  : published_row five_card_row_repeated39
  = published_row five_card_row_repeated_spectral_tableau
  := erefl.

(* A3. The two completion levels give one model slot type, so
   five_card_row_repeated_modelE keeps its statement after a landing. *)
Definition A3_slot_type_same
  : AnalysisModelSlot FiveCardAnalysis.observed Sampled
  = AnalysisModelSlot FiveCardAnalysis.observed AnalysisBridged
  := erefl.

(* A4. The reprice obligation at one index is exactly the split identity, so
   the payload needs an equality and the identity supplied is that equality. *)
Definition A4_reprice39_obligation (R : realType) (idx : unit)
  : cert_eps (kim_centi_cert40 R idx)
  = odflt (cert_eps (kim_centi_cert40 R idx)) (five_card_reprice39 R)
  := five_card_pow2_39_split R.

Definition A4b_reprice_inv25_obligation (R : realType) (idx : unit)
  : cert_eps (kim_biased_cert_exact R idx)
  = odflt (cert_eps (kim_biased_cert_exact R idx)) (five_card_reprice_inv25 R)
  := five_card_inv50_split R.

(* A5. The reprice is not free: the same payload at a different constant is
   rejected. *)
Definition five_card_reprice38 : Reprice := fun R => Some (2%:R ^- 38 : R).

Fail Definition A5_wrong_constant : PublishedRowAt five_card_reprice38 :=
  five_card_committed
    ;;; sample_step of kim_centi_family
    ;;; certify_spectral of kim_centi_cert40
    ;;; conclude five_card_reprice38 of (fun R _ => five_card_pow2_39_split R)
    ;;; publish BaselineClassicalOnly of IdealFinite.

(* A6. A landing that moves the manifest's repeated row to AnalysisBridged
   breaks the ascription at five_card_rows.v:456-458. *)
Fail Definition A6_repeated_at_bridged : Tableau AnalysisBridged :=
  five_card_row_repeated_tableau.

(* A7. The two statements carried beside the programs still typecheck. *)
Check five_card_row_repeated_endpoint_lt.
Check five_card_row_biased_leak_bound.

(* A8. What the repriced one-cut row certifies, read off the published
   theorem at one real field and the single index. *)
Check (fun R : realType =>
  proj2 (published_thm five_card_row_biased_inv25) R tt).

(* A9. The same for the repriced repeated row. *)
Check (fun R : realType =>
  proj2 (published_thm five_card_row_repeated39) R tt).

(* A10. The threshold really is two at this instance. *)
Definition A10_threshold : profile_k (instance_profile five_card_algebra) = 2
  := erefl.

Print Assumptions A1_biased_only_transfer.
Print Assumptions A2_repeated_two_fields.
Print Assumptions A4_reprice39_obligation.
