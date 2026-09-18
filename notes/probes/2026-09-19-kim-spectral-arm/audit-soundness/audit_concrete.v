(* AUDIT SCRATCH: the rows are not vacuously quantified over realType.     *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import boolp reals.
From mathcomp Require Import Rstruct.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_sample_adapter pgg_tableau.
From pgg_smc Require Import five_card_models.
From kim_spectral_arm_probe Require Import kim_spectral_rows_probe.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* A concrete real field, so every "forall R : realType" statement of the
   probe has at least one instance and is not vacuously true. *)
Definition A6_field : realType := Rdefinitions.R.

Definition A6_concrete_cert (idx : unit)
  : SpectralCert (amf_sample kim_centi_family A6_field idx) :=
  kim_centi_cert A6_field idx.

Definition A6_concrete_prop (idx : unit) : Prop :=
  SpectralPropAt (kim_centi_cert A6_field idx)
                 (cert_eps (kim_centi_cert A6_field idx)).

Definition A6_concrete_proof (idx : unit) : A6_concrete_prop idx :=
  spectral_tail (kim_centi_cert A6_field idx).

Print Assumptions A6_concrete_proof.
