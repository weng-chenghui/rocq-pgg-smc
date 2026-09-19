(* Audit round 2, question 2: is TOKEN a global keyword in a file requiring
   the extended surface?  A keyword cannot be a binder name. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset reals.
From infotheo Require Import fdist.
From pgg_smc Require Import pgg_analysis_status pgg_instance.
From pgg_smc Require Import pgg_analysis_manifest.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.

Definition kwp_inputs (inputs : nat) : nat := inputs.
Definition kwp_terminates (terminates : nat) : nat := terminates.
Definition kwp_publish (publish : nat) : nat := publish.
Definition kwp_conclude (conclude : nat) : nat := conclude.
Definition kwp_vm_compute (vm_compute : nat) : nat := vm_compute.
Definition kwp_ExactIndependence (ExactIndependence : nat) : nat := ExactIndependence.
Definition kwp_SpectralDecay (SpectralDecay : nat) : nat := SpectralDecay.
