(* K16 of the claim ledger at the five-card instance: the surface migration
   is notation only.

   The equation puts the input-indistinguishability program of the staged
   instance file, written in the decided surface with its certificate as one
   record, against the same program written through the bind and its
   payloads.  exact: erefl decides it. *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp.
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
From pgg_smc Require Import kim_input_privacy five_card_mixing.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import five_card_proximity.
From pgg_smc Require Import five_card_tableau_observed.
From pgg_smc Require Import five_card_tableau_sampled.
From pgg_smc Require Import five_card_tableau_analysis_bridged.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* certify InputIndistinguishability by c, and publish t assuming a. *)
Lemma k16_kim_indistinguishability_bindE :
  five_card_repeated_indistinguishability_published
  = (five_card_repeated_sampled
       ;;; certify_indistinguishability of kim_centi_cert
       ;;; publish BaselineClassicalOnly of IdealFinite).
Proof. exact: erefl. Qed.
