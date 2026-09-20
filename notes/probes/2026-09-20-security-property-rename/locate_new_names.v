(* Library collision probe for the security-property / security-evidence
   rename.  The preamble is the union of the Require Import preambles of
   manifest/pgg_tableau.v, manifest/pgg_tableau_syntax.v,
   manifest/pgg_tableau_arm_relations.v,
   instances/kim2025/tableau/five_card_tableau_analysis_bridged.v and
   instances/pgl27/tableau/pgl27_tableau_checks.v, plus those five modules
   themselves.  Every Locate below must answer "No object of basename ...". *)

Require Import Lia.
From HB Require Import structures.
From mathcomp Require Import zify.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_weighted_words.
From pgg_smc Require Import pgg_observed_execution pgg_sample_adapter.
From pgg_smc Require Import pgg_leakage_witness pgg_trace_secrecy.
From pgg_smc Require Import pgg_collusion_bound pgg_analysis_status.
From pgg_smc Require Import var_dist_supp var_dist_joint_law.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage five_card_exec five_card_models.
From pgg_smc Require Import kim_input_privacy five_card_mixing.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import pgg_tableau_arm_relations.
From pgg_smc Require Import five_card_proximity pgl27_proximity.
From pgg_smc Require Import five_card_tableau_observed.
From pgg_smc Require Import five_card_tableau_sampled.
From pgg_smc Require Import pgl27_tableau_observed.
From pgg_smc Require Import pgl27_tableau_analysis_bridged.
From pgg_smc Require Import five_card_tableau_analysis_bridged.
From pgg_smc Require Import pgl27_tableau_checks.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Locate ExactIndependenceProperty.
Locate IdealProximityProperty.
Locate InputIndistinguishabilityProperty.
Locate EvidenceProp.
Locate SecurityProperty.
Locate SecurityEvidence.
Locate ab_security_property.
Locate ab_evidence.
Locate certify_exact_propertyE.
Locate certify_idealproximity_propertyE.
Locate certify_indistinguishability_propertyE.
Locate conclude_propertyE.
Locate five_card_biased_branch_indistinguishability_published_propertyE.
Locate five_card_biased_indistinguishability_published_propertyE.
Locate five_card_biased_proximity_published_propertyE.
Locate five_card_biased_published_property_neq.
Locate five_card_biased_published_inv25_propertyE.
Locate five_card_repeated_indistinguishability_published_propertyE.
Locate five_card_repeated_published39_propertyE.
Locate five_card_uniform_published_propertyE.
Locate pgl27_exact_published_propertyE.
Locate pgl27_prior_exact_published_propertyE.
Locate pgl27_word_property_is_not_exact.
Locate pgl27_word_branch_published39_propertyE.
Locate pgl27_word_proximity_published_propertyE.
Locate pgl27_word_published39_propertyE.
Locate pgl27_word_published_propertyE.
Locate pgl27_word_published_property_neq.
Locate evidence_property.
Locate evidence_conclude.
Locate psl211_alldecks_published_propertyE.
Locate psl211_word_proximity_published_propertyE.
Locate publish_propertyE.
Locate s5_rand_published_propertyE.
Locate security_property_of.
