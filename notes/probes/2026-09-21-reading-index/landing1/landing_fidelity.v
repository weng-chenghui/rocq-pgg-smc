(* The landed surface against the bind, at the four instances.

   The migration of the statement surface is notation only, and this file is
   the evidence for that against production rather than against a staged
   copy: every equation below puts a program of a production instance file,
   written in the landed surface, against the same program written through
   the bind and its payloads, which is the spelling the surface expanded to
   under the rules the landing removes.  exact: erefl decides each one, so
   the two texts are one term and every theorem proved about a program
   reaches the program as it now stands.

   The terms on the right are taken from the probe, surface/k16_s5.v,
   surface/k16_pgl27.v, surface/k16_kim.v, surface/k16_psl211.v and
   surface2/k_obstruction_inline.v, and are written here unchanged.  The
   file requires production alone.

   The five rules the landing changes are covered: the certify statement at
   each of the three security properties, the tightness annotation, the
   conclude terminal, the three-payload publish terminal, the Observed
   terminal, the Sampled terminal and the obstruction terminal.  The last is
   the one whose expansion gained a builder, so the Checks below read that
   builder's type and put the payload it builds against the payload the
   instance names. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import matrix zmodp boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter pgg_trace_secrecy.
From pgg_smc Require Import pgg_weighted_words smc_interpreter.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import var_dist_joint_law.
From pgg_smc Require Import pgg_randomized_sharing pgg_canonical_sharing.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import s5_profile s5_exec s5_models.
From pgg_smc Require Import s5_tableau_observed s5_tableau_sampled.
From pgg_smc Require Import s5_tableau_analysis_bridged.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models pgl27_proximity.
From pgg_smc Require Import pgl27_tableau_observed pgl27_tableau_sampled.
From pgg_smc Require Import pgl27_tableau_analysis_bridged.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage five_card_exec five_card_models.
From pgg_smc Require Import kim_input_privacy five_card_mixing.
From pgg_smc Require Import five_card_proximity.
From pgg_smc Require Import five_card_tableau_observed.
From pgg_smc Require Import five_card_tableau_sampled.
From pgg_smc Require Import five_card_tableau_analysis_bridged.
From pgg_smc Require Import psl211_group psl211_orbit psl211_closure.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_mixing.
From pgg_smc Require Import psl211_exec psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_word_model psl211_word_proximity.
From pgg_smc Require Import psl211_reading_constancy.
From pgg_smc Require Import psl211_tableau_observed psl211_tableau_sampled.
From pgg_smc Require Import psl211_tableau_analysis_bridged.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* publish Observed assuming a. *)
Lemma fid_s5_observed_bindE :
  s5_dealt_observed_published
  = (s5_dealt ;;; publish_observed of (AcceptsAxioms [:: AxS5GroupOrder])).
Proof. exact: erefl. Qed.

(* certify ExactIndependence by w, and publish t assuming a. *)
Lemma fid_s5_exact_bindE :
  s5_rand_published
  = (s5_rand_sampled
       ;;; certify_exact of s5_rand_exact_witness
       ;;; publish (AcceptsAxioms [:: AxS5GroupOrder]) of StaticExecutedOnly).
Proof. exact: erefl. Qed.

(* certify ExactIndependence by w leaks at k by H, and publish t assuming a. *)
Lemma fid_pgl27_exact_bindE :
  pgl27_exact_published
  = (pgl27_exact_sampled
       ;;; certify_exact of (exact_leaks (tableau_at pgl27_exact_sampled)
                               pgl27_exact_witness 4 pgl27_exact_leak4)
       ;;; publish BaselineClassicalOnly of StaticExecutedOnly).
Proof. exact: erefl. Qed.

(* conclude at c by p, beside a certify statement and a publish terminal. *)
Lemma fid_pgl27_conclude_bindE :
  pgl27_word_published39
  = (pgl27_dealt
       ;;; sample_step of pgl27_word_family
       ;;; certify_indistinguishability of pgl27_word_cert
       ;;; conclude pgl27_bound39
             of (fun R _ => ssr_ext.eqW (pow2_split R))
       ;;; publish BaselineClassicalOnly of IdealFinite).
Proof. exact: erefl. Qed.

(* certify InputIndistinguishability by c, and publish t assuming a. *)
Lemma fid_kim_indistinguishability_bindE :
  five_card_repeated_indistinguishability_published
  = (five_card_repeated_sampled
       ;;; certify_indistinguishability of kim_centi_cert
       ;;; publish BaselineClassicalOnly of IdealFinite).
Proof. exact: erefl. Qed.

(* certify IdealProximity by c, and publish t assuming a. *)
Lemma fid_psl211_proximity_bindE :
  psl211_word_proximity_published
  = (psl211_word_sampled
       ;;; certify_idealproximity of psl211_word_proximity_cert
       ;;; publish BaselineClassicalOnly of IdealFinite).
Proof. exact: erefl. Qed.

(* publish Obstruction InputDistinguishability at c by pf assuming a,
   against the bind form the removed rule expanded to, which names the
   payload psl211_alldecks_obstruction. *)
Lemma fid_psl211_obstruction_bindE :
  psl211_alldecks_obstruction_published
  = (psl211_exact_sampled
       ;;; publish_obstruction BaselineClassicalOnly
             of (mk_obstruction (tableau_at psl211_exact_sampled)
                   psl211_alldecks_obstruction
                   psl211_alldecks_obstruction_pf)).
Proof. exact: erefl. Qed.

(* publish Sampled t assuming a, the rule no program of the tree writes. *)
Definition fid_psl211_sampled_published : PublishedSampled :=
  psl211_exact_sampled
    |> publish Sampled SampledStaticExecutedOnly assuming BaselineClassicalOnly.

Lemma fid_psl211_sampled_bindE :
  fid_psl211_sampled_published
  = (psl211_exact_sampled
       ;;; publish_sampled BaselineClassicalOnly of SampledStaticExecutedOnly).
Proof. exact: erefl. Qed.

(* The builder the obstruction terminal expands through: a Sampled value and
   a number in the real field alone, giving the one obstruction kind at every
   field and index of that value's model family. *)
Check input_distinguishability_obstruction.
Check (input_distinguishability_obstruction (tableau_at psl211_exact_sampled)
         psl211_alldecks_number).

(* The payload the builder gives at the all-decks family and the payload the
   instance names are one term, which is why the instance's proof, stated at
   the named payload, fits the terminal with no ascription. *)
Lemma fid_psl211_builder_payloadE :
  input_distinguishability_obstruction (tableau_at psl211_exact_sampled)
    psl211_alldecks_number
  = psl211_alldecks_obstruction.
Proof. exact: erefl. Qed.

(* The number a reader takes back off the published value, at the one index
   of the all-decks family. *)
Lemma fid_psl211_obstruction_numberE (R : realType) :
  published_obstruction_kind psl211_alldecks_obstruction_published R tt
  = @InputDistinguishabilityObstruction R psl211_algebra
      psl211_alldecks_params (amf_sample psl211_exact_family R tt)
      ((#|pgg_G psl211_M|%:R)^-1).
Proof. exact: erefl. Qed.
