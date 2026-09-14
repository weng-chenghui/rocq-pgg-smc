From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5 five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_exec.
From pgg_smc Require Import pgg_instance pgg_algebra_syntax pgg_functionality.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ------------------------------------------------------------------ *)
(* 1. the algebra                                                       *)
(* ------------------------------------------------------------------ *)

Definition fc_algebra : PGGAlgebraic := algebra {
  mount   << fc_kim_gens >> ;
  seat    players (ord_tuple 5) by ord_tuple5_uniq ;
  secret  bool ;
  deal    fcI_scheme
          encode fcI_encode
          read   fcI_recon
          private by fcI_private
          shuffled_by pgg_rho by fcI_perm_compatible_kim ;
  cache   seats den_boer_players by five_card_players_enumE }.

Lemma fc_profileE : instance_profile fc_algebra = five_card_profile.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* 2. the committer processes and the payload they send                 *)
(* ------------------------------------------------------------------ *)

Definition fc_procs (ab : bool * bool)
    : seq (aproc pgg_dtype (pgg_data (pga_n fc_algebra).+2)) :=
  [:: mk_aproc (@pgg_commit FiveCardKim_M 7 (encode_bool ab.1))
    ; mk_aproc (@pgg_commit FiveCardKim_M 8 (encode_bool ab.2))].

Definition fc_payload (ab : bool * bool) : seq 'I_(pga_n fc_algebra).+2 :=
  [:: encode_bool ab.1; encode_bool ab.2].

(* ------------------------------------------------------------------ *)
(* 3. the parameters, and the plug they build                           *)
(* ------------------------------------------------------------------ *)

Definition fc_params : ExecutionParams fc_algebra :=
  encoded_input_params fc_algebra (bool * bool)
    (fun ab => ab.1 && ab.2) den_boer_layout den_boer_assemble_valid
    den_boer_decode fc_procs 100.

Lemma fc_execE : instance_exec fc_params = five_card_exec_plug.
Proof. by []. Qed.

Lemma fc_obsE : ex_content_obs fc_params = five_card_content_obs.
Proof. by []. Qed.

Lemma fc_expectedE :
  ex_expected fc_params = (fun ab : bool * bool => ab.1 && ab.2).
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* 4. the three run obligations                                         *)
(* ------------------------------------------------------------------ *)

Lemma fc_terminates : instance_terminates_stmt fc_params.
Proof. by vm_compute. Qed.

Lemma fc_commit_endpoints :
  profile_commit_endpoints_stmt fc_procs fc_payload 100.
Proof. by vm_compute. Qed.

Lemma fc_decK : forall ab : bool * bool, den_boer_decode (fc_payload ab) = ab.
Proof. by case=> a b; exact: den_boer_decodeK. Qed.

Definition fc_endpoints : instance_endpoints_stmt fc_params :=
  encoded_endpointsE fc_commit_endpoints fc_decK.

Definition fc_recon : instance_recon_stmt fc_params := encoded_static_recon.

Definition fc_observed : OE.ObservedExecution :=
  instance_observed fc_terminates fc_endpoints fc_recon.

(* the five data fields agree with the hand-written record; the three proof
   fields are different terms of the same three propositions, so the records
   themselves are not convertible *)
Lemma fc_observed_profileE :
  OE.oe_profile fc_observed = OE.oe_profile five_card_observed.
Proof. by []. Qed.
Lemma fc_observed_execE :
  OE.oe_execution fc_observed = OE.oe_execution five_card_observed.
Proof. by []. Qed.
Lemma fc_observed_obsE :
  OE.oe_content_obs fc_observed = OE.oe_content_obs five_card_observed.
Proof. by []. Qed.
Lemma fc_observed_expectedE :
  OE.oe_expected fc_observed = OE.oe_expected five_card_observed.
Proof. by []. Qed.
Lemma fc_observed_idxE :
  OE.oe_P_idx fc_observed = OE.oe_P_idx five_card_observed.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* 5. the same, written as a Tableau program                            *)
(* ------------------------------------------------------------------ *)

Definition fc_target : Targeted :=
  fc_algebra functionality (fun ab : bool * bool => ab.1 && ab.2).

Definition fc_prefix : Tableau Observed :=
  fc_target
  encoded inputs (bool * bool)
          layout den_boer_layout
          by den_boer_assemble_valid
          decoded_by den_boer_decode
          committed_by fc_procs
          fuel 100
  execute terminates by vm_compute
          endpoints by fc_endpoints
          recon by fc_recon.

Lemma fc_prefix_paramsE : projT1 (projT2 (tableau_at fc_prefix)) = fc_params.
Proof. by []. Qed.

Lemma fc_prefix_execE :
  instance_exec (projT1 (projT2 (tableau_at fc_prefix))) = five_card_exec_plug.
Proof. by []. Qed.

Lemma fc_prefix_realises :
  realises_expected (ob_obs (tableau_at fc_prefix)) (targeted_F fc_target).
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* 6. the two framework equations this instance does not otherwise use  *)
(* ------------------------------------------------------------------ *)

(* dealt_step and params_step at the dealer-dealt parameters are one term *)
Lemma fc_dealt_params_stepE :
  @dealt_step fc_algebra I 100
  = params_step fc_algebra I (dealt_secret_params fc_algebra 100).
Proof. exact: dealt_params_stepE. Qed.

(* the functionality obligation through the framework lemma rather than by [] *)
Lemma fc_realises_expected :
  realises_expected
    (@instance_observed fc_algebra fc_params fc_terminates fc_endpoints
       fc_recon)
    (targeted_F fc_target).
Proof.
exact (@encoded_realises_expected fc_target den_boer_layout
          den_boer_assemble_valid den_boer_decode fc_procs 100
          fc_terminates fc_endpoints fc_recon).
Qed.

(* every argument before the three run facts occurs in their types and is
   therefore implicit; leaving them to unification does not close the goal,
   which is why the lemma is applied with @ above *)
Lemma fc_realises_expected' :
  realises_expected
    (@instance_observed fc_algebra fc_params fc_terminates fc_endpoints
       fc_recon)
    (targeted_F fc_target).
Proof.
Fail exact: encoded_realises_expected.
exact (@encoded_realises_expected fc_target den_boer_layout
         den_boer_assemble_valid den_boer_decode fc_procs 100
         fc_terminates fc_endpoints fc_recon).
Qed.
