From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import matrix vector zmodp.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import pgg_raag_path.
From pgg_smc Require Import s5_profile s5_run s5_exec.
From pgg_smc Require Import pgg_instance pgg_algebra_syntax pgg_functionality.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ------------------------------------------------------------------ *)
(* 1. the algebra                                                       *)
(* ------------------------------------------------------------------ *)

Definition s5_algebra : PGGAlgebraic := algebra {
  mount   << path_gen_tuple 3 >> ;
  seat    players (ord_tuple 5) by s5_starts_uniq ;
  secret  'I_5 ;
  deal    s5_scheme
          encode (ts_encode s5_scheme)
          read   (ts_recon s5_scheme)
          private by (ts_private s5_scheme)
          shuffled_by pgg_rho by (@rp_recon_invariant _ _ s5_plug) ;
  cache   seats s5_run.s5_players by s5_players_enumE }.

Lemma s5_profileE : instance_profile s5_algebra = s5_profile.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* 2. the parameters, and the plug they build                           *)
(* ------------------------------------------------------------------ *)

Definition s5_rand_params : ExecutionParams s5_algebra :=
  supplied_input_params s5_algebra 'rV['Z_5]_5
    s5_rfree_layout (fun u => s5_codec (s5_tape_secret u)) 150.

Lemma s5_rand_execE : instance_exec s5_rand_params = s5_rand_exec_plug.
Proof. by []. Qed.

Lemma s5_rand_obsE : ex_content_obs s5_rand_params = s5_rcontent_obs.
Proof. by []. Qed.

Lemma s5_rand_expectedE :
  ex_expected s5_rand_params = (fun u => s5_codec (s5_tape_secret u)).
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* 3. the three run obligations                                         *)
(* ------------------------------------------------------------------ *)

Lemma s5_rand_terminatesP : instance_terminates_stmt s5_rand_params.
Proof. by vm_compute. Qed.

Lemma s5_profile_endpoints : profile_endpoints_stmt s5_algebra 150.
Proof. by vm_compute. Qed.

Definition s5_rand_endpointsP : instance_endpoints_stmt s5_rand_params :=
  supplied_endpointsE s5_profile_endpoints.

(* The framework route, from the sharing claim alone. Both this and
   s5_rand_endpointsP inherit the pre-existing axiom s5_group_order_eq
   (instances/s5/rigidity_s5_instance.v:179) through s5_algebra, whose
   reconstruction invariance is read off s5_plug; the axiom is S5's own and
   is not introduced by the encoded or supplied constructors. *)
Definition s5_rand_reconP : instance_recon_stmt s5_rand_params :=
  supplied_static_recon s5_algebra s5_rfree_valid.

(* the instance's own route, through the interpreter *)
Definition s5_rand_reconP' : instance_recon_stmt s5_rand_params :=
  s5_rand_recon.

Definition s5_rand_observedP : OE.ObservedExecution :=
  instance_observed s5_rand_terminatesP s5_rand_endpointsP s5_rand_reconP.

Lemma s5_rand_observed_profileE :
  OE.oe_profile s5_rand_observedP = OE.oe_profile s5_rand_observed.
Proof. by []. Qed.
Lemma s5_rand_observed_execE :
  OE.oe_execution s5_rand_observedP = OE.oe_execution s5_rand_observed.
Proof. by []. Qed.
Lemma s5_rand_observed_obsE :
  OE.oe_content_obs s5_rand_observedP = OE.oe_content_obs s5_rand_observed.
Proof. by []. Qed.
Lemma s5_rand_observed_expectedE :
  OE.oe_expected s5_rand_observedP = OE.oe_expected s5_rand_observed.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* 4. the same, written as a Tableau program                            *)
(* ------------------------------------------------------------------ *)

Definition s5_prefix : Tableau Observed :=
  s5_algebra
  supplied inputs 'rV['Z_5]_5
           layout s5_rfree_layout
           expecting (fun u => s5_codec (s5_tape_secret u))
           fuel 150
  execute terminates by vm_compute
          endpoints by s5_rand_endpointsP
          recon by s5_rand_reconP.

Lemma s5_prefix_paramsE :
  projT1 (projT2 (tableau_at s5_prefix)) = s5_rand_params.
Proof. by []. Qed.

Lemma s5_prefix_execE :
  instance_exec (projT1 (projT2 (tableau_at s5_prefix))) = s5_rand_exec_plug.
Proof. by []. Qed.

(* a supplied row that also names a functionality: the expecting clause and
   the ideal function are convertible, so supplied_realises applies *)
Definition s5_target : Targeted :=
  s5_algebra functionality (fun u : 'rV['Z_5]_5 => s5_codec (s5_tape_secret u)).

Lemma s5_prefix_realises :
  realises_expected (ob_obs (tableau_at s5_prefix)) (targeted_F s5_target).
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* 5. the two framework equations this instance does not otherwise use  *)
(* ------------------------------------------------------------------ *)

(* the dealer-dealt parameters are the supplied ones at the canonical
   encoding, so a fact about one transports to the other by rewriting *)
Lemma s5_dealt_suppliedE :
  instance_exec (dealt_secret_params s5_algebra 150)
  = instance_exec (supplied_input_params s5_algebra (pga_secretT s5_algebra)
      (ts_encode (pga_scheme s5_algebra)) id 150).
Proof. by rewrite dealt_supplied_paramsE. Qed.

(* the functionality obligation through the framework lemma rather than by [] *)
Lemma s5_realises_expected :
  realises_expected
    (@instance_observed s5_algebra s5_rand_params s5_rand_terminatesP
       s5_rand_endpointsP s5_rand_reconP)
    (targeted_F s5_target).
Proof.
exact (@supplied_realises_expected s5_target s5_rfree_layout 150
          s5_rand_terminatesP s5_rand_endpointsP s5_rand_reconP).
Qed.
