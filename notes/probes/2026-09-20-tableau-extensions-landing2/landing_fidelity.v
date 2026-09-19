(******************************************************************************)
(* landing_fidelity: landing 2's staged text against the probe's statements   *)
(*                                                                            *)
(* Logical path tableau_ext_landing2. Every Require below resolves to the     *)
(* staged copy, because the staged roots are the last -R entries bound to     *)
(* pgg_smc. Nothing here is a new mathematical claim: each restatement is the *)
(* probe's statement verbatim and is closed by the staged declaration it      *)
(* restates.                                                                  *)
(*                                                                            *)
(* The provenance block is what fails if a production object were loaded in   *)
(* place of a staged one. security/var_dist_joint_law.v is a file no          *)
(* production load path holds at all, so a Require of it that resolves        *)
(* resolved to the staged tree, and var_dist_own_marginals and var_dist_prodL *)
(* exist in it and in no production file. card_tnth_count has to be gone from *)
(* the staged lib/var_dist_supp.v and present in five_card_mixing.v;          *)
(* kim_centi_marginal_bound40 and kim_centi_cut_mixing40 exist in the         *)
(* production instances/kim2025/five_card_mixing.v and not in the staged one, *)
(* so a Check on them has to fail. kim_centi_cert40 and its number equation   *)
(* left instances/kim2025/five_card_rows.v with landing 1 and have to fail    *)
(* for the same reason.                                                       *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import var_dist_joint_law.
From pgg_reconstruct Require Import algebraic_rigidity.
From pgg_smc Require Import five_card_group five_card_family.
From pgg_smc Require Import five_card_exec five_card_models.
From pgg_smc Require Import five_card_leakage five_card_kim kim_input_privacy.
From pgg_smc Require Import five_card_mixing.
From pgg_smc Require Import s5_exec s5_models.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import pgg_tableau_arm_relations.
From pgg_smc Require Import five_card_rows s5_rows five_card_proximity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     Provenance                                                             *)
(******************************************************************************)

Check var_dist_own_marginals.
Check var_dist_prodL.
Check var_dist_fdistmap_pair.
Check card_tnth_count.
Fail Check kim_centi_marginal_bound40.
Fail Check kim_centi_cut_mixing40.
Fail Check kim_centi_cert40.
Fail Check kim_centi_cert40_epsE.
Check var_dist_supp.var_dist_le2.
Fail Check var_dist_supp.card_tnth_count.
Check five_card_mixing.card_tnth_count.

(******************************************************************************)
(*     The five lemmas of security/var_dist_joint_law.v                       *)
(******************************************************************************)

Lemma landing_var_dist_fdistmap_pair (R : realType) (U V W : finType)
    (P Q : R.-fdist U) (reading : U -> V) (secret : U -> W) (d : R) :
  var_dist P Q <= d ->
  var_dist (fdistmap (fun u => (reading u, secret u)) P)
           (fdistmap (fun u => (reading u, secret u)) Q) <= d.
Proof. exact: var_dist_fdistmap_pair. Qed.

Lemma landing_var_dist_prodR (R : realType) (A B : finType)
    (P : R.-fdist A) (Q1 Q2 : R.-fdist B) :
  var_dist (P `x Q1) (P `x Q2) = var_dist Q1 Q2.
Proof. exact: var_dist_prodR. Qed.

Lemma landing_var_dist_prodL (R : realType) (A B : finType)
    (P1 P2 : R.-fdist A) (Q : R.-fdist B) :
  var_dist (P1 `x Q) (P2 `x Q) = var_dist P1 P2.
Proof. exact: var_dist_prodL. Qed.

Lemma landing_fdist_prod_snd (R : realType) (A B : finType)
    (P : R.-fdist A) (Q : R.-fdist B) :
  fdistmap snd (P `x Q) = Q.
Proof. exact: fdist_prod_snd. Qed.

Lemma landing_var_dist_own_marginals (R : realType) (V W : finType)
    (J : R.-fdist (V * W)) (Mr : R.-fdist V) (Ms : R.-fdist W) (d : R) :
  var_dist J (Mr `x Ms) <= d ->
  var_dist J ((fdistmap fst J) `x (fdistmap snd J)) <= 3%:R * d.
Proof. exact: var_dist_own_marginals. Qed.

(******************************************************************************)
(*     The lemma moved into instances/kim2025/five_card_mixing.v              *)
(******************************************************************************)

Lemma landing_card_tnth_count (n : nat) (T : Type) (t : n.-tuple T)
    (p : pred T) :
  #|[pred k : 'I_n | p (tnth t k)]| = count p t.
Proof. exact: card_tnth_count. Qed.

(******************************************************************************)
(*     manifest/pgg_tableau_arm_relations.v                                   *)
(******************************************************************************)

Lemma landing_idealproximity_prop_at2 (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IdealProximityCert sa) :
  IdealProximityPropAt cert 2%:R.
Proof. exact: idealproximity_prop_at2. Qed.

Lemma landing_indistinguishability_prop_cert_free (R : realType)
    (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E))
    (cert cert' : IndistinguishabilityCert sa) (c : R) :
  IndistinguishabilityPropAt cert c = IndistinguishabilityPropAt cert' c.
Proof. exact: indistinguishability_prop_cert_free. Qed.

Lemma landing_idealproximity_reading_le (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IdealProximityCert sa) (c : R) :
  IdealProximityPropAt cert c ->
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| < profile_k (instance_profile A))%N ->
    var_dist
      (fdistmap (@sa_coalition_view R (instance_profile A) (instance_exec E)
                   sa 0 C) (sa_sampleP sa))
      (fdistmap (@sa_coalition_view R (instance_profile A) (instance_exec E)
                   (ipc_ideal cert) 0 C) (sa_sampleP (ipc_ideal cert)))
    <= c.
Proof. exact: idealproximity_reading_le. Qed.

(******************************************************************************)
(*     instances/kim2025/five_card_proximity.v : the distance                 *)
(******************************************************************************)

Lemma landing_five_card_uniform_pairE (R : realType) :
  fdist_uniform card_bool2 = fdist_uniform five_card_card_bool2
    :> R.-fdist (bool * bool).
Proof. exact: five_card_uniform_pairE. Qed.

Lemma landing_five_card_reading_secretE (R : realType)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1})
    (d : R.-fdist five_card_leakage.Omega) :
  fdistmap (fun u => (@static_coalition_obs five_card_algebra five_card_params
                        C (five_card_sample_arg u) (five_card_sample_cut u),
                      five_card_leakage.Secret R u)) d
  = fdistmap (fun ag : (bool * bool) *
                pgg_gT (mp_M (instance_profile five_card_algebra)) =>
                (@static_coalition_obs five_card_algebra five_card_params C
                   ag.1 ag.2, ag.1.1 && ag.1.2))
      (fdistmap (fun u : five_card_leakage.Omega =>
                   (u.1, five_card_sample_cut u)) d).
Proof. exact: five_card_reading_secretE. Qed.

Lemma landing_five_card_arg_cut_prodE (R : realType) (W : R.-fdist 'I_5) :
  fdistmap (fun u : five_card_leakage.Omega => (u.1, five_card_sample_cut u))
    ((fdist_uniform five_card_card_bool2) `x W)
  = ((fdist_uniform five_card_card_bool2)
     `x (fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g) W)).
Proof. exact: five_card_arg_cut_prodE. Qed.

Lemma landing_kim_biased_proximity_close (R : realType)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1}) :
  var_dist
    (fdistmap (fun u => (@static_coalition_obs five_card_algebra
                           five_card_params C (five_card_sample_arg u)
                           (five_card_sample_cut u),
                         five_card_leakage.Secret R u))
       (kim_input_dist (kim_centi_lt R) (kim_centi_gt R)))
    (fdistmap (fun u => (@static_coalition_obs five_card_algebra
                           five_card_params C (five_card_sample_arg u)
                           (five_card_sample_cut u),
                         five_card_leakage.Secret R u))
       (five_card_leakage.P R))
  <= 1 / 50 :> R.
Proof. exact: kim_biased_proximity_close. Qed.

(******************************************************************************)
(*     The certificate and its number                                         *)
(******************************************************************************)

Check (kim_biased_proximity_cert
       : forall (R : realType) (idx : unit),
           IdealProximityCert (amf_sample kim_biased_family R idx)).

Lemma landing_kim_biased_proximity_cert_idealE (R : realType) (idx : unit) :
  ipc_ideal (kim_biased_proximity_cert R idx)
  = amf_sample (ab_f (published_at five_card_row_uniform_tableau)) R idx
  /\ ExactIndependence (ipc_witness (kim_biased_proximity_cert R idx))
     = ab_port (published_at five_card_row_uniform_tableau) R idx.
Proof. exact: kim_biased_proximity_cert_idealE. Qed.

Lemma landing_kim_biased_proximity_cert_epsE (R : realType) (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx) = 1 / 50 :> R.
Proof. exact: kim_biased_proximity_cert_epsE. Qed.

Lemma landing_kim_biased_proximity_eps_halfE (R : realType) (idx : unit) :
  cert_eps (kim_biased_cert_exact R idx)
  = ipc_eps (kim_biased_proximity_cert R idx)
    + ipc_eps (kim_biased_proximity_cert R idx).
Proof. exact: kim_biased_proximity_eps_halfE. Qed.

Lemma landing_kim_biased_proximity_cert_eps_lt2 (R : realType) (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx) < 2%:R.
Proof. exact: kim_biased_proximity_cert_eps_lt2. Qed.

(******************************************************************************)
(*     The two rows over the one model                                        *)
(******************************************************************************)

Check (five_card_row_biased_branch_indistinguishability : PublishedRow).
Check (five_card_row_biased_proximity : PublishedRow).

Lemma landing_branch_atE :
  published_at five_card_row_biased_branch_indistinguishability
  = published_at five_card_row_biased_indistinguishability_tableau.
Proof. exact: five_card_row_biased_branch_indistinguishability_atE. Qed.

Lemma landing_branch_rowE :
  published_row five_card_row_biased_branch_indistinguishability
  = five_card_row_biased.
Proof. exact: five_card_row_biased_branch_indistinguishability_rowE. Qed.

Lemma landing_proximity_rowE :
  published_row five_card_row_biased_proximity = five_card_row_biased.
Proof. exact: five_card_row_biased_proximity_rowE. Qed.

Lemma landing_proximity_publishedE :
  apr_completion (published_row five_card_row_biased_proximity)
    = AnalysisBridged
  /\ apr_transfer (published_row five_card_row_biased_proximity) = IdealFinite
  /\ apr_assumptions (published_row five_card_row_biased_proximity)
     = BaselineClassicalOnly.
Proof. exact: five_card_row_biased_proximity_publishedE. Qed.

Lemma landing_branch_armE (R : realType)
    (idx : amf_index
             (ab_f (published_at
                      five_card_row_biased_branch_indistinguishability))
             R) :
  security_arm_of five_card_row_biased_branch_indistinguishability R idx
  = InputIndistinguishabilityArm.
Proof. exact: five_card_row_biased_branch_indistinguishability_armE. Qed.

Lemma landing_proximity_armE (R : realType)
    (idx : amf_index (ab_f (published_at five_card_row_biased_proximity)) R) :
  security_arm_of five_card_row_biased_proximity R idx = IdealProximityArm.
Proof. exact: five_card_row_biased_proximity_armE. Qed.

Lemma landing_arm_neq (R : realType)
    (idx : amf_index (ab_f (published_at five_card_row_biased_proximity)) R) :
  security_arm_of five_card_row_biased_proximity R idx
  <> security_arm_of five_card_row_biased_branch_indistinguishability R idx.
Proof. exact: five_card_row_biased_arm_neq. Qed.

(******************************************************************************)
(*     The published number, and what the row states                          *)
(******************************************************************************)

Theorem landing_five_card_biased_view_proximity (R : realType)
    (C : {set 'I_5}) (HC : (#|C| < 2)%N) :
  var_dist
    (fdistmap (fun u => (@sa_coalition_view R five_card_profile
                           five_card_exec_plug
                           (amf_sample kim_biased_family R tt) 0 C u,
                         five_card_leakage.Secret R u))
       (sa_sampleP (amf_sample kim_biased_family R tt)))
    ((fdistmap (@sa_coalition_view R five_card_profile five_card_exec_plug
                  (five_card_sample R) 0 C) (P R))
     `x (fdistmap (five_card_leakage.Secret R) (P R)))
  <= 1 / 50.
Proof. exact: five_card_biased_view_proximity. Qed.

Theorem landing_five_card_biased_view_own_marginals (R : realType)
    (C : {set 'I_5}) (HC : (#|C| < 2)%N) :
  var_dist
    (fdistmap (fun u => (@sa_coalition_view R five_card_profile
                           five_card_exec_plug
                           (amf_sample kim_biased_family R tt) 0 C u,
                         five_card_leakage.Secret R u))
       (sa_sampleP (amf_sample kim_biased_family R tt)))
    ((fdistmap fst
        (fdistmap (fun u => (@sa_coalition_view R five_card_profile
                               five_card_exec_plug
                               (amf_sample kim_biased_family R tt) 0 C u,
                             five_card_leakage.Secret R u))
           (sa_sampleP (amf_sample kim_biased_family R tt))))
     `x (fdistmap snd
           (fdistmap (fun u => (@sa_coalition_view R five_card_profile
                                  five_card_exec_plug
                                  (amf_sample kim_biased_family R tt) 0 C u,
                                five_card_leakage.Secret R u))
              (sa_sampleP (amf_sample kim_biased_family R tt)))))
  <= 3%:R * (1 / 50).
Proof. exact: five_card_biased_view_own_marginals. Qed.

(******************************************************************************)
(*     The number cannot be moved down                                        *)
(******************************************************************************)

Check (five_card_reprice_inv100 : Reprice).

Lemma landing_reprice_inv100E (R : realType) :
  five_card_reprice_inv100 R = Some (1 / 100 : R).
Proof. exact: erefl. Qed.

Lemma landing_kim_biased_conclude_below_false (R : realType) (idx : unit) :
  ~ (ipc_eps (kim_biased_proximity_cert R idx)
     <= odflt (ipc_eps (kim_biased_proximity_cert R idx))
          (five_card_reprice_inv100 R)).
Proof. exact: kim_biased_conclude_below_false. Qed.

(******************************************************************************)
(*     Every hypothesis discharged, and the arm's proposition at the instance *)
(******************************************************************************)

Lemma landing_five_card_singleton_below_threshold (i : 'I_5) :
  (#|[set i]| < profile_k (instance_profile five_card_algebra))%N.
Proof. exact: five_card_singleton_below_threshold. Qed.

Check (five_card_biased_proximity_at_singleton
       : forall (R : realType) (i : 'I_5), _).

Lemma landing_five_card_biased_proximity_prop_holds (R : realType) :
  IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 50).
Proof. exact: five_card_biased_proximity_prop_holds. Qed.

Lemma landing_five_card_biased_indistinguishability_implies_proximity
    (R : realType) (c : R) :
  IndistinguishabilityPropAt (kim_biased_cert R tt) c ->
  IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 50).
Proof. exact: five_card_biased_indistinguishability_implies_proximity. Qed.

(******************************************************************************)
(*     Print Assumptions : security/var_dist_joint_law.v                      *)
(******************************************************************************)

Print Assumptions var_dist_fdistmap_pair.
Print Assumptions var_dist_prodR.
Print Assumptions var_dist_prodL.
Print Assumptions fdist_prod_snd.
Print Assumptions var_dist_own_marginals.

(******************************************************************************)
(*     Print Assumptions : instances/kim2025/five_card_mixing.v               *)
(******************************************************************************)

Print Assumptions card_tnth_count.

(******************************************************************************)
(*     Print Assumptions : manifest/pgg_tableau_arm_relations.v               *)
(******************************************************************************)

Print Assumptions idealproximity_prop_at2.
Print Assumptions indistinguishability_prop_cert_free.
Print Assumptions idealproximity_reading_le.

(******************************************************************************)
(*     Print Assumptions : instances/kim2025/five_card_proximity.v            *)
(******************************************************************************)

Print Assumptions five_card_uniform_pairE.
Print Assumptions five_card_reading_secretE.
Print Assumptions five_card_arg_cut_prodE.
Print Assumptions kim_biased_proximity_close.
Print Assumptions kim_biased_proximity_cert.
Print Assumptions kim_biased_proximity_cert_idealE.
Print Assumptions kim_biased_proximity_cert_epsE.
Print Assumptions kim_biased_proximity_eps_halfE.
Print Assumptions kim_biased_proximity_cert_eps_lt2.
Print Assumptions five_card_row_biased_branch_indistinguishability.
Print Assumptions five_card_row_biased_branch_indistinguishability_atE.
Print Assumptions five_card_row_biased_branch_indistinguishability_rowE.
Print Assumptions five_card_row_biased_proximity.
Print Assumptions five_card_row_biased_proximity_rowE.
Print Assumptions five_card_row_biased_proximity_publishedE.
Print Assumptions five_card_row_biased_branch_indistinguishability_armE.
Print Assumptions five_card_row_biased_proximity_armE.
Print Assumptions five_card_row_biased_arm_neq.
Print Assumptions five_card_biased_view_proximity.
Print Assumptions five_card_biased_view_own_marginals.
Print Assumptions five_card_reprice_inv100.
Print Assumptions kim_biased_conclude_below_false.
Print Assumptions five_card_singleton_below_threshold.
Print Assumptions five_card_biased_proximity_at_singleton.
Print Assumptions five_card_biased_proximity_prop_holds.
Print Assumptions five_card_biased_indistinguishability_implies_proximity.
