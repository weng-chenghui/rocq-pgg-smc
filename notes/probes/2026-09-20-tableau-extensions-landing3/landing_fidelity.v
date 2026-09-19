(******************************************************************************)
(* landing_fidelity: the staged text of landing 3 against the probe's         *)
(* statements                                                                 *)
(*                                                                            *)
(* Every declaration landing 3 adds is restated here at the statement the     *)
(* probe proved, modulo the two edits the landing forces: the R7 rename of    *)
(* pow2_40_ge1 and pow2_40_gt0 to pgl27_pow2_40_ge1 and pgl27_pow2_40_gt0,    *)
(* and the replacement of the four-branch first [...] of                      *)
(* var_dist_fdist1_uniform by the one branch that fires.  Each restatement is *)
(* closed by exact: <staged name>, so a staged statement that drifted from    *)
(* the probe's fails here.                                                    *)
(*                                                                            *)
(* The Require block resolves to the staged copies, because _CoqProject maps  *)
(* the staged roots to pgg_smc after production's.  The provenance block      *)
(* below is what witnesses that: each Check names a constant that exists only *)
(* in the staged text of the file that declares it, so loading production's   *)
(* pgl27_exec, pgl27_models, pgl27_analysis or pgg_analysis_manifest would    *)
(* make it an error.                                                          *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_collusion_bound.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models pgl27_analysis.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import pgl27_rows pgl27_proximity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     Provenance: the four edited files are the staged ones                  *)
(******************************************************************************)

Check pgl27_exec.pgl27_prior_sample.
Check pgl27_models.pgl27_prior_exact_family.
Check pgl27_analysis.PGL27Analysis.prior_sample.
Check pgl27_analysis.PGL27Analysis.prior_exact_family.
Check pgg_analysis_manifest.pgl27_row_prior_exact.

(* The new file is reachable and is not in any production load path. *)
Check pgl27_proximity.pgl27_word_proximity_cert.

(******************************************************************************)
(*     The four additions to the edited files                                 *)
(******************************************************************************)

Check (pgl27_prior_sample
  : forall (R : realType) (secretP : R.-fdist bool),
      SampleAdapter R pgl27_exec_plug).

Check (pgl27_prior_exact_family : AnalysisModelFamily pgl27_observed).

Check (PGL27Analysis.prior_exact_family
  : AnalysisModelFamily PGL27Analysis.observed).

Check (pgl27_row_prior_exact : AnalysisPathRow).

(******************************************************************************)
(*     The ideal at every prior                                               *)
(******************************************************************************)

Lemma f_pgl27_prior_viewE (R : realType) (secretP : R.-fdist bool)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  (fun u => @static_coalition_obs pgl27_algebra pgl27_dealt_params C
              ((amf_sample pgl27_prior_exact_family R secretP).(sa_arg) u)
              ((amf_sample pgl27_prior_exact_family R secretP).(sa_cut) u))
  = pgl27_view R C.
Proof. exact: pgl27_prior_viewE. Qed.

Check (pgl27_prior_exact_witness
  : forall (R : realType) (secretP : R.-fdist bool),
      ExactWitness (amf_sample pgl27_prior_exact_family R secretP)).

Check (pgl27_row_prior_exact_tableau : PublishedRow).

Lemma f_pgl27_row_prior_exact_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_prior_exact_tableau)) R) :
  security_arm_of pgl27_row_prior_exact_tableau R idx = ExactIndependenceArm.
Proof. exact: pgl27_row_prior_exact_armE. Qed.

(* The landed statement: the manifest row of landing 3 against the program,
   rather than typed a second time.  The five fields the manifest writes in
   facade vocabulary are the five the program publishes. *)
Lemma f_pgl27_row_prior_exact_rowE :
  published_row pgl27_row_prior_exact_tableau = pgl27_row_prior_exact.
Proof. exact: pgl27_row_prior_exact_rowE. Qed.

(* The probe's own statement of the same equation, at the raw family names,
   which the landed lemma no longer spells. *)
Lemma f_pgl27_row_prior_exact_rowE_families :
  published_row pgl27_row_prior_exact_tableau
  = @MkAnalysisPathRow pgl27_observed AnalysisBridged
      pgl27_prior_exact_family StaticExecutedOnly BaselineClassicalOnly.
Proof. exact: erefl. Qed.

(* The equation published_row pgl27_row_prior_exact_tableau = pgl27_row_exact
   is a row-against-row conversion, measured at 48 to 96 s on this instance,
   and is not stated here. *)

(******************************************************************************)
(*     The distance, the certificate and the number                           *)
(******************************************************************************)

Check (pgl27_word_secret
  : forall (R : realType) (secretP : R.-fdist bool),
      {RV (sa_sampleP (pgl27_word_sample secretP)) -> bool}).

Lemma f_pgl27_word_proximity_close (R : realType) (secretP : R.-fdist bool)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  (#|C| < profile_k (instance_profile pgl27_algebra))%N ->
  var_dist
    (fdistmap (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params
                           C ((pgl27_word_sample secretP).(sa_arg) u)
                           ((pgl27_word_sample secretP).(sa_cut) u),
                         pgl27_word_secret secretP u))
       (sa_sampleP (pgl27_word_sample secretP)))
    (fdistmap (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params
                           C ((pgl27_prior_sample secretP).(sa_arg) u)
                           ((pgl27_prior_sample secretP).(sa_cut) u),
                         pgl27_secret R u))
       (sa_sampleP (pgl27_prior_sample secretP)))
  <= 2%:R^-40.
Proof. exact: pgl27_word_proximity_close. Qed.

Check (pgl27_word_proximity_cert
  : forall (R : realType) (secretP : R.-fdist bool),
      IdealProximityCert (amf_sample pgl27_word_family R secretP)).

Lemma f_pgl27_word_proximity_cert_idealE (R : realType)
    (secretP : R.-fdist bool) :
  ipc_ideal (pgl27_word_proximity_cert secretP)
  = amf_sample (ab_f (published_at pgl27_row_prior_exact_tableau)) R secretP
  /\ ExactIndependence (ipc_witness (pgl27_word_proximity_cert secretP))
     = ab_port (published_at pgl27_row_prior_exact_tableau) R secretP.
Proof. exact: pgl27_word_proximity_cert_idealE. Qed.

Lemma f_pgl27_word_proximity_cert_epsE (R : realType)
    (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP) = 2%:R^-40 :> R.
Proof. exact: pgl27_word_proximity_cert_epsE. Qed.

Lemma f_pgl27_word_proximity_eps_halfE (R : realType)
    (secretP : R.-fdist bool) :
  cert_eps (pgl27_word_cert secretP)
  = ipc_eps (pgl27_word_proximity_cert secretP)
    + ipc_eps (pgl27_word_proximity_cert secretP).
Proof. exact: pgl27_word_proximity_eps_halfE. Qed.

(* R7: the probe declares these two as pow2_40_ge1 and pow2_40_gt0, with no
   instance prefix.  The statements are the probe's. *)
Fact f_pow2_40_ge1 (R : realType) : (1:R) <= 2%:R^+40.
Proof. exact: pgl27_pow2_40_ge1. Qed.

Fact f_pow2_40_gt0 (R : realType) : (0:R) < 2%:R^+40.
Proof. exact: pgl27_pow2_40_gt0. Qed.

Lemma f_pgl27_word_proximity_le39 (R : realType) (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP) <= 2%:R^-39 :> R.
Proof. exact: pgl27_word_proximity_le39. Qed.

(* The obligation is met strictly: the certificate's number is half the
   number the row publishes. *)
Lemma f_pgl27_word_proximity_lt39 (R : realType) (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP) < 2%:R^-39 :> R.
Proof.
have H0 : (0:R) < 2%:R^-40 by rewrite invr_gt0 pgl27_pow2_40_gt0.
have He := pow2_split R.
rewrite pgl27_word_proximity_cert_epsE; lra.
Qed.

Lemma f_pgl27_word_proximity_cert_eps_lt2 (R : realType)
    (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP) < 2%:R :> R.
Proof. exact: pgl27_word_proximity_cert_eps_lt2. Qed.

(******************************************************************************)
(*     The two rows over the word model                                       *)
(******************************************************************************)

Check (pgl27_row_word_proximity : PublishedRowAt pgl27_reprice39).

Lemma f_pgl27_row_word_proximity_rowE :
  published_row pgl27_row_word_proximity = pgl27_row_word.
Proof. exact: pgl27_row_word_proximity_rowE. Qed.

Lemma f_pgl27_row_word_proximity_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_word_proximity)) R) :
  security_arm_of pgl27_row_word_proximity R idx = IdealProximityArm.
Proof. exact: pgl27_row_word_proximity_armE. Qed.

Lemma f_pgl27_row_word_arms_sampledE :
  ab_f (published_at pgl27_row_word_proximity)
  = sp_f (tableau_at pgl27_word_sampled)
  /\ ab_f (published_at pgl27_row_word_branch39)
     = sp_f (tableau_at pgl27_word_sampled).
Proof. exact: pgl27_row_word_arms_sampledE. Qed.

Lemma f_pgl27_row_word_obs_sampledE :
  ab_obs (published_at pgl27_row_word_proximity)
  = sp_obs (tableau_at pgl27_word_sampled)
  /\ ab_obs (published_at pgl27_row_word_branch39)
     = sp_obs (tableau_at pgl27_word_sampled).
Proof. exact: pgl27_row_word_obs_sampledE. Qed.

Lemma f_pgl27_row_word_arm_neq (R : realType) (secretP : R.-fdist bool) :
  security_arm_of pgl27_row_word_proximity R secretP
  <> security_arm_of pgl27_row_word_branch39 R secretP.
Proof. exact: pgl27_row_word_arm_neq. Qed.

(******************************************************************************)
(*     What the row states, and what is refused                               *)
(******************************************************************************)

Theorem f_pgl27_word_view_proximity (R : realType) (secretP : R.-fdist bool)
    (C : {set 'I_8}) (HC : (#|C| <= 3)%N) :
  var_dist
    (fdistmap (fun u => (@sa_coalition_view R pgl27_profile pgl27_exec_plug
                           (amf_sample pgl27_word_family R secretP) 0 C u,
                         pgl27_word_secret secretP u))
       (sa_sampleP (amf_sample pgl27_word_family R secretP)))
    ((fdistmap (@sa_coalition_view R pgl27_profile pgl27_exec_plug
                  (pgl27_prior_sample secretP) 0 C) (pgl27P_gen secretP))
     `x (fdistmap (pgl27_secret R) (pgl27P_gen secretP)))
  <= 2%:R^-39.
Proof. exact: pgl27_word_view_proximity. Qed.

Lemma f_var_dist_fdist1_uniform (R : realType) :
  var_dist (fdist1 true : R.-fdist bool) (fdist_uniform (R := R) card_bool)
  = 1.
Proof. exact: var_dist_fdist1_uniform. Qed.

Lemma f_pgl27_word_uniform_ideal_not_close (R : realType)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  ~ (var_dist
       (fdistmap (fun u => (@static_coalition_obs pgl27_algebra
                              pgl27_dealt_params C
                              ((pgl27_word_sample (fdist1 true : R.-fdist bool))
                                 .(sa_arg) u)
                              ((pgl27_word_sample (fdist1 true : R.-fdist bool))
                                 .(sa_cut) u),
                            pgl27_word_secret
                              (fdist1 true : R.-fdist bool) u))
          (sa_sampleP (pgl27_word_sample (fdist1 true : R.-fdist bool))))
       (fdistmap (fun u => (@static_coalition_obs pgl27_algebra
                              pgl27_dealt_params C
                              ((pgl27_sample R).(sa_arg) u)
                              ((pgl27_sample R).(sa_cut) u),
                            pgl27_secret R u))
          (sa_sampleP (pgl27_sample R)))
     <= 2%:R^-40).
Proof. exact: pgl27_word_uniform_ideal_not_close. Qed.

(******************************************************************************)
(*     Assumptions                                                            *)
(******************************************************************************)

(* pgl27_exec.v *)
Print Assumptions pgl27_prior_sample.

(* pgl27_models.v *)
Print Assumptions pgl27_prior_exact_family.

(* pgl27_analysis.v *)
Print Assumptions PGL27Analysis.prior_sample.
Print Assumptions PGL27Analysis.prior_exact_family.

(* pgg_analysis_manifest.v *)
Print Assumptions pgl27_row_prior_exact.

(* pgl27_proximity.v *)
Print Assumptions pgl27_prior_viewE.
Print Assumptions pgl27_prior_exact_witness.
Print Assumptions pgl27_row_prior_exact_tableau.
Print Assumptions pgl27_row_prior_exact_armE.
Print Assumptions pgl27_row_prior_exact_rowE.
Print Assumptions pgl27_word_secret.
Print Assumptions pgl27_word_proximity_close.
Print Assumptions pgl27_word_proximity_cert.
Print Assumptions pgl27_word_proximity_cert_idealE.
Print Assumptions pgl27_word_proximity_cert_epsE.
Print Assumptions pgl27_word_proximity_eps_halfE.
Print Assumptions pgl27_pow2_40_ge1.
Print Assumptions pgl27_pow2_40_gt0.
Print Assumptions pgl27_word_proximity_le39.
Print Assumptions pgl27_word_proximity_cert_eps_lt2.
Print Assumptions pgl27_row_word_proximity.
Print Assumptions pgl27_row_word_proximity_rowE.
Print Assumptions pgl27_row_word_proximity_armE.
Print Assumptions pgl27_row_word_arms_sampledE.
Print Assumptions pgl27_row_word_obs_sampledE.
Print Assumptions pgl27_row_word_arm_neq.
Print Assumptions pgl27_word_view_proximity.
Print Assumptions var_dist_fdist1_uniform.
Print Assumptions pgl27_word_uniform_ideal_not_close.
