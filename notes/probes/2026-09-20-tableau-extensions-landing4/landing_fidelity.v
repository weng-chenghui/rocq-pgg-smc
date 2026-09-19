(******************************************************************************)
(* landing_fidelity: the staged text of landing 4 against the probe's         *)
(* statements                                                                 *)
(*                                                                            *)
(* Every declaration landing 4 adds is restated here at the statement the     *)
(* probe proved, modulo the one edit the landing forces: the right-hand side  *)
(* of psl211_row_word_proximity_rowE, which the landing states at the         *)
(* manifest row psl211_row_word that the same landing adds.  Both forms are   *)
(* kept below, the landed one closed by the landed lemma and the probe's      *)
(* raw-family one closed by exact: erefl.  Every other restatement is closed  *)
(* by exact: <staged name>, so a staged statement that drifted from the       *)
(* probe's fails here.                                                        *)
(*                                                                            *)
(* The Require block resolves to the staged copies, because _CoqProject maps  *)
(* the staged roots to pgg_smc after production's.  The provenance block      *)
(* below is what witnesses that: each Check names a constant that exists only *)
(* in the staged text of the file that declares it, so loading production's   *)
(* psl211_analysis or pgg_analysis_manifest would make it an error.  Two of   *)
(* the six files landing 4 edits carry no such witness.                       *)
(* psl211_reading_constancy.v and pgg_analysis_client.v change in comments    *)
(* and in Check lines alone, so neither declares a name a Check could         *)
(* discriminate on; what stands for them is that the whole chain is compiled  *)
(* from the staged text and every dependant loads its staged .vo by digest.   *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals lra.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import var_dist_supp var_dist_joint_law.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_instance pgg_analysis_status.
From pgg_smc Require Import psl211_group psl211_closure psl211_profile.
From pgg_smc Require Import psl211_mixing.
From pgg_smc Require Import psl211_exec psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_analysis.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import psl211_rows psl211_word_model.
From pgg_smc Require Import psl211_word_proximity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Local Notation seatT :=
  ('I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1).

(******************************************************************************)
(*     Provenance: the edited files are the staged ones                       *)
(******************************************************************************)

Check psl211_analysis.PSL211Analysis.word_sample.
Check psl211_analysis.PSL211Analysis.word_family.
Check pgg_analysis_manifest.psl211_row_word.

(* The two new files are reachable and are in no production load path. *)
Check psl211_word_model.psl211_word_family.
Check psl211_word_proximity.psl211_word_proximity_cert.

(******************************************************************************)
(*     The word model, at the probe's statements                              *)
(******************************************************************************)

Check (psl211_word_cutP : forall R : realType, R.-fdist (pgg_gT psl211_M)).

Check (psl211_wordP
  : forall R : realType,
      R.-fdist (psl211_inputT * pgg_gT psl211_M)%type).

Check (psl211_word_sample
  : forall R : realType,
      SampleAdapter R (instance_exec psl211_alldecks_params)).

Check (psl211_word_family : AnalysisModelFamily psl211_alldecks_observed).

Lemma f_psl211_word_sampleP_E (R : realType) :
  sa_sampleP (psl211_word_sample R) = psl211_wordP R.
Proof. exact: psl211_word_sampleP_E. Qed.

Lemma f_psl211_word_cut_distE (R : realType) :
  @sa_cut_dist R (instance_profile psl211_algebra)
    (instance_exec psl211_alldecks_params) (psl211_word_sample R)
  = psl211_word_cutP R.
Proof. exact: psl211_word_cut_distE. Qed.

Lemma f_psl211_word_law_le40 (R : realType) :
  var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2%:R^-40.
Proof. exact: psl211_word_law_le40. Qed.

(* The cut law of the word model is the 584-letter walk the refutation
   psl211_alldecks_constancy_false_word584 is stated on, so the adapter and
   that refutation speak of one law. *)
Lemma f_psl211_word_cutP_is_walk (R : realType) :
  psl211_word_cutP R
  = @rho_from_words_weighted R 10 2 584 psl211_moves (psl211_Wuni R).
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The two facade aliases                                                 *)
(******************************************************************************)

Check (PSL211Analysis.word_sample
  : forall R : realType, SampleAdapter R PSL211Analysis.exec_plug).

Check (PSL211Analysis.word_family
  : AnalysisModelFamily PSL211Analysis.observed).

Lemma f_psl211_word_family_alias :
  PSL211Analysis.word_family = psl211_word_family.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The manifest row                                                       *)
(******************************************************************************)

Check (psl211_row_word : AnalysisPathRow).

(* The landed equation: the program publishes the manifest row by name. *)
Lemma f_psl211_row_word_proximity_rowE :
  published_row psl211_row_word_proximity = psl211_row_word.
Proof. exact: psl211_row_word_proximity_rowE. Qed.

(* The probe's form of the same equation, at the raw family names, which is
   what the manifest row's five fields were drafted from. *)
Lemma f_psl211_row_word_proximity_rowE_families :
  published_row psl211_row_word_proximity
  = @MkAnalysisPathRow psl211_alldecks_observed AnalysisBridged
      psl211_word_family IdealFinite BaselineClassicalOnly.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The distance, the certificate and its ideal                            *)
(******************************************************************************)

Lemma f_psl211_word_proximity_close (R : realType) (C : {set seatT}) :
  (#|C| < profile_k (instance_profile psl211_algebra))%N ->
  var_dist
    (fdistmap (fun u => (@static_coalition_obs psl211_algebra
                           psl211_alldecks_params C
                           ((psl211_word_sample R).(sa_arg) u)
                           ((psl211_word_sample R).(sa_cut) u),
                         psl211_alldecks_secret R u))
       (sa_sampleP (psl211_word_sample R)))
    (fdistmap (fun u => (@static_coalition_obs psl211_algebra
                           psl211_alldecks_params C
                           ((psl211_alldecks_sample R).(sa_arg) u)
                           ((psl211_alldecks_sample R).(sa_cut) u),
                         psl211_alldecks_secret R u))
       (sa_sampleP (psl211_alldecks_sample R)))
  <= 2%:R^-40.
Proof. exact: psl211_word_proximity_close. Qed.

Check (psl211_word_proximity_cert
  : forall (R : realType) (idx : unit),
      IdealProximityCert (amf_sample psl211_word_family R idx)).

Lemma f_psl211_word_proximity_cert_idealE (R : realType) (idx : unit) :
  ipc_ideal (psl211_word_proximity_cert R idx)
  = amf_sample (ab_f (published_at psl211_row_alldecks_tableau)) R idx
  /\ ExactIndependence (ipc_witness (psl211_word_proximity_cert R idx))
     = ab_port (published_at psl211_row_alldecks_tableau) R idx.
Proof. exact: psl211_word_proximity_cert_idealE. Qed.

Lemma f_psl211_word_proximity_cert_secretE (R : realType) (idx : unit) :
  ipc_secret (psl211_word_proximity_cert R idx) = psl211_alldecks_secret R
  /\ ew_secret (ipc_witness (psl211_word_proximity_cert R idx))
     = psl211_alldecks_secret R.
Proof. exact: psl211_word_proximity_cert_secretE. Qed.

Lemma f_psl211_word_proximity_cert_secretTE (R : realType) (idx : unit) :
  ew_secretT (ipc_witness (psl211_word_proximity_cert R idx)) = bool.
Proof. exact: psl211_word_proximity_cert_secretTE. Qed.

(******************************************************************************)
(*     The number the row publishes                                           *)
(******************************************************************************)

Lemma f_psl211_word_proximity_cert_epsE (R : realType) (idx : unit) :
  ipc_eps (psl211_word_proximity_cert R idx) = 2%:R^-40 :> R.
Proof. exact: psl211_word_proximity_cert_epsE. Qed.

Fact f_psl211_pow2_40_ge1 (R : realType) : (1:R) <= 2%:R^+40.
Proof. exact: psl211_pow2_40_ge1. Qed.

Fact f_psl211_pow2_40_gt0 (R : realType) : (0:R) < 2%:R^+40.
Proof. exact: psl211_pow2_40_gt0. Qed.

Lemma f_psl211_word_law_le2 (R : realType) :
  var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2%:R.
Proof. exact: psl211_word_law_le2. Qed.

Lemma f_psl211_word_proximity_cert_eps_lt2 (R : realType) (idx : unit) :
  ipc_eps (psl211_word_proximity_cert R idx) < 2%:R :> R.
Proof. exact: psl211_word_proximity_cert_eps_lt2. Qed.

(******************************************************************************)
(*     The arm, and what the row states                                       *)
(******************************************************************************)

(* PublishedRow and not PublishedRowAt c: this row carries no conclude
   coordinate, so the number it publishes is the certificate's own 2^-40 and
   not an upper bound restated at a constant. *)
Check (psl211_row_word_proximity : PublishedRow).

Lemma f_psl211_row_word_proximity_armE (R : realType)
    (idx : amf_index (ab_f (published_at psl211_row_word_proximity)) R) :
  security_arm_of psl211_row_word_proximity R idx = IdealProximityArm.
Proof. exact: psl211_row_word_proximity_armE. Qed.

Theorem f_psl211_word_view_proximity (R : realType) (C : {set seatT})
    (HC : (#|C| <= 5)%N) :
  var_dist
    (fdistmap (fun u => (@sa_coalition_view R (instance_profile psl211_algebra)
                           (instance_exec psl211_alldecks_params)
                           (amf_sample psl211_word_family R tt) 0 C u,
                         psl211_alldecks_secret R u))
       (sa_sampleP (amf_sample psl211_word_family R tt)))
    ((fdistmap (@sa_coalition_view R (instance_profile psl211_algebra)
                  (instance_exec psl211_alldecks_params)
                  (psl211_alldecks_sample R) 0 C) (psl211_alldecksP R))
     `x (fdistmap (psl211_alldecks_secret R) (psl211_alldecksP R)))
  <= 2%:R^-40.
Proof. exact: psl211_word_view_proximity. Qed.

(* The three recorded Fail guards of psl211_word_proximity.v declare nothing,
   so there is no statement to ascribe here.  Their fidelity is verify.py's
   token comparison against p6_mutations.v and the un-Fail'ed scratch
   compiles STATUS.md records. *)

(******************************************************************************)
(*     Assumptions                                                            *)
(******************************************************************************)

(* psl211_word_model.v *)
Print Assumptions psl211_word_cutP.
Print Assumptions psl211_wordP.
Print Assumptions psl211_word_sample.
Print Assumptions psl211_word_sampleP_E.
Print Assumptions psl211_word_cut_distE.
Print Assumptions psl211_word_family.
Print Assumptions psl211_word_law_le40.

(* psl211_analysis.v *)
Print Assumptions PSL211Analysis.word_sample.
Print Assumptions PSL211Analysis.word_family.

(* pgg_analysis_manifest.v *)
Print Assumptions psl211_row_word.

(* psl211_word_proximity.v *)
Print Assumptions psl211_word_proximity_close.
Print Assumptions psl211_word_proximity_cert.
Print Assumptions psl211_word_proximity_cert_idealE.
Print Assumptions psl211_word_proximity_cert_secretE.
Print Assumptions psl211_word_proximity_cert_secretTE.
Print Assumptions psl211_word_proximity_cert_epsE.
Print Assumptions psl211_pow2_40_ge1.
Print Assumptions psl211_pow2_40_gt0.
Print Assumptions psl211_word_law_le2.
Print Assumptions psl211_word_proximity_cert_eps_lt2.
Print Assumptions psl211_row_word_proximity.
Print Assumptions psl211_row_word_proximity_armE.
Print Assumptions psl211_row_word_proximity_rowE.
Print Assumptions psl211_word_view_proximity.
