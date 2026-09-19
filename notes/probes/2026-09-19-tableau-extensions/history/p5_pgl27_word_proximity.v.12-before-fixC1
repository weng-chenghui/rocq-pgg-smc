(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P5, second half: the PGL(2,7) word row through the proximity arm     *)
(*                                                                            *)
(* The two-hundred-letter word model and the prior-indexed exact shuffle of   *)
(* p5_pgl27_prior_ideal.v run one execution at one prior and differ in the    *)
(* law of the cut alone. That is the shape the proximity arm compares, and    *)
(* the eight-card orbit instance is its second carrier after Kim's one-cut    *)
(* five-card model. The ideal is an execution whose own privacy is a theorem: *)
(* pgl27_row_prior_exact_tableau publishes it with the exact arm, and         *)
(* pgl27_word_proximity_cert_idealE says that the model the certificate calls *)
(* ideal and the model that row publishes are one term.                       *)
(*                                                                            *)
(* One named Tableau Sampled value, pgl27_word_sampled of                     *)
(* t0_sampled_branch_pgl27.v, carries both claims about the word model: the   *)
(* spectral one, which pgl27_row_word_branch39 already publishes, and the     *)
(* proximity one below. The two are two rows over one model, and              *)
(* pgl27_row_word_arms_sampledE says that both read their model family off    *)
(* that one name.                                                             *)
(*                                                                            *)
(* Both numbers come from one distance, pgl27_word_mixing on the cut group.   *)
(* The spectral arm spends it once for each of the two dealt secrets it       *)
(* compares and the proximity arm spends it once, so the proximity number is  *)
(* half the spectral one at this model. The row is concluded at 2^-39, the    *)
(* number pgl27_row_word39 publishes for the spectral arm, so the two rows    *)
(* are read in one column.                                                    *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_word_secret         == the dealt secret on the word sample space   *)
(*   pgl27_word_proximity_cert == the word model's proximity certificate      *)
(*   pgl27_row_word_proximity  == the proximity claim, published at 2^-39     *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_word_proximity_close                                               *)
(*                             == the two models' joint laws of reading and   *)
(*                                secret are within 2^-40                     *)
(*   pgl27_word_proximity_cert_idealE                                         *)
(*                             == the certificate's ideal is the ideal row    *)
(*   pgl27_word_proximity_eps_halfE                                           *)
(*                             == the spectral number is twice this one       *)
(*   pgl27_word_view_proximity == what the row states at this instance        *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.
From tableau_ext_probe Require Import pgl27_rows t0_sampled_branch_pgl27.
From tableau_ext_probe Require Import p5_pgl27_prior_ideal.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     The distance between the two models' joint laws                        *)
(******************************************************************************)

(** The dealt secret as a random variable on the word sample space. The word
    space is the pair of the secret and the sampled generator word, so the
    secret is its first projection, and it is typed at the carrier the ideal's
    witness names so that the two models speak of one secret. *)
Definition pgl27_word_secret (R : realType) (secretP : R.-fdist bool)
  : {RV (sa_sampleP (pgl27_word_sample secretP)) -> bool} := fun u => u.1.
Arguments pgl27_word_secret [R] secretP.

(** At every coalition of fewer than four seats and at every prior, the joint
    law of that coalition's reading with the dealt secret under the
    two-hundred-letter word walk is within 2^-40 of the same joint law under
    the uniform cut at the same prior. It is the certificate field of the
    proximity arm at this instance: the two models differ in the law of the
    cut alone, the secret is drawn from the same prior and independently of
    the cut in both, and the pair of a reading and the secret is a
    deterministic function of the pair of the secret and the cut. The bound
    holds at every coalition and not only below the threshold; the threshold
    enters the arm's proposition and not this distance. *)
Lemma pgl27_word_proximity_close (R : realType) (secretP : R.-fdist bool)
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
Proof.
(* The word side is rewritten as a reading of the pair of the secret and the
   evaluated cut, which is the carrier pgl27_view_mixing is stated on; the
   ideal side is that same reading under the uniform cut, turned into the
   product of its marginals by the ideal witness's own independence. *)
move=> HC.
have H3 : (#|C| <= 3)%N := HC.
have Hact :
  (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params C
               ((pgl27_word_sample secretP).(sa_arg) u)
               ((pgl27_word_sample secretP).(sa_cut) u),
             pgl27_word_secret secretP u))
  = [% pgl27_view R C, pgl27_secret R]
      \o (fun u => ((pgl27_word_sample secretP).(sa_arg) u,
                    (pgl27_word_sample secretP).(sa_cut) u)).
  by apply: boolp.funext => u /=; rewrite (pgl27_static_obsE R).
rewrite Hact -fdistmap_comp.
rewrite -/(sa_joint_dist (sa_arg (s := pgl27_word_sample secretP))).
rewrite pgl27_word_sample_joint_distE.
have Hid :
  (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params C
               ((pgl27_prior_sample secretP).(sa_arg) u)
               ((pgl27_prior_sample secretP).(sa_cut) u),
             pgl27_secret R u))
  = [% pgl27_view R C, pgl27_secret R].
  by apply: boolp.funext; case=> s g; rewrite /= (pgl27_static_obsE R).
rewrite Hid.
have Hprod :
  fdistmap [% pgl27_view R C, pgl27_secret R]
    (sa_sampleP (pgl27_prior_sample secretP))
  = (fdistmap (pgl27_view R C) (pgl27P_gen secretP))
    `x (fdistmap (pgl27_secret R) (pgl27P_gen secretP)).
  exact: (inde_dist_of_RV2 (pgl27_view_indep_gen secretP H3)).
rewrite Hprod.
exact: (pgl27_view_mixing secretP H3).
Qed.

(******************************************************************************)
(*     The certificate, and its ideal                                         *)
(******************************************************************************)

(** The proximity certificate of the PGL(2,7) word row at every prior. Its
    five fields are the prior-indexed exact shuffle as the ideal; that model's
    exact witness, which is what makes the ideal an execution whose coalitions
    below four seats learn nothing at all; the dealt secret of the word model;
    the walk's marginal number 2^-40; and the distance above. The only inexact
    quantity is that number: the ideal, its witness and the secret are the
    terms the ideal row already publishes. *)
Definition pgl27_word_proximity_cert (R : realType) (secretP : R.-fdist bool)
  : IdealProximityCert (amf_sample pgl27_word_family R secretP) :=
  @MkIdealProximityCert R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP)
    (amf_sample pgl27_prior_exact_family R secretP)
    (pgl27_prior_exact_witness secretP)
    (pgl27_word_secret secretP)
    (sw_bound_eps (pgl27_word_marginal_bound R))
    (fun C HC => pgl27_word_proximity_close secretP HC).

(** The model the certificate calls ideal, and the witness it carries for it,
    are the model and the witness of the published ideal row. Conversion
    decides both, so the ideal a word row is measured against is the row
    p5_pgl27_prior_ideal.v publishes and not a second description of it. *)
Lemma pgl27_word_proximity_cert_idealE (R : realType)
    (secretP : R.-fdist bool) :
  ipc_ideal (pgl27_word_proximity_cert secretP)
  = amf_sample (ab_f (published_at pgl27_row_prior_exact_tableau)) R secretP
  /\ ExactIndependence (ipc_witness (pgl27_word_proximity_cert secretP))
     = ab_port (published_at pgl27_row_prior_exact_tableau) R secretP.
Proof. by split. Qed.

(******************************************************************************)
(*     The number                                                             *)
(******************************************************************************)

(** The certificate's number in closed form: the two-hundred-letter walk's
    marginal number, 2^-40. *)
Lemma pgl27_word_proximity_cert_epsE (R : realType) (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP) = 2%:R^-40 :> R.
Proof. exact: erefl. Qed.

(** The spectral arm's number at this model is twice the proximity arm's. Both
    are read off pgl27_word_mixing, the one distance on the cut group; the
    spectral arm spends it once for each of the two dealt secrets it compares
    and the proximity arm compares one law with one law. *)
Lemma pgl27_word_proximity_eps_halfE (R : realType) (secretP : R.-fdist bool) :
  cert_eps (pgl27_word_cert secretP)
  = ipc_eps (pgl27_word_proximity_cert secretP)
    + ipc_eps (pgl27_word_proximity_cert secretP).
Proof. by []. Qed.

(** Two to the fortieth is at least one, at every real field. *)
Fact pgl27_pow2_40_ge1 (R : realType) : (1:R) <= 2%:R^+40.
Proof. by apply: exprn_ege1; rewrite ler1n. Qed.

(** Two to the fortieth is positive, at every real field. *)
Fact pgl27_pow2_40_gt0 (R : realType) : (0:R) < 2%:R^+40.
Proof. by rewrite exprn_gt0 // ltr0n. Qed.

(** The certificate's number is under 2^-39, the constant the word row
    publishes for the spectral arm. It is the obligation of the terminal that
    concludes the proximity row at that constant. *)
Lemma pgl27_word_proximity_le39 (R : realType) (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP) <= 2%:R^-39 :> R.
Proof.
have H0 : (0:R) < 2%:R^-40 by rewrite invr_gt0 pgl27_pow2_40_gt0.
have He := pow2_split R.
rewrite pgl27_word_proximity_cert_epsE; lra.
Qed.

(** The certificate's own number is under two, the ceiling var_dist_le2 gives
    for a variation distance, so the certificate is not vacuous. At about
    4.5e-13 of the ceiling it is a cryptographic separation and not a weak
    one, as the proximity certificate of Kim's one-cut model is. *)
Lemma pgl27_word_proximity_cert_eps_lt2 (R : realType)
    (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP) < 2%:R :> R.
Proof.
have H1 : 2%:R^-40 <= (1:R)
  by rewrite invf_le1 ?pgl27_pow2_40_gt0 ?pgl27_pow2_40_ge1.
rewrite pgl27_word_proximity_cert_epsE; lra.
Qed.

(******************************************************************************)
(*     One model, two claims, two rows                                        *)
(******************************************************************************)

(** The word model certified by the proximity arm and concluded at 2^-39, the
    constant the spectral row of the same model publishes. What a coalition of
    fewer than four seats is shown is that the joint law of its reading with
    the dealt secret is within that number of the product of the two marginals
    the prior-indexed exact execution has, where the reading and the secret
    are independent outright. The number is spent once, against the spectral
    row's twice, and the transfer status is the one the spectral row earns,
    since the same ideal cut is what both certificates compare against. *)
Definition pgl27_row_word_proximity : PublishedRowAt pgl27_reprice39 :=
  pgl27_word_sampled
    certify IdealProximity pgl27_word_proximity_cert
    |> conclude pgl27_reprice39 by (fun R idx => pgl27_word_proximity_le39 idx)
    |> publish IdealFinite BaselineClassicalOnly.

(* exact: erefl and not by [], following the hang shape recorded in STATUS.md:
   done does not return on an equation between two rows' coordinates. *)

(** The proximity row publishes the manifest's row for the word path, as its
    spectral sibling does. An AnalysisPathRow holds descriptive metadata and
    no Prop, so one manifest row carrying a spectral row and a proximity row
    says nothing about either claim. *)
Lemma pgl27_row_word_proximity_rowE :
  published_row pgl27_row_word_proximity = pgl27_row_word.
Proof. exact: erefl. Qed.

(** The arm the proximity row carries, at every real field and prior: the
    distance to a private ideal model, and not the distance between two
    readings of one model. This is the value a paper's table prints in the arm
    column for this row. *)
Lemma pgl27_row_word_proximity_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_word_proximity)) R) :
  security_arm_of pgl27_row_word_proximity R idx = IdealProximityArm.
Proof. by []. Qed.

(** The arm the spectral continuation of the same named value carries. *)
Lemma pgl27_row_word_branch39_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_word_branch39)) R) :
  security_arm_of pgl27_row_word_branch39 R idx = SpectralDecayArm.
Proof. by []. Qed.

(** Both rows over the word model read their analysis model family off the one
    named Tableau Sampled value, so the pair differs in the arm and in nothing
    about the algebra, the run or the law. The statement is on the family and
    not on the whole observed execution: an equation between the two rows'
    observed executions is decided by conversion in 48 seconds, against four
    milliseconds for the family, and the family is what a continuation reads
    off the name. *)
Lemma pgl27_row_word_arms_sampledE :
  ab_f (published_at pgl27_row_word_proximity)
  = sp_f (tableau_at pgl27_word_sampled)
  /\ ab_f (published_at pgl27_row_word_branch39)
     = sp_f (tableau_at pgl27_word_sampled).
Proof. split; exact: erefl. Qed.

(** The two rows over the one model carry different arms, so the pair is two
    statements about one probability model and not one statement published
    twice. *)
Lemma pgl27_row_word_arm_neq (R : realType) (secretP : R.-fdist bool) :
  security_arm_of pgl27_row_word_proximity R secretP
  <> security_arm_of pgl27_row_word_branch39 R secretP.
Proof.
(* Three costs were measured on 2026-09-19 and each is why one line reads as
   it does. Binding the prior as an index of the proximity row costs 78.7 s
   in the statement alone, because the branch row's index type is then
   reached by conversion through both rows' observed executions, so it is
   bound at its own type. Rewriting with the two armE lemmas applied to that
   prior costs 24.3 s, and restating the two equations locally and rewriting
   with both in the inequation costs 24.1 s, because a rewrite scans the
   other side of the goal and so converts one row against the other. The
   equation between the arms is therefore assumed first, and each rewrite
   then runs on a goal that mentions one row. *)
have Hp : security_arm_of pgl27_row_word_proximity R secretP
  = IdealProximityArm by [].
have Hs : security_arm_of pgl27_row_word_branch39 R secretP
  = SpectralDecayArm by [].
move=> Harm; move: Hp; rewrite Harm Hs => Hf; discriminate Hf.
Qed.

(******************************************************************************)
(*     What the proximity row states at this instance                         *)
(******************************************************************************)

(** The proximity row's security statement at the eight-card orbit instance:
    at fewer than four colluding seats and at every prior on the dealt secret,
    the joint law of the executed coalition view and that secret under the
    two-hundred-letter word walk is within 2^-39 of the product of the two
    marginals of the exact execution at the same prior. The proof is the row's
    security projection applied, so the row and this statement are one
    theorem. *)
Theorem pgl27_word_view_proximity (R : realType) (secretP : R.-fdist bool)
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
Proof.
exact: (view_proximity_of pgl27_row_word_proximity R secretP C HC).
Qed.
