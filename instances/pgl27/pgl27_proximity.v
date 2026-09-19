(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_proximity: the eight-card orbit instance at the proximity arm        *)
(*                                                                            *)
(* The eight-card orbit instance runs one execution under two laws of the     *)
(* cut: the exact shuffle, which draws it uniformly from PGL(2,7), and the    *)
(* two-hundred-letter word walk, which draws it by evaluating a sampled       *)
(* generator word. A proximity certificate compares two models at one index,  *)
(* so the two have to be read at one law of the dealt secret.                 *)
(* pgl27_prior_exact_family of pgl27_models.v carries that law as its index,  *)
(* where pgl27_exact_family is indexed by the unit type and its one member    *)
(* fixes the uniform secret. An ideal taken from the unit-indexed family can  *)
(* therefore only be the ideal of a word model at the uniform prior, and the  *)
(* distance of a word model at another prior to it is at least the distance   *)
(* between the two laws of the secret, which                                  *)
(* pgl27_word_uniform_ideal_close_false exhibits at a point mass.             *)
(*                                                                            *)
(* The ideal's own privacy is a theorem and not an assumption.                *)
(* pgl27_row_prior_exact_tableau publishes the exact execution through the    *)
(* exact arm at every law of the dealt secret, and                            *)
(* pgl27_word_proximity_cert_idealE says that the model the proximity         *)
(* certificate calls ideal is the model that row publishes, and that the      *)
(* port built from its witness is the row's own port.                         *)
(*                                                                            *)
(* Both certificates over the word model are built from one number, the       *)
(* walk's single-card marginal number 2^-40 of pgl27_word_marginal_bound,     *)
(* which rests on pgl27_word_mixing, the bound by that same number on the     *)
(* distance between the word walk and the uniform cut on the group. The       *)
(* proximity certificate carries that number and the                          *)
(* input-indistinguishability certificate carries it added to itself, which   *)
(* pgl27_word_proximity_eps_halfE states. The proximity row concludes at      *)
(* 2^-39, the constant pgl27_row_word_branch39 publishes for the other arm,   *)
(* so the two rows over this model conclude at one constant and the           *)
(* terminal's obligation is met strictly. Each of these numbers bounds a sum  *)
(* of absolute differences, twice the total variation distance, so a          *)
(* distinguisher's advantage against the published row is at most 2^-40.      *)
(*                                                                            *)
(* What the row claims is an average over the run argument under the law of   *)
(* the secret: both sides are pushforwards of whole sample laws and neither   *)
(* is a statement about one dealt arrangement. At the fixed deck pair         *)
(* orbit_encode and at four seats the reading does depend on the dealt        *)
(* secret: pgl27_view_dep_k4 exhibits a four-seat coalition whose reading is  *)
(* not independent of the orbit secret under the uniform prior, and           *)
(* pgl27_view_leak_k4 gives that coalition strictly positive mutual           *)
(* information with it.                                                       *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_prior_exact_witness == the exact arm's witness at the              *)
(*                                prior-indexed exact shuffle                 *)
(*   pgl27_row_prior_exact_tableau                                            *)
(*                             == that shuffle published as its own program   *)
(*   pgl27_word_secret         == the dealt secret on the word sample space   *)
(*   pgl27_word_proximity_cert == the word model's proximity certificate      *)
(*   pgl27_row_word_proximity  == the proximity claim, concluded at 2^-39     *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_prior_viewE         == the framework's reading of a coalition at   *)
(*                                the prior-indexed exact shuffle is the      *)
(*                                instance's own reading pgl27_view           *)
(*   pgl27_row_prior_exact_armE                                               *)
(*                             == the ideal row carries the exact arm         *)
(*   pgl27_row_prior_exact_rowE                                               *)
(*                             == the ideal program publishes                 *)
(*                                pgl27_row_prior_exact                       *)
(*   pgl27_word_proximity_close                                               *)
(*                             == below the four-seat threshold, the two      *)
(*                                models' joint laws of reading and secret    *)
(*                                are within 2^-40                            *)
(*   pgl27_word_proximity_cert_idealE                                         *)
(*                             == the certificate's ideal is the ideal row's  *)
(*                                model, and the port built from its witness  *)
(*                                is that row's port                          *)
(*   pgl27_word_proximity_cert_epsE                                           *)
(*                             == the certificate's number is 2^-40           *)
(*   pgl27_word_proximity_eps_halfE                                           *)
(*                             == the input-indistinguishability              *)
(*                                certificate's number is twice the proximity *)
(*                                certificate's                               *)
(*   pgl27_pow2_40_ge1         == two to the fortieth is at least one         *)
(*   pgl27_pow2_40_gt0         == two to the fortieth is positive             *)
(*   pgl27_word_proximity_le39 == the certificate's number is at most 2^-39   *)
(*   pgl27_word_proximity_cert_eps_lt2                                        *)
(*                             == that number is below the bound two          *)
(*                                var_dist_le2 gives                          *)
(*   pgl27_row_word_proximity_rowE                                            *)
(*                             == the proximity row publishes pgl27_row_word  *)
(*   pgl27_row_word_proximity_armE                                            *)
(*                             == that row carries the proximity arm          *)
(*   pgl27_row_word_families_sampledE                                         *)
(*                             == both rows over the word model read their    *)
(*                                model family off the one named Sampled      *)
(*                                value                                       *)
(*   pgl27_row_word_obs_sampledE                                              *)
(*                             == both rows read their observed execution     *)
(*                                off that same value                         *)
(*   pgl27_row_word_arm_neq    == the two rows carry different arms           *)
(*   pgl27_word_view_proximity == the proximity row's security statement, at  *)
(*                                2^-39                                       *)
(*   pgl27_word_uniform_ideal_close_false                                     *)
(*                             == the distance field is false at every        *)
(*                                coalition, with the uniform-secret exact    *)
(*                                model as the ideal of the word model at a   *)
(*                                point-mass prior                            *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import pgl27_rows.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     The ideal: the exact shuffle at every prior                            *)
(******************************************************************************)

(** The framework's static reading of a coalition at this model is the
    instance's own reading pgl27_view, with the secret left inside the sample
    point. Every security statement of a row is made about the left-hand side
    and every theorem of the instance about the right, so this equation is
    the whole of what carries one to the other at the prior-indexed model. *)
Lemma pgl27_prior_viewE (R : realType) (secretP : R.-fdist bool)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  (fun u => @static_coalition_obs pgl27_algebra pgl27_dealt_params C
              ((amf_sample pgl27_prior_exact_family R secretP).(sa_arg) u)
              ((amf_sample pgl27_prior_exact_family R secretP).(sa_cut) u))
  = pgl27_view R C.
Proof. by apply: boolp.funext; case=> s g; exact: pgl27_static_obsE. Qed.

(** The exact arm's witness at every prior: the dealt secret as a random
    variable on this sample space, and, at every coalition of fewer than four
    seats, the independence of that coalition's reading from it. The
    independence is pgl27_view_indep_gen, three-transitivity of PGL(2,7) read
    as a privacy statement, which holds whatever the law of the secret is. The
    reading carries no information about the secret at all and not a small
    amount, so this model is an execution a proximity certificate may call
    ideal. *)
Definition pgl27_prior_exact_witness (R : realType) (secretP : R.-fdist bool)
  : ExactWitness (amf_sample pgl27_prior_exact_family R secretP) :=
  @MkExactWitness R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_prior_exact_family R secretP) bool (pgl27_secret R)
    (fun C HC =>
       let H3 : (#|C| <= 3)%N := HC in
       (eq_ind_r
          (fun v => pgl27P_gen secretP |= v _|_ pgl27_secret R)
          (pgl27_view_indep_gen secretP H3)
          (pgl27_prior_viewE secretP C))).

(** The prior-indexed exact shuffle, from the observed prefix the two existing
    PGL(2,7) rows share, certified by the exact arm and published. Its
    transfer status is StaticExecutedOnly, because this model draws the
    uniform cut itself and no idealized shuffle is being compared with a real
    one; what the row carries about a coalition of fewer than four seats is
    independence of the dealt secret, at every real field and every prior,
    with no numeric bound anywhere in it. *)
Definition pgl27_row_prior_exact_tableau : PublishedRow :=
  pgl27_dealt
    sample  pgl27_prior_exact_family
    certify ExactIndependence pgl27_prior_exact_witness
    |> publish StaticExecutedOnly BaselineClassicalOnly.

(** The arm the ideal row carries, at every real field and prior:
    independence of the dealt secret, and not a distance to some other
    model. *)
Lemma pgl27_row_prior_exact_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_prior_exact_tableau)) R) :
  security_arm_of pgl27_row_prior_exact_tableau R idx = ExactIndependenceArm.
Proof. by []. Qed.

(** The manifest's typed row for the eight-card orbit instance at the
    prior-indexed exact shuffle is the row this program publishes. Its five
    coordinates are the observed execution the program runs on, the
    completion level the publish terminal reaches, the model family the
    sample step named, and the two statuses the terminal was given. The
    manifest writes those coordinates in the facade's vocabulary and the
    program in this file's, and conversion decides the equation, so the
    manifest's row for this path is a claim this equation discharges rather
    than a table maintained beside the program. *)
Lemma pgl27_row_prior_exact_rowE :
  published_row pgl27_row_prior_exact_tableau = pgl27_row_prior_exact.
Proof. exact: erefl. Qed.

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
    deterministic function of the pair of the secret and the cut. The premise
    is the arm's threshold at this instance, four seats. pgl27_word_mixing,
    the bound on the cut group's own distance, carries no coalition premise,
    so the same bound is reachable at every coalition by a route this proof
    does not take. *)
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
   product of its marginals by the ideal witness's own independence. The
   threshold is used twice, once for the ideal witness's independence and
   once for pgl27_view_mixing. *)
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
    quantity is that number: the ideal and its witness are the terms the ideal
    row already publishes, and the secret is the word model's own first
    projection, typed at the carrier that witness names. *)
Definition pgl27_word_proximity_cert (R : realType) (secretP : R.-fdist bool)
  : IdealProximityCert (amf_sample pgl27_word_family R secretP) :=
  @MkIdealProximityCert R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP)
    (amf_sample pgl27_prior_exact_family R secretP)
    (pgl27_prior_exact_witness secretP)
    (pgl27_word_secret secretP)
    (sw_bound_eps (pgl27_word_marginal_bound R))
    (fun C HC => pgl27_word_proximity_close secretP HC).

(** The model the certificate calls ideal is the model the published ideal
    row carries, and the port built from the certificate's witness is that
    row's port. Conversion decides both, so the ideal a word row is measured
    against is the model pgl27_row_prior_exact_tableau publishes and not a
    second description of it. *)
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

(** The certificate's number is the two-hundred-letter walk's marginal
    number, 2^-40. *)
Lemma pgl27_word_proximity_cert_epsE (R : realType) (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP) = 2%:R^-40 :> R.
Proof. exact: erefl. Qed.

(** The number pgl27_word_cert carries at this model is twice the number
    pgl27_word_proximity_cert carries. Both are read off pgl27_word_mixing,
    the one bound on the cut group's distance; the input-indistinguishability
    arm spends it once for each of the two dealt secrets it compares and the
    proximity arm compares one law with one law. The relation is between
    these two certificates and not between the two arms: cert_eps is by
    definition the walk's marginal number added to itself, and this proximity
    certificate chooses that same marginal number as its own field, which a
    proximity certificate over the same model and the same ideal is free not
    to do. *)
Lemma pgl27_word_proximity_eps_halfE (R : realType) (secretP : R.-fdist bool) :
  cert_eps (pgl27_word_cert secretP)
  = ipc_eps (pgl27_word_proximity_cert secretP)
    + ipc_eps (pgl27_word_proximity_cert secretP).
Proof. by []. Qed.

(** Two to the fortieth is at least one, at every real field.                 *)
Fact pgl27_pow2_40_ge1 (R : realType) : (1:R) <= 2%:R^+40.
Proof. by apply: exprn_ege1; rewrite ler1n. Qed.

(** Two to the fortieth is positive, at every real field.                     *)
Fact pgl27_pow2_40_gt0 (R : realType) : (0:R) < 2%:R^+40.
Proof. by rewrite exprn_gt0 // ltr0n. Qed.

(** The certificate's number is at most 2^-39, the constant the word row
    publishes for the input-indistinguishability arm. It is the obligation of
    the terminal that concludes the proximity row at that constant, and the
    obligation is met strictly, the certificate's number being half of the
    published one. *)
Lemma pgl27_word_proximity_le39 (R : realType) (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP) <= 2%:R^-39 :> R.
Proof.
have H0 : (0:R) < 2%:R^-40 by rewrite invr_gt0 pgl27_pow2_40_gt0.
have He := pow2_split R.
rewrite pgl27_word_proximity_cert_epsE; lra.
Qed.

(** The certificate's own number is below two, the bound var_dist_le2 gives
    for a variation distance, so the certificate is not vacuous. At about
    4.5e-13 of that bound it is a cryptographic separation, where the
    proximity certificate of Kim's one-cut model at one percent of the same
    bound is a weak one. *)
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
    constant the input-indistinguishability row of the same model publishes and
    the one the published reading statement pgl27_word_view_proximity carries.
    The certificate's own number is 2^-40, half of that. Below four seats its
    distance field, pgl27_word_proximity_close, puts the joint law of a
    coalition's reading with the dealt secret within that number of the same
    joint law under the prior-indexed exact execution, where the reading and
    the secret are independent outright, so the ideal side is the product of
    its two marginals. The number is spent once, against the
    input-indistinguishability certificate's twice. Its transfer status is
    IdealFinite, the same the input-indistinguishability row carries, and the
    two certificates compare against the same ideal cut. *)
Definition pgl27_row_word_proximity : PublishedRowAt pgl27_reprice39 :=
  pgl27_word_sampled
    certify IdealProximity pgl27_word_proximity_cert
    |> conclude pgl27_reprice39 by (fun R idx => pgl27_word_proximity_le39 idx)
    |> publish IdealFinite BaselineClassicalOnly.

(** The proximity row publishes the manifest's row for the word path, as
    pgl27_row_word_rowE of pgl27_rows.v says of the word program. An
    AnalysisPathRow holds descriptive metadata and no Prop, so one manifest
    row carrying an input-indistinguishability row and a proximity row says
    nothing about either claim. *)
Lemma pgl27_row_word_proximity_rowE :
  published_row pgl27_row_word_proximity = pgl27_row_word.
Proof.
(* exact: erefl and not by []: done does not return on an equation between
   two rows' coordinates. *)
exact: erefl.
Qed.

(** The arm the proximity row carries, at every real field and prior: the
    distance to a private ideal model, and not the distance between two
    readings of one model. *)
Lemma pgl27_row_word_proximity_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_word_proximity)) R) :
  security_arm_of pgl27_row_word_proximity R idx = IdealProximityArm.
Proof. by []. Qed.

(** Both rows over the word model read their analysis model family off the one
    named Tableau Sampled value, so the pair differs in the arm and in nothing
    about the algebra, the run or the law. The family is what a continuation
    of a named value reads off the name. *)
Lemma pgl27_row_word_families_sampledE :
  ab_f (published_at pgl27_row_word_proximity)
  = sp_f (tableau_at pgl27_word_sampled)
  /\ ab_f (published_at pgl27_row_word_branch39)
     = sp_f (tableau_at pgl27_word_sampled).
Proof. split; exact: erefl. Qed.

(** Both rows read their observed execution off that same named value, so the
    two claims are made about one run and one static observation of it and
    not about two executions that happen to agree. Together with the family
    equation above, everything the two rows hold in common comes from the one
    name. *)
Lemma pgl27_row_word_obs_sampledE :
  ab_obs (published_at pgl27_row_word_proximity)
  = sp_obs (tableau_at pgl27_word_sampled)
  /\ ab_obs (published_at pgl27_row_word_branch39)
     = sp_obs (tableau_at pgl27_word_sampled).
Proof.
(* Each row stated against the named value closes by exact: erefl in under
   0.01 s. The row-against-row form is the expensive one, 96.0 s by
   exact: erefl and 48.1 s by reflexivity, and is not stated. *)
split; exact: erefl.
Qed.

(** The two rows over the one model carry different arms, so the pair is two
    statements about one probability model and not one statement published
    twice. *)
Lemma pgl27_row_word_arm_neq (R : realType) (secretP : R.-fdist bool) :
  security_arm_of pgl27_row_word_proximity R secretP
  <> security_arm_of pgl27_row_word_branch39 R secretP.
Proof.
(* Three costs are each why one line reads as it does. Binding the prior as
   an index of the proximity row costs 78.7 s in the statement alone,
   because the branch row's index type is then reached by conversion through
   both rows' observed executions, so it is bound at its own type. Rewriting
   with the two armE lemmas applied to that prior costs 24.3 s, and
   restating the two equations locally and rewriting with both in the
   inequation costs 24.1 s, because a rewrite scans the other side of the
   goal and so converts one row against the other. The equation between the
   arms is therefore assumed first, and each rewrite then runs on a goal that
   mentions one row. *)
have Hp : security_arm_of pgl27_row_word_proximity R secretP
  = IdealProximityArm by [].
have Hs : security_arm_of pgl27_row_word_branch39 R secretP
  = InputIndistinguishabilityArm by [].
move=> Harm; move: Hp; rewrite Harm Hs => Hf; discriminate Hf.
Qed.

(******************************************************************************)
(*     What the proximity row states at this instance                         *)
(******************************************************************************)

(** The proximity row's security statement at the eight-card orbit instance:
    at fewer than four colluding seats and at every prior on the dealt secret,
    the joint law of the executed coalition reading and that secret under the
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

(******************************************************************************)
(*     What a certificate may name as its ideal, and what refutes one         *)
(******************************************************************************)

(** The unit-indexed exact family cannot be read at the prior the word model
    carries. The index of an analysis model family is a type depending on the
    real field alone, and amf_sample asks for an inhabitant of it, so a
    distribution on the booleans is offered where the unit type is expected
    and the two sample adapters are never reached. The term written here is
    therefore refused before any distance is considered. The same family at
    its own index tt is a well-typed ideal for this actual model, and what
    refuses it there is the distance field, which the guard below records. *)
Fail Definition pgl27_word_proximity_cert_unit_ideal (R : realType)
    (secretP : R.-fdist bool)
  : IdealProximityCert (amf_sample pgl27_word_family R secretP) :=
  @MkIdealProximityCert R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP)
    (amf_sample pgl27_exact_family R secretP)
    (@pgl27_exact_witness R secretP)
    (pgl27_word_secret secretP)
    (sw_bound_eps (pgl27_word_marginal_bound R))
    (fun C HC => pgl27_word_proximity_close secretP HC).

Section pgl27_word_uniform_ideal.
Variable R : realType.

Let P1 : R.-fdist bool := fdist1 true.

(** The distance field of a proximity certificate is false, and not merely
    unwritable, when the ideal is the uniform-secret member of the tree's
    exact family and the actual model is the word walk at the point-mass
    prior. Pushing both joint laws forward along the secret coordinate leaves
    the two priors themselves, one apart, and 2^-40 is below that, so the two
    models are separated by their secrets alone and no reading of the cut can
    bring them together. It says nothing at a prior near the uniform one,
    where the same lower bound is small. It is stated at every coalition and
    not only below four seats, so it refutes more than the field asks. *)
Lemma pgl27_word_uniform_ideal_close_false
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  ~ (var_dist
       (fdistmap (fun u => (@static_coalition_obs pgl27_algebra
                              pgl27_dealt_params C
                              ((pgl27_word_sample P1).(sa_arg) u)
                              ((pgl27_word_sample P1).(sa_cut) u),
                            pgl27_word_secret P1 u))
          (sa_sampleP (pgl27_word_sample P1)))
       (fdistmap (fun u => (@static_coalition_obs pgl27_algebra
                              pgl27_dealt_params C
                              ((pgl27_sample R).(sa_arg) u)
                              ((pgl27_sample R).(sa_cut) u),
                            pgl27_secret R u))
          (sa_sampleP (pgl27_sample R)))
     <= 2%:R^-40).
Proof.
move=> Hle.
have Hdp := var_dist_fdistmap (@snd _ _)
  (fdistmap (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params C
                         ((pgl27_word_sample P1).(sa_arg) u)
                         ((pgl27_word_sample P1).(sa_cut) u),
                       pgl27_word_secret P1 u))
     (sa_sampleP (pgl27_word_sample P1)))
  (fdistmap (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params C
                         ((pgl27_sample R).(sa_arg) u)
                         ((pgl27_sample R).(sa_cut) u),
                       pgl27_secret R u))
     (sa_sampleP (pgl27_sample R))).
rewrite !fdistmap_comp in Hdp.
have Hw : fdistmap ((@snd _ _) \o
            (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params C
                         ((pgl27_word_sample P1).(sa_arg) u)
                         ((pgl27_word_sample P1).(sa_cut) u),
                       pgl27_word_secret P1 u)))
            (sa_sampleP (pgl27_word_sample P1))
          = P1.
  exact: fdist_prod1.
have Hi : fdistmap ((@snd _ _) \o
            (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params C
                         ((pgl27_sample R).(sa_arg) u)
                         ((pgl27_sample R).(sa_cut) u),
                       pgl27_secret R u)))
            (sa_sampleP (pgl27_sample R))
          = fdist_uniform (R := R) card_bool.
  exact: fdist_prod1.
rewrite Hw Hi var_dist_fdist1_uniform in Hdp.
have Hge : (1:R) <= 2%:R^+39 by apply: exprn_ege1; rewrite ler1n.
have Hpos : (0:R) < 2%:R^+40 by rewrite exprn_gt0 // ltr0n.
have Hgt1 : (1:R) < 2%:R^+40 by rewrite exprS; lra.
have Hlt : (2%:R : R)^-40 < 1 by rewrite invf_lt1.
lra.
Qed.

End pgl27_word_uniform_ideal.

(** The one member of the unit-indexed exact family fixes the uniform secret,
    and it is a well-typed ideal for a word model at any prior: the index is
    supplied as tt and both adapters live over the same execution. What the
    kernel rejects is the distance field, whose proof is stated between the
    word model at secretP and the exact model at secretP and not between the
    word model at secretP and the exact model at the uniform prior. The Fail
    rejects the one term written here, on that mismatch of types, and rules
    out no other term. What refutes the field itself is
    pgl27_word_uniform_ideal_close_false above, at the point-mass prior, where
    the two secret marginals are one apart and 2^-40 is not; at a prior near
    the uniform one that lower bound is small and nothing is claimed. *)
Fail Definition pgl27_word_proximity_cert_uniform_ideal (R : realType)
    (secretP : R.-fdist bool)
  : IdealProximityCert (amf_sample pgl27_word_family R secretP) :=
  @MkIdealProximityCert R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP)
    (amf_sample pgl27_exact_family R tt)
    (@pgl27_exact_witness R tt)
    (pgl27_word_secret secretP)
    (sw_bound_eps (pgl27_word_marginal_bound R))
    (fun C HC => pgl27_word_proximity_close secretP HC).

(** The word model's proximity certificate does not continue the exact model's
    branch point. The payload type is IdealProximityPayload at the model family
    the Sampled value names, so the clause is checked first against that
    family's index type, unit against a distribution on the booleans. The Fail
    rejects the one term written here, on that mismatch of index types, and
    rules out no other term. The index types separate pgl27_exact_family from
    pgl27_word_family. The certificate this file builds,
    pgl27_word_proximity_cert, reads its two models at one index, the member of
    pgl27_prior_exact_family at secretP and the member of pgl27_word_family at
    that same secretP. *)
Fail Definition pgl27_cross_model_proximity : Tableau AnalysisBridged :=
  pgl27_dealt sample pgl27_exact_family
    certify IdealProximity pgl27_word_proximity_cert.
