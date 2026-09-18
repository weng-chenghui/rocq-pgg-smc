(* PROBE, notes/probes/2026-09-19-kim-spectral-arm/kim_spectral_rows_probe.v  *)
(* Ledger rows S6, S7 and S8 of                                               *)
(* notes/20260919-kim-spectral-arm-probe-design.md.                           *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import morphism.
From mathcomp Require Import boolp reals.
From mathcomp Require Import lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import perm_uniform pgg_interface pgg_collusion_bound.
From pgg_smc Require Import pgg_weighted_words.
From pgg_smc Require Import pgg_monodromy_profile.
From pgg_smc Require Import pgg_instance pgg_functionality pgg_sample_adapter.
From pgg_smc Require Import pgg_trace_secrecy.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_encoding den_boer_run den_boer_profile.
From pgg_smc Require Import five_card_leakage five_card_exec five_card_models.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import five_card_rows.
From pgg_reconstruct Require Import algebraic_rigidity.
From kim_spectral_arm_probe Require Import var_dist_injective_probe.
From kim_spectral_arm_probe Require Import five_card_rotation_probe.
From kim_spectral_arm_probe Require Import kim_sc_close_probe.
From kim_spectral_arm_probe Require Import five_card_sc_const_probe.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     The tying field, restated so this probe stands alone                   *)
(******************************************************************************)

(* The cut law the one-cut adapter draws from is the law the length-one
   bundle bounds. It is the tying field of the spectral certificate: without
   it the bundle's number would be a bound on some other shuffle than the
   one the row executes. *)
Definition kim_biased_sample_cut_witnessE (R : realType)
  : sw_rho_dist (kim_biased_marginal_bound R)
  = sa_cut_dist (amf_sample kim_biased_family R tt) :=
  ltac:(rewrite /kim_biased_marginal_bound /= rho_from_words_weighted1
                kim_single_cut_distE;
        congr fdistmap; apply: funext => k; exact: fc_kim_gensE).

(******************************************************************************)
(*     S6, form 1: the certificates at the bundles' own numbers               *)
(******************************************************************************)

(* The spectral certificate of the repeated row. Its five fields are the
   seven-cut bundle's marginal bound; the identification of that bound's law
   with the law the repeated adapter draws its cut from; the uniform rotation
   law as the ideal cut; the distance of the seven-cut law from that ideal;
   and the invariance of a coalition's reading of the ideal cut in the
   committed pair. The only inexact quantity in the row is the bundle's
   spectral number; the two fields about the ideal cut are exact. *)
Definition kim_centi_cert (R : realType) (idx : unit)
  : SpectralCert (amf_sample kim_centi_family R idx) :=
  @MkSpectralCert R five_card_algebra five_card_params
    (amf_sample kim_centi_family R idx)
    (scb_bound (kim_security_bundle_centi R))
    (esym (kim_centi_cut_distE R))
    (sa_cut_dist (five_card_sample R))
    (@kim_centi_cut_mixing R)
    (@five_card_static_obs_const R).

(* The spectral certificate of the one-cut row, with the same five fields at
   word length one. The ideal cut and the invariance of a coalition's
   reading of it are the same two terms as in the repeated row's
   certificate, so the two rows differ only in the shuffle and its number. *)
Definition kim_biased_cert (R : realType) (idx : unit)
  : SpectralCert (amf_sample kim_biased_family R idx) :=
  @MkSpectralCert R five_card_algebra five_card_params
    (amf_sample kim_biased_family R idx)
    (kim_biased_marginal_bound R)
    (kim_biased_sample_cut_witnessE R)
    (sa_cut_dist (five_card_sample R))
    (@kim_biased_cut_mixing R)
    (@five_card_static_obs_const R).

(******************************************************************************)
(*     S6, form 1: the two row programs                                       *)
(******************************************************************************)

(* Kim's repeated row certified by the spectral arm and published at
   IdealFinite. A certificate that compares a finite shuffle with a named
   ideal cut and discharges the base premise on the cut carrier is what
   pgg_analysis_status.v admits at that transfer status. *)
Definition five_card_row_repeated_spectral_tableau : PublishedRow :=
  five_card_committed
    sample kim_centi_family
    certify SpectralDecay kim_centi_cert
    |> publish IdealFinite BaselineClassicalOnly.

(* Kim's one-cut row certified by the same arm and published at the same
   transfer status. Its certificate has the shape the repeated row's has,
   over the same ideal cut and with the same invariance field, so the same
   status is the honest one for it. *)
Definition five_card_row_biased_ideal_tableau : PublishedRow :=
  five_card_committed
    sample kim_biased_family
    certify SpectralDecay kim_biased_cert
    |> publish IdealFinite BaselineClassicalOnly.

(******************************************************************************)
(*     S7, form 1: the numbers the rows carry                                 *)
(******************************************************************************)

(* Two copies of two to the minus fortieth make two to the minus
   thirty-ninth. A spectral certificate publishes its marginal bound twice,
   once for each of the two committed pairs, so a row at the constant bound
   publishes a sum of two equal terms, and this identity is what names that
   sum by a single constant. *)
(* The mulr_natl and mulr_natr routes fail here because the ring numeral 2
   is itself a natmul and the rewrite fires inside it, yielding
   (2 * 1) ^- 40. *)
Fact five_card_pow2_39_split (R : realType) :
  (2%:R : R)^-40 + 2%:R^-40 = 2%:R^-39.
Proof. by rewrite [RHS]splitr exprSr invfM. Qed.

Section kim_cert_numbers.
Variable R : realType.

(* The repeated row's published bound in closed form: twice the bundle's
   spectral number at word length seven. It is the quantity a reader of the
   row sees, before any reprice names it by a constant. *)
Lemma kim_centi_cert_epsE (idx : unit) :
  cert_eps (kim_centi_cert R idx)
  = Num.sqrt 5%:R * (1 / 80) ^+ 7 + Num.sqrt 5%:R * (1 / 80) ^+ 7.
Proof. by rewrite /cert_eps /= kim_lambda2_at_centi. Qed.

(* That bound is below two to the minus thirty-ninth, which is the number
   PGL(2,7)'s word row publishes. *)
Lemma kim_centi_cert_eps_lt (idx : unit) :
  cert_eps (kim_centi_cert R idx) < 2%:R ^- 39.
Proof.
rewrite /cert_eps.
have -> : (2%:R : R) ^- 39 = 2%:R ^- 40 + 2%:R ^- 40.
  by rewrite five_card_pow2_39_split.
by apply: ltrD; exact: kim_bound_centi.
Qed.

(* The one-cut row's published bound in closed form: twice the bundle's
   spectral number at word length one, sqrt 5 over forty. *)
Lemma kim_biased_cert_epsE (idx : unit) :
  cert_eps (kim_biased_cert R idx)
  = Num.sqrt 5%:R * (1 / 80) + Num.sqrt 5%:R * (1 / 80).
Proof. by rewrite /cert_eps !kim_biased_epsE. Qed.

(* The one-cut row's bound is below two, the ceiling var_dist_le2 gives for
   a variation distance. The row therefore excludes readings that the
   trivial bound permits, which is what makes it non-vacuous; at about
   three percent of the ceiling it is not strong. *)
Lemma kim_biased_cert_eps_lt2 (idx : unit) :
  cert_eps (kim_biased_cert R idx) < 2%:R.
Proof.
have Hs0 : 0 <= Num.sqrt 5%:R :> R by exact: sqrtr_ge0.
have Hs : Num.sqrt 5%:R <= 3%:R :> R.
  rewrite -(@ler_pXn2r R 2 isT).
  2: by rewrite nnegrE sqrtr_ge0.
  2: by rewrite nnegrE ler0n.
  by rewrite sqr_sqrtr ?ler0n // -natrX ler_nat.
by rewrite kim_biased_cert_epsE; lra.
Qed.

End kim_cert_numbers.

(******************************************************************************)
(*     S8, form 1: the rows against the manifest                              *)
(******************************************************************************)

(* The one-cut row published at IdealFinite is not the manifest's row for
   that path: the manifest records StaticExecutedOnly there. Under the
   manifest's own criterion a cut-carrier comparison with a discharged base
   premise is IdealFinite, so the manifest field is what a landing changes,
   not the program. *)
Fail Definition five_card_row_biased_ideal_rowE
  : published_row five_card_row_biased_ideal_tableau = five_card_row_biased
  := erefl.

(* The repeated row cannot match the manifest as it stands: publish always
   reaches AnalysisBridged and the manifest records Sampled, with
   NoModelComparison beside it. *)
Fail Definition five_card_row_repeated_spectral_rowE
  : published_row five_card_row_repeated_spectral_tableau
    = five_card_row_repeated
  := erefl.

(* The three coordinates the repeated row's program publishes. The manifest
   holds Sampled and NoModelComparison for that path, so the completion
   level and the transfer status are the two fields a landing changes. *)
Lemma five_card_row_repeated_spectral_publishedE :
  apr_completion (published_row five_card_row_repeated_spectral_tableau)
    = AnalysisBridged
  /\ apr_transfer (published_row five_card_row_repeated_spectral_tableau)
     = IdealFinite
  /\ apr_assumptions (published_row five_card_row_repeated_spectral_tableau)
     = BaselineClassicalOnly.
Proof. by []. Qed.

(* The three coordinates the one-cut row's program publishes. The manifest
   already holds AnalysisBridged for that path but records
   StaticExecutedOnly beside it, so the transfer status is the one field a
   landing changes. *)
Lemma five_card_row_biased_ideal_publishedE :
  apr_completion (published_row five_card_row_biased_ideal_tableau)
    = AnalysisBridged
  /\ apr_transfer (published_row five_card_row_biased_ideal_tableau)
     = IdealFinite
  /\ apr_assumptions (published_row five_card_row_biased_ideal_tableau)
     = BaselineClassicalOnly.
Proof. by []. Qed.

(******************************************************************************)
(*     S7, form 2: the same rows at a bound written as a constant             *)
(******************************************************************************)

(* The seven-cut law's marginal bound with its number written as the
   constant two to the minus fortieth rather than as the spectral
   expression. The per-card-position proof is the tree's own
   kim_deal_centi_lt weakened to a non-strict inequality, so the record
   asserts nothing new. This is the shape PGL(2,7)'s word row carries, and
   the shape a published constant needs. *)
Definition kim_centi_marginal_bound40 (R : realType)
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  @MkShuffleMarginalBound R FiveCardKim_M 7 (2%:R ^- 40)
    (sw_rho_dist (scb_bound (kim_security_bundle_centi R)))
    (fun s => Order.POrderTheory.ltW (kim_deal_centi_lt R s)).

(* The seven-cut law is within the constant two to the minus fortieth of
   the uniform rotation law, in variation distance on the cut group. It is
   the mixing field of the repeated row's certificate at the constant
   bound. *)
Lemma kim_centi_cut_mixing40 (R : realType) :
  var_dist (sw_rho_dist (kim_centi_marginal_bound40 R))
           (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps (kim_centi_marginal_bound40 R).
Proof.
by apply: five_card_cut_mixing_of_supp_pow; exact: kim_centi_cut_supp_pow.
Qed.

(* The repeated row's certificate with the constant in the marginal-bound
   field. Only that field changes: the ideal cut, the tying equation and the
   invariance of a coalition's reading are the same terms as in the
   certificate at the spectral number. *)
Definition kim_centi_cert40 (R : realType) (idx : unit)
  : SpectralCert (amf_sample kim_centi_family R idx) :=
  @MkSpectralCert R five_card_algebra five_card_params
    (amf_sample kim_centi_family R idx)
    (kim_centi_marginal_bound40 R)
    (esym (kim_centi_cut_distE R))
    (sa_cut_dist (five_card_sample R))
    (@kim_centi_cut_mixing40 R)
    (@five_card_static_obs_const R).

(* The certificate's own bound is then two copies of two to the minus
   fortieth, by conversion and with no arithmetic. *)
Lemma kim_centi_cert40_epsE (R : realType) (idx : unit) :
  cert_eps (kim_centi_cert40 R idx) = 2%:R ^- 40 + 2%:R ^- 40 :> R.
Proof. by []. Qed.

(* The name two to the minus thirty-ninth for a bound, at every real field. *)
Definition five_card_reprice39 : Reprice := fun R => Some (2%:R ^- 39 : R).

(* The repeated row republished at that constant. The reprice supplies the
   identity five_card_pow2_39_split and changes nothing else: the data, the
   model and the certificate are the same terms, so what a coalition below
   the threshold is shown is the same statement under a different name for
   the number. *)
Definition five_card_row_repeated39 : PublishedRowAt five_card_reprice39 :=
  five_card_committed
    ;;; sample_step of kim_centi_family
    ;;; certify_spectral of kim_centi_cert40
    ;;; conclude five_card_reprice39 of (fun R _ => five_card_pow2_39_split R)
    ;;; publish BaselineClassicalOnly of IdealFinite.

(* The reprice obligation is one identity per real field and per index, and
   five_card_pow2_39_split alone is an identity at one field. *)
Fail Definition five_card_row_repeated39_bare
  : PublishedRowAt five_card_reprice39 :=
  five_card_committed
    ;;; sample_step of kim_centi_family
    ;;; certify_spectral of kim_centi_cert40
    ;;; conclude five_card_reprice39 of five_card_pow2_39_split
    ;;; publish BaselineClassicalOnly of IdealFinite.

(******************************************************************************)
(*     S7, form 2: the one-cut row at its exact number                        *)
(******************************************************************************)

(* One card position of Kim's one-cut law is within one fiftieth of the
   uniform law on card positions. kim_one_cut_centiE makes this an equality,
   so the one-cut row can publish the distance itself instead of the
   spectral overestimate. *)
Lemma kim_one_cut_centi_le (R : realType) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
              (@rho_from_words_weighted R 3 4 1 fc_kim_gens
                 (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R))))
           (fdist_uniform (card_ord 5)) <= 1 / 50 :> R.
Proof. by rewrite kim_one_cut_centiE. Qed.

(* The one-cut law's marginal bound at the exact number one fiftieth. *)
Definition kim_biased_marginal_bound_exact (R : realType)
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  @MkShuffleMarginalBound R FiveCardKim_M 1 (1 / 50)
    (@rho_from_words_weighted R 3 4 1 fc_kim_gens
       (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R)))
    (fun s => kim_one_cut_centi_le R s).

(* Kim's one-cut law is within one fiftieth of the uniform rotation law, in
   variation distance on the cut group. It is the mixing field of the
   one-cut row's certificate at the exact number. *)
Lemma kim_biased_cut_mixing_exact (R : realType) :
  var_dist (sw_rho_dist (kim_biased_marginal_bound_exact R))
           (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps (kim_biased_marginal_bound_exact R).
Proof.
by apply: five_card_cut_mixing_of_supp_pow; exact: fc_kim_rho_supp_pow.
Qed.

(* The one-cut row's certificate at the exact number. *)
Definition kim_biased_cert_exact (R : realType) (idx : unit)
  : SpectralCert (amf_sample kim_biased_family R idx) :=
  @MkSpectralCert R five_card_algebra five_card_params
    (amf_sample kim_biased_family R idx)
    (kim_biased_marginal_bound_exact R)
    (kim_biased_sample_cut_witnessE R)
    (sa_cut_dist (five_card_sample R))
    (@kim_biased_cut_mixing_exact R)
    (@five_card_static_obs_const R).

(* Two copies of one fiftieth make one twenty-fifth. It is the identity
   that names the sum of the one-cut row's two exact per-card-position
   numbers by the single constant that row publishes. *)
Fact five_card_inv50_split (R : realType) : (1 / 50 : R) + 1 / 50 = 1 / 25.
Proof. by lra. Qed.

(* The name one twenty-fifth for a bound, at every real field. *)
Definition five_card_reprice_inv25 : Reprice := fun R => Some (1 / 25 : R).

(* The one-cut row republished at the exact constant, at the same transfer
   status as the row at the spectral number. The certificate it carries
   compares the same cut with the same ideal, so the number it publishes
   changes and the status it earns does not. *)
Definition five_card_row_biased_inv25
  : PublishedRowAt five_card_reprice_inv25 :=
  five_card_committed
    ;;; sample_step of kim_biased_family
    ;;; certify_spectral of kim_biased_cert_exact
    ;;; conclude five_card_reprice_inv25 of (fun R _ => five_card_inv50_split R)
    ;;; publish BaselineClassicalOnly of IdealFinite.

(* The repriced one-cut row is not the manifest's row either, for the one
   reason the unrepriced row is not: the manifest records StaticExecutedOnly
   for this path and a discharged cut-carrier comparison is IdealFinite. *)
Fail Definition five_card_row_biased_inv25_rowE
  : published_row five_card_row_biased_inv25 = five_card_row_biased := erefl.

(* The two one-cut programs publish one row, although their certificates
   carry different numbers, sqrt 5 over forty against one twenty-fifth. An
   AnalysisPathRow holds descriptive metadata and no Prop, so an equation
   between two published rows says nothing about either certificate, and in
   particular cannot say which transfer status is the honest one. *)
Lemma five_card_row_biased_forms_publishedE :
  published_row five_card_row_biased_ideal_tableau
  = published_row five_card_row_biased_inv25.
Proof. by []. Qed.

(* One twenty-fifth is below two, the ceiling var_dist_le2 gives for a
   variation distance, so the repriced one-cut row is not vacuous. *)
Lemma five_card_reprice_inv25_lt2 (R : realType) : (1 / 25 : R) < 2%:R.
Proof. by lra. Qed.

Print Assumptions five_card_row_repeated_spectral_tableau.
Print Assumptions five_card_row_biased_ideal_tableau.
Print Assumptions five_card_row_repeated39.
Print Assumptions five_card_row_biased_inv25.
