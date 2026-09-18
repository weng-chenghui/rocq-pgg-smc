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
From pgg_smc Require Import pgl27_word_privacy.
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

(* The one-cut model's cut law is the law the length-one bundle bounds. *)
Definition five_card_biased_sc_Hd (R : realType)
  : sw_rho_dist (five_card_biased_sc_b R)
  = sa_cut_dist (amf_sample kim_biased_family R tt) :=
  ltac:(rewrite /five_card_biased_sc_b /= rho_from_words_weighted1
                kim_single_cut_distE;
        congr fdistmap; apply: funext => k; exact: fc_kim_gensE).

(******************************************************************************)
(*     S6, form 1: the certificates at the bundles' own numbers               *)
(******************************************************************************)

(* The spectral certificate of the repeated row. Its five fields are the
   seven-cut bundle's marginal bound; the identification of that bound's law
   with the law the repeated adapter draws its cut from; the uniform rotation
   law as the ideal cut; the distance of the seven-cut law from that ideal;
   and the constancy of a coalition's reading of the ideal cut in the
   committed pair. The only inexact quantity in the row is the bundle's
   spectral number; the two fields about the ideal cut are exact. *)
Definition kim_centi_cert (R : realType) (idx : unit)
  : SpectralCert (amf_sample kim_centi_family R idx) :=
  @MkSpectralCert R five_card_algebra five_card_params
    (amf_sample kim_centi_family R idx)
    (scb_bound (kim_security_bundle_centi R))
    (esym (kim_centi_cut_distE R))
    (sa_cut_dist (five_card_sample R))
    (@kim_centi_sc_close R)
    (@five_card_sc_const R).

(* The same certificate for the one-cut row, at word length one. *)
Definition kim_biased_cert (R : realType) (idx : unit)
  : SpectralCert (amf_sample kim_biased_family R idx) :=
  @MkSpectralCert R five_card_algebra five_card_params
    (amf_sample kim_biased_family R idx)
    (five_card_biased_sc_b R)
    (five_card_biased_sc_Hd R)
    (sa_cut_dist (five_card_sample R))
    (@kim_biased_sc_close R)
    (@five_card_sc_const R).

(******************************************************************************)
(*     S6, form 1: the two row programs                                       *)
(******************************************************************************)

(* The repeated row certified by the spectral arm, at the transfer status a
   comparison of a finite shuffle with an ideal cut carries. *)
Definition kim_row_repeated_spectral : PublishedRow :=
  five_card_committed
    sample kim_centi_family
    certify SpectralDecay kim_centi_cert
    |> publish IdealFinite BaselineClassicalOnly.

(* The one-cut row certified by the same arm, at the same transfer status. *)
Definition kim_row_biased_spectral : PublishedRow :=
  five_card_committed
    sample kim_biased_family
    certify SpectralDecay kim_biased_cert
    |> publish IdealFinite BaselineClassicalOnly.

(* The one-cut row at the transfer status the manifest records for it. *)
Definition kim_row_biased_spectral_static : PublishedRow :=
  five_card_committed
    sample kim_biased_family
    certify SpectralDecay kim_biased_cert
    |> publish StaticExecutedOnly BaselineClassicalOnly.

(******************************************************************************)
(*     S7, form 1: the numbers the rows carry                                 *)
(******************************************************************************)

Section kim_cert_numbers.
Variable R : realType.

(* The repeated row's published bound, in closed form. *)
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
have -> : (2%:R : R) ^- 39 = 2%:R ^- 40 + 2%:R ^- 40 by rewrite pow2_split.
by apply: ltrD; exact: kim_bound_centi.
Qed.

(* The one-cut row's published bound, in closed form. *)
Lemma kim_biased_cert_epsE (idx : unit) :
  cert_eps (kim_biased_cert R idx)
  = Num.sqrt 5%:R * (1 / 80) + Num.sqrt 5%:R * (1 / 80).
Proof. by rewrite /cert_eps !five_card_biased_epsE. Qed.

(* A variation distance here is the sum of the absolute differences, twice
   the total variation distance, so its ceiling is two. The one-cut row's
   bound is far below that ceiling, so the row's statement is not vacuous. *)
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

(* The one-cut row certified by the spectral arm, published at the manifest's
   own transfer status, is the manifest's row for that path. Conversion
   decides it, so this row reaches AnalysisBridged through the arm with no
   manifest field changed. *)
Lemma kim_row_biased_static_rowE :
  published_row kim_row_biased_spectral_static = five_card_row_biased.
Proof. by []. Qed.

(* At IdealFinite the same program publishes a different row: the manifest
   records StaticExecutedOnly for this instance's biased path. *)
Fail Definition kim_row_biased_rowE_bad
  : published_row kim_row_biased_spectral = five_card_row_biased := erefl.

(* The repeated row cannot match the manifest as it stands: publish always
   reaches AnalysisBridged and the manifest records Sampled, with
   NoModelComparison beside it. *)
Fail Definition kim_row_repeated_rowE_bad
  : published_row kim_row_repeated_spectral = five_card_row_repeated := erefl.

(* The three coordinates the repeated row's program publishes, read off the
   published row. The first two are the manifest fields a landing changes. *)
Lemma kim_row_repeated_published_fields :
  apr_completion (published_row kim_row_repeated_spectral) = AnalysisBridged
  /\ apr_transfer (published_row kim_row_repeated_spectral) = IdealFinite
  /\ apr_assumptions (published_row kim_row_repeated_spectral)
     = BaselineClassicalOnly.
Proof. by []. Qed.

(******************************************************************************)
(*     S7, form 2: the same rows at a bound written as a constant             *)
(******************************************************************************)

(* The seven-cut law's marginal bound with its number written as the constant
   two to the minus fortieth rather than as the spectral expression. The
   per-position proof is the tree's own kim_deal_centi_lt weakened to a
   non-strict inequality, so the record asserts nothing new. This is the
   shape PGL(2,7)'s word row carries, and the shape a published constant
   needs. *)
Definition kim_centi_bound40 (R : realType)
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  @MkShuffleMarginalBound R FiveCardKim_M 7 (2%:R ^- 40)
    (sw_rho_dist (scb_bound (kim_security_bundle_centi R)))
    (fun s => Order.POrderTheory.ltW (kim_deal_centi_lt R s)).

(* The same distance statement at the constant bound. *)
Lemma kim_centi40_sc_close (R : realType) :
  var_dist (sw_rho_dist (kim_centi_bound40 R))
           (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps (kim_centi_bound40 R).
Proof.
by apply: five_card_sc_close_of_rot_supp; exact: kim_centi_rot_supp.
Qed.

(* The repeated row's certificate at the constant bound. *)
Definition kim_centi_cert40 (R : realType) (idx : unit)
  : SpectralCert (amf_sample kim_centi_family R idx) :=
  @MkSpectralCert R five_card_algebra five_card_params
    (amf_sample kim_centi_family R idx)
    (kim_centi_bound40 R)
    (esym (kim_centi_cut_distE R))
    (sa_cut_dist (five_card_sample R))
    (@kim_centi40_sc_close R)
    (@five_card_sc_const R).

(* The certificate's own bound is then two copies of two to the minus
   fortieth, by conversion and with no arithmetic. *)
Lemma kim_centi_cert40_epsE (R : realType) (idx : unit) :
  cert_eps (kim_centi_cert40 R idx) = 2%:R ^- 40 + 2%:R ^- 40 :> R.
Proof. by []. Qed.

(* The name two to the minus thirty-ninth for a bound, at every real field. *)
Definition kim_reprice39 : Reprice := fun R => Some (2%:R ^- 39 : R).

(* The repeated row republished at that constant. The identity that adds the
   two copies is the tree's own pow2_split, and the data, the model and the
   certificate are untouched. *)
Definition kim_row_repeated39 : PublishedRowAt kim_reprice39 :=
  five_card_committed
    ;;; sample_step of kim_centi_family
    ;;; certify_spectral of kim_centi_cert40
    ;;; conclude kim_reprice39 of (fun R _ => pow2_split R)
    ;;; publish BaselineClassicalOnly of IdealFinite.

(* The reprice obligation is one identity per real field and per index, and
   pow2_split alone is an identity at one field. *)
Fail Definition kim_row_repeated39_bare : PublishedRowAt kim_reprice39 :=
  five_card_committed
    ;;; sample_step of kim_centi_family
    ;;; certify_spectral of kim_centi_cert40
    ;;; conclude kim_reprice39 of pow2_split
    ;;; publish BaselineClassicalOnly of IdealFinite.

(******************************************************************************)
(*     S7, form 2: the one-cut row at its exact number                        *)
(******************************************************************************)

(* The exact one-cut endpoint distance, read as a bound. kim_one_cut_centiE
   is an equality, so the marginal bound record can carry the exact number
   rather than the spectral one. *)
Lemma kim_one_cut_le (R : realType) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
              (@rho_from_words_weighted R 3 4 1 fc_kim_gens
                 (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R))))
           (fdist_uniform (card_ord 5)) <= 1 / 50 :> R.
Proof. by rewrite kim_one_cut_centiE. Qed.

(* The one-cut law's marginal bound at the exact number one fiftieth. *)
Definition kim_biased_bound50 (R : realType)
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  @MkShuffleMarginalBound R FiveCardKim_M 1 (1 / 50)
    (@rho_from_words_weighted R 3 4 1 fc_kim_gens
       (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R)))
    (fun s => kim_one_cut_le R s).

(* The same distance statement at the exact number. *)
Lemma kim_biased50_sc_close (R : realType) :
  var_dist (sw_rho_dist (kim_biased_bound50 R))
           (sa_cut_dist (five_card_sample R))
  <= sw_bound_eps (kim_biased_bound50 R).
Proof.
by apply: five_card_sc_close_of_rot_supp; exact: rho_words_rot_supp.
Qed.

(* The one-cut row's certificate at the exact number. *)
Definition kim_biased_cert50 (R : realType) (idx : unit)
  : SpectralCert (amf_sample kim_biased_family R idx) :=
  @MkSpectralCert R five_card_algebra five_card_params
    (amf_sample kim_biased_family R idx)
    (kim_biased_bound50 R)
    (five_card_biased_sc_Hd R)
    (sa_cut_dist (five_card_sample R))
    (@kim_biased50_sc_close R)
    (@five_card_sc_const R).

(* Two fiftieths make a twenty-fifth. *)
Fact fifty_split (R : realType) : (1 / 50 : R) + 1 / 50 = 1 / 25.
Proof. by lra. Qed.

(* The name one twenty-fifth for a bound, at every real field. *)
Definition kim_reprice25 : Reprice := fun R => Some (1 / 25 : R).

(* The one-cut row republished at that constant, at the transfer status the
   manifest records for this path. *)
Definition kim_row_biased25 : PublishedRowAt kim_reprice25 :=
  five_card_committed
    ;;; sample_step of kim_biased_family
    ;;; certify_spectral of kim_biased_cert50
    ;;; conclude kim_reprice25 of (fun R _ => fifty_split R)
    ;;; publish BaselineClassicalOnly of StaticExecutedOnly.

(* The repriced one-cut row still publishes the manifest's own row. *)
Lemma kim_row_biased25_rowE :
  published_row kim_row_biased25 = five_card_row_biased.
Proof. by []. Qed.

(* One twenty-fifth is below the ceiling of a variation distance. *)
Lemma kim_reprice25_lt2 (R : realType) : (1 / 25 : R) < 2%:R.
Proof. by lra. Qed.

Print Assumptions kim_row_repeated_spectral.
Print Assumptions kim_row_biased_spectral_static.
Print Assumptions kim_row_repeated39.
Print Assumptions kim_row_biased25.
