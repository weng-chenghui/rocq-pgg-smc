(* PROBE, notes/probes/2026-09-19-kim-tableau-sampled/kim_biased_arms_probe.v *)
(* Ledger rows K7 and K8 of notes/20260919-kim-tableau-sampled-design.md:     *)
(* whether Kim's input-privacy bound restates on the law the biased row       *)
(* samples, and which fields of the two certify arms exist for that row.      *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import reals boolp.
From infotheo Require Import fdist proba entropy.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter pgg_trace_secrecy.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage five_card_exec five_card_models.
From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import five_card_rows.
From pgg_smc Require Import kim_input_privacy pgg_weighted_words.
From pgg_reconstruct Require Import algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

Definition five_card_row_biased_tableau : Tableau Sampled :=
  five_card_committed
    sample kim_biased_family.

(******************************************************************************)
(*     K7: Kim's bound on the law the biased row samples                      *)
(******************************************************************************)

(* sa_sampleP of the family member is Kim's joint law, as terms. *)
Check (fun R : realType =>
  erefl : sa_sampleP (amf_sample kim_biased_family R tt)
        = kim_input_dist (kim_centi_lt R) (kim_centi_gt R)).

(* The fourth side condition on the bias. The tree carries kim_centi_lt,
   kim_centi_gt and kim_centi_spec at bias one hundredth and not this one,
   which five_card_colour_view_leak_bound consumes. *)
Lemma kim_centi_small (R : realType) : 0 < 5%:R^-1 - `|1 / 100 : R|.
Proof.
by rewrite subr_gt0 ger0_norm ?divr_ge0// ltr_pdivrMr ?ltr0n//
   mulrC ltr_pdivlMr ?ltr0n// mul1r ltr_nat.
Qed.

(* Kim's input-privacy bound, restated with every random variable typed at the
   law the biased row's program samples. *)
Lemma five_card_row_biased_leak_bound (R : realType) (A : seq nat) :
  cond_mutual_info
    (`p_ [% (kim_inputs (kim_centi_lt R) (kim_centi_gt R)
             : {RV (sa_sampleP (amf_sample kim_biased_family R tt))
                   -> bool * bool}),
            ((fun w : five_card_leakage.Omega =>
                five_card_exec_colour_view A w.1
                  (five_card_group.fc_sigma ^+ w.2)%g)
             : {RV (sa_sampleP (amf_sample kim_biased_family R tt))
                   -> (size A).-tuple bool}),
            (kim_secret (kim_centi_lt R) (kim_centi_gt R)
             : {RV (sa_sampleP (amf_sample kim_biased_family R tt)) -> bool})])
  <= kim_leak_bound (1 / 100 : R).
Proof. exact: (five_card_colour_view_leak_bound _ _ (kim_centi_small R)). Qed.

Print Assumptions five_card_row_biased_leak_bound.

(******************************************************************************)
(*     K8, exact arm: the witness the biased row would need                   *)
(******************************************************************************)

(* The residual obligation of MkExactWitness at the biased row, printed: it is
   ew_indep, exact independence of the coalition's static reading from a
   secret on sa_sampleP of the biased member. *)
Check (fun R : realType =>
  @MkExactWitness R five_card_algebra five_card_params
    (amf_sample kim_biased_family R tt) bool (Secret R)).

(* Expected failure: the tree's one independence theorem of this shape,
   five_card_static_obs_indep, is typed at the uniform family's member and
   does not apply to the biased one. *)
Fail Definition five_card_biased_exact_witness (R : realType)
  : ExactWitness (amf_sample kim_biased_family R tt) :=
  @MkExactWitness R five_card_algebra five_card_params
    (amf_sample kim_biased_family R tt) bool (Secret R)
    (@five_card_static_obs_indep R tt).

(******************************************************************************)
(*     K8, spectral arm: the three fields that can be built                   *)
(******************************************************************************)

Section five_card_biased_spectral_fields.
Variable R : realType.

(* sc_b: the marginal bound of the certificate bundle at bias one hundredth
   and word length one. *)
Definition five_card_biased_sc_b
  : ShuffleMarginalBound R (instance_M five_card_algebra) :=
  scb_bound (@fc_kim_security_bundle R (1 / 100)
               (kim_centi_lt R) (kim_centi_gt R) (kim_centi_spec R) 1).

(* sc_Hd: that bound's law is the law the biased row draws its cut from. *)
Definition five_card_biased_sc_Hd
  : sw_rho_dist five_card_biased_sc_b
  = sa_cut_dist (amf_sample kim_biased_family R tt) :=
  ltac:(rewrite /five_card_biased_sc_b /= rho_from_words_weighted1
                kim_single_cut_distE;
        congr fdistmap; apply: funext => k; exact: fc_kim_gensE).

(* sc_ideal: any law on the cut carrier serves; the uniform rotation one is
   the instance's own. *)
Definition five_card_biased_sc_ideal
  : R.-fdist (pgg_gT (mp_M (instance_profile five_card_algebra))) :=
  sa_cut_dist (five_card_sample R).

(* The two residual obligations, printed: sc_close, a variation distance on
   the cut group, and sc_const, constancy of a coalition's reading of the
   ideal law in the run argument. *)
Check (@MkSpectralCert R five_card_algebra five_card_params
         (amf_sample kim_biased_family R tt)
         five_card_biased_sc_b five_card_biased_sc_Hd
         five_card_biased_sc_ideal).

(* Expected failure: the only distance the bundle carries is sw_bound, one
   endpoint marginal on 'I_5 at each starting position, and sc_close asks for
   a distance between two laws on the cut group itself. *)
Fail Definition five_card_biased_sc_close :
  var_dist (sw_rho_dist five_card_biased_sc_b) five_card_biased_sc_ideal
  <= sw_bound_eps five_card_biased_sc_b
  := ltac:(exact: (sw_bound five_card_biased_sc_b)).

(* Expected failure: kim_one_cut_centiE is the same per-position shape, an
   exact value rather than a bound, and equally not a distance on the group. *)
Fail Definition five_card_biased_sc_close_exact :
  var_dist (sw_rho_dist five_card_biased_sc_b) five_card_biased_sc_ideal
  <= sw_bound_eps five_card_biased_sc_b
  := ltac:(exact: (kim_one_cut_centiE R)).

End five_card_biased_spectral_fields.

(* The sc_const field's shape is proved for one instance in the tree, at
   PGL(2,7), by pgl27_word_view_const in instances/pgl27/pgl27_rows.v:224,
   where three-transitivity supplies it. The five-card development states
   nothing of this shape at any cut law, so the field is quoted here from its
   own file rather than checked, this probe importing what five_card_rows.v
   imports and not the PGL(2,7) row file. *)
