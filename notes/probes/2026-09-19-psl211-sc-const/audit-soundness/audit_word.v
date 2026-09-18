(* Soundness audit scratch, 2026-09-19. Not a production file. *)
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
From pgg_smc Require Import pgg_sample_adapter pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import design_privacy algebraic_rigidity.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import psl211_group psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_exec.
From pgg_smc Require Import psl211_endpoints psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_blocks psl211_closure.
From psl211_sc_const_probe Require Import psl211_sc_const_probe.
From psl211_sc_const_probe Require Import psl211_sc_const_bound_probe.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Import Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Notation cutT := (pgg_gT psl211_M).

Local Opaque psl211_alldecks_view psl211_elem_table psl211_perdeck_raw_count.

(* A1. Field fidelity, forward: the record field has the restatement's type. *)
Check (fun (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
           (sa : SampleAdapter R (instance_exec E)) (cert : SpectralCert sa) =>
         (sc_const cert : sc_const_prop E (sc_ideal cert))).

(* A2. Field fidelity, backward: the restatement is accepted in the field slot
   of the constructor, so the two types are convertible and not merely
   related by an implication. *)
Definition audit_mk (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E))
    (b : ShuffleMarginalBound R (instance_M A))
    (Hd : sw_rho_dist b = sa_cut_dist sa)
    (ideal : R.-fdist (pgg_gT (mp_M (instance_profile A))))
    (Hc : var_dist (sw_rho_dist b) ideal <= sw_bound_eps b)
    (Hconst : sc_const_prop E ideal) : SpectralCert sa :=
  @MkSpectralCert R A E sa b Hd ideal Hc Hconst.

(* A3. The restatement quantifies over the raw run-argument carrier: at the
   all-decks parameters that carrier is the deck-description type, with no
   validity predicate standing between it and the field. *)
Check (erefl : ex_inputT psl211_alldecks_params = psl211_inputT).
Check ((true, psl211_perdeck_deal) : ex_inputT psl211_alldecks_params).
Check ((false, psl211_perdeck_deal) : ex_inputT psl211_alldecks_params).

(* B1. The triangle inequality for infotheo's variation distance, which the
   library does not state. *)
Lemma audit_var_dist_tri (R : realType) (T : finType) (P Q S : R.-fdist T) :
  var_dist P S <= var_dist P Q + var_dist Q S.
Proof.
rewrite /var_dist -big_split /=.
apply: ler_sum => a _.
have E : (P a - Q a) + (Q a - S a) = P a - S a by rewrite addrA addrNK.
by rewrite -E; exact: ler_normD.
Qed.

(* B2. The word-row corollary: a cut law W at distance d from the group-uniform
   law and an ideal at distance eps from W leave no constancy field, provided
   twice the sum stays below the reciprocal of the group order. This is the
   shape a weighted-word adapter would enter through, and it is the statement
   the probe's close lemma does not itself make. *)
Lemma audit_sc_const_false_word (R : realType) (W ideal : R.-fdist cutT)
    (d eps : R) :
  var_dist ((`U psl211_G_pos) : R.-fdist cutT) W <= d ->
  var_dist W ideal <= eps ->
  (d + eps) + (d + eps) < (#|pgg_G psl211_M|%:R)^-1 ->
  ~ sc_const_prop psl211_alldecks_params ideal.
Proof.
move=> HW Hi Hlt Hconst.
have Hclose : var_dist ((`U psl211_G_pos) : R.-fdist cutT) ideal <= d + eps.
  apply: (Order.POrderTheory.le_trans (audit_var_dist_tri _ W _)).
  exact: lerD HW Hi.
exact: (@psl211_alldecks_sc_const_false_close R ideal (d + eps)
          Hclose Hlt Hconst).
Qed.

Print Assumptions audit_var_dist_tri.
Print Assumptions audit_sc_const_false_word.
