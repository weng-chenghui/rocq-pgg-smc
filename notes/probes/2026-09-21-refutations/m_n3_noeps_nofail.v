(* Probe for notes/20260921-refutations-probe-design.md. Not production text. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_alldecks.
From pgg_smc Require Import psl211_models psl211_reading_constancy.
From refuteprobe Require Import n_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Notation cutT := (pgg_gT psl211_M).

(* The route of N2 at the name the tree uses, repeated here so that the
   mutation below is the N3 statement alone and not a second change. *)
Lemma no_certificate_near_of_constancy_false (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (U : R.-fdist (pgg_gT (mp_M (instance_profile A)))) (eps : R) :
  (forall u : R.-fdist (pgg_gT (mp_M (instance_profile A))),
     var_dist U u <= eps -> ~ coalition_reading_constancy E u) ->
  NoIndistinguishabilityCertNear sa U eps.
Proof.
move=> H cert Hc.
exact: (H (ic_ideal cert) Hc
          (indistinguishability_cert_reading_constancy cert)).
Qed.

(* N3 with its hypothesis eps + eps < 1 / #|G| deleted. The proof body is the
   original one, whose last step has nothing left to supply that hypothesis
   from. *)
Definition mutant_no_eps_bound (R : realType) (eps : R)
  : NoIndistinguishabilityCertNear (amf_sample psl211_exact_family R tt)
      ((`U psl211_G_pos) : R.-fdist cutT) eps
  := ltac:(apply: (@no_certificate_near_of_constancy_false R psl211_algebra
                     psl211_alldecks_params
                     (amf_sample psl211_exact_family R tt)
                     ((`U psl211_G_pos) : R.-fdist cutT) eps);
           move=> u Hclose;
           exact (@psl211_alldecks_constancy_false_close R u eps Hclose)).
