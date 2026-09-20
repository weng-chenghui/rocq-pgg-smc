(* Fidelity check of the P8 landing. Requires production only: every landed  *)
(* declaration is ascribed at its statement written out in full, every        *)
(* Arguments line is exercised by an application, and the two headlines and   *)
(* the universal report their assumptions.                                    *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import fdist_prod_cst_cond var_dist_joint_law.
From pgg_reconstruct Require Import pgg_sharing_framework algebraic_rigidity.
From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.
From pgg_smc Require Import pgg_tableau_security_property_relations.
From pgg_smc Require Import pgl27_word_privacy pgl27_exec pgl27_models.
From pgg_smc Require Import pgl27_tableau_analysis_bridged.
From pgg_smc Require Import five_card_group five_card_kim five_card_leakage.
From pgg_smc Require Import kim_input_privacy five_card_exec five_card_models.
From pgg_smc Require Import five_card_tableau_analysis_bridged.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(* lib/var_dist_supp.v *)

Check (@fdistmap_notin_codom0
  : forall (R : realType) (U B : finType) (g : U -> B) (P : R.-fdist U)
      (b : B), (forall u : U, g u != b) -> fdistmap g P b = 0).

Check (@var_dist_supp_disjoint_eq2
  : forall (R : realType) (A : finType) (P Q : R.-fdist A),
      (forall a : A, P a = 0 \/ Q a = 0) -> var_dist P Q = 2%:R).

(* lib/fdist_prod_cst_cond.v *)

Check (@inde_RV_cst
  : forall (R : realType) (U : finType) (P : R.-fdist U) (TA TB : finType)
      (X : {RV P -> TA}) (c : TB),
      P |= X _|_ ((fun=> c) : {RV P -> TB})).

Check (@sum_prod_fibreE
  : forall (R : realType) (T G V : finType) (PT : R.-fdist T)
      (Q : R.-fdist G) (f : T -> G -> V) (v : V) (x : T),
      \sum_(z : T * G | (f z.1 z.2 == v) && (z.1 == x)) PT z.1 * Q z.2
      = PT x * fdistmap (f x) Q v).

Check (@fdistmap_pair_fst_condE
  : forall (R : realType) (T G V : finType) (PT : R.-fdist T)
      (Q : R.-fdist G) (f : T -> G -> V) (v : V) (x : T),
      fdistmap (fun z : T * G => (f z.1 z.2, z.1)) (PT `x Q) (v, x)
      = PT x * fdistmap (f x) Q v).

Check (@fdistmap_prod_mixtureE
  : forall (R : realType) (T G V : finType) (PT : R.-fdist T)
      (Q : R.-fdist G) (f : T -> G -> V) (v : V),
      fdistmap (fun z : T * G => f z.1 z.2) (PT `x Q) v
      = \sum_(x : T) PT x * fdistmap (f x) Q v).

Check (@fdistmap_pair_fst_prodE
  : forall (R : realType) (T G V : finType) (PT : R.-fdist T)
      (Q : R.-fdist G) (f : T -> G -> V),
      (forall x x' : T, fdistmap (f x) Q = fdistmap (f x') Q) ->
      fdistmap (fun z : T * G => (f z.1 z.2, z.1)) (PT `x Q)
      = (fdistmap (fun z : T * G => f z.1 z.2) (PT `x Q)) `x PT).

(* security/var_dist_joint_law.v *)

Check (@var_dist_fdistmap_prodR_le
  : forall (R : realType) (A B C : finType) (P : R.-fdist A)
      (Q1 Q2 : R.-fdist B) (h : A * B -> C),
      var_dist (fdistmap h (P `x Q1)) (fdistmap h (P `x Q2))
      <= var_dist Q1 Q2).

(* manifest/pgg_tableau_security_property_relations.v, the threshold *)

Check (@profile_k_gt0
  : forall A : PGGAlgebraic, (0 < profile_k (instance_profile A))%N).

(******************************************************************************)
(*     Section A: the certificate whose two secrets are constant              *)
(******************************************************************************)

Section fidelity_A.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

Check (@exact_witness_cst_true R A E sa : ExactWitness sa).

Check (@idealproximity_cert_cst_secrets_true_false R A E sa
  : IdealProximityCert sa).

(* The fields the two docstrings claim. *)
Check (fun u : sa_sampleT sa =>
  (erefl : ew_secret (@exact_witness_cst_true R A E sa) u = true)).

Check (erefl
  : ipc_ideal (@idealproximity_cert_cst_secrets_true_false R A E sa) = sa).

Check (fun u : sa_sampleT sa =>
  (erefl : ew_secret (ipc_witness
     (@idealproximity_cert_cst_secrets_true_false R A E sa)) u = true)).

Check (fun u : sa_sampleT sa =>
  (erefl : ipc_secret
     (@idealproximity_cert_cst_secrets_true_false R A E sa) u = false)).

Check (erefl
  : ipc_eps (@idealproximity_cert_cst_secrets_true_false R A E sa)
    = 2%:R :> R).

Check (@idealproximity_prop_cst_secrets_lt2_false R A E sa
  : forall c : R, c < 2%:R ->
      ~ IdealProximityPropAt
          (@idealproximity_cert_cst_secrets_true_false R A E sa) c).

Check (@idealproximity_prop_lt2_uniform_in_cert_false R A E sa
  : forall c : R, c < 2%:R ->
      ~ (forall cert : IdealProximityCert sa, IdealProximityPropAt cert c)).

Check (@indistinguishability_prop_idealproximity_lt2_false R A E sa
  : forall (ic : IndistinguishabilityCert sa) (c : R), c < 2%:R ->
      ~ (IndistinguishabilityPropAt ic (cert_eps ic) ->
         forall cert : IdealProximityCert sa, IdealProximityPropAt cert c)).

End fidelity_A.

(******************************************************************************)
(*     Section B: ideal proximity from input indistinguishability             *)
(******************************************************************************)

Section fidelity_B.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).
Variable argT : finType.
Variable arg_decode : argT -> ex_inputT E.
Variable arg_read : sa_sampleT sa -> argT.
Hypothesis Harg : forall u : sa_sampleT sa,
  sa.(sa_arg) u = arg_decode (arg_read u).
Hypothesis Hprod :
  fdistmap (fun u => (arg_read u, sa.(sa_cut) u)) (sa_sampleP sa)
  = (fdistmap arg_read (sa_sampleP sa)) `x (sa_cut_dist sa).
Variable ic : IndistinguishabilityCert sa.
Variable Hendp : instance_endpoints_stmt E.
Variable C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}.
Hypothesis HC : (#|C| < profile_k (instance_profile A))%N.

(* The Arguments lines, exercised by an application. *)
Definition chk_adapter := ideal_prod_adapter arg_decode arg_read ic.
Definition chk_prodE := ideal_prod_reading_arg_prodE arg_decode arg_read ic HC.
Definition chk_indep := ideal_prod_reading_indep_arg arg_decode arg_read ic HC.
Definition chk_witness := exact_witness_ideal_prod arg_decode arg_read ic.
Definition chk_argdist := arg_read_distE arg_decode arg_read ic.
Definition chk_joint := var_dist_joint_reading_arg_le Harg Hprod ic C.
Definition chk_close :=
  idealproximity_close_of_indistinguishability Harg Hprod ic HC.
Definition chk_cert :=
  idealproximity_cert_of_indistinguishability Harg Hprod ic.
Definition chk_prop :=
  idealproximity_prop_of_indistinguishability Harg Hprod ic Hendp.

(* The fields the docstrings claim. *)
Check (erefl
  : sa_sampleP (ideal_prod_adapter arg_decode arg_read ic)
    = (fdistmap arg_read (sa_sampleP sa)) `x (ic_ideal ic)).

Check (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
  (erefl : ew_secret (exact_witness_ideal_prod arg_decode arg_read ic) z
           = z.1)).

Check (erefl
  : ipc_eps (idealproximity_cert_of_indistinguishability Harg Hprod ic)
    = sw_bound_eps (ic_b ic)).

(* The statements written out in full. *)

Check (ideal_prod_adapter arg_decode arg_read ic
  : SampleAdapter R (instance_exec E)).

Check (@ideal_prod_reading_arg_prodE R A E sa argT arg_decode arg_read ic C
  : (#|C| < profile_k (instance_profile A))%N ->
    fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
                (static_coalition_obs C (arg_decode z.1) z.2, z.1))
      ((fdistmap arg_read (sa_sampleP sa)) `x (ic_ideal ic))
    = (fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
                   static_coalition_obs C (arg_decode z.1) z.2)
         ((fdistmap arg_read (sa_sampleP sa)) `x (ic_ideal ic)))
      `x (fdistmap arg_read (sa_sampleP sa))).

Check (@ideal_prod_reading_indep_arg R A E sa argT arg_decode arg_read ic C
  : (#|C| < profile_k (instance_profile A))%N ->
    sa_sampleP (ideal_prod_adapter arg_decode arg_read ic)
    |= ((fun z => static_coalition_obs C
                    ((ideal_prod_adapter arg_decode arg_read ic).(sa_arg) z)
                    ((ideal_prod_adapter arg_decode arg_read ic).(sa_cut) z))
        : {RV (sa_sampleP (ideal_prod_adapter arg_decode arg_read ic))
             -> {ffun 'I_(pi_T' (mp_PI (instance_profile A))).+1
                   -> 'I_(pgg_N' (mp_M (instance_profile A))).+1}})
       _|_ ((fun z => z.1)
            : {RV (sa_sampleP (ideal_prod_adapter arg_decode arg_read ic))
                 -> argT})).

Check (exact_witness_ideal_prod arg_decode arg_read ic
  : ExactWitness (ideal_prod_adapter arg_decode arg_read ic)).

Check (arg_read_distE arg_decode arg_read ic
  : fdistmap (ew_secret (exact_witness_ideal_prod arg_decode arg_read ic))
      (sa_sampleP (ideal_prod_adapter arg_decode arg_read ic))
    = fdistmap arg_read (sa_sampleP sa)).

Check (var_dist_joint_reading_arg_le Harg Hprod ic C
  : var_dist
      (fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                             (sa.(sa_cut) u), arg_read u)) (sa_sampleP sa))
      (fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
                   (static_coalition_obs C (arg_decode z.1) z.2, z.1))
         ((fdistmap arg_read (sa_sampleP sa)) `x (ic_ideal ic)))
    <= var_dist (sa_cut_dist sa) (ic_ideal ic)).

Check (@idealproximity_close_of_indistinguishability R A E sa argT arg_decode
         arg_read Harg Hprod ic C
  : (#|C| < profile_k (instance_profile A))%N ->
    var_dist
      (fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                             (sa.(sa_cut) u), arg_read u)) (sa_sampleP sa))
      (fdistmap (fun z => (static_coalition_obs C
                             ((ideal_prod_adapter arg_decode arg_read
                                 ic).(sa_arg) z)
                             ((ideal_prod_adapter arg_decode arg_read
                                 ic).(sa_cut) z),
                           ew_secret (exact_witness_ideal_prod arg_decode
                                        arg_read ic) z))
         (sa_sampleP (ideal_prod_adapter arg_decode arg_read ic)))
    <= sw_bound_eps (ic_b ic)).

Check (idealproximity_cert_of_indistinguishability Harg Hprod ic
  : IdealProximityCert sa).

Check (idealproximity_prop_of_indistinguishability Harg Hprod ic Hendp
  : IdealProximityPropAt
      (idealproximity_cert_of_indistinguishability Harg Hprod ic)
      (sw_bound_eps (ic_b ic))).

End fidelity_B.

(******************************************************************************)
(*     The instance facts                                                     *)
(******************************************************************************)

Check (@pgl27_word_arg_cut_prodE
  : forall (R : realType) (secretP : R.-fdist bool),
      fdistmap
        (fun u => (@sa_arg _ _ _ (amf_sample pgl27_word_family R secretP) u,
                   @sa_cut _ _ _ (amf_sample pgl27_word_family R secretP) u))
        (sa_sampleP (amf_sample pgl27_word_family R secretP))
      = secretP `x (rho_word R)).

Check (@pgl27_word_arg_cut_marginals_prodE
  : forall (R : realType) (secretP : R.-fdist bool),
      fdistmap
        (fun u : bool * (200.-tuple 'I_5) =>
           (u.1, @sa_cut _ _ _ (amf_sample pgl27_word_family R secretP) u))
        (sa_sampleP (amf_sample pgl27_word_family R secretP))
      = (fdistmap (fun u : bool * (200.-tuple 'I_5) => u.1)
           (sa_sampleP (amf_sample pgl27_word_family R secretP)))
        `x (sa_cut_dist (amf_sample pgl27_word_family R secretP))).

Check (@pgl27_word_arg_readE
  : forall (R : realType) (secretP : R.-fdist bool)
      (u : bool * (200.-tuple 'I_5)),
      @sa_arg _ _ _ (amf_sample pgl27_word_family R secretP) u = u.1).

Check (@kim_biased_arg_cut_prodE
  : forall (R : realType) (idx : unit),
      fdistmap
        (fun u => (@sa_arg _ _ _ (amf_sample kim_biased_family R idx) u,
                   @sa_cut _ _ _ (amf_sample kim_biased_family R idx) u))
        (sa_sampleP (amf_sample kim_biased_family R idx))
      = (fdist_uniform card_bool2)
        `x (fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g)
              (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R)))).

Check (@kim_biased_arg_cut_marginals_prodE
  : forall (R : realType) (idx : unit),
      fdistmap
        (fun u : five_card_leakage.Omega =>
           (five_card_sample_arg u,
            @sa_cut _ _ _ (amf_sample kim_biased_family R idx) u))
        (sa_sampleP (amf_sample kim_biased_family R idx))
      = (fdistmap (fun u : five_card_leakage.Omega => five_card_sample_arg u)
           (sa_sampleP (amf_sample kim_biased_family R idx)))
        `x (sa_cut_dist (amf_sample kim_biased_family R idx))).

Check (@kim_biased_arg_readE
  : forall (R : realType) (idx : unit) (u : five_card_leakage.Omega),
      @sa_arg _ _ _ (amf_sample kim_biased_family R idx) u
      = five_card_sample_arg u).

Check (@pgl27_word_proximity_eps_sw_boundE
  : forall (R : realType) (secretP : R.-fdist bool),
      ipc_eps (pgl27_word_proximity_cert secretP)
      = sw_bound_eps (ic_b (pgl27_word_cert secretP))).

Check (@kim_biased_proximity_eps_cert_exact_sw_boundE
  : forall (R : realType) (idx : unit),
      ipc_eps (kim_biased_proximity_cert R idx)
      = sw_bound_eps (ic_b (kim_biased_cert_exact R idx))).

Check (@kim_biased_proximity_eps_le_cert_sw_bound
  : forall (R : realType) (idx : unit),
      ipc_eps (kim_biased_proximity_cert R idx)
      <= sw_bound_eps (ic_b (kim_biased_cert R idx))).

(******************************************************************************)
(*     Assumptions of the two headlines and of the universal                  *)
(******************************************************************************)

Print Assumptions idealproximity_prop_cst_secrets_lt2_false.
Print Assumptions idealproximity_prop_lt2_uniform_in_cert_false.
Print Assumptions indistinguishability_prop_idealproximity_lt2_false.
Print Assumptions idealproximity_prop_of_indistinguishability.
