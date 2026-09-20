(* P8 arm-relations probe, ledger row B6: B1's hypothesis at the two          *)
(* production models over which a proximity certificate was built by hand,    *)
(* and the generic construction's number against the hand-built one.          *)
(*                                                                            *)
(* Both models draw a finite run argument and a cut from a product law, the   *)
(* cut through a map of the second factor alone, which is the shape           *)
(* fdistmap_prodr states. The hypothesis of B1 therefore holds at both, and   *)
(* the number the generic certificate would carry is the number the hand-     *)
(* built certificate carries.                                                 *)

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
From pgg_reconstruct Require Import algebraic_rigidity.
From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgl27_tableau_analysis_bridged.
From pgg_smc Require Import five_card_group five_card_leakage.
From pgg_smc Require Import five_card_exec five_card_models.
From pgg_smc Require Import five_card_tableau_analysis_bridged.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     The PGL(2,7) word model                                                *)
(******************************************************************************)

(** The word model's run argument is the first factor of its sample space and
    its cut is the evaluation of the second, so the pair of the two is a
    product law: B1's hypothesis holds there with the secret prior as the
    argument factor. *)
Lemma pgl27_word_arg_cut_prod (R : realType) (secretP : R.-fdist bool) :
  exists (Parg : R.-fdist bool)
         (rho : R.-fdist (pgg_gT (mp_M (instance_profile pgl27_algebra)))),
    fdistmap (fun u => (@sa_arg _ _ _ (amf_sample pgl27_word_family R secretP) u,
                        @sa_cut _ _ _ (amf_sample pgl27_word_family R secretP) u))
      (sa_sampleP (amf_sample pgl27_word_family R secretP))
    = Parg `x rho.
Proof. by do 2 eexists; exact: fdistmap_prodr. Qed.

(** The argument factor is the model's own run-argument reader, so the
    decoding B1 asks for is the identity at this model. *)
Lemma pgl27_word_arg_readE (R : realType) (secretP : R.-fdist bool)
    (u : bool * (200.-tuple 'I_5)) :
  @sa_arg _ _ _ (amf_sample pgl27_word_family R secretP) u = u.1.
Proof. exact: erefl. Qed.

(** The generic construction's number at this model is the number the
    hand-built proximity certificate carries: both are the word model's
    marginal-bound epsilon, two to the minus fortieth. *)
Lemma pgl27_word_proximity_eps_genericE (R : realType)
    (secretP : R.-fdist bool) :
  ipc_eps (pgl27_word_proximity_cert secretP)
  = sw_bound_eps (ic_b (pgl27_word_cert secretP)).
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The five-card one-cut model                                            *)
(******************************************************************************)

(** Kim's one-cut model draws the committed pair uniformly and the rotation
    from the biased weight, the two apart, and its cut is a map of the
    rotation alone: B1's hypothesis holds there with the uniform pair as the
    argument factor. *)
Lemma kim_biased_arg_cut_prod (R : realType) (idx : unit) :
  exists (Parg : R.-fdist (bool * bool))
         (rho : R.-fdist (pgg_gT (mp_M (instance_profile five_card_algebra)))),
    fdistmap (fun u => (@sa_arg _ _ _ (amf_sample kim_biased_family R idx) u,
                        @sa_cut _ _ _ (amf_sample kim_biased_family R idx) u))
      (sa_sampleP (amf_sample kim_biased_family R idx))
    = Parg `x rho.
Proof.
do 2 eexists.
exact: (@fdistmap_prodr R _ _ _ _ _
          (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)).
Qed.

Lemma kim_biased_arg_readE (R : realType) (idx : unit)
    (u : five_card_leakage.Omega) :
  @sa_arg _ _ _ (amf_sample kim_biased_family R idx) u = five_card_sample_arg u.
Proof. exact: erefl. Qed.

(** The two numbers at this model are not the same. The hand-built
    certificate carries one fiftieth, proved from an exact computation of the
    one-cut distance, while the generic construction carries the spectral
    marginal bound the input-indistinguishability certificate was built on,
    the square root of five over eighty. *)
Lemma kim_biased_proximity_epsE (R : realType) (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx) = 1 / 50 :> R.
Proof. exact: erefl. Qed.

Lemma kim_biased_indistinguishability_epsE (R : realType) (idx : unit) :
  sw_bound_eps (ic_b (kim_biased_cert R idx)) = Num.sqrt 5%:R * (1 / 80) :> R.
Proof. exact: kim_biased_epsE. Qed.

(** The generic construction is the looser of the two at this model. *)
Lemma kim_biased_proximity_eps_generic_le (R : realType) (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx)
  <= sw_bound_eps (ic_b (kim_biased_cert R idx)).
Proof.
rewrite kim_biased_proximity_epsE kim_biased_indistinguishability_epsE.
have H2 : 2%:R <= Num.sqrt 5%:R :> R.
  rewrite -(@ler_pXn2r R 2 isT).
  2: by rewrite nnegrE ler0n.
  2: by rewrite nnegrE sqrtr_ge0.
  by rewrite sqr_sqrtr ?ler0n // -natrX ler_nat.
by lra.
Qed.
