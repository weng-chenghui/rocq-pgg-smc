(* P8 arm-relations probe, ledger rows B1 to B5 and B7.                       *)
(*                                                                            *)
(* An input-indistinguishability certificate carries a cut law, an ideal cut  *)
(* law within its own number of that one, and the constancy of the ideal      *)
(* reading in the run argument. When the model draws its run argument         *)
(* independently of its cut, those three fields build a proximity certificate *)
(* over the same model, and the proximity arm's proposition holds at the      *)
(* certificate's marginal-bound number once rather than twice.                *)
(*                                                                            *)
(* Scope. The comparison is average-case over the prior on the run argument   *)
(* and concerns one run. var_dist is the sum of absolute differences, twice   *)
(* the literature's total variation distance, so a distinguisher's advantage  *)
(* is at most half of any number here. A model whose cut depends on its run   *)
(* argument is outside all of this: the independence is a hypothesis on the   *)
(* model, not a theorem about it.                                             *)
(*                                                                            *)
(* Departure from the spec's B1 and B2. The spec writes the independence      *)
(* hypothesis as an equation between fdistmap along u |-> (sa_arg u, sa_cut   *)
(* u) and a product, and the ideal adapter's sample space as ex_inputT E *    *)
(* pgg_gT _. Neither typechecks: ex_inputT E is a bare Type, while fdistmap   *)
(* needs a finite codomain and sa_sampleT needs a finType. The hypothesis is  *)
(* therefore stated on a finite reading arg_read of the sample point together *)
(* with a decoding arg_decode back into ex_inputT E that agrees with sa_arg,  *)
(* which is the shape both production models already have.                    *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import var_dist_joint_law.
From pgg_reconstruct Require Import algebraic_rigidity.
From pgg_smc Require Import pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     A reading whose law does not depend on the first coordinate            *)
(******************************************************************************)

Section reading_with_a_constant_conditional_law.
Variable R : realType.
Variables T G V : finType.
Variables (PT : R.-fdist T) (Q : R.-fdist G) (f : T -> G -> V).

(** The mass a product law puts on one value of the reading and one value of
    the first coordinate: the mass of that coordinate times the mass its own
    reading law puts on the value. *)
Lemma sum_reading_fibreE (v : V) (x : T) :
  \sum_(z : T * G | (f z.1 z.2 == v) && (z.1 == x)) PT z.1 * Q z.2
  = PT x * fdistmap (f x) Q v.
Proof.
rewrite (reindex_onto (fun g : G => (x, g)) snd) /=;
  last by case=> a g /= /andP[_ /eqP ->].
rewrite -big_distrr /=; congr (_ * _).
by rewrite fdistmapE; apply: eq_bigl => g; rewrite !inE /= !eqxx !andbT.
Qed.

(** The joint law of the reading and the first coordinate under a product
    law. *)
Lemma fdistmap_pair_arg_condE (v : V) (x : T) :
  fdistmap (fun z : T * G => (f z.1 z.2, z.1)) (PT `x Q) (v, x)
  = PT x * fdistmap (f x) Q v.
Proof.
rewrite fdistmapE -sum_reading_fibreE; apply: eq_big.
- by case=> a g; rewrite !inE /= xpair_eqE.
- by move=> i _; rewrite fdist_prodE.
Qed.

(** The law of the reading alone under a product law: the mixture of its
    conditional laws over the first coordinate. *)
Lemma fdistmap_reading_mixtureE (v : V) :
  fdistmap (fun z : T * G => f z.1 z.2) (PT `x Q) v
  = \sum_(x : T) PT x * fdistmap (f x) Q v.
Proof.
rewrite fdistmapE.
rewrite (eq_big (fun z : T * G => f z.1 z.2 == v)
                (fun z : T * G => PT z.1 * Q z.2)); first last.
- by move=> i _; rewrite fdist_prodE.
- by case=> a g; rewrite !inE.
rewrite (partition_big fst xpredT) //=.
by apply: eq_bigr => x _; exact: sum_reading_fibreE.
Qed.

(** A reading whose conditional law does not depend on the first coordinate is
    independent of that coordinate: the joint law is the product of the two
    marginals. This is the mathematics of the input-indistinguishability
    certificate's constancy field, read on the ideal model whose run argument
    is drawn independently of its cut. *)
Lemma fdistmap_pair_arg_prodE :
  (forall x x' : T, fdistmap (f x) Q = fdistmap (f x') Q) ->
  fdistmap (fun z : T * G => (f z.1 z.2, z.1)) (PT `x Q)
  = (fdistmap (fun z : T * G => f z.1 z.2) (PT `x Q)) `x PT.
Proof.
move=> Hc; apply/fdist_ext => -[v x].
have Hf1 : \sum_(x' : T) PT x' = 1.
  by rewrite -(FDist.f1 PT); apply: eq_bigl => a; rewrite inE.
rewrite fdist_prodE /= fdistmap_pair_arg_condE fdistmap_reading_mixtureE.
under eq_bigr do rewrite (Hc _ x).
by rewrite -big_distrl /= Hf1 mul1r mulrC.
Qed.

End reading_with_a_constant_conditional_law.

(******************************************************************************)
(*     B1 to B5 over a model whose cut is drawn apart from its argument       *)
(******************************************************************************)

Section proximity_from_indistinguishability.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

(* The finite reading of the model's run argument, and the decoding back into
   the execution's run-argument carrier. ex_inputT E is a bare Type, so the
   run argument itself carries no law; what a product hypothesis can be stated
   on is a finite reading of the sample point that determines it. *)
Variable argT : finType.
Variable arg_decode : argT -> ex_inputT E.
Variable arg_read : sa_sampleT sa -> argT.
Hypothesis Harg : forall u : sa_sampleT sa,
  sa.(sa_arg) u = arg_decode (arg_read u).

Variable Parg : R.-fdist argT.
Variable rho : R.-fdist (pgg_gT (mp_M (instance_profile A))).

(* B1's hypothesis: the model draws its run argument independently of its cut.
   A model whose cut depends on the run argument does not satisfy it and lies
   outside everything below. *)
Hypothesis Hprod :
  fdistmap (fun u => (arg_read u, sa.(sa_cut) u)) (sa_sampleP sa)
  = Parg `x rho.

(** B1. Under that hypothesis the model's cut law is the product's second
    factor. *)
Lemma sa_cut_dist_of_prodE : sa_cut_dist sa = rho.
Proof.
rewrite /sa_cut_dist -(fdist_prod_snd Parg rho) -Hprod fdistmap_comp.
exact: erefl.
Qed.

(* The ideal cut law and its constancy in the run argument, the two fields an
   input-indistinguishability certificate carries beside its number. *)
Variable rho0 : R.-fdist (pgg_gT (mp_M (instance_profile A))).
Hypothesis Hconst :
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| < profile_k (instance_profile A))%N ->
    forall x x' : ex_inputT E,
      fdistmap (static_coalition_obs C x) rho0
      = fdistmap (static_coalition_obs C x') rho0.

(** B2. The ideal model: the same execution run on a sample space that draws
    the run argument from the actual model's own prior and the cut from the
    ideal law, the two apart. It leaks nothing about the argument by
    construction, and that is what makes it a model whose privacy is proved
    rather than a bare law. *)
Definition ideal_product_adapter : SampleAdapter R (instance_exec E) :=
  @MkSampleAdapter R (instance_profile A) (instance_exec E)
    [the finType of (argT * pgg_gT (mp_M (instance_profile A)))%type]
    (Parg `x rho0) (fun z => arg_decode z.1) (fun z => z.2).

Lemma ideal_product_sampleP :
  sa_sampleP ideal_product_adapter = Parg `x rho0.
Proof. exact: erefl. Qed.

(** B2. Below the threshold the ideal model's coalition reading is
    independent of its run argument, because the constancy field says the
    reading's conditional law is one law. *)
Lemma ideal_product_joint_prodE
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  (#|C| < profile_k (instance_profile A))%N ->
  fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
              (static_coalition_obs C (arg_decode z.1) z.2, z.1))
    (Parg `x rho0)
  = (fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
                 static_coalition_obs C (arg_decode z.1) z.2) (Parg `x rho0))
    `x Parg.
Proof.
move=> HC.
exact: (@fdistmap_pair_arg_prodE R argT _ _ Parg rho0
  (fun (x : argT) (g : pgg_gT (mp_M (instance_profile A))) =>
     static_coalition_obs C (arg_decode x) g)
  (fun x x' => @Hconst C HC (arg_decode x) (arg_decode x'))).
Qed.

Lemma ideal_product_reading_indep
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  (#|C| < profile_k (instance_profile A))%N ->
  sa_sampleP ideal_product_adapter
  |= ((fun z => static_coalition_obs C (ideal_product_adapter.(sa_arg) z)
                  (ideal_product_adapter.(sa_cut) z))
      : {RV (sa_sampleP ideal_product_adapter)
           -> {ffun 'I_(pi_T' (mp_PI (instance_profile A))).+1
                 -> 'I_(pgg_N' (mp_M (instance_profile A))).+1}})
     _|_ ((fun z => z.1)
          : {RV (sa_sampleP ideal_product_adapter) -> argT}).
Proof.
move=> HC v x.
have Hfst : fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) => z.1)
              (Parg `x rho0) = Parg by exact: fdist_prod1.
rewrite -!dist_of_RVE.
transitivity
  (((fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
        static_coalition_obs C (arg_decode z.1) z.2) (Parg `x rho0))
    `x Parg) (v, x)).
  rewrite -(ideal_product_joint_prodE HC); exact: erefl.
rewrite fdist_prodE /=.
have Hfstx : Parg x
           = fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) => z.1)
               (Parg `x rho0) x by rewrite Hfst.
rewrite Hfstx; exact: erefl.
Qed.

(** B2. The ideal model's exact witness: its secret is its own run argument,
    and the independence above is the witness's whole content. *)
Definition ideal_product_witness : ExactWitness ideal_product_adapter :=
  @MkExactWitness R A E ideal_product_adapter argT
    ((fun z => z.1) : {RV (sa_sampleP ideal_product_adapter) -> argT})
    ideal_product_reading_indep.

(** B3. The two models' joint laws of a coalition's reading and the run
    argument are no further apart than their two cut laws. The two models
    share the prior on the run argument and read one function of the pair,
    so the distance on the cut group transfers by data processing. *)
Lemma joint_reading_arg_var_dist_le
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  var_dist
    (fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                           (sa.(sa_cut) u), arg_read u)) (sa_sampleP sa))
    (fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
                 (static_coalition_obs C (arg_decode z.1) z.2, z.1))
       (Parg `x rho0))
  <= var_dist rho rho0.
Proof.
have HL : fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                                (sa.(sa_cut) u), arg_read u)) (sa_sampleP sa)
        = fdistmap (fun z : argT * pgg_gT (mp_M (instance_profile A)) =>
                      (static_coalition_obs C (arg_decode z.1) z.2, z.1))
            (Parg `x rho).
  rewrite -Hprod fdistmap_comp; congr fdistmap.
  by apply: funext => u; rewrite Harg.
rewrite HL.
apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)).
by rewrite var_dist_prodR.
Qed.

(** B4. The distance field of the proximity certificate, at the
    input-indistinguishability certificate's marginal-bound number. The
    certificate's own two fields, the identification of its bound's law with
    the model's cut and the closeness of the ideal law, are what carry the
    number across. *)
Lemma proximity_close_of_indistinguishability
    (ic : IndistinguishabilityCert sa) (Hic : ic_ideal ic = rho0)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}) :
  (#|C| < profile_k (instance_profile A))%N ->
  var_dist
    (fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                           (sa.(sa_cut) u), arg_read u)) (sa_sampleP sa))
    (fdistmap (fun z => (static_coalition_obs C
                           (ideal_product_adapter.(sa_arg) z)
                           (ideal_product_adapter.(sa_cut) z),
                         ew_secret ideal_product_witness z))
       (sa_sampleP ideal_product_adapter))
  <= sw_bound_eps (ic_b ic).
Proof.
move=> _.
apply: (Order.POrderTheory.le_trans (joint_reading_arg_var_dist_le C)).
rewrite -Hic -sa_cut_dist_of_prodE -(ic_Hd ic).
exact: (ic_close ic).
Qed.

(** B4. The proximity certificate an input-indistinguishability certificate
    builds over a model that draws its cut apart from its run argument. Its
    ideal is the product model, its ideal secret the ideal's own run argument,
    its own secret the model's run argument, and its number the
    input-indistinguishability certificate's marginal-bound epsilon once. *)
Definition proximity_cert_of_indistinguishability
    (ic : IndistinguishabilityCert sa) (Hic : ic_ideal ic = rho0)
  : IdealProximityCert sa :=
  @MkIdealProximityCert R A E sa ideal_product_adapter ideal_product_witness
    (arg_read : {RV (sa_sampleP sa) -> argT})
    (sw_bound_eps (ic_b ic))
    (proximity_close_of_indistinguishability Hic).

(** B5. The proximity arm's proposition at that certificate, at the
    input-indistinguishability certificate's marginal-bound epsilon once. The
    same certificate's input-indistinguishability proposition is at that
    epsilon added to itself, since cert_eps is the sum of the two run
    arguments' terms, so the proximity reading of one certificate is the
    sharper of the two numbers by a factor of two. *)
Lemma proximity_prop_of_indistinguishability
    (ic : IndistinguishabilityCert sa) (Hic : ic_ideal ic = rho0)
    (Hendp : instance_endpoints_stmt E) :
  IdealProximityPropAt (proximity_cert_of_indistinguishability Hic)
    (sw_bound_eps (ic_b ic)).
Proof.
exact: (idealproximity_tail (proximity_cert_of_indistinguishability Hic)
  (fun C => @sa_coalition_viewE R (instance_profile A) (instance_exec E)
              sa 0 (ex_content_obs E) (fun u => Hendp _ _) C)
  (fun C => @sa_coalition_viewE R (instance_profile A) (instance_exec E)
              ideal_product_adapter 0 (ex_content_obs E)
              (fun u => Hendp _ _) C)).
Qed.

(** B7. The proposition B5 states is not closed by conversion: the two joint
    laws it compares are two laws, and the number is not read off either of
    them. With the guard removed the error is "No applicable tactic", the
    ssreflect closing tactic failing on the inequality, not a missing name. *)
Fail Definition proximity_prop_of_indistinguishability_by_conversion
    (ic : IndistinguishabilityCert sa) (Hic : ic_ideal ic = rho0)
  : IdealProximityPropAt (proximity_cert_of_indistinguishability Hic)
      (sw_bound_eps (ic_b ic))
  := ltac:(by []).

(** The two numbers over one certificate: the proximity arm reads it once,
    the input-indistinguishability arm twice. *)
Lemma proximity_eps_halves_cert_epsE (ic : IndistinguishabilityCert sa)
    (Hic : ic_ideal ic = rho0) :
  cert_eps ic = ipc_eps (proximity_cert_of_indistinguishability Hic)
                + ipc_eps (proximity_cert_of_indistinguishability Hic).
Proof. exact: erefl. Qed.

End proximity_from_indistinguishability.

Print Assumptions proximity_prop_of_indistinguishability.
