(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgg_tableau_reading: what one reading of a coalition's endpoints says      *)
(*                      about another                                         *)
(*                                                                            *)
(* A reading of a coalition's endpoints is CoalitionReading of                *)
(* manifest/pgg_tableau.v, and the propositions of the framework are stated   *)
(* at the reading their evidence carries. This file holds what relates two    *)
(* readings of one model.                                                     *)
(*                                                                            *)
(* One reading factors through another when a coalitionwise map sends what    *)
(* the finer grants to what the coarser grants. Along such a map the two      *)
(* distance properties travel in opposite directions, and saying which is     *)
(* the whole content of the file. An input-indistinguishability bound travels *)
(* from the finer reading to the coarser one, which is the data processing    *)
(* inequality: granting a coalition less cannot separate two run arguments    *)
(* further. Input DISTINGUISHABILITY travels the other way, from the coarser  *)
(* to the finer: a coalition granted more still tells the two arguments       *)
(* apart. The coalition's own endpoints are the finest reading of all, every  *)
(* reading factoring through them, so every obstruction is an obstruction     *)
(* there.                                                                     *)
(*                                                                            *)
(* Exact independence at a reading is an independence and not a numeric       *)
(* bound, and an exact-independence witness is that proposition at its own    *)
(* reading with no proof.                                                     *)
(*                                                                            *)
(* Every number below bounds a sum of absolute differences, twice the total   *)
(* variation distance of the literature, so a distinguisher's advantage is at *)
(* most half of it. Naming a reading leaves the attack model as it is, a      *)
(* static coalition of fewer than profile_k seats, and changes what that      *)
(* coalition is granted to see. A reading is not security evidence: what      *)
(* certifies a security property is a program.                                *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   reading_factors            == a coalitionwise map from one reading to    *)
(*                                 another                                    *)
(*   ReadingExactIndependence   == independence of a reading from the secret  *)
(*                                 below the privacy threshold                *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   reading_factors_coalition_endpoint_reading                               *)
(*                              == every reading factors through the          *)
(*                                 coalition's own endpoints                  *)
(*   reading_indistinguishability_postprocessing                              *)
(*                              == a bound travels to a reading that factors  *)
(*                                 through the one it was proved at           *)
(*   input_distinguishability_prop_finer                                      *)
(*                              == an obstruction travels the other way,      *)
(*                                 at the same number, the same coalition     *)
(*                                 and the same two run arguments             *)
(*   input_distinguishability_prop_coalition_endpoint_reading                 *)
(*                              == so every obstruction is one at the         *)
(*                                 coalition's own endpoints                  *)
(*   indistinguishability_number_ge_across_readings                           *)
(*                              == an obstruction at a reading and a          *)
(*                                 certificate at a finer one bound each      *)
(*                                 other                                      *)
(*   exact_independence_of_witness                                            *)
(*                              == a witness is exact independence at its     *)
(*                                 own reading                                *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_reconstruct Require Import algebraic_rigidity pgg_sharing_framework.
From pgg_smc Require Import pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(******************************************************************************)
(*     One reading factoring through another                                  *)
(******************************************************************************)

Section reading_factorisation.

Variable A : PGGAlgebraic.

Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.
Local Notation cards := 'I_(pgg_N' (mp_M (instance_profile A))).+1.

(* A reading r' factors through a reading r when a coalitionwise map sends
   what r grants to what r' grants. It is the hypothesis both transport
   lemmas below take, stated on the readings and not on one model, so a
   factorisation proved once serves every model of the instance. *)
Definition reading_factors (r r' : CoalitionReading A)
    (f : forall C : {set seats}, @cr_readT A r C -> @cr_readT A r' C) : Prop :=
  forall (C : {set seats}) (v : {ffun seats -> cards}),
    @cr_read A r' C v = f C (@cr_read A r C v).

(* Every reading factors through the coalition's own endpoints, the map
   being the reading itself. The endpoint reading is therefore the finest
   one, and the direction of both transport lemmas is fixed by that. *)
Lemma reading_factors_coalition_endpoint_reading (r : CoalitionReading A) :
  @reading_factors (coalition_endpoint_reading A) r (@cr_read A r).
Proof. by []. Qed.

End reading_factorisation.

Arguments reading_factors {A} r r' f.

(******************************************************************************)
(*     What travels between two readings of one model                         *)
(******************************************************************************)

Section reading_transport.

Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.

(* An input-indistinguishability bound proved at a reading holds at every
   reading that factors through it, at the same number. This is the data
   processing inequality for the sum of absolute differences: granting a
   coalition less cannot separate two run arguments further. It transports a
   bound and produces none. *)
Lemma reading_indistinguishability_postprocessing (r r' : CoalitionReading A)
    (f : forall C : {set seats}, @cr_readT A r C -> @cr_readT A r' C)
    (Hf : reading_factors r r' f) (c : R) :
  ReadingIndistinguishabilityPropAt sa r c ->
  ReadingIndistinguishabilityPropAt sa r' c.
Proof.
move=> H C x x' HC.
(* a repeat rewrite with fdistmap_comp does not terminate here: its left side
   matches the image of any reading, so the second pass unifies the reading
   itself with a composition. Each side is rewritten once, at its own
   instance *)
have Hlaw : forall y : ex_inputT E,
    fdistmap (fun g => @cr_read A r' C (static_coalition_obs C y g))
      (sa_cut_dist sa)
    = fdistmap (f C)
        (fdistmap (fun g => @cr_read A r C (static_coalition_obs C y g))
           (sa_cut_dist sa)).
  move=> y.
  have -> : (fun g => @cr_read A r' C (static_coalition_obs C y g))
          = (f C) \o (fun g => @cr_read A r C (static_coalition_obs C y g)).
    by apply: boolp.funext => g; exact: Hf.
  by rewrite fdistmap_comp.
rewrite (Hlaw x) (Hlaw x').
apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)).
exact: H.
Qed.

(* Input distinguishability travels the other way. A model distinguishable
   at a reading is distinguishable at every reading the first factors
   through, at the same number, with the same coalition and the same two run
   arguments: a coalition granted MORE still tells the two arguments apart.
   The two lemmas are the two directions of one fact, and an obstruction is
   therefore a claim about the coarsest reading it is proved at. *)
Lemma input_distinguishability_prop_finer (r r' : CoalitionReading A)
    (f : forall C : {set seats}, @cr_readT A r C -> @cr_readT A r' C)
    (Hf : reading_factors r r' f) (c : R) :
  InputDistinguishabilityPropAt sa r' c -> InputDistinguishabilityPropAt sa r c.
Proof.
move=> [C [x [x' [HC Hge]]]]; exists C, x, x'; split=> //.
apply: (Order.POrderTheory.le_trans Hge).
have Hlaw : forall y : ex_inputT E,
    fdistmap (fun g => @cr_read A r' C (static_coalition_obs C y g))
      (sa_cut_dist sa)
    = fdistmap (f C)
        (fdistmap (fun g => @cr_read A r C (static_coalition_obs C y g))
           (sa_cut_dist sa)).
  move=> y.
  have -> : (fun g => @cr_read A r' C (static_coalition_obs C y g))
          = (f C) \o (fun g => @cr_read A r C (static_coalition_obs C y g)).
    by apply: boolp.funext => g; exact: Hf.
  by rewrite fdistmap_comp.
rewrite (Hlaw x) (Hlaw x'); exact: var_dist_fdistmap.
Qed.

(* Every obstruction is an obstruction at the coalition's own endpoints, that
   reading being the finest. A published obstruction at a coarse reading
   therefore refutes certificates at the endpoint reading too, which is the
   direction a designer has to read it in. *)
Corollary input_distinguishability_prop_coalition_endpoint_reading
    (r : CoalitionReading A) (c : R) :
  InputDistinguishabilityPropAt sa r c ->
  InputDistinguishabilityPropAt sa (coalition_endpoint_reading A) c.
Proof.
exact: (input_distinguishability_prop_finer
          (reading_factors_coalition_endpoint_reading r)).
Qed.

(* An obstruction at one reading and a certificate at a reading the first
   factors through bound each other. The number bound of the framework is
   this one at a single reading; a bound across two readings needs the
   factorisation and is this lemma, not that one. *)
Lemma indistinguishability_number_ge_across_readings
    (r r' : CoalitionReading A)
    (f : forall C : {set seats}, @cr_readT A r C -> @cr_readT A r' C)
    (Hf : reading_factors r r' f) (cert : IndistinguishabilityCert sa r)
    (c c' : R) :
  InputDistinguishabilityPropAt sa r' c ->
  IndistinguishabilityPropAt cert c' -> c <= c'.
Proof.
move=> Hd Hp.
exact: (indistinguishability_number_ge_of_input_distinguishability
          (input_distinguishability_prop_finer Hf Hd) Hp).
Qed.

(******************************************************************************)
(*     Exact independence at a reading                                        *)
(******************************************************************************)

(* Exact independence at a reading r: below the privacy threshold, the
   coalition's reading through r of the model's own run argument and cut is
   independent of the secret. It is an independence and not a numeric bound.
   The framework's entropy forms sit inside ExactProp, derived there from
   independence of the executed coalition view, which this proposition
   reaches along the link lemma of the Sampled level; none of those forms is
   restated here. *)
Definition ReadingExactIndependence (r : CoalitionReading A)
    (secretT : finType) (secret : {RV (sa_sampleP sa) -> secretT}) : Prop :=
  forall C : {set seats},
    (#|C| < profile_k (instance_profile A))%N ->
    sa_sampleP sa
    |= (fun u => @cr_read A r C
                   (static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u)))
       _|_ secret.

(* An exact-independence witness is exact independence at its own reading,
   with no proof: the witness's independence field is that proposition. *)
Definition exact_independence_of_witness (r : CoalitionReading A)
    (w : ExactWitness sa r)
  : ReadingExactIndependence r (ew_secret w) :=
  @ew_indep _ _ _ _ _ w.

End reading_transport.

Arguments ReadingExactIndependence {R A E} sa r {secretT} secret.
Arguments reading_indistinguishability_postprocessing {R A E sa} r r' f Hf c.
Arguments input_distinguishability_prop_finer {R A E sa} r r' f Hf c.
