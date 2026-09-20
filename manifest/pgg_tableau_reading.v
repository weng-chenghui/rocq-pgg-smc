(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgg_tableau_reading: the framework's propositions with the reading left    *)
(*                      free                                                  *)
(*                                                                            *)
(* A static reading of an execution is a family of functions of the           *)
(* coalition, the run argument and the cut, valued in a finite type that may  *)
(* depend on the coalition. A coalition's static endpoint reading is one of   *)
(* them, and an instance whose cards carry a colour has a coarser one, the    *)
(* colours of the cards a coalition holds.                                    *)
(*                                                                            *)
(* Two propositions are stated here with the reading left free. The           *)
(* input-indistinguishability proposition at a reading is                     *)
(* IndistinguishabilityPropAt of manifest/pgg_tableau.v with the coalition's  *)
(* static reading replaced by the given one, and at that reading the two are  *)
(* one proposition, at every certificate and every number. Exact              *)
(* independence at a reading is one independence and not a numeric bound. At  *)
(* the coalition's static reading it is the independence field of an          *)
(* exact-independence witness, and it reaches ExactProp, which speaks of the  *)
(* executed coalition view, along the link lemma of the Sampled level.        *)
(*                                                                            *)
(* Every number below bounds a sum of absolute differences, twice the total   *)
(* variation distance of the literature, so a distinguisher's advantage is at *)
(* most half of it.                                                           *)
(*                                                                            *)
(* Naming a reading leaves the attack model as it is, a static coalition of   *)
(* fewer than profile_k seats, and changes what that coalition is granted to  *)
(* see. A reading is not security evidence: what certifies a security         *)
(* property is a program, with an exact-independence witness, an              *)
(* input-indistinguishability certificate or an ideal-proximity certificate.  *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   StaticReading              == a reading of an execution: a finite type   *)
(*                                 and a reading function per coalition       *)
(*   static_coalition_reading   == a coalition's static endpoint reading as   *)
(*                                 a reading                                  *)
(*   ReadingIndistinguishabilityPropAt                                        *)
(*                              == the input-indistinguishability             *)
(*                                 proposition stated at a reading            *)
(*   ReadingExactIndependence   == independence of a reading from the secret  *)
(*                                 below the privacy threshold                *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   static_coalition_readingTE == the value type of that reading is the      *)
(*                                 seat-indexed card positions                *)
(*   static_coalition_readE     == it reads by static_coalition_obs           *)
(*   reading_indistinguishability_static_coalitionE                           *)
(*                              == at that reading the proposition is the     *)
(*                                 framework's own                            *)
(*   reading_indistinguishability_postprocessing                              *)
(*                              == a factorisation carries the number to the  *)
(*                                 coarser reading                            *)
(*   exact_independence_of_witness                                            *)
(*                              == an exact-independence witness is exact     *)
(*                                 independence at that reading               *)
(*   exact_independence_executed_of_reading                                   *)
(*                              == along the link lemma it gives              *)
(*                                 independence of the executed view          *)
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
(*     A static reading of an execution                                       *)
(******************************************************************************)

Section static_reading.

Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.

Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.
Local Notation cards := 'I_(pgg_N' (mp_M (instance_profile A))).+1.

(* A static reading of an execution is a family of functions of the
   coalition, the run argument and the cut, valued in a finite type that may
   depend on the coalition. That is the whole of what the type constrains: it
   does not say that a reading is a group action, nor that it ignores the
   interpreter's messages. That a given reading is a function of the dealt
   deck and the cut alone is a theorem about it. The value type may depend on
   the coalition; both readings of this tree return a seat-indexed map at
   every coalition and do not use that freedom. *)
Record StaticReading := MkStaticReading {
  sr_readT : {set seats} -> finType ;
  sr_read : forall C : {set seats},
    ex_inputT E -> pgg_gT (mp_M (instance_profile A)) -> sr_readT C }.

(* A coalition's static endpoint reading as a reading. The
   input-indistinguishability proposition of the Tableau is stated at it; the
   exact-independence and the ideal-proximity propositions are stated at the
   executed coalition view, which the link lemma of the Sampled level
   identifies with it. *)
Definition static_coalition_reading : StaticReading :=
  @MkStaticReading (fun _ => [the finType of {ffun seats -> cards}])
    (@static_coalition_obs A E).

(* The value type of a coalition's static reading is the finite type of
   seat-indexed card positions, at every coalition. What a coalition reads is
   a whole seat-indexed record and not one seat's card. *)
Lemma static_coalition_readingTE (C : {set seats}) :
  sr_readT static_coalition_reading C
  = [the finType of {ffun seats -> cards}].
Proof. exact: erefl. Qed.

(* A coalition's static reading reads by static_coalition_obs, so a
   proposition stated at it is the framework's own proposition and not a
   second one. *)
Lemma static_coalition_readE (C : {set seats}) (x : ex_inputT E)
    (g : pgg_gT (mp_M (instance_profile A))) :
  sr_read static_coalition_reading C x g = static_coalition_obs C x g.
Proof. exact: erefl. Qed.

End static_reading.

Arguments StaticReading {A} E.
Arguments sr_readT {A E}.
Arguments sr_read {A E}.
Arguments static_coalition_reading {A} E.


(******************************************************************************)
(*     The input-indistinguishability proposition at a reading                *)
(******************************************************************************)

Section reading_propositions.

Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.

(* The input-indistinguishability proposition at a reading r: below the
   privacy threshold, two run arguments give readings of the model's own cut
   law within c. It is the framework's proposition with the coalition's static
   reading replaced by r, so the attack model is unchanged, a static coalition
   of fewer than profile_k seats, and what changes is what that coalition is
   granted to see. The number bounds a sum of absolute differences, twice the
   total variation distance of the literature, so a distinguisher's advantage
   is at most half of it. A reading through which another factors carries the
   same number to it. *)
Definition ReadingIndistinguishabilityPropAt (r : StaticReading E) (c : R)
    : Prop :=
  forall (C : {set seats}) (x x' : ex_inputT E),
    (#|C| < profile_k (instance_profile A))%N ->
    var_dist (fdistmap (sr_read r C x) (sa_cut_dist sa))
             (fdistmap (sr_read r C x') (sa_cut_dist sa))
    <= c.

(* At a coalition's static reading the proposition at a reading is the
   framework's input-indistinguishability proposition, at every certificate
   and every number. The framework's proposition therefore states nothing the
   reading form does not. *)
Lemma reading_indistinguishability_static_coalitionE
    (cert : IndistinguishabilityCert sa) (c : R) :
  ReadingIndistinguishabilityPropAt (static_coalition_reading E) c
  = IndistinguishabilityPropAt cert c.
Proof. exact: erefl. Qed.

(* Post-processing: when reading r' is a coalitionwise function of reading r,
   the proposition at r gives the proposition at r' at the same number. This
   is the data processing inequality for the sum of absolute differences, and
   it is what carries a number published about one reading of a run to a
   coarser reading of the same run. *)
Lemma reading_indistinguishability_postprocessing
    (r r' : StaticReading E)
    (f : forall C : {set seats}, sr_readT r C -> sr_readT r' C)
    (Hf : forall (C : {set seats}) (x : ex_inputT E)
                 (g : pgg_gT (mp_M (instance_profile A))),
            sr_read r' C x g = f C (sr_read r C x g))
    (c : R) :
  ReadingIndistinguishabilityPropAt r c ->
  ReadingIndistinguishabilityPropAt r' c.
Proof.
move=> H C x x' HC.
(* a repeat rewrite with fdistmap_comp does not terminate here: its left side
   matches the image of any reading, so the second pass unifies the reading
   itself with a composition. Each side is rewritten once, at its own
   instance *)
have Hlaw : forall y : ex_inputT E,
    fdistmap (sr_read r' C y) (sa_cut_dist sa)
    = fdistmap (f C) (fdistmap (sr_read r C y) (sa_cut_dist sa)).
  move=> y.
  have -> : sr_read r' C y = (f C) \o (sr_read r C y).
    by apply: boolp.funext => g; exact: Hf.
  by rewrite fdistmap_comp.
rewrite (Hlaw x) (Hlaw x').
apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)).
exact: H.
Qed.


(******************************************************************************)
(*     Exact independence at a reading                                        *)
(******************************************************************************)

(* Exact independence at a reading r: below the privacy threshold, the
   coalition's reading through r of the model's own run argument and cut is
   independent of the secret. It is an independence and not a numeric bound.
   The framework's entropy forms sit inside ExactProp, derived there from
   independence of the executed coalition view, which this proposition reaches
   at a coalition's static reading along the link lemma of the Sampled level;
   none of those forms is restated here. *)
Definition ReadingExactIndependence (r : StaticReading E) (secretT : finType)
    (secret : {RV (sa_sampleP sa) -> secretT}) : Prop :=
  forall C : {set seats},
    (#|C| < profile_k (instance_profile A))%N ->
    sa_sampleP sa |= (fun u => sr_read r C (sa.(sa_arg) u) (sa.(sa_cut) u))
                     _|_ secret.

(* An exact-independence witness is exact independence at a coalition's static
   reading, with no proof: the witness's independence field is that
   proposition. *)
Definition exact_independence_of_witness (w : ExactWitness sa)
  : ReadingExactIndependence (static_coalition_reading E) (ew_secret w) :=
  @ew_indep _ _ _ _ w.

(* Exact independence at a coalition's static reading gives the independence
   conjunct of the framework's exact-independence proposition, along the link
   lemma of the Sampled level. The link lemma is the only thing between them:
   the framework states independence of the executed coalition view and the
   reading form states it of the static reading. *)
Lemma exact_independence_executed_of_reading (secretT : finType)
    (secret : {RV (sa_sampleP sa) -> secretT})
    (Hview : forall C : {set seats},
       @sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C
       = (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u))) :
  ReadingExactIndependence (static_coalition_reading E) secret ->
  forall C : {set seats}, (#|C| < profile_k (instance_profile A))%N ->
    sa_sampleP sa
    |= (@sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C)
       _|_ secret.
Proof. by move=> H C HC; rewrite (Hview C); exact: H. Qed.

End reading_propositions.

Arguments ReadingIndistinguishabilityPropAt {R A E} sa r c.
Arguments ReadingExactIndependence {R A E} sa r {secretT} secret.
Arguments reading_indistinguishability_postprocessing {R A E sa} r r' f Hf c.
