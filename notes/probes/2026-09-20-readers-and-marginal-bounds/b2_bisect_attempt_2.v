(* PROBE bisect file 2 (attempt 2: ordinary proofs, read with -time): the remaining commands of r_framework.v, each
   Timeout-guarded, so the first offender is named. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_weighted_words.
From pgg_smc Require Import pgg_observed_execution pgg_sample_adapter.
From pgg_smc Require Import pgg_leakage_witness pgg_trace_secrecy.
From pgg_smc Require Import pgg_collusion_bound pgg_analysis_status.
From pgg_smc Require Import var_dist_supp.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import pgg_instance pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

Section static_reader.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.
Local Notation cards := 'I_(pgg_N' (mp_M (instance_profile A))).+1.

Record StaticReader := MkStaticReader {
  sr_T : {set seats} -> finType ;
  sr_read : forall C : {set seats},
    ex_inputT E -> pgg_gT (mp_M (instance_profile A)) -> sr_T C }.

Definition coalition_reading_reader : StaticReader :=
  @MkStaticReader (fun _ => [the finType of {ffun seats -> cards}])
    (@static_coalition_obs A E).

End static_reader.

Arguments StaticReader {A} E.
Arguments sr_T {A E}.
Arguments sr_read {A E}.
Arguments coalition_reading_reader {A} E.

Section reader_propositions.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).
Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.

Definition ReaderIndistinguishabilityPropAt (r : StaticReader E) (c : R)
    : Prop :=
  forall (C : {set seats}) (x x' : ex_inputT E),
    (#|C| < profile_k (instance_profile A))%N ->
    var_dist (fdistmap (sr_read r C x) (sa_cut_dist sa))
             (fdistmap (sr_read r C x') (sa_cut_dist sa))
    <= c.

(* c1: the post-processing law. *)
Lemma c1_postprocessing
    (r r' : StaticReader E)
    (f : forall C : {set seats}, sr_T r C -> sr_T r' C)
    (Hf : forall (C : {set seats}) (x : ex_inputT E)
                 (g : pgg_gT (mp_M (instance_profile A))),
            sr_read r' C x g = f C (sr_read r C x g))
    (c : R) :
  ReaderIndistinguishabilityPropAt r c ->
  ReaderIndistinguishabilityPropAt r' c.
Proof.
move=> H C x x' HC.
have Hfun : forall y : ex_inputT E,
    sr_read r' C y = (f C) \o (sr_read r C y).
  by move=> y; apply: boolp.funext => g; exact: Hf.
rewrite (Hfun x) (Hfun x') -!fdistmap_comp.
apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)).
exact: H.
Qed.

Definition ReaderExactPropAt (r : StaticReader E) (secretT : finType)
    (secret : {RV (sa_sampleP sa) -> secretT}) : Prop :=
  forall C : {set seats},
    (#|C| < profile_k (instance_profile A))%N ->
    sa_sampleP sa |= (fun u => sr_read r C (sa.(sa_arg) u) (sa.(sa_cut) u))
                     _|_ secret.

(* c2: the exact witness is exact independence at the canonical reader. *)
Definition c2_exact_of_witness (w : ExactWitness sa)
  : ReaderExactPropAt (coalition_reading_reader E) (ew_secret w) :=
  @ew_indep _ _ _ _ w.

(* c3: the link lemma carries it to the executed view. *)
Lemma c3_exact_executed (secretT : finType)
    (secret : {RV (sa_sampleP sa) -> secretT})
    (Hview : forall C : {set seats},
       @sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C
       = (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u))) :
  ReaderExactPropAt (coalition_reading_reader E) secret ->
  forall C : {set seats}, (#|C| < profile_k (instance_profile A))%N ->
    sa_sampleP sa
    |= (@sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C)
       _|_ secret.
Proof. by move=> H C HC; rewrite (Hview C); exact: H. Qed.

Definition SeatMarginalPropAt (i : seats)
    (ideal : R.-fdist 'I_(pgg_N' (mp_M (instance_profile A))).+1) (c : R)
    : Prop :=
  var_dist (@sa_seat_dist R (instance_profile A) (instance_exec E) sa 0 i)
           ideal
  <= c.

Definition CutMarginalPropAt (T : finType)
    (read : pgg_gT (mp_M (instance_profile A)) -> T)
    (ideal : R.-fdist T) (c : R) : Prop :=
  var_dist (fdistmap read (sa_cut_dist sa)) ideal <= c.

(* c4: every model and ideal satisfy the seat form at two. *)
Lemma c4_seat_at_two (i : seats)
    (ideal : R.-fdist 'I_(pgg_N' (mp_M (instance_profile A))).+1) :
  SeatMarginalPropAt i ideal 2%:R.
Proof. exact: var_dist_le2. Qed.

(* c5: the same at the cut form. *)
Lemma c5_cut_at_two (T : finType)
    (read : pgg_gT (mp_M (instance_profile A)) -> T) (ideal : R.-fdist T) :
  CutMarginalPropAt read ideal 2%:R.
Proof. exact: var_dist_le2. Qed.

End reader_propositions.

Arguments ReaderIndistinguishabilityPropAt {R A E} sa r c.
Arguments ReaderExactPropAt {R A E} sa r {secretT} secret.
Arguments SeatMarginalPropAt {R A E} sa i ideal c.
Arguments CutMarginalPropAt {R A E} sa {T} read ideal c.
Arguments c4_seat_at_two {R A E} sa i ideal.

Section refusals.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).
Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.

(* c6: refused where the framework's proposition is expected. *)
Fail Check (fun (i : seats)
                (ideal : R.-fdist 'I_(pgg_N' (mp_M (instance_profile A))).+1)
                (cert : IndistinguishabilityCert sa) =>
  (c4_seat_at_two sa i ideal : IndistinguishabilityPropAt cert 2%:R)).

(* c7: refused where exact independence is expected. *)
Fail Check (fun (i : seats)
                (ideal : R.-fdist 'I_(pgg_N' (mp_M (instance_profile A))).+1)
                (secretT : finType)
                (secret : {RV (sa_sampleP sa) -> secretT}) =>
  (c4_seat_at_two sa i ideal
     : ReaderExactPropAt sa (coalition_reading_reader E) secret)).

(* c8: the post-processing law without its factorisation hypothesis. *)
Fail Definition c8_no_factorisation
    (r r' : StaticReader E) (c : R)
    (H : ReaderIndistinguishabilityPropAt sa r c)
    : ReaderIndistinguishabilityPropAt sa r' c :=
  ltac:(move=> C x x' HC;
        apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _));
        exact: H).

End refusals.
