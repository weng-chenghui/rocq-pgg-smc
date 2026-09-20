(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* r_framework: a proposition stated at a reader, and a one-seat marginal     *)
(* bound that is not security evidence                                        *)
(*                                                                            *)
(* PROBE FILE. Nothing permanent requires it. Ledger rows R1, R2, R3, R6      *)
(* (framework part), R8 (definitions) and R9 of                               *)
(* notes/20260920-readers-and-marginal-bounds-probe-design.md.                *)
(*                                                                            *)
(* Every proposition the Tableau states today is about one reader of an       *)
(* execution, a coalition's static endpoint reading. The tree proves the same *)
(* kind of statement about other readers of the same execution, and the       *)
(* framework has no name for them. A static reader is that missing name: a    *)
(* family of finite-valued functions of the run argument and the cut, indexed *)
(* by the coalition. The coalition's reading is one of them; a coalition's    *)
(* content trace is another; one seat's content is a third. The propositions  *)
(* below are the framework's propositions with the reader left free, and the  *)
(* framework's own propositions are their values at the canonical reader.     *)
(******************************************************************************)

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


(******************************************************************************)
(*     R1: a static reader of an execution                                    *)
(******************************************************************************)

Section static_reader.

Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.

Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.
Local Notation cards := 'I_(pgg_N' (mp_M (instance_profile A))).+1.

(* A static reader of an execution: for each coalition, a finite type and a
   function reading the run argument and the cut into it. What a reader omits
   is the interpreter state: a static reader sees the run argument and the
   shuffle and nothing of the messages the run exchanged, which is why a
   statement made at a reader is a statement about a group action. The value
   type depends on the coalition because a coalition of a different size reads
   a different amount. *)
Record StaticReader := MkStaticReader {
  sr_T : {set seats} -> finType ;
  sr_read : forall C : {set seats},
    ex_inputT E -> pgg_gT (mp_M (instance_profile A)) -> sr_T C }.

(* The canonical static reader: a coalition's static endpoint reading. It is
   the reader every proposition of the Tableau is about today, and the reader
   the link lemma of the Sampled level identifies with the executed coalition
   view. *)
Definition coalition_reading_reader : StaticReader :=
  @MkStaticReader (fun _ => [the finType of {ffun seats -> cards}])
    (@static_coalition_obs A E).

(* The value type of the canonical reader is the finite type of seat-indexed
   card positions, at every coalition. *)
Lemma coalition_reading_readerTE (C : {set seats}) :
  sr_T coalition_reading_reader C = [the finType of {ffun seats -> cards}].
Proof. exact: erefl. Qed.

(* The canonical reader reads by the framework's own static coalition
   reading. *)
Lemma coalition_reading_readE (C : {set seats}) (x : ex_inputT E)
    (g : pgg_gT (mp_M (instance_profile A))) :
  sr_read coalition_reading_reader C x g = static_coalition_obs C x g.
Proof. exact: erefl. Qed.

End static_reader.

Arguments StaticReader {A} E.
Arguments sr_T {A E}.
Arguments sr_read {A E}.
Arguments coalition_reading_reader {A} E.


(******************************************************************************)
(*     R2, R3: the input-indistinguishability proposition at a reader         *)
(******************************************************************************)

Section reader_propositions.

Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.

(* The input-indistinguishability proposition at a reader r: below the privacy
   threshold, two run arguments give readings of the model's own cut law
   within variation distance c. It is the framework's proposition with the
   coalition's reading replaced by r, so the attack model is unchanged, a
   static coalition of fewer than k seats, and what changes is what that
   coalition is granted to see. A finer reader makes the statement stronger:
   the same number bounds a larger distance. *)
Definition ReaderIndistinguishabilityPropAt (r : StaticReader E) (c : R)
    : Prop :=
  forall (C : {set seats}) (x x' : ex_inputT E),
    (#|C| < profile_k (instance_profile A))%N ->
    var_dist (fdistmap (sr_read r C x) (sa_cut_dist sa))
             (fdistmap (sr_read r C x') (sa_cut_dist sa))
    <= c.

(* At the canonical reader the proposition at a reader is the framework's
   input-indistinguishability proposition, at every certificate and every
   number. The framework's proposition therefore states nothing the reader
   form does not, and nothing the framework proves today changes. *)
Lemma reader_indistinguishability_canonicalE
    (cert : IndistinguishabilityCert sa) (c : R) :
  ReaderIndistinguishabilityPropAt (coalition_reading_reader E) c
  = IndistinguishabilityPropAt cert c.
Proof. exact: erefl. Qed.

(* Post-processing: when reader r' is a coalitionwise function of reader r,
   the proposition at r gives the proposition at r' at the same number. This
   is the data processing inequality for the sum of absolute differences, and
   it is what relates a number published about a coalition's content trace to
   a number about its endpoint reading whenever one of the two determines the
   other. *)
Lemma reader_indistinguishability_postprocessing
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
(* A repeat rewrite with fdistmap_comp does not terminate here: its left side
   matches the image of any reader, so the second pass unifies the reader
   itself with a composition. Each side is rewritten once, at its own
   instance. *)
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
(*     R6: exact independence at a reader                                     *)
(******************************************************************************)

(* Exact independence at a reader r: below the privacy threshold, the
   coalition's reading through r of the model's own run argument and cut is
   independent of the secret. Independence and not a numeric bound, as in the
   framework's exact-independence witness, so the entropy forms the framework
   derives from that witness are available at any reader satisfying this. *)
Definition ReaderExactPropAt (r : StaticReader E) (secretT : finType)
    (secret : {RV (sa_sampleP sa) -> secretT}) : Prop :=
  forall C : {set seats},
    (#|C| < profile_k (instance_profile A))%N ->
    sa_sampleP sa |= (fun u => sr_read r C (sa.(sa_arg) u) (sa.(sa_cut) u))
                     _|_ secret.

(* An exact-independence witness is exact independence at the canonical
   reader, with no proof: the witness's independence field is that
   proposition. *)
Definition reader_exact_of_witness (w : ExactWitness sa)
  : ReaderExactPropAt (coalition_reading_reader E) (ew_secret w) :=
  @ew_indep _ _ _ _ w.

(* Exact independence at the canonical reader gives the independence conjunct
   of the framework's exact-independence proposition, along the link lemma of
   the Sampled level. The link lemma is the only thing between them: the
   framework states independence of the executed coalition view and the reader
   form states it of the static reading. *)
Lemma reader_exact_executed (secretT : finType)
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


(******************************************************************************)
(*     R8: one-seat marginal bounds, which are not security evidence          *)
(******************************************************************************)

(* A one-seat marginal bound: the law of seat i's executed endpoint under the
   model is within c of a named ideal law. It mentions no coalition, no second
   run argument and no secret, so it is not a statement about what an
   adversary distinguishes; it compares one model's one-seat law with one
   named law and says nothing more. It carries no constructor of the
   framework's security evidence for that reason. *)
Definition SeatMarginalPropAt (i : seats)
    (ideal : R.-fdist 'I_(pgg_N' (mp_M (instance_profile A))).+1) (c : R)
    : Prop :=
  var_dist (@sa_seat_dist R (instance_profile A) (instance_exec E) sa 0 i)
           ideal
  <= c.

(* A one-position marginal bound on the cut: the law of one finite reading of
   the model's cut is within c of a named ideal law. The reading is a function
   of the shuffle alone and not of the run argument, so this states less than
   the seat form: it is about the model's randomness and not about what any
   seat sees. Like the seat form it mentions no coalition, no second run
   argument and no secret. *)
Definition CutMarginalPropAt (T : finType)
    (read : pgg_gT (mp_M (instance_profile A)) -> T)
    (ideal : R.-fdist T) (c : R) : Prop :=
  var_dist (fdistmap read (sa_cut_dist sa)) ideal <= c.


(******************************************************************************)
(*     R9: a one-seat marginal bound at two, and what it does not imply       *)
(******************************************************************************)

(* Every model and every ideal law satisfy the one-seat marginal bound at two,
   the sum of absolute differences between two laws on a finite carrier being
   at most two. The number a one-seat marginal bound publishes is therefore
   the whole of what it says, and a bound at or above two says nothing. *)
Lemma seat_marginal_at_two (i : seats)
    (ideal : R.-fdist 'I_(pgg_N' (mp_M (instance_profile A))).+1) :
  SeatMarginalPropAt i ideal 2%:R.
Proof. exact: var_dist_le2. Qed.

(* The same at the cut form. *)
Lemma cut_marginal_at_two (T : finType)
    (read : pgg_gT (mp_M (instance_profile A)) -> T) (ideal : R.-fdist T) :
  CutMarginalPropAt read ideal 2%:R.
Proof. exact: var_dist_le2. Qed.

End reader_propositions.

Arguments ReaderIndistinguishabilityPropAt {R A E} sa r c.
Arguments ReaderExactPropAt {R A E} sa r {secretT} secret.
Arguments SeatMarginalPropAt {R A E} sa i ideal c.
Arguments CutMarginalPropAt {R A E} sa {T} read ideal c.
Arguments seat_marginal_at_two {R A E} sa i ideal.
Arguments reader_indistinguishability_postprocessing {R A E sa} r r' f Hf c.


(******************************************************************************)
(*     R9, second half: a one-seat marginal bound is refused as evidence      *)
(******************************************************************************)

Section marginal_is_not_evidence.

Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.

(* A proof of a one-seat marginal bound is refused where the framework's
   input-indistinguishability proposition is expected. The two propositions
   are not comparable statements: one compares one law with one named law and
   the other compares two laws the same model gives at two run arguments. *)
Fail Check (fun (i : seats)
                (ideal : R.-fdist 'I_(pgg_N' (mp_M (instance_profile A))).+1)
                (cert : IndistinguishabilityCert sa) =>
  (seat_marginal_at_two sa i ideal
     : IndistinguishabilityPropAt cert 2%:R)).

(* The same proof is refused where exact independence at the canonical reader
   is expected. A one-seat marginal bound names no secret, so there is no
   secret for it to be independent of. *)
Fail Check (fun (i : seats)
                (ideal : R.-fdist 'I_(pgg_N' (mp_M (instance_profile A))).+1)
                (secretT : finType)
                (secret : {RV (sa_sampleP sa) -> secretT}) =>
  (seat_marginal_at_two sa i ideal
     : ReaderExactPropAt sa (coalition_reading_reader E) secret)).

End marginal_is_not_evidence.


(******************************************************************************)
(*     R3 mutation: the factorisation hypothesis is load-bearing              *)
(******************************************************************************)

Section postprocessing_mutation.

Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).

Local Notation seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1.

(* At a reader that is not the canonical one the equation of R2 is refused:
   the framework's proposition is the reader form at one reader and not at
   every reader, so generalising over the reader is not a renaming. *)
Fail Definition canonicalE_at_another_reader
    (r : StaticReader E) (cert : IndistinguishabilityCert sa) (c : R)
    : ReaderIndistinguishabilityPropAt sa r c
      = IndistinguishabilityPropAt cert c :=
  ltac:(exact: erefl).

(* Without the factorisation hypothesis the same proof script does not close
   the goal: the two readers' pushforwards are laws on unrelated carriers and
   the data processing inequality has nothing to apply to. *)
Fail Definition postprocessing_without_factorisation
    (r r' : StaticReader E) (c : R)
    (H : ReaderIndistinguishabilityPropAt sa r c)
    : ReaderIndistinguishabilityPropAt sa r' c :=
  ltac:(move=> C x x' HC;
        apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _));
        exact: H).

End postprocessing_mutation.
