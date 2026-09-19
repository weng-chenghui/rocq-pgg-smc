(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Tableau: the row program of one protocol instance                          *)
(*                                                                            *)
(* A row of the analysis manifest is written here as a program. Its lines     *)
(* are statements; each one takes the data accumulated so far, the            *)
(* proposition proved about it so far, and one payload of its own, and        *)
(* returns the data raised one completion level. dealt_step carries the True  *)
(* of the two bottom levels forward, execute_step establishes the proposition *)
(* in its place, and the three above them extend it by one conjunct on the    *)
(* right, so from Sampled upwards it is a left-nested conjunction whose added *)
(* conjuncts are about the coalition's view. A reader who stops at any line   *)
(* knows exactly what has been proved there, and the named projections at the *)
(* bottom read those conjuncts back off a finished row.                       *)
(*                                                                            *)
(* There are six statements. dealt_step fixes the run argument to be the      *)
(* dealer's secret and chooses a fuel. execute_step adjoins the three run     *)
(* facts and reaches run correctness. sample_step adjoins an analysis model   *)
(* family and proves that the executed coalition reader is the static one,    *)
(* which is what moves the row from a claim about interpreter messages to a   *)
(* claim about a group action. certify_exact, certify_indistinguishability    *)
(* and certify_idealproximity adjoin a security witness of one arm. Each arm  *)
(* speaks only of a coalition below the privacy threshold, and the arms are   *)
(* not comparable statements: the exact arm concludes independence of the     *)
(* coalition's view from the secret, unconditionally and at every real field, *)
(* the input-indistinguishability arm concludes a variation distance between  *)
(* the readings of two run arguments, bounded by the certificate's            *)
(* marginal-bound epsilon twice, one for each argument, and the proximity arm *)
(* concludes a variation distance between the joint law of the coalition's    *)
(* view with the secret and the product of the two marginals of an ideal      *)
(* model whose own privacy is exact. A row commits to one arm and claims      *)
(* nothing about the rest, and security_arm_of names which arm a finished row *)
(* committed to.                                                              *)
(*                                                                            *)
(* The exact arm's and the proximity arm's propositions mention terms an      *)
(* instance chooses, so a row of either says as much as those terms say.      *)
(* ExactProp mentions the witness's ew_secret, and a constant ew_secret       *)
(* satisfies ew_indep at every coalition. IdealProximityPropAt mentions       *)
(* the certificate's ipc_secret and the two marginals of its ipc_ideal, and   *)
(* at an ipc_ideal that is the row's own adapter, with ipc_secret that        *)
(* adapter's witness's own secret, ipc_close compares one distribution with   *)
(* itself and holds at the number zero. The input-indistinguishability arm    *)
(* is different in kind: IndistinguishabilityPropAt mentions neither          *)
(* ic_ideal nor a secret, only the readings of the model's own cut law at     *)
(* two run arguments and the number bounding their distance, so ic_ideal      *)
(* is a means of proving it. ic_close holds ic_ideal within the marginal      *)
(* bound's epsilon of that bound's own law and ic_const asks a coalition      *)
(* below the threshold to read it the same at every two run arguments, and    *)
(* at some models no law satisfies both below a positive number.              *)
(*                                                                            *)
(* Each arm has one composition law, and those laws are where the mathematics *)
(* of the row sits. exact_tail transports a witness's independence from the   *)
(* direct computation to the view along the previous statement's link lemma,  *)
(* then derives the entropy forms by leakage_of_view_indep and the closure    *)
(* under deterministic post-processing by inde_RV_comp.                       *)
(* indistinguishability_tail feeds the certificate's cut-carrier distance and *)
(* its ideal constancy to var_dist_fdistmap_transfer. idealproximity_tail     *)
(* transports the certificate's distance between two joint laws to the        *)
(* executed readers of both models, along that link lemma taken once for each *)
(* model, and rewrites the ideal joint law as the product of its two          *)
(* marginals through the ideal witness's independence.                        *)
(*                                                                            *)
(* Two things stay outside the program. The mathematics of a particular       *)
(* instance never appears as a line: it enters as the witness or the          *)
(* certificate a certify statement takes, and once more as the payload of     *)
(* conclude, which for an input-indistinguishability or a proximity port is   *)
(* an inequality between the number the row's own certificate proved and the  *)
(* number the row publishes and for an exact port is nothing. And of the      *)
(* three terminals only conclude returns a tableau and only it has a step's   *)
(* shape, but it too is outside: it leaves the data and the arms untouched    *)
(* and moves the real an arm's proposition mentions to any upper bound of it. *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   ExactWitness           == the exact arm's security witness               *)
(*   IndistinguishabilityCert                                                 *)
(*                          == the input-indistinguishability arm's           *)
(*                             security certificate                           *)
(*   IdealProximityCert     == the proximity arm's security certificate       *)
(*   SecurityPort           == the arm an instance certifies                  *)
(*   SecurityArm            == which arm, with no witness or certificate      *)
(*   port_arm               == the arm a port commits to                      *)
(*   StackAt                == the data a row holds at one completion level   *)
(*   StackProp              == the proposition a row holds at one level       *)
(*   TableauAt              == data at a level with a proof about it          *)
(*   tableau_bind           == sequencing, written s ;;; f 'of' p             *)
(*   dealt_step             == the statement dealing a secret at a fuel       *)
(*   execute_step           == the statement adjoining the three run facts    *)
(*   sample_step            == the statement adjoining an analysis family     *)
(*   certify_exact          == the statement adjoining an exact witness       *)
(*   certify_indistinguishability                                             *)
(*                          == the statement adjoining an                     *)
(*                             input-indistinguishability certificate         *)
(*   certify_idealproximity == the statement adjoining a proximity            *)
(*                             certificate                                    *)
(*   conclude               == the terminal publishing an upper bound of the  *)
(*                             accumulated bound                              *)
(*   restate                == the terminal handing over a chosen proposition *)
(*   publish                == the terminal attaching the row's manifest row  *)
(*   PublishedRowAt         == a row's data, its manifest row and its theorem *)
(*   run_correct_of         == run correctness of a published row             *)
(*   view_identification_of == its link lemma, the view as the                *)
(*                             direct computation                             *)
(*   view_secrecy_of        == its security statement, exact-arm name         *)
(*   view_indistinguishability_of                                             *)
(*                          == the same statement, under the                  *)
(*                             input-indistinguishability arm's name          *)
(*   view_proximity_of      == the same statement, proximity-arm name         *)
(*   security_arm_of        == which arm a published row carries              *)
(*                                                                            *)
(* Key results:                                                               *)
(*   tableau_left_unit      == sequencing onto a built tableau is application *)
(*   exact_tail             == the exact arm's composition law                *)
(*   indistinguishability_tail                                                *)
(*                          == the input-indistinguishability arm's           *)
(*                             composition law                                *)
(*   idealproximity_tail    == the proximity arm's composition law            *)
(*   port_conclude          == a port's proposition at a number above its own *)
(*                             bound                                          *)
(*   certify_exact_armE     == the exact statement writes the exact arm       *)
(*   certify_indistinguishability_armE                                        *)
(*                          == the input-indistinguishability statement       *)
(*                             writes that arm                                *)
(*   certify_idealproximity_armE                                              *)
(*                          == the proximity statement writes the proximity   *)
(*                             arm                                            *)
(*   conclude_armE          == concluding a row leaves its arm alone          *)
(*   publish_armE           == publishing a row leaves its arm alone          *)
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
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import pgg_instance pgg_analysis_manifest.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     The security witnesses of the arms                                     *)
(******************************************************************************)

(* The exact arm's witness: a secret random variable on the sampled space,
   and, at every coalition below the privacy threshold, the independence of
   that coalition's static endpoint reading from it. Independence is the
   statement rather than a numeric leakage bound, and the entropy forms and
   the closure under post-processing are derived from it below, so an instance
   producing this record owes nothing further about mutual information. *)
Record ExactWitness (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) :=
  MkExactWitness {
    ew_secretT : finType ;
    ew_secret  : {RV (sa_sampleP sa) -> ew_secretT} ;
    ew_indep   : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
      (#|C| < profile_k (instance_profile A))%N ->
      sa_sampleP sa |= (fun u => static_coalition_obs C (sa.(sa_arg) u)
                                   (sa.(sa_cut) u)) _|_ ew_secret }.

(* The input-indistinguishability arm's certificate: a marginal bound on the
   instance's shuffle, the identification of the bound's law with the
   adapter's cut, an ideal cut law within that bound in variation distance,
   and the constancy, at every coalition below the privacy threshold, of the
   reading of the ideal cut in the run argument. Five fields and not the two
   of a marginal bound alone: the transfer inequality is stated on the cut
   carrier, where it needs both a distance and the ideal constancy, and a
   per-position marginal bound holds neither. *)
Record IndistinguishabilityCert (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) :=
  MkIndistinguishabilityCert {
    ic_b : ShuffleMarginalBound R (instance_M A) ;
    ic_Hd : sw_rho_dist ic_b = sa_cut_dist sa ;
    ic_ideal : R.-fdist (pgg_gT (mp_M (instance_profile A))) ;
    ic_close : var_dist (sw_rho_dist ic_b) ic_ideal <= sw_bound_eps ic_b ;
    ic_const : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
        (#|C| < profile_k (instance_profile A))%N ->
        forall x x' : ex_inputT E,
          fdistmap (static_coalition_obs C x) ic_ideal
          = fdistmap (static_coalition_obs C x') ic_ideal }.

(* The proximity arm's certificate: a second sample adapter over the row's own
   execution, standing for the ideal run; an exact witness for that ideal,
   which is what makes the ideal a model whose own privacy is proved and not a
   bare law; the actual model's secret, typed at the carrier the ideal's
   witness names, so that the two models speak of one secret; a number; and,
   at every coalition below the privacy threshold, that number as a bound on
   the variation distance between the two models' joint laws of the
   coalition's reading and the secret. The comparison is an average over the
   run argument of each model and not a statement at a fixed run argument, and
   the number is an upper bound the instance chooses on what the actual model
   loses against an execution that leaks nothing, not a quantity the record
   determines: any number at which ipc_close is provable is a legal field, so a
   certificate says as much as its number is small and no more. *)
Record IdealProximityCert (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) :=
  MkIdealProximityCert {
    ipc_ideal   : SampleAdapter R (instance_exec E) ;
    ipc_witness : ExactWitness ipc_ideal ;
    ipc_secret  : {RV (sa_sampleP sa) -> ew_secretT ipc_witness} ;
    ipc_eps     : R ;
    ipc_close   : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
      (#|C| < profile_k (instance_profile A))%N ->
      var_dist
        (fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                               (sa.(sa_cut) u), ipc_secret u))
           (sa_sampleP sa))
        (fdistmap (fun u => (static_coalition_obs C (ipc_ideal.(sa_arg) u)
                               (ipc_ideal.(sa_cut) u),
                             ew_secret ipc_witness u))
           (sa_sampleP ipc_ideal))
      <= ipc_eps }.

(* Which arm an instance certifies, at one real field and one index of its
   analysis family. A row commits to an arm here, and the proposition it
   carries from that line on is that arm's own; the arms are different
   statements about a coalition, so a row certifying input
   indistinguishability asserts nothing about mutual information. *)
Variant SecurityPort (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) : Type :=
  | ExactIndependence of ExactWitness sa
  | InputIndistinguishability of IndistinguishabilityCert sa
  | IdealProximity of IdealProximityCert sa.

(* Which arm a row commits to, with the witness and the
   certificate forgotten. A published row's manifest row records the path the
   row ran and no theorem, so two rows over one model and one pair of statuses
   are one manifest row; the arm is where they differ, and a reader asking
   what a finished row proved about a coalition reads this and not the
   manifest. *)
Variant SecurityArm :=
  ExactIndependenceArm | InputIndistinguishabilityArm | IdealProximityArm.

(* The arm a port commits to, with its witness or its certificate forgotten.
   The constructor alone decides the answer, so a row's arm is fixed by the
   certify statement that wrote the port and needs no proof about the model. *)
Definition port_arm (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (p : SecurityPort sa) : SecurityArm :=
  match p with
  | ExactIndependence _ => ExactIndependenceArm
  | InputIndistinguishability _ => InputIndistinguishabilityArm
  | IdealProximity _ => IdealProximityArm
  end.
Arguments port_arm {R A E sa} p.

(******************************************************************************)
(*     The completion-level stack                                             *)
(******************************************************************************)

(* The data a row holds at each completion level: an algebra; an algebra with
   its run parameters; those with the three run facts; those with an analysis
   model family; those with a security port at every real field and index. The
   levels are the manifest's own, so the level of a row's last statement is
   the level the manifest records for it. Each component after the first is
   typed by the ones before it, which is what makes the sequencing below
   dependent. *)
Definition StackAt (c : CompletionLevel) : Type :=
  match c with
  | Algebraic       => PGGAlgebraic
  | Executable      => {A : PGGAlgebraic & ExecutionParams A}
  | Observed        => {A : PGGAlgebraic & {E : ExecutionParams A
                          & {Ht : instance_terminates_stmt E
                          & {He : instance_endpoints_stmt E
                          & instance_recon_stmt E}}}}
  | Sampled         => {A : PGGAlgebraic & {E : ExecutionParams A
                          & {Ht : instance_terminates_stmt E
                          & {He : instance_endpoints_stmt E
                          & {Hr : instance_recon_stmt E
                          & AnalysisModelFamily
                              (instance_observed Ht He Hr)}}}}}
  | AnalysisBridged => {A : PGGAlgebraic & {E : ExecutionParams A
                          & {Ht : instance_terminates_stmt E
                          & {He : instance_endpoints_stmt E
                          & {Hr : instance_recon_stmt E
                          & {f : AnalysisModelFamily
                                   (instance_observed Ht He Hr)
                          & forall (R : realType) (idx : amf_index f R),
                              SecurityPort (amf_sample f R idx)}}}}}}
  end.

(* The three run facts and the observed execution they build, at the Observed
   level. A statement reads its predecessor's data through these rather than
   through nested projT2 chains, which is what keeps the statements below
   readable as one line each.

   The nine run-fact accessors and ab_port return a Prop or a Type that
   delta-reduces to a dependent product, so Unset Strict Implicit takes the
   stack coordinate for something to infer and the product's own first binder
   steals its argument slot; the Arguments directive on each pins it back.
   The *_obs and *_f accessors return a record, where nothing is stolen and
   no directive is needed. *)
Definition ob_Ht (q : StackAt Observed) := projT1 (projT2 (projT2 q)).
Arguments ob_Ht : clear implicits.
Definition ob_He (q : StackAt Observed) := projT1 (projT2 (projT2 (projT2 q))).
Arguments ob_He : clear implicits.
Definition ob_Hr (q : StackAt Observed) := projT2 (projT2 (projT2 (projT2 q))).
Arguments ob_Hr : clear implicits.
Definition ob_obs (q : StackAt Observed) : OE.ObservedExecution :=
  instance_observed (ob_Ht q) (ob_He q) (ob_Hr q).

(* The same at the Sampled level, together with the analysis model family the
   sampling statement adjoined. The family is what fixes the probability
   model, so every proposition mentioning a real field is stated below it. *)
Definition sp_Ht (q : StackAt Sampled) := projT1 (projT2 (projT2 q)).
Arguments sp_Ht : clear implicits.
Definition sp_He (q : StackAt Sampled) := projT1 (projT2 (projT2 (projT2 q))).
Arguments sp_He : clear implicits.
Definition sp_Hr (q : StackAt Sampled) :=
  projT1 (projT2 (projT2 (projT2 (projT2 q)))).
Arguments sp_Hr : clear implicits.
Definition sp_obs (q : StackAt Sampled) : OE.ObservedExecution :=
  instance_observed (sp_Ht q) (sp_He q) (sp_Hr q).
Definition sp_f (q : StackAt Sampled) : AnalysisModelFamily (sp_obs q) :=
  projT2 (projT2 (projT2 (projT2 (projT2 q)))).

(* The same at the AnalysisBridged level, together with the security port at
   every real field and index. The port is a function of the real field
   because the analysis family is, so the arm a row certifies is certified
   uniformly and not at one chosen field. *)
Definition ab_Ht (q : StackAt AnalysisBridged) := projT1 (projT2 (projT2 q)).
Arguments ab_Ht : clear implicits.
Definition ab_He (q : StackAt AnalysisBridged) :=
  projT1 (projT2 (projT2 (projT2 q))).
Arguments ab_He : clear implicits.
Definition ab_Hr (q : StackAt AnalysisBridged) :=
  projT1 (projT2 (projT2 (projT2 (projT2 q)))).
Arguments ab_Hr : clear implicits.
Definition ab_obs (q : StackAt AnalysisBridged) : OE.ObservedExecution :=
  instance_observed (ab_Ht q) (ab_He q) (ab_Hr q).
Definition ab_f (q : StackAt AnalysisBridged)
  : AnalysisModelFamily (ab_obs q) :=
  projT1 (projT2 (projT2 (projT2 (projT2 (projT2 q))))).
Definition ab_port (q : StackAt AnalysisBridged) :
  forall (R : realType) (idx : amf_index (ab_f q) R),
    SecurityPort (amf_sample (ab_f q) R idx) :=
  projT2 (projT2 (projT2 (projT2 (projT2 (projT2 q))))).
Arguments ab_port : clear implicits.

(* The arm the data at this level carries, at one real field and one index.
   The port is a function of both, so the arm is read at the arguments the
   port is written at rather than at one chosen field. The certify
   statements build a port whose constructor is the same at every field and
   index, so for a row written in the surface the answer does not depend on
   either argument. *)
Definition ab_arm (q : StackAt AnalysisBridged) (R : realType)
    (idx : amf_index (ab_f q) R) : SecurityArm :=
  port_arm (ab_port q R idx).
Arguments ab_arm : clear implicits.

(******************************************************************************)
(*     The proposition family                                                 *)
(******************************************************************************)

(* The run-correctness conjunction of an observed execution, restated as the
   value of a proposition family rather than as the type of one theorem. A
   row's proposition has to be a function of the row's data, and this is the
   form in which correctness enters that function and is carried unchanged by
   every statement above it. *)
Definition oe_correct_prop (oe : OE.ObservedExecution) : Prop :=
  forall (x : ep_inputT (OE.oe_execution oe))
         (w0 : pgg_gT (mp_M (OE.oe_profile oe))),
    w0 \in pgg_G (mp_M (OE.oe_profile oe)) ->
    [/\ (@exec_run (OE.oe_profile oe) (OE.oe_execution oe)
           x w0 (OE.oe_P_idx oe)).1
        = nseq (size (@exec_procs (OE.oe_profile oe) (OE.oe_execution oe)
                        x w0 (OE.oe_P_idx oe))) Finish,
        size (@exec_endpoints (OE.oe_profile oe) (OE.oe_execution oe)
                x w0 (OE.oe_P_idx oe))
        = (pi_T' (mp_PI (OE.oe_profile oe))).+1
      & @exec_decode (OE.oe_profile oe) (OE.oe_execution oe)
          (@exec_endpoints (OE.oe_profile oe) (OE.oe_execution oe)
             x w0 (OE.oe_P_idx oe))
          (OE.oe_endpoints_size oe x w0)
        = OE.oe_expected oe x].
Arguments oe_correct_prop : clear implicits.

(* The proof of that proposition, read off the observed execution's own field.
   It is the whole content of the Observed level: a row that supplies the
   three run facts reaches run correctness at no further cost. *)
Definition observed_correct (oe : OE.ObservedExecution) : oe_correct_prop oe :=
  @OE.oe_run_correct oe.
Arguments observed_correct : clear implicits.

(* At every real field and every index of the family, the executed coalition
   reader is the static one. This is the identification that lets the security
   statements be made about static_coalition_obs, which names no interpreter
   state, and it is the hypothesis along which exact_tail transports a
   witness's independence. *)
Definition sampled_viewE_prop (A : PGGAlgebraic) (E : ExecutionParams A)
    (Ht : instance_terminates_stmt E) (He : instance_endpoints_stmt E)
    (Hr : instance_recon_stmt E)
    (f : AnalysisModelFamily (instance_observed Ht He Hr)) : Prop :=
  forall (R : realType) (idx : amf_index f R)
         (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}),
    @sa_coalition_view R (instance_profile A) (instance_exec E)
      (amf_sample f R idx) 0 C
    = (fun u => static_coalition_obs C ((amf_sample f R idx).(sa_arg) u)
                  ((amf_sample f R idx).(sa_cut) u)).
Arguments sampled_viewE_prop {A E Ht He Hr} f.

(* The exact arm's proposition: below the threshold, the coalition's executed
   view is independent of the secret, its mutual information with the secret
   is zero, conditioning on it leaves the secret's entropy unchanged, and
   every deterministic function of it is still independent. Independence leads
   and the entropy forms follow it, so the information-theoretic reading of
   the arm is proved from the same fact rather than assumed beside it. *)
Definition ExactProp (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (w : ExactWitness sa) : Prop :=
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| < profile_k (instance_profile A))%N ->
    [/\ sa_sampleP sa |= (@sa_coalition_view R (instance_profile A)
                            (instance_exec E) sa 0 C)
                         _|_ (ew_secret w),
        `I( ew_secret w ;
            @sa_coalition_view R (instance_profile A) (instance_exec E)
              sa 0 C ) = 0,
        `H( ew_secret w |
            @sa_coalition_view R (instance_profile A) (instance_exec E)
              sa 0 C ) = `H `p_ (ew_secret w)
      & forall (W : finType)
               (h : {ffun 'I_(pi_T' (mp_PI (instance_profile A))).+1
                       -> 'I_(pgg_N' (mp_M (instance_profile A))).+1} -> W),
          sa_sampleP sa
          |= (h `o (@sa_coalition_view R (instance_profile A)
                      (instance_exec E) sa 0 C))
             _|_ (ew_secret w)].
Arguments ExactProp {R A E sa} w.

(* The input-indistinguishability arm's proposition: below the threshold, two
   run arguments give coalition readings of the cut within variation distance
   c. The bound is a parameter rather than the certificate's own sum, so
   conclude can state a finished row at any number at or above that sum, the
   constant a paper cites among them, without reproving the arm. *)
Definition IndistinguishabilityPropAt (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IndistinguishabilityCert sa) (c : R) : Prop :=
  forall (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1})
         (x x' : ex_inputT E),
    (#|C| < profile_k (instance_profile A))%N ->
    var_dist (fdistmap (static_coalition_obs C x) (sa_cut_dist sa))
             (fdistmap (static_coalition_obs C x') (sa_cut_dist sa))
    <= c.
Arguments IndistinguishabilityPropAt {R A E sa} cert c.

(* A certificate's own bound: the marginal bound's epsilon twice, one for each
   of the two run arguments the arm compares. It is the number a row carries
   when its coordinate names none. *)
Definition cert_eps (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E))
    (cert : IndistinguishabilityCert sa) : R :=
  sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert).
Arguments cert_eps {R A E sa} cert.

(* The proximity arm's proposition: below the threshold, the joint law of the
   coalition's executed reading and the secret under the actual model is
   within variation distance c of the product of the two marginals the ideal
   model has, its own reading and its own secret. The right side is a product
   because the ideal's witness makes those two independent there, so c bounds
   the sum of the absolute differences between what a coalition below the
   threshold sees jointly with the secret and two quantities drawn apart, and
   a distinguisher's advantage is at most half of c, the sum of the absolute
   differences being twice the total variation distance of the literature.
   The attack model is a static coalition of fewer than k seats reading its
   own endpoints, and the claim is an average over the run argument and not a
   statement at a fixed run argument. The bound is a parameter, as it is for
   the input-indistinguishability arm, so conclude can state a finished row at
   any number at or above it, the one a paper cites among them. *)
Definition IdealProximityPropAt (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IdealProximityCert sa) (c : R) : Prop :=
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| < profile_k (instance_profile A))%N ->
    var_dist
      (fdistmap (fun u => (@sa_coalition_view R (instance_profile A)
                             (instance_exec E) sa 0 C u, ipc_secret cert u))
         (sa_sampleP sa))
      ((fdistmap (@sa_coalition_view R (instance_profile A) (instance_exec E)
                    (ipc_ideal cert) 0 C) (sa_sampleP (ipc_ideal cert)))
       `x (fdistmap (ew_secret (ipc_witness cert))
             (sa_sampleP (ipc_ideal cert))))
    <= c.
Arguments IdealProximityPropAt {R A E sa} cert c.

(* A bound named once per real field, with None meaning the program's own sum.
   A single real will not serve, because the security port quantifies over the
   real field and the published number is therefore a function of it. *)
Definition Reprice := forall R : realType, option R.

(* The coordinate that names nothing. Every row that publishes the bound it
   accumulated carries it. *)
Definition no_reprice : Reprice := fun _ => None.

(* The proposition a port carries at a given coordinate: independence for the
   exact arm, the variation bound at the named number for the
   input-indistinguishability arm, the distance to the ideal model's product
   law at the named number for the proximity arm. The arm selects the
   proposition, so a row cannot state one arm's claim about another's
   witness. *)
Definition PortProp (c : Reprice) (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (p : SecurityPort sa) : Prop :=
  match p with
  | ExactIndependence w => ExactProp w
  | InputIndistinguishability cert =>
      IndistinguishabilityPropAt cert (odflt (cert_eps cert) (c R))
  | IdealProximity cert =>
      IdealProximityPropAt cert (odflt (ipc_eps cert) (c R))
  end.
Arguments PortProp c {R A E sa} p.

(* What a row has proved at the AnalysisBridged level: run correctness, the
   view identification, and at every real field and index the port's own
   proposition. The conjunction nests to the left, so each statement extends
   it by one conjunct on the right and the earlier conjuncts stay reachable
   by proj1. *)
Definition BridgedProp (c : Reprice) (q : StackAt AnalysisBridged) : Prop :=
  (oe_correct_prop (ab_obs q) /\ sampled_viewE_prop (ab_f q))
  /\ forall (R : realType) (idx : amf_index (ab_f q) R),
       PortProp c (ab_port q R idx).
Arguments BridgedProp c q : assert.

(* The proposition a row carries at each completion level: nothing about a
   coalition below Observed, run correctness at Observed, that with the view
   identification at Sampled, and the bridged conjunction at the program's own
   bound above it. This is the default proposition family of the carrier
   below, and the family a terminal leaves when it concludes a row.

   The match needs no return annotation: the expected type
   StackAt b -> Prop determines the motive. *)
Definition StackProp (b : CompletionLevel) : StackAt b -> Prop :=
  match b with
  | Algebraic       => fun _ => True
  | Executable      => fun _ => True
  | Observed        => fun q => oe_correct_prop (ob_obs q)
  | Sampled         => fun q => oe_correct_prop (sp_obs q)
                               /\ sampled_viewE_prop (sp_f q)
  | AnalysisBridged => fun q => BridgedProp no_reprice q
  end.
Arguments StackProp : clear implicits.

(******************************************************************************)
(*     The carrier and its dependent bind                                     *)
(******************************************************************************)

(* A completion level's data together with a proof of a proposition about it.
   The carrier is indexed by the proposition family and not only by the level,
   because a terminal that concludes a row at a chosen number hands back a
   record at the same level whose proposition is no longer StackProp. *)
#[projections(primitive)]
Record TableauAt (b : CompletionLevel) (Q : StackAt b -> Prop) :=
  MkTableau {
    tableau_at  : StackAt b ;
    tableau_thm : Q tableau_at }.

Arguments TableauAt : clear implicits.

(* A tableau at the default proposition family of its level: what every line
   of a row returns until a terminal changes the family. *)
Notation Tableau b := (TableauAt b (StackProp b)).

(* Sequencing: a statement receives the accumulated data, the accumulated
   proof and one payload of its own, and returns what it builds. The bind is
   dependent in the data because the next statement's witness type mentions
   the incoming coordinate, and a non-dependent sequencing would have to fix
   that type before the coordinate is known and would silently drop the
   previous line's proposition. *)
Definition tableau_bind (a : CompletionLevel) (Q : StackAt a -> Prop)
    (P : StackAt a -> Type) (T : Type) (s : TableauAt a Q)
    (f : forall x : StackAt a, Q x -> P x -> T) (p : P (tableau_at s)) : T :=
  f (tableau_at s) (tableau_thm s) p.
Arguments tableau_bind {a Q P T} s f p.

(* The surface of a row: a statement f applied to the program so far and to
   its payload p. Left associative, so a row reads as a sequence of statements
   applied to a growing coordinate; right associativity parses one line's
   payload as the next line's continuation. The infix >>= is taken by the
   fdist scope, so the separator is spelled of. *)
Notation "s ;;; f 'of' p" := (tableau_bind s f p)
  (at level 90, left associativity).

(* The first line of every row: an algebra, with the empty proposition its
   level carries. Nothing about a coalition has been proved at this point,
   which is what True records. *)
Definition tableau_start (A : PGGAlgebraic) : Tableau Algebraic :=
  @MkTableau Algebraic (StackProp Algebraic) A I.

(* Sequencing a statement onto a tableau built from given data and proof is
   that statement applied to them. The left unit law of the bind; it holds by
   conversion, so a row's proof term is the composition of its statements with
   no bookkeeping between the lines. *)
Lemma tableau_left_unit (a : CompletionLevel) (Q : StackAt a -> Prop)
    (P : StackAt a -> Type) (T : Type) (x : StackAt a) (pf : Q x)
    (f : forall y : StackAt a, Q y -> P y -> T) (p : P x) :
  tableau_bind (@MkTableau a Q x pf) f p = f x pf p.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The statements                                                         *)
(******************************************************************************)

(* From an algebra and a fuel, the run parameters of a dealer-dealt secret.
   The first statement of a dealer-dealt row, and the point at which the run
   argument becomes the secret itself. *)
Definition dealt_step (x : StackAt Algebraic) (_ : StackProp Algebraic x)
    (fuel : nat) : Tableau Executable :=
  @MkTableau Executable (StackProp Executable)
    (existT (fun A : PGGAlgebraic => ExecutionParams A) x
       (dealt_secret_params x fuel)) I.

(* The payload of execute_step: the three run facts at the accumulated
   parameters. Its type mentions those parameters, which is the reason the
   sequencing above is dependent. *)
Definition ObsPayload (x : StackAt Executable) : Type :=
  {Ht : instance_terminates_stmt (projT2 x)
   & {He : instance_endpoints_stmt (projT2 x)
   & instance_recon_stmt (projT2 x)}}.

(* Adjoins the three run facts, reaching the Observed level with run
   correctness proved from the observed execution they build. This is the one
   line at which an instance's own reduction work enters a row. *)
Definition execute_step (x : StackAt Executable) (_ : StackProp Executable x)
    (p : ObsPayload x) : Tableau Observed :=
  @MkTableau Observed (StackProp Observed)
    (existT _ (projT1 x) (existT _ (projT2 x)
       (existT _ (projT1 p)
          (existT _ (projT1 (projT2 p)) (projT2 (projT2 p))))))
    (observed_correct _).

Arguments execute_step x _ p : assert.

(* The payload of sample_step: an analysis model family over the accumulated
   observed execution, the value that fixes the probability model a row's
   security statements are made in. *)
Definition FamPayload (x : StackAt Observed) : Type :=
  AnalysisModelFamily (ob_obs x).

(* Adjoins an analysis model family, reaching the Sampled level and proving
   that at every real field and index the executed coalition reader is the
   static one. It is the line that turns a row's claims from claims about the
   interpreter's messages into claims about a group action. *)
Definition sample_step (x : StackAt Observed) (q : StackProp Observed x)
    (f : FamPayload x) : Tableau Sampled :=
  @MkTableau Sampled (StackProp Sampled)
    (existT _ (projT1 x) (existT _ (projT1 (projT2 x))
       (existT _ (ob_Ht x) (existT _ (ob_He x) (existT _ (ob_Hr x) f)))))
    (conj q (fun R idx C =>
               @sa_coalition_viewE R (instance_profile (projT1 x))
                 (instance_exec (projT1 (projT2 x))) (amf_sample f R idx) 0
                 (ex_content_obs (projT1 (projT2 x)))
                 (fun u => ob_He x _ _) C)).

Arguments sample_step x q f : assert.

(* The payload of certify_exact: one exact witness per real field and index of
   the accumulated family. Uniformity in the field is what makes the arm's
   conclusion unconditional rather than a statement at one chosen field. *)
Definition ExactPayload (x : StackAt Sampled) : Type :=
  forall (R : realType) (idx : amf_index (sp_f x) R),
    ExactWitness (amf_sample (sp_f x) R idx).

(* The payload of certify_indistinguishability: one
   input-indistinguishability certificate per real field and index of the
   accumulated family. Uniform in the field for the same reason the exact
   payload is, so the bound the arm publishes is a bound at every field
   rather than at one chosen field. *)
Definition IndistinguishabilityPayload (x : StackAt Sampled) : Type :=
  forall (R : realType) (idx : amf_index (sp_f x) R),
    IndistinguishabilityCert (amf_sample (sp_f x) R idx).

(* The payload of certify_idealproximity: one proximity certificate per real
   field and index of the accumulated family. Uniform in the field for the
   reason the other two payloads are, so the ideal a row compares itself with
   and the number it loses against that ideal are fixed at every field. *)
Definition IdealProximityPayload (x : StackAt Sampled) : Type :=
  forall (R : realType) (idx : amf_index (sp_f x) R),
    IdealProximityCert (amf_sample (sp_f x) R idx).

(* The independence a witness states at the direct computation, transported
   to the view along the link lemma, with its entropy forms and
   its closure under deterministic post-processing. The composition law of the
   exact arm, and what makes an ExactWitness the whole of what an instance
   owes on it. *)
Lemma exact_tail (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E)) (w : ExactWitness sa)
    (Hview : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
       @sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C
       = (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u))) :
  ExactProp w.
Proof.
move=> C HC.
have Hi : sa_sampleP sa
          |= (@sa_coalition_view R (instance_profile A) (instance_exec E)
                sa 0 C) _|_ (ew_secret w).
  by rewrite (Hview C); exact: (@ew_indep _ _ _ _ w C HC).
pose lw : LeakageWitness (sa_sampleP sa) := MkLeakageWitness Hi.
split; first exact: (@lw_indep _ _ _ lw).
- exact: (proj1 (leakage_of_view_indep (lw_secret lw) (lw_view lw)
                   (@lw_indep _ _ _ lw))).
- exact: (proj2 (leakage_of_view_indep (lw_secret lw) (lw_view lw)
                   (@lw_indep _ _ _ lw))).
- move=> W h; exact: (pgg_trace_secrecy.inde_RV_comp h (@lw_indep _ _ _ lw)).
Qed.
Arguments exact_tail {R A E sa} w Hview.

(* The certificate's cut-carrier distance and its ideal constancy, fed to the
   transfer inequality, give the two-argument variation bound at cert_eps,
   the certificate's marginal-bound epsilon twice. The composition law of the
   input-indistinguishability arm, and the only place the mixing bound is
   used. *)
Lemma indistinguishability_tail (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IndistinguishabilityCert sa) :
  IndistinguishabilityPropAt cert (cert_eps cert).
Proof.
move=> C x x' HC.
apply: (var_dist_fdistmap_transfer R _ _ (sa_cut_dist sa) (ic_ideal cert)
  (static_coalition_obs C x) (static_coalition_obs C x')
  (sw_bound_eps (ic_b cert))).
- by rewrite -(ic_Hd cert); exact: (ic_close cert).
- exact: (@ic_const _ _ _ _ cert C HC x x').
Qed.
Arguments indistinguishability_tail {R A E sa} cert.

(* The certificate's distance between the two models' joint laws, stated at
   the direct computation, carried to the executed readers of both models
   along the link lemma taken once for each, with the ideal joint law
   rewritten as the product of its two marginals by the ideal witness's
   independence. The composition law of the proximity arm; the two link
   hypotheses have the shape the previous statement proved, and the ideal's is
   available because the ideal adapter runs the row's own execution. *)
Lemma idealproximity_tail (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IdealProximityCert sa)
    (Hview : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
       @sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C
       = (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u)))
    (Hideal : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
       @sa_coalition_view R (instance_profile A) (instance_exec E)
         (ipc_ideal cert) 0 C
       = (fun u => static_coalition_obs C ((ipc_ideal cert).(sa_arg) u)
                     ((ipc_ideal cert).(sa_cut) u))) :
  IdealProximityPropAt cert (ipc_eps cert).
Proof.
move=> C HC.
rewrite (Hview C) (Hideal C).
rewrite -(inde_dist_of_RV2 (@ew_indep _ _ _ _ (ipc_witness cert) C HC)).
exact: (@ipc_close _ _ _ _ cert C HC).
Qed.
Arguments idealproximity_tail {R A E sa} cert Hview Hideal.

(* Adjoins the exact arm's witness at every real field and index, reaching
   AnalysisBridged with the arm's proposition proved by exact_tail from the
   previous line's identification. *)
Definition certify_exact (x : StackAt Sampled) (q : StackProp Sampled x)
    (p : ExactPayload x) : Tableau AnalysisBridged :=
  @MkTableau AnalysisBridged (StackProp AnalysisBridged)
    (existT _ (projT1 x) (existT _ (projT1 (projT2 x))
       (existT _ (sp_Ht x) (existT _ (sp_He x) (existT _ (sp_Hr x)
          (existT _ (sp_f x)
             (fun R idx => ExactIndependence (p R idx))))))))
    (conj q (fun R idx => exact_tail (p R idx) (proj2 q R idx))).

Arguments certify_exact x q p : assert.

(* Adjoins the input-indistinguishability arm's certificate at every real
   field and index, reaching AnalysisBridged with the arm's proposition
   proved by indistinguishability_tail. The certify statements are the only
   lines through which an instance's own mathematics enters a row; the
   payload of conclude is the one place outside a line where it enters. *)
Definition certify_indistinguishability (x : StackAt Sampled)
    (q : StackProp Sampled x)
    (p : IndistinguishabilityPayload x) : Tableau AnalysisBridged :=
  @MkTableau AnalysisBridged (StackProp AnalysisBridged)
    (existT _ (projT1 x) (existT _ (projT1 (projT2 x))
       (existT _ (sp_Ht x) (existT _ (sp_He x) (existT _ (sp_Hr x)
          (existT _ (sp_f x)
             (fun R idx => InputIndistinguishability (p R idx))))))))
    (conj q (fun R idx => indistinguishability_tail (p R idx))).

Arguments certify_indistinguishability x q p : assert.

(* Adjoins the proximity arm's certificate at every real field and index,
   reaching AnalysisBridged with the arm's proposition proved by
   idealproximity_tail. The link lemma the previous statement proved serves
   the actual model, and the ideal model's is built here by the same lemma
   sample_step used, which applies because the certificate's ideal adapter
   runs this row's own execution and so meets this row's endpoint equation. *)
Definition certify_idealproximity (x : StackAt Sampled)
    (q : StackProp Sampled x) (p : IdealProximityPayload x)
    : Tableau AnalysisBridged :=
  @MkTableau AnalysisBridged (StackProp AnalysisBridged)
    (existT _ (projT1 x) (existT _ (projT1 (projT2 x))
       (existT _ (sp_Ht x) (existT _ (sp_He x) (existT _ (sp_Hr x)
          (existT _ (sp_f x)
             (fun R idx => IdealProximity (p R idx))))))))
    (conj q (fun R idx =>
       idealproximity_tail (p R idx) (proj2 q R idx)
         (fun C => @sa_coalition_viewE R (instance_profile (projT1 x))
                     (instance_exec (projT1 (projT2 x)))
                     (ipc_ideal (p R idx)) 0
                     (ex_content_obs (projT1 (projT2 x)))
                     (fun u => sp_He x _ _) C))).

Arguments certify_idealproximity x q p : assert.

(******************************************************************************)
(*     The terminals                                                          *)
(******************************************************************************)

(* The obligation of conclude: at every real field and index, the number a
   port carrying one is concluded at is at least that port's own, and nothing
   for an exact port. A row may therefore publish the constant a paper cites
   whenever that constant is an upper bound of the distance the row proved,
   and may not publish a number below the one its certificate proved. The
   exact arm carries no number, so concluding a row leaves it untouched. An
   upper bound is the right obligation because the propositions of the two
   arms that carry a number are monotone in it; an arm whose proposition is
   not monotone in the number it carries owes a different obligation here. *)
Definition ConcludePayload (c : Reprice) (q : StackAt AnalysisBridged) : Type :=
  forall (R : realType) (idx : amf_index (ab_f q) R),
    match ab_port q R idx with
    | ExactIndependence _ => unit
    | InputIndistinguishability cert =>
        cert_eps cert <= odflt (cert_eps cert) (c R)
    | IdealProximity cert => ipc_eps cert <= odflt (ipc_eps cert) (c R)
    end.
Arguments ConcludePayload c q : assert.

(* A port's proposition at the program's own bound, and a proof that a chosen
   number is at least that bound, give the port's proposition at the chosen
   number. The step is sound because the propositions of the arms that carry a
   number are monotone in it, which is the condition any future arm carrying a
   number owes as well; it is what lets a row state the constant a paper
   cites while asserting about the coalition no more than the certificate
   proved. *)
Lemma port_conclude (c : Reprice) (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (p : SecurityPort sa) :
  PortProp no_reprice p ->
  (match p with
   | ExactIndependence _ => unit
   | InputIndistinguishability cert =>
       cert_eps cert <= odflt (cert_eps cert) (c R)
   | IdealProximity cert => ipc_eps cert <= odflt (ipc_eps cert) (c R)
   end) ->
  PortProp c p.
Proof.
case: p => [w|cert|cert] //=.
- move=> H1 H2 C x x' HC.
  exact: Order.POrderTheory.le_trans (H1 C x x' HC) H2.
- move=> H1 H2 C HC.
  exact: Order.POrderTheory.le_trans (H1 C HC) H2.
Qed.
Arguments port_conclude c {R A E sa} p.

(* The terminal concluding a row at a chosen number, against a proof that the
   number is at least the row's accumulated bound. Post-processing of the
   published constant rather than a step: the data and the arms are
   unchanged, only the real the input-indistinguishability arm's proposition
   mentions moves, and it moves only upward. *)
Definition conclude (c : Reprice) (q : StackAt AnalysisBridged)
    (pf : StackProp AnalysisBridged q) (p : ConcludePayload c q)
    : TableauAt AnalysisBridged (BridgedProp c) :=
  @MkTableau AnalysisBridged (BridgedProp c) q
    (conj (proj1 pf)
       (fun R idx => port_conclude c (ab_port q R idx)
                       (proj2 pf R idx) (p R idx))).
Arguments conclude : clear implicits.

(* The payload of restate: a function from the proposition a row accumulated
   to the proposition its caller wants stated. The caller supplies the
   derivation, so restating is where a row's own conjunction is traded for
   the statement a downstream file cites, and nothing of the row survives the
   trade except what that derivation uses. *)
Definition RestatePayload (Q : Prop) (q : StackAt AnalysisBridged) : Type :=
  StackProp AnalysisBridged q -> Q.
Arguments RestatePayload Q q : assert.

(* A row's data together with an arbitrary proposition proved from what the
   row accumulated. The proposition is a parameter and not a field of the
   data, so two rows over the same instance may be handed over as different
   theorems. *)
Record RestatedTableau (Q : Prop) := MkRestatedTableau {
  rq_at  : StackAt AnalysisBridged ;
  rq_thm : Q }.
Arguments RestatedTableau : clear implicits.

(* The terminal handing a row over as a proposition its caller writes out.
   conclude is not an instance of it: conclude's target is computed by the
   framework from that coordinate, this one's is supplied. *)
Definition restate (Q : Prop) (q : StackAt AnalysisBridged)
    (pf : StackProp AnalysisBridged q) (p : RestatePayload Q q)
    : RestatedTableau Q :=
  @MkRestatedTableau Q q (p pf).
Arguments restate : clear implicits.

(* A row's data, the manifest row describing it, and the proposition the row
   reached. The manifest already publishes the descriptive row; a published
   row is that same value with its theorem attached, so the manifest's claim
   about an instance and the proof of it are one term. *)
Record PublishedRowAt (c : Reprice) := MkPublishedRow {
  published_at  : StackAt AnalysisBridged ;
  published_row : AnalysisPathRow ;
  published_thm : BridgedProp c published_at }.
Arguments PublishedRowAt : clear implicits.

(* A published row at the program's own bound: what a row whose coordinate
   names no number publishes. *)
Notation PublishedRow := (PublishedRowAt no_reprice).

(* The terminal pairing the accumulated proposition with the manifest row for
   it. The assumption status precedes the coordinate because the sequencing
   carries one payload per line and the transfer status is that payload. *)
Definition publish (a : AssumptionStatus) (c : Reprice)
    (q : StackAt AnalysisBridged) (pf : BridgedProp c q)
    (t : TransferStatus) : PublishedRowAt c :=
  @MkPublishedRow c q
    (@MkAnalysisPathRow (ab_obs q) AnalysisBridged (ab_f q) t a) pf.
Arguments publish a {c} q pf t.

(* Run correctness of a published row: every process finishes, the endpoints
   number one per seat, and decoding them returns the dealt value. *)
Definition run_correct_of (c : Reprice) (r : PublishedRowAt c) :=
  proj1 (proj1 (published_thm r)).
Arguments run_correct_of {c} r.

(* The link lemma of a published row, identifying its view with the direct
   computation, the fact on which its security statement is stated
   about a group action. *)
Definition view_identification_of (c : Reprice) (r : PublishedRowAt c) :=
  proj2 (proj1 (published_thm r)).
Arguments view_identification_of {c} r.

(* The security statement of a published row, under the name a reader of the
   exact arm expects. *)
Definition view_secrecy_of (c : Reprice) (r : PublishedRowAt c) :=
  proj2 (published_thm r).
Arguments view_secrecy_of {c} r.

(* The same projection under the name a reader of the
   input-indistinguishability arm expects. The arm is selected only when the
   result is applied, so naming the one that does not match a row fails at
   the next application rather than here. *)
Definition view_indistinguishability_of (c : Reprice) (r : PublishedRowAt c) :=
  proj2 (published_thm r).
Arguments view_indistinguishability_of {c} r.

(* The same projection under the name a reader of the proximity arm expects.
   The three names are one term and differ in what a reader is told to expect
   of it, which is the arm's own proposition and is selected only when the
   result is applied. *)
Definition view_proximity_of (c : Reprice) (r : PublishedRowAt c) :=
  proj2 (published_thm r).
Arguments view_proximity_of {c} r.

(* Which arm a published row carries, at one real field and one index of its
   family. It reads ab_arm past the publish statement, so it is the reader a
   paper's arm column is taken from, and publish_armE is why the publish
   statement does not change the answer. *)
Definition security_arm_of (c : Reprice) (r : PublishedRowAt c)
    (R : realType) (idx : amf_index (ab_f (published_at r)) R)
  : SecurityArm :=
  ab_arm (published_at r) R idx.
Arguments security_arm_of {c} r R idx.

(******************************************************************************)
(*     Where a row's arm is decided                                           *)
(******************************************************************************)

(* A row built by the exact statement carries the exact arm at every real
   field and index of its family. With conclude_armE and publish_armE below
   it settles the arm of a finished row by one line of the row's text, so a
   reader needs no argument about the instance's probability model to know
   which statement the row proved. *)
Lemma certify_exact_armE (x : StackAt Sampled) (q : StackProp Sampled x)
    (p : ExactPayload x) (R : realType)
    (idx : amf_index (ab_f (tableau_at (@certify_exact x q p))) R) :
  ab_arm (tableau_at (@certify_exact x q p)) R idx = ExactIndependenceArm.
Proof. by []. Qed.

(* The same for the input-indistinguishability statement. With
   certify_exact_armE this is what makes the arm a property of the program's
   text: the certify statements are the only ones that build a port, and each
   writes one constructor at every field and index. *)
Lemma certify_indistinguishability_armE (x : StackAt Sampled)
    (q : StackProp Sampled x) (p : IndistinguishabilityPayload x)
    (R : realType)
    (idx : amf_index
             (ab_f (tableau_at (@certify_indistinguishability x q p))) R) :
  ab_arm (tableau_at (@certify_indistinguishability x q p)) R idx
  = InputIndistinguishabilityArm.
Proof. by []. Qed.

(* The same for the proximity statement. The three statements are the only
   ones that build a port, and each writes one constructor at every field and
   index, so a reader of a program's text knows which of the three claims the
   row will publish. *)
Lemma certify_idealproximity_armE (x : StackAt Sampled)
    (q : StackProp Sampled x) (p : IdealProximityPayload x) (R : realType)
    (idx : amf_index (ab_f (tableau_at (@certify_idealproximity x q p))) R) :
  ab_arm (tableau_at (@certify_idealproximity x q p)) R idx
  = IdealProximityArm.
Proof. by []. Qed.

(* Concluding a row at a chosen number leaves its arm where the certify
   statement put it. The terminal moves a real and not the alternative the
   row committed to, so a row at the constant a paper cites states the same
   kind of fact about a coalition as the row at its own bound. *)
Lemma conclude_armE (c : Reprice) (q : StackAt AnalysisBridged)
    (pf : StackProp AnalysisBridged q) (p : ConcludePayload c q)
    (R : realType)
    (idx : amf_index (ab_f (tableau_at (conclude c q pf p))) R) :
  ab_arm (tableau_at (conclude c q pf p)) R idx = ab_arm q R idx.
Proof. by []. Qed.

(* Publishing attaches the manifest row and leaves the arm alone, so the arm
   a finished row reports is the arm its data carried before the last line.
   This is the step that carries the three certify statements' arm equations
   out to a published row, where a paper's table reads them. *)
Lemma publish_armE (a : AssumptionStatus) (c : Reprice)
    (q : StackAt AnalysisBridged) (pf : BridgedProp c q) (t : TransferStatus)
    (R : realType)
    (idx : amf_index (ab_f (published_at (publish a q pf t))) R) :
  security_arm_of (publish a q pf t) R idx = ab_arm q R idx.
Proof. by []. Qed.
