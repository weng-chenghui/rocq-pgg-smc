(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Tableau: an analysis path of one protocol instance as a program            *)
(*                                                                            *)
(* A path of the analysis manifest is written here as a program. Its lines    *)
(* are statements; each one takes the data accumulated so far, the            *)
(* proposition proved about it so far, and one payload of its own, and        *)
(* returns the data raised one completion level. dealt_step carries the True  *)
(* of the two bottom levels forward, execute_step establishes the proposition *)
(* in its place, and the three above them extend it by one conjunct on the    *)
(* right, so from Sampled upwards it is a left-nested conjunction whose added *)
(* conjuncts are about the coalition's view. A reader who stops at any line   *)
(* knows exactly what has been proved there, and the named projections at the *)
(* bottom read those conjuncts back off a finished program.                   *)
(*                                                                            *)
(* There are six statements. dealt_step fixes the run argument to be the      *)
(* dealer's secret and chooses a fuel. execute_step adjoins the three run     *)
(* facts and reaches run correctness. sample_step adjoins an analysis model   *)
(* family and proves that the executed coalition reader is the static one,    *)
(* which is what moves the program from a claim about interpreter messages to *)
(* a claim about a group action. certify_exact, certify_indistinguishability  *)
(* and certify_idealproximity adjoin the security evidence for one of three   *)
(* security properties. Each of the three propositions speaks only of a       *)
(* coalition below the privacy threshold, and the three are not comparable    *)
(* statements: the exact-independence proposition concludes independence of   *)
(* the coalition's view from the secret, unconditionally and at every real    *)
(* field, the input-indistinguishability proposition concludes a variation    *)
(* distance between the readings of two run arguments, bounded by the         *)
(* certificate's marginal-bound epsilon twice, one for each argument, and the *)
(* ideal-proximity proposition concludes a variation distance between the     *)
(* joint law of the coalition's view with the secret and the product of the   *)
(* two marginals of an ideal model whose own privacy is exact. A program      *)
(* commits to one security property and claims nothing about the rest, and    *)
(* security_property_of names which property a finished program committed to. *)
(*                                                                            *)
(* The exact-independence and the ideal-proximity propositions mention terms  *)
(* an instance chooses, so a program of either says as much as those terms    *)
(* say. ExactProp mentions the witness's ew_secret, and a constant ew_secret  *)
(* satisfies ew_indep at every coalition. IdealProximityPropAt mentions the   *)
(* certificate's ipc_secret and the two marginals of its ipc_ideal, and at an *)
(* ipc_ideal that is the program's own adapter, with ipc_secret that          *)
(* adapter's witness's own secret, the two sides of ipc_close are one term at *)
(* every coalition below the threshold and the field holds at an ipc_eps of   *)
(* zero. The input-indistinguishability proposition is different in kind:     *)
(* IndistinguishabilityPropAt mentions neither ic_ideal nor a secret, only    *)
(* the readings of the model's own cut law at two run arguments and the       *)
(* number bounding their distance, so ic_ideal is a means of proving it.      *)
(* ic_close holds ic_ideal within the marginal bound's epsilon of that        *)
(* bound's own law, ic_Hd identifies that law with the model's own cut law,   *)
(* and ic_const asks a coalition below the threshold to read ic_ideal the     *)
(* same at every two run arguments. At some models these three fields leave   *)
(* no certificate whose marginal bound's epsilon, taken twice, is below a     *)
(* positive number.                                                           *)
(*                                                                            *)
(* Each of the three propositions is reached by one composition law, and      *)
(* those laws are where the mathematics of the program sits. exact_tail       *)
(* transports a witness's independence from the direct computation to the     *)
(* view along the previous statement's link lemma, then derives the entropy   *)
(* forms by leakage_of_view_indep and the closure under deterministic         *)
(* post-processing by inde_RV_comp. indistinguishability_tail feeds the       *)
(* certificate's cut-carrier distance and its ideal constancy to              *)
(* var_dist_fdistmap_transfer. idealproximity_tail transports the             *)
(* certificate's distance between two joint laws to the executed readers of   *)
(* both models, along that link lemma taken once for each model, and rewrites *)
(* the ideal joint law as the product of its two marginals through the ideal  *)
(* witness's independence.                                                    *)
(*                                                                            *)
(* Two things stay outside the program. The mathematics of a particular       *)
(* instance never appears as a line: it enters as the witness or the          *)
(* certificate a certify statement takes, and once more as the payload of     *)
(* conclude, which for input-indistinguishability or proximity evidence is an *)
(* inequality between the number the program's own certificate proved and the *)
(* number the program publishes and for exact-independence evidence is        *)
(* nothing. And of the three terminals only conclude returns a tableau and    *)
(* only it has a step's shape, but it too is outside: it leaves the data and  *)
(* the security property untouched and moves the real the evidence's          *)
(* proposition mentions to any upper bound of it.                             *)
(*                                                                            *)
(* Two levels below the bridge have a terminal of their own. A program that   *)
(* stops at Observed hands over run correctness with a manifest path whose    *)
(* observed execution is the program's own, whose level, model slot and       *)
(* transfer status the terminal fixes, and whose assumption status is the     *)
(* payload the line writes. One that stops at Sampled hands over run          *)
(* correctness and the link lemma of the model family it named. The two       *)
(* records are inductive types distinct from PublishedAt, which is what makes *)
(* every security reader inapplicable to a value of either, so a coercion     *)
(* added later out of either record into PublishedAt would turn each recorded *)
(* rejection into an acceptance. The Sampled terminal takes its transfer      *)
(* status at a payload type holding the two statuses that name an absent      *)
(* premise rather than a theorem, because a program at that level has proved  *)
(* no statement in which an idealized model occurs. The assumption status is  *)
(* a payload at all three levels. No level's proposition determines it and    *)
(* nothing in the term ties it to Print Assumptions: it is the author's       *)
(* statement, and the manifest's prose defines when it is true.               *)
(*                                                                            *)
(* A fourth terminal hands over an obstruction in place of a security         *)
(* property. Its record holds a program's data at Sampled, a manifest path at *)
(* AnalysisBridged and NegativeTransfer, and one member of a closed           *)
(* enumeration of facts about the model together with the proof of it. The    *)
(* single member is input distinguishability at a number, and the proposition *)
(* it stands for is that the number is above zero and that some coalition     *)
(* below the privacy threshold reads two run arguments of the model's own cut *)
(* law at least that far apart, in the sum of absolute differences. No        *)
(* security property follows from such a value, and two lemmas read           *)
(* consequences off it. Every number at which an input-indistinguishability   *)
(* program over that model states its proposition is at least the number, and *)
(* no certificate over it has its ideal cut within eps of the model's own cut *)
(* law once eps added to itself stays below the number. The second goes       *)
(* through indistinguishability_prop_of_ideal_close, the composition law for  *)
(* input indistinguishability with the number left free.                      *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   ExactWitness           == the security witness for exact independence    *)
(*   IndistinguishabilityCert                                                 *)
(*                          == the security certificate for input             *)
(*                             indistinguishability                           *)
(*   IdealProximityCert     == the security certificate for ideal proximity   *)
(*   SecurityEvidence       == the evidence an instance certifies with        *)
(*   SecurityProperty       == which security property, with no witness or    *)
(*                             certificate                                    *)
(*   evidence_property      == the security property the evidence proves      *)
(*   StackAt                == the data a program holds at one completion     *)
(*                             level                                          *)
(*   StackProp              == the proposition a program holds at one level   *)
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
(*   publish                == the terminal attaching the program's manifest  *)
(*                             path                                           *)
(*   PublishedAt            == a program's data, its manifest path and its    *)
(*                             theorem                                        *)
(*   run_correct_of         == run correctness of a published program         *)
(*   view_identification_of == its link lemma, the view as the direct         *)
(*                             computation                                    *)
(*   view_secrecy_of        == its security statement, under the              *)
(*                             exact-independence name                        *)
(*   view_indistinguishability_of                                             *)
(*                          == the same statement, under the                  *)
(*                             input-indistinguishability name                *)
(*   view_proximity_of      == the same statement, under the                  *)
(*                             ideal-proximity name                           *)
(*   security_property_of   == which security property a published program    *)
(*                             carries                                        *)
(*   PublishedObserved      == a program stopped at Observed, its path and    *)
(*                             run correctness                                *)
(*   PublishedSampled       == a program stopped at Sampled, its path and     *)
(*                             that level's two conjuncts                     *)
(*   TransferStatusWithoutTheorem                                             *)
(*                          == the transfer statuses carrying no theorem      *)
(*                             about an idealized model                       *)
(*   transfer_of_without_theorem                                              *)
(*                          == the manifest transfer status a payload of the  *)
(*                             Sampled terminal stands for                    *)
(*   publish_observed       == the terminal of a program stopped at Observed  *)
(*   publish_sampled        == the terminal of a program stopped at Sampled   *)
(*   run_correct_of_observed                                                  *)
(*                          == run correctness of a program published at      *)
(*                             Observed                                       *)
(*   run_correct_of_sampled == run correctness of a program published at      *)
(*                             Sampled                                        *)
(*   view_identification_of_sampled                                           *)
(*                          == the link lemma of a program published at       *)
(*                             Sampled                                        *)
(*   InputDistinguishabilityPropAt                                            *)
(*                          == some coalition below the privacy threshold     *)
(*                             reads two run arguments of the model's own cut *)
(*                             law at least c apart                           *)
(*   ObstructionKind        == which obstruction, with no proof of it         *)
(*   ObstructionProp        == the proposition an obstruction stands for: a   *)
(*                             positive number, and distinguishability at it  *)
(*   ObstructionPayload     == an obstruction at every field and index        *)
(*   ObstructionPayloadProp == the proposition such a payload asserts         *)
(*   PublishObstructionPayload                                                *)
(*                          == that payload together with its proof           *)
(*   mk_obstruction         == the two halves of it written apart             *)
(*   PublishedObstruction   == a program stopped at Sampled, its path and the *)
(*                             obstruction it publishes                       *)
(*   publish_obstruction    == the terminal handing over an obstruction       *)
(*   obstruction_of         == the obstruction of such a program              *)
(*   run_correct_of_obstruction                                               *)
(*                          == run correctness of such a program              *)
(*   view_identification_of_obstruction                                       *)
(*                          == its link lemma, the view as the direct         *)
(*                             computation                                    *)
(*                                                                            *)
(* Key results:                                                               *)
(*   tableau_left_unit      == sequencing onto a built tableau is application *)
(*   exact_tail             == the composition law for exact independence     *)
(*   indistinguishability_tail                                                *)
(*                          == the composition law for input                  *)
(*                             indistinguishability                           *)
(*   idealproximity_tail    == the composition law for ideal proximity        *)
(*   evidence_conclude      == the proposition the evidence proves, at a      *)
(*                             number above its own bound                     *)
(*   certify_exact_propertyE                                                  *)
(*                          == a program built by the exact statement carries *)
(*                             exact independence                             *)
(*   certify_indistinguishability_propertyE                                   *)
(*                          == a program built by that statement carries      *)
(*                             input indistinguishability                     *)
(*   certify_idealproximity_propertyE                                         *)
(*                          == a program built by the proximity statement     *)
(*                             carries ideal proximity                        *)
(*   conclude_propertyE     == concluding a program leaves its security       *)
(*                             property alone                                 *)
(*   publish_propertyE      == publishing a program leaves its security       *)
(*                             property alone                                 *)
(*   publish_observed_completionE                                             *)
(*                          == the path of a program published at Observed    *)
(*                             records Observed                               *)
(*   publish_observed_transferE                                               *)
(*                          == it records no model comparison                 *)
(*   publish_observed_modelE                                                  *)
(*                          == its model slot is empty                        *)
(*   publish_sampled_completionE                                              *)
(*                          == the path of a program published at Sampled     *)
(*                             records Sampled                                *)
(*   publish_sampled_transferE                                                *)
(*                          == it records the manifest status the program's   *)
(*                             last line wrote                                *)
(*   publish_sampled_modelE == its model slot is the family the program named *)
(*   indistinguishability_prop_of_ideal_close                                 *)
(*                          == the input-indistinguishability proposition at  *)
(*                             twice a bound on the distance from the model's *)
(*                             cut law to a certificate's ideal               *)
(*   input_distinguishability_prop_le                                         *)
(*                          == a model distinguishable at a number is         *)
(*                             distinguishable at every smaller number        *)
(*   indistinguishability_number_ge_of_input_distinguishability               *)
(*                          == a distinguishable model bounds from below the  *)
(*                             number an input-indistinguishability program   *)
(*                             over it publishes                              *)
(*   no_indistinguishability_cert_ideal_close_of_input_distinguishability     *)
(*                          == and leaves no certificate whose ideal cut is   *)
(*                             that close to its own cut law                  *)
(*   publish_obstruction_completionE                                          *)
(*                          == the path of a published obstruction records    *)
(*                             AnalysisBridged                                *)
(*   publish_obstruction_transferE                                            *)
(*                          == it records NegativeTransfer                    *)
(*   publish_obstruction_modelE                                               *)
(*                          == its model slot is the family the program named *)
(*   publish_obstruction_observedE                                            *)
(*                          == its observed execution is the program's own    *)
(*   publish_obstruction_assumptionsE                                         *)
(*                          == its assumption status is the line's payload    *)
(*   publish_obstruction_kindE                                                *)
(*                          == the obstruction it publishes is the one the    *)
(*                             line wrote                                     *)
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
(*     The security witnesses of the three properties                         *)
(******************************************************************************)

(* The exact-independence witness: a secret random variable on the sampled
   space, and, at every coalition below the privacy threshold, the
   independence of that coalition's static endpoint reading from it.
   Independence is the statement rather than a numeric leakage bound, and the
   entropy forms and the closure under post-processing are derived from it
   below, so an instance producing this record has nothing further to supply
   about mutual information. *)
Record ExactWitness (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) :=
  MkExactWitness {
    ew_secretT : finType ;
    ew_secret  : {RV (sa_sampleP sa) -> ew_secretT} ;
    ew_indep   : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
      (#|C| < profile_k (instance_profile A))%N ->
      sa_sampleP sa |= (fun u => static_coalition_obs C (sa.(sa_arg) u)
                                   (sa.(sa_cut) u)) _|_ ew_secret }.

(* The input-indistinguishability certificate: a marginal bound on the
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

(* The proximity certificate: a second sample adapter over the program's
   own execution, standing for the ideal run; an exact witness for that ideal,
   which is what makes the ideal a model whose own privacy is proved and not a
   bare law; the actual model's secret, typed at the carrier the ideal's witness
   names, so that the two models speak of one secret; a number; and, at every
   coalition below the privacy threshold, that number as a bound on the
   variation distance between the two models' joint laws of the coalition's
   reading and the secret. The comparison is an average over the run argument of
   each model and not a statement at a fixed run argument, and the number is an
   upper bound the instance chooses on what the actual model loses against an
   execution that leaks nothing, not a quantity the record determines: any
   number at which ipc_close is provable is a legal field, so a certificate says
   as much as its number is small and no more. *)
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

(* The evidence an instance certifies with, at one real field and one index of
   its analysis family: an exact-independence witness, an
   input-indistinguishability certificate or a proximity certificate. A program
   supplies one of the three here, and the proposition it carries from that
   line on is the one the evidence proves; the three are different statements
   about a coalition, so a program certifying input indistinguishability
   asserts nothing about mutual information. *)
Variant SecurityEvidence (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) : Type :=
  | ExactIndependence of ExactWitness sa
  | InputIndistinguishability of IndistinguishabilityCert sa
  | IdealProximity of IdealProximityCert sa.

(* Which of the three security properties a program commits to, with the
   witness and the certificate forgotten. A published program's manifest path
   records the execution, the level, the model family and the two statuses, and
   no theorem, so two programs over one model and one pair of statuses are one
   manifest path; the security property is where they differ, and a reader
   asking what a finished program proved about a coalition reads this and not
   the manifest. *)
Variant SecurityProperty :=
  ExactIndependenceProperty
  | InputIndistinguishabilityProperty
  | IdealProximityProperty.

(* The security property the evidence proves, with its witness or its
   certificate forgotten. The constructor alone decides the answer, so a
   program's security property is fixed by the certify statement that wrote the
   evidence and needs no proof about the model. *)
Definition evidence_property (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (p : SecurityEvidence sa) : SecurityProperty :=
  match p with
  | ExactIndependence _ => ExactIndependenceProperty
  | InputIndistinguishability _ => InputIndistinguishabilityProperty
  | IdealProximity _ => IdealProximityProperty
  end.
Arguments evidence_property {R A E sa} p.

(******************************************************************************)
(*     The completion-level stack                                             *)
(******************************************************************************)

(* The data a program holds at each completion level: an algebra; an algebra
   with its run parameters; those with the three run facts; those with an
   analysis model family; those with security evidence at every real field and
   index. The levels are the manifest's own, so the level of a program's last
   statement is the level the manifest records for it. Each component after the
   first is typed by the ones before it, which is what makes the sequencing
   below dependent. *)
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
                              SecurityEvidence (amf_sample f R idx)}}}}}}
  end.

(* The three run facts and the observed execution they build, at the Observed
   level. A statement reads its predecessor's data through these rather than
   through nested projT2 chains, which is what keeps the statements below
   readable as one line each.

   The nine run-fact accessors and ab_evidence return a Prop or a Type that
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

(* The same at the AnalysisBridged level, together with the security evidence
   at every real field and index. The evidence is a function of the real field
   because the analysis family is, so the security property a program
   certifies is certified uniformly and not at one chosen field. *)
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
Definition ab_evidence (q : StackAt AnalysisBridged) :
  forall (R : realType) (idx : amf_index (ab_f q) R),
    SecurityEvidence (amf_sample (ab_f q) R idx) :=
  projT2 (projT2 (projT2 (projT2 (projT2 (projT2 q))))).
Arguments ab_evidence : clear implicits.

(* The security property the data at this level carries, at one real field and
   one index. The evidence is a function of both, so the property is read at
   the arguments the evidence is written at rather than at one chosen field.
   The certify statements build evidence whose constructor is the same at every
   field and index, so for a program written in the surface the answer does not
   depend on either argument. *)
Definition ab_security_property (q : StackAt AnalysisBridged) (R : realType)
    (idx : amf_index (ab_f q) R) : SecurityProperty :=
  evidence_property (ab_evidence q R idx).
Arguments ab_security_property : clear implicits.

(******************************************************************************)
(*     The proposition family                                                 *)
(******************************************************************************)

(* The run-correctness conjunction of an observed execution, restated as the
   value of a proposition family rather than as the type of one theorem. A
   program's proposition has to be a function of the program's data, and this is
   the form in which correctness enters that function and is carried unchanged
   by every statement above it. *)
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
   It is the whole content of the Observed level: a program that supplies the
   three run facts reaches run correctness with no further proof. *)
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

(* The exact-independence proposition: below the threshold, the coalition's
   executed view is independent of the secret, its mutual information with the
   secret is zero, conditioning on it leaves the secret's entropy unchanged,
   and every deterministic function of it is still independent. Independence
   leads and the entropy forms follow it, so the information-theoretic reading
   of exact independence is proved from the same fact rather than assumed
   beside it. *)
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

(* The input-indistinguishability proposition: below the threshold, two run
   arguments give coalition readings of the cut within variation distance c. The
   bound is a parameter rather than the certificate's own sum, so conclude can
   state a finished program at any number at or above that sum, the constant a
   paper cites among them, without reproving the proposition. *)
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
   of the two run arguments the input-indistinguishability proposition
   compares. It is the number a program carries when its coordinate names
   none. *)
Definition cert_eps (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E))
    (cert : IndistinguishabilityCert sa) : R :=
  sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert).
Arguments cert_eps {R A E sa} cert.

(* The ideal-proximity proposition: below the threshold, the joint law of the
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
   the input-indistinguishability proposition, so conclude can state a
   finished program at any number at or above the certificate's ipc_eps, the
   one a paper cites among them. *)
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
   A single real will not serve, because the security evidence is given at
   every real field and the published number is therefore a function of it. *)
Definition ConcludedBound := forall R : realType, option R.

(* The coordinate that names nothing. Every program that publishes the bound it
   accumulated carries it. *)
Definition no_concluded_bound : ConcludedBound := fun _ => None.

(* The proposition the evidence proves at a given coordinate: independence for
   an exact-independence witness, the variation bound at the named number for an
   input-indistinguishability certificate, the distance to the ideal model's
   product law at the named number for a proximity certificate. The constructor
   selects the proposition, so a program cannot state one property's claim about
   another's witness. *)
Definition EvidenceProp (c : ConcludedBound) (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (p : SecurityEvidence sa) : Prop :=
  match p with
  | ExactIndependence w => ExactProp w
  | InputIndistinguishability cert =>
      IndistinguishabilityPropAt cert (odflt (cert_eps cert) (c R))
  | IdealProximity cert =>
      IdealProximityPropAt cert (odflt (ipc_eps cert) (c R))
  end.
Arguments EvidenceProp c {R A E sa} p.

(* What a program has proved at the AnalysisBridged level: run correctness, the
   view identification, and at every real field and index the proposition the
   evidence proves. The conjunction nests to the left, so each statement extends
   it by one conjunct on the right and the earlier conjuncts stay reachable
   by proj1. *)
Definition BridgedProp (c : ConcludedBound)
    (q : StackAt AnalysisBridged) : Prop :=
  (oe_correct_prop (ab_obs q) /\ sampled_viewE_prop (ab_f q))
  /\ forall (R : realType) (idx : amf_index (ab_f q) R),
       EvidenceProp c (ab_evidence q R idx).
Arguments BridgedProp c q : assert.

(* The proposition a program carries at each completion level: nothing about a
   coalition below Observed, run correctness at Observed, that with the view
   identification at Sampled, and the bridged conjunction at the program's own
   bound above it. This is the default proposition family of the carrier
   below, and the family a terminal leaves when it concludes a program.

   The match needs no return annotation: the expected type
   StackAt b -> Prop determines the motive. *)
Definition StackProp (b : CompletionLevel) : StackAt b -> Prop :=
  match b with
  | Algebraic       => fun _ => True
  | Executable      => fun _ => True
  | Observed        => fun q => oe_correct_prop (ob_obs q)
  | Sampled         => fun q => oe_correct_prop (sp_obs q)
                               /\ sampled_viewE_prop (sp_f q)
  | AnalysisBridged => fun q => BridgedProp no_concluded_bound q
  end.
Arguments StackProp : clear implicits.

(******************************************************************************)
(*     The carrier and its dependent bind                                     *)
(******************************************************************************)

(* A completion level's data together with a proof of a proposition about it.
   The carrier is indexed by the proposition family and not only by the level,
   because a terminal that concludes a program at a chosen number hands back a
   record at the same level whose proposition is no longer StackProp. *)
#[projections(primitive)]
Record TableauAt (b : CompletionLevel) (Q : StackAt b -> Prop) :=
  MkTableau {
    tableau_at  : StackAt b ;
    tableau_thm : Q tableau_at }.

Arguments TableauAt : clear implicits.

(* A tableau at the default proposition family of its level: what every line
   of a program returns until a terminal changes the family. *)
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

(* The surface of a program: a statement f applied to the program so far and to
   its payload p. Left associative, so a program reads as a sequence of
   statements applied to a growing coordinate; right associativity parses one
   line's payload as the next line's continuation. The infix >>= is taken by the
   fdist scope, so the separator is spelled of. *)
Notation "s ;;; f 'of' p" := (tableau_bind s f p)
  (at level 90, left associativity).

(* The first line of every program: an algebra, with the empty proposition its
   level carries. Nothing about a coalition has been proved at this point,
   which is what True records. *)
Definition tableau_start (A : PGGAlgebraic) : Tableau Algebraic :=
  @MkTableau Algebraic (StackProp Algebraic) A I.

(* Sequencing a statement onto a tableau built from given data and proof is that
   statement applied to them. The left unit law of the bind; it holds by
   conversion, so a program's proof term is the composition of its statements
   with no bookkeeping between the lines. *)
Lemma tableau_left_unit (a : CompletionLevel) (Q : StackAt a -> Prop)
    (P : StackAt a -> Type) (T : Type) (x : StackAt a) (pf : Q x)
    (f : forall y : StackAt a, Q y -> P y -> T) (p : P x) :
  tableau_bind (@MkTableau a Q x pf) f p = f x pf p.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The statements                                                         *)
(******************************************************************************)

(* From an algebra and a fuel, the run parameters of a dealer-dealt secret.
   The first statement of a dealer-dealt program, and the point at which the run
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
   line at which an instance's own reduction work enters a program. *)
Definition execute_step (x : StackAt Executable) (_ : StackProp Executable x)
    (p : ObsPayload x) : Tableau Observed :=
  @MkTableau Observed (StackProp Observed)
    (existT _ (projT1 x) (existT _ (projT2 x)
       (existT _ (projT1 p)
          (existT _ (projT1 (projT2 p)) (projT2 (projT2 p))))))
    (observed_correct _).

Arguments execute_step x _ p : assert.

(* The payload of sample_step: an analysis model family over the accumulated
   observed execution, the value that fixes the probability model a program's
   security statements are made in. *)
Definition FamPayload (x : StackAt Observed) : Type :=
  AnalysisModelFamily (ob_obs x).

(* Adjoins an analysis model family, reaching the Sampled level and proving that
   at every real field and index the executed coalition reader is the static
   one. It is the line that turns a program's claims from claims about the
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
   the accumulated family. Uniformity in the field is what makes the
   exact-independence conclusion unconditional rather than a statement at one
   chosen field. *)
Definition ExactPayload (x : StackAt Sampled) : Type :=
  forall (R : realType) (idx : amf_index (sp_f x) R),
    ExactWitness (amf_sample (sp_f x) R idx).

(* The payload of certify_indistinguishability: one
   input-indistinguishability certificate per real field and index of the
   accumulated family. Uniform in the field for the same reason the exact
   payload is, so the bound the program publishes is a bound at every field
   rather than at one chosen field. *)
Definition IndistinguishabilityPayload (x : StackAt Sampled) : Type :=
  forall (R : realType) (idx : amf_index (sp_f x) R),
    IndistinguishabilityCert (amf_sample (sp_f x) R idx).

(* The payload of certify_idealproximity: one proximity certificate per real
   field and index of the accumulated family. Uniform in the field for the
   reason the other two payloads are, so the ideal a program compares itself
   with and the number it loses against that ideal are fixed at every field. *)
Definition IdealProximityPayload (x : StackAt Sampled) : Type :=
  forall (R : realType) (idx : amf_index (sp_f x) R),
    IdealProximityCert (amf_sample (sp_f x) R idx).

(* The independence a witness states at the direct computation, transported
   to the view along the link lemma, with its entropy forms and
   its closure under deterministic post-processing. The composition law for
   exact independence, and what makes an ExactWitness the whole of what an
   instance supplies on it. *)
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
   transfer inequality, give the two-argument variation bound at cert_eps, the
   certificate's marginal-bound epsilon twice. The composition law for input
   indistinguishability, and the only place the mixing bound is used. *)
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

(* The input-indistinguishability proposition at twice a bound on the distance
   from the model's own cut law to a certificate's ideal cut. Each of the two
   readings of the cut law moves by at most that distance when the law is
   replaced by the ideal, and the certificate's fifth field makes the two
   readings of the ideal one law, so the two readings of the cut law lie
   within the distance twice. It is indistinguishability_tail with the number
   left free: that lemma is this one at the certificate's own marginal-bound
   epsilon, reached through ic_close and ic_Hd. Read in the other direction it
   is what turns a lower bound on the distance between two readings of the cut
   law into a statement about every certificate whose ideal sits close to that
   law. *)
Lemma indistinguishability_prop_of_ideal_close (R : realType)
    (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E))
    (cert : IndistinguishabilityCert sa) (eps : R) :
  var_dist (sa_cut_dist sa) (ic_ideal cert) <= eps ->
  IndistinguishabilityPropAt cert (eps + eps).
Proof.
move=> Hc C x x' HC.
have H1 : var_dist (fdistmap (static_coalition_obs C x) (sa_cut_dist sa))
                   (fdistmap (static_coalition_obs C x) (ic_ideal cert))
        <= eps.
  exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) Hc).
have Hconst : fdistmap (static_coalition_obs C x) (ic_ideal cert)
            = fdistmap (static_coalition_obs C x') (ic_ideal cert)
  := @ic_const R A E sa cert C HC x x'.
have H2 : var_dist (fdistmap (static_coalition_obs C x) (ic_ideal cert))
                   (fdistmap (static_coalition_obs C x') (sa_cut_dist sa))
        <= eps.
  rewrite Hconst symmetric_var_dist.
  exact: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) Hc).
exact: (Order.POrderTheory.le_trans (var_dist_triangle _ _ _) (lerD H1 H2)).
Qed.
Arguments indistinguishability_prop_of_ideal_close {R A E sa} cert eps.

(* The certificate's distance between the two models' joint laws, stated at
   the direct computation, carried to the executed readers of both models
   along the link lemma taken once for each, with the ideal joint law
   rewritten as the product of its two marginals by the ideal witness's
   independence. The composition law for ideal proximity; the two link
   hypotheses have the shape the previous statement proved, and the ideal's is
   available because the ideal adapter runs the program's own execution. *)
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

(* Adjoins the exact-independence witness at every real field and index,
   reaching AnalysisBridged with the exact-independence proposition proved by
   exact_tail from the previous line's identification. *)
Definition certify_exact (x : StackAt Sampled) (q : StackProp Sampled x)
    (p : ExactPayload x) : Tableau AnalysisBridged :=
  @MkTableau AnalysisBridged (StackProp AnalysisBridged)
    (existT _ (projT1 x) (existT _ (projT1 (projT2 x))
       (existT _ (sp_Ht x) (existT _ (sp_He x) (existT _ (sp_Hr x)
          (existT _ (sp_f x)
             (fun R idx => ExactIndependence (p R idx))))))))
    (conj q (fun R idx => exact_tail (p R idx) (proj2 q R idx))).

Arguments certify_exact x q p : assert.

(* Adjoins the input-indistinguishability certificate at every real field and
   index, reaching AnalysisBridged with the input-indistinguishability
   proposition proved by indistinguishability_tail. The certify statements are
   the only lines through which an instance's own mathematics enters a
   program; the payload of conclude is the one place outside a line where it
   enters. *)
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

(* Adjoins the proximity certificate at every real field and index, reaching
   AnalysisBridged with the ideal-proximity proposition proved by
   idealproximity_tail. The link lemma the previous statement proved serves the
   actual model, and the ideal model's is built here by the same lemma
   sample_step used, which applies because the certificate's ideal adapter runs
   this program's own execution and so meets this program's endpoint
   equation. *)
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

(* The obligation of conclude: at every real field and index, the number the
   program is concluded at is at least the certificate's own, and nothing for an
   exact-independence witness. A program may therefore publish the constant a
   paper cites whenever that constant is an upper bound of the distance the
   program proved, and may not publish a number below the one its certificate
   proved. An exact-independence witness carries no number, so concluding a
   program leaves it untouched. An upper bound is the right obligation because
   the two propositions that mention a number are monotone in it; a security
   property whose proposition is not monotone in that number needs a different
   obligation here. *)
Definition ConcludePayload (c : ConcludedBound)
    (q : StackAt AnalysisBridged) : Type :=
  forall (R : realType) (idx : amf_index (ab_f q) R),
    match ab_evidence q R idx with
    | ExactIndependence _ => unit
    | InputIndistinguishability cert =>
        cert_eps cert <= odflt (cert_eps cert) (c R)
    | IdealProximity cert => ipc_eps cert <= odflt (ipc_eps cert) (c R)
    end.
Arguments ConcludePayload c q : assert.

(* The proposition the evidence proves at the program's own bound, and a proof
   that a chosen number is at least that bound, give that proposition at the
   chosen number. The step is sound because the propositions that mention a
   number are monotone in it, which is the condition any future security
   property whose proposition mentions a number must satisfy as well; it is what
   lets a program state the constant a paper cites while asserting about the
   coalition no more than the certificate proved. *)
Lemma evidence_conclude (c : ConcludedBound) (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (p : SecurityEvidence sa) :
  EvidenceProp no_concluded_bound p ->
  (match p with
   | ExactIndependence _ => unit
   | InputIndistinguishability cert =>
       cert_eps cert <= odflt (cert_eps cert) (c R)
   | IdealProximity cert => ipc_eps cert <= odflt (ipc_eps cert) (c R)
   end) ->
  EvidenceProp c p.
Proof.
case: p => [w|cert|cert] //=.
- move=> H1 H2 C x x' HC.
  exact: Order.POrderTheory.le_trans (H1 C x x' HC) H2.
- move=> H1 H2 C HC.
  exact: Order.POrderTheory.le_trans (H1 C HC) H2.
Qed.
Arguments evidence_conclude c {R A E sa} p.

(* The terminal concluding a program at a chosen number, against a proof that
   the number is at least the program's accumulated bound. Post-processing of
   the published constant rather than a step: the data and the security property
   are unchanged, only the real the input-indistinguishability and the
   ideal-proximity propositions mention moves, and it moves only upward. *)
Definition conclude (c : ConcludedBound) (q : StackAt AnalysisBridged)
    (pf : StackProp AnalysisBridged q) (p : ConcludePayload c q)
    : TableauAt AnalysisBridged (BridgedProp c) :=
  @MkTableau AnalysisBridged (BridgedProp c) q
    (conj (proj1 pf)
       (fun R idx => evidence_conclude c (ab_evidence q R idx)
                       (proj2 pf R idx) (p R idx))).
Arguments conclude : clear implicits.

(* The payload of restate: a function from the proposition a program accumulated
   to the proposition its caller wants stated. The caller supplies the
   derivation, so restating is where a program's own conjunction is traded for
   the statement a downstream file cites, and nothing of the program survives
   the trade except what that derivation uses. *)
Definition RestatePayload (Q : Prop) (q : StackAt AnalysisBridged) : Type :=
  StackProp AnalysisBridged q -> Q.
Arguments RestatePayload Q q : assert.

(* A program's data together with an arbitrary proposition proved from what the
   program accumulated. The proposition is a parameter and not a field of the
   data, so two programs over the same instance may be handed over as different
   theorems. *)
Record RestatedTableau (Q : Prop) := MkRestatedTableau {
  rq_at  : StackAt AnalysisBridged ;
  rq_thm : Q }.
Arguments RestatedTableau : clear implicits.

(* The terminal handing a program over as a proposition its caller writes out.
   conclude is not an instance of it: conclude's target is BridgedProp of the
   ConcludedBound it is given, where this terminal's target Q is a parameter. *)
Definition restate (Q : Prop) (q : StackAt AnalysisBridged)
    (pf : StackProp AnalysisBridged q) (p : RestatePayload Q q)
    : RestatedTableau Q :=
  @MkRestatedTableau Q q (p pf).
Arguments restate : clear implicits.

(* A program's data, the manifest path describing it, and the proposition the
   program reached. The manifest already records the descriptive path; a
   published program is that same value with its theorem attached, so the
   manifest's claim about an instance and the proof of it are one term. *)
Record PublishedAt (c : ConcludedBound) := MkPublished {
  published_at   : StackAt AnalysisBridged ;
  published_path : AnalysisPath ;
  published_thm  : BridgedProp c published_at }.
Arguments PublishedAt : clear implicits.

(* A published program at the program's own bound: what a program whose
   coordinate names no number publishes. *)
Notation Published := (PublishedAt no_concluded_bound).

(* The terminal pairing the accumulated proposition with the manifest path for
   it. The assumption status precedes the coordinate because the sequencing
   carries one payload per line and the transfer status is that payload. *)
Definition publish (a : AssumptionStatus) (c : ConcludedBound)
    (q : StackAt AnalysisBridged) (pf : BridgedProp c q)
    (t : TransferStatus) : PublishedAt c :=
  @MkPublished c q
    (@MkAnalysisPath (ab_obs q) AnalysisBridged (ab_f q) t a) pf.
Arguments publish a {c} q pf t.

(* Run correctness of a published program: every process finishes, the endpoints
   number one per seat, and decoding them returns the dealt value. *)
Definition run_correct_of (c : ConcludedBound) (r : PublishedAt c) :=
  proj1 (proj1 (published_thm r)).
Arguments run_correct_of {c} r.

(* The link lemma of a published program, identifying its view with the direct
   computation, the fact on which its security statement is stated
   about a group action. *)
Definition view_identification_of (c : ConcludedBound) (r : PublishedAt c) :=
  proj2 (proj1 (published_thm r)).
Arguments view_identification_of {c} r.

(* The security statement of a published program, under the name a reader of
   exact independence expects. *)
Definition view_secrecy_of (c : ConcludedBound) (r : PublishedAt c) :=
  proj2 (published_thm r).
Arguments view_secrecy_of {c} r.

(* The same projection under the name a reader of input indistinguishability
   expects. The proposition is selected only when the result is applied, so
   naming the one that does not match a program fails at the next application
   rather than here. *)
Definition view_indistinguishability_of (c : ConcludedBound)
    (r : PublishedAt c) :=
  proj2 (published_thm r).
Arguments view_indistinguishability_of {c} r.

(* The same projection under the name a reader of ideal proximity expects.
   The three names are one term and differ in what a reader is told to expect
   of it, which is the proposition the evidence proves and is selected only
   when the result is applied. *)
Definition view_proximity_of (c : ConcludedBound) (r : PublishedAt c) :=
  proj2 (published_thm r).
Arguments view_proximity_of {c} r.

(* Which security property a published program carries, at one real field and
   one index of its family. It reads ab_security_property past the publish
   statement, and publish_propertyE is why the publish statement does not
   change the answer. *)
Definition security_property_of (c : ConcludedBound) (r : PublishedAt c)
    (R : realType) (idx : amf_index (ab_f (published_at r)) R)
  : SecurityProperty :=
  ab_security_property (published_at r) R idx.
Arguments security_property_of {c} r R idx.

(******************************************************************************)
(*     Handing a program over below AnalysisBridged                           *)
(******************************************************************************)

(* A program that stopped at Observed, handed over: its data, a manifest
   path, and run correctness of the observed execution that data reached. The
   path field is constrained by neither of the other two, as PublishedAt's is
   not: the terminal below builds it from the program's own data, and the
   record accepts any path written by hand beside any data. The proposition
   field is typed at the data field, as PublishedAt's third field is. A value
   carries StackProp Observed and nothing above it, so no coalition, privacy
   or security statement follows from one. *)
Record PublishedObserved := MkPublishedObserved {
  published_observed_at   : StackAt Observed ;
  published_observed_path : AnalysisPath ;
  published_observed_thm  : StackProp Observed published_observed_at }.

(* StackProp Observed unfolds to a statement quantified over a run argument,
   so Set Implicit Arguments would take the record for something to infer
   from that argument. *)
Arguments published_observed_thm : clear implicits.

(* A program that stopped at Sampled, handed over: its data, a manifest path,
   and run correctness together with the link lemma of the analysis model
   family the program named. The path field stands in the same relation to
   the other two. The program has proved no statement in which an idealized
   model occurs, so no security property is certified by such a value. *)
Record PublishedSampled := MkPublishedSampled {
  published_sampled_at   : StackAt Sampled ;
  published_sampled_path : AnalysisPath ;
  published_sampled_thm  : StackProp Sampled published_sampled_at }.

(* The two transfer statuses that carry no theorem about an idealized model.
   A program at Sampled has proved run correctness and the link lemma and
   nothing about an ideal, so these are the two its own proposition supports,
   and a path carrying either of them owes the manifest the premise it lacks
   rather than a theorem. *)
Variant TransferStatusWithoutTheorem :=
  SampledNoModelComparison | SampledStaticExecutedOnly.

(* The manifest transfer status a restricted payload stands for. It is the
   coordinate a reader of such a path finds, so the two statuses naming a
   transfer theorem never appear on a path the Sampled terminal built. *)
Definition transfer_of_without_theorem (t : TransferStatusWithoutTheorem)
    : TransferStatus :=
  match t with
  | SampledNoModelComparison => NoModelComparison
  | SampledStaticExecutedOnly => StaticExecutedOnly
  end.

(* The terminal of a program that stops at run correctness. The path takes
   the observed execution from the program's own data and the terminal writes
   the other three coordinates: the level Observed, the empty model slot, and
   NoModelComparison, which is not a payload because a program naming no
   model compares its execution with nothing. The assumption status is the
   line's payload. No level's proposition determines it and nothing ties it
   to Print Assumptions: it is the author's statement, and the manifest's
   prose defines when it is true. *)
Definition publish_observed (q : StackAt Observed) (pf : StackProp Observed q)
    (a : AssumptionStatus) : PublishedObserved :=
  @MkPublishedObserved q
    (@MkAnalysisPath (ob_obs q) Observed None NoModelComparison a) pf.

(* The data occurs in the type of the proof, so Set Implicit Arguments would
   infer it and the bind above, which passes the terminal unapplied, would
   have no slot to write it in. *)
Arguments publish_observed : clear implicits.

(* The terminal of a program that stops at a named analysis model family. The
   path takes the family the program's own data carries, and the transfer
   status is the line's payload at the restricted type, so the two statuses
   naming a transfer theorem are unreachable through this terminal. The
   restriction is carried by this terminal and not by the record, whose path
   field accepts any path. The assumption status stands on the same footing
   as at Observed. *)
Definition publish_sampled (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (t : TransferStatusWithoutTheorem)
    : PublishedSampled :=
  @MkPublishedSampled q
    (@MkAnalysisPath (sp_obs q) Sampled (sp_f q)
       (transfer_of_without_theorem t) a) pf.

(* The data occurs in the type of the proof here too. *)
Arguments publish_sampled : clear implicits.

(* The path of a program published at Observed records Observed. Conversion
   decides it, so a reader of the value learns the level its program stopped
   at without consulting the manifest. *)
Lemma publish_observed_completionE (q : StackAt Observed)
    (pf : StackProp Observed q) (a : AssumptionStatus) :
  ap_completion (published_observed_path (publish_observed q pf a)) = Observed.
Proof. exact: erefl. Qed.

(* The transfer status of such a path is fixed and not chosen: the program
   names no model, so nothing of it is compared with an idealized one. *)
Lemma publish_observed_transferE (q : StackAt Observed)
    (pf : StackProp Observed q) (a : AssumptionStatus) :
  ap_transfer (published_observed_path (publish_observed q pf a))
  = NoModelComparison.
Proof. exact: erefl. Qed.

(* The model slot of such a path is empty: the program named no model, so
   nothing in the path points at a distribution. *)
Lemma publish_observed_modelE (q : StackAt Observed)
    (pf : StackProp Observed q) (a : AssumptionStatus) :
  ap_model (published_observed_path (publish_observed q pf a)) = None.
Proof. exact: erefl. Qed.

(* The path of a program published at Sampled records Sampled, which is as far
   as that program's own proposition reaches. *)
Lemma publish_sampled_completionE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (t : TransferStatusWithoutTheorem) :
  ap_completion (published_sampled_path (publish_sampled a q pf t)) = Sampled.
Proof. exact: erefl. Qed.

(* The transfer status of such a path is the manifest status the line's
   payload stands for, and the manifest then owes that path the premise the
   status names as absent. *)
Lemma publish_sampled_transferE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (t : TransferStatusWithoutTheorem) :
  ap_transfer (published_sampled_path (publish_sampled a q pf t))
  = transfer_of_without_theorem t.
Proof. exact: erefl. Qed.

(* The model slot of such a path is the family the program's data carries, so
   the path names the model the link lemma was proved at and not a second
   family that resembles it. *)
Lemma publish_sampled_modelE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (t : TransferStatusWithoutTheorem) :
  ap_model (published_sampled_path (publish_sampled a q pf t)) = sp_f q.
Proof. exact: erefl. Qed.

(* Run correctness of a program published at Observed: every process
   finishes, the endpoints number one per seat, and decoding them returns the
   value the run recovers. It is the whole of what such a value proves, and
   the reader is the third field itself, so a value the execute rule built
   hands back the instance's own run-correctness field and the reader adds
   nothing to it. *)
Definition run_correct_of_observed (r : PublishedObserved)
  : oe_correct_prop (ob_obs (published_observed_at r)) :=
  published_observed_thm r.
Arguments run_correct_of_observed : clear implicits.

(* Run correctness of a program published at Sampled, the first of the two
   conjuncts that level carries. A reader of such a value learns that the run
   finished and that its endpoints decode, and nothing about a coalition. *)
Definition run_correct_of_sampled (r : PublishedSampled)
  : oe_correct_prop (sp_obs (published_sampled_at r)) :=
  proj1 (published_sampled_thm r).
Arguments run_correct_of_sampled : clear implicits.

(* The link lemma of a program published at Sampled, identifying its executed
   coalition reader with the direct computation at every real field and
   index. It is the second and last conjunct of that level, and the
   hypothesis along which a security statement about this model would be
   transported, were one proved. *)
Definition view_identification_of_sampled (r : PublishedSampled)
  : sampled_viewE_prop (sp_f (published_sampled_at r)) :=
  proj2 (published_sampled_thm r).
Arguments view_identification_of_sampled : clear implicits.

(******************************************************************************)
(*     An obstruction a program publishes at its model                        *)
(******************************************************************************)

(* Input distinguishability at c: some coalition below the privacy threshold
   reads two run arguments of the model's own cut law at least c apart, in the
   sum of absolute differences. It is the quantitative negation of the
   input-indistinguishability proposition, and no certificate occurs in it, so
   it is a fact about the model and the coalition's static reading and holds
   or fails whether or not a certificate over the model exists. The attack
   model is a static coalition of fewer than k seats reading its own
   endpoints, and the two run arguments are named rather than drawn, so a
   distinguisher told which two arguments to compare has advantage at least
   half of c there, var_dist summing the absolute differences and so being
   twice the total variation distance of the literature. *)
Definition InputDistinguishabilityPropAt (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (c : R) : Prop :=
  exists (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1})
         (x x' : ex_inputT E),
    (#|C| < profile_k (instance_profile A))%N /\
    c <= var_dist (fdistmap (static_coalition_obs C x) (sa_cut_dist sa))
                  (fdistmap (static_coalition_obs C x') (sa_cut_dist sa)).
Arguments InputDistinguishabilityPropAt {R A E} sa c.

(* A model distinguishable at c is distinguishable at every smaller number,
   the same coalition and the same two run arguments witnessing it. The family
   is downward closed in c, so the sharpest statement one coalition and one
   pair of run arguments support is the one at the distance between their
   two readings. *)
Lemma input_distinguishability_prop_le (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (c c' : R) :
  c' <= c ->
  InputDistinguishabilityPropAt sa c -> InputDistinguishabilityPropAt sa c'.
Proof.
move=> Hle [C [x [x' [HC Hge]]]].
by exists C, x, x'; split=> //; exact: (Order.POrderTheory.le_trans Hle Hge).
Qed.

(* Every number at which an input-indistinguishability program over a
   distinguishable model states its proposition is at least the number the
   model is distinguishable at. That proposition bounds the distance between
   the readings of every two run arguments, and distinguishability exhibits
   two whose distance reaches c, so c bounds from below what such a program
   can publish, whatever its certificate. *)
Lemma indistinguishability_number_ge_of_input_distinguishability
    (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E))
    (cert : IndistinguishabilityCert sa) (c c' : R) :
  InputDistinguishabilityPropAt sa c ->
  IndistinguishabilityPropAt cert c' -> c <= c'.
Proof.
move=> [C [x [x' [HC Hge]]]] Hprop.
exact: (Order.POrderTheory.le_trans Hge (Hprop C x x' HC)).
Qed.

(* Over a model distinguishable at c, no input-indistinguishability
   certificate has its ideal cut within eps of the model's own cut law once
   eps added to itself stays below c. The law is the model's and not a free
   argument: a certificate's second and fourth fields place its ideal within
   its marginal bound of the cut law the model draws and of no other law. The
   route is indistinguishability_prop_of_ideal_close, which turns closeness of
   the ideal into the proposition at eps twice, against which the number bound
   above is then read. *)
Lemma no_indistinguishability_cert_ideal_close_of_input_distinguishability
    (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E)) (c eps : R) :
  InputDistinguishabilityPropAt sa c -> eps + eps < c ->
  forall cert : IndistinguishabilityCert sa,
    var_dist (sa_cut_dist sa) (ic_ideal cert) <= eps -> False.
Proof.
move=> Hd Heps cert Hc.
have Hge := indistinguishability_number_ge_of_input_distinguishability Hd
  (indistinguishability_prop_of_ideal_close cert eps Hc).
by move: (Order.POrderTheory.le_lt_trans Hge Heps);
   rewrite Order.POrderTheory.ltxx.
Qed.

(* The obstructions a program may publish at one model, one constructor each.
   A constructor of SecurityEvidence names a security property a program
   certifies; a constructor here names a fact about the model from which no
   security property follows, so the two enumerations are disjoint in kind and
   this one leaves SecurityEvidence with its three members. It is a closed
   enumeration and not a free proposition: a free proposition is what restate
   hands over, and a reader of a free payload cannot tell what kind of fact
   was published. The one member carries the number the model is
   distinguishable at, and the proposition that member stands for requires
   that number positive. At a number at or below zero the inequality is free,
   var_dist being non-negative, and the empty coalition is below every
   threshold, so the distinguishability proposition alone would hold at every
   model whose run-argument type is inhabited. Positivity is what makes a
   published member a comparison of two readings of the model. *)
Variant ObstructionKind (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) : Type :=
  | InputDistinguishabilityObstruction of R.

(* The proposition a kind stands for: at the one member, the number is above
   zero and the model is input distinguishable at it. The constructor selects
   the proposition, as the constructor of SecurityEvidence selects the
   proposition EvidenceProp gives, so a program cannot publish one kind's
   constructor with another kind's proof. Positivity sits here and not in
   InputDistinguishabilityPropAt, which is the downward-closed family a
   number bound is read against and which a smaller number must stay in. *)
Definition ObstructionProp (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (o : ObstructionKind sa) : Prop :=
  match o with
  | InputDistinguishabilityObstruction c =>
      0 < c /\ InputDistinguishabilityPropAt sa c
  end.

(* A kind at every real field and every index of a program's model family. The
   security evidence of a program is given at every field and index, and an
   obstruction is given at every field and index for the same reason: the
   model is a family and a statement at one chosen field would describe a
   member and not the model. The kind may differ at each field and each index,
   as ExactPayload and its two companions may, so a reader of a published
   obstruction reads the number off the field and the index it asks about. *)
Definition ObstructionPayload (q : StackAt Sampled) : Type :=
  forall (R : realType) (idx : amf_index (sp_f q) R),
    ObstructionKind (amf_sample (sp_f q) R idx).
Arguments ObstructionPayload q : assert.

(* The proposition such a payload asserts: its kind's proposition at every
   real field and every index, as BridgedProp is the proposition a program's
   evidence asserts there. *)
Definition ObstructionPayloadProp (q : StackAt Sampled)
    (o : ObstructionPayload q) : Prop :=
  forall (R : realType) (idx : amf_index (sp_f q) R), ObstructionProp (o R idx).
Arguments ObstructionPayloadProp q o : assert.

(* The payload of the terminal below: a kind at every field and index together
   with its proof. The two travel as one term because the terminal carries one
   payload per line. *)
Definition PublishObstructionPayload (q : StackAt Sampled) : Type :=
  { o : ObstructionPayload q & ObstructionPayloadProp o }.
Arguments PublishObstructionPayload q : assert.

(* The two halves written apart, as mk_indistinguishability writes a
   certificate's five components apart: a statement then displays the
   proposition claimed and the proof of it as two named things. *)
Definition mk_obstruction (q : StackAt Sampled) (o : ObstructionPayload q)
    (H : ObstructionPayloadProp o) : PublishObstructionPayload q :=
  existT _ o H.
Arguments mk_obstruction : clear implicits.

(* A program's data at Sampled, the manifest path describing it, the
   obstruction it publishes and two proofs: what the program proved at
   Sampled, and the obstruction. It certifies no security property, its data
   carrying no SecurityEvidence, and it denies only what its kind names; a
   program over the same model publishing security evidence is untouched by
   it, the two being facts about one model. The path field is constrained by
   neither of the others, as PublishedAt's is not. *)
Record PublishedObstruction := MkPublishedObstruction {
  published_obstruction_at   : StackAt Sampled ;
  published_obstruction_path : AnalysisPath ;
  published_obstruction_kind : ObstructionPayload published_obstruction_at ;
  published_obstruction_thm  : StackProp Sampled published_obstruction_at ;
  published_obstruction_pf   : ObstructionPayloadProp
                                 published_obstruction_kind }.

(* ObstructionPayload, StackProp Sampled and ObstructionPayloadProp all unfold
   to quantified statements, so Unset Strict Implicit takes the record for
   something to infer and the quantifier's own binder steals its slot. *)
Arguments published_obstruction_kind : clear implicits.
Arguments published_obstruction_thm : clear implicits.
Arguments published_obstruction_pf : clear implicits.

(* The terminal of a program that stops at a named model and publishes an
   obstruction there. The path is built from the program's own data: the
   observed execution the program reached, the level AnalysisBridged, the
   model family the sample statement named, and NegativeTransfer, which is not
   a payload because the record's own proposition is the theorem that status
   names. The assumption status is the line's payload, as it is at the two
   terminals below AnalysisBridged. *)
Definition publish_obstruction (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (p : PublishObstructionPayload q)
    : PublishedObstruction :=
  @MkPublishedObstruction q
    (@MkAnalysisPath (sp_obs q) AnalysisBridged (sp_f q) NegativeTransfer a)
    (projT1 p) pf (projT2 p).

(* The data occurs in the types of the proof and the payload, so Set Implicit
   Arguments would infer it and the bind, which passes the terminal unapplied,
   would have no slot to write it in. *)
Arguments publish_obstruction : clear implicits.

(* The level of such a path is AnalysisBridged. The manifest's own definition
   of that level reads "AnalysisBridged + bridge alias to a named security,
   leakage, mixing or limitation theorem about the same distribution and the
   same observer", and an obstruction is a limitation theorem about the
   model's own cut law and the path's observer. Conversion decides it. *)
Lemma publish_obstruction_completionE (a : AssumptionStatus)
    (q : StackAt Sampled) (pf : StackProp Sampled q)
    (p : PublishObstructionPayload q) :
  ap_completion (published_obstruction_path (publish_obstruction a q pf p))
  = AnalysisBridged.
Proof. exact: erefl. Qed.

(* The transfer status is fixed and not chosen: NegativeTransfer is defined as
   a theorem transporting an obstruction to the path's observer, and the
   record's own proposition is that theorem. *)
Lemma publish_obstruction_transferE (a : AssumptionStatus)
    (q : StackAt Sampled) (pf : StackProp Sampled q)
    (p : PublishObstructionPayload q) :
  ap_transfer (published_obstruction_path (publish_obstruction a q pf p))
  = NegativeTransfer.
Proof. exact: erefl. Qed.

(* The model slot is the family the program's own data carries, so the path
   names the model the obstruction was proved at and not a second family that
   resembles it. *)
Lemma publish_obstruction_modelE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (p : PublishObstructionPayload q) :
  ap_model (published_obstruction_path (publish_obstruction a q pf p))
  = sp_f q.
Proof. exact: erefl. Qed.

(* The observed execution of the path is the run the program made its three
   run facts about. *)
Lemma publish_obstruction_observedE (a : AssumptionStatus)
    (q : StackAt Sampled) (pf : StackProp Sampled q)
    (p : PublishObstructionPayload q) :
  ap_observed (published_obstruction_path (publish_obstruction a q pf p))
  = sp_obs q.
Proof. exact: erefl. Qed.

(* The assumption status of the path is the line's payload, on the same
   footing as at the other three terminals. *)
Lemma publish_obstruction_assumptionsE (a : AssumptionStatus)
    (q : StackAt Sampled) (pf : StackProp Sampled q)
    (p : PublishObstructionPayload q) :
  ap_assumptions (published_obstruction_path (publish_obstruction a q pf p))
  = a.
Proof. exact: erefl. Qed.

(* The obstruction such a value publishes is the one the line wrote, so a
   reader of the value learns which fact was claimed without unfolding the
   terminal. *)
Lemma publish_obstruction_kindE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (o : ObstructionPayload q)
    (H : ObstructionPayloadProp o) :
  published_obstruction_kind
    (publish_obstruction a q pf (mk_obstruction q o H)) = o.
Proof. exact: erefl. Qed.

(* The obstruction of a published program, under the name a reader of a
   refutation expects. It is the whole of what such a value says beyond the
   Sampled level: every reader of this file that names a security statement
   or a security property takes a PublishedAt, and PublishedObstruction is a
   different inductive type, so none of them applies to a value of it. *)
Definition obstruction_of (r : PublishedObstruction)
  : ObstructionPayloadProp (published_obstruction_kind r) :=
  published_obstruction_pf r.
Arguments obstruction_of : clear implicits.

(* Run correctness of such a program, the first of the two conjuncts the
   Sampled level carries. *)
Definition run_correct_of_obstruction (r : PublishedObstruction)
  : oe_correct_prop (sp_obs (published_obstruction_at r)) :=
  proj1 (published_obstruction_thm r).
Arguments run_correct_of_obstruction : clear implicits.

(* The link lemma of such a program, identifying its executed coalition reader
   with the direct computation. It is the fact the obstruction is stated
   beside: the obstruction is about the direct reader, and this is what ties
   that reader to the run. *)
Definition view_identification_of_obstruction (r : PublishedObstruction)
  : sampled_viewE_prop (sp_f (published_obstruction_at r)) :=
  proj2 (published_obstruction_thm r).
Arguments view_identification_of_obstruction : clear implicits.

(******************************************************************************)
(*     Where a program's security property is decided                         *)
(******************************************************************************)

(* A program built by the exact statement carries exact independence at every
   real field and index of its family. With conclude_propertyE and
   publish_propertyE below it settles the security property of a finished
   program by one line of the program's text, so a reader needs no argument
   about the instance's probability model to know which statement the program
   proved. *)
Lemma certify_exact_propertyE (x : StackAt Sampled) (q : StackProp Sampled x)
    (p : ExactPayload x) (R : realType)
    (idx : amf_index (ab_f (tableau_at (@certify_exact x q p))) R) :
  ab_security_property (tableau_at (@certify_exact x q p)) R idx
  = ExactIndependenceProperty.
Proof. by []. Qed.

(* The same for the input-indistinguishability statement. With
   certify_exact_propertyE this is what makes the security property readable
   off the program's text: the certify statements are the only ones that build
   evidence, and each writes one constructor at every field and index. *)
Lemma certify_indistinguishability_propertyE (x : StackAt Sampled)
    (q : StackProp Sampled x) (p : IndistinguishabilityPayload x)
    (R : realType)
    (idx : amf_index
             (ab_f (tableau_at (@certify_indistinguishability x q p))) R) :
  ab_security_property (tableau_at (@certify_indistinguishability x q p)) R idx
  = InputIndistinguishabilityProperty.
Proof. by []. Qed.

(* The same for the proximity statement. The three statements are the only
   ones that build evidence, and each writes one constructor at every field
   and index, so a reader of a program's text knows which of the three claims
   the program will publish. *)
Lemma certify_idealproximity_propertyE (x : StackAt Sampled)
    (q : StackProp Sampled x) (p : IdealProximityPayload x) (R : realType)
    (idx : amf_index (ab_f (tableau_at (@certify_idealproximity x q p))) R) :
  ab_security_property (tableau_at (@certify_idealproximity x q p)) R idx
  = IdealProximityProperty.
Proof. by []. Qed.

(* Concluding a program at a chosen number leaves its security property where
   the certify statement put it. The terminal moves a real and not the
   alternative the program committed to, so a program at the constant a paper
   cites states the same kind of fact about a coalition as the program at its
   own bound. *)
Lemma conclude_propertyE (c : ConcludedBound) (q : StackAt AnalysisBridged)
    (pf : StackProp AnalysisBridged q) (p : ConcludePayload c q)
    (R : realType)
    (idx : amf_index (ab_f (tableau_at (conclude c q pf p))) R) :
  ab_security_property (tableau_at (conclude c q pf p)) R idx
  = ab_security_property q R idx.
Proof. by []. Qed.

(* Publishing attaches the manifest path and leaves the security property
   alone, so the property a finished program reports is the one its data
   carried before the last line. This is the step that carries the three
   certify statements' property equations out to a published program. *)
Lemma publish_propertyE (a : AssumptionStatus) (c : ConcludedBound)
    (q : StackAt AnalysisBridged) (pf : BridgedProp c q) (t : TransferStatus)
    (R : realType)
    (idx : amf_index (ab_f (published_at (publish a q pf t))) R) :
  security_property_of (publish a q pf t) R idx = ab_security_property q R idx.
Proof. by []. Qed.
