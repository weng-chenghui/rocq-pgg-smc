(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Tableau: the row program of one protocol instance                        *)
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
(* There are five statements. dealt_step fixes the run argument to be the     *)
(* dealer's secret and chooses a fuel. execute_step adjoins the three run     *)
(* facts and reaches run correctness. sample_step adjoins an analysis model   *)
(* family and proves that the executed coalition reader is the static one,    *)
(* which is what moves the row from a claim about interpreter messages to a   *)
(* claim about a group action. certify_exact and certify_spectral adjoin a    *)
(* security witness of one of the two arms. Both arms speak only of a         *)
(* coalition below the privacy threshold, and they are not comparable         *)
(* statements: the exact arm concludes independence of the coalition's view   *)
(* from the secret, unconditionally and at every real field, while the        *)
(* spectral arm concludes a variation distance between the readings of two    *)
(* run arguments, bounded by the certificate's mixing epsilon. A row commits  *)
(* to one of them and claims nothing about the other.                         *)
(*                                                                            *)
(* Each arm has one composition law, and the two laws are where the           *)
(* mathematics of the row sits. exact_tail transports a witness's             *)
(* independence from the static reader to the executed one along the previous *)
(* line's identification, then derives the entropy forms by                   *)
(* leakage_of_view_indep and the closure under deterministic post-processing  *)
(* by inde_RV_comp. spectral_tail feeds the certificate's cut-carrier         *)
(* distance and its ideal constancy to var_dist_fdistmap_transfer.            *)
(*                                                                            *)
(* Two things stay outside the program. The mathematics of a particular       *)
(* instance never appears as a line: it enters only as the witness or the     *)
(* certificate a certify statement takes, so an instance owes one record per  *)
(* arm and no proof about the framework. And of the three terminals only      *)
(* conclude returns a Tableau and so only it has a step's shape, but it is    *)
(* outside: it leaves the data and the arms untouched and moves only the real *)
(* the spectral arm's proposition mentions.                                   *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   ExactWitness            == the exact arm's security witness              *)
(*   SpectralCert            == the spectral arm's security certificate       *)
(*   SecurityPort            == the arm an instance certifies                 *)
(*   StackAt                 == the data a row holds at one completion level  *)
(*   StackProp               == the proposition a row holds at one level      *)
(*   TableauAt               == data at a level with a proof about it         *)
(*   tableau_bind            == sequencing, written s ;;; f 'of' p            *)
(*   dealt_step              == the statement dealing a secret at a fuel      *)
(*   execute_step            == the statement adjoining the three run facts   *)
(*   sample_step             == the statement adjoining an analysis family    *)
(*   certify_exact           == the statement adjoining an exact witness      *)
(*   certify_spectral        == the statement adjoining a spectral cert       *)
(*   conclude                == the terminal republishing the bound           *)
(*   restate                 == the terminal handing over a proposition       *)
(*   publish                 == the terminal attaching the row's manifest row *)
(*   PublishedRowAt          == a row's data, its manifest row and theorem    *)
(*   run_correct_of          == run correctness of a published row            *)
(*   view_identification_of  == its executed-to-static view equation          *)
(*   view_secrecy_of         == its security statement, exact-arm name        *)
(*   view_indist_of          == the same statement, spectral-arm name         *)
(*                                                                            *)
(* Key results:                                                               *)
(*   tableau_left_unit       == sequencing onto a tableau is application      *)
(*   exact_tail              == the exact arm's composition law               *)
(*   spectral_tail           == the spectral arm's composition law            *)
(*   port_reprice            == a port's proposition at a renamed bound       *)
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
(*     The two security witnesses                                             *)
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

(* The spectral arm's certificate: a marginal bound on the instance's shuffle,
   the identification of the bound's law with the adapter's cut, an ideal cut
   law within that bound in variation distance, and the constancy of a
   coalition's reading of the ideal cut in the run argument. Five fields and
   not the two of a marginal bound alone: the transfer inequality is stated on
   the cut carrier, where it needs both a distance and the ideal constancy,
   and a per-position marginal bound holds neither. *)
Record SpectralCert (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) :=
  MkSpectralCert {
    sc_b : ShuffleMarginalBound R (instance_M A) ;
    sc_Hd : sw_rho_dist sc_b = sa_cut_dist sa ;
    sc_ideal : R.-fdist (pgg_gT (mp_M (instance_profile A))) ;
    sc_close : var_dist (sw_rho_dist sc_b) sc_ideal <= sw_bound_eps sc_b ;
    sc_const : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
        (#|C| < profile_k (instance_profile A))%N ->
        forall x x' : ex_inputT E,
          fdistmap (static_coalition_obs C x) sc_ideal
          = fdistmap (static_coalition_obs C x') sc_ideal }.

(* Which of the two arms an instance certifies, at one real field and one
   index of its analysis family. A row commits to an arm here, and the
   proposition it carries from that line on is that arm's own; the two are
   different claims about a coalition, so a row certifying decay asserts
   nothing about mutual information. *)
Variant SecurityPort (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) : Type :=
  | ExactIndependence of ExactWitness sa
  | SpectralDecay of SpectralCert sa.

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

(* The spectral arm's proposition: below the threshold, two run arguments give
   coalition readings of the cut within variation distance c. The bound is a
   parameter rather than the certificate's own sum, so a terminal can restate
   a finished row at the number a paper cites without reproving the arm. *)
Definition SpectralPropAt (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : SpectralCert sa) (c : R) : Prop :=
  forall (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1})
         (x x' : ex_inputT E),
    (#|C| < profile_k (instance_profile A))%N ->
    var_dist (fdistmap (static_coalition_obs C x) (sa_cut_dist sa))
             (fdistmap (static_coalition_obs C x') (sa_cut_dist sa))
    <= c.
Arguments SpectralPropAt {R A E sa} cert c.

(* A certificate's own bound: the marginal bound's epsilon twice, one for each
   of the two run arguments the arm compares. It is the number a row carries
   when nothing restates it. *)
Definition cert_eps (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E)) (cert : SpectralCert sa) : R :=
  sw_bound_eps (sc_b cert) + sw_bound_eps (sc_b cert).
Arguments cert_eps {R A E sa} cert.

(* A bound named once per real field, with None meaning the chain's own sum. A
   single real will not serve, because the security port quantifies over the
   real field and the published number is therefore a function of it. *)
Definition Reprice := forall R : realType, option R.

(* The reprice that names nothing. It is the coordinate of every row that
   publishes the bound it accumulated. *)
Definition no_reprice : Reprice := fun _ => None.

(* The proposition a port carries at a given reprice: independence for the
   exact arm, the variation bound at the named number for the spectral arm.
   The arm selects the proposition, so a row cannot state one arm's claim
   about the other's witness. *)
Definition PortProp (c : Reprice) (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (p : SecurityPort sa) : Prop :=
  match p with
  | ExactIndependence w => ExactProp w
  | SpectralDecay cert => SpectralPropAt cert (odflt (cert_eps cert) (c R))
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
   identification at Sampled, and the bridged conjunction at the chain's own
   bound above it. This is the default proposition family of the carrier
   below, and the family a terminal leaves when it republishes a row.

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
   because a terminal that republishes the bound hands back a record at the
   same level whose proposition is no longer StackProp. *)
#[projections(primitive)]
Record TableauAt (b : CompletionLevel) (Q : StackAt b -> Prop) :=
  MkTableau {
    tableau_at  : StackAt b ;
    tableau_thm : Q tableau_at }.

Arguments TableauAt : clear implicits.

(* A Tableau at the default proposition family of its level: what every line
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

(* The surface of a row: a statement f applied to the chain so far and to its
   payload p. Left associative, so a row reads as a sequence of statements
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

(* Sequencing a statement onto a Tableau built from given data and proof is
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

(* The payload of certify_spectral: one spectral certificate per real field
   and index of the accumulated family. Uniform in the field for the same
   reason the exact payload is, so the bound the arm publishes is a bound at
   every field rather than at one chosen field. *)
Definition SpectralPayload (x : StackAt Sampled) : Type :=
  forall (R : realType) (idx : amf_index (sp_f x) R),
    SpectralCert (amf_sample (sp_f x) R idx).

(* The independence a witness states at the static reader, transported to the
   executed reader along the view identification, with its entropy forms and
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
   transfer inequality, give the two-argument variation bound at the
   certificate's own epsilon. The composition law of the spectral arm, and the
   only place the mixing bound is used. *)
Lemma spectral_tail (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E)) (cert : SpectralCert sa) :
  SpectralPropAt cert (cert_eps cert).
Proof.
move=> C x x' HC.
apply: (var_dist_fdistmap_transfer R _ _ (sa_cut_dist sa) (sc_ideal cert)
  (static_coalition_obs C x) (static_coalition_obs C x')
  (sw_bound_eps (sc_b cert))).
- by rewrite -(sc_Hd cert); exact: (sc_close cert).
- exact: (@sc_const _ _ _ _ cert C HC x x').
Qed.
Arguments spectral_tail {R A E sa} cert.

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

(* Adjoins the spectral arm's certificate at every real field and index,
   reaching AnalysisBridged with the arm's proposition proved by
   spectral_tail. The two certify statements are the only lines through which
   an instance's own mathematics enters a row. *)
Definition certify_spectral (x : StackAt Sampled) (q : StackProp Sampled x)
    (p : SpectralPayload x) : Tableau AnalysisBridged :=
  @MkTableau AnalysisBridged (StackProp AnalysisBridged)
    (existT _ (projT1 x) (existT _ (projT1 (projT2 x))
       (existT _ (sp_Ht x) (existT _ (sp_He x) (existT _ (sp_Hr x)
          (existT _ (sp_f x)
             (fun R idx => SpectralDecay (p R idx))))))))
    (conj q (fun R idx => spectral_tail (p R idx))).

Arguments certify_spectral x q p : assert.

(******************************************************************************)
(*     The terminals                                                          *)
(******************************************************************************)

(* The obligation of conclude: at every real field and index, one numeric
   identity for a spectral port and nothing for an exact port. The exact arm
   carries no number, so renaming a bound leaves it untouched. *)
Definition RepricePayload (c : Reprice) (q : StackAt AnalysisBridged) : Type :=
  forall (R : realType) (idx : amf_index (ab_f q) R),
    match ab_port q R idx with
    | ExactIndependence _ => unit
    | SpectralDecay cert => cert_eps cert = odflt (cert_eps cert) (c R)
    end.
Arguments RepricePayload c q : assert.

(* A port's proposition at the chain's own bound, with an identity naming
   another number, is that port's proposition at the other number. Renaming
   proves nothing new about the coalition, and it is what lets a row publish
   the constant a paper cites. *)
Lemma port_reprice (c : Reprice) (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (p : SecurityPort sa) :
  PortProp no_reprice p ->
  (match p with
   | ExactIndependence _ => unit
   | SpectralDecay cert => cert_eps cert = odflt (cert_eps cert) (c R)
   end) ->
  PortProp c p.
Proof. by case: p => [w|cert] //= H1 H2; rewrite -H2. Qed.
Arguments port_reprice c {R A E sa} p.

(* The terminal republishing a row's accumulated bound at a chosen number.
   Post-processing of the published constant rather than a step: the data and
   the arms are unchanged, and only the real the spectral arm's proposition
   mentions moves. *)
Definition conclude (c : Reprice) (q : StackAt AnalysisBridged)
    (pf : StackProp AnalysisBridged q) (p : RepricePayload c q)
    : TableauAt AnalysisBridged (BridgedProp c) :=
  @MkTableau AnalysisBridged (BridgedProp c) q
    (conj (proj1 pf)
       (fun R idx => port_reprice c (ab_port q R idx)
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
   framework from the reprice, this one's is supplied. *)
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

(* A published row at the chain's own bound: what a row that never restates
   its number publishes. *)
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

(* The executed-to-static view identification of a published row, the fact on
   which its security statement is stated about a group action. *)
Definition view_identification_of (c : Reprice) (r : PublishedRowAt c) :=
  proj2 (proj1 (published_thm r)).
Arguments view_identification_of {c} r.

(* The security statement of a published row, under the name a reader of the
   exact arm expects. *)
Definition view_secrecy_of (c : Reprice) (r : PublishedRowAt c) :=
  proj2 (published_thm r).
Arguments view_secrecy_of {c} r.

(* The same projection under the name a reader of the spectral arm expects.
   The arm is selected only when the result is applied, so naming the one that
   does not match a row fails at the next application rather than here. *)
Definition view_indist_of (c : Reprice) (r : PublishedRowAt c) :=
  proj2 (published_thm r).
Arguments view_indist_of {c} r.
