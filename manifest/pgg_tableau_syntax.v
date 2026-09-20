(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* The statement surface of a Tableau program                                 *)
(*                                                                            *)
(* A program of pgg_tableau.v is a sequence of binds over anonymous tuples.   *)
(* This file gives each statement a named surface, so that a statement says   *)
(* which fact occupies which clause and a term written in the wrong clause is *)
(* rejected where it is written rather than deep inside an existT. Nothing    *)
(* here changes what a program proves: every rule expands to one              *)
(* tableau_bind, and the accumulated proposition is that of pgg_tableau.v     *)
(* unchanged. The three lemmas hold by conversion: one identifies the         *)
(* dealer-dealt statement with params_step, and two say that a run whose      *)
(* parameters take the ideal function from a Targeted meets the               *)
(* specification that Targeted names.                                         *)
(*                                                                            *)
(* Two typed builders carry the work. obs_payload takes the three run facts   *)
(* in order at the data the previous statement reached; its point is that the *)
(* data is passed explicitly, because a clause elaborated at an evar-typed    *)
(* position accepts an obligation for the wrong proposition, and an ltac:     *)
(* clause at such a position is closed by done with a term that proves        *)
(* nothing. mk_indistinguishability takes the five components of a            *)
(* certificate separately, each quantified over the real field and the model  *)
(* index, so a statement displays the marginal bound, the equation between    *)
(* that bound's law and the model's cut law, the ideal cut, the mixing        *)
(* distance and the constancy of a coalition's view of the ideal cut in the   *)
(* run argument as five named things rather than one record. The statement    *)
(* binds those two variables once, after at, and abstracts every clause over  *)
(* them, so a clause is a term in R and idx rather than a function of them.   *)
(* The proximity rule takes its certificate whole and has no builder, because *)
(* four of that record's five fields are terms of the instance and the fifth  *)
(* is the number, so a builder would display the plumbing and not the         *)
(* mathematics.                                                               *)
(*                                                                            *)
(* The termination statement comes in two forms. One names a lemma; the other *)
(* writes the literal vm_compute and builds the obligation in place. The two  *)
(* are not the same term, so a program through the literal is a different     *)
(* program from one through the lemma, proving the same proposition.          *)
(*                                                                            *)
(* The separator of the terminal rules is |>. Measured on 2026-09-14, |>      *)
(* occurs as a standalone notation token nowhere in the kept tree, MathComp   *)
(* with analysis, infotheo or Stdlib: every occurrence is inside infotheo's   *)
(* convex notation x <| p |> y, in fdist_scope and fsdist_scope, and in       *)
(* mathcomp-analysis convex.v, with which it was checked to coexist in one    *)
(* file.                                                                      *)
(*                                                                            *)
(* A run is driven in one of three modes and there is a statement for each.   *)
(* dealt and supplied are the sharing family: no party commits and the dealer *)
(* lays the cards itself, from the algebra's own secret under dealt and from  *)
(* the layout the run argument names under supplied. encoded is the input     *)
(* family: the committers hand over their inputs through commit processes and *)
(* the dealer assembles the layout from what they committed. Two of the three *)
(* expand to one statement body, params_step, differing in the parameter      *)
(* record their clauses build; the dealer-dealt rule expands to dealt_step,   *)
(* which dealt_params_stepE identifies with params_step at                    *)
(* dealt_secret_params.                                                       *)
(*                                                                            *)
(* The three run obligations at execute are the only proofs whose statements  *)
(* mention the interpreter. The by clause of encoded is a proof too, but      *)
(* ts_valid takes a secret and a share tuple and nothing else, so it          *)
(* constrains the layout and not the run, and it is what makes the program's  *)
(* recon clause a bare lemma name.                                            *)
(*                                                                            *)
(* The surface reserves nineteen identifiers as global keywords in every file *)
(* that requires this one: dealt, functionality, execute, endpoints, recon,   *)
(* sample, certify, leaks, tied, ideal, mixing, invariant, encoded, supplied, *)
(* layout, decoded_by, committed_by, expecting and fuel. Each follows a slot  *)
(* in some rule. Measured on 2026-09-14, fuel is among them: it follows the   *)
(* literal dealt in the dealer-dealt rule and would stay an identifier for    *)
(* that rule alone, but it follows a slot in the two rules added beside it.   *)
(* The tokens inputs, terminates, publish, conclude, vm_compute,              *)
(* ExactIndependence, InputIndistinguishability and IdealProximity follow a   *)
(* literal and stay identifiers, which is what keeps the three evidence       *)
(* constructors and the conclude terminal usable by name; at follows a        *)
(* literal too, the literal leaks in one rule and InputIndistinguishability   *)
(* in the other, and was a keyword of Rocq before this file. by follows the   *)
(* slot L of the encoded rule, the slot k of the leaks rule and the slot c of *)
(* the conclude rule, so it would be a twentieth, and it is not one only      *)
(* because ssreflect already reserves it, measured on 2026-09-19 by binding   *)
(* it in a file that requires nothing but ssreflect. Observed and Sampled     *)
(* follow a literal too, measured on 2026-09-21: each follows the literal     *)
(* publish in one of the two terminal rules below AnalysisBridged, each stays *)
(* a binder name in a file whose Require lines are ssreflect and this one,    *)
(* and each stays the CompletionLevel constructor it names, as Tableau        *)
(* Observed in s5_tableau_observed.v and Tableau Sampled in                   *)
(* s5_tableau_sampled.v write it. The count of nineteen is unchanged. Inside  *)
(* the publish position the two tokens are taken by those two rules, so the   *)
(* transfer-status slot of the three-payload rule cannot be filled by a bare  *)
(* token spelled Observed or Sampled, though a parenthesised one reaches the  *)
(* slot.                                                                      *)
(*                                                                            *)
(* One of the nineteen shadows a framework definition: endpoints is also the  *)
(* verifier's endpoint tuple in pgg_interface.v. A file requiring this        *)
(* surface must write that one through its module path. No file in the tree   *)
(* writes it bare. No file requiring the surface writes any of the other      *)
(* eighteen bare either, and no declaration of this file binds any of the     *)
(* nineteen: the two realisation lemmas bind L and n, and dealt_params_stepE  *)
(* binds x, q and n.                                                          *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   obs_payload  == the three run facts in the shape execute_step wants      *)
(*   mk_indistinguishability                                                  *)
(*                == a certificate at every field and index, from its five    *)
(*                   components                                               *)
(*   Targeted     == an algebra with the ideal function a run of it computes  *)
(*   targeted_F   == the Functionality a Targeted names                       *)
(*   ExactLeakAt  == some coalition of k seats has a view of positive mutual  *)
(*                   information with the secret                              *)
(*   exact_leaks  == the witness again, with such an annotation checked       *)
(*   params_step  == the statement raising a program to Executable at given   *)
(*                   parameters                                               *)
(*                                                                            *)
(* Key results:                                                               *)
(*   dealt_params_stepE == the dealer-dealt statement is params_step at the   *)
(*                         dealer-dealt parameters                            *)
(*   encoded_realises_expected                                                *)
(*                      == an input-family run meets the Targeted's           *)
(*                         specification                                      *)
(*   supplied_realises_expected                                               *)
(*                      == the same for a sharing-family run                  *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_analysis_manifest.
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
(*     The two typed builders                                                 *)
(******************************************************************************)

(* The three run facts of a parameter record, in the order execute_step reads
   them. The accumulated data is an argument and not inferred, which is what
   fixes each of the three propositions before its obligation is
   elaborated. *)
Definition obs_payload (x : StackAt Executable)
    (Ht : instance_terminates_stmt (projT2 x))
    (He : instance_endpoints_stmt (projT2 x))
    (Hr : instance_recon_stmt (projT2 x)) : ObsPayload x :=
  existT _ Ht (existT _ He Hr).
Arguments obs_payload : clear implicits.

(* A certificate at every real field and every index of the accumulated model,
   assembled from its five components: the cut's marginal bound, the equation
   between that bound's law and the law the model draws its cut from, the
   ideal cut, the distance of the drawn cut from the ideal, and the constancy
   of a coalition's view of the ideal cut in the run argument. The split is
   what makes the certificate's perfect and statistical halves visible where
   it is written: the fourth component is an inequality at the first
   component's epsilon, and the fifth is an equation. *)
Definition mk_indistinguishability (x : StackAt Sampled)
    (b : forall (R : realType) (idx : amf_index (sp_f x) R),
           ShuffleMarginalBound R (instance_M (projT1 x)))
    (Hd : forall (R : realType) (idx : amf_index (sp_f x) R),
            sw_rho_dist (b R idx) = sa_cut_dist (amf_sample (sp_f x) R idx))
    (u : forall (R : realType) (idx : amf_index (sp_f x) R),
           R.-fdist (pgg_gT (mp_M (instance_profile (projT1 x)))))
    (Hc : forall (R : realType) (idx : amf_index (sp_f x) R),
            var_dist (sw_rho_dist (b R idx)) (u R idx)
            <= sw_bound_eps (b R idx))
    (Hk : forall (R : realType) (idx : amf_index (sp_f x) R)
            (C : {set 'I_(pi_T' (mp_PI (instance_profile (projT1 x)))).+1}),
            (#|C| < profile_k (instance_profile (projT1 x)))%N ->
            forall y y' : ex_inputT (projT1 (projT2 x)),
              fdistmap (static_coalition_obs C y) (u R idx)
              = fdistmap (static_coalition_obs C y') (u R idx))
    : IndistinguishabilityPayload x :=
  fun R idx => @MkIndistinguishabilityCert R (projT1 x) (projT1 (projT2 x))
    (amf_sample (sp_f x) R idx)
    (b R idx) (Hd R idx) (u R idx) (Hc R idx) (Hk R idx).
Arguments mk_indistinguishability : clear implicits.

(******************************************************************************)
(*     The ideal function a run computes                                      *)
(******************************************************************************)

(* An algebra together with the ideal function a run of it is meant to compute,
   from whatever a run takes as argument to the value it reconstructs. The
   record exists because the completion-level stack carries no functionality:
   the accumulated proposition is about a coalition's view and never mentions
   the ideal function, so naming one happens beside the program rather than
   inside it. For a dealer-dealt run the ideal function is forced to be the
   identity, and the record is written only for an input family, where it is
   not.

   targeted_F is what such a run is measured against: a run whose recovered
   value ex_expected is written as this ideal function meets realises_expected
   by conversion, which is the whole obligation of the functionality statement.

   The consumer is the encoded statement below: it reads the algebra, the input
   carrier and the ideal function off this record and writes them into the
   parameter record the run is driven by, so the function a program names and
   the value its run recovers are one term and not two that agree. *)
Record Targeted := MkTargeted {
  tg_algebra : PGGAlgebraic ;
  tg_inputT  : Type ;
  tg_f       : tg_inputT -> pga_secretT tg_algebra }.

(* The tg_f projection returns an arrow, so Unset Strict Implicit takes the
   record for something to infer and the arrow's own argument steals its
   slot; the directive pins it back. *)
Arguments tg_f : clear implicits.

(* The specification a Targeted names: its own ideal function, at the privacy
   threshold of the algebra's scheme. The threshold is read off the scheme and
   not written, because an execution narrows no coalition size the scheme
   already guarantees. *)
Definition targeted_F (t : Targeted)
    : Functionality (tg_inputT t) (pga_secretT (tg_algebra t)) :=
  MkFunctionality (tg_f t) (ts_k' (pga_scheme (tg_algebra t))).

Notation "A 'functionality' f" := (@MkTargeted A _ f)
  (at level 90, left associativity, f at level 0).

(* An input-family run whose parameters take the ideal function from the
   Targeted itself meets that specification. The two sides are the same term, so
   the identification realises_expected asks for is conversion and the
   correctness half of such a program is discharged by reflexivity.

   A program therefore closes this obligation by by [] and never cites the
   lemma. Where the lemma is applied instead, every argument is written through
   @: each one before the three run facts occurs in their types and is implicit,
   and leaving them to unification does not close the goal, because apply-style
   unification will not reduce the definition a goal names to the parameter
   record this conclusion builds. *)
Lemma encoded_realises_expected (t : Targeted) L Hv d procs n Ht He Hr :
  realises_expected
    (@instance_observed (tg_algebra t)
       (encoded_input_params (tg_algebra t) (tg_inputT t) (tg_f t)
          L Hv d procs n) Ht He Hr)
    (targeted_F t).
Proof. by []. Qed.

(* The same for a sharing-family run at a supplied layout. Such a statement
   writes the value the run recovers in its own expecting clause rather than
   taking it from a Targeted, so a program that also names a functionality meets
   it when the two are convertible, which is what this lemma asks of them.

   It is closed by by [] in a program and applied with every argument written
   elsewhere, for the reason above. *)
Lemma supplied_realises_expected (t : Targeted) L n Ht He Hr :
  realises_expected
    (@instance_observed (tg_algebra t)
       (supplied_input_params (tg_algebra t) (tg_inputT t) L (tg_f t) n)
       Ht He Hr)
    (targeted_F t).
Proof. by []. Qed.

(******************************************************************************)
(*     The tightness annotation of exact independence                         *)
(******************************************************************************)

(* At every real field and index, some coalition of exactly k seats reads a
   view whose mutual information with the secret is strictly positive. It is
   the affirmation, at size k, of what an ExactWitness denies below the
   threshold, stated at the same reader ew_indep is stated at, so the two are
   claims about one object rather than two.

   A scheme guarantees nothing at or above its threshold, and this is what
   separates a threshold that is sharp from one that is merely as far as a
   proof reached. It is an annotation on the guarantee and not part of it: k
   occurs in the type, so the kernel checks the number against the proof, and
   the annotated program is convertible with the unannotated one. It attaches
   to exact independence alone, so a program certifying input
   indistinguishability carries no such claim. *)
Definition ExactLeakAt (k : nat) (x : StackAt Sampled) (p : ExactPayload x)
    : Prop :=
  forall (R : realType) (idx : amf_index (sp_f x) R),
    exists C : {set 'I_(pi_T' (mp_PI (instance_profile (projT1 x)))).+1},
      #|C| = k
      /\ 0 < `I( ew_secret (p R idx) ;
                 (fun u => static_coalition_obs C
                             ((amf_sample (sp_f x) R idx).(sa_arg) u)
                             ((amf_sample (sp_f x) R idx).(sa_cut) u)) ).
Arguments ExactLeakAt : clear implicits.

(* The exact-independence witness, with a tightness annotation checked against
   it and then dropped. The result is the witness itself, so the annotation
   leaves the term a program builds unchanged and everything proved about an
   annotated program is proved about the unannotated one. *)
Definition exact_leaks (x : StackAt Sampled) (p : ExactPayload x)
    (k : nat) (H : ExactLeakAt k x p) : ExactPayload x := p.
Arguments exact_leaks : clear implicits.

(******************************************************************************)
(*     The program statements                                                 *)
(******************************************************************************)

Notation "A 'dealt' 'fuel' n" := (tableau_start A ;;; dealt_step of n)
  (at level 90, left associativity, n at level 0).

(* From an algebra and a parameter record, the statement that raises a program
   to Executable at those parameters. The encoded and supplied rules below
   differ only in the record their clauses build, and dealt_step is this
   statement at dealt_secret_params. *)
Definition params_step (x : StackAt Algebraic) (_ : StackProp Algebraic x)
    (E : ExecutionParams x) : Tableau Executable :=
  @MkTableau Executable (StackProp Executable)
    (existT (fun A : PGGAlgebraic => ExecutionParams A) x E) I.

(* The algebra occurs in the types of the two arguments after it, which the
   file-level Unset Strict Implicit would otherwise take for a reason to infer
   it. The rules below pass the name unapplied to tableau_bind and are
   unaffected. *)
Arguments params_step : clear implicits.

(* The dealer-dealt statement is this one at the dealer-dealt parameters. The
   two are the same term, so a program written with either reaches the same
   completion level. *)
Lemma dealt_params_stepE (x : StackAt Algebraic) (q : StackProp Algebraic x)
    (n : nat) :
  dealt_step q n = params_step x q (dealt_secret_params x n).
Proof. by []. Qed.

(* The input family. The committers named in committed_by hand over their
   inputs, decoded_by reads the joint input back out of the payload list they
   committed, and layout turns that input into the sharing the dealer deals.

   The by clause is the sharing claim of the encoding, that the layout is a
   valid sharing of the ideal function's value at the same input. It is checked
   where it is written and read back from the parameter term by
   encoded_static_recon, so the reconstruction obligation of such a program is
   that lemma's name and nothing else.

   The algebra and the ideal function come from the Targeted on the left, so the
   value the run recovers is the one functionality named, and a program cannot
   name one function and recover another. *)
Notation "t 'encoded' 'inputs' T 'layout' L 'by' enc 'decoded_by' d 'committed_by' procs 'fuel' n" :=
  (tableau_start (tg_algebra t) ;;; params_step
     of (encoded_input_params (tg_algebra t) T (tg_f t) L enc d procs n))
  (at level 90, left associativity, T at level 10, L at level 10,
   enc at level 10, d at level 10, procs at level 10, n at level 0,
   only parsing).

(* The sharing family at a supplied layout. The layout arrives with the run
   argument and no party commits, so the run carries no commit process and the
   dealer lays the cards itself from the layout the argument names.

   expecting is the value the run recovers, a reading of the run argument
   rather than an ideal function of committed inputs, which is why the
   statement begins at an algebra and not at a Targeted. The sharing claim is
   not written here, so such a program discharges its reconstruction
   obligation through supplied_static_recon at its own algebra and validity
   lemma, or through the interpreter. *)
Notation "A 'supplied' 'inputs' T 'layout' L 'expecting' e 'fuel' n" :=
  (tableau_start A ;;; params_step of (supplied_input_params A T L e n))
  (at level 90, left associativity, T at level 10, L at level 10,
   e at level 10, n at level 0, only parsing).

(* The run the three obligations are made about is the framework's own process
   list, exec_saprocs of pgg_execution_plug.v: a dealer carrying the plug's
   content function, a verifier, one player per seat, and then ep_input_procs,
   the commit processes an input family supplies and a sharing family leaves
   empty. exec_procs is that list erased to what the interpreter consumes, and
   termination and the endpoint equation are both stated over it.

   What this statement builds is the observed execution, and publish writes it
   unchanged into the path's ap_observed. A program therefore describes the run
   these three obligations were proved about, and not a second run that
   resembles it. *)
Notation "s 'execute' 'terminates' 'by' t 'endpoints' 'by' e 'recon' 'by' r" :=
  (s ;;; execute_step of (obs_payload (tableau_at s) t e r))
  (at level 90, left associativity, t at level 0, e at level 0, r at level 0,
   only parsing).

Notation "s 'execute' 'terminates' 'by' 'vm_compute' 'endpoints' 'by' e 'recon' 'by' r" :=
  (s ;;; execute_step
       of (obs_payload (tableau_at s) ltac:(by vm_compute) e r))
  (at level 90, left associativity, e at level 0, r at level 0, only parsing).

Notation "s 'sample' f" := (s ;;; sample_step of f)
  (at level 90, left associativity, f at level 0).

Notation "s 'certify' 'ExactIndependence' w" := (s ;;; certify_exact of w)
  (at level 90, left associativity, w at level 0).

Notation "s 'certify' 'ExactIndependence' w 'leaks' 'at' k 'by' H" :=
  (s ;;; certify_exact of (exact_leaks (tableau_at s) w k H))
  (at level 90, left associativity, w at level 0, k at level 0, H at level 0,
   only parsing).

Notation "s 'certify' 'InputIndistinguishability' c" :=
  (s ;;; certify_indistinguishability of c)
  (at level 90, left associativity, c at level 0).

(* The proximity rule takes its certificate whole and has no builder. The
   input-indistinguishability rule has both that form, above, and the
   five-clause builder mk_indistinguishability below. *)
Notation "s 'certify' 'IdealProximity' c" :=
  (s ;;; certify_idealproximity of c)
  (at level 90, left associativity, c at level 0).

(* The five clauses name the real field and the model index once, after at,
   and the statement abstracts every clause over them. Each component is a
   term in those two variables rather than a function of them, so what a
   clause displays is the component and not the plumbing that quantifies it. *)
Notation "s 'certify' 'InputIndistinguishability' 'at' R idx b 'tied' 'by' Hd 'ideal' u 'mixing' 'by' Hc 'invariant' 'by' Hk" :=
  (s ;;; certify_indistinguishability of (mk_indistinguishability (tableau_at s)
     (fun R idx => b) (fun R idx => Hd) (fun R idx => u)
     (fun R idx => Hc) (fun R idx => Hk)))
  (at level 90, left associativity, R ident, idx ident,
   b at level 10, Hd at level 10, u at level 10, Hc at level 10,
   Hk at level 10, only parsing).

(* The number a program publishes, and the proof that the program's own bound is
   at most that number. The terminal is written in the same surface as the
   statements of a program, so a program that publishes a constant a paper cites
   is one program in one language and not a program that falls back to the bind
   at its last two lines. *)
Notation "s |> 'conclude' c 'by' p" := (s ;;; conclude c of p)
  (at level 90, left associativity, c at level 0, p at level 0).

(* The two statuses are written transfer first, against the argument order of
   publish itself, so that a program's last statement reads in the order the
   manifest column headings run. *)
Notation "s |> 'publish' t a" := (s ;;; publish a of t)
  (at level 90, left associativity, t at level 0, a at level 0).

(* One payload, the assumption status. The terminal takes the observed
   execution from the program's own data and writes the other three
   coordinates itself: the level, the empty model slot and
   NoModelComparison. *)
Notation "s |> 'publish' 'Observed' a" := (s ;;; publish_observed of a)
  (at level 90, left associativity, a at level 0).

(* The transfer status and then the assumption status, in the order the
   manifest's path record carries them and the order the three-payload
   publish rule writes them. The status slot is the restricted payload type,
   so a program at this level cannot write one of the two statuses that name
   a transfer theorem. *)
Notation "s |> 'publish' 'Sampled' t a" := (s ;;; publish_sampled a of t)
  (at level 90, left associativity, t at level 0, a at level 0).
