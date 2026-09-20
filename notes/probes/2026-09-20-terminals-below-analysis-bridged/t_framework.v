(* PROBE, not production. Rows T1, T2, T4, T5 and the framework half of T6 of *)
(* notes/20260920-terminals-below-analysis-bridged-probe-design.md.           *)
(*                                                                            *)
(* A program that honestly stops below AnalysisBridged has no terminal today: *)
(* publish takes a StackAt AnalysisBridged. This file compiles the record     *)
(* family and the two terminals the spec designs, at the framework's own      *)
(* carrier and at no instance.                                                *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finset reals.
From pgg_smc Require Import pgg_observed_execution.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     T1: the level-indexed published record                                 *)
(******************************************************************************)

(* A program's data at one completion level, the manifest path describing it,
   and the proposition that level's StackProp carries about the data. It sits
   beside PublishedAt and does not replace it: a value of this record asserts
   StackProp l and nothing above it, so no coalition, privacy or security
   statement follows from one below AnalysisBridged. *)
Record PublishedAtLevel (l : CompletionLevel) := MkPublishedAtLevel {
  published_level_at   : StackAt l ;
  published_level_path : AnalysisPath ;
  published_level_thm  : StackProp l published_level_at }.

(* A program whose last statement is the three run facts: run correctness of
   the observed execution, and no model. *)
Notation PublishedObserved := (PublishedAtLevel Observed).

(* A program whose last statement names an analysis model family: run
   correctness and the link lemma of that family, and no security evidence. *)
Notation PublishedSampled := (PublishedAtLevel Sampled).

(* The model slot of a path at Observed is the option type, so a path whose
   program names no model carries the empty slot, and the slot at Sampled is
   the family itself. These two conversions are what let the terminals below
   build the slot from the program's own data rather than take it as a
   payload. *)
Section ModelSlotShapes.
Variable obs : OE.ObservedExecution.

Check (erefl : AnalysisModelSlot obs Observed
               = option (AnalysisModelFamily obs)).
Check (None : AnalysisModelSlot obs Observed).
Check (erefl : AnalysisModelSlot obs Sampled = AnalysisModelFamily obs).

End ModelSlotShapes.

(******************************************************************************)
(*     T2: the two terminals                                                  *)
(******************************************************************************)

(* The terminal of a program that stops at the three run facts. The path is
   built from the program's own data: the observed execution the program
   reached, the level Observed, the empty model slot, and NoModelComparison,
   which is not a payload because a program that names no model compares its
   execution with nothing. The assumption status is a payload, because it
   records what the instance's own proofs accept and the program cannot read
   it off its data. *)
Definition publish_observed (a : AssumptionStatus) (s : Tableau Observed)
    : PublishedObserved :=
  @MkPublishedAtLevel Observed (tableau_at s)
    (@MkAnalysisPath (ob_obs (tableau_at s)) Observed None NoModelComparison a)
    (tableau_thm s).

(* The terminal of a program that stops at a named analysis model family. The
   path takes the family the program's own data carries, and the transfer
   status is a payload because a program at this level may carry a refutation
   of a model comparison as well as no comparison at all. *)
Definition publish_sampled (a : AssumptionStatus) (t : TransferStatus)
    (s : Tableau Sampled) : PublishedSampled :=
  @MkPublishedAtLevel Sampled (tableau_at s)
    (@MkAnalysisPath (sp_obs (tableau_at s)) Sampled (sp_f (tableau_at s)) t a)
    (tableau_thm s).

(* The path of a program published at Observed records the level the program
   stopped at. Conversion decides it, so the manifest's sentence about how far
   a path's theorems reach is a term at this level and not prose. *)
Lemma publish_observed_completionE (a : AssumptionStatus)
    (s : Tableau Observed) :
  ap_completion (published_level_path (publish_observed a s)) = Observed.
Proof. exact: erefl. Qed.

(* The transfer status of such a path is fixed, not chosen: no model is named,
   so no comparison with an idealized model is claimed. *)
Lemma publish_observed_transferE (a : AssumptionStatus) (s : Tableau Observed) :
  ap_transfer (published_level_path (publish_observed a s))
  = NoModelComparison.
Proof. exact: erefl. Qed.

(* The model slot of such a path is empty. *)
Lemma publish_observed_modelE (a : AssumptionStatus) (s : Tableau Observed) :
  ap_model (published_level_path (publish_observed a s)) = None.
Proof. exact: erefl. Qed.

(* The Sampled twin of the completion equation. *)
Lemma publish_sampled_completionE (a : AssumptionStatus) (t : TransferStatus)
    (s : Tableau Sampled) :
  ap_completion (published_level_path (publish_sampled a t s)) = Sampled.
Proof. exact: erefl. Qed.

(* The transfer status of a path published at Sampled is the one the program's
   last line wrote. *)
Lemma publish_sampled_transferE (a : AssumptionStatus) (t : TransferStatus)
    (s : Tableau Sampled) :
  ap_transfer (published_level_path (publish_sampled a t s)) = t.
Proof. exact: erefl. Qed.

(* The model slot of such a path is the family the program's data carries, so
   the path names the model the program's link lemma was proved at and not a
   second family that resembles it. *)
Lemma publish_sampled_modelE (a : AssumptionStatus) (t : TransferStatus)
    (s : Tableau Sampled) :
  ap_model (published_level_path (publish_sampled a t s))
  = sp_f (tableau_at s).
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The bind-shaped spelling of the Sampled terminal                       *)
(******************************************************************************)

(* The Sampled terminal written in the argument shape publish itself has, so
   that it can be sequenced by the bind with the transfer status as the line's
   payload. The Observed terminal has no payload and therefore no such
   spelling. *)
Definition publish_sampled_step (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (t : TransferStatus) : PublishedSampled :=
  @MkPublishedAtLevel Sampled q
    (@MkAnalysisPath (sp_obs q) Sampled (sp_f q) t a) pf.

(* The two spellings of the Sampled terminal are one term, so a surface rule
   may expand to either. *)
Lemma publish_sampled_stepE (a : AssumptionStatus) (t : TransferStatus)
    (s : Tableau Sampled) :
  (s ;;; publish_sampled_step a of t) = publish_sampled a t s.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     T4: the readers a level-published program admits                       *)
(******************************************************************************)

(* Run correctness of the observed execution a program's data reaches, at
   every level. Below Observed a program has proved nothing about a run, which
   is what True records; above it the conjunction nests to the left and run
   correctness stays the leftmost conjunct. *)
Definition level_run_correct (l : CompletionLevel) : StackAt l -> Prop :=
  match l with
  | Algebraic | Executable => fun _ => True
  | Observed => fun q => oe_correct_prop (ob_obs q)
  | Sampled => fun q => oe_correct_prop (sp_obs q)
  | AnalysisBridged => fun q => oe_correct_prop (ab_obs q)
  end.
Arguments level_run_correct : clear implicits.

(* Run correctness of a program published at its own level: every process
   finishes, the endpoints number one per seat, and decoding them returns the
   value the run recovers. It is the whole content of a program published at
   Observed. *)
Definition run_correct_of_level (l : CompletionLevel) (r : PublishedAtLevel l)
    : level_run_correct l (published_level_at r) :=
  match l return forall u : PublishedAtLevel l,
                   level_run_correct l (published_level_at u) with
  | Algebraic => fun _ => I
  | Executable => fun _ => I
  | Observed => fun u => published_level_thm u
  | Sampled => fun u => proj1 (published_level_thm u)
  | AnalysisBridged => fun u => proj1 (proj1 (published_level_thm u))
  end r.

(* The link lemma of a program published at Sampled, identifying its executed
   coalition reader with the direct computation at every real field and index.
   It is the second and last conjunct of that level, and the fact on which a
   security statement would be made were one proved. *)
Definition view_identification_of_sampled (r : PublishedSampled)
    : sampled_viewE_prop (sp_f (published_level_at r)) :=
  proj2 (published_level_thm r).

(******************************************************************************)
(*     T5: no security reader applies below AnalysisBridged                   *)
(******************************************************************************)

Section NoSecurityReaderBelowBridged.
Variable r : PublishedObserved.

(* The exact-independence reader takes a PublishedAt, whose data is at
   AnalysisBridged. *)
Fail Check (view_secrecy_of r).

(* So does the reader naming which security property a program certified. *)
Fail Check (security_property_of r).

(* And a program published at Observed is not a Published: the two records are
   different types, so a downstream file cannot silently read one for the
   other. *)
Fail Check (r : Published).

End NoSecurityReaderBelowBridged.

(* The Observed terminal refuses a program that has not reached Observed. *)
Fail Check (fun (a : AssumptionStatus) (s : Tableau Executable) =>
              publish_observed a s).

(******************************************************************************)
(*     T6: which transfer statuses a Sampled program may carry                *)
(******************************************************************************)

(* The transfer statuses a program at Sampled can honestly write: no model
   comparison at all, or a theorem transporting an obstruction to the
   program's own observer. The two statuses TransferStatus also offers name a
   transfer theorem, which a program with no security evidence has not
   proved. *)
Variant SampledTransfer :=
  SampledNoModelComparison | SampledNegativeTransfer.

(* The manifest's own status a SampledTransfer stands for. *)
Definition transfer_of_sampled (t : SampledTransfer) : TransferStatus :=
  match t with
  | SampledNoModelComparison => NoModelComparison
  | SampledNegativeTransfer => NegativeTransfer
  end.

(* The Sampled terminal restricted to the two statuses a program at that level
   can write, the payload type being the restriction. *)
Definition publish_sampled_restricted (a : AssumptionStatus)
    (t : SampledTransfer) (s : Tableau Sampled) : PublishedSampled :=
  publish_sampled a (transfer_of_sampled t) s.

(* The restricted terminal writes the status its payload names. *)
Lemma publish_sampled_restricted_transferE (a : AssumptionStatus)
    (t : SampledTransfer) (s : Tableau Sampled) :
  ap_transfer (published_level_path (publish_sampled_restricted a t s))
  = transfer_of_sampled t.
Proof. exact: erefl. Qed.

(* The restricted terminal refuses IdealFinite, which names a public
   model-transfer theorem. *)
Fail Check (fun (a : AssumptionStatus) (s : Tableau Sampled) =>
              publish_sampled_restricted a IdealFinite s).

(* The unrestricted terminal accepts it, a status being data. *)
Check (fun (a : AssumptionStatus) (s : Tableau Sampled) =>
         publish_sampled a IdealFinite s).
