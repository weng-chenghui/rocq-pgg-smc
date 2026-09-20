(* PROBE, not production. The landing shape of decisions 1, 2 and 3 of        *)
(* notes/20260920-terminals-below-analysis-bridged-probe-design.md: two       *)
(* records instead of the family t_framework.v compiled, the Sampled payload  *)
(* restricted to the two statuses that name an absent premise, and both       *)
(* terminals in the argument shape publish itself has.                        *)
(*                                                                            *)
(* The text below the Locate block is what manifest/pgg_tableau.v receives,   *)
(* verbatim.                                                                  *)

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
(*     Every name this batch introduces is free under the home's imports      *)
(******************************************************************************)

Locate PublishedObserved.
Locate PublishedSampled.
Locate MkPublishedObserved.
Locate MkPublishedSampled.
Locate published_observed_at.
Locate published_observed_path.
Locate published_observed_thm.
Locate published_sampled_at.
Locate published_sampled_path.
Locate published_sampled_thm.
Locate TransferStatusWithoutTheorem.
Locate SampledNoModelComparison.
Locate SampledStaticExecutedOnly.
Locate transfer_of_sampled.
Locate publish_observed.
Locate publish_sampled.
Locate publish_observed_completionE.
Locate publish_observed_transferE.
Locate publish_observed_modelE.
Locate publish_sampled_completionE.
Locate publish_sampled_transferE.
Locate publish_sampled_modelE.
Locate run_correct_of_observed.
Locate run_correct_of_sampled.
Locate view_identification_of_sampled.

(******************************************************************************)
(*     Handing a program over below AnalysisBridged                           *)
(******************************************************************************)

(* A program that stopped at Observed, handed over: its data, a manifest path,
   and run correctness of the observed execution that data reached. The three
   fields are independent, as the three of PublishedAt are: the terminal below
   builds the path from the program's own data, and the record does not force
   a path written by hand to describe the data beside it. A value carries
   StackProp Observed and nothing above it, so no coalition, privacy or
   security statement follows from one. *)
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
   family the program named. The three fields are independent in the same
   sense. The program has proved no statement in which an idealized model
   occurs, so no security property is certified by such a value. *)
Record PublishedSampled := MkPublishedSampled {
  published_sampled_at   : StackAt Sampled ;
  published_sampled_path : AnalysisPath ;
  published_sampled_thm  : StackProp Sampled published_sampled_at }.

(* The two transfer statuses that assert no theorem about an idealized model.
   A program at Sampled has proved run correctness and the link lemma and
   nothing about an ideal, so these are the two its own proposition supports,
   and a path carrying either of them owes the manifest the premise it lacks
   rather than a theorem. The restriction is on the terminal below and not on
   the record: a value written by hand still carries any path. *)
Variant TransferStatusWithoutTheorem :=
  SampledNoModelComparison | SampledStaticExecutedOnly.

(* The manifest's own status such a payload stands for. *)
Definition transfer_of_sampled (t : TransferStatusWithoutTheorem)
    : TransferStatus :=
  match t with
  | SampledNoModelComparison => NoModelComparison
  | SampledStaticExecutedOnly => StaticExecutedOnly
  end.

(* The terminal of a program that stops at run correctness. The path is built
   from the program's own data: the observed execution the program reached,
   the level Observed, the empty model slot, and NoModelComparison, which is
   not a payload because a program naming no model compares its execution
   with nothing. The assumption status is the line's payload. No level's
   proposition determines it and nothing ties it to Print Assumptions: it is
   the author's statement, and the manifest's prose defines when it is
   true. *)
Definition publish_observed (q : StackAt Observed) (pf : StackProp Observed q)
    (a : AssumptionStatus) : PublishedObserved :=
  @MkPublishedObserved q
    (@MkAnalysisPath (ob_obs q) Observed None NoModelComparison a) pf.

(* The data occurs in the type of the proof, so Set Implicit Arguments would
   infer it and the bind of pgg_tableau.v, which passes the terminal
   unapplied, would have no slot to write it in. *)
Arguments publish_observed : clear implicits.

(* The terminal of a program that stops at a named analysis model family. The
   path takes the family the program's own data carries, and the transfer
   status is the line's payload at the restricted type, so the two statuses
   naming a transfer theorem are unreachable through this terminal. The
   assumption status stands on the same footing as at Observed. *)
Definition publish_sampled (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (t : TransferStatusWithoutTheorem)
    : PublishedSampled :=
  @MkPublishedSampled q
    (@MkAnalysisPath (sp_obs q) Sampled (sp_f q) (transfer_of_sampled t) a) pf.

(* Explicit for the reason publish_observed's directive gives. *)
Arguments publish_sampled : clear implicits.

(* The path of a program published at Observed records Observed. Conversion
   decides it, so the manifest's sentence about how far a path's theorems
   reach is a term at this level and not prose. *)
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
  = transfer_of_sampled t.
Proof. exact: erefl. Qed.

(* The model slot of such a path is the family the program's data carries, so
   the path names the model the link lemma was proved at and not a second
   family that resembles it. *)
Lemma publish_sampled_modelE (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (t : TransferStatusWithoutTheorem) :
  ap_model (published_sampled_path (publish_sampled a q pf t)) = sp_f q.
Proof. exact: erefl. Qed.

(* Run correctness of a program published at Observed: every process finishes,
   the endpoints number one per seat, and decoding them returns the value the
   run recovers. It is the whole content of such a value, and the proof is the
   observed execution's own field, so the terminal hands back what the
   instance discharged and the reader adds nothing to it. *)
Definition run_correct_of_observed (r : PublishedObserved)
  : oe_correct_prop (ob_obs (published_observed_at r)) :=
  published_observed_thm r.
Arguments run_correct_of_observed : clear implicits.

(* Run correctness of a program published at Sampled, the first of the two
   conjuncts that level carries. *)
Definition run_correct_of_sampled (r : PublishedSampled)
  : oe_correct_prop (sp_obs (published_sampled_at r)) :=
  proj1 (published_sampled_thm r).
Arguments run_correct_of_sampled : clear implicits.

(* The link lemma of a program published at Sampled, identifying its executed
   coalition reader with the direct computation at every real field and index.
   It is the second and last conjunct of that level, and the fact a security
   statement about this model would be made along were one proved. *)
Definition view_identification_of_sampled (r : PublishedSampled)
  : sampled_viewE_prop (sp_f (published_sampled_at r)) :=
  proj2 (published_sampled_thm r).
Arguments view_identification_of_sampled : clear implicits.

(******************************************************************************)
(*     The rejections the two records rest on                                 *)
(******************************************************************************)

Section NoSecurityReaderBelowBridged.
Variable r : PublishedObserved.

Fail Check (view_secrecy_of r).
Fail Check (security_property_of r).
Fail Check (r : Published).

End NoSecurityReaderBelowBridged.

Fail Check (fun (q : StackAt Executable) (pf : StackProp Executable q)
                (a : AssumptionStatus) => publish_observed q pf a).

Fail Check (fun (a : AssumptionStatus) (q : StackAt Sampled)
                (pf : StackProp Sampled q) =>
              publish_sampled a q pf IdealFinite).

Fail Check (fun (a : AssumptionStatus) (q : StackAt Sampled)
                (pf : StackProp Sampled q) =>
              publish_sampled a q pf NegativeTransfer).

(* The two admitted statuses do build a value. *)
Check (fun (a : AssumptionStatus) (q : StackAt Sampled)
           (pf : StackProp Sampled q) =>
         publish_sampled a q pf SampledNoModelComparison).
Check (fun (a : AssumptionStatus) (q : StackAt Sampled)
           (pf : StackProp Sampled q) =>
         publish_sampled a q pf SampledStaticExecutedOnly).
