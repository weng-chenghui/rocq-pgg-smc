(* PROBE, not production. The third variant of row T6: the restriction the    *)
(* docstring of TransferStatus itself draws, as against the pair the spec     *)
(* proposes.                                                                  *)
(*                                                                            *)
(* The docstring separates the two statuses that name a theorem, IdealFinite  *)
(* and NegativeTransfer, from the two that name an absent premise,            *)
(* StaticExecutedOnly and NoModelComparison. A program published at Sampled   *)
(* carries run correctness and the static-to-executed bridge and no theorem   *)
(* about an idealized model, so this is the pair its own proposition          *)
(* supports.                                                                  *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From belowprobe Require Import t_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* The two statuses that name no theorem about an idealized model: the
   program named no model layer at all, or it named one and proved the
   static-to-executed bridge over it and nothing further. *)
Variant SampledNoTransferTheorem :=
  NoTheoremNoModelComparison | NoTheoremStaticExecutedOnly.

(* The manifest's own status such a value stands for. *)
Definition transfer_of_no_theorem (t : SampledNoTransferTheorem)
    : TransferStatus :=
  match t with
  | NoTheoremNoModelComparison => NoModelComparison
  | NoTheoremStaticExecutedOnly => StaticExecutedOnly
  end.

(* The Sampled terminal restricted to those two. *)
Definition publish_sampled_no_theorem (a : AssumptionStatus)
    (t : SampledNoTransferTheorem) (s : Tableau Sampled) : PublishedSampled :=
  publish_sampled a (transfer_of_no_theorem t) s.

Lemma publish_sampled_no_theorem_transferE (a : AssumptionStatus)
    (t : SampledNoTransferTheorem) (s : Tableau Sampled) :
  ap_transfer (published_level_path (publish_sampled_no_theorem a t s))
  = transfer_of_no_theorem t.
Proof. exact: erefl. Qed.

(* This restriction refuses both statuses that name a theorem. *)
Fail Check (fun (a : AssumptionStatus) (s : Tableau Sampled) =>
              publish_sampled_no_theorem a IdealFinite s).
Fail Check (fun (a : AssumptionStatus) (s : Tableau Sampled) =>
              publish_sampled_no_theorem a NegativeTransfer s).

(* The pair the spec proposes admits NegativeTransfer and refuses
   StaticExecutedOnly, which is the status a program at Sampled has in fact
   proved the premise of. *)
Fail Check (fun (a : AssumptionStatus) (s : Tableau Sampled) =>
              publish_sampled_restricted a StaticExecutedOnly s).
