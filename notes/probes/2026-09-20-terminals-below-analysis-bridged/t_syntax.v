(* PROBE, not production. Row T8 of                                           *)
(* notes/20260920-terminals-below-analysis-bridged-probe-design.md.           *)
(*                                                                            *)
(* The statement surface of manifest/pgg_tableau_syntax.v ends a program at   *)
(* one terminal, |> publish t a, which takes a program at AnalysisBridged.    *)
(* Two rules are added for the two terminals below it. Both spell the level   *)
(* as a token following the literal publish, which by the measured rule of    *)
(* that file's header reserves no global keyword; the measurement is in       *)
(* t_keyword_check.v and in the two identifier checks at the end of this      *)
(* file.                                                                      *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset.
From mathcomp Require Import matrix zmodp ssralg ssrnum reals.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_smc Require Import pgg_observed_execution.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import s5_exec.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import s5_tableau_executable.
From pgg_smc Require Import s5_tableau_observed.
From belowprobe Require Import t_framework.
From belowprobe Require Import t_s5.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     The two terminal rules                                                 *)
(******************************************************************************)

(* The terminal of a program that stops at the three run facts. One payload,
   the assumption status: the level, the model slot and the transfer status
   are all read off the program's own data. *)
Notation "s |> 'publish' 'observed' a" := (publish_observed a s)
  (at level 90, left associativity, a at level 0).

(* The terminal of a program that stops at a named model. Two payloads,
   written transfer first, in the order the manifest column headings run and
   against the argument order of the terminal itself, as the existing
   publish rule is. *)
Notation "s |> 'publish' 'sampled' a t" := (publish_sampled a t s)
  (at level 90, left associativity, a at level 0, t at level 0).

(******************************************************************************)
(*     The three terminals parse side by side                                 *)
(******************************************************************************)

Section TerminalsParse.

(* A program at Observed, written as the record its statements build. *)
Variable qo : StackAt Observed.
Variable pfo : StackProp Observed qo.

Definition probe_observed_terminal : PublishedObserved :=
  @MkTableau Observed (StackProp Observed) qo pfo
  |> publish observed BaselineClassicalOnly.

(* A program at Sampled. *)
Variable qs : StackAt Sampled.
Variable pfs : StackProp Sampled qs.

Definition probe_sampled_terminal : PublishedSampled :=
  @MkTableau Sampled (StackProp Sampled) qs pfs
  |> publish sampled BaselineClassicalOnly NoModelComparison.

(* The existing terminal still parses beside the two new rules, at a
   transfer status that is a bare identifier in the slot the two new rules
   put a literal in. *)
Variable qb : StackAt AnalysisBridged.
Variable pfb : BridgedProp no_concluded_bound qb.

Definition probe_bridged_terminal : Published :=
  @MkTableau AnalysisBridged (StackProp AnalysisBridged) qb pfb
  |> publish IdealFinite BaselineClassicalOnly.

End TerminalsParse.

(******************************************************************************)
(*     A program of the five-seat instance written in the surface             *)
(******************************************************************************)

(* The dealer-dealt run of the five-seat instance, from the algebra to the
   published value, in one program. The last line is the new terminal, and
   the four above it are the surface as it stands. *)
Definition s5_det_published_program : PublishedObserved :=
  s5_algebra
    dealt   fuel 150
    execute terminates by s5_dealt_terminates
            endpoints by s5_dealt_endpoints
            recon by s5_dealt_recon
  |> publish observed (AcceptsAxioms [:: AxS5GroupOrder]).

(* The program written in the surface is the value t_s5.v builds by applying
   the terminal, so the surface adds no term of its own. *)
Lemma s5_det_published_programE :
  s5_det_published_program = s5_det_published.
Proof. exact: erefl. Qed.

(* The path of the program written in the surface is the manifest's own
   deterministic path. *)
Lemma s5_det_published_program_pathE :
  published_level_path s5_det_published_program = s5_det_path.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The two level tokens after the literal publish                         *)
(******************************************************************************)

(* Neither token is reserved: both are still binder names in this very file,
   after both rules are declared. The same two checks are made in
   t_keyword_check.v, in a file whose only other import is ssreflect. *)
Definition probe_observed_identifier (observed : nat) : nat := observed.
Definition probe_sampled_identifier (sampled : nat) : nat := sampled.

(* And still usable at the type the framework binds them at, which is where
   pgg_analysis_status.v writes observed today. *)
Definition probe_observed_binder (observed : OE.ObservedExecution)
  : OE.ObservedExecution := observed.
