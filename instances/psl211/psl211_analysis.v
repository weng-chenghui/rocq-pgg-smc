(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_analysis: the typed facade of the twelve-card chirality instance    *)
(*                                                                            *)
(* The facade presents the PSL(2,11) all-decks analysis cone through one      *)
(* alias per public value, inside Module PSL211Analysis, in seven fixed       *)
(* source sections:                                                           *)
(*                                                                            *)
(*   1 Program   2 Execution   3 Observers   4 Models                         *)
(*   5 Correctness   6 Security   7 Transfer                                  *)
(*                                                                            *)
(* The facade contract:                                                       *)
(*                                                                            *)
(*   - every declaration is a Definition whose body is the landed constant,   *)
(*     so the alias carries the landed type verbatim;                         *)
(*   - no proof body appears in this file, and no statement, observer         *)
(*     carrier, assumption or numeric constant is restated;                   *)
(*   - the module supplies the namespace, so the aliases drop the psl211_     *)
(*     prefix of their targets;                                               *)
(*   - the type vocabulary the alias types are written in is Require          *)
(*     Export'ed, and the PSL(2,11) instance cone is Require Import'ed only,  *)
(*     so a client reaching this file through the analysis manifest names     *)
(*     the framework records by short name and the instance constants by      *)
(*     qualified name alone.                                                  *)
(*                                                                            *)
(* The dealer this facade is about is the ALL-DECKS one: the run argument is  *)
(* a whole deck description drawn uniformly, not a bare secret. The           *)
(* fixed-dealer colour results of psl211_secrecy.v are about a different      *)
(* dealer and a different observer and are not aliased here.                  *)
(*                                                                            *)
(* Check table against the minimum list of the twelve-card facade:            *)
(*                                                                            *)
(*   probability-independent program profile  -> profile                      *)
(*   execution plug                           -> exec_plug                    *)
(*   ObservedExecution value                  -> observed                     *)
(*   participant endpoint observer            -> seat_endpoint                *)
(*   coalition endpoint observer              -> coalition_endpoints          *)
(*   finite content-trace observer            -> content_trace                *)
(*   deck-level coalition observer            -> static_view                  *)
(*   exact-uniform sample model               -> exact_sample,                *)
(*                                               exact_family                 *)
(*   distribution-to-observer bridges         -> cut_distE,                   *)
(*                                               exact_coalition_distE,       *)
(*                                               content_traceE               *)
(*   execution correctness and recovery       -> observed_recovers,           *)
(*                                               secret_expectedE             *)
(*   exact-security bridges                   -> exact_view_indep,            *)
(*                                               static_indep                 *)
(*   single-card marginal bound               -> marginal_bound,              *)
(*                                               certificate_bundle           *)
(*   transfer status                          -> exact_transfer_status        *)
(******************************************************************************)

From HB Require Import structures.

(* Exported type vocabulary: every constant an alias type is written in. *)
From mathcomp Require Export ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Export div fintype tuple finfun finset fingroup perm.
From mathcomp Require Export morphism action bigop order ssrnum ssralg.
From mathcomp Require Export boolp reals.
From infotheo Require Export realType_ext fdist proba.
From pgg_smc Require Export pgg_interface pgg_monodromy_profile.
From pgg_smc Require Export pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Export pgg_sample_adapter pgg_instance.
From pgg_smc Require Export pgg_analysis_status.
From pgg_reconstruct Require Export algebraic_rigidity.

(* Imported instance cone: loaded, never re-exported. *)
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    input_encoding design_privacy.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_endpoints.
From pgg_smc Require Import psl211_alldecks psl211_models.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Module PSL211Analysis.

(******************************************************************************)
(* ===== 1. Program ===== *)
(******************************************************************************)

(** profile — the probability-independent twelve-card program profile. *)
Definition profile := psl211_profile.

(******************************************************************************)
(* ===== 2. Execution ===== *)
(******************************************************************************)

(** exec_plug — the execution plug of the all-decks parametrization: the run
    whose argument is a whole deck description and whose dealt deck is the
    layout that description names. *)
Definition exec_plug := instance_exec psl211_alldecks_params.

(******************************************************************************)
(* ===== 3. Observers ===== *)
(*                                                                            *)
(* Three carriers, kept distinct: a card of the twelve-card deck for one      *)
(* seat's endpoint, a finfun of cards indexed by seats for a coalition's      *)
(* endpoints, for its reading of the laid deck and for the content reading of *)
(* its executed rows, and bool for the chirality.                             *)
(******************************************************************************)

(** observed — the observed execution of the profile and plug: the run, its
    static observation and the chirality it recovers. *)
Definition observed := psl211_alldecks_observed.

(** prior — the law the sampled observers are random variables on: a deck
    description drawn uniformly over all of them and a cut drawn uniformly
    over the group, the two independent. *)
Definition prior := @psl211_alldecksP.

(** content_trace — the coalition's executed interpreter rows read through the
    instance's row reader, a finfun of cards. *)
Definition content_trace := @psl211_exec_content_trace.

(** static_view — the coalition's reading of the laid deck: a seat of the
    coalition reads the card the layout puts at the cut image of that seat.
    The instance's counting argument is stated about this function, and the
    framework's static_coalition_obs is the same reading in the framework's
    own spelling. *)
Definition static_view := @psl211_alldecks_view.

(** coalition_endpoints — a coalition's executed endpoints, a finfun of cards
    indexed by seats. *)
Definition coalition_endpoints :=
  @exec_coalition_endpoints
    (instance_profile psl211_algebra)
    (instance_exec psl211_alldecks_params).

(** seat_endpoint — one seat's executed endpoint, a dealt card. *)
Definition seat_endpoint :=
  @exec_seat_endpoint
    (instance_profile psl211_algebra)
    (instance_exec psl211_alldecks_params).

(** secret — the chirality of the sampled deck description read as a random
    variable: which of the two Steiner systems S(5,6,12) the dealt heart
    positions form a block of. *)
Definition secret := @psl211_alldecks_secret.

(******************************************************************************)
(* ===== 4. Models ===== *)
(*                                                                            *)
(* The model is followed by the equations that identify its cut and its       *)
(* coalition distributions, so that a security statement about a named        *)
(* distribution can be attached to a named executed observer.                 *)
(******************************************************************************)

(** exact_sample — the all-decks model as a sample adapter: one sample point
    is a deck description together with a cut, the run argument the
    description and the cut the group element the run is dealt at. *)
Definition exact_sample := @psl211_alldecks_sample.

(** exact_family — that model as a unit-indexed typed family, one member at
    every real field, the model having no parameter to range over. *)
Definition exact_family := psl211_exact_family.

(** cut_distE — the model's cut distribution is the uniform law on the
    shuffle group. *)
Definition cut_distE := @psl211_alldecks_cut_distE.

(** exact_coalition_distE — the model's executed coalition distribution is the
    pushforward of its own law along the coalition's reading of the laid
    deck. *)
Definition exact_coalition_distE := @psl211_alldecks_coalition_distE.

(******************************************************************************)
(* ===== 5. Correctness ===== *)
(*                                                                            *)
(* The observed-execution package derives recovery, and the second alias      *)
(* names the secret the exact arm is about as the value that recovery         *)
(* returns.                                                                   *)
(******************************************************************************)

(** observed_recovers — the observed run decodes to the chirality its deck
    description names, at every description and every cut in the group. *)
Definition observed_recovers := @psl211_alldecks_observed_recovers.

(** secret_expectedE — the secret of the model is the value the run is
    expected to recover, read off the same sample point. Without it the
    published independence could be about a bit the protocol never
    reconstructs. *)
Definition secret_expectedE := @psl211_alldecks_secret_expectedE.

(******************************************************************************)
(* ===== 6. Security ===== *)
(******************************************************************************)

(** content_traceE — the executed content reader is the sampled reader of the
    same interpreter rows, the equation that carries a statement about the
    model to what the interpreter's messages contain. *)
Definition content_traceE := @psl211_content_traceE.

(** exact_view_indep — at a coalition of at most five of the twelve seats the
    executed coalition observation and the chirality have a product joint
    distribution. *)
Definition exact_view_indep := @psl211_alldecks_exec_exact_view_indep.

(** static_indep — the same independence at the framework's static reading,
    which is the form the exact arm's witness field takes. *)
Definition static_indep := @psl211_alldecks_static_indep.

(** marginal_bound — the single-card marginal bound of the shuffle, at
    epsilon zero: the one-position pushforward of the uniform cut is exactly
    uniform. *)
Definition marginal_bound := @psl211_marginal_bound.

(** certificate_bundle — that marginal bound with the exact-equality
    certificate attached and no asymptotic certificate. *)
Definition certificate_bundle := @psl211_certificate_bundle.

(******************************************************************************)
(* ===== 7. Transfer ===== *)
(******************************************************************************)

(** exact_transfer_status — the all-decks path's transfer status.
    StaticExecutedOnly, the path carrying its results from the deck-level
    reading to the executed one and comparing no idealized model, the cut it
    draws being the uniform law on the group already. *)
Definition exact_transfer_status : TransferStatus := StaticExecutedOnly.

End PSL211Analysis.

(******************************************************************************)
(*     Retention checks                                                       *)
(*                                                                            *)
(* Value-level identity is checked for the two program-layer aliases, whose   *)
(* bodies do not reach the piSMC interpreter.  On every other alias the       *)
(* value-level form Check (erefl : alias = landed) DIVERGES: the unifier      *)
(* unfolds past the alias into exec_participant_trace and evaluates           *)
(* run_interp.  Those aliases are retained by spelled type ascriptions, one   *)
(* representative per section, so the assumptions, observers and numeric      *)
(* constants are legible in the source and not only up to conversion.  Every  *)
(* line is Timeout-guarded, so a future re-aim of an alias into interpreter   *)
(* territory fails loudly at a named line instead of hanging the build.       *)
(******************************************************************************)

Timeout 60 Check (erefl : PSL211Analysis.profile = psl211_profile).
Timeout 60 Check
  (erefl : PSL211Analysis.exec_plug = instance_exec psl211_alldecks_params).

(* 1 Program *)
Timeout 60 Check (PSL211Analysis.profile : MonodromyProfile).

(* 2 Execution *)
Timeout 60 Check (PSL211Analysis.exec_plug :
  ExecutionPlug PSL211Analysis.profile).

(* 3 Observers: the executed content reader keeps its {ffun 'I_12 -> 'I_12}
   carrier, its coalition index domain and the deck description it runs on. *)
Timeout 60 Check (PSL211Analysis.content_trace :
  {set 'I_12} -> (bool * ('I_132 * {perm 'I_6} * {perm 'I_6}))%type ->
  pgg_gT (mp_M PSL211Analysis.profile) -> {ffun 'I_12 -> 'I_12}).

(* 4 Models: the sample adapter keeps its dependent index on the plug. *)
Timeout 60 Check (PSL211Analysis.exact_sample :
  forall R : realType, SampleAdapter R PSL211Analysis.exec_plug).

(* 5 Correctness: recovery keeps its group-membership hypothesis and returns
   the class bit of the deck description the run was given. *)
Timeout 60 Check (PSL211Analysis.observed_recovers :
  forall (x : (bool * ('I_132 * {perm 'I_6} * {perm 'I_6}))%type)
         (w0 : pgg_gT (mp_M PSL211Analysis.profile)),
    w0 \in pgg_G (mp_M PSL211Analysis.profile) ->
    exec_decode PSL211Analysis.exec_plug
      (OE.oe_endpoints_size PSL211Analysis.observed x w0) = x.1).

(* 6 Security: the exact independence keeps its cardinality hypothesis, its
   two sample-layer distributions and the product shape of its joint law. *)
Timeout 60 Check (PSL211Analysis.exact_view_indep :
  forall (R : realType) (C : {set 'I_12}),
    (#|C| <= 5)%N ->
    fdistmap (fun u => (PSL211Analysis.static_view C u.1 u.2,
                        PSL211Analysis.secret R u)) (PSL211Analysis.prior R)
    = ((sa_coalition_dist (PSL211Analysis.exact_sample R) 0 C)
       `x (fdistmap (PSL211Analysis.secret R) (PSL211Analysis.prior R)))%fdist).

(* 7 Transfer: this section carries no theorem, so its typed status is pinned
   at its constructor. *)
Timeout 60 Check
  (erefl : PSL211Analysis.exact_transfer_status = StaticExecutedOnly).
