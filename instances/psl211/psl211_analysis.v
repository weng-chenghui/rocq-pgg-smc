(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_analysis: the typed facade of the twelve-card chirality instance    *)
(*                                                                            *)
(* The facade presents the PSL(2,11) analysis cone through one alias per      *)
(* public value, inside Module PSL211Analysis, in seven fixed source          *)
(* sections:                                                                  *)
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
(* Two dealers are aliased here and their aliases are kept apart by name.     *)
(* An unprefixed alias is about the ALL-DECKS dealer, whose run argument is   *)
(* a whole deck description drawn uniformly. An alias whose name begins       *)
(* dealt_ is about the DEALER-DEALT one, whose run argument is the bare       *)
(* chirality, so that at that dealer the two run arguments a limitation       *)
(* theorem compares are the two values of the secret. The two dealers are     *)
(* different executions over one profile and no alias of one is an alias of   *)
(* the other. The alias dealt_secret is the framework's constant of that name *)
(* at this instance's arguments.                                              *)
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
(*   584-letter word sample model             -> word_sample, word_family     *)
(*   distribution-to-observer bridges         -> cut_distE,                   *)
(*                                               exact_coalition_distE,       *)
(*                                               content_traceE               *)
(*   dealer-dealt execution                   -> dealt_exec_plug,             *)
(*                                               dealt_observed               *)
(*   dealer-dealt observers                   -> dealt_static_view,           *)
(*                                               dealt_colour_of_reading,     *)
(*                                               dealt_secret, dealt_prior    *)
(*   dealer-dealt model                       -> dealt_sample, dealt_family,  *)
(*                                               dealt_cut_distE              *)
(*   dealer-dealt correctness                 -> dealt_observed_recovers      *)
(*   dealer-dealt security                    -> dealt_colour_indep           *)
(*   dealer-dealt limitation                  -> dealt_perdeck_reading_ge     *)
(*   execution correctness and recovery       -> observed_recovers,           *)
(*                                               secret_expectedE             *)
(*   exact-security bridges                   -> exact_view_indep,            *)
(*                                               static_indep                 *)
(*   input-distinguishability limitation      -> perdeck_reading_ge           *)
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
From infotheo Require Export realType_ext fdist proba variation_dist.
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
From pgg_smc Require Import psl211_alldecks psl211_models psl211_word_model.
From pgg_smc Require Import psl211_alldecks_input_distinguishability.
From pgg_smc Require Import psl211_secrecy psl211_dealt_model.

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

(** dealt_exec_plug — the execution plug of the dealer-dealt parametrization:
    the run whose argument is the chirality alone and whose dealt deck the
    dealer lays from it. *)
Definition dealt_exec_plug := instance_exec psl211_dealt_params.

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

(** dealt_observed — the observed execution of the dealer-dealt run: the run,
    its static observation and the chirality it recovers. *)
Definition dealt_observed := psl211_dealt_observed.

(** dealt_prior — the law the dealer-dealt observers are random variables on:
    a chirality bit from a prior on it and a cut drawn uniformly over the
    group, the two independent. Its index is the prior, where the all-decks
    prior has none, because the dealer-dealt results hold at every prior. *)
Definition dealt_prior := @psl211P.

(** dealt_static_view — a coalition's reading of the deck the dealer laid: a
    seat of the coalition reads the card the encoder deck of the chirality
    puts at the cut image of that seat, and card zero outside the coalition.
    It is the framework's static_coalition_obs at the dealer-dealt plug. *)
Definition dealt_static_view :=
  @static_coalition_obs psl211_algebra psl211_dealt_params.

(** dealt_colour_of_reading — the colour map on a coalition's endpoints: the
    colour, heart or club, of the card each seat of the coalition holds, and
    false outside it. It is a strictly coarser observer than
    dealt_static_view, which keeps the card identity. *)
Definition dealt_colour_of_reading := @psl211_colour_of_reading.

(** dealt_secret — the chirality the dealer was given, read as a random
    variable of the dealer-dealt law: the run argument itself. *)
Definition dealt_secret := @psl211_secret.

(******************************************************************************)
(* ===== 4. Models ===== *)
(*                                                                            *)
(* The all-decks model is followed by the equations that identify its cut and *)
(* its coalition distributions, so that a security statement about a named    *)
(* distribution can be attached to a named executed observer. The word model  *)
(* carries its own cut equation psl211_word_cut_distE at                      *)
(* instances/psl211/psl211_word_model.v, and is aliased here for the sample   *)
(* and model slots of its own manifest path.                                  *)
(******************************************************************************)

(** exact_sample — the all-decks model as a sample adapter: one sample point
    is a deck description together with a cut, the run argument the
    description and the cut the group element the run is dealt at. *)
Definition exact_sample := @psl211_alldecks_sample.

(** word_sample — the 584-letter word model as a sample adapter: the sample
    space and the law of the deck description of exact_sample, with the cut
    drawn by evaluating a word in the three generators. *)
Definition word_sample := @psl211_word_sample.

(** exact_family — that model as a unit-indexed typed family, one member at
    every real field, the model having no parameter to range over. *)
Definition exact_family := psl211_exact_family.

(** word_family — the word model as a unit-indexed typed family, carrying the
    index type exact_family carries, so a program over each of the two models is
    read at one index. *)
Definition word_family := psl211_word_family.

(** cut_distE — the model's cut distribution is the uniform law on the
    shuffle group. *)
Definition cut_distE := @psl211_alldecks_cut_distE.

(** dealt_sample — the fixed-dealer colour model as a sample adapter: one
    sample point is a chirality bit and a cut, the run argument the bit and
    the cut the group element the run is dealt at. *)
Definition dealt_sample := @psl211_dealt_sample.

(** dealt_family — that model as a typed family indexed by the prior on the
    chirality, one member at every real field and every prior. The index is
    the prior where exact_family's is the unit type. *)
Definition dealt_family := psl211_dealt_family.

(** dealt_cut_distE — the dealer-dealt model's cut distribution is the uniform
    law on the shuffle group, at every prior on the chirality. *)
Definition dealt_cut_distE := @psl211_dealt_sample_cut_distE.

(** exact_coalition_distE — the model's executed coalition distribution is the
    pushforward of its own law along the coalition's reading of the laid
    deck. *)
Definition exact_coalition_distE := @psl211_alldecks_coalition_distE.

(******************************************************************************)
(* ===== 5. Correctness ===== *)
(*                                                                            *)
(* The observed-execution package derives recovery, and the second alias      *)
(* names the secret the exact-independence witness carries as the value that  *)
(* recovery returns.                                                          *)
(******************************************************************************)

(** observed_recovers — the observed run decodes to the chirality its deck
    description names, at every description and every cut in the group. *)
Definition observed_recovers := @psl211_alldecks_observed_recovers.

(** secret_expectedE — the secret of the model is the value the run is
    expected to recover, read off the same sample point. Without it the
    published independence could be about a bit the protocol never
    reconstructs. *)
Definition secret_expectedE := @psl211_alldecks_secret_expectedE.

(** dealt_observed_recovers — the packaged dealer-dealt run decodes to the
    chirality the dealer was given, at every chirality and every cut in the
    group. The value the dealer-dealt security lines are about is the value
    that run reconstructs. *)
Definition dealt_observed_recovers := @psl211_dealt_observed_recovers.

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
    which is the form the exact-independence witness's field takes. *)
Definition static_indep := @psl211_alldecks_static_indep.

(** perdeck_reading_ge — the limitation this model carries: under its own cut
    law a coalition of three of the twelve seats reads two named deck
    descriptions of one deal at least 1/660 apart, in the sum of absolute
    differences, so a distinguisher told to compare those two run arguments
    has advantage at least 1/1320. It fixes two run arguments where
    static_indep draws the deck description, so the two stand under different
    quantifiers over the run argument and both hold at this model. *)
Definition perdeck_reading_ge := @psl211_alldecks_perdeck_reading_ge.

(** dealt_colour_indep — at a coalition below the threshold of six of the
    twelve seats, the colour map of that coalition's endpoints is independent
    of the chirality the dealer was given, at every prior on it. It is the
    dealer-dealt counterpart of static_indep, and it is stated at the colour
    observer and not at the card-identity one, where over this model it is
    false. *)
Definition dealt_colour_indep := @psl211_dealt_colour_indep.

(** dealt_perdeck_reading_ge — the limitation the dealer-dealt model carries:
    under its own cut law a coalition of three of the twelve seats reads the
    two chiralities of one deal at least 1/660 apart, in the sum of absolute
    differences, so a distinguisher told to compare those two run arguments
    has advantage at least 1/1320. The run argument is the chirality here, so
    the two run arguments it compares are the two values of the secret, which
    is what perdeck_reading_ge over the all-decks dealer does not say. *)
Definition dealt_perdeck_reading_ge := @psl211_dealt_perdeck_reading_ge.

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

(** dealt_colour_transfer_status — the transfer status of the dealer-dealt
    colour path. StaticExecutedOnly, the path carrying its result from the
    deck-level colour observer to the executed one and comparing no idealized
    model, the cut it draws being the uniform law on the group already. *)
Definition dealt_colour_transfer_status : TransferStatus := StaticExecutedOnly.

(** dealt_obstruction_transfer_status — the transfer status of the
    dealer-dealt limitation path. NegativeTransfer, that path's theorem
    transporting an obstruction to its observer. *)
Definition dealt_obstruction_transfer_status : TransferStatus :=
  NegativeTransfer.

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
Timeout 60 Check
  (erefl : PSL211Analysis.dealt_colour_transfer_status = StaticExecutedOnly).
Timeout 60 Check
  (erefl : PSL211Analysis.dealt_obstruction_transfer_status = NegativeTransfer).

(* The dealer-dealt aliases at their spelled types. The execution and the
   model keep their dependent indices, recovery keeps its group-membership
   hypothesis, and the two security aliases are pinned at the observers they
   are stated at, the colour map for the first and the framework's static
   reader for the second. *)
Timeout 60 Check (PSL211Analysis.dealt_exec_plug :
  ExecutionPlug PSL211Analysis.profile).

Timeout 60 Check (PSL211Analysis.dealt_observed : OE.ObservedExecution).

Timeout 60 Check (PSL211Analysis.dealt_colour_of_reading :
  {set 'I_12} -> {ffun 'I_12 -> 'I_12} -> {ffun 'I_12 -> bool}).

Timeout 60 Check (PSL211Analysis.dealt_sample :
  forall (R : realType) (secretP : R.-fdist bool),
    SampleAdapter R PSL211Analysis.dealt_exec_plug).

Timeout 60 Check (PSL211Analysis.dealt_family :
  AnalysisModelFamily PSL211Analysis.dealt_observed).

(* 5 Correctness: recovery keeps its group-membership hypothesis and returns
   the chirality the dealer was given. *)
Timeout 60 Check (PSL211Analysis.dealt_observed_recovers :
  forall (x : bool) (w0 : pgg_gT (mp_M PSL211Analysis.profile)),
    w0 \in pgg_G (mp_M PSL211Analysis.profile) ->
    exec_decode PSL211Analysis.dealt_exec_plug
      (OE.oe_endpoints_size PSL211Analysis.dealt_observed x w0) = x).

Timeout 60 Check (PSL211Analysis.dealt_colour_indep :
  forall (R : realType) (secretP : R.-fdist bool) (C : {set 'I_12}),
    (#|C| < profile_k PSL211Analysis.profile)%N ->
    sa_sampleP (PSL211Analysis.dealt_sample secretP)
    |= (fun u => PSL211Analysis.dealt_colour_of_reading C
                   (PSL211Analysis.dealt_static_view C
                      ((PSL211Analysis.dealt_sample secretP).(sa_arg) u)
                      ((PSL211Analysis.dealt_sample secretP).(sa_cut) u)))
       _|_ PSL211Analysis.dealt_secret secretP).

Timeout 60 Check (PSL211Analysis.dealt_perdeck_reading_ge :
  forall (R : realType) (secretP : R.-fdist bool),
    (#|pgg_G psl211_M|%:R)^-1 <=
    var_dist
      (fdistmap (PSL211Analysis.dealt_static_view psl211_perdeck_coalition true)
         (sa_cut_dist (PSL211Analysis.dealt_sample secretP)))
      (fdistmap (PSL211Analysis.dealt_static_view psl211_perdeck_coalition
           false)
         (sa_cut_dist (PSL211Analysis.dealt_sample secretP)))).
