(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_models: the all-decks probability model of the twelve-card          *)
(*                chirality instance, its executed readers, and independence  *)
(*                of the chirality at five seats                              *)
(*                                                                            *)
(* The all-decks run of psl211_alldecks.v carries no probability model. This  *)
(* file supplies one: a deck description drawn uniformly from the 136857600   *)
(* of them and a cut drawn uniformly from the 660 elements of the group, the  *)
(* two independent. Under that law the run is packaged as an observed         *)
(* execution, its three run facts collected, and the reading of a coalition   *)
(* of at most five of the twelve seats is proved independent of the           *)
(* chirality. The independence is exact and is an average over decks and      *)
(* cuts; it neither implies nor is implied by the fixed-dealer colour result  *)
(* of psl211_secrecy.v, which is about a different dealer and a different     *)
(* observer.                                                                  *)
(*                                                                            *)
(* Two readings of a coalition are identified here. The framework's           *)
(* static_coalition_obs reads seat i at tnth (pi_starts _) i through the      *)
(* layout's share cast; the instance's psl211_alldecks_view reads it at i.    *)
(* The share cast disappears by conversion, the scheme's share count and the  *)
(* algebra's card count both being twelve, and the starting tuple is          *)
(* ord_tuple 12, so the two readings agree. The executed reading of the       *)
(* interpreter's messages is carried to the static one by the endpoint        *)
(* equation of psl211_endpoints.v, which enters here only through             *)
(* supplied_endpointsE and is never unfolded.                                 *)
(*                                                                            *)
(* Naming: the law of the model is psl211_alldecksP, where the repository's   *)
(* other two-mode instance writes the mode prefix with a _sampleP suffix      *)
(* (s5_models.v:105 s5_rand_sampleP).                                         *)
(*                                                                            *)
(* content_of lives in instances/pgl27/pgl27_trace.v and nothing shared       *)
(* exports it, so the row reader is restated here as psl211_content_of and    *)
(* pinned in both directions by psl211_content_ofE.                           *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_alldecksP        == the law of the model, decks times cuts        *)
(*   psl211_alldecks_secret  == the chirality of the sampled description      *)
(*   psl211_alldecks_sample  == the sample adapter over the all-decks plug    *)
(*   psl211_alldecks_endpoints == the endpoint obligation of the run          *)
(*   psl211_alldecks_observed  == the run packaged with its three run facts   *)
(*   psl211_content_of       == the card an executed interpreter row reports  *)
(*   psl211_exec_content_trace == the coalition's rows read through it        *)
(*   psl211_content_trace    == the same reader as a random variable          *)
(*   psl211_exact_family     == the model as a unit-indexed family            *)
(*   psl211_exact_witness    == the exact arm's witness over that family      *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_alldecks_inputTE == the plug's run argument carrier is the        *)
(*                              description carrier                           *)
(*   psl211_alldecks_cut_distE == the model's cut is the uniform shuffle      *)
(*   psl211_alldecks_static_obsE == the framework's reading at a seat is the  *)
(*                              card the laid deck puts at its cut image      *)
(*   psl211_alldecks_exact_viewE == the same with the description inside the  *)
(*                              sample point                                  *)
(*   psl211_alldecks_observed_recovers == the packaged run decodes to the     *)
(*                              chirality its input names                     *)
(*   psl211_exec_rowE        == a seat's executed trace is row 2 + i          *)
(*   psl211_content_traceE   == the executed content reader is that random    *)
(*                              variable                                      *)
(*   psl211_alldecks_exec_viewE == the executed coalition reader is the       *)
(*                              static one                                    *)
(*   psl211_alldecks_secret_expectedE == the secret is the value the run      *)
(*                              recovers                                      *)
(*   psl211_alldecks_view_indep == a coalition of at most five seats reads a  *)
(*                              view independent of the chirality             *)
(*   psl211_alldecks_static_indep == the same on the framework's side         *)
(*   psl211_alldecks_coalition_distE == the executed coalition distribution   *)
(*                              is the pushforward of the law along the view  *)
(*   psl211_alldecks_exec_exact_view_indep == the product joint law at the    *)
(*                              executed sample layer                         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import design_privacy.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_tableau.
From pgg_smc Require Import psl211_group psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_exec.
From pgg_smc Require Import psl211_endpoints psl211_alldecks.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(** mpP — the monodromy profile the twelve-card algebra derives. *)
Local Notation mpP := (instance_profile psl211_algebra).

(** eP — the execution plug the all-decks parametrization derives. *)
Local Notation eP := (instance_exec psl211_alldecks_params).

(** seatT — a seat of the instance's starting interface, the index a coalition
    is a set of. *)
Local Notation seatT := ('I_(pi_T' (mp_PI mpP)).+1).

(** cardT — a card of the twelve-card deck, the value a seat reads. *)
Local Notation cardT := ('I_(pgg_N' (mp_M mpP)).+1).

(******************************************************************************)
(*     The law, the secret and the sample adapter                             *)
(******************************************************************************)

(** psl211_alldecksP — the law of the all-decks model: the deck description
    uniform over all of them, which is one of the two chiralities, one of the
    132 block lines of that chirality's Steiner system for the six heart
    positions, one of the 720 labellings of the heart codes and one of the 720
    labellings of the club codes; the cut uniform over the 660 elements of the
    group; the two independent. Every statement this instance publishes about
    a coalition is an average over decks and cuts under this law, per
    coalition and at a single observation. *)
Definition psl211_alldecksP (R : realType)
  : R.-fdist (psl211_inputT * pgg_gT psl211_M)%type :=
  (`U psl211_alldecks_gt0) `x (`U psl211_G_pos).

(** psl211_alldecks_secret — the secret of the all-decks model is the class
    bit of the sampled deck description, which is the value the run
    reconstructs and the value a coalition must not learn. *)
Definition psl211_alldecks_secret (R : realType)
  : {RV (psl211_alldecksP R) -> bool} := fun u => u.1.1.

(** psl211_alldecks_inputTE — the run argument carrier of the all-decks plug
    is the description carrier the parametrization names. The two coordinates
    of a sample point are therefore the plug's own input carrier and the
    group, with no coercion standing between the probability layer and the
    execution layer. *)
Lemma psl211_alldecks_inputTE : ep_inputT eP = psl211_inputT.
Proof. by []. Qed.

(** psl211_alldecks_sample — the all-decks probability model as a sample
    adapter: one sample point is a deck description together with a cut, the
    two drawn independently and each uniformly, the run argument the deck
    description and the cut the group element the run is dealt at. *)
Definition psl211_alldecks_sample (R : realType)
  : SampleAdapter R (instance_exec psl211_alldecks_params) :=
  @MkSampleAdapter R (instance_profile psl211_algebra)
    (instance_exec psl211_alldecks_params)
    ((psl211_inputT * pgg_gT psl211_M)%type : finType)
    (psl211_alldecksP R) fst snd.

(** psl211_alldecks_sampleP_E — the adapter's law is the model's law. *)
Lemma psl211_alldecks_sampleP_E (R : realType) :
  sa_sampleP (psl211_alldecks_sample R) = psl211_alldecksP R.
Proof. by []. Qed.

(** psl211_alldecks_sample_argE — the run argument of a sample point is its
    deck description. *)
Lemma psl211_alldecks_sample_argE (R : realType)
    (u : psl211_inputT * pgg_gT psl211_M) :
  (psl211_alldecks_sample R).(sa_arg) u = u.1.
Proof. by []. Qed.

(** psl211_alldecks_sample_cutE — the cut of a sample point is its group
    element. *)
Lemma psl211_alldecks_sample_cutE (R : realType)
    (u : psl211_inputT * pgg_gT psl211_M) :
  (psl211_alldecks_sample R).(sa_cut) u = u.2.
Proof. by []. Qed.

(** psl211_alldecks_cut_distE — the cut this model draws is the uniform law on
    the shuffle group. This is the cut the exact arm needs, and it is the law
    a spectral arm would compare a generator walk against. *)
Lemma psl211_alldecks_cut_distE (R : realType) :
  @sa_cut_dist R (instance_profile psl211_algebra)
    (instance_exec psl211_alldecks_params) (psl211_alldecks_sample R)
  = (`U psl211_G_pos : R.-fdist (pgg_gT psl211_M)).
Proof.
have -> : @sa_cut_dist R (instance_profile psl211_algebra)
            (instance_exec psl211_alldecks_params) (psl211_alldecks_sample R)
        = fdist_snd (psl211_alldecksP R) by [].
apply/fdist_ext => g; rewrite fdist_sndE.
under eq_bigr do rewrite fdist_prodE /=.
by rewrite -big_distrl /= FDist.f1 mul1r.
Qed.

(******************************************************************************)
(*     The identification of the coalition's reading                          *)
(******************************************************************************)

(** psl211_alldecks_static_obsE — seat i's entry of the framework's static
    coalition reading is the card the laid deck puts at the shuffle image of
    seat i. Every security statement of this instance is made about the
    left-hand side and every counting argument about the right, so this
    equation is the whole of what carries one to the other. *)
Lemma psl211_alldecks_static_obsE (C : {set seatT}) (x : psl211_inputT)
    (g : pgg_gT psl211_M) (i : seatT) :
  @static_coalition_obs psl211_algebra psl211_alldecks_params C x g i
  = if i \in C
    then tnth (psl211_alldecks_layout x) (@pgg_rho psl211_M g i)
    else ord0.
Proof.
rewrite static_coalition_obsE.
(* The share cast of the framework's right-hand side disappears by conversion,
   the scheme's share count and the algebra's card count both being twelve;
   the /= before tnth_ord_tuple is what exposes tnth (pi_starts _) i. *)
by case: ifP => // _; rewrite /= tnth_ord_tuple.
Qed.

(** psl211_alldecks_static_obs_viewE — the whole reading, as one finite
    function: the framework's static coalition observation at a description
    and a cut is the instance's view of the laid deck. *)
Lemma psl211_alldecks_static_obs_viewE (C : {set seatT}) (x : psl211_inputT)
    (g : pgg_gT psl211_M) :
  @static_coalition_obs psl211_algebra psl211_alldecks_params C x g
  = psl211_alldecks_view C x g.
Proof.
apply/ffunP => i; rewrite psl211_alldecks_static_obsE /psl211_alldecks_view.
by rewrite [RHS]ffunE.
Qed.

(** psl211_alldecks_static_obs_funE — the same identification with the cut
    left free, as an equality of functions of the cut. A law obtained by
    pushing a reader forward along a distribution on cuts needs the reader as
    one function and not as its values. *)
Lemma psl211_alldecks_static_obs_funE (C : {set seatT}) (x : psl211_inputT) :
  @static_coalition_obs psl211_algebra psl211_alldecks_params C x
  = psl211_alldecks_view C x.
Proof.
by apply: boolp.funext => g; exact: psl211_alldecks_static_obs_viewE.
Qed.

(** psl211_alldecks_exact_viewE — the same identification once more, with the
    deck description inside the sample point. The exact arm compares a
    coalition's reading with the secret on one probability space, so the run
    argument cannot be fixed first. *)
Lemma psl211_alldecks_exact_viewE (C : {set seatT}) :
  (fun u : psl211_inputT * pgg_gT psl211_M =>
     @static_coalition_obs psl211_algebra psl211_alldecks_params C u.1 u.2)
  = (fun u : psl211_inputT * pgg_gT psl211_M => psl211_alldecks_view C u.1 u.2).
Proof.
by apply: boolp.funext; case=> x g; exact: psl211_alldecks_static_obs_viewE.
Qed.

(** psl211_alldecks_read_position — seat i of the coalition reads the card the
    laid deck puts at position pgg_rho g i. The position is the image of the
    seat under the cut and not its preimage, which is what fixes the set the
    block census of the counting argument is taken over. *)
Lemma psl211_alldecks_read_position (C : {set seatT}) (x : psl211_inputT)
    (g : pgg_gT psl211_M) (i : seatT) :
  i \in C ->
  @static_coalition_obs psl211_algebra psl211_alldecks_params C x g i
  = tnth (psl211_alldecks_layout x) (@pgg_rho psl211_M g i).
Proof. by move=> Hi; rewrite psl211_alldecks_static_obsE Hi. Qed.

(******************************************************************************)
(*     The observed execution                                                 *)
(******************************************************************************)

(** psl211_alldecks_endpoints — the interpreter's messages of the all-decks
    run compute the direct computation of the laid deck. The profile's
    abstract-readout equation quantifies over the content readout, so the
    dealer-dealt mode and the all-decks mode rest on that one equation and
    this file names it rather than deciding anything about the run. *)
Definition psl211_alldecks_endpoints
  : instance_endpoints_stmt psl211_alldecks_params :=
  @supplied_endpointsE psl211_algebra psl211_inputT psl211_alldecks_layout
    psl211_alldecks_expected psl211_fuel psl211_profile_endpoints.

(** psl211_alldecks_observed — the observed execution of the all-decks run:
    the run finishes inside its budget, the verifier collects one endpoint per
    seat, and decoding them returns the chirality the input names. This is the
    value every analysis of this instance consumes. *)
Definition psl211_alldecks_observed : OE.ObservedExecution :=
  instance_observed psl211_alldecks_terminates psl211_alldecks_endpoints
    psl211_alldecks_recon.

(** psl211_alldecks_observed_recovers — the packaged all-decks run decodes to
    the chirality its input names, at every deck description and every cut in
    the group. This is the correctness half of what the instance publishes:
    the value a coalition is proved to learn nothing about is the value the
    protocol actually reconstructs. *)
Theorem psl211_alldecks_observed_recovers (x : psl211_inputT)
    (w0 : pgg_gT psl211_M) (Gw0 : w0 \in pgg_G psl211_M) :
  @exec_decode mpP eP (@exec_endpoints mpP eP x w0 0)
    (OE.oe_endpoints_size psl211_alldecks_observed x w0) = x.1.
Proof. exact: (OE.oe_run_recovers psl211_alldecks_observed x w0 Gw0). Qed.

(******************************************************************************)
(*     The executed content reader                                            *)
(******************************************************************************)

(** psl211_content_of tr — the card a participant's executed interpreter row
    reports: the first card of the first hand message the row carries. *)
Definition psl211_content_of (N : nat) (tr : seq (pgg_data N.+1)) : 'I_N.+1 :=
  if tr is _ :: PGG_hand (x :: _) :: _ then x else ord0.

(** psl211_exec_content_trace C x w0 — the coalition's executed trace read
    through psl211_content_of: the finite function sending a seat in C to the
    content of that seat's executed interpreter row, and every seat outside C
    to ord0. The profile's seat index and the coalition view's are the same
    type, so no transport stands between the execution layer and the view. *)
Definition psl211_exec_content_trace (C : {set seatT}) (x : psl211_inputT)
    (w0 : pgg_gT psl211_M) : {ffun seatT -> cardT} :=
  [ffun i => if i \in C
             then psl211_content_of
                    (@exec_participant_trace mpP eP x w0 0 i)
             else ord0].

(** psl211_alldecks_fuelE — the derived plug runs at the budget the
    parametrization names. *)
Lemma psl211_alldecks_fuelE : ep_fuel eP = psl211_fuel.
(* Stated on its own so that the row equation below never has to compare two
   interpreter applications at two spellings of the fuel: the kernel, asked
   for that comparison, unfolds run_interp, which is the 561-second reduction
   of psl211_endpoints.v (measured 2026-09-15). *)
Proof. by []. Qed.

(** psl211_exec_rowE — the executed participant trace at seat i is row 2 + i
    of the derived run. The dealer and the verifier take the first two process
    identifiers, so a seat's row starts at two. *)
Lemma psl211_exec_rowE (x : psl211_inputT) (w0 : pgg_gT psl211_M) (i : seatT) :
  @exec_participant_trace mpP eP x w0 0 i
  = nth [::] (@exec_run mpP eP x w0 0).2 (2 + i).
(* Stated against exec_run and not against a fuel literal: the literal version
   holds by erefl and hangs at Qed, the kernel unfolding run_interp to decide
   it. The all-decks run has no hand-written process list beside the derived
   one, so as stated it holds by delta on the two extractors. *)
Proof. by []. Qed.

(** psl211_content_trace — the same reader as a random variable of a sample
    point of the all-decks model. *)
Definition psl211_content_trace (R : realType) (C : {set seatT})
  : {RV (psl211_alldecksP R) -> {ffun seatT -> cardT}} :=
  fun u => [ffun i => if i \in C
                      then psl211_content_of
                             (nth [::] (@exec_run mpP eP u.1 u.2 0).2 (2 + i))
                      else ord0].

(** psl211_content_traceE — the executed content reader is that random
    variable. What a coalition's interpreter rows actually contain is what the
    sampled reader reads, so a statement proved about the random variable is a
    statement about the executed run. *)
Lemma psl211_content_traceE (R : realType) (C : {set seatT})
    (u : psl211_inputT * pgg_gT psl211_M) :
  psl211_exec_content_trace C u.1 u.2 = psl211_content_trace R C u.
Proof.
apply/ffunP => i.
rewrite /psl211_exec_content_trace /psl211_content_trace.
(* An unscoped rewrite ffunE reaches inside the finfun body and evaluates the
   interpreter; the scoped form fires immediately. *)
rewrite [LHS]ffunE [RHS]ffunE.
by case Hi: (i \in C); rewrite ?psl211_exec_rowE.
Qed.

(** psl211_content_ofE — the reader skips one message and takes the head of
    the hand. The card a row reports is the first card of the hand the dealer
    sent and not of the row's first message, which is what makes the executed
    content reader a reader of the dealt deck. *)
Lemma psl211_content_ofE (N : nat) (m : pgg_data N.+1) (x : 'I_N.+1)
    (l : seq 'I_N.+1) (rest : seq (pgg_data N.+1)) :
  psl211_content_of (m :: PGG_hand (x :: l) :: rest) = x.
Proof. by []. Qed.

(** psl211_alldecks_secret_expectedE — the secret the exact witness is about
    is the value the run recovers, read off the same sample point. ExactWitness
    has no field relating its secret to the run's expected value, so without
    this equation the witness could be independent of a bit the protocol never
    reconstructs and the published independence would be true and empty. *)
Lemma psl211_alldecks_secret_expectedE (R : realType)
    (u : psl211_inputT * pgg_gT psl211_M) :
  psl211_alldecks_secret R u
  = ex_expected psl211_alldecks_params ((psl211_alldecks_sample R).(sa_arg) u).
Proof. by []. Qed.

(** psl211_alldecks_exec_viewE — the executed coalition reader of the
    all-decks model is the static coalition reading. This is the step that
    turns a claim about the interpreter's messages into a claim about the
    group action, and it is what the endpoint equation buys. *)
Lemma psl211_alldecks_exec_viewE (R : realType) (C : {set seatT}) :
  @sa_coalition_view R mpP eP (psl211_alldecks_sample R) 0 C
  = (fun u => @static_coalition_obs psl211_algebra psl211_alldecks_params C
                u.1 u.2).
Proof.
exact: (@sa_coalition_viewE R mpP eP (psl211_alldecks_sample R) 0
          (ex_content_obs psl211_alldecks_params)
          (fun u => psl211_alldecks_endpoints _ _) C).
Qed.

(** psl211_alldecks_exec_view_instE — and therefore the executed coalition
    reader is the instance-side view of the laid deck, which is the function
    the counting argument is stated about. *)
Lemma psl211_alldecks_exec_view_instE (R : realType) (C : {set seatT}) :
  @sa_coalition_view R mpP eP (psl211_alldecks_sample R) 0 C
  = (fun u => psl211_alldecks_view C u.1 u.2).
Proof.
by rewrite psl211_alldecks_exec_viewE psl211_alldecks_exact_viewE.
Qed.

(******************************************************************************)
(*     Independence of the chirality at five seats                            *)
(******************************************************************************)

(** psl211_alldecks_view_indep — under the all-decks dealer the raw code
    reading of any coalition of at most five of the twelve seats is
    independent of the chirality. Exact, at every real field, and an average
    over decks and cuts rather than a statement about one deck: the whole
    instance-specific content is the equality of the two chiralities' deal
    counts, which the uniform-pair bridge turns into independence. *)
Lemma psl211_alldecks_view_indep (R : realType) (C : {set seatT}) :
  (#|C| <= 5)%N ->
  psl211_alldecksP R |= (fun u => psl211_alldecks_view C u.1 u.2)
                    _|_ psl211_alldecks_secret R.
Proof.
move=> HC.
apply: (@uniform_pair_indep_of_fibers R psl211_inputT (pgg_gT psl211_M) _
          (fun x : psl211_inputT => x.1) (pgg_G psl211_M) psl211_G_pos
          psl211_alldecks_gt0 (psl211_alldecks_view C)).
by move=> v; exact: psl211_alldecks_fiber_transfer.
Qed.

(** psl211_alldecks_static_indep — the same independence on the framework's
    side, which is the form the exact arm's witness field demands. *)
Lemma psl211_alldecks_static_indep (R : realType) (C : {set seatT}) :
  (#|C| <= 5)%N ->
  psl211_alldecksP R
  |= (fun u : psl211_inputT * pgg_gT psl211_M =>
        @static_coalition_obs psl211_algebra psl211_alldecks_params C u.1 u.2)
  _|_ psl211_alldecks_secret R.
Proof.
move=> HC; rewrite psl211_alldecks_exact_viewE.
exact: psl211_alldecks_view_indep.
Qed.

(** psl211_exact_family — the all-decks model as a unit-indexed family: one
    member at every real field, the model having no parameter to range over. *)
Definition psl211_exact_family : AnalysisModelFamily psl211_alldecks_observed :=
  @MkAnalysisModelFamily psl211_alldecks_observed (fun _ => unit)
    (fun R _ => psl211_alldecks_sample R).

(** psl211_exact_witness — the exact arm's witness: the chirality as a random
    variable on the all-decks sample space, and at every coalition of fewer
    than six seats the independence of that coalition's reading from it. The
    framework derives the zero mutual information, the unchanged conditional
    entropy and the closure under post-processing from this one field, so the
    witness is the whole of what this instance owes the exact arm. *)
Definition psl211_exact_witness (R : realType) (idx : unit)
  : ExactWitness (amf_sample psl211_exact_family R idx) :=
  @MkExactWitness R psl211_algebra psl211_alldecks_params
    (amf_sample psl211_exact_family R idx) bool (psl211_alldecks_secret R)
    (fun C HC =>
       (* The field's premise is #|C| < profile_k (instance_profile
          psl211_algebra), the threshold is six by profile_k_psl211_algebra,
          and the coercion to #|C| <= 5 is by conversion. *)
       let H5 : (#|C| <= 5)%N := HC in
       (eq_ind_r
          (fun v => psl211_alldecksP R |= v _|_ psl211_alldecks_secret R)
          (psl211_alldecks_view_indep R H5)
          (psl211_alldecks_exact_viewE C))).

(** psl211_alldecks_coalition_distE — the executed coalition distribution of
    the all-decks model is the pushforward of the model's own law along the
    instance-side reading. This is the equation that makes a counting result
    proved about the laid deck a result about what the interpreter's messages
    carry, so every independence statement here is attached to the executed
    observer and not only to the static one. *)
Lemma psl211_alldecks_coalition_distE (R : realType) (C : {set seatT}) :
  @sa_coalition_dist R (instance_profile psl211_algebra)
    (instance_exec psl211_alldecks_params) (psl211_alldecks_sample R) 0 C
  = fdistmap (fun u => psl211_alldecks_view C u.1 u.2) (psl211_alldecksP R).
Proof.
rewrite /sa_coalition_dist; congr fdistmap.
exact: psl211_alldecks_exec_view_instE.
Qed.

(** psl211_alldecks_exec_exact_view_indep — at five seats the executed
    coalition observation of the all-decks model and the chirality have a
    product joint distribution, for a coalition of at most five of the twelve
    seats. This is psl211_alldecks_view_indep transported to the executed
    sample layer, so the independence is a statement about what the
    interpreter's messages contain and not only about the instance-side
    reading. *)
Corollary psl211_alldecks_exec_exact_view_indep (R : realType)
    (C : {set seatT}) :
  (#|C| <= 5)%N ->
  fdistmap (fun u => (psl211_alldecks_view C u.1 u.2,
                      psl211_alldecks_secret R u))
           (psl211_alldecksP R)
  = ((@sa_coalition_dist R (instance_profile psl211_algebra)
        (instance_exec psl211_alldecks_params) (psl211_alldecks_sample R) 0 C)
     `x (fdistmap (psl211_alldecks_secret R) (psl211_alldecksP R)))%fdist.
Proof.
move=> HC; rewrite psl211_alldecks_coalition_distE.
exact: (inde_dist_of_RV2 (psl211_alldecks_view_indep R HC)).
Qed.
