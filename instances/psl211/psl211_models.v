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
(* Naming: the law of the model is psl211_alldecksP and not                   *)
(* psl211_alldecks_sampleP, which is the conventional spelling the            *)
(* repository's other two-mode instance uses (s5_models.v:106                 *)
(* s5_rand_sampleP). The short form is the one the probes compiled and the    *)
(* one psl211_alldecks_sampleP_E is the equation of.                          *)
(*                                                                            *)
(* content_of lives in instances/pgl27/pgl27_trace.v and nothing shared       *)
(* exports it, so the row reader is restated here as psl211_content_of and    *)
(* pinned in both directions by psl211_content_ofE.                           *)
(*                                                                            *)
(* The exact arm's witness over psl211_exact_family is built in               *)
(* instances/psl211/tableau/psl211_tableau_analysis_bridged.v, beside the     *)
(* Tableau surface whose ExactWitness record gives it its type, which is      *)
(* where the other three instances build theirs. This file therefore          *)
(* imports nothing from the manifest layer.                                   *)
(*                                                                            *)
(* The dealer route. The all-decks independence is obtained a second way,     *)
(* from the dealer model of reconstruct/dealer_privacy.v, by placing the      *)
(* chirality, the deal and the cut in its sample space. The                   *)
(* route goes through the mixed-law condition, whose premise the per-cut      *)
(* count of psl211_alldecks.v discharges, and it restates                     *)
(* psl211_alldecks_view_indep without replacing its proof. Two refutations    *)
(* bound it: the per-deck condition has no solution under this dealer, and    *)
(* under a dealer laying one fixed deal the reading of three                  *)
(* seats is not independent of the chirality.                                 *)
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
(*   psl211_dealer_delta     == the all-decks dealer of the dealer model      *)
(*   psl211_dealer_nu        == the uniform cut law                           *)
(*   psl211_dealerP          == the instance's data in the dealer sample      *)
(*                              space                                         *)
(*   psl211_dealer_assoc     == the reassociation of the two sample spaces    *)
(*   psl211_dealer_view      == the coalition's reading as a function of the  *)
(*                              dealer model's three coordinates              *)
(*   psl211_dealer_mixed_law == the reading's law at one chirality,           *)
(*                              averaged over the deal and the cut            *)
(*   psl211_perdeck_deal     == the deal fixing the counterexample            *)
(*   psl211_perdeck_coalition == the three seats 0, 1 and 2                   *)
(*   psl211_perdeck_view     == the reading that fixes the counterexample     *)
(*   psl211_perdeck_fiber    == the cuts producing that reading               *)
(*   psl211_fixed_deal_delta == the dealer laying one deal at                 *)
(*                              both chiralities                              *)
(*   psl211_fixed_dealP      == the dealer law at that kernel                 *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_alldecks_inputTE == the plug's run argument carrier is the        *)
(*                              description carrier                           *)
(*   psl211_alldecks_cut_distE == the model's cut is the uniform shuffle      *)
(*   psl211_alldecks_static_obsE == the framework's reading at a seat is the  *)
(*                              card the laid deck puts at its cut image,     *)
(*                              and ord0 outside the coalition                *)
(*   psl211_alldecks_exact_viewE == the same with the description inside the  *)
(*                              sample point                                  *)
(*   psl211_alldecks_observed_recovers == the packaged run decodes to the     *)
(*                              chirality its input names                     *)
(*   psl211_exec_rowE        == a seat's executed trace is row 2 + i          *)
(*   psl211_content_traceE   == the executed content reader is that random    *)
(*                              variable                                      *)
(*   psl211_alldecks_secret_expectedE == the secret is the value the run      *)
(*                              recovers                                      *)
(*   psl211_alldecks_exec_viewE == the executed coalition reader is the       *)
(*                              static one                                    *)
(*   psl211_alldecks_view_indep == a coalition of at most five seats reads a  *)
(*                              view independent of the chirality             *)
(*   psl211_alldecks_static_indep == the same on the framework's side         *)
(*   psl211_alldecks_coalition_distE == the executed coalition distribution   *)
(*                              is the pushforward of the law along the view  *)
(*   psl211_alldecks_exec_exact_view_indep == the product joint law at the    *)
(*                              executed sample layer                         *)
(*   psl211_dealerPE         == the reassociation carries the all-decks law   *)
(*                              to the dealer model's law                     *)
(*   psl211_dealer_sectionE  == at one cut the two chiralities send the       *)
(*                              uniform law on deals to the same reading law  *)
(*   psl211_dealer_mixed_lawE == and so do they averaged over the deal        *)
(*                              and the cut                                   *)
(*   psl211_dealer_view_indep == independence in the dealer sample space      *)
(*   psl211_alldecks_view_indep_via_dealer == psl211_alldecks_view_indep      *)
(*                              obtained from dealer_shuffle_view_indep       *)
(*   psl211_perdeck_raw_countE == at one deal the two                         *)
(*                              chiralities have 0 and 1 cuts producing one   *)
(*                              reading                                       *)
(*   psl211_perdeck_fiber_card_neq == the same as a statement about the       *)
(*                              fibers in the group                           *)
(*   psl211_perdeck_law_neq  == and as a statement about the two laws         *)
(*   psl211_dealer_view_indep_of_deck_unsat == the two premises of            *)
(*                              dealer_shuffle_view_indep_of_deck have no     *)
(*                              common solution at this instance's dealer     *)
(*   psl211_fixed_deal_view_dep == under a dealer laying one fixed deck       *)
(*                              description the reading of three seats is     *)
(*                              not independent of the chirality              *)
(*   psl211_dealer_viewE == the model's reading along the reassociation is    *)
(*                              the instance's reading                        *)
(*   psl211_dealer_secretE == and its secret the instance's chirality         *)
(*   psl211_dealer_valid_forced == the all-decks dealer forces every validity *)
(*                              predicate to accept psl211_perdeck_deal       *)
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
From pgg_reconstruct Require Import dealer_privacy.
From pgg_reconstruct Require Import design_privacy.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import psl211_group psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_exec.
From pgg_smc Require Import psl211_endpoints psl211_alldecks.
(* psl211_blocks and psl211_closure carry the raw permutation tables that the
   per-deck count below runs over; every other statement of this file reaches
   them only through psl211_alldecks. *)
From pgg_smc Require Import psl211_blocks psl211_closure.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
(* Num.Theory is needed by the per-deck refutations at the end of the file,
   which compare a mass with zero; nothing above them uses it. *)
Import Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(** mpP — the monodromy profile the twelve-card algebra derives. *)
Local Notation mpP := (instance_profile psl211_algebra).

(** eP — the execution plug the all-decks parametrization derives. *)
Local Notation eP := (instance_exec psl211_alldecks_params).

(* Both are spelled through the derived profile rather than as 'I_12, so that
   the framework's obligations unify with the instance's statements by
   conversion. *)
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
    the shuffle group. This is the cut the exact arm needs. *)
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
    coalition reading is the card the laid deck puts at the cut image of
    seat i, and ord0 at every seat outside C. Every security statement of this
    instance is made about the left-hand side and every counting argument
    about the right, so this equation is the whole of what carries one to the
    other. *)
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
    block count of the counting argument is taken over. *)
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
    the run finishes inside its fuel, the verifier collects one endpoint per
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

(** psl211_alldecks_fuelE — the derived plug runs at the fuel the
    parametrization names. *)
Lemma psl211_alldecks_fuelE : ep_fuel eP = psl211_fuel.
(* Stated on its own so that the row equation below never has to compare two
   interpreter applications at two spellings of the fuel: the kernel, asked
   for that comparison, unfolds run_interp. That reduction measured 561.4 s in
   probe P1b2 and 568.1 s in the compile of psl211_endpoints.v itself, both on
   2026-09-15. *)
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

(** psl211_alldecks_secret_expectedE — the secret the exact arm certifies is
    the value the run recovers, read off the same sample point. The exact
    arm's witness has no field relating its secret to the run's expected
    value, so without this equation that secret could be independent of a bit
    the protocol never reconstructs and the published independence would be
    true and empty. *)
Lemma psl211_alldecks_secret_expectedE (R : realType)
    (u : psl211_inputT * pgg_gT psl211_M) :
  psl211_alldecks_secret R u
  = ex_expected psl211_alldecks_params ((psl211_alldecks_sample R).(sa_arg) u).
Proof. by []. Qed.

(** psl211_alldecks_exec_viewE — the executed coalition reader of the
    all-decks model is the static coalition reading. This is the step that
    turns a claim about the interpreter's messages into a claim about the
    group action, and it is what the endpoint equation gives. *)
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
    side, which is the form the exact arm's witness demands of it. *)
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
(* The funext step of the pgl27 script is not needed here:
   psl211_alldecks_exec_view_instE is already an equality of functions, where
   pgl27's bridge lemma is pointwise, so exact: closes the goal congr fdistmap
   leaves. *)
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

(******************************************************************************)
(*     The same independence through the dealer model                         *)
(******************************************************************************)

(** dealT — a deal, the chirality-free part of a deck description: a block
    index together with two labellings. *)
Local Notation dealT := psl211_deal.

(** cutT — an element of the shuffle group. *)
Local Notation cutT := (pgg_gT psl211_M).

(** viewT — what a coalition reads, one card code per seat. *)
Local Notation viewT := ({ffun seatT -> cardT}).

(* psl211_alldecks_view expands to the laid deck and through it to the two
   132-row block tables of psl211_alldecks.v.  Sealing it keeps a failed
   unification from descending into those tables: a rule differing from the
   other side of the goal only in the chirality bit makes the matcher compare
   the two table literals, and it does not come back.  No step below needs the
   body of the reading; each names it and closes by exact. *)
Local Opaque psl211_alldecks_view.

Section psl211_dealer.
Variable R : realType.

(** psl211_deal_pos — the type of deals is inhabited, so it carries a
    uniform law. *)
Lemma psl211_deal_pos : (0 < #|[set: dealT]|)%N.
Proof.
apply/card_gt0P.
by exists (ord0, 1%g, 1%g); rewrite inE.
Qed.

(** psl211_dealer_delta — the all-decks dealer: whatever the chirality, the
    deal is drawn uniformly and independently of it.  This is the
    instance's dealer kernel, and its independence of the chirality is what
    makes the averaged symmetry of psl211_alldecks available. *)
Definition psl211_dealer_delta (_ : bool) : R.-fdist dealT :=
  `U psl211_deal_pos.

(** psl211_dealer_nu — the cut law: a uniform element of the PSL(2,11) shuffle
    group. *)
Definition psl211_dealer_nu : R.-fdist cutT := `U psl211_G_pos.

(** psl211_dealerP — the instance's data placed in the dealer model's sample
    space, a chirality paired with a deal and a cut. *)
Definition psl211_dealerP : R.-fdist (bool * (dealT * cutT)) :=
  @dealer_shuffleP R bool dealT cutT
    (fdist_uniform card_bool) psl211_dealer_delta psl211_dealer_nu.

(** psl211_dealer_assoc — the reassociation of the instance's sample space,
    which pairs a chirality with a deal before pairing with the cut, into the
    dealer model's, which pairs the chirality with the pair.  It moves no
    mass. *)
Definition psl211_dealer_assoc
    (u : psl211_inputT * cutT) : bool * (dealT * cutT) :=
  (u.1.1, (u.1.2, u.2)).

(** psl211_dealerPE — the reassociation carries the instance's all-decks law
    to the dealer model's law at psl211_dealer_delta and psl211_dealer_nu.  Both
    are uniform on the same finite set written in two associations, so the
    identification adds nothing probabilistic and fixes which of the dealer
    model's three draws each of the instance's coordinates is. *)
Lemma psl211_dealerPE :
  fdistmap psl211_dealer_assoc (psl211_alldecksP R) = psl211_dealerP.
Proof.
apply: fdist_ext => -[b [d g]].
rewrite fdistmapE /psl211_dealer_assoc /psl211_alldecksP /psl211_dealerP.
rewrite dealer_shufflePE /psl211_dealer_delta /psl211_dealer_nu.
rewrite (big_pred1 ((b, d), g)) /=.
- rewrite !fdist_prodE /= !fdist_uniformE.
  have Hall : (b, d) \in [set: psl211_inputT] by rewrite inE.
  have Hdall : d \in [set: dealT] by rewrite inE.
  rewrite (fdist_uniform_supp_in R psl211_alldecks_gt0 Hall).
  rewrite (fdist_uniform_supp_in R psl211_deal_pos Hdall).
  by rewrite !cardsT card_prod card_bool natrM invfM mulrA.
- move=> [[b' d'] g']; rewrite !inE /= !xpair_eqE.
  by rewrite andbA.
Qed.

(** psl211_dealer_view C — the reading of a coalition C of seats, as a
    function of the dealer model's three coordinates.  It reads the chirality
    only through the deck the deal lays, which is why a symmetry between the two
    chiralities is enough to hide the chirality from C. *)
Definition psl211_dealer_view (C : {set seatT})
    (b : bool) (d : dealT) (g : cutT) : viewT :=
  psl211_alldecks_view C (b, d) g.

(** psl211_dealer_viewE — the dealer model's reading, composed with the
    reassociation, is the instance's reading. *)
Lemma psl211_dealer_viewE (C : {set seatT}) :
  @dealer_shuffle_view R bool dealT cutT viewT
    (fdist_uniform card_bool) psl211_dealer_delta psl211_dealer_nu
    (psl211_dealer_view C) \o psl211_dealer_assoc =
  (fun u => psl211_alldecks_view C u.1 u.2).
Proof. by apply: boolp.funext => -[[b d] g]. Qed.

(** psl211_dealer_secretE — the dealer model's secret, composed with the
    reassociation, is the instance's chirality. *)
Lemma psl211_dealer_secretE :
  @dealer_shuffle_secret R bool dealT cutT
    (fdist_uniform card_bool) psl211_dealer_delta psl211_dealer_nu
    \o psl211_dealer_assoc =
  psl211_alldecks_secret R.
Proof. by []. Qed.

(** psl211_dealer_bad_assoc — the reassociation with the chirality negated,
    used only to show that the identification of the secret is not automatic. *)
Definition psl211_dealer_bad_assoc
    (u : psl211_inputT * cutT) : bool * (dealT * cutT) :=
  (~~ u.1.1, (u.1.2, u.2)).

(* Expected failure: the secret identification under a negated chirality.  The
   two sides are convertible only if ~~ b and b are, so erefl does not
   typecheck against the ascribed equation. *)
Fail Definition psl211_dealer_bad_secretE :
  @dealer_shuffle_secret R bool dealT cutT
    (fdist_uniform card_bool) psl211_dealer_delta psl211_dealer_nu
    \o psl211_dealer_bad_assoc =
  psl211_alldecks_secret R := erefl.

(** psl211_dealer_mixed_law C b — the law of the coalition's reading at
    chirality b, averaged over the deal and the cut.  It is the quantity the
    dealer model's privacy premise asks to be the same for both chiralities. *)
Definition psl211_dealer_mixed_law (C : {set seatT}) (b : bool) :
    R.-fdist viewT :=
  fdistmap (fun dg => psl211_dealer_view C b dg.1 dg.2)
    ((psl211_dealer_delta b) `x psl211_dealer_nu).

(** psl211_dealer_sectionE — at one cut, the two chiralities send the uniform
    law on deals to the same law on what a coalition of at most
    five seats reads.  This is the per-cut deal count of psl211_alldecks read
    as an equality of laws, and it is the only place where the instance's laid
    deck enters the bridge. *)
Lemma psl211_dealer_sectionE (C : {set seatT}) (g : cutT) :
  (#|C| <= 5)%N ->
  fdistmap (fun d => psl211_dealer_view C true d g)
    ((`U psl211_deal_pos) : R.-fdist dealT) =
  fdistmap (fun d => psl211_dealer_view C false d g)
    ((`U psl211_deal_pos) : R.-fdist dealT).
Proof.
move=> HC; apply: uniform_fdistmap_fiberTE => v.
rewrite /psl211_dealer_view.
exact: (psl211_alldecks_per_cut_count C g v HC).
Qed.

(** psl211_dealer_mixed_lawE — the two chiralities have the same averaged
    reading law.  The per-cut equality is lifted to the pair of deal and cut,
    which is the dealer model's privacy premise at this instance. *)
Lemma psl211_dealer_mixed_lawE (C : {set seatT}) :
  (#|C| <= 5)%N ->
  psl211_dealer_mixed_law C false = psl211_dealer_mixed_law C true.
Proof.
move=> HC.
rewrite /psl211_dealer_mixed_law /psl211_dealer_delta /psl211_dealer_nu.
apply: (@fdistmap_prod_sectionE R dealT cutT viewT
  ((`U psl211_deal_pos) : R.-fdist dealT) psl211_dealer_nu
  (fun d g => psl211_dealer_view C false d g)
  (fun d g => psl211_dealer_view C true d g)) => g _.
symmetry; exact: (@psl211_dealer_sectionE C g HC).
Qed.

(** psl211_dealer_view_indep — in the dealer model's sample space, the reading
    of a coalition of at most five seats is independent of the chirality.  This
    is dealer_shuffle_view_indep at the common averaged law, and it is exact: no
    approximation and no computational premise. *)
Lemma psl211_dealer_view_indep (C : {set seatT}) :
  (#|C| <= 5)%N ->
  psl211_dealerP |=
    @dealer_shuffle_view R bool dealT cutT viewT
      (fdist_uniform card_bool) psl211_dealer_delta psl211_dealer_nu
      (psl211_dealer_view C)
    _|_ @dealer_shuffle_secret R bool dealT cutT
      (fdist_uniform card_bool) psl211_dealer_delta psl211_dealer_nu.
Proof.
move=> HC.
apply: (@dealer_shuffle_view_indep R bool dealT cutT viewT
  (fdist_uniform card_bool) psl211_dealer_delta psl211_dealer_nu
  (psl211_dealer_view C) (psl211_dealer_mixed_law C true)) => b _.
case: b; first exact: erefl.
exact: (@psl211_dealer_mixed_lawE C HC).
Qed.

(** psl211_alldecks_view_indep_via_dealer — the statement is
    psl211_alldecks_view_indep verbatim; only the route differs.  It is the
    instance's own privacy statement, obtained by transporting the dealer
    model's independence back across the reassociation.  Nothing of the counting
    argument is redone here: the deal count of psl211_alldecks entered at
    psl211_dealer_sectionE and this step only changes the coordinates the same
    law is written in. *)
Lemma psl211_alldecks_view_indep_via_dealer (C : {set seatT}) :
  (#|C| <= 5)%N ->
  psl211_alldecksP R |=
    (fun u => psl211_alldecks_view C u.1 u.2)
    _|_ psl211_alldecks_secret R.
Proof.
move=> HC; have Hgen := @psl211_dealer_view_indep C HC.
rewrite -psl211_dealerPE in Hgen.
(* the two commuting equations are rewritten into the goal, not into Hgen: the
   goal names the reading only through psl211_alldecks_view, which is sealed,
   so the matcher never reaches the block tables underneath it *)
rewrite -(@psl211_dealer_viewE C) -psl211_dealer_secretE.
by apply/inde_RV_fdistmap.
Qed.

End psl211_dealer.

(* The counting below is on raw data and needs the body of the reading, so the
   seal is released here and taken again once the raw count is carried back to
   the real objects. *)
Local Transparent psl211_alldecks_view.

(******************************************************************************)
(*     What the dealer law does and does not preserve                         *)
(******************************************************************************)

(* Only raw nat data reduces here.  `inord` is `insubd ord0`, whose `insub`
   branches on the Qed-opaque `idP`, so `inord k` never becomes an `Ordinal`
   under vm_compute; measured 2026-09-18, `Eval vm_compute in val (inord 0)`
   returns a stuck `match idP with ...`.  Since `psl211_alldecks_seq` and every
   finfun or finset over the card type go through `inord` or `ord_enum`, the
   counted term below names none of them: it is a `count` over the raw
   permutation tables, and the three lemmas psl211_perdeck_seqE,
   psl211_perdeck_raw_viewE and psl211_perdeck_testE carry it back to the deck,
   the reading and the shuffle group symbolically. *)

(** psl211_perdeck_deal — the deal that fixes the counterexample:
    block index zero of the chirality's table, with both labellings the
    identity. *)
Definition psl211_perdeck_deal : dealT := (ord0, 1%g, 1%g).

(** psl211_perdeck_coalition — the three seats 0, 1 and 2. *)
Definition psl211_perdeck_coalition : {set seatT} :=
  [set i : seatT | val i \in [:: 0; 1; 2]].

(** psl211_perdeck_view — the reading that gives cards 0, 1 and 5 to seats 0,
    1 and 2, and card 0 to every seat outside the coalition. *)
Definition psl211_perdeck_view : viewT :=
  [ffun i => psl211_code12 (nth 0 [:: 0; 1; 5] (val i))].

(** psl211_perdeck_seq b — the deck psl211_perdeck_deal names at chirality b,
    as raw codes by position: a position of block zero carries its own rank in
    that block, and every other position carries six plus its rank in the
    complement, the identity labellings acting trivially. *)
Definition psl211_perdeck_seq (b : bool) : seq nat :=
  let H := psl211_alldecks_row (b, psl211_perdeck_deal) in
  let K := psl211_alldecks_corow (b, psl211_perdeck_deal) in
  [seq (if p \in H then index p H else 6 + index p K) | p <- iota 0 12].

(** psl211_perdeck_row_size — block zero of either chirality's table has six
    positions, the heart block of a Steiner sextet. *)
Lemma psl211_perdeck_row_size (b : bool) :
  size (psl211_alldecks_row (b, psl211_perdeck_deal)) = 6.
Proof. by case: b; vm_compute. Qed.

(** psl211_perdeck_corow_size — its complement has the other six. *)
Lemma psl211_perdeck_corow_size (b : bool) :
  size (psl211_alldecks_corow (b, psl211_perdeck_deal)) = 6.
Proof. by case: b; vm_compute. Qed.

(** psl211_perdeck_seqE — that raw list is the deck the all-decks dealer lays
    for this deal, so a count over raw codes is a count over dealt decks. *)
Lemma psl211_perdeck_seqE (b : bool) :
  psl211_alldecks_seq (b, psl211_perdeck_deal) = psl211_perdeck_seq b.
Proof.
(* The two sides differ only by the identity labelling and the inord that
   names a rank: `\val (inord _)` is convertible to, but not syntactically,
   the `nat_of_ord (inord _)` that inordK keys on, so inordK is applied
   rather than rewritten with. *)
have Hrow := psl211_perdeck_row_size b.
have Hcorow := psl211_perdeck_corow_size b.
rewrite /psl211_perdeck_deal in Hrow Hcorow.
rewrite /psl211_alldecks_seq /psl211_perdeck_seq /psl211_perdeck_deal.
apply/eq_in_map => p Hp.
(* the pattern carries %N: this file opens ring_scope, so an unannotated
   _ < X parses as the ring order and matches no subterm of a nat goal *)
case: ifP => Hin.
  rewrite perm1; apply: inordK.
  by rewrite -[X in (_ < X)%N]Hrow index_mem Hin.
rewrite perm1; apply/eqP; rewrite eqn_add2l; apply/eqP.
apply: inordK.
rewrite -[X in (_ < X)%N]Hcorow index_mem /psl211_alldecks_corow mem_filter.
by rewrite Hin Hp.
Qed.

(** psl211_perdeck_raw_view sq t — the reading the coalition gets from the
    deck sq under the cut whose table is t, written on raw data. *)
Definition psl211_perdeck_raw_view (sq t : seq nat) : viewT :=
  [ffun i => if val i \in [:: 0; 1; 2]
             then psl211_code12 (nth 0 sq (nth 0 t (val i)))
             else ord0].

(** psl211_perdeck_test sq t — the same reading matches psl211_perdeck_view,
    tested on raw codes. *)
Definition psl211_perdeck_test (sq t : seq nat) : bool :=
  [&& nth 0 sq (nth 0 t 0) %% 12 == 0,
      nth 0 sq (nth 0 t 1) %% 12 == 1 &
      nth 0 sq (nth 0 t 2) %% 12 == 5].

(** psl211_perdeck_testE — the raw test decides the reading, so the fiber over
    psl211_perdeck_view is counted by a boolean on nat lists. *)
Lemma psl211_perdeck_testE (sq t : seq nat) :
  (psl211_perdeck_raw_view sq t == psl211_perdeck_view) =
  psl211_perdeck_test sq t.
Proof.
rewrite /psl211_perdeck_test; apply/idP/idP.
- move/eqP/ffunP => H; apply/and3P; split; apply/eqP.
  + by move: (H (psl211_code12 0)) => /(congr1 val); rewrite !ffunE /=.
  + by move: (H (psl211_code12 1)) => /(congr1 val); rewrite !ffunE /=.
  + by move: (H (psl211_code12 2)) => /(congr1 val); rewrite !ffunE /=.
- case/and3P => H0 H1 H2; apply/eqP/ffunP => i.
  rewrite !ffunE; apply/val_inj.
  case: i => [] [|[|[|k]]] Hk //=.
  + by rewrite (eqP H0).
  + by rewrite (eqP H1).
  + by rewrite (eqP H2).
  + by rewrite nth_default.
Qed.

(** psl211_perdeck_raw_count b — how many of the 660 cuts carry the deck
    of chirality b to psl211_perdeck_view. *)
Definition psl211_perdeck_raw_count (b : bool) : nat :=
  let sq := psl211_perdeck_seq b in
  count (psl211_perdeck_test sq) (unzip1 psl211_elem_table).

(** psl211_perdeck_raw_countE — that count is zero at one chirality and one
    at the other, which is the per-deck failure of the chirality symmetry: at
    a fixed deal the two chiralities do not have equally many cuts producing
    a given reading, even though summing over the deals they do. *)
Lemma psl211_perdeck_raw_countE :
  psl211_perdeck_raw_count true = 0 /\ psl211_perdeck_raw_count false = 1.
Proof. by split; vm_compute. Qed.

(** psl211_perdeck_entry_perm_enum — the 660 tabulated entries list the
    shuffle group. *)
Lemma psl211_perdeck_entry_perm_enum :
  perm_eq (enum (pgg_G psl211_M))
    [seq psl211_entry_perm k | k <- iota 0 660].
Proof.
apply: uniq_perm.
- exact: enum_uniq.
- rewrite map_inj_in_uniq.
    exact: iota_uniq.
  exact: psl211_entry_perm_inj.
- move=> g; rewrite mem_enum.
  apply/idP/idP.
    exact: psl211_mem_entry_perm.
  move=> /mapP[k _ ->].
  exact: psl211_entry_perm_mem.
Qed.

(** psl211_perdeck_ptbl_nth — a cut's table reads off its images. *)
Lemma psl211_perdeck_ptbl_nth (g : cutT) (i : seatT) :
  nth 0 (psl211_ptbl g) i = val (g i).
Proof.
rewrite /psl211_ptbl (nth_map i) ?size_enum_ord ?ltn_ord //.
by rewrite nth_ord_enum.
Qed.

(** psl211_perdeck_raw_viewE — the raw reading is the instance's reading. *)
Lemma psl211_perdeck_raw_viewE (b : bool) (g : cutT) :
  psl211_perdeck_raw_view (psl211_alldecks_seq (b, psl211_perdeck_deal))
    (psl211_ptbl g) =
  psl211_alldecks_view psl211_perdeck_coalition (b, psl211_perdeck_deal) g.
Proof.
apply/ffunP => i.
(* in_set and not inE: inE would rewrite the seq membership on the left
   instead of the set membership on the right, leaving the two conditions
   different and the case split incomplete. *)
rewrite /psl211_perdeck_raw_view /psl211_alldecks_view !ffunE.
rewrite /psl211_perdeck_coalition in_set.
case Hi: (val i \in [:: 0; 1; 2]) => //.
rewrite /psl211_alldecks_layout tnth_mktuple.
by rewrite psl211_perdeck_ptbl_nth.
Qed.

(** psl211_perdeck_ptbl_enum — the tabulated tables are the tables of the
    group's elements, so a count over the table list is a count over the
    group. *)
Lemma psl211_perdeck_ptbl_enum :
  perm_eq [seq psl211_ptbl g | g <- enum (pgg_G psl211_M)]
    (unzip1 psl211_elem_table).
Proof.
apply: (perm_trans (perm_map psl211_ptbl psl211_perdeck_entry_perm_enum)).
rewrite -map_comp.
have Heq :
    [seq (psl211_ptbl \o psl211_entry_perm) k | k <- iota 0 660] =
    unzip1 psl211_elem_table.
  apply: (@eq_from_nth _ [::]); first by rewrite size_map size_iota
    psl211_size_keys.
  (* nth_iota and exact:, never /=: a simpl here would descend into the
     closure that psl211_elem_table is defined by. *)
  move=> k; rewrite size_map size_iota => Hk.
  rewrite (nth_map 0) ?size_iota // nth_iota //.
  exact: psl211_ptbl_entry Hk.
(* exact: perm_refl, never by: after the rewrite the goal is a perm_eq of the
   closure with itself, and done would try to decide it. *)
rewrite Heq; exact: perm_refl.
Qed.

(* Past this point no proof needs the body of the laid deck or of the
   closure table, and every step that names both chiralities must not be left
   to a tactic that searches for a match. *)
Local Opaque psl211_alldecks_view psl211_elem_table.

(** psl211_perdeck_fiber b — the cuts of the group carrying the deck of
    chirality b at psl211_perdeck_deal to psl211_perdeck_view. *)
Definition psl211_perdeck_fiber (b : bool) : {set cutT} :=
  [set g in pgg_G psl211_M |
     psl211_alldecks_view psl211_perdeck_coalition
       (b, psl211_perdeck_deal) g == psl211_perdeck_view].

(** psl211_perdeck_fiberE — that fiber has the raw count as its
    cardinality. *)
Lemma psl211_perdeck_fiberE (b : bool) :
  #|psl211_perdeck_fiber b| = psl211_perdeck_raw_count b.
Proof.
rewrite /psl211_perdeck_fiber /psl211_perdeck_raw_count.
transitivity
  (count (fun g => psl211_alldecks_view psl211_perdeck_coalition
      (b, psl211_perdeck_deal) g == psl211_perdeck_view)
    (enum (pgg_G psl211_M))).
  rewrite cardE /enum_mem size_filter count_filter.
  by apply: eq_count => g; rewrite !inE andbC.
transitivity
  (count (psl211_perdeck_test (psl211_perdeck_seq b))
    [seq psl211_ptbl g | g <- enum (pgg_G psl211_M)]).
  rewrite count_map; apply: eq_count => g.
  by rewrite -psl211_perdeck_raw_viewE psl211_perdeck_seqE psl211_perdeck_testE.
rewrite -!size_filter; apply: perm_size.
exact: (perm_filter _ psl211_perdeck_ptbl_enum).
Qed.

(** psl211_perdeck_fiber_card_neq — at one deal the two chiralities have
    different numbers of cuts producing one reading.  The symmetry the
    all-decks counting argument uses holds only in its per-cut form, which
    fixes a cut and counts deals.  The statement with the roles exchanged,
    fixing a deal and counting cuts, is false, and psl211_perdeck_deal
    witnesses it. *)
Lemma psl211_perdeck_fiber_card_neq :
  #|psl211_perdeck_fiber true| != #|psl211_perdeck_fiber false|.
Proof.
(* Each cardinality is pinned to its numeral in term mode before the two are
   brought together, so no tactic ever searches a goal in which the two
   chiralities of the same definition could be matched against each other. *)
have [Ht Hf] := psl211_perdeck_raw_countE.
have H1 : #|psl211_perdeck_fiber true| = 0 :=
  etrans (psl211_perdeck_fiberE true) Ht.
have H0 : #|psl211_perdeck_fiber false| = 1 :=
  etrans (psl211_perdeck_fiberE false) Hf.
apply/negP => /eqP Heq.
by case: (etrans (esym H1) (etrans Heq H0)).
Qed.

(* psl211_perdeck_raw_count is sealed for the rest of the file: nothing below
   needs its body, psl211_perdeck_raw_countE supplies both values, and leaving
   it transparent lets a unifier that falls back to conversion evaluate the
   count over the 660 tabulated cuts. *)
Local Opaque psl211_perdeck_raw_count.

(** psl211_perdeck_massE b — at the deal psl211_perdeck_deal, the law of what
    the coalition reads under chirality b gives psl211_perdeck_view the mass of
    its fiber of cuts over the order of the shuffle group. *)
Lemma psl211_perdeck_massE (R : realType) (b : bool) :
  (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
       (b, psl211_perdeck_deal) g)
     ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view =
  (#|pgg_G psl211_M|%:R)^-1 *+ #|psl211_perdeck_fiber b| :> R.
Proof. by rewrite /psl211_perdeck_fiber uniform_fdistmap_pointE. Qed.

(** psl211_perdeck_law_neq — at the single deal psl211_perdeck_deal the two
    chiralities send the uniform cut law to two different laws on what the
    coalition reads.  The averaged symmetry that psl211_alldecks establishes
    is therefore genuinely a statement about the average over deals: fixing
    one deal destroys it, and with it the per-deck route to privacy. *)
Lemma psl211_perdeck_law_neq (R : realType) :
  fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
      (true, psl211_perdeck_deal) g)
    ((`U psl211_G_pos) : R.-fdist cutT) !=
  fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
      (false, psl211_perdeck_deal) g)
    ((`U psl211_G_pos) : R.-fdist cutT).
Proof.
(* each mass is pinned to its value in a goal naming one chirality only, and
   the two are brought together in term mode, so no tactic ever searches a
   goal in which the two chiralities could be matched against each other *)
have [Ht Hf] := psl211_perdeck_raw_countE.
have H0 : #|psl211_perdeck_fiber true| = 0 :=
  etrans (psl211_perdeck_fiberE true) Ht.
have H1 : #|psl211_perdeck_fiber false| = 1 :=
  etrans (psl211_perdeck_fiberE false) Hf.
have Lt : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
      (true, psl211_perdeck_deal) g)
    ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view = 0 :> R.
  by rewrite psl211_perdeck_massE H0 mulr0n.
have Lf : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
      (false, psl211_perdeck_deal) g)
    ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view =
  (#|pgg_G psl211_M|%:R)^-1 :> R.
  by rewrite psl211_perdeck_massE H1 mulr1n.
apply/negP => /eqP Heq.
have Hz : (0 : R) = (#|pgg_G psl211_M|%:R)^-1 :=
  etrans (esym Lt)
    (etrans (congr1 (fun q : R.-fdist viewT => q psl211_perdeck_view) Heq) Lf).
have : (#|pgg_G psl211_M|%:R)^-1 == 0 :> R by rewrite -Hz.
rewrite invr_eq0 pnatr_eq0 => /eqP Hcard.
by move: psl211_G_pos; rewrite Hcard.
Qed.

(** psl211_perdeck_no_common_law — no law on readings is the law of the
    coalition's reading at psl211_perdeck_deal under both chiralities.  This is
    the second premise of dealer_shuffle_view_indep_of_deck written at
    PSL(2,11), for an arbitrary validity predicate that accepts that deal, and
    it has no solution, so the per-deck condition of
    dealer_shuffle_view_indep_of_deck is not available at this deal. *)
Lemma psl211_perdeck_no_common_law (R : realType)
    (valid : bool -> psl211_deal -> bool) (mu : R.-fdist viewT) :
  (forall b : bool, valid b psl211_perdeck_deal) ->
  ~ (forall (b : bool) (d : psl211_deal),
       (fdist_uniform card_bool : R.-fdist bool) b != 0 -> valid b d ->
       fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
           (b, d) g) ((`U psl211_G_pos) : R.-fdist cutT) = mu).
Proof.
move=> Hvalid Hlaw.
have Hpos : forall b : bool,
    (fdist_uniform card_bool : R.-fdist bool) b != 0.
  (* card_bool is needed: done cannot evaluate #|bool| on its own *)
  by move=> b; rewrite fdist_uniformE invr_eq0 pnatr_eq0 card_bool.
move/negP: (psl211_perdeck_law_neq R); apply; apply/eqP.
exact: etrans (Hlaw true psl211_perdeck_deal (Hpos true) (Hvalid true))
  (esym (Hlaw false psl211_perdeck_deal (Hpos false) (Hvalid false))).
Qed.

(** psl211_dealer_valid_forced — the all-decks dealer gives every deal
    positive mass, so the first premise of
    dealer_shuffle_view_indep_of_deck cannot exclude any deal: a validity
    predicate satisfying it accepts psl211_perdeck_deal at both chiralities.
    This is what stops the per-deck route from being repaired by a narrower
    notion of validity. *)
Lemma psl211_dealer_valid_forced (R : realType)
    (valid : bool -> psl211_deal -> bool) :
  (forall (b : bool) (d : psl211_deal),
     psl211_dealer_delta R b d != 0 -> valid b d) ->
  forall b : bool, valid b psl211_perdeck_deal.
Proof.
move=> Hvalid b; apply: Hvalid.
by rewrite /psl211_dealer_delta fdist_uniform_supp_neq0 inE.
Qed.

(** psl211_dealer_view_indep_of_deck_unsat — at PSL(2,11) under its own dealer
    law the two premises of dealer_shuffle_view_indep_of_deck have no common
    solution, for every validity predicate and every candidate reading law.
    So of the model's two conditions only the mixed-law condition of
    dealer_shuffle_view_indep is available to this instance, and the uniform
    law on deals meets it. *)
Lemma psl211_dealer_view_indep_of_deck_unsat (R : realType)
    (valid : bool -> psl211_deal -> bool) (mu : R.-fdist viewT) :
  (forall (b : bool) (d : psl211_deal),
     psl211_dealer_delta R b d != 0 -> valid b d) ->
  ~ (forall (b : bool) (d : psl211_deal),
       (fdist_uniform card_bool : R.-fdist bool) b != 0 -> valid b d ->
       fdistmap (psl211_dealer_view psl211_perdeck_coalition b d)
         (psl211_dealer_nu R) = mu).
Proof.
move=> Hvalid Hlaw.
apply: (@psl211_perdeck_no_common_law R valid mu
  (psl211_dealer_valid_forced Hvalid)).
exact: Hlaw.
Qed.

(** psl211_fixed_deal_delta — the degenerate dealer that lays one and the same
    deal whatever the chirality.  It is a dealer kernel in the
    sense of dealer_shuffleP, and it is named here so that the general model
    can be asked whether it claims privacy for it.  The kernel does not depend
    on the chirality at all, and what the coalition reads still does, because
    psl211_alldecks_seq reads the chirality table at the chirality: one deal
    names two different decks. *)
Definition psl211_fixed_deal_delta (R : realType) (_ : bool) :
    R.-fdist psl211_deal := fdist1 psl211_perdeck_deal.

(** psl211_fixed_dealP — the dealer law at that kernel: a uniform chirality, a
    fixed deal, a uniform cut. *)
Definition psl211_fixed_dealP (R : realType) :
    R.-fdist (bool * (psl211_deal * cutT)) :=
  @dealer_shuffleP R bool psl211_deal cutT (fdist_uniform card_bool)
    (@psl211_fixed_deal_delta R) (`U psl211_G_pos).

(** psl211_fixed_deal_view_dep — under that dealer law the reading of three
    seats is NOT independent of the chirality.  This is what entitles the
    paper to say that privacy is a property of the dealer law and not of the
    protocol alone: the shuffle group, the design and the coalition are the
    ones PSL(2,11) uses, only the dealer changed, and the conclusion fails.
    Read together with psl211_alldecks_view_indep_via_dealer it says that for
    PSL(2,11) privacy depends on which deal law the dealer uses: the uniform
    one delivers it, and the point mass at psl211_perdeck_deal does not.  What
    is NOT shown here is that a hidden uniform deal leaks: the deal is public
    in this refutation, being a point mass. *)
Lemma psl211_fixed_deal_view_dep (R : realType) :
  ~ (psl211_fixed_dealP R |=
       @dealer_shuffle_view R bool psl211_deal cutT viewT
         (fdist_uniform card_bool) (@psl211_fixed_deal_delta R)
         (`U psl211_G_pos)
         (psl211_dealer_view psl211_perdeck_coalition)
     _|_ @dealer_shuffle_secret R bool psl211_deal cutT
         (fdist_uniform card_bool) (@psl211_fixed_deal_delta R)
         (`U psl211_G_pos)).
Proof.
move=> H.
have [Ht Hf] := psl211_perdeck_raw_countE.
(* both cardinalities are pinned in term mode with the type ascribed, before
   any tactic sees a goal that spells the cardinal differently: an exact: of
   the same etrans against the goal left by rewrite -cards_eq0 makes the
   unifier fall back to conversion and re-evaluate psl211_perdeck_raw_count *)
have Hcard0 : #|psl211_perdeck_fiber true| = 0 :=
  etrans (psl211_perdeck_fiberE true) Ht.
have Hcard1 : #|psl211_perdeck_fiber false| = 1 :=
  etrans (psl211_perdeck_fiberE false) Hf.
have Hemp : psl211_perdeck_fiber true = set0.
  by apply/eqP; rewrite -cards_eq0 Hcard0.
have Hmass : forall (b : bool) (g : cutT), g \in pgg_G psl211_M ->
    0 < psl211_fixed_dealP R (b, (psl211_perdeck_deal, g)).
  move=> b g Hg; rewrite /psl211_fixed_dealP dealer_shufflePE.
  rewrite /psl211_fixed_deal_delta fdist1xx mul1r.
  rewrite (fdist_uniform_supp_in R psl211_G_pos Hg) fdist_uniformE.
  (* never // or done on a goal holding #|pgg_G psl211_M|: done would try to
     evaluate the 660-element closure and does not come back *)
  apply: mulr_gt0.
    by rewrite invr_gt0 ltr0n card_bool.
  by rewrite invr_gt0 ltr0n; exact: psl211_G_pos.
have /card_gt0P[g0 Hg0] : (0 < #|psl211_perdeck_fiber false|)%N.
  by rewrite Hcard1.
move: Hg0; rewrite inE => /andP[Hg0G /eqP Hg0v].
move: (H psl211_perdeck_view true).
(* the joint vanishes term by term: off the fixed deal the deal factor is
   zero, off the group the cut factor is zero, and on both the sample
   would put its cut in the empty true fiber *)
(* no /= and no case on a boolean numeral anywhere below: the sample carries
   psl211_perdeck_deal, whose permutations a simplification would try to
   compute, and the reading is only ever moved by conversion at an ascription
   or by a named rewrite *)
rewrite pfwd1E /Pr big1; last first.
  move=> [b [d g]]; rewrite inE => /eqP [Hv Hb].
  have Hb' : b = true := Hb.
  rewrite Hb' dealer_shufflePE /psl211_fixed_deal_delta.
  have [Hd|Hd] := eqVneq d psl211_perdeck_deal; last first.
    by rewrite (fdist10 _ Hd) mul0r mulr0.
  have [Hg|Hg] := boolP (g \in pgg_G psl211_M); last first.
    by rewrite (fdist_uniform_supp_notin R psl211_G_pos Hg) mulr0 mulr0.
  have Hin : g \in psl211_perdeck_fiber b.
    by rewrite inE Hg andTb; apply/eqP; rewrite -Hd; exact: Hv.
  by move: Hin; rewrite Hb' Hemp inE.
move/esym/eqP; rewrite mulf_eq0.
case/orP => H0; move: H0; apply/negP; apply/pfwd1_neq0.
- exists (false, (psl211_perdeck_deal, g0)); split; last by apply: Hmass.
  by rewrite inE; apply/eqP; exact: Hg0v.
- exists (true, (psl211_perdeck_deal, g0)); split; last by apply: Hmass.
  by rewrite inE; apply/eqP.
Qed.

(* Nothing after this point reasons about the reading or the counts, so the
   seals are released; Opaque is not section-scoped and would otherwise leak
   into every file that requires this one. *)
Local Transparent psl211_alldecks_view psl211_elem_table.
Local Transparent psl211_perdeck_raw_count.
