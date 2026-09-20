(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* five_card_models: the biased sample models of the five-card instance and   *)
(* the decoded colour reader                                                  *)
(*                                                                            *)
(* The five-card execution plug five_card_exec_plug carries no probability    *)
(* model. This file supplies three sample adapters over it, beside the landed *)
(* uniform one five_card_sample: one biased cut, L repeated biased cuts, and  *)
(* the concrete seven-cut model at bias 1/100. Each is identified by its cut  *)
(* distribution, so a shuffle bound stated at that distribution transfers to  *)
(* the executed run.                                                          *)
(*                                                                            *)
(* The second half reads the executed endpoints as card colours at a list of  *)
(* card positions and identifies that reader with the leakage space's partial *)
(* view ViewA, which carries Kim's input-privacy bound.                       *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   kim_single_sample     == the sample adapter whose sample space is the    *)
(*                            den Boer leakage space under Kim's biased joint *)
(*                            distribution                                    *)
(*   kim_repeated_sampleT  == the repeated-cut sample space: a committed pair *)
(*                            together with an L-letter word                  *)
(*   kim_repeated_dist     == uniform committed pairs times the weighted word *)
(*                            distribution                                    *)
(*   kim_repeated_sample   == the sample adapter whose cut is the word        *)
(*                            evaluation of the sampled word                  *)
(*   five_card_exec_colour_view == the executed endpoints decoded as colours  *)
(*                            at a list of card positions                     *)
(*   kim_centi_repeated_sample  == kim_repeated_sample at bias 1/100 and word *)
(*                            length 7                                        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   kim_single_cut_distE   == the biased model's cut distribution is the     *)
(*                             image of Kim's weight distribution under the   *)
(*                             rotation realization                           *)
(*   kim_repeated_cut_distE == the repeated model's cut distribution is the   *)
(*                             weighted word shuffle at word length L         *)
(*   kim_centi_cut_distE    == the concrete model's cut distribution is the   *)
(*                             marginal bound of the centi certificate bundle *)
(*   five_card_colour_viewE == the decoded executed colour reader agrees with *)
(*                             the leakage-space partial view ViewA           *)
(*   five_card_colour_view_RV_E == the same agreement as an equality of       *)
(*                             random variables on Kim's joint distribution   *)
(*   five_card_colour_view_leak_bound == the executed colour reader carries   *)
(*                             at most kim_leak_bound eps about the inputs    *)
(*                             given the output                               *)
(*   kim_repeated_seat_distE == the repeated model's executed seat            *)
(*                             distribution is the static pushforward         *)
(*   kim_biased_arg_cut_prodE                                                 *)
(*                          == the one-cut model's run argument and its       *)
(*                             cut have a product joint distribution          *)
(*   kim_biased_arg_cut_marginals_prodE                                       *)
(*                          == the same joint law as the product of its       *)
(*                             own two marginals                              *)
(*   kim_biased_arg_readE   == the one-cut model's run argument is the        *)
(*                             committed pair five_card_sample_arg reads      *)
(*                                                                            *)
(* Hypothesis consumption. The five-card layer carries four side conditions   *)
(* on the bias eps and one word length. Each declaration consumes a strict    *)
(* subset:                                                                    *)
(*                                                                            *)
(*   declaration                       lt   gt   spec  small  L               *)
(*   -------------------------------   ---  ---  ----  -----  ---             *)
(*   kim_weight_dist                    x    x     .     .     .              *)
(*   kim_input_dist                     x    x     .     .     .              *)
(*   kim_view / kim_inputs              x    x     .     .     .              *)
(*   kim_secret                         x    x     .     .     .              *)
(*   kim_input_private                  x    x     .     x     .              *)
(*   five_card_profile                  .    .     .     .     .              *)
(*   five_card_exec_plug                .    .     .     .     .              *)
(*   five_card_exec_colour_view         .    .     .     .     .              *)
(*   five_card_colour_view_leak_bound   x    x     .     x     .              *)
(*   kim_single_sample                  x    x     .     .     .              *)
(*   kim_repeated_sample                x    x     .     .     x              *)
(*   fc_kim_security_bundle             x    x     x     .     x              *)
(*                                                                            *)
(* Here lt is eps < 1/5, gt is -(4/5) < eps, spec is |eps| < 4/5 and small is *)
(* 0 < 1/5 - |eps|. The condition small is not implied by lt and gt: at       *)
(* eps = -1/2 both lt and gt hold while 1/5 - |eps| is negative. The program  *)
(* layer rows are empty because five_card_profile and five_card_exec_plug are *)
(* closed terms, so the executed colour reader carries no side condition and  *)
(* five_card_colour_view_leak_bound consumes exactly the three conditions of  *)
(* kim_input_private.                                                         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg matrix.
From mathcomp Require Import boolp reals.
From infotheo Require Import ssralg_ext realType_ext realType_ln fdist proba.
From infotheo Require Import variation_dist entropy.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_sample_adapter.
From pgg_smc Require Import pgg_weighted_words.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage denboer_trace.
From pgg_smc Require Import five_card_exec kim_input_privacy.
From pgg_smc Require Import pgg_analysis_status.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section five_card_sample_models.

Variable R : realType.
Variable eps : R.
Hypothesis eps_lt_inv5 : eps < 5%:R^-1.
Hypothesis eps_gt_neg4inv5 : - (4%:R * 5%:R^-1) < eps.
Variable L : nat.

Let mpF : MonodromyProfile := five_card_profile.

(******************************************************************************)
(*     The biased sample models over the five-card plug                       *)
(******************************************************************************)

(* The uniform model is the landed five_card_sample: the den Boer leakage
   space Omega under the uniform distribution P, argument the committed pair
   and cut the sampled rotation. Its cut distribution is
   five_card_sample_cut_distE, and the same distribution read as the den Boer
   member's marginal bound is den_boer_sample_cut_witnessE. Neither is restated
   here. *)

(** kim_single_sample — the sample layer over five_card_exec_plug whose sample
    space is the den Boer leakage space Omega under Kim's biased joint
    distribution kim_input_dist, with the committed pair as run argument and
    the realized rotation as cut. Its carrier and both maps are exactly those
    of five_card_sample; only the distribution differs, so results proved
    generically for the sample-adapter shape transfer here unchanged. *)
Definition kim_single_sample : SampleAdapter R five_card_exec_plug :=
  @MkSampleAdapter R mpF five_card_exec_plug
    five_card_leakage.Omega (kim_input_dist eps_lt_inv5 eps_gt_neg4inv5)
    five_card_sample_arg five_card_sample_cut.

(** kim_repeated_sampleT — the repeated-cut sample space: a committed pair of
    bits together with an L-letter word over the five rotation generators. *)
Definition kim_repeated_sampleT : finType :=
  [the finType of ((bool * bool) * (L.-tuple 'I_5))%type].

(** kim_repeated_dist — the repeated-cut distribution: the product of the
    uniform distribution on committed pairs with the weighted word
    distribution built from Kim's generator weights. *)
Definition kim_repeated_dist : R.-fdist kim_repeated_sampleT :=
  ((fdist_uniform card_bool2)
   `x (@word_weighted R 4 L
         (kim_weight_dist eps_lt_inv5 eps_gt_neg4inv5)))%fdist.

(** kim_repeated_sample — the L-repeated-biased-cut model: the sample layer
    over five_card_exec_plug whose sample space is kim_repeated_sampleT under
    kim_repeated_dist, with the committed pair as run argument and the word
    evaluation of the sampled word as cut. *)
Definition kim_repeated_sample : SampleAdapter R five_card_exec_plug :=
  @MkSampleAdapter R mpF five_card_exec_plug
    kim_repeated_sampleT kim_repeated_dist
    (fun u => u.1) (fun u => @word_eval FiveCardKim_M L u.2).

(******************************************************************************)
(*     The cut distributions of the models                                    *)
(******************************************************************************)

(** kim_single_snd_weightE — the rotation marginal of Kim's joint distribution
    kim_input_dist equals Kim's weight distribution kim_weight_dist outright.
    This is the algebraic identity kim_single_cut_distE composes with
    fdistmap_comp to identify the one-biased-cut model's cut distribution. *)
Lemma kim_single_snd_weightE :
  fdistmap (fun u : five_card_leakage.Omega => u.2)
    (kim_input_dist eps_lt_inv5 eps_gt_neg4inv5)
  = kim_weight_dist eps_lt_inv5 eps_gt_neg4inv5.
Proof.
by rewrite /kim_input_dist -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

(** kim_single_cut_distE — the one-biased-cut model's cut distribution
    sa_cut_dist kim_single_sample is the image of Kim's weight distribution
    kim_weight_dist under the rotation realization k |-> fc_sigma^k. This
    identifies the model inside the shared cut-distribution machinery, so a
    shuffle bound proved generically at kim_weight_dist transfers to
    kim_single_sample with no restatement. *)
Lemma kim_single_cut_distE :
  sa_cut_dist kim_single_sample
  = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
      (kim_weight_dist eps_lt_inv5 eps_gt_neg4inv5).
Proof.
rewrite /sa_cut_dist /kim_single_sample /= /five_card_sample_cut.
by rewrite -kim_single_snd_weightE fdistmap_comp.
Qed.

(** kim_repeated_snd_wordE — the word marginal of kim_repeated_dist equals the
    weighted word distribution word_weighted built from kim_weight_dist
    outright. This is the identity kim_repeated_cut_distE composes with
    fdistmap_comp to identify the repeated model's cut distribution. *)
Lemma kim_repeated_snd_wordE :
  fdistmap (fun u : kim_repeated_sampleT => u.2) kim_repeated_dist
  = @word_weighted R 4 L (kim_weight_dist eps_lt_inv5 eps_gt_neg4inv5).
Proof.
by rewrite /kim_repeated_dist -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

(** kim_repeated_cut_distE — the repeated model's cut distribution
    sa_cut_dist kim_repeated_sample is the weighted word shuffle
    rho_from_words_weighted at word length L over Kim's generator weights.
    This lets a shuffle bound proved at the weighted-word level transfer to
    the L-repeated-cut model. *)
Lemma kim_repeated_cut_distE :
  sa_cut_dist kim_repeated_sample
  = @rho_from_words_weighted R 3 4 L fc_kim_gens
      (kim_weight_dist eps_lt_inv5 eps_gt_neg4inv5).
Proof.
rewrite /sa_cut_dist /kim_repeated_sample /= /rho_from_words_weighted.
by rewrite -kim_repeated_snd_wordE fdistmap_comp.
Qed.

(******************************************************************************)
(*     The executed seat distribution of the repeated model                   *)
(******************************************************************************)

(** kim_repeated_seat_distE — the repeated model's executed seat distribution
    at round 0 and seat i is the fdistmap pushforward of the static seat
    observation five_card_content_obs along kim_repeated_dist. This licenses
    reading the executed run's per-seat marginal directly off the sample
    layer's own distribution, with no separate execution-side argument. *)
Lemma kim_repeated_seat_distE (i : 'I_(pi_T' (mp_PI mpF)).+1) :
  @sa_seat_dist R mpF five_card_exec_plug kim_repeated_sample 0 i
  = fdistmap (@sa_static_seat_view R mpF five_card_exec_plug
                kim_repeated_sample five_card_content_obs i) kim_repeated_dist.
Proof.
(* The endpoint hypothesis of the generic sa_seat_distE is discharged by
   five_card_exec_endpoints, which quantifies over every cut and so applies
   at the word-evaluation cut. *)
by apply: sa_seat_distE => -[[a b] v]; exact: five_card_exec_endpoints.
Qed.

(******************************************************************************)
(*     The decoded colour reader of the executed endpoints                    *)
(******************************************************************************)

(** five_card_layout_colourE — the dealt layout entry den_boer_layout (a, b)
    at the monodromy image of seat i's start decodes (decode_bool) to the
    colour the leakage space's arr reads at seat i, for the rotation cut
    fc_sigma^+k. This is the per-position bridge fact
    five_card_endpoint_colourE assembles across every seat to identify the
    executed colour reader with the leakage space's own colour array. *)
Lemma five_card_layout_colourE (a b : bool) (k : 'I_5) (i : 'I_5) :
  decode_bool (tnth (den_boer_layout (a, b))
    (@pgg_rho FiveCardKim_M (five_card_group.fc_sigma ^+ k)%g
       (tnth (pi_starts FiveCardKim_PI) i)))
  = nth false (five_card_leakage.arr (a, b, k)) i.
Proof.
(* Cut is oriented as fc_sigma^+k: denboer_player_trace_shape and
   denboer_player_trace_ok tie the executed layout entry at that cut to
   nth false (arr w) i. *)
rewrite -(denboer_player_trace_shape R a b k i).
rewrite denboer_player_trace_ok /comp_RV decode_encode_bool.
by rewrite /ViewA /thead tnth_map (tnth_nth 0%N).
Qed.

(** five_card_decode_ord0 — the card position ord0 decodes (decode_bool) to
    false, the club colour. This is the value the executed colour reader
    returns at a position outside the five dealt cards, and it is exactly the
    default false ViewA returns there, so the two readers agree on
    out-of-range positions with no separate case. *)
Lemma five_card_decode_ord0 : decode_bool ord0 = false.
(* Not closed by computation: decode_bool compares against inord 1, whose
   reduction is blocked by the opaque idP, so the value is read off through
   inordK instead. *)
Proof. by rewrite /decode_bool -(inj_eq val_inj) /= inordK. Qed.

(** five_card_exec_colour_view — the executed endpoints, decoded (decode_bool)
    as colours at a list of card positions A: the tuple, in the order and
    with the multiplicity of A, of decode_bool applied to exec_endpoints's
    entries, defaulting to card position ord0, hence colour false, outside
    the five dealt cards. This is the executed-side reader
    five_card_colour_viewE identifies with the leakage space's own view
    ViewA. *)
Definition five_card_exec_colour_view (A : seq nat) (ab : bool * bool)
    (w0 : pgg_gT FiveCardKim_M) : (size A).-tuple bool :=
  map_tuple (fun j => decode_bool
    (nth ord0 (@exec_endpoints mpF five_card_exec_plug ab w0 0) j))
    (in_tuple A).

(** five_card_endpoint_colourE — the decoded executed endpoint at any card
    position j equals the colour the leakage space's arr reads at j, for
    every leakage outcome w. This is the per-position agreement
    five_card_colour_viewE assembles into the whole-tuple identification of
    the executed colour reader with ViewA. *)
Lemma five_card_endpoint_colourE (w : five_card_leakage.Omega) (j : nat) :
  decode_bool (nth ord0 (@exec_endpoints mpF five_card_exec_plug
                  w.1 (five_card_group.fc_sigma ^+ w.2)%g 0) j)
  = nth false (five_card_leakage.arr w) j.
Proof.
(* Positions below five go through five_card_exec_seat_endpointE and
   five_card_layout_colourE; positions from five on are the two default
   values, ord0 on the executed side and false on the leakage side. *)
case: w => -[a b] k /=.
have [Hj|Hj] := ltnP j 5.
  have -> : nth ord0 (@exec_endpoints mpF five_card_exec_plug
      (a, b) (five_card_group.fc_sigma ^+ k)%g 0) j
    = @exec_seat_endpoint mpF five_card_exec_plug
        (a, b) (five_card_group.fc_sigma ^+ k)%g 0 (Ordinal Hj) by [].
  rewrite five_card_exec_seat_endpointE /five_card_content_obs.
  exact: five_card_layout_colourE.
have Hsz : size (@exec_endpoints mpF five_card_exec_plug (a, b)
                   (five_card_group.fc_sigma ^+ k)%g 0) = 5.
  exact: (exec_endpoints_size (five_card_exec_endpoints a b _)).
rewrite [in RHS]nth_default;
  last by rewrite /fc_shuffle size_rot fc_arrange_size.
rewrite nth_default; last by rewrite Hsz.
exact: five_card_decode_ord0.
Qed.

(** five_card_colour_viewE — the executed colour reader
    five_card_exec_colour_view, evaluated at the rotation cut fc_sigma^+w.2,
    equals the leakage space's own partial view ViewA, for every position
    list A and every leakage outcome w. This is the identification that lets
    Kim's input-privacy bound, proved against ViewA, be read directly off the
    executed run. *)
Lemma five_card_colour_viewE (A : seq nat) (w : five_card_leakage.Omega) :
  five_card_exec_colour_view A w.1 (five_card_group.fc_sigma ^+ w.2)%g
  = ViewA R A w.
Proof.
apply: val_inj => /=.
by apply: eq_map => j; exact: five_card_endpoint_colourE.
Qed.

(** five_card_colour_view_RV_E — the executed colour reader, read as a
    function of the leakage outcome, is exactly Kim's view random variable
    kim_view A on Omega. This upgrades the pointwise agreement
    five_card_colour_viewE to an equality of random variables, the form the
    conditional-mutual-information bound below needs. *)
Lemma five_card_colour_view_RV_E (A : seq nat) :
  (fun w : five_card_leakage.Omega =>
     five_card_exec_colour_view A w.1 (five_card_group.fc_sigma ^+ w.2)%g)
  = kim_view eps_lt_inv5 eps_gt_neg4inv5 A
    :> (five_card_leakage.Omega -> (size A).-tuple bool).
Proof. by apply: funext => w; rewrite five_card_colour_viewE. Qed.

(******************************************************************************)
(*     Kim's input-privacy bound at the executed colour reader                *)
(******************************************************************************)

Section five_card_input_privacy_transport.

Hypothesis eps_small : 0 < 5%:R^-1 - `|eps|.

(** five_card_colour_view_leak_bound — the conditional mutual information
    between the inputs, the executed colour reader at position list A, and
    the secret, is at most kim_leak_bound eps. This transports Kim's abstract
    input-privacy bound kim_input_private to the executed run via the
    random-variable identification five_card_colour_view_RV_E, with no
    separate execution-side security argument. *)
Corollary five_card_colour_view_leak_bound (A : seq nat) :
  cond_mutual_info (`p_ [% kim_inputs eps_lt_inv5 eps_gt_neg4inv5,
    (fun w : five_card_leakage.Omega =>
       five_card_exec_colour_view A w.1 (five_card_group.fc_sigma ^+ w.2)%g),
    kim_secret eps_lt_inv5 eps_gt_neg4inv5]) <= kim_leak_bound eps.
Proof. by rewrite five_card_colour_view_RV_E; exact: kim_input_private. Qed.

End five_card_input_privacy_transport.

End five_card_sample_models.

(******************************************************************************)
(*     The concrete seven-cut model at bias 1/100                             *)
(******************************************************************************)

Section five_card_centi_model.

Variable R : realType.

(** kim_centi_repeated_sample — the concrete seven-cut model:
    kim_repeated_sample instantiated at bias 1/100, Kim's centi side-condition
    pack (kim_centi_lt, kim_centi_gt), and word length 7. *)
Definition kim_centi_repeated_sample :=
  @kim_repeated_sample R (1 / 100) (kim_centi_lt R) (kim_centi_gt R) 7.

(** kim_centi_witness_rhoE — the centi certificate bundle's marginal-bound
    distribution sw_rho_dist equals the weighted word shuffle
    rho_from_words_weighted at word length 7 outright, by computation. This
    is the identity kim_centi_cut_distE composes with kim_repeated_cut_distE
    to identify the concrete model's cut distribution with the certificate
    bundle's own bound. *)
Lemma kim_centi_witness_rhoE :
  sw_rho_dist (scb_bound (kim_security_bundle_centi R))
  = @rho_from_words_weighted R 3 4 7 fc_kim_gens
      (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R)).
Proof. by []. Qed.

(** kim_centi_cut_distE — the concrete seven-cut model's cut distribution
    sa_cut_dist kim_centi_repeated_sample is exactly the marginal bound
    sw_rho_dist carried by the centi security-certificate bundle. This lets
    the certificate bundle's shuffle security be read off the concrete model
    directly, with no separate marginal computation. *)
Lemma kim_centi_cut_distE :
  sa_cut_dist kim_centi_repeated_sample
  = sw_rho_dist (scb_bound (kim_security_bundle_centi R)).
Proof.
by rewrite kim_centi_witness_rhoE /kim_centi_repeated_sample
   kim_repeated_cut_distE.
Qed.

(** kim_centi_repeated_seat_distE — the concrete seven-cut model's executed
    seat distribution is the pushforward of the static observation:
    kim_repeated_seat_distE instantiated at bias 1/100 and word length 7. *)
Definition kim_centi_repeated_seat_distE :=
  @kim_repeated_seat_distE R (1 / 100) (kim_centi_lt R) (kim_centi_gt R) 7.

End five_card_centi_model.

(******************************************************************************)
(*     The typed model families of the five-card analysis paths               *)
(******************************************************************************)

(** five_card_uniform_family — the uniform rotation model as a unit-indexed
    AnalysisModelFamily over five_card_observed, whose sole member at every
    real field R is five_card_sample R. This is the baseline model the
    analysis paths compare Kim's biased families against. *)
Definition five_card_uniform_family
    : AnalysisModelFamily five_card_observed :=
  @MkAnalysisModelFamily five_card_observed (fun _ => unit)
    (fun R _ => five_card_sample R).

(** kim_biased_family — the single biased cut at bias 1/100 as a unit-indexed
    AnalysisModelFamily over five_card_observed, whose sole member at every
    real field R is kim_single_sample R at that bias, with its two side
    conditions discharged by kim_centi_lt and kim_centi_gt. *)
Definition kim_biased_family : AnalysisModelFamily five_card_observed :=
  @MkAnalysisModelFamily five_card_observed (fun _ => unit)
    (fun R _ => @kim_single_sample R (1 / 100)
                  (kim_centi_lt R) (kim_centi_gt R)).

(** kim_centi_family — the seven-cut repeated model at bias 1/100 as a
    unit-indexed AnalysisModelFamily over five_card_observed, whose sole
    member at every real field R is kim_centi_repeated_sample R. *)
Definition kim_centi_family : AnalysisModelFamily five_card_observed :=
  @MkAnalysisModelFamily five_card_observed (fun _ => unit)
    (fun R _ => kim_centi_repeated_sample R).

(******************************************************************************)
(*     The one-cut model draws its cut apart from its run argument            *)
(******************************************************************************)

(** The one-cut model's run argument and its cut have a product joint
    distribution: the committed pair drawn uniformly, and the rotation drawn
    from Kim's biased weight and realised in the group.
    kim_biased_arg_cut_marginals_prodE writes the same joint law with the
    model's own two marginals, which is the shape a construction of
    ideal-proximity evidence from an input-indistinguishability certificate
    asks a model for. *)
Lemma kim_biased_arg_cut_prodE (R : realType) (idx : unit) :
  fdistmap (fun u => (@sa_arg _ _ _ (amf_sample kim_biased_family R idx) u,
                      @sa_cut _ _ _ (amf_sample kim_biased_family R idx) u))
    (sa_sampleP (amf_sample kim_biased_family R idx))
  = (fdist_uniform card_bool2)
    `x (fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g)
          (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R))).
Proof. exact: fdistmap_prodr. Qed.

(** The one-cut model's joint law of the finite coordinate
    five_card_sample_arg takes off the sample point and its cut is the
    product of that law's own two marginals. It is the product hypothesis a
    construction of ideal-proximity evidence from an
    input-indistinguishability certificate places on a model, written at this
    model: the first factor is the uniform law on committed pairs by
    fdist_prod1 and the second is the rotation law by kim_single_cut_distE. *)
Lemma kim_biased_arg_cut_marginals_prodE (R : realType) (idx : unit) :
  fdistmap (fun u : five_card_leakage.Omega =>
              (five_card_sample_arg u,
               @sa_cut _ _ _ (amf_sample kim_biased_family R idx) u))
    (sa_sampleP (amf_sample kim_biased_family R idx))
  = (fdistmap (fun u : five_card_leakage.Omega => five_card_sample_arg u)
       (sa_sampleP (amf_sample kim_biased_family R idx)))
    `x (sa_cut_dist (amf_sample kim_biased_family R idx)).
Proof.
have Hfst : fdistmap (fun u : five_card_leakage.Omega => five_card_sample_arg u)
    (sa_sampleP (amf_sample kim_biased_family R idx))
  = fdist_uniform card_bool2.
  transitivity (fdistmap fst
    (fdistmap (fun u : five_card_leakage.Omega =>
       (five_card_sample_arg u,
        @sa_cut _ _ _ (amf_sample kim_biased_family R idx) u))
       (sa_sampleP (amf_sample kim_biased_family R idx)))).
    by rewrite fdistmap_comp.
  by rewrite (@kim_biased_arg_cut_prodE R idx) -/(fdist_fst _) fdist_prod1.
have Hsnd : sa_cut_dist (amf_sample kim_biased_family R idx)
  = fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g)
      (kim_weight_dist (kim_centi_lt R) (kim_centi_gt R))
  by exact: kim_single_cut_distE.
rewrite Hfst Hsnd.
exact: kim_biased_arg_cut_prodE.
Qed.

(** The one-cut model's run argument is the committed pair of bits that
    five_card_sample_arg reads off the sample point. A construction over a
    finite coordinate of the sample point asks for a decoding of that
    coordinate back into the run-argument carrier; here that coordinate is
    the run argument itself and the decoding is the identity. *)
Lemma kim_biased_arg_readE (R : realType) (idx : unit)
    (u : five_card_leakage.Omega) :
  @sa_arg _ _ _ (amf_sample kim_biased_family R idx) u = five_card_sample_arg u.
Proof. exact: erefl. Qed.
