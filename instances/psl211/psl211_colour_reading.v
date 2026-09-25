(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_colour_reading: a coalition's colour reading at the twelve-card     *)
(*                        chirality instance, and the card-identity reading   *)
(*                        beside it                                           *)
(*                                                                            *)
(* The colour theorems of instances/psl211/psl211_secrecy.v are read in       *)
(* psl211P, the law of a chirality bit drawn from a prior together with an    *)
(* independent uniform PSL(2,11) shuffle. A proposition of the Verifolio is     *)
(* stated at a sample adapter and at a reading. The adapter over that law is  *)
(* psl211_dealt_sample of instances/psl211/psl211_dealt_model.v, over the     *)
(* dealer-dealt run parameters, whose run argument carrier is the chirality   *)
(* itself. What this file supplies is the reading: the colour reading, which  *)
(* gives each position of a coalition the colour of the card the encoder      *)
(* deck of that chirality puts at the cut image of that position.             *)
(*                                                                            *)
(* Two readings of one model are separated here. The colour reading is a      *)
(* non-injective function of the coalition's card-identity reading, so the    *)
(* post-processing law carries a number from the second to the first and not  *)
(* back. Below the threshold of six positions the colour reading is exactly   *)
(* independent of the chirality and at six it is not, while the               *)
(* card-identity reading is already dependent at one coalition of three       *)
(* positions. A proposition stated at a reading therefore has an instance     *)
(* here that is not the framework's own reading under a second name.          *)
(*                                                                            *)
(* The dealer-dealt parameters read their endpoints through                   *)
(* profile_endpointsE, as instances/psl211/psl211_endpoints.v states, so      *)
(* psl211_models.v carries an endpoints statement and an observed execution   *)
(* for them and instances/psl211/verifolio/psl211_verifolio_dealt.v carries the   *)
(* Sampled level and the two programs over them. Every statement in this      *)
(* file is about the model's law and a reading of a coalition's endpoints,    *)
(* and the identification of that reading with the executed one is the link   *)
(* lemma the Sampled level of that file proves.                               *)
(*                                                                            *)
(* The model itself is not built here. The sample adapter                     *)
(* psl211_dealt_sample, the colour map psl211_colour_of_reading and the two   *)
(* theorems the analysis manifest's dealer-dealt paths name are stated in     *)
(* instances/psl211/psl211_dealt_model.v, below the analysis manifest,        *)
(* because a theorem a manifest path names has to be reachable from the       *)
(* facade. What is here is the reading record those results are read at and   *)
(* the statements that need it.                                               *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_colour_reading     == the colour of the card at each position of  *)
(*                                a coalition, as a reading of its endpoints  *)
(*   psl211_dealt_perdeck_reading                                             *)
(*                             == the card-identity reading of three named    *)
(*                                positions, as a random variable             *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_colour_readingE    == the model's colour view is the reading's    *)
(*                                value at that sample point                  *)
(*   psl211_colour_reading_funE                                               *)
(*                             == the same with the sample point left free    *)
(*   psl211_colour_indistinguishability_of_coalition_reading                  *)
(*                             == the post-processing law at that             *)
(*                                factorisation                               *)
(*   psl211_colour_reading_indep                                              *)
(*                             == below the threshold the colour reading is   *)
(*                                independent of the chirality                *)
(*   psl211_leak_coalition_not_below_k                                        *)
(*                             == the six-position coalition is not below     *)
(*                                the threshold                               *)
(*   psl211_colour_reading_dep_k6                                             *)
(*                             == at that coalition the colour reading is     *)
(*                                not independent of the chirality            *)
(*   psl211_dealt_perdeck_readingE                                            *)
(*                             == the card-identity reading over this         *)
(*                                adapter, the sample point left free         *)
(*   psl211_dealt_reading_indep_false                                         *)
(*                             == at three positions the card-identity        *)
(*                                reading is not independent of it            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_reconstruct Require Import transitivity_privacy design_privacy.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_secrecy.
From pgg_smc Require Import psl211_models psl211_dealt_model.
From pgg_smc Require Import psl211_reading_constancy.
From pgg_smc Require Import pgg_verifolio pgg_verifolio_reading.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Notation seats :=
  'I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1.
Local Notation cards :=
  'I_(pgg_N' (mp_M (instance_profile psl211_algebra))).+1.
Local Notation cutT := (pgg_gT (mp_M (instance_profile psl211_algebra))).


(******************************************************************************)
(*     The colour view as a reading of a coalition's endpoints                *)
(******************************************************************************)

(** psl211_colour_reading — the colour a coalition sees at each of its
    positions, as a reading of that coalition's endpoints: keep the colour of
    the card each position holds and discard its identity, and return false
    outside the coalition.  It is a function of the endpoints alone, which is
    what makes the colour view a reading of this record and not a second
    kind of thing; the identification with the model's colour view is
    psl211_colour_readingE below.  It is a function of the coalition as well
    as of the endpoint map, because a coalition's endpoints give card zero
    outside the coalition and card zero is a heart. *)
Definition psl211_colour_reading : CoalitionReading psl211_algebra :=
  @MkCoalitionReading psl211_algebra
    (fun _ => [the finType of {ffun seats -> bool}])
    psl211_colour_of_reading.

(** psl211_colour_readingE — the model's colour view of a sample point is what
    the colour reading grants the coalition of that point's endpoints. It is
    where the instance's seat reconciliation is used: the colour view is
    written at the position index the model uses and a coalition's endpoints
    index through pi_starts, and psl211_colour_of_reading_obsE is what
    identifies the two. *)
Lemma psl211_colour_readingE (R : realType) (secretP : R.-fdist bool)
    (C : {set seats}) (u : bool * pgg_gT psl211_M) :
  psl211_colour_view secretP C u
  = cr_read psl211_colour_reading C
      (static_coalition_obs C ((psl211_dealt_sample secretP).(sa_arg) u)
         ((psl211_dealt_sample secretP).(sa_cut) u)).
(* The reading record's read function is psl211_colour_of_reading by one iota
   step, so the raw identification is this one at a fixed sample point. *)
Proof.
exact: (congr1 (fun f => f u) (psl211_dealt_colour_viewE secretP C)).
Qed.

(** psl211_colour_reading_funE — the same identification with the sample point
    left free. A proposition stated at a reading pushes the reading forward
    along the model's law, so it needs the reading as one function and not as
    its values. *)
Lemma psl211_colour_reading_funE (R : realType) (secretP : R.-fdist bool)
    (C : {set seats}) :
  psl211_colour_view secretP C
  = (fun u => cr_read psl211_colour_reading C
                (static_coalition_obs C
                   ((psl211_dealt_sample secretP).(sa_arg) u)
                   ((psl211_dealt_sample secretP).(sa_cut) u))).
Proof. exact: psl211_dealt_colour_viewE. Qed.


(******************************************************************************)
(*     What travels from the endpoint reading to the colour reading           *)
(******************************************************************************)

(** psl211_colour_indistinguishability_of_coalition_reading — the framework's
    post-processing law discharged at this pair of readings: an
    input-indistinguishability proposition at the coalition's card-identity
    reading gives the same number at the colour reading. The factorisation it
    consumes holds by conversion, psl211_colour_of_reading being the read
    function of the colour reading itself. That map is not injective, so this is
    the data processing inequality applied at a genuine coarsening and not at a
    renaming. It transports a bound and produces none. At zero the card-identity
    reading has no such proposition over this adapter, by
    psl211_dealt_constancy_false of instances/psl211/psl211_reading_constancy.v;
    at a positive number none is proved and none is refuted. *)
Lemma psl211_colour_indistinguishability_of_coalition_reading (R : realType)
    (secretP : R.-fdist bool) (c : R) :
  ReadingIndistinguishabilityPropAt (psl211_dealt_sample secretP)
    (coalition_endpoint_reading psl211_algebra) c ->
  ReadingIndistinguishabilityPropAt (psl211_dealt_sample secretP)
    psl211_colour_reading c.
Proof.
(* the reading arguments and the factorisation are positional on the
   framework's law, only its carrier arguments being implicit *)
exact: (reading_indistinguishability_postprocessing
          (coalition_endpoint_reading psl211_algebra) psl211_colour_reading
          psl211_colour_of_reading
          (fun C v => erefl) c).
Qed.

(******************************************************************************)
(*     Exact independence at the colour reading, and the sharp threshold      *)
(******************************************************************************)

(** psl211_colour_reading_indep — below the framework's privacy threshold the
    colour reading's value is independent of the dealt chirality, under every
    prior on the chirality. It is psl211_colour_view_indep of
    instances/psl211/psl211_secrecy.v stated at the colour reading over this
    adapter. The thresholds meet on the nose, the instance's counting argument
    reaching five of the twelve positions and the derived profile declaring
    six. The statement is an independence and not a numeric bound, and no
    entropy form of the framework is restated at it. It is stated of the
    model's law and the colour reading of a coalition's endpoints; the
    program of instances/psl211/verifolio/psl211_verifolio_dealt.v carries it to
    the executed run along the link lemma of the Sampled level. *)
Lemma psl211_colour_reading_indep (R : realType) (secretP : R.-fdist bool) :
  ReadingExactIndependence (psl211_dealt_sample secretP) psl211_colour_reading
    (psl211_secret secretP).
(* The proposition is the raw theorem with the reading record's read function
   in place of psl211_colour_of_reading, one iota step apart. *)
Proof. exact: psl211_dealt_colour_indep. Qed.

(** psl211_leak_coalition_not_below_k — the six positions of the mirror
    representative are not below the framework's threshold, so the coalition
    at which the next lemma refutes independence is outside the range
    psl211_colour_reading_indep covers. Without this the two statements would
    contradict each other rather than bound each other. *)
Lemma psl211_leak_coalition_not_below_k :
  ~~ (#|psl211_leak_coalition| < profile_k (instance_profile psl211_algebra))%N.
Proof. by rewrite psl211_leak_coalition_card6 profile_k_psl211_algebra. Qed.

(** psl211_colour_reading_dep_k6 — at the six positions of the mirror
    representative, and at a prior giving mass to both chiralities, the colour
    reading's value is not independent of the dealt chirality; that coalition
    has exactly as many positions as the framework's threshold declares. It is
    psl211_colour_view_dep_k6 stated at the colour reading. Together with
    psl211_colour_reading_indep it says that the threshold of the proposition
    at this reading is the largest one: one position past it, independence
    already fails, and it fails at a coalition that is a block of one of the
    two Steiner systems. The two positivity premises are part of the
    mathematics: at a prior supported on one chirality the secret is almost
    surely constant and every reading is independent of it. *)
Lemma psl211_colour_reading_dep_k6 (R : realType) (secretP : R.-fdist bool) :
  secretP true != 0 -> secretP false != 0 ->
  (#|psl211_leak_coalition| = profile_k (instance_profile psl211_algebra))%N /\
  ~ sa_sampleP (psl211_dealt_sample secretP)
      |= (fun u => cr_read psl211_colour_reading psl211_leak_coalition
                     (@static_coalition_obs psl211_algebra
                        psl211_dealt_params psl211_leak_coalition
                        ((psl211_dealt_sample secretP).(sa_arg) u)
                        ((psl211_dealt_sample secretP).(sa_cut) u)))
         _|_ psl211_secret secretP.
Proof.
move=> Ht Hf; have [Hcard Hdep] := psl211_colour_view_dep_k6 secretP Ht Hf.
split; first by rewrite Hcard profile_k_psl211_algebra.
by rewrite -psl211_colour_reading_funE; exact: Hdep.
Qed.


(******************************************************************************)
(*     The card-identity reading is not independent of the chirality          *)
(******************************************************************************)

(** psl211_dealt_perdeck_reading — the coalition's card-identity reading at
    the three positions zero, one and two, as a random variable of the
    fixed-dealer colour model. The coalition is the one the instance's
    constancy counterexample already uses, and three is below the threshold of
    six. *)
Definition psl211_dealt_perdeck_reading (R : realType) (secretP : R.-fdist bool)
  : {RV (psl211P secretP) -> {ffun seats -> cards}} :=
  fun u => @static_coalition_obs psl211_algebra psl211_dealt_params
             psl211_perdeck_coalition u.1 u.2.

(** psl211_dealt_perdeck_readingE — the coalition's card-identity reading over
    this adapter is the card-identity reading of the sample point's two
    coordinates. One iota step of the reading record and two of the adapter
    record. *)
Lemma psl211_dealt_perdeck_readingE (R : realType) (secretP : R.-fdist bool) :
  (fun u => @cr_read psl211_algebra
              (coalition_endpoint_reading psl211_algebra)
              psl211_perdeck_coalition
              (static_coalition_obs psl211_perdeck_coalition
                 ((psl211_dealt_sample secretP).(sa_arg) u)
                 ((psl211_dealt_sample secretP).(sa_cut) u)))
  = psl211_dealt_perdeck_reading secretP.
Proof. by []. Qed.

(** psl211_dealt_reading_indep_false — over the same model, the same adapter
    and at a coalition of three of the twelve positions, the coalition's
    card-identity reading is not independent of the dealt chirality, under
    every prior giving mass to both chiralities. Three is below the threshold
    of six, so this is a coalition psl211_colour_reading_indep covers: at one
    model and one coalition the proposition holds at the colour reading and
    fails at the card-identity one, so the colour reading's exact independence
    is not the image of the card-identity reading's, that one being false.
    What separates them is the card identity: the encoder decks of the two
    chiralities put one reading of three positions under exactly one cut and
    under none, which is psl211_dealt_raw_countE, while their colour patterns
    on five positions or fewer are equidistributed. It is the probabilistic
    form of psl211_dealt_constancy_false of
    instances/psl211/psl211_reading_constancy.v: the same coalition, the same
    fibers and the same two counts, a mass equality there and an independence
    here. It is stated of the model's law and the coalition's own endpoint
    reading, and it is why exact independence at the colour reading does not
    carry back to the endpoint reading. *)
Lemma psl211_dealt_reading_indep_false (R : realType)
    (secretP : R.-fdist bool) :
  secretP true != 0 -> secretP false != 0 ->
  ~ ReadingExactIndependence (psl211_dealt_sample secretP)
      (coalition_endpoint_reading psl211_algebra) (psl211_secret secretP).
Proof.
move=> Ht Hf Hind.
have Hmass (b : bool) (g : pgg_gT psl211_M) :
    secretP b != 0 -> g \in pgg_G psl211_M -> 0 < psl211P secretP (b, g).
  move=> Hb gG; rewrite /psl211P fdist_prodE /=; apply: mulr_gt0.
    by rewrite lt0r Hb FDist.ge0.
  rewrite (@fdist_uniform_supp_in R _ (pgg_G psl211_M) psl211_G_pos g gG).
  by rewrite invr_gt0 ltr0n; exact: psl211_G_pos.
have [Htc Hfc] := psl211_dealt_raw_countE.
have Hempty : psl211_dealt_fiber true = set0.
  by apply/cards0_eq; rewrite psl211_dealt_fiberE Htc.
have [g0 Hg0] : exists g0, g0 \in psl211_dealt_fiber false.
  by apply/card_gt0P; rewrite psl211_dealt_fiberE Hfc.
move: Hg0; rewrite inE => /andP[g0G /eqP Hg0v].
have HV : 0 < `Pr[ (psl211_dealt_perdeck_reading secretP)
                   = psl211_dealt_view ].
  rewrite lt0r pfwd1_ge0 andbT.
  apply/pfwd1_neq0; exists (false, g0); split;
    last exact: Hmass false g0 Hf g0G.
  by rewrite inE /=; apply/eqP; exact: Hg0v.
have HS : 0 < `Pr[ (psl211_secret secretP) = true ].
  rewrite lt0r pfwd1_ge0 andbT.
  apply/pfwd1_neq0; exists (true, 1%g); split;
    last exact: Hmass true 1%g Ht (group1 _).
  by rewrite inE.
have Hzero : `Pr[ [% psl211_dealt_perdeck_reading secretP,
                     psl211_secret secretP] = (psl211_dealt_view, true) ] = 0.
  apply/eqP; apply/negPn; apply/negP => /pfwd1_neq0 [[s g] [Hmem Hpos]].
  have gG : g \in pgg_G psl211_M.
    apply: contraLR Hpos => gN.
    rewrite /psl211P fdist_prodE /=
      (@fdist_uniform_supp_notin R _ (pgg_G psl211_M) psl211_G_pos g gN) mulr0.
    by apply/negP => /lt0r_neq0; rewrite eqxx.
  move: Hmem; rewrite inE /= xpair_eqE => /andP[/eqP Hv /eqP Hs].
  have Hs' : s = true by exact: Hs.
  have : g \in psl211_dealt_fiber true.
    by rewrite inE gG /=; apply/eqP; rewrite -Hs'; exact: Hv.
  by rewrite Hempty inE.
move: (Hind psl211_perdeck_coalition psl211_perdeck_coalition_below_k).
rewrite psl211_dealt_perdeck_readingE => Hcan.
move: (mulr_gt0 HV HS); rewrite -(Hcan psl211_dealt_view true) Hzero.
by move/lt0r_neq0; rewrite eqxx.
Qed.
