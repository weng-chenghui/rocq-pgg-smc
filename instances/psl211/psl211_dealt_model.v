(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_dealt_model: the dealer-dealt model of the twelve-card chirality    *)
(*                     instance, and the two theorems the analysis manifest's *)
(*                     paths over it name                                     *)
(*                                                                            *)
(* The dealer-dealt run of this instance lays the cards itself from the       *)
(* chirality, so the run argument of psl211_dealt_params IS the chirality a   *)
(* coalition is not to learn. This file carries the model built on that run   *)
(* and the two theorems stated over it, in the framework's own vocabulary and *)
(* with no definition of the Tableau: the sample adapter, the model family    *)
(* indexed by the prior on the chirality, the colour map on a coalition's     *)
(* endpoints, the fibre counts of the two encoder decks, and the two          *)
(* theorems the analysis manifest's paths over this model name.               *)
(*                                                                            *)
(* Why the two theorems are here and not beside their programs: the analysis  *)
(* manifest names only facade aliases, and the facade is below the Tableau    *)
(* while the programs are above it, so a theorem a manifest path names has to *)
(* be stated where the facade can reach it.                                   *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_dealt_sample       == the fixed-dealer colour model as a sample   *)
(*                                adapter over the dealer-dealt execution     *)
(*   psl211_dealt_family       == that model as an analysis model family, one *)
(*                                member per prior on the chirality           *)
(*   psl211_dealt_decktbl      == the encoder deck of a chirality as a        *)
(*                                twelve-entry position-to-code table         *)
(*   psl211_dealt_view         == the reading giving cards 0, 1 and 6 to      *)
(*                                seats 0, 1 and 2                            *)
(*   psl211_dealt_fiber        == the cuts carrying one encoder deck to it    *)
(*   psl211_colour_of_reading  == the colour map on a coalition's endpoints   *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_perdeck_coalition_below_k                                         *)
(*                             == the three seats are below the threshold     *)
(*   psl211_dealt_sample_lawE  == the adapter's law is psl211P                *)
(*   psl211_dealt_sample_cut_distE                                            *)
(*                             == the cut law is uniform on the group         *)
(*   psl211_dealt_raw_countE   == one encoder deck reaches psl211_dealt_view  *)
(*                                under no cut and the other under one        *)
(*   psl211_dealt_massE        == the mass of that reading is the fibre's     *)
(*                                cardinality over the order of the group     *)
(*   psl211_dealt_colour_viewE == the model's colour view of a coalition is   *)
(*                                the colour map of that coalition's          *)
(*                                endpoints                                   *)
(*   psl211_dealt_colour_indep == below the threshold the colour map of a     *)
(*                                coalition's endpoints is independent of the *)
(*                                dealt chirality, at every prior             *)
(*   psl211_dealt_perdeck_reading_ge                                          *)
(*                             == three seats read the two chiralities of one *)
(*                                deal at least 1/660 apart, in the sum of    *)
(*                                absolute differences                        *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import transitivity_privacy design_privacy.
From pgg_reconstruct Require Import algebraic_rigidity.
From pgg_smc Require Import pgg_instance pgg_analysis_status.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_secrecy.
From pgg_smc Require Import psl211_blocks psl211_closure.
From pgg_smc Require Import psl211_endpoints psl211_alldecks psl211_models.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(** seatT — a seat of the instance's starting interface, the index a coalition
    is a set of. *)
Local Notation seatT :=
  ('I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1).

(** cardT — a card of the twelve-card deck, the value a seat reads. *)
Local Notation cardT :=
  ('I_(pgg_N' (mp_M (instance_profile psl211_algebra))).+1).

(** cutT — a cut, an element of the ambient permutation group the shuffle
    group sits inside. *)
Local Notation cutT := (pgg_gT psl211_M).

(** viewT — a reading, the card a coalition's seats see at each seat. *)
Local Notation viewT := ({ffun seatT -> cardT}).


(******************************************************************************)
(*     The three seats are below the privacy threshold                        *)
(******************************************************************************)

(** psl211_perdeck_coalition_le3 — the coalition witnessing the refutations
    has at most three seats, so it is one of the coalitions the instance's
    privacy claim covers and not an oversized one. *)
(* The bound is read off a three-point superset and never off an enumeration
   of the twelve seats, the ordinal enumeration going through an opaque
   decision that does not reduce. *)
Lemma psl211_perdeck_coalition_le3 : (#|psl211_perdeck_coalition| <= 3)%N.
Proof.
have Hsub : psl211_perdeck_coalition \subset
    ((psl211_code12 0 : seatT) |: ((psl211_code12 1 : seatT) |:
       [set (psl211_code12 2 : seatT)])).
  apply/subsetP => i.
  rewrite /psl211_perdeck_coalition in_set !inE -!val_eqE.
  by case: i => [] [|[|[|k]]] Hk.
apply: leq_trans (subset_leq_card Hsub) _.
rewrite cardsU1 cardsU1 cards1.
by case: (_ \notin _); case: (_ \notin _).
Qed.

(** psl211_perdeck_coalition_below_k — those three seats meet the threshold
    premise every security proposition states, the derived profile declaring
    six. A refutation of a field quantified over coalitions below the
    threshold has to discharge this premise, and it is the counterexample's
    only nontrivial premise. *)
Lemma psl211_perdeck_coalition_below_k :
  (#|psl211_perdeck_coalition| < profile_k (instance_profile psl211_algebra))%N.
Proof. by apply: leq_ltn_trans psl211_perdeck_coalition_le3 _. Qed.


(******************************************************************************)
(*     The fixed-dealer colour model as a sample adapter                      *)
(******************************************************************************)

(** psl211_dealt_inputTE — the run argument carrier of the dealer-dealt plug
    is the Boolean chirality, the first coordinate of a sample point of
    psl211P. The two layers therefore meet with no coercion between them. *)
Lemma psl211_dealt_inputTE :
  ep_inputT (instance_exec psl211_dealt_params) = bool.
Proof. by []. Qed.

(* Why the dealer-dealt mode and not the all-decks one: the all-decks run
   argument is a whole deck description and its law psl211_alldecksP redraws
   the deck, so psl211_alldecks_sample is over a different sample space and a
   different execution, and the weighted-word family draws the cut from a walk
   rather than uniformly. No family of this instance has psl211P as its law. *)

(** psl211_dealt_sample — the fixed-dealer colour model as a sample adapter
    over the dealer-dealt execution: one sample point is a chirality bit and
    a cut, the bit from the prior and the cut uniform on PSL(2,11), the two
    independent; the run argument is the bit and the cut is the shuffle. The
    run argument of these parameters is the chirality itself, and the
    chirality is what the colour view reads. Every statement made over this
    adapter is about the model's law and a reading of a coalition's
    endpoints; the Sampled level built over these parameters in
    instances/psl211/tableau/psl211_tableau_dealt.v is what identifies that
    reading with the executed one. *)
Definition psl211_dealt_sample (R : realType) (secretP : R.-fdist bool)
  : SampleAdapter R (instance_exec psl211_dealt_params) :=
  @MkSampleAdapter R (instance_profile psl211_algebra)
    (instance_exec psl211_dealt_params)
    ((bool * pgg_gT psl211_M)%type : finType)
    (psl211P secretP) fst snd.

(** psl211_dealt_sample_lawE — the adapter's law is the model's law. *)
Lemma psl211_dealt_sample_lawE (R : realType) (secretP : R.-fdist bool) :
  sa_sampleP (psl211_dealt_sample secretP) = psl211P secretP.
Proof. by []. Qed.

(** psl211_dealt_sample_argE — the run argument of a sample point is its
    chirality bit. *)
Lemma psl211_dealt_sample_argE (R : realType) (secretP : R.-fdist bool)
    (u : bool * pgg_gT psl211_M) :
  (psl211_dealt_sample secretP).(sa_arg) u = u.1.
Proof. by []. Qed.

(** psl211_dealt_sample_cutE — the cut of a sample point is its shuffle. *)
Lemma psl211_dealt_sample_cutE (R : realType) (secretP : R.-fdist bool)
    (u : bool * pgg_gT psl211_M) :
  (psl211_dealt_sample secretP).(sa_cut) u = u.2.
Proof. by []. Qed.

(** psl211_dealt_sample_cut_distE — the cut this model draws is the uniform
    law on the shuffle group, whatever the prior on the chirality. The
    input-indistinguishability proposition at a reading pushes the reading
    forward along this law, so it is the law the colour theorems' own
    uniformity hypothesis meets. *)
Lemma psl211_dealt_sample_cut_distE (R : realType) (secretP : R.-fdist bool) :
  @sa_cut_dist R (instance_profile psl211_algebra)
    (instance_exec psl211_dealt_params) (psl211_dealt_sample secretP)
  = (`U psl211_G_pos : R.-fdist (pgg_gT psl211_M)).
Proof.
have -> : @sa_cut_dist R (instance_profile psl211_algebra)
            (instance_exec psl211_dealt_params) (psl211_dealt_sample secretP)
        = fdist_snd (psl211P secretP) by [].
apply/fdist_ext => g; rewrite fdist_sndE.
under eq_bigr do rewrite /psl211P fdist_prodE /=.
by rewrite -big_distrl /= FDist.f1 mul1r.
Qed.

(** psl211_dealt_family — the fixed-dealer colour model as an analysis model
    family: one member per prior on the chirality, at every real field. The
    index is the prior and not the unit type, because the colour theorems of
    this instance hold under every prior and the two facts that refute
    independence need a prior giving mass to both chiralities. *)
Definition psl211_dealt_family : AnalysisModelFamily psl211_dealt_observed :=
  @MkAnalysisModelFamily psl211_dealt_observed
    (fun R : realType => R.-fdist bool)
    (fun (R : realType) (secretP : R.-fdist bool) =>
       psl211_dealt_sample secretP).


(******************************************************************************)
(*     The two encoder decks and the fibres of one reading of three seats     *)
(******************************************************************************)

(** psl211_dealt_decktbl b — the encoder deck of chirality b as a twelve-entry
    position-to-code table: the heart codes 0 to 5 ascend along the
    representative row of the system b names and the club codes 6 to 11 ascend
    along its complement. *)
(* Only raw nat data is counted from here on, the ordinal enumeration going
   through an opaque decision that does not reduce. *)
Definition psl211_dealt_decktbl (b : bool) : seq nat :=
  if b then [:: 6; 7; 0; 1; 8; 2; 9; 3; 4; 5; 10; 11]
       else [:: 0; 1; 6; 2; 7; 8; 9; 3; 10; 11; 4; 5].

(** psl211_dealt_decktblE — the card the encoder deals to a position is that
    table's entry at the position. *)
Lemma psl211_dealt_decktblE (b : bool) (i : 'I_12) :
  val (tnth (psl211_orbit_encode b) i)
  = nth 0 (psl211_dealt_decktbl b) (val i).
Proof.
rewrite /psl211_orbit_encode tnth_mktuple.
by case: b; case: i => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

(** psl211_dealt_decktbl_mod — every entry of that table is below twelve, so
    reading it modulo twelve changes nothing. *)
Lemma psl211_dealt_decktbl_mod (b : bool) (k : nat) :
  nth 0 (psl211_dealt_decktbl b) k %% 12 = nth 0 (psl211_dealt_decktbl b) k.
Proof.
by case: b; case: k => [|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]] //=;
   rewrite nth_nil.
Qed.

(** psl211_dealt_view — the reading that gives cards 0, 1 and 6 to seats 0, 1
    and 2, and card 0 to every seat outside the coalition. The encoder decks
    of the two chiralities reach it under different numbers of cuts, which is
    what refutes the constancy field in the dealt mode. *)
Definition psl211_dealt_view : viewT :=
  [ffun i => psl211_code12 (nth 0 [:: 0; 1; 6] (val i))].

(** psl211_dealt_test sq t — what the coalition is granted of the deck sq
    under the cut whose table is t matches psl211_dealt_view, tested on raw
    codes. *)
Definition psl211_dealt_test (sq t : seq nat) : bool :=
  [&& nth 0 sq (nth 0 t 0) %% 12 == 0,
      nth 0 sq (nth 0 t 1) %% 12 == 1 &
      nth 0 sq (nth 0 t 2) %% 12 == 6].

(** psl211_dealt_testE — the raw test decides the reading, so the fiber over
    psl211_dealt_view is counted by a boolean on nat lists. *)
Lemma psl211_dealt_testE (sq t : seq nat) :
  (psl211_perdeck_raw_view sq t == psl211_dealt_view) = psl211_dealt_test sq t.
Proof.
rewrite /psl211_dealt_test; apply/idP/idP.
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

(** psl211_dealt_raw_count b — how many of the 660 cuts carry the encoder deck
    of chirality b to psl211_dealt_view. *)
Definition psl211_dealt_raw_count (b : bool) : nat :=
  count (psl211_dealt_test (psl211_dealt_decktbl b))
    (unzip1 psl211_elem_table).

(** psl211_dealt_raw_countE — that count is zero at one chirality and one at
    the other. *)
Lemma psl211_dealt_raw_countE :
  psl211_dealt_raw_count true = 0 /\ psl211_dealt_raw_count false = 1.
Proof. by split; vm_compute. Qed.

(** psl211_dealt_static_obsE — seat i's entry of the framework's static
    coalition reading under the dealt parameters is the card the encoder deck
    of the run argument puts at the cut image of seat i. The dealt analogue of
    psl211_alldecks_static_obsE. *)
Lemma psl211_dealt_static_obsE (C : {set seatT})
    (b : ex_inputT psl211_dealt_params) (g : cutT) (i : seatT) :
  @static_coalition_obs psl211_algebra psl211_dealt_params C b g i
  = if i \in C
    then tnth (psl211_orbit_encode b) (@pgg_rho psl211_M g i)
    else ord0.
Proof.
rewrite static_coalition_obsE.
by case: ifP => // _; rewrite /= tnth_ord_tuple.
Qed.

(** psl211_dealt_raw_viewE — the raw reading is the framework's reading. *)
Lemma psl211_dealt_raw_viewE (b : bool) (g : cutT) :
  psl211_perdeck_raw_view (psl211_dealt_decktbl b) (psl211_ptbl g)
  = @static_coalition_obs psl211_algebra psl211_dealt_params
      psl211_perdeck_coalition b g.
Proof.
apply/ffunP => i.
rewrite /psl211_perdeck_raw_view ffunE psl211_dealt_static_obsE.
(* in_set and not inE: inE would rewrite the seq membership on the left
   instead of the set membership on the right *)
rewrite /psl211_perdeck_coalition in_set.
case Hi: (val i \in [:: 0; 1; 2]) => //.
rewrite psl211_perdeck_ptbl_nth; apply/val_inj.
by rewrite psl211_dealt_decktblE /= psl211_dealt_decktbl_mod.
Qed.

(** psl211_dealt_fiber b — the cuts of the group carrying the encoder deck of
    chirality b to psl211_dealt_view. *)
Definition psl211_dealt_fiber (b : bool) : {set cutT} :=
  [set g in pgg_G psl211_M |
     @static_coalition_obs psl211_algebra psl211_dealt_params
       psl211_perdeck_coalition b g == psl211_dealt_view].

(** psl211_dealt_fiberE — that fiber has the raw count as its cardinality. *)
Lemma psl211_dealt_fiberE (b : bool) :
  #|psl211_dealt_fiber b| = psl211_dealt_raw_count b.
Proof.
rewrite /psl211_dealt_fiber /psl211_dealt_raw_count.
transitivity
  (count (fun g => @static_coalition_obs psl211_algebra psl211_dealt_params
      psl211_perdeck_coalition b g == psl211_dealt_view)
    (enum (pgg_G psl211_M))).
  rewrite cardE /enum_mem size_filter count_filter.
  by apply: eq_count => g; rewrite !inE andbC.
transitivity
  (count (psl211_dealt_test (psl211_dealt_decktbl b))
    [seq psl211_ptbl g | g <- enum (pgg_G psl211_M)]).
  rewrite count_map; apply: eq_count => g.
  by rewrite -psl211_dealt_raw_viewE psl211_dealt_testE.
rewrite -!size_filter; apply: perm_size.
exact: (perm_filter _ psl211_perdeck_ptbl_enum).
Qed.

(* psl211_dealt_raw_count is sealed for the rest of the file: nothing further
   needs its body, psl211_dealt_raw_countE supplies both values, and leaving
   it transparent lets a unifier that falls back to conversion evaluate the
   count over the 660 tabulated cuts. *)
Local Opaque psl211_dealt_raw_count.

(** psl211_dealt_massE b — at the encoder deck of chirality b the law of what
    the coalition reads gives psl211_dealt_view the mass of its fiber of cuts
    over the order of the shuffle group. *)
Lemma psl211_dealt_massE (R : realType) (b : bool) :
  (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
       psl211_perdeck_coalition b) ((`U psl211_G_pos) : R.-fdist cutT))
     psl211_dealt_view
  = (#|pgg_G psl211_M|%:R)^-1 *+ #|psl211_dealt_fiber b| :> R.
Proof. by rewrite /psl211_dealt_fiber uniform_fdistmap_pointE. Qed.


(******************************************************************************)
(*     The colour map on a coalition's endpoints                              *)
(******************************************************************************)

(** psl211_colour_of_reading — the colour map on a coalition's endpoints:
    send each position of the coalition to the colour, heart or club, of the
    card that position holds, and every position outside the coalition to
    false. It is the read function of psl211_colour_reading of
    instances/psl211/psl211_colour_reading.v, and it is a function of the
    coalition as well as of the endpoint map, because a coalition's endpoints
    give card zero outside the coalition and card zero is a heart. *)
Definition psl211_colour_of_reading (C : {set seatT})
    (v : {ffun seatT -> cardT}) : {ffun seatT -> bool} :=
  [ffun i => if i \in C then psl211_is_heart (v i) else false].

(** psl211_colour_of_reading_obsE — reading a coalition's endpoints through
    the colour map gives each position of the coalition the colour of the
    card the encoder deck of that chirality puts at the cut image of the
    position. It is where the instance's seat reconciliation enters: the
    framework's endpoint map indexes through pi_starts and the colour pattern
    does not. *)
Lemma psl211_colour_of_reading_obsE (C : {set seatT})
    (b : ex_inputT psl211_dealt_params) (g : cutT) :
  psl211_colour_of_reading C
    (@static_coalition_obs psl211_algebra psl211_dealt_params C b g)
  = [ffun i => if i \in C
               then psl211_is_heart
                      (tnth (psl211_orbit_encode b) (@pgg_rho psl211_M g i))
               else false].
Proof.
apply/ffunP => i.
have HR : psl211_colour_of_reading C
            (@static_coalition_obs psl211_algebra psl211_dealt_params C b g) i
        = if i \in C
          then psl211_is_heart
                 (tnth (psl211_orbit_encode b) (@pgg_rho psl211_M g i))
          else false.
  rewrite /psl211_colour_of_reading ffunE psl211_dealt_static_obsE.
  (* the membership is cased and not the outer conditional alone: the
     reconciliation leaves a second copy of it under psl211_is_heart *)
  by case: (i \in C).
by rewrite HR ffunE.
Qed.

(** psl211_colour_of_reading_collides — two finite maps that give a position
    of the coalition two different hearts have the same colour value, so the
    colour map is not injective and the post-processing law discharged at it
    in instances/psl211/psl211_colour_reading.v runs in one direction only.
    That the two readings themselves differ is not this lemma's content; it is
    psl211_dealt_reading_indep_false there. *)
Lemma psl211_colour_of_reading_collides (C : {set seatT}) (i0 : seatT) :
  i0 \in C ->
  exists v w : {ffun seatT -> cardT},
    v != w /\ psl211_colour_of_reading C v = psl211_colour_of_reading C w.
Proof.
move=> Hi0.
exists [ffun _ : seatT => (@Ordinal 12 0 isT : cardT)],
       [ffun _ : seatT => (@Ordinal 12 1 isT : cardT)]; split.
  apply/eqP => Hvw; have := congr1 (fun f : {ffun seatT -> cardT} => f i0) Hvw.
  by rewrite !ffunE.
by apply/ffunP => i; rewrite /psl211_colour_of_reading !ffunE; case: ifP.
Qed.

(** psl211_dealt_colour_viewE — the model's colour view of a coalition is the
    colour map applied to that coalition's endpoints at the run argument and
    cut of the sample point, with the sample point left free. The instance's
    colour theorems are stated of the left side and the manifest's theorem of
    the right, and this is the identification between them. *)
Lemma psl211_dealt_colour_viewE (R : realType) (secretP : R.-fdist bool)
    (C : {set seatT}) :
  psl211_colour_view secretP C
  = (fun u => psl211_colour_of_reading C
                (static_coalition_obs C
                   ((psl211_dealt_sample secretP).(sa_arg) u)
                   ((psl211_dealt_sample secretP).(sa_cut) u))).
Proof.
apply: boolp.funext => u.
rewrite psl211_colour_of_reading_obsE.
by apply/ffunP => i; rewrite /psl211_colour_view /colour_view !ffunE.
Qed.


(******************************************************************************)
(*     The two theorems the manifest records over this model                  *)
(******************************************************************************)

(** psl211_dealt_colour_indep — below the framework's privacy threshold the
    colour map of a coalition's endpoints is independent of the dealt
    chirality, under every prior on the chirality. It is
    psl211_colour_view_indep of instances/psl211/psl211_secrecy.v stated over
    this model's own law and this model's own endpoint reader. The thresholds
    meet on the nose, the instance's counting argument reaching five of the
    twelve positions and the derived profile declaring six. The statement is
    an independence and not a numeric bound, and no entropy form of the
    framework is restated at it. *)
Theorem psl211_dealt_colour_indep (R : realType) (secretP : R.-fdist bool) :
  forall C : {set seatT},
    (#|C| < profile_k (instance_profile psl211_algebra))%N ->
    sa_sampleP (psl211_dealt_sample secretP)
    |= (fun u => psl211_colour_of_reading C
                   (static_coalition_obs C
                      ((psl211_dealt_sample secretP).(sa_arg) u)
                      ((psl211_dealt_sample secretP).(sa_cut) u)))
       _|_ psl211_secret secretP.
Proof.
move=> C HC.
have HC5 : (#|C| <= 5)%N by rewrite -ltnS -profile_k_psl211_algebra; exact: HC.
by rewrite -psl211_dealt_colour_viewE; exact: psl211_colour_view_indep HC5.
Qed.

(** psl211_dealt_perdeck_reading_ge — under this model's own cut law a
    coalition of three of the twelve seats reads the two chiralities of one
    deal at least 1/660 apart, in the sum of absolute differences, 1/660 being
    the reciprocal of the order of the shuffle group. The encoder deck of one
    chirality puts the three cards of psl211_dealt_view under exactly one cut
    and the other under none, so the two pushforwards of the uniform cut law
    differ at that reading by one cut's mass. Over these parameters the run
    argument is the chirality, so the two run arguments compared here are the
    two values of the secret, and a distinguisher told to compare them has
    advantage at least 1/1320; that reading of the statement is particular to
    the dealer-dealt mode and does not generalise to a mode whose run argument
    is a deck description. It is the dealer-dealt twin of
    psl211_alldecks_perdeck_reading_ge. *)
Theorem psl211_dealt_perdeck_reading_ge (R : realType)
    (secretP : R.-fdist bool) :
  (#|pgg_G psl211_M|%:R)^-1 <=
  var_dist
    (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
         psl211_perdeck_coalition true)
       (sa_cut_dist (psl211_dealt_sample secretP)))
    (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
         psl211_perdeck_coalition false)
       (sa_cut_dist (psl211_dealt_sample secretP))).
Proof.
(* each mass is pinned in a statement naming one chirality, and the two are
   brought together afterwards: a rewrite with a mass lemma in a goal
   holding both chiralities searches a goal holding both deck tables *)
rewrite (psl211_dealt_sample_cut_distE secretP).
have [Ht Hf] := psl211_dealt_raw_countE.
have Ct : #|psl211_dealt_fiber true| = 0 :=
  etrans (psl211_dealt_fiberE true) Ht.
have Cf : #|psl211_dealt_fiber false| = 1 :=
  etrans (psl211_dealt_fiberE false) Hf.
have Ut : (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
    psl211_perdeck_coalition true) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_dealt_view = 0 :> R.
  by rewrite psl211_dealt_massE Ct mulr0n.
have Uf : (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
    psl211_perdeck_coalition false) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_dealt_view = (#|pgg_G psl211_M|%:R)^-1 :> R.
  by rewrite psl211_dealt_massE Cf mulr1n.
apply: (Order.POrderTheory.le_trans _ (leq_var_dist _ _ psl211_dealt_view)).
by rewrite Ut Uf sub0r normrN ger0_norm ?invr_ge0 ?ler0n.
Qed.
