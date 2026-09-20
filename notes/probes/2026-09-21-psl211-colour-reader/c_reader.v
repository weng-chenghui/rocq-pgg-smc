(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* c_reader: the twelve-card colour view as a static reader, and how it sits  *)
(*           above the coalition's card-identity reading                      *)
(*                                                                            *)
(* PROBE FILE. Nothing permanent requires it. Ledger rows C2, C3, C6 and C7   *)
(* of notes/probes/2026-09-21-psl211-colour-reader/LEDGER.md.                 *)
(*                                                                            *)
(* C7, the record's statement comment. StaticReader of the first probe        *)
(* (notes/probes/2026-09-20-readers-and-marginal-bounds/r_framework.v) claims *)
(* in its comment that a reader sees nothing of the messages the run          *)
(* exchanged. The type does not enforce that, and the first probe's own       *)
(* second instance broke it. The sentence the record should carry instead is  *)
(* written below, above psl211_colour_reader, and checked against this        *)
(* instance: the type constrains the arguments and the value type, a function *)
(* of the coalition, the run argument and the cut into a finite type, and     *)
(* says nothing about how an instance computes its value. Whether a given     *)
(* reader is a group action is a theorem about that instance, here            *)
(* psl211_colour_reader_factorsE together with psl211_dealt_static_obsE.      *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_colour_reader      == the colour view as a static reader          *)
(*   psl211_colour_of_reading  == the colour map from a card-identity reading *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_colour_readerE     == the reader reads the colour view of the     *)
(*                                model, seat indices reconciled              *)
(*   psl211_colour_reader_funE == the same with the sample point left free    *)
(*   psl211_colour_reader_factorsE                                            *)
(*                             == the colour reader is the colour map of the  *)
(*                                canonical card-identity reader              *)
(*   psl211_colour_of_reading_collides                                        *)
(*                             == that colour map is not injective at a       *)
(*                                nonempty coalition                          *)
(*   psl211_canonical_reader_not_exact                                        *)
(*                             == the canonical reader is not independent of  *)
(*                                the chirality at this model, at three seats *)
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
From pgg_smc Require Import psl211_models psl211_reading_constancy.
From readersprobe Require Import r_framework.
From colourprobe Require Import c_adapter.

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
(*     C2: the colour view as a static reader                                 *)
(******************************************************************************)

(** psl211_colour_reader — the colour a coalition sees at each of its
    positions, as a static reader of the dealer-dealt execution: the reader
    takes the coalition, the run argument and the cut, and returns the finite
    map sending each position of the coalition to the colour, heart or club,
    of the card the encoder deck of that chirality puts at the cut image of
    the position, and each position outside the coalition to false. It is
    what a coalition holding cards of two indistinguishable colours sees, and
    it holds no card identity.

    The statement comment the record StaticReader should carry, checked here
    against an instance: a static reader of an execution is a family of
    functions of the coalition, the run argument and the cut, valued in a
    finite type that may depend on the coalition. That is the whole of what
    the type constrains. It does not say that a reader is a group action, nor
    that it ignores the interpreter's messages; a reader whose body reads the
    run is typed by the same record. That a given reader is a function of the
    dealt deck and the cut alone is a theorem about that reader, here the
    definition itself and, against the framework's own reading,
    psl211_colour_reader_factorsE. *)
Definition psl211_colour_reader : StaticReader psl211_dealt_params :=
  @MkStaticReader psl211_algebra psl211_dealt_params
    (fun _ => [the finType of {ffun seats -> bool}])
    (fun (C : {set seats}) (b : ex_inputT psl211_dealt_params) (g : cutT) =>
       [ffun i => if i \in C
                  then psl211_is_heart
                         (tnth (psl211_orbit_encode b) (@pgg_rho psl211_M g i))
                  else false]).

(** psl211_colour_readerE — the model's colour view of a sample point is the
    reader's value at that point's run argument and cut. The two sides are
    not the same term: the model's view is indexed by a card position and the
    reader by a seat of the execution's starting interface, and they agree
    because this instance's seats start at the twelve card positions in
    order. Every theorem of psl211_secrecy.v is about the left-hand side and
    every proposition stated at a reader about the right, so this equation is
    what carries one to the other. *)
Lemma psl211_colour_readerE (R : realType) (secretP : R.-fdist bool)
    (C : {set seats}) (u : bool * pgg_gT psl211_M) :
  psl211_colour_view secretP C u
  = sr_read psl211_colour_reader C
      ((psl211_colour_sample secretP).(sa_arg) u)
      ((psl211_colour_sample secretP).(sa_cut) u).
Proof. by apply/ffunP => i; rewrite /psl211_colour_view /colour_view !ffunE. Qed.

(** psl211_colour_reader_funE — the same identification with the sample point
    left free. A proposition stated at a reader pushes the reader forward
    along the model's law, so it needs the reader as one function and not as
    its values. *)
Lemma psl211_colour_reader_funE (R : realType) (secretP : R.-fdist bool)
    (C : {set seats}) :
  psl211_colour_view secretP C
  = (fun u => sr_read psl211_colour_reader C
                ((psl211_colour_sample secretP).(sa_arg) u)
                ((psl211_colour_sample secretP).(sa_cut) u)).
Proof. by apply: boolp.funext => u; exact: psl211_colour_readerE. Qed.


(******************************************************************************)
(*     C3: the colour reader is the colour map of the canonical reader        *)
(******************************************************************************)

(** psl211_colour_of_reading — the colour map on readings: keep the colour of
    the card each position of the coalition reads and discard its identity,
    and return false outside the coalition. It is a function of the coalition
    as well as of the reading, because the canonical reader returns card zero
    outside the coalition and card zero is a heart. *)
Definition psl211_colour_of_reading (C : {set seats})
    (v : {ffun seats -> cards}) : {ffun seats -> bool} :=
  [ffun i => if i \in C then psl211_is_heart (v i) else false].

(** psl211_colour_reader_factorsE — the colour reader is the colour map
    applied to the canonical card-identity reader, at every coalition, every
    run argument and every cut. This is the factorisation hypothesis of the
    post-processing law of a proposition at a reader, in the direction that
    holds: card identities determine colours. The converse direction is
    refuted by psl211_colour_of_reading_collides. *)
Lemma psl211_colour_reader_factorsE (C : {set seats})
    (b : ex_inputT psl211_dealt_params) (g : cutT) :
  sr_read psl211_colour_reader C b g
  = psl211_colour_of_reading C
      (sr_read (coalition_reading_reader psl211_dealt_params) C b g).
Proof.
(* the canonical reader's value is the framework's reading by one iota step,
   and the instance's reconciliation lemma needs it under that name; each
   ffunE is fired once and at a named side, an unscoped repeat rewriting the
   framework's reading open before the reconciliation can see it *)
have -> : sr_read (coalition_reading_reader psl211_dealt_params) C b g
        = @static_coalition_obs psl211_algebra psl211_dealt_params C b g by [].
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


(** psl211_colour_indistinguishability_of_reading — the framework's
    post-processing law discharged at this pair of readers: an
    input-indistinguishability proposition at the canonical card-identity
    reader gives the same number at the colour reader. The factorisation it
    consumes is psl211_colour_reader_factorsE, whose map is not injective, so
    this is the data processing inequality applied at a genuine coarsening
    and not at a renaming. It transports a bound and does not produce one:
    over this adapter the canonical reader has no such proposition at any
    small number, by psl211_canonical_reader_not_exact below and by
    psl211_dealt_constancy_false of
    instances/psl211/psl211_reading_constancy.v. *)
Lemma psl211_colour_indistinguishability_of_reading (R : realType)
    (secretP : R.-fdist bool) (c : R) :
  ReaderIndistinguishabilityPropAt (psl211_colour_sample secretP)
    (coalition_reading_reader psl211_dealt_params) c ->
  ReaderIndistinguishabilityPropAt (psl211_colour_sample secretP)
    psl211_colour_reader c.
Proof.
(* the reader arguments and the factorisation are positional on the
   framework's law, only its carrier arguments being implicit *)
exact: (reader_indistinguishability_postprocessing
          (coalition_reading_reader psl211_dealt_params) psl211_colour_reader
          psl211_colour_of_reading psl211_colour_reader_factorsE c).
Qed.


(******************************************************************************)
(*     C6, first half: the colour map loses the card identity                 *)
(******************************************************************************)

(** psl211_colour_of_reading_collides — at a coalition holding at least one
    position, two readings that give that position two different hearts have
    the same colour reading. The colour map is therefore not injective, so
    the identity of psl211_colour_reader_factorsE is a factorisation in one
    direction only and the colour reader is strictly coarser than the
    canonical one. *)
Lemma psl211_colour_of_reading_collides (C : {set seats}) (i0 : seats) :
  i0 \in C ->
  exists v w : {ffun seats -> cards},
    v != w /\ psl211_colour_of_reading C v = psl211_colour_of_reading C w.
Proof.
move=> Hi0.
exists [ffun _ : seats => (@Ordinal 12 0 isT : cards)],
       [ffun _ : seats => (@Ordinal 12 1 isT : cards)]; split.
  apply/eqP => Hvw; have := congr1 (fun f : {ffun seats -> cards} => f i0) Hvw.
  by rewrite !ffunE.
by apply/ffunP => i; rewrite /psl211_colour_of_reading !ffunE; case: ifP.
Qed.


(******************************************************************************)
(*     C6, second half: the two readers publish different propositions        *)
(******************************************************************************)

(** psl211_perdeck_static_view — the canonical card-identity reading of the
    three seats zero, one and two, as a random variable of the fixed-dealer
    colour model. The coalition is the one the instance's constancy
    counterexample already uses, and three is below the threshold of six. *)
Definition psl211_perdeck_static_view (R : realType) (secretP : R.-fdist bool)
  : {RV (psl211P secretP) -> {ffun seats -> cards}} :=
  fun u => @static_coalition_obs psl211_algebra psl211_dealt_params
             psl211_perdeck_coalition u.1 u.2.

(** psl211_canonical_reader_funE — the canonical reader over this adapter is
    the card-identity reading of the sample point's two coordinates. One iota
    step of the reader record and two of the adapter record. *)
Lemma psl211_canonical_reader_funE (R : realType) (secretP : R.-fdist bool) :
  (fun u => sr_read (coalition_reading_reader psl211_dealt_params)
              psl211_perdeck_coalition
              ((psl211_colour_sample secretP).(sa_arg) u)
              ((psl211_colour_sample secretP).(sa_cut) u))
  = psl211_perdeck_static_view secretP.
Proof. by []. Qed.

(** psl211_canonical_reader_not_exact — over the same model, the same adapter
    and at a coalition of three of the twelve positions, the canonical
    card-identity reader is not independent of the dealt chirality, under
    every prior giving mass to both chiralities. Three is below the threshold
    of six, so this is a coalition psl211_colour_reader_exact covers: at one
    model and one coalition the proposition holds at the colour reader and
    fails at the canonical one. The colour reader is therefore not the
    canonical reader renamed, and its theorem is not the image of any
    canonical-reader proposition over this adapter. What separates them is
    the card identity: the encoder decks of the two chiralities put one
    reading of three seats under exactly one cut and under none, which is
    psl211_dealt_raw_countE, while their colour patterns on five positions or
    fewer are equidistributed. *)
Lemma psl211_canonical_reader_not_exact (R : realType)
    (secretP : R.-fdist bool) :
  secretP true != 0 -> secretP false != 0 ->
  ~ ReaderExactPropAt (psl211_colour_sample secretP)
      (coalition_reading_reader psl211_dealt_params) (psl211_secret secretP).
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
have HV : 0 < `Pr[ (psl211_perdeck_static_view secretP) = psl211_dealt_view ].
  rewrite lt0r pfwd1_ge0 andbT.
  apply/pfwd1_neq0; exists (false, g0); split; last exact: Hmass false g0 Hf g0G.
  by rewrite inE /=; apply/eqP; exact: Hg0v.
have HS : 0 < `Pr[ (psl211_secret secretP) = true ].
  rewrite lt0r pfwd1_ge0 andbT.
  apply/pfwd1_neq0; exists (true, 1%g); split;
    last exact: Hmass true 1%g Ht (group1 _).
  by rewrite inE.
have Hzero : `Pr[ [% psl211_perdeck_static_view secretP,
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
rewrite psl211_canonical_reader_funE => Hcan.
move: (mulr_gt0 HV HS); rewrite -(Hcan psl211_dealt_view true) Hzero.
by move/lt0r_neq0; rewrite eqxx.
Qed.

Print Assumptions psl211_colour_reader_funE.
Print Assumptions psl211_colour_reader_factorsE.
Print Assumptions psl211_canonical_reader_not_exact.
