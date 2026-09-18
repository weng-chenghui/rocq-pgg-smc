(* Probe, 2026-09-19. Not a production file.                                  *)
(******************************************************************************)
(* psl211_sc_const_probe: the spectral certificate's constancy field at the    *)
(*                        twelve-card chirality instance, under the all-decks  *)
(*                        run parameters and the group-uniform ideal cut       *)
(*                                                                            *)
(* The SpectralCert record of manifest/pgg_tableau.v carries a field sc_const  *)
(* asking that a coalition below the privacy threshold read the ideal cut the  *)
(* same way whatever the run argument. This file restates that field as a      *)
(* standalone proposition, checks the restatement against the record, and      *)
(* decides it at PSL(2,11) under the all-decks parameters with the ideal taken *)
(* to be the uniform law on the shuffle group: it is false, at every real      *)
(* field, and the three seats 0, 1 and 2 at the deck description               *)
(* psl211_perdeck_deal witness it.                                            *)
(*                                                                            *)
(* Everything mathematical is already in instances/psl211/psl211_models.v.     *)
(* What is added here is the discharge of the threshold premise for those      *)
(* three seats and the transport of the framework's seat reader to the         *)
(* instance's, which is one congr1 and no rewrite through the tables.          *)
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
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import psl211_group psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_exec.
From pgg_smc Require Import psl211_endpoints psl211_alldecks psl211_models.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Import Num.Theory.

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

(******************************************************************************)
(*     The constancy field as a standalone proposition                        *)
(******************************************************************************)

(** sc_const_prop E ideal — a coalition of fewer than profile_k seats reads
    the law ideal on cuts the same way whatever the run argument. This is what
    a spectral certificate asserts about its idealized cut: the run argument
    carries the secret, so constancy in it is the whole of the privacy content
    the spectral arm gets from the ideal, and the variation-distance field is
    what transfers that content from the ideal to the real cut. *)
Definition sc_const_prop (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A)
    (ideal : R.-fdist (pgg_gT (mp_M (instance_profile A)))) : Prop :=
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| < profile_k (instance_profile A))%N ->
    forall x x' : ex_inputT E,
      fdistmap (@static_coalition_obs A E C x) ideal
      = fdistmap (@static_coalition_obs A E C x') ideal.

(** sc_const_prop_field — the proposition above is the certificate's fourth
    field read at the certificate's own ideal. Nothing below depends on the
    spelling of the field, so a change to the record surfaces here. *)
Lemma sc_const_prop_field (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : SpectralCert sa) : sc_const_prop E (sc_ideal cert).
Proof. exact: sc_const cert. Qed.

(******************************************************************************)
(*     The three seats are below the privacy threshold                        *)
(******************************************************************************)

(** psl211_perdeck_coalition_le3 — the counterexample coalition has at most
    three seats. The bound is read off a three-point superset and never off an
    enumeration of the twelve seats, the ordinal enumeration going through an
    opaque decision that does not reduce. *)
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
    premise of both security arms, the derived profile declaring six. A
    refutation of a field quantified over coalitions below the threshold has
    to discharge this premise, and it is the only nontrivial premise the
    counterexample owes. *)
Lemma psl211_perdeck_coalition_below_k :
  (#|psl211_perdeck_coalition| < profile_k (instance_profile psl211_algebra))%N.
Proof. by apply: leq_ltn_trans psl211_perdeck_coalition_le3 _. Qed.

(******************************************************************************)
(*     The constancy field fails at the group-uniform ideal                   *)
(******************************************************************************)

(** psl211_alldecks_sc_const_false — under the all-decks run parameters no
    spectral certificate can take the uniform law on the shuffle group as its
    ideal cut: seats 0, 1 and 2 read that law differently at the two
    chiralities of one deck description. The all-decks dealer's privacy is an
    average over deck descriptions, and a constancy field quantified over
    every run argument asks for the statement one deck description at a time,
    which is the statement psl211_perdeck_law_neq refutes. *)
Lemma psl211_alldecks_sc_const_false (R : realType) :
  ~ sc_const_prop psl211_alldecks_params
      ((`U psl211_G_pos) : R.-fdist cutT).
Proof.
move=> Hconst.
have Heq := Hconst psl211_perdeck_coalition psl211_perdeck_coalition_below_k
  (true, psl211_perdeck_deal) (false, psl211_perdeck_deal).
(* the reader is moved by one congr1 under fdistmap and never by a rewrite:
   the two sides differ only in the chirality bool, and a rewrite there has to
   search a goal holding both deck tables *)
have Et : @static_coalition_obs psl211_algebra psl211_alldecks_params
     psl211_perdeck_coalition (true, psl211_perdeck_deal)
   = (fun g => psl211_alldecks_view psl211_perdeck_coalition
        (true, psl211_perdeck_deal) g)
  := psl211_alldecks_static_obs_funE _ _.
have Ef : @static_coalition_obs psl211_algebra psl211_alldecks_params
     psl211_perdeck_coalition (false, psl211_perdeck_deal)
   = (fun g => psl211_alldecks_view psl211_perdeck_coalition
        (false, psl211_perdeck_deal) g)
  := psl211_alldecks_static_obs_funE _ _.
move/negP: (psl211_perdeck_law_neq R); apply; apply/eqP.
exact: (etrans
  (esym (congr1 (fun f => fdistmap f ((`U psl211_G_pos) : R.-fdist cutT)) Et))
  (etrans Heq
    (congr1 (fun f => fdistmap f ((`U psl211_G_pos) : R.-fdist cutT)) Ef))).
Qed.

(******************************************************************************)
(*     The mutation: the empty coalition reads every ideal constantly         *)
(******************************************************************************)

(** psl211_alldecks_static_obs_set0 — a coalition with no seats reads every
    cut as the constant map to card zero. The framework's reader returns card
    zero outside the coalition, so at the empty coalition it carries no deck
    information at all. *)
Lemma psl211_alldecks_static_obs_set0 (x : ex_inputT psl211_alldecks_params) :
  @static_coalition_obs psl211_algebra psl211_alldecks_params set0 x
  = (fun _ : cutT => [ffun _ : seatT => (ord0 : cardT)]).
Proof.
apply: boolp.funext => g; apply/ffunP => i.
by rewrite psl211_alldecks_static_obsE in_set0 ffunE.
Qed.

(** psl211_alldecks_sc_const_set0 — at the empty coalition the constancy
    statement holds, for every law on cuts. The refutation above therefore
    spends its coalition: what fails is a reading of three seats, not the
    shape of the field. *)
Lemma psl211_alldecks_sc_const_set0 (R : realType)
    (ideal : R.-fdist cutT) (x x' : ex_inputT psl211_alldecks_params) :
  fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params set0 x)
    ideal
  = fdistmap
      (@static_coalition_obs psl211_algebra psl211_alldecks_params set0 x')
      ideal.
Proof.
by rewrite (psl211_alldecks_static_obs_set0 x)
  (psl211_alldecks_static_obs_set0 x').
Qed.

Print Assumptions psl211_alldecks_sc_const_false.
Print Assumptions psl211_alldecks_sc_const_set0.
Print Assumptions sc_const_prop_field.
