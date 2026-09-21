(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_tableau_dealt: two readings of the fixed-dealer colour model of the *)
(*                       twelve-card chirality instance, as two programs      *)
(*                                                                            *)
(* The dealer-dealt run of the twelve-card chirality instance lays the cards  *)
(* itself from the chirality, so the run argument of these parameters IS the  *)
(* chirality the coalition is not to learn. Over the one model built on that  *)
(* run this file writes two programs, and they state two different            *)
(* properties at two different readings.                                      *)
(*                                                                            *)
(* The first certifies exact independence at the colour reading: below the    *)
(* threshold of six of the twelve positions, the colours a coalition sees at  *)
(* its own positions are independent of the dealt chirality, at every prior   *)
(* on that chirality. The second publishes an obstruction at the coalition's  *)
(* own endpoint reading: three named positions read the two chiralities of    *)
(* one deal 1/660 apart in the sum of absolute differences, 1/660 being the   *)
(* reciprocal of the order of the shuffle group, so a distinguisher told to   *)
(* compare those two run arguments has advantage at least 1/1320 there. Both  *)
(* are unconditional and neither rests on an assumption about an adversary.   *)
(*                                                                            *)
(* Because the run argument is the chirality here, the second program is a    *)
(* privacy statement at this model and not only a statement about two inputs: *)
(* the two run arguments it compares are the two values of the secret. That   *)
(* reading of it is particular to the dealer-dealt mode and does not          *)
(* generalise: at the all-decks mode of this instance, and at every instance  *)
(* whose run argument is a deck description, input distinguishability         *)
(* compares two inputs and says nothing about a secret.                       *)
(*                                                                            *)
(* The two programs share every line up to the Sampled level, and they must:  *)
(* a reading is a coordinate of the security claim and not of the model, so   *)
(* two programs that differ in the reading alone still name one execution,    *)
(* one model family and one link lemma. The paths they publish are the        *)
(* manifest's thirteenth and fourteenth, psl211_dealt_colour_path and         *)
(* psl211_dealt_obstruction_path of manifest/pgg_analysis_manifest.v, and     *)
(* the two _pathE lemmas below decide each equality by conversion. Both       *)
(* differ from the manifest's twelfth path in two coordinates, the observed   *)
(* execution and the model family, the twelfth being over the all-decks run.  *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_dealt_sampled   == the shared prefix of both programs, at Sampled *)
(*   psl211_colour_exact_witness                                              *)
(*                          == the exact-independence witness at the colour   *)
(*                             reading, the dealt chirality as the secret     *)
(*   psl211_colour_exact_published                                            *)
(*                          == the colour program, published                  *)
(*   psl211_dealt_number    == 1/660, as a term in the real field alone       *)
(*   psl211_dealt_obstruction                                                 *)
(*                          == the obstruction at the endpoint reading and    *)
(*                             that number, at every field and prior          *)
(*   psl211_dealt_obstruction_published                                       *)
(*                          == the obstruction program                        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_dealt_sampled_viewE                                               *)
(*                          == the link lemma of the Sampled level, for both  *)
(*                             programs                                       *)
(*   psl211_colour_exact_published_readingE                                   *)
(*                          == the colour program's reading is the colour     *)
(*                             reading                                        *)
(*   psl211_colour_exact_published_propertyE                                  *)
(*                          == its security property is exact independence    *)
(*   psl211_colour_exact_published_pathE                                      *)
(*                          == the path it publishes                          *)
(*   psl211_dealt_input_distinguishable                                       *)
(*                          == the model is input distinguishable at 1/660    *)
(*                             at the coalition's own endpoint reading        *)
(*   psl211_dealt_number_gt0                                                  *)
(*                          == the number is above zero                       *)
(*   psl211_dealt_obstruction_pf                                              *)
(*                          == its proof at every field and prior             *)
(*   psl211_dealt_obstruction_published_kindE                                 *)
(*                          == the obstruction the second program hands over  *)
(*   psl211_dealt_obstruction_published_pathE                                 *)
(*                          == the path it publishes                          *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_instance pgg_sample_adapter.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_secrecy.
From pgg_smc Require Import psl211_models psl211_dealt_model.
From pgg_smc Require Import psl211_reading_constancy psl211_colour_reading.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Notation cutT := (pgg_gT (mp_M (instance_profile psl211_algebra))).

(******************************************************************************)
(*     The model family and the prefix both programs share                    *)
(******************************************************************************)

(* The model family psl211_dealt_family the sample line below names is built
   in instances/psl211/psl211_dealt_model.v, below the analysis manifest, so
   that the manifest's two paths over this model can carry it as their typed
   model witness. *)

(** psl211_dealt_sampled — the shared prefix of both programs: the algebra,
    the dealer-dealt parameters at the instance's fuel, the three run facts
    and the model family. The two programs below branch here and nowhere
    earlier, which is what a reading being a coordinate of the security claim
    and not of the model means in the text of a program. *)
Definition psl211_dealt_sampled : Tableau Sampled :=
  psl211_algebra dealt fuel psl211_fuel
    execute terminates by psl211_dealt_terminates
            endpoints  by psl211_dealt_endpoints
            recon      by psl211_dealt_recon
    sample psl211_dealt_family.

(** psl211_dealt_sampled_viewE — the link lemma this level proves: at every
    real field, every prior and every coalition, the executed coalition
    reader of the dealer-dealt run is the direct computation on that run's
    argument and cut. It is what carries a claim about a reading of the
    endpoints to a claim about an execution. *)
Lemma psl211_dealt_sampled_viewE :
  sampled_viewE_prop (sp_f (tableau_at psl211_dealt_sampled)).
Proof. exact: (proj2 (tableau_thm psl211_dealt_sampled)). Qed.

(******************************************************************************)
(*     Exact independence of the chirality at the colour reading              *)
(******************************************************************************)

(** psl211_colour_exact_witness — the exact-independence witness at the colour
    reading: the dealt chirality as the secret, and, below the threshold of
    six positions, the independence of the colours a coalition sees from it.
    The independence field is psl211_colour_reading_indep and nothing else,
    which is the instance's counting argument on five positions or fewer read
    as a privacy statement about what the colour reading grants. *)
Definition psl211_colour_exact_witness (R : realType)
    (secretP : R.-fdist bool)
  : ExactWitness (psl211_dealt_sample secretP) psl211_colour_reading :=
  @MkExactWitness R psl211_algebra psl211_dealt_params
    (psl211_dealt_sample secretP) psl211_colour_reading bool
    (psl211_secret secretP) (psl211_colour_reading_indep secretP).

(** psl211_colour_exact_published — the colour program. What the finished
    value carries about a coalition of fewer than six of the twelve positions
    is independence of the dealt chirality from the colours that coalition
    sees, at every real field and every prior, with no number in it. It says
    nothing about the card identities the same coalition holds, which the
    obstruction below is about. *)
Definition psl211_colour_exact_published : Published :=
  psl211_dealt_sampled
    certify ExactIndependence of psl211_colour_reading
            by psl211_colour_exact_witness
    |> publish StaticExecutedOnly assuming BaselineClassicalOnly.

(** psl211_colour_exact_published_readingE — the reading the published claim
    is made at is the colour reading, decided by conversion. It is the
    coordinate that separates this program from one certified at the
    coalition's own endpoints, which over this model would be false. *)
Lemma psl211_colour_exact_published_readingE (R : realType)
    (secretP : R.-fdist bool) :
  reading_of psl211_colour_exact_published R secretP = psl211_colour_reading.
Proof. exact: erefl. Qed.

(** psl211_colour_exact_published_propertyE — the security property it carries
    is exact independence: an independence and not a bound at a number. *)
Lemma psl211_colour_exact_published_propertyE (R : realType)
    (secretP : R.-fdist bool) :
  security_property_of psl211_colour_exact_published R secretP
  = ExactIndependenceProperty.
Proof. exact: erefl. Qed.

(** psl211_colour_exact_published_pathE — the path it publishes is the
    manifest's thirteenth: the dealer-dealt run, the AnalysisBridged level,
    the family the sample statement named and the two statuses. The equality
    is decided by conversion, so the program and the manifest cannot drift
    apart. *)
Lemma psl211_colour_exact_published_pathE :
  published_path psl211_colour_exact_published = psl211_dealt_colour_path.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The obstruction at the coalition's own endpoint reading                *)
(******************************************************************************)

(** psl211_dealt_input_distinguishable — the fixed-dealer model is input
    distinguishable at the coalition's own endpoint reading, at the reciprocal
    of the order of the shuffle group. The coalition is the three positions
    psl211_perdeck_coalition, below the threshold of six, and the two run
    arguments are the two chiralities, the dealer laying the cards from each:
    the encoder deck of one puts the three cards of psl211_dealt_view under
    exactly one cut and the other under none, so the two pushforwards of the
    uniform cut law differ at that reading by one cut's mass and the sum of
    absolute differences is at least that. Over these parameters the run
    argument is the chirality, so this is a privacy statement at this model, and
    that does not generalise to a mode whose run argument is a deck
    description. *)
Lemma psl211_dealt_input_distinguishable (R : realType)
    (secretP : R.-fdist bool) :
  InputDistinguishabilityPropAt (psl211_dealt_sample secretP)
    (coalition_endpoint_reading psl211_algebra)
    ((#|pgg_G psl211_M|%:R)^-1 : R).
Proof.
(* the goal the existential leaves reads the coalition's endpoints through
   the identity reading, and the raw inequality is stated at the bare reader.
   The identification is one iota step and one eta step and is discharged
   here, in a statement naming one chirality, rather than left to the
   conversion that closes the goal: a goal holding both chiralities and both
   deck tables is the shape that does not return *)
have Hred (b : bool) :
    (fun g : cutT => @cr_read psl211_algebra
        (coalition_endpoint_reading psl211_algebra) psl211_perdeck_coalition
        (@static_coalition_obs psl211_algebra psl211_dealt_params
           psl211_perdeck_coalition b g))
  = @static_coalition_obs psl211_algebra psl211_dealt_params
      psl211_perdeck_coalition b.
  exact: erefl.
exists psl211_perdeck_coalition, true, false.
split; first exact: psl211_perdeck_coalition_below_k.
rewrite (Hred true) (Hred false).
exact: psl211_dealt_perdeck_reading_ge.
Qed.

(** psl211_dealt_number — 1/660, the reciprocal of the order of the shuffle
    group, as a term in the real field and in nothing else. The terminal
    writes this name after at, so the number a reader of the program meets
    and the number the published member carries are one term. *)
Definition psl211_dealt_number : forall R : realType, R :=
  fun R => (#|pgg_G psl211_M|%:R)^-1.

(** psl211_dealt_obstruction — the obstruction the second program publishes,
    at every real field and every prior: the model is input distinguishable
    at the coalition's own endpoint reading at 1/660. *)
Definition psl211_dealt_obstruction
  : ObstructionPayload (tableau_at psl211_dealt_sampled) :=
  input_distinguishability_obstruction (tableau_at psl211_dealt_sampled)
    (coalition_endpoint_reading psl211_algebra) psl211_dealt_number.

(** psl211_dealt_number_gt0 — the number is above zero, the shuffle group
    being non-empty. At a number at or below zero the distance inequality is
    free and a published member would compare nothing. *)
Lemma psl211_dealt_number_gt0 (R : realType) : 0 < psl211_dealt_number R.
Proof. by rewrite /psl211_dealt_number invr_gt0 ltr0n; exact: psl211_G_pos. Qed.

(** psl211_dealt_obstruction_pf — its proof at every field and prior: the
    number is above zero, and the model is input distinguishable at it. *)
Definition psl211_dealt_obstruction_pf
  : ObstructionPayloadProp psl211_dealt_obstruction :=
  fun (R : realType) (secretP : R.-fdist bool) =>
    conj (psl211_dealt_number_gt0 R)
         (psl211_dealt_input_distinguishable secretP).

(** psl211_dealt_obstruction_published — the obstruction program. It certifies
    no security property, its data carrying no SecurityEvidence, and two
    exclusions follow from its one member: every number at which an
    input-indistinguishability program over this model at this reading states
    its proposition is at least 1/660, and no certificate at this reading has
    its ideal cut within eps of the model's own cut law once eps added to itself
    stays below 1/660. It leaves the colour reading untouched, where
    psl211_colour_exact_published certifies exact independence over the same
    model; the two are the pair a reading of a coalition's endpoints exists to
    separate. *)
Definition psl211_dealt_obstruction_published : PublishedObstruction :=
  psl211_dealt_sampled
    |> publish Obstruction InputDistinguishability
       of (coalition_endpoint_reading psl211_algebra)
       at psl211_dealt_number
       by psl211_dealt_obstruction_pf assuming BaselineClassicalOnly.

(** psl211_dealt_obstruction_published_kindE — the obstruction the program
    hands over is the one written on its own line. *)
Lemma psl211_dealt_obstruction_published_kindE :
  published_obstruction_kind psl211_dealt_obstruction_published
  = psl211_dealt_obstruction.
Proof. exact: erefl. Qed.

(** psl211_dealt_obstruction_published_pathE — the path it publishes is the
    manifest's fourteenth: the dealer-dealt run, the AnalysisBridged level,
    the model family and NegativeTransfer. It is not the manifest's twelfth,
    which is over the all-decks run. *)
Lemma psl211_dealt_obstruction_published_pathE :
  published_obstruction_path psl211_dealt_obstruction_published
  = psl211_dealt_obstruction_path.
Proof. exact: erefl. Qed.
