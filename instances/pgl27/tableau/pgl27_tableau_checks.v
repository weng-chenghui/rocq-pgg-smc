(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_tableau_checks: the terms the kernel refuses at the eight-card orbit *)
(* instance                                                                   *)
(*                                                                            *)
(* Each entry below is one written term that the kernel rejects, recorded so  *)
(* that the rejection is compiled rather than described. A recorded rejection *)
(* says what it says about the one term written under it and about no other   *)
(* term: it fixes a spelling that does not typecheck, and states no general   *)
(* impossibility.                                                             *)
(*                                                                            *)
(* Seven groups. Two are about what a clause records: the coalition size      *)
(* written in a leaks clause is checked against the proof it names, and the   *)
(* arm a program carries is the one its certify statement wrote, so recording *)
(* the word program at the exact arm is refused. Beside the second sits the   *)
(* one positive statement of this file, that the two programs over the word   *)
(* model carry different arms, which is a comparison of two programs rather   *)
(* than a statement about one; the sixth group turns the same point the other *)
(* way, refusing to read the exact arm's four conjuncts off the word program. *)
(*                                                                            *)
(* One group is the fork the literal reduction makes: a prefix that builds    *)
(* its own termination obligation is not the term pgl27_dealt is, and the     *)
(* instance's own model family, typed against pgl27_observed, is refused over *)
(* the forked execution. Two are about the terminal: a conclude payload with  *)
(* no index binder is refused in both spellings of the program, and the       *)
(* program at 2^-41 is refused where its terminal is written, the             *)
(* certificate's own number being twice 2^-40.                                *)
(*                                                                            *)
(* The last group is what a proximity certificate may name as its ideal, and  *)
(* its three rejections have two causes. Two are refused at the index type,   *)
(* which separates the exact family indexed by the unit type from the two     *)
(* families indexed by a law of the dealt secret, and not the exact shuffle   *)
(* from the word walk. The third is well typed at its index and refused at    *)
(* its distance field, whose proof relates the word model at one law of the   *)
(* secret to the exact model at that same law and not to the exact model at   *)
(* the uniform one. What refutes that field, rather than refusing a written   *)
(* term, is pgl27_word_uniform_ideal_close_false of pgl27_proximity.v.        *)
(*                                                                            *)
(* One lemma of this file shares its name with the rejection recorded above   *)
(* it, and the order is what lets both compile. Rocq checks that a name is    *)
(* free before it elaborates a body, so a file holding the lemma first would  *)
(* reject the term for an occupied name and not for the arm the term asserts. *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_word_published_arm_neq  == the two programs over the word model    *)
(*                              carry different arms                          *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import pgl27_tableau_observed.
From pgg_smc Require Import pgl27_proximity.
From pgg_smc Require Import pgl27_tableau_analysis_bridged.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.


(******************************************************************************)
(*     The number written in a leaks clause                                   *)
(******************************************************************************)

(** The number written in the leaks clause is checked against the proof.
    Writing seven where the coalition has four seats fails on unification of
    #|C| = 4 with #|C| = 7, so the clause records a size the kernel decided
    rather than a size a reader is asked to believe. *)
Fail Definition pgl27_exact_published_leak7 : Published :=
  pgl27_dealt
    sample  pgl27_exact_family
    certify ExactIndependence pgl27_exact_witness
            leaks at 7 by pgl27_exact_leak4
    |> publish StaticExecutedOnly BaselineClassicalOnly.


(******************************************************************************)
(*     The arm a program carries                                              *)
(******************************************************************************)

(** Recording the word program at the exact arm is rejected by conversion, so
    the program carries the arm its certify statement wrote and no other. *)
Fail Definition pgl27_word_published_arm_neq (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_word_published)) R) :=
  (erefl : security_arm_of pgl27_word_published R idx
           = ExactIndependenceArm).

(** The two programs over the one model carry different arms, so the pair is two
    statements about one probability model and not one statement published
    twice. *)
Lemma pgl27_word_published_arm_neq (R : realType) (secretP : R.-fdist bool) :
  security_arm_of pgl27_word_proximity_published R secretP
  <> security_arm_of pgl27_word_branch_published39 R secretP.
Proof.
(* Three timings are each why one line reads as it does. Binding the prior as an
   index of the proximity program costs 78.7 s in the statement alone, because
   the branch program's index type is then reached by conversion through both
   programs' observed executions, so it is bound at its own type. Rewriting with
   the two armE lemmas applied to that prior costs 24.3 s, and restating the two
   equations locally and rewriting with both in the inequation costs 24.1 s,
   because a rewrite scans the other side of the goal and so converts one
   program against the other. The equation between the arms is therefore assumed
   first, and each rewrite then runs on a goal that mentions one program. *)
have Hp : security_arm_of pgl27_word_proximity_published R secretP
  = IdealProximityArm by [].
have Hs : security_arm_of pgl27_word_branch_published39 R secretP
  = InputIndistinguishabilityArm by [].
move=> Harm; move: Hp; rewrite Harm Hs => Hf; discriminate Hf.
Qed.


(******************************************************************************)
(*     The fork the literal reduction makes                                   *)
(******************************************************************************)

(** The two prefixes are not the same term. *)
Fail Definition pgl27_inline_neq : pgl27_inline_dealt = pgl27_dealt := erefl.

(** The instance's own model is typed against pgl27_observed and is rejected
    over the forked one. This is the fork made visible, and the reason the
    demonstration stops at the prefix: a program through the literal
    reduction shares no typed evidence with the programs above. *)
Fail Definition pgl27_inline_reuse : Tableau Sampled :=
  pgl27_inline_dealt sample pgl27_exact_family.


(******************************************************************************)
(*     The terminal's index binder                                            *)
(******************************************************************************)

(** The terminal's obligation is one inequality per real field and per index of
    the family. A payload with the right relation but no index binder is
    rejected, which is what keeps a program from publishing a bound that holds
    only at the index a reader happened to pick. *)
Fail Definition pgl27_word_published39_unindexed : PublishedAt pgl27_bound39 :=
  pgl27_dealt
    sample  pgl27_word_family
    certify InputIndistinguishability pgl27_word_cert
    |> conclude pgl27_bound39 by (fun R => ssr_ext.eqW (pow2_split R))
    |> publish IdealFinite BaselineClassicalOnly.

(** The same rejection through the bind, so the surface is not what rejects
    it. *)
Fail Definition pgl27_word_published39_unindexed_bind
  : PublishedAt pgl27_bound39 :=
  pgl27_dealt
    ;;; sample_step of pgl27_word_family
    ;;; certify_indistinguishability of pgl27_word_cert
    ;;; conclude pgl27_bound39 of (fun R => ssr_ext.eqW (pow2_split R))
    ;;; publish BaselineClassicalOnly of IdealFinite.


(******************************************************************************)
(*     A number below the proved one                                          *)
(******************************************************************************)

(** The program at that number is rejected where its terminal is written. *)
Fail Definition pgl27_word_published41 : PublishedAt pgl27_bound41 :=
  pgl27_dealt
    sample  pgl27_word_family
    certify InputIndistinguishability pgl27_word_cert
    |> conclude pgl27_bound41 by (fun R _ => ssr_ext.eqW (pow2_split R))
    |> publish IdealFinite BaselineClassicalOnly.


(******************************************************************************)
(*     The arms are different statements                                      *)
(******************************************************************************)

(** The arms are different statements, and the difference is visible in what a
    program's projection takes after the coalition. A program certifying input
    indistinguishability is asked here for a threshold proof in the position
    where it expects the first of two dealt secrets, and is rejected: what the
    word program proves at a coalition is a distance between the readings of two
    secrets, so the two secrets come before the threshold proof. *)
Fail Definition pgl27_word_arm_is_not_exact (R : realType)
    (secretP : R.-fdist bool) (C : {set 'I_8}) (HC : (#|C| < 4)%N) :=
  view_secrecy_of pgl27_word_published R secretP C HC.


(******************************************************************************)
(*     What a certificate may name as its ideal                               *)
(******************************************************************************)

(** The unit-indexed exact family cannot be read at the prior the word model
    carries. The index of an analysis model family is a type depending on the
    real field alone, and amf_sample asks for an inhabitant of it, so a
    distribution on the booleans is offered where the unit type is expected
    and the two sample adapters are never reached. The term written here is
    therefore refused before any distance is considered. The same family at
    its own index tt is a well-typed ideal for this actual model, and what
    refuses it there is the distance field, which the guard below records. *)
Fail Definition pgl27_word_proximity_cert_unit_ideal (R : realType)
    (secretP : R.-fdist bool)
  : IdealProximityCert (amf_sample pgl27_word_family R secretP) :=
  @MkIdealProximityCert R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP)
    (amf_sample pgl27_exact_family R secretP)
    (@pgl27_exact_witness R secretP)
    (pgl27_word_secret secretP)
    (sw_bound_eps (pgl27_word_marginal_bound R))
    (fun C HC => pgl27_word_proximity_close secretP HC).

(** The one member of the unit-indexed exact family fixes the uniform
    secret, and it is a well-typed ideal for a word model at any prior: the
    index is supplied as tt and both adapters live over the same execution.
    What the kernel rejects is the distance field, whose proof is stated
    between the word model at secretP and the exact model at secretP and not
    between the word model at secretP and the exact model at the uniform
    prior. The Fail rejects the one term written here, on that mismatch of
    types, and rules out no other term. What refutes the field itself is
    pgl27_word_uniform_ideal_close_false of pgl27_proximity.v, at the point-
    mass prior, where the two secret marginals are one apart and 2^-40 is
    not; at a prior near the uniform one that lower bound is small and
    nothing is claimed. *)
Fail Definition pgl27_word_proximity_cert_uniform_ideal (R : realType)
    (secretP : R.-fdist bool)
  : IdealProximityCert (amf_sample pgl27_word_family R secretP) :=
  @MkIdealProximityCert R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP)
    (amf_sample pgl27_exact_family R tt)
    (@pgl27_exact_witness R tt)
    (pgl27_word_secret secretP)
    (sw_bound_eps (pgl27_word_marginal_bound R))
    (fun C HC => pgl27_word_proximity_close secretP HC).

(** The word model's proximity certificate does not continue the exact model's
    branch point. The payload type is IdealProximityPayload at the model family
    the Sampled value names, so the clause is checked first against that
    family's index type, unit against a distribution on the booleans. The Fail
    rejects the one term written here, on that mismatch of index types, and
    rules out no other term. The index types separate pgl27_exact_family from
    pgl27_word_family. The certificate this file builds,
    pgl27_word_proximity_cert, reads its two models at one index, the member of
    pgl27_prior_exact_family at secretP and the member of pgl27_word_family at
    that same secretP. *)
Fail Definition pgl27_cross_model_proximity : Tableau AnalysisBridged :=
  pgl27_dealt sample pgl27_exact_family
    certify IdealProximity pgl27_word_proximity_cert.
