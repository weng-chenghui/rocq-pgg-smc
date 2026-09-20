(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* n_psl211_number: the second member of the family, an obstruction at a      *)
(*                  number (probe, ledger row N9, optional)                   *)
(*                                                                            *)
(* The row above denies a class of certificates. This one denies the          *)
(* input-indistinguishability proposition itself below a number, at the       *)
(* all-decks model and at no certificate in particular: the model's own cut   *)
(* is the group-uniform law, and under it the two chiralities of one deal     *)
(* give the reading psl211_perdeck_view masses zero and the reciprocal of the *)
(* group order, so the two readings are that far apart in the sum of absolute *)
(* differences whatever a certificate says.                                   *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_alldecks.
From pgg_smc Require Import psl211_models psl211_reading_constancy.
From refuteprobe Require Import n_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Notation seatT :=
  ('I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1).
Local Notation cardT :=
  ('I_(pgg_N' (mp_M (instance_profile psl211_algebra))).+1).
Local Notation cutT := (pgg_gT psl211_M).
Local Notation viewT := ({ffun seatT -> cardT}).

(** The mass the group-uniform cut gives psl211_perdeck_view at chirality
    true, read at the framework's own static reader: zero, the true fiber
    being empty. The reader is moved by congr1 in term mode and never by a
    rewrite, as psl211_reading_constancy.v moves it. *)
Lemma psl211_perdeck_static_mass_true (R : realType) :
  (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
       psl211_perdeck_coalition (true, psl211_perdeck_deal))
     ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view = 0 :> R.
Proof.
have [Ht _] := psl211_perdeck_raw_countE.
have Ct : #|psl211_perdeck_fiber true| = 0 :=
  etrans (psl211_perdeck_fiberE true) Ht.
have Ut : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
    (true, psl211_perdeck_deal) g) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_perdeck_view = 0 :> R.
  by rewrite psl211_perdeck_massE Ct mulr0n.
have Et : @static_coalition_obs psl211_algebra psl211_alldecks_params
     psl211_perdeck_coalition (true, psl211_perdeck_deal)
   = (fun g => psl211_alldecks_view psl211_perdeck_coalition
        (true, psl211_perdeck_deal) g)
  := psl211_alldecks_static_obs_funE _ _.
exact: (etrans
  (congr1 (fun q : R.-fdist viewT => q psl211_perdeck_view)
     (congr1 (fun f => fdistmap f ((`U psl211_G_pos) : R.-fdist cutT)) Et))
  Ut).
Qed.

(** The same mass at chirality false: the reciprocal of the group order, the
    false fiber holding exactly one cut. *)
Lemma psl211_perdeck_static_mass_false (R : realType) :
  (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
       psl211_perdeck_coalition (false, psl211_perdeck_deal))
     ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view
  = (#|pgg_G psl211_M|%:R)^-1 :> R.
Proof.
have [_ Hf] := psl211_perdeck_raw_countE.
have Cf : #|psl211_perdeck_fiber false| = 1 :=
  etrans (psl211_perdeck_fiberE false) Hf.
have Uf : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
    (false, psl211_perdeck_deal) g) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_perdeck_view = (#|pgg_G psl211_M|%:R)^-1 :> R.
  by rewrite psl211_perdeck_massE Cf mulr1n.
have Ef : @static_coalition_obs psl211_algebra psl211_alldecks_params
     psl211_perdeck_coalition (false, psl211_perdeck_deal)
   = (fun g => psl211_alldecks_view psl211_perdeck_coalition
        (false, psl211_perdeck_deal) g)
  := psl211_alldecks_static_obs_funE _ _.
exact: (etrans
  (congr1 (fun q : R.-fdist viewT => q psl211_perdeck_view)
     (congr1 (fun f => fdistmap f ((`U psl211_G_pos) : R.-fdist cutT)) Ef))
  Uf).
Qed.

(** Over the all-decks model, the number an input-indistinguishability
    program publishes is at least the reciprocal of the order of the shuffle
    group. Three of the twelve seats read the two chiralities of one deal at
    masses zero and that reciprocal under the model's own cut, so the two
    readings are that far apart in the sum of absolute differences, and the
    proposition asserts they are within the published number. The statement
    quantifies over the certificate and constrains none of its fields: it
    fixes from below what any input-indistinguishability program over this
    model can say, where psl211_alldecks_no_certificate_near denies a class
    of certificates. *)
Theorem psl211_alldecks_indistinguishability_number_ge (R : realType)
    (cert : IndistinguishabilityCert (amf_sample psl211_exact_family R tt))
    (c : R) :
  IndistinguishabilityPropAt cert c -> (#|pgg_G psl211_M|%:R)^-1 <= c.
Proof.
move=> Hprop.
have H0 := Hprop psl211_perdeck_coalition (true, psl211_perdeck_deal)
  (false, psl211_perdeck_deal) psl211_perdeck_coalition_below_k.
have Hd : sa_cut_dist (amf_sample psl211_exact_family R tt)
        = ((`U psl211_G_pos) : R.-fdist cutT) := psl211_alldecks_cut_distE R.
rewrite Hd in H0.
have T := Order.POrderTheory.le_trans
  (leq_var_dist _ _ psl211_perdeck_view) H0.
have Habs0 : `| (0:R) - (#|pgg_G psl211_M|%:R)^-1 |
           = (#|pgg_G psl211_M|%:R)^-1.
  rewrite sub0r normrN ger0_norm //.
  by rewrite invr_ge0 ler0n.
(* Each mass is substituted by one congr1 and never by a rewrite. A rewrite
   here matches its pattern against the other chirality's reader as well, and
   that mismatch is decided by conversion on the two deck tables: measured on
   2026-09-21, the two-rewrite form costs 228 s and this one nothing. *)
have Hval : `| (fdistmap (@static_coalition_obs psl211_algebra
                   psl211_alldecks_params psl211_perdeck_coalition
                   (true, psl211_perdeck_deal))
                  ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view
              - (fdistmap (@static_coalition_obs psl211_algebra
                   psl211_alldecks_params psl211_perdeck_coalition
                   (false, psl211_perdeck_deal))
                  ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view |
            = (#|pgg_G psl211_M|%:R)^-1 :> R :=
  etrans
    (congr1 (fun z : R => `| z
        - (fdistmap (@static_coalition_obs psl211_algebra
             psl211_alldecks_params psl211_perdeck_coalition
             (false, psl211_perdeck_deal))
            ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view |)
       (@psl211_perdeck_static_mass_true R))
    (etrans
       (congr1 (fun z : R => `| (0:R) - z |)
          (@psl211_perdeck_static_mass_false R))
       Habs0).
exact: (eq_ind _ (fun z : R => z <= c) T _ Hval).
Qed.

Print Assumptions psl211_alldecks_indistinguishability_number_ge.
