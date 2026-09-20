(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* landing_draft_psl211: the text appended to                                 *)
(* instances/psl211/psl211_reading_constancy.v, compiled before it is written *)
(* there. Every declaration below is the production text; only this header    *)
(* and the Check are not.                                                     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_collusion_bound.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import psl211_group psl211_orbit psl211_scheme.
From pgg_smc Require Import psl211_profile psl211_exec psl211_alldecks.
From pgg_smc Require Import psl211_models psl211_reading_constancy.
From refuteprobe Require Import landing_draft_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Import Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Notation seatT :=
  ('I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1).
Local Notation cardT :=
  ('I_(pgg_N' (mp_M (instance_profile psl211_algebra))).+1).
Local Notation cutT := (pgg_gT psl211_M).
Local Notation viewT := ({ffun seatT -> cardT}).

(* The two spellings of the all-decks model are one term: the exact family
   indexed by unit returns this adapter at every index. *)
Check (fun R : realType =>
  erefl : psl211_alldecks_sample R = amf_sample psl211_exact_family R tt).

(******************************************************************************)
(*     How far apart the two chiralities of one deal are read                 *)
(******************************************************************************)

(** psl211_perdeck_static_mass_true — the mass the group-uniform cut gives the
    reading psl211_perdeck_view at chirality true, taken at the framework's own
    static reader: zero, the true fiber being empty. This is the first of the
    two masses psl211_alldecks_constancy_false_close computes inline, named
    here because the quantitative core below takes both as its inputs. *)
(* The reader is moved by congr1 in term mode and never by a rewrite, as the
   two masses above are moved. *)
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

(** psl211_perdeck_static_mass_false — the same mass at chirality false: the
    reciprocal of the group order, the false fiber holding exactly one cut.
    This is the second of the two masses psl211_alldecks_constancy_false_close
    computes inline. *)
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

(** psl211_alldecks_perdeck_reading_ge — under the all-decks model's own cut
    law, the coalition psl211_perdeck_coalition of three of the twelve seats
    reads the two chiralities of the deal psl211_perdeck_deal at least the
    reciprocal 1/660 of the group order apart, in the sum of absolute
    differences. The two run arguments are named and not drawn, and no
    certificate occurs in the statement, so this is a fact about the model and
    the coalition's static reading alone. A distinguisher told to compare those
    two run arguments therefore has advantage at least 1/1320 at this model, the
    sum of absolute differences being twice the total variation distance of the
    literature. *)
Theorem psl211_alldecks_perdeck_reading_ge (R : realType) :
  (#|pgg_G psl211_M|%:R)^-1 <=
  var_dist
    (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
         psl211_perdeck_coalition (true, psl211_perdeck_deal))
       (sa_cut_dist (psl211_alldecks_sample R)))
    (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
         psl211_perdeck_coalition (false, psl211_perdeck_deal))
       (sa_cut_dist (psl211_alldecks_sample R))).
Proof.
rewrite (psl211_alldecks_cut_distE R).
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
exact: (eq_ind _ (fun z : R => z <= var_dist _ _)
  (leq_var_dist _ _ psl211_perdeck_view) _ Hval).
Qed.

(** psl211_alldecks_input_distinguishability — the all-decks model is input
    distinguishable at 1/660: the coalition and the pair of run arguments above
    witness the existential the framework's proposition asks for. It is the
    quantitative negation of input indistinguishability at this model and it
    certifies no security property; what a coalition of at most five of the
    twelve seats learns about the chirality when the deck description is drawn
    is psl211_alldecks_static_indep, exactly nothing, and the two facts stand
    under different quantifiers over the run argument, one drawing it and one
    fixing two of its values. *)
Theorem psl211_alldecks_input_distinguishability (R : realType) :
  InputDistinguishabilityPropAt (psl211_alldecks_sample R)
    ((#|pgg_G psl211_M|%:R)^-1).
Proof.
exists psl211_perdeck_coalition, (true, psl211_perdeck_deal),
  (false, psl211_perdeck_deal); split.
- exact: psl211_perdeck_coalition_below_k.
- exact: (psl211_alldecks_perdeck_reading_ge R).
Qed.

(** psl211_alldecks_indistinguishability_number_ge — every number at which an
    input-indistinguishability program over the all-decks model states its
    proposition is at least 1/660, whatever the program's certificate. The
    proposition bounds the distance between the readings of every two run
    arguments and the theorem above exhibits two whose distance reaches 1/660.
    This constrains the number a program publishes, where
    psl211_alldecks_no_small_eps_cert constrains the certificate's own marginal
    bound; the second follows from the general form of the tail lemma at the
    certificate's own number, and neither is edited by the other. A certificate
    whose ideal cut sits further than half of 1/660 from the group-uniform law
    is untouched by both, and it still publishes a number of at least 1/660. *)
Corollary psl211_alldecks_indistinguishability_number_ge (R : realType)
    (cert : IndistinguishabilityCert (psl211_alldecks_sample R)) (c : R) :
  IndistinguishabilityPropAt cert c -> (#|pgg_G psl211_M|%:R)^-1 <= c.
Proof.
move=> Hprop.
exact: (indistinguishability_number_ge_of_input_distinguishability
  (psl211_alldecks_input_distinguishability R) Hprop).
Qed.

Print Assumptions psl211_alldecks_perdeck_reading_ge.
Print Assumptions psl211_alldecks_indistinguishability_number_ge.
