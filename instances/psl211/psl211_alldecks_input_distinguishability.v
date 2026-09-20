(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_alldecks_input_distinguishability: how far apart a coalition reads  *)
(*                                           the two chiralities of one deal  *)
(*                                                                            *)
(* Under the all-decks model's own cut law the coalition                      *)
(* psl211_perdeck_coalition of three of the twelve seats reads the two        *)
(* chiralities of the deal psl211_perdeck_deal 1/660 apart, in the sum of     *)
(* absolute differences. The attack model is a static coalition below the     *)
(* privacy threshold reading its own endpoints at two named run arguments,    *)
(* and that number is what the twelve-card chirality instance's limitation is *)
(* stated at.                                                                 *)
(*                                                                            *)
(* Position. The analysis manifest records that limitation as one of its      *)
(* paths. A path names facade aliases alone, a facade aliases the instance    *)
(* cone, and the framework that phrases a limitation requires the manifest,   *)
(* so the inequality is stated here, below the facade, and everything said    *)
(* about certificates and published programs over it stays in                 *)
(* instances/psl211/psl211_reading_constancy.v. No certificate, no program    *)
(* and no path occurs in this file.                                           *)
(*                                                                            *)
(* In a proof script below a leading C is a fiber cardinality, U a mass at    *)
(* the group-uniform law, E a reader identification and H every other named   *)
(* fact; a t or f suffix names the chirality the quantity is taken at.        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_perdeck_static_mass_true                                          *)
(*                           == the group-uniform cut gives the reading       *)
(*                              psl211_perdeck_view mass zero at chirality    *)
(*                              true                                          *)
(*   psl211_perdeck_static_mass_false                                         *)
(*                           == and mass 1/660 at chirality false             *)
(*   psl211_alldecks_perdeck_reading_ge                                       *)
(*                           == three seats read the two chiralities of one   *)
(*                              deal at least 1/660 apart under the model's   *)
(*                              own cut law                                   *)
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
From pgg_reconstruct Require Import design_privacy algebraic_rigidity.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import psl211_group psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_exec.
From pgg_smc Require Import psl211_endpoints psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_blocks psl211_closure.

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

(** viewT — a reading, the card a coalition's seats see at each seat. *)
Local Notation viewT := ({ffun seatT -> cardT}).

(******************************************************************************)
(*     How far apart the two chiralities of one deal are read                 *)
(******************************************************************************)

(** psl211_perdeck_static_mass_true — the mass the group-uniform cut gives the
    reading psl211_perdeck_view at chirality true, taken at the framework's own
    static reader: zero, the true fiber being empty. It is the first of the two
    masses psl211_alldecks_constancy_false_close computes inline, named here
    because the quantitative core below takes both as its inputs. *)
(* The reader is moved by congr1 in term mode and never by a rewrite, as it is
   moved in that lemma. *)
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
    reciprocal of the group order, the false fiber holding exactly one cut. It
    is the second of the two masses psl211_alldecks_constancy_false_close
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
    a coalition's static reading alone. A distinguisher told to compare those
    two run arguments therefore has advantage at least 1/1320 at this model,
    the sum of absolute differences being twice the total variation distance
    of the literature. *)
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
