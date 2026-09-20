(* Probe, 2026-09-21. Question: do the three lemmas the manifest's twelfth
   path needs reach anything above psl211_models.v?

   The file states the two masses and the raw inequality with their production
   proofs verbatim and requires no Tableau file, no pgg_analysis_manifest and
   no pgg_analysis_status. It compiles against production's load path. A green
   compile says the three can sit below the manifest, so psl211_analysis.v can
   alias the inequality and the manifest can name that alias without the
   Require cycle pgg_tableau -> pgg_analysis_manifest -> psl211_analysis ->
   psl211_reading_constancy -> pgg_tableau. *)

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

Local Notation seatT :=
  ('I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1).
Local Notation cardT :=
  ('I_(pgg_N' (mp_M (instance_profile psl211_algebra))).+1).
Local Notation cutT := (pgg_gT psl211_M).
Local Notation viewT := ({ffun seatT -> cardT}).

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
    differences. *)
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

(* The positivity of the number, by the one-line field argument the framework's
   positivity conjunct will need at this model. *)
Lemma probe_psl211_perdeck_number_gt0 (R : realType) :
  0 < (#|pgg_G psl211_M|%:R)^-1 :> R.
Proof. by rewrite invr_gt0 ltr0n; exact: psl211_G_pos. Qed.

Print Assumptions psl211_alldecks_perdeck_reading_ge.
