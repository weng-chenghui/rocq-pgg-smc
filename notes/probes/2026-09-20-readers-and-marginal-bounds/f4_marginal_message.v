(* PROBE: the same command as the Fail guard at the end of r_marginals.v,
   without the Fail, so the rejection message is read. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.
From pgg_smc Require Import s5_profile s5_run s5_mixing s5_exec s5_models.
From pgg_smc Require Import five_card_group five_card_program five_card_kim.
From pgg_smc Require Import five_card_exec five_card_models five_card_mixing.
From pgg_smc Require Import five_card_tableau_sampled.
From readersprobe Require Import r_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.


From readersprobe Require Import r_marginals.

Check (fun (R : realType) (s : 'I_5) =>
  (five_card_repeated_endpoint_as_marginal R s
     : @SeatMarginalPropAt R five_card_algebra five_card_params
         (amf_sample kim_centi_family R tt) s (fdist_uniform (card_ord 5))
         (2%:R^-40))).
