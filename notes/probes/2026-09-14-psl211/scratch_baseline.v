(* scratch_baseline: the axiom floor of transitivity_privacy.v itself, so the
   probes' Print Assumptions output can be read against a baseline rather than
   against zero. *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_reconstruct Require Import transitivity_privacy.

Print Assumptions inde_prod_fst.
Print Assumptions ttrans_view_indep_gen.
Print Assumptions ttrans_view_indep_alldecks.
Print Assumptions profile_view_indep.
