(* Probe diagnostic, 2026-09-19. Prints the two decks side by side.          *)
(* Recorded output, 2026-09-19:                                              *)
(*   psl211_alldecks_row (true,  psl211_perdeck_deal) = [:: 0;1;2;3;4;10]     *)
(*   psl211_alldecks_row (false, psl211_perdeck_deal) = [:: 0;1;2;3;4;11]     *)
(*   psl211_rep_list true  = [:: 2;3;5;7;8;9]                                 *)
(*   psl211_rep_list false = [:: 0;1;3;7;10;11]                               *)
(*   psl211_perdeck_seq true  = [:: 0;1;2;3;4;6;7;8;9;10;5;11]                *)
(*   psl211_perdeck_seq false = [:: 0;1;2;3;4;6;7;8;9;10;11;5]                *)
(* Block index zero of either chirality's table is therefore not the          *)
(* representative row the encoder deals on, so the encoder deck is not the    *)
(* deck the all-decks dealer lays at psl211_perdeck_deal and the all-decks    *)
(* refutation does not transport to the dealt mode by that route.             *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import psl211_group psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_exec.
From pgg_smc Require Import psl211_endpoints psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_blocks psl211_closure.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Eval vm_compute in psl211_alldecks_row (true, psl211_perdeck_deal).
Eval vm_compute in psl211_alldecks_row (false, psl211_perdeck_deal).
Eval vm_compute in psl211_rep_list true.
Eval vm_compute in psl211_rep_list false.
Eval vm_compute in psl211_perdeck_seq true.
Eval vm_compute in psl211_perdeck_seq false.
