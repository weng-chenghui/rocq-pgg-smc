(* The certify statement with its evidence written bare, the spelling the
   surface no longer has.  The program is s5_rand_published with by taken
   out of its certify statement and nothing else changed.

   The parser refuses it, and f0_fail_catches_parse.v measures that Fail
   does not catch a parse error, so the boundary cannot be recorded as a
   compiled Fail sentence in the instance's checks file.  This file is
   compiled once without a guard and its message is kept beside it, in
   r1_bare_certify.msg, and quoted in the comment the checks file carries. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset.
From mathcomp Require Import matrix zmodp ssralg ssrnum reals.
From infotheo Require Import fdist proba entropy.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import s5_exec s5_models.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import s5_tableau_observed s5_tableau_sampled.
From pgg_smc Require Import s5_tableau_analysis_bridged.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition r1_bare_certify : Published :=
  s5_rand_sampled
    certify ExactIndependence s5_rand_exact_witness
    |> publish StaticExecutedOnly assuming (AcceptsAxioms [:: AxS5GroupOrder]).
