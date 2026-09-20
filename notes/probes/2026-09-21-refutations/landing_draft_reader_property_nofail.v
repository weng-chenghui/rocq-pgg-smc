(* The first recorded rejection of the landing, written without Fail so the
   kernel's message is printed once and can be quoted in the checks file. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From refuteprobe Require Import landing_draft_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section reader_property.
Variable r : PublishedObstruction.
Check (security_property_of r).
End reader_property.
