(* Audit round 2, question 2: is encoded a global keyword in a file requiring
   the extended surface?  A keyword cannot be a binder name. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset reals.
From infotheo Require Import fdist.
From pgg_smc Require Import pgg_analysis_status pgg_instance.
From pgg_smc Require Import pgg_analysis_manifest.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.

Definition kw_encoded (encoded : nat) : nat := encoded.
