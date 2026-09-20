(* PROBE: R10. The axiom footprint of every restated proposition, beside the
   footprint of the theorem each one cites, so a reader can see that restating
   a theorem at a reader adds nothing. *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import order ssrnum ssralg boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_instance pgg_sample_adapter pgg_tableau.
From pgg_smc Require Import pgl27_word_privacy pgl27_models.
From pgg_smc Require Import s5_models.
From pgg_smc Require Import five_card_tableau_sampled.
From readersprobe Require Import r_framework r_pgl27 r_marginals.

(* R4 and its cited theorem. *)
Print Assumptions pgl27_word_trace_indistinguishability_at_reader.
Print Assumptions pgl27_word_trace_indistinguishability.

(* R5: the same proposition at the canonical reader, once by post-processing
   and once through the framework's own composition law. *)
Print Assumptions pgl27_word_reading_indistinguishability_by_postprocessing.
Print Assumptions pgl27_word_reading_indistinguishability_by_certificate.

(* R3, the post-processing law itself. *)
Print Assumptions reader_indistinguishability_postprocessing.

(* R6 at the trace reader, and R7. *)
Print Assumptions pgl27_trace_exact_at_reader.
Print Assumptions pgl27_exec_trace_link.

(* R8 and the two theorems it restates. *)
Print Assumptions s5_exec_endpoint_bound_as_marginal.
Print Assumptions s5_exec_endpoint_bound.
Print Assumptions five_card_repeated_endpoint_as_marginal.
Print Assumptions five_card_repeated_endpoint_lt.

(* R9. *)
Print Assumptions seat_marginal_at_two.
