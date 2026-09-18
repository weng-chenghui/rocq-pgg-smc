(* PROBE, notes/probes/2026-09-19-kim-tableau-sampled/kim_fidelity.v         *)
(* The assumption closure of every declaration the landing copy adds to      *)
(* instances/kim2025/five_card_rows.v. The repository baseline is the        *)
(* classical trio propositional_extensionality,                              *)
(* functional_extensionality_dep and constructive_indefinite_description,    *)
(* which an fdist-record statement carries throughout the tree. Any fourth   *)
(* name printed below is a finding.                                          *)

From kim_tableau_sampled_probe Require Import five_card_rows_landing.

Print Assumptions five_card_row_repeated_tableau.
Print Assumptions five_card_row_biased_tableau.
Print Assumptions five_card_row_repeated_prefixE.
Print Assumptions five_card_row_biased_prefixE.
Print Assumptions five_card_row_repeated_modelE.
Print Assumptions five_card_row_biased_modelE.
Print Assumptions five_card_row_repeated_at_manifest_level.
Print Assumptions five_card_row_biased_levelE.
Print Assumptions five_card_row_repeated_endpoint_lt.
Print Assumptions kim_centi_small.
Print Assumptions five_card_row_biased_leak_bound.
