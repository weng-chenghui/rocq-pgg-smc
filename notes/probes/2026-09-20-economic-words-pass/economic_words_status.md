# Economic-metaphor comment pass: status

**All 34 editable files done.** 119 changed passages. 5 literal uses kept.
Both recorded residues done.

Artifacts in this scratchpad:
- `frozen_occurrences.md` - 49 occurrences, 12 frozen files, UNCHANGED text
- `economic_words_changes.md` - all 119 passages: file:line (HEAD), before,
  after, declaration checked, table row
- `econ_scan.py` (scanner), `econ_apply.py` (applier), `edits_b1..b10.py`
- `econ_closure.py`, `econ_compile_order.txt`, `econ_compile.log`

## Verification

1. Token check: `token_check.py` run after every batch on every touched file.
   All OK (comment-stripped token stream identical to HEAD:6a20f7d).
2. Final scan of the editable set: 5 occurrences left, all literal:
   - `instances/pgl27/tableau/pgl27_tableau_checks.v` x3, `costs 78.7 s`,
     `costs 24.3 s`, `costs 24.1 s` (measured compile times, stated in
     seconds; the table permits keeping `costs` for these)
   - `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v` x1,
     `erefl takes costs 147 s` (was `spent 147 s`; changed to the table's own
     sanctioned literal verb)
   - `instances/s5/s5_mixing.v` x1, `costs minutes to typecheck` (measured
     elaboration time of a table of six-digit int literals)
3. Compile: reverse closure of the 35 touched files over both logical paths
   = 94 files; the closure meets **no** frozen file. Running single-file
   through `compile_prod.py` in topological order.

## Files done (34, all)

five_card_tableau_analysis_bridged, pgl27_tableau_analysis_bridged,
psl211_reading_constancy, five_card_exec, pgl27_exec, s5_exec,
psl211_alldecks, psl211_tableau_observed, s5_mixing, pgg_tableau,
pgg_mixing, five_card_mixing, pgl27_spectral, pgl27_tableau_checks,
psl211_models, pgg_tableau_syntax, psl211_mixing,
psl211_tableau_analysis_bridged, mutual_info_recoding, var_dist_supp,
pgg_tableau_arm_relations, pgl27_mixing, pgl27_profile,
pgl27_word_privacy, invariant_profiler, var_dist_joint_law,
pgg_raag_clique, den_boer_run, five_card_analysis, pgl27_profile_privacy,
psl211_tableau_executable, s5_tableau_analysis_bridged, pgg_functionality,
pgg_schreier.
Plus, for the two residues: pgl27_tableau_algebraic (a).

## Not done

Nothing. No commit made.
