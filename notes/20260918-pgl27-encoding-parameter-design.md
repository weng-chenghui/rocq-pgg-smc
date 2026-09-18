# PGL(2,7): the deck pair as a parameter of the instance

Date: 2026-09-18. Branch `feat/pgl27-encoding-parameter`. Plan:
`docs/superpowers/plans/2026-09-18-pgl27-encoding-parameter.md`. Probe, audits
and rulings: `notes/probes/2026-09-18-pgl27-encoding-parameter/`.

## Problem

The exact leakage theorem of 2026-09-17 was a statement about one fixed deck
pair, `orbit_encode`. The values above the privacy threshold and the smallest
coalition size with one full bit depend on the pair. Script evidence
(`notes/probes/2026-09-18-pgl27-encoding-dependence/`) finds four leakage
profiles over the 3456 pairs up to shuffling. The framework had one profile
`pgl27_M` (encoding-free) and one encoding. The deck pair is now a record
parameter of the leakage chain and of the executed trace, instantiated twice.

## Default pair (decision of 2026-09-18, evening)

`orbit_encode` of `pgl27_orbit.v` now deals the `_r5` pair (true deck
`0 1 2 4 3 5 7 6`). The Tableau row of `pgl27_rows.v`,
`deal orbit_scheme encode orbit_encode ...`, is textually unchanged and tells
the `_r5` story. `_r7` is the comparison pair, defined by explicit decks in
`pgl27_encoding_r7.v` with class recovery through heart-set equality with
`orbit_encode`. The swap rebuilt 33 files (all of `instances/pgl27/`, the
three rows files, `manifest/`). One downstream proof changed:
`pgl27_six_reveal_ambiguous` in `pgl27_recovery.v` needs two valid decks of
opposite classes differing in two positions only, which the new default pair
is not; its witness is now a local deck `0 1 2 4 3 5 6 7`. Statement unchanged.
Commits fcb6173, d7ce84d, 3317b91.

## The two pairs

| tag   | secret false      | secret true       | collisions 4h, 4e, 5, 6, 7 | values 4h, 4e, 5, 6, 7 | recovery threshold |
|-------|-------------------|-------------------|----------------------------|------------------------|--------------------|
| `_r5` (default, `orbit_encode`) | `0 1 2 3 4 5 6 7` | `0 1 2 4 3 5 7 6` | 48, 72, 0, 0, 0 | 6/7, 11/14, 1, 1, 1 | 5 |
| `_r7` (comparison) | `0 1 2 3 4 5 6 7` | `0 1 2 4 3 5 6 7` | 96, 72, 36, 12, 0 | 5/7, 11/14, 25/28, 27/28, 1 | 7 |

Hearts are the cards 0 to 3. Both true decks hold them at positions
{0,1,2,4}, so `orbit_class` returns the same secret on either pair
(`pgl27_compare_classE`, proved through `pgl27_r5_hearts`). The pairs differ
only in where the cards 6 and 7 sit, which the decoder never reads and a
coalition of enough positions does. The minimum above the privacy threshold
is 5/7 on the harmonic class at `_r7` and 11/14 on the equianharmonic class
at `_r5`. At a fixed pair, "the view determines the secret" is "collision
count zero", so the recovery threshold of a fixed pair is the smallest size
with one full bit. The paper's r = 7 is the all-decks statement
`pgl27_seven_reveal_class`, which is encoding-free and holds for both pairs.

## Files (import order)

| file | content |
|------|---------|
| `pgl27_leakage_census.v` | group table, subsets, orbits, representatives; `code_views code b S`, `pgl27_collisions code S` take the code table |
| `pgl27_encoding.v` | `Record pgl27_encoding` (`enc_deck`, `enc_code`, `enc_deck_ok`, `enc_classK`, `enc_codeE`), `enc_code_nthE`, `pgl27_enc_view R e C`, `pgl27_enc_view_indep`, `pgl27_enc_view_leakage_le` |
| `pgl27_encoding_r5.v` (default, from `orbit_encode`), `pgl27_encoding_r7.v` (explicit `deck_r7`, `pgl27_r7_hearts`, `pgl27_r7_classK`) | code tables, the instances, per-pair census facts (`pgl27_r5_views_uniq_*`, `pgl27_r5_collisions_*`, same for `_r7`), headers list the decks |
| `pgl27_trace_encoding.v` | `pgl27_enc_player_trace`, `pgl27_enc_coalition_trace`, `pgl27_enc_coalition_traceE` (trace = view, no premise), `pgl27_enc_coalition_trace_secrecy`, `pgl27_enc_run_recovers_class`, `pgl27_aprocs_abs_terminates`, `pgl27_r5_coalition_traceE` (agreement with the manifest-pinned trace) |
| `pgl27_table_bridge.v`, `pgl27_view_census.v`, `pgl27_mutual_info.v` | the chain over `e`: agreement, per-secret injectivity, `pgl27_ambiguous_probabilityE`, `pgl27_view_mutual_info_ambiguityE` |
| `pgl27_leakage_transport.v` | encoding-free position facts; over `e`: `pgl27_enc_view_mutual_info_imset`, `_le1`, `_le3E`, `_k4E` to `_k7E`, `pgl27_enc_view_mutual_info1_card_ge` |
| `pgl27_leakage_r5.v` (over `pgl27_view R C` and the manifest-pinned `pgl27_coalition_trace R C`) | `pgl27_r5_viewE`, `pgl27_r5_view_mutual_infoE`, `_eq0`, `_k4_lt1`, `_leak_coalitionE` (6/7), `_card_ge4` (11/14), `pgl27_r5_view_determines` (5), `pgl27_r5_trace_mutual_infoE`, `pgl27_r5_trace_mutual_info_eq0`, `pgl27_r5_trace_determines` |
| `pgl27_leakage_r7.v` (over `pgl27_enc_view R pgl27_encoding_r7 C` and `pgl27_enc_coalition_trace`) | `pgl27_r7_view_mutual_infoE`, `_eq0`, `_k6_lt1`, `_leak_coalitionE` (5/7), `_card_ge4` (5/7), `pgl27_r7_view_determines` (7), `pgl27_r7_trace_mutual_infoE`, `pgl27_r7_trace_mutual_info_eq0`, `pgl27_r7_trace_determines` |
| `pgl27_encoding_compare.v` | `pgl27_compare_heart_setE`, `_classE`, `_le3E`, `_equianharmonicE`, `_harmonicE`, `_k5E`, `_k6E`, `pgl27_compare_recovery_thresholdE` |

Edited by the default swap: `pgl27_orbit.v` (the deck), `pgl27_recovery.v`
(witness). Untouched: `pgl27_secrecy.v`, `pgl27_trace.v`, `pgl27_run.v`,
`pgl27_exec.v`, `pgl27_analysis.v`, `manifest/`, the rows. The manifest pins
`pgl27_coalition_trace`; the `_r5` trace theorems are stated over it.

## Flow (final)

```
flow leakage_of_encoding e            (e = r7 or r5)     // known about the secret: nothing
object run    := interpreter run dealing deck e(s) at cut g   [pgl27_procs_deck]   // one executed trace per seat
change run -> card    by pgl27_procs_deck_abs, pgl27_full_p0..p7                    // seat i's trace = card e(s)[g i]
change cards -> view  by pgl27_enc_coalition_traceE                                 // coalition trace = coalition view, equality of random variables
join   |C| <= 3       by ttrans_view_indep_gen        [needs uniq (e s)]            // I = 0
extern census := collisions of e over the 336-row table                             // enters by pre-composition through pgl27_ambiguous_probabilityE
change census -> view by enc_codeE and the table bridge                             // Pr[ambiguous view] = m/336
eval   representative by pgl27_view_mutual_info_ambiguityE                          // I = 1 - m/336 at five representatives
step   rep -> orbit   by pgl27_enc_view_mutual_info_imset + subset orbit lemmas     // every C with 4 <= |C| <= 7
join   |C| >= r(e)    by pgl27_enc_view_mutual_info1_card_ge                        // I = 1; r7: 7, r5: 5 (two bounds meet by le_anti)
final  pgl27_r5_view_mutual_infoE (default) / pgl27_r7_view_mutual_infoE, then the trace twins
post   pgl27_encoding_compare.v: decoder equality, values side by side, thresholds 7 and 5
```

No monad: a theory parametrised by the record, composed from exact equalities.

## Evidence levels

- Rocq, for both pairs: every statement above. Assumptions: the three boolp
  axioms on anything typed against an `fdist`; `pgl27_compare_classE`,
  `pgl27_enc_run_recovers_class`, `pgl27_enc_run_terminates` closed.
- Rocq, encoding-free: privacy up to three positions, transport, the
  all-decks recovery threshold seven.
- Script only: the classification into four profiles, minimality of `_r7`
  among pairs, non-existence of a pair with threshold four, all-decks values.

## Renames since `main` (for the paper footnotes)

| old (main 82352e3) | new |
|---|---|
| `pgl27_leakage_ramp.v` | `pgl27_leakage_r7.v` |
| `code_deal`, `code_tau` | `code_table_r7` (in `pgl27_encoding_r7.v`); `code_tau` gone |
| `code_views b S`, `pgl27_collisions S` | `code_views code b S`, `pgl27_collisions code S` |
| `pgl27_collisions_{harmonic,equianharmonic,five,six,seven,three}` | `pgl27_r7_collisions_*` in `pgl27_encoding_r7.v` |
| `pgl27_views_uniq_*` | `pgl27_r7_views_uniq_*` |
| `pgl27_collisions_*_neq`, `pgl27_collision_ratio_*` | deleted (unused; the closed forms carry the values) |
| `pgl27_code_deal_orbit_encodeE` | `enc_code_nthE` |
| `pgl27_conditional_view_inj_*`, `pgl27_ambiguous_probability_*E`, `pgl27_noncollision_ratio_*`, `pgl27_reachable_view_entropy_*E`, `pgl27_view_mutual_info_{harmonic,...,seven}E` | deleted; the generic lemmas with the census premises replace them |
| `pgl27_view_mutual_info_imset`, `_le1`, `_le3E`, `_k4E`..`_k7E` | `pgl27_enc_view_mutual_info_*` in `pgl27_leakage_transport.v` |
| `pgl27_view_mutual_infoE`, `_eq0`, `_leak_coalitionE`, `_ge4` (values of the old default pair) | `pgl27_r7_view_mutual_infoE`, `_eq0`, `_leak_coalitionE`, `_card_ge4`, now over `pgl27_enc_view R pgl27_encoding_r7`; the statements over `pgl27_view` are the `_r5` ones with the `_r5` values |
| `pgl27_view_mutual_info_ge7E` | `pgl27_r7_view_determines` (`I == 1` iff `7 <= #|C|`); default pair: `pgl27_r5_view_determines` (5) |
| `orbit_encode true = 0 1 2 4 3 5 6 7` | `orbit_encode true = 0 1 2 4 3 5 7 6` |

Paper lines to update: `paper-wadt2026/main.tex:1378-1399` and
`candidate-main.tex:1430-1452` cite `pgl27_collisions` (arity changed), give
the old default pair's numbers 96, 72, 36, 12 and values 5/7, 25/28, 27/28
(the default is now 48, 72, 0, 0, 0 and 6/7, 11/14, 1), and call the identity
`I = 1 - m/336` and the orbit extension pen-and-paper; both are theorems now.
The figure of the two orbit encodings and any text saying the true deck swaps
only positions 3 and 4 must show `0 1 2 4 3 5 7 6`. `instances/pgl27/pgl_leakage_targets.py` names the old
lemmas.

## Out of scope

A second `ThresholdScheme`/`ReconPlug`/`ExecutionPlug`; word-shuffle privacy
for `_r5`; manifest rows for `_r5`; a third pair would need `orbit_classE` of
`pgl27_orbit.v` made non-Local (class recovery for `_r5` goes through
heart-set equality with `_r7`).
