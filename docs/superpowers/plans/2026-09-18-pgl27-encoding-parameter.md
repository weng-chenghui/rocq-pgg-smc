# PGL(2,7): the deck pair as a parameter of the instance (`_r7` and `_r5`)

Date: 2026-09-18. Branch: `feat/pgl27-encoding-parameter`. Coordinator: main
session. All `.v` edits: rocq-prover subagents on Opus.

## Problem

The exact leakage theorem of `pgl27_leakage_ramp.v` is a statement about one
fixed pair of decks, `orbit_encode`. The values above the privacy threshold and
the smallest coalition size with one full bit (`r_info`) depend on that pair.
The script evidence in `notes/probes/2026-09-18-pgl27-encoding-dependence/`
finds four leakage profiles over the 3456 pairs. The repository's pair has
`r_info = 7`. A pair with `r_info = 5` behaves like a sharp threshold above the
four-position ramp and is the wanted comparison. The framework has one
`MonodromyProfile` (`pgl27_M`, encoding-free) and one encoding. The plan makes
the encoding a parameter of the third-layer chain and of the executed trace,
and instantiates it twice.

## Decks

| tag   | secret false        | secret true         | collisions 4h, 4e, 5, 6, 7 | r_info |
|-------|---------------------|---------------------|----------------------------|--------|
| `_r7` | `0 1 2 3 4 5 6 7`   | `0 1 2 4 3 5 6 7`   | 96, 72, 36, 12, 0          | 7      |
| `_r5` | `0 1 2 3 4 5 6 7`   | `0 1 2 4 3 5 7 6`   | 48, 72, 0, 0, 0            | 5      |

`_r7` is `orbit_encode`. Both true decks put the hearts at positions
`{0,1,2,4}`, so the decoder `orbit_class` cannot tell the two pairs apart.

## Flow sketch

```
flow leakage_of_encoding e            (e = r7 or r5)     // known about the secret: nothing
object run    := interpreter run dealing deck e(s) at cut g   [pgl27_procs_deck]   // one executed trace per seat
change run -> card    by pgl27_procs_deck_abs, pgl27_full_p0..p7                    // seat i's trace = card e(s)[g i]; cost 0
change cards -> view  by coalition_trace_E, generic in e                            // coalition trace = coalition view, as random variables
join   |C| <= 3       by ttrans_view_indep_gen        [needs deck_ok (e s)]         // I = 0 up to three positions
object census := collisions of e over the 336-row table                             // five nat counts, one per representative
change census -> view by table bridge + agreement of e with its nat table           // Pr[ambiguous view] = m/336
eval   representative by pgl27_view_mutual_info_ambiguityE, generic in e            // I = 1 - m/336 at five representatives
step   rep -> orbit   by coalition_view_mutual_info_imset + subset orbit lemmas     // every C with 4 <= |C| <= 7
join   |C| = 8        by monotonicity + I <= H(secret) = 1                          // every C
final  view closed form for e, then the same closed form for the EXECUTED trace     // I(secret ; executed coalition trace C), every C
post   outside the flow: r_info(e), r7 versus r5, decoder equality
```

Monad verdict: no monad. A theory parametrised by an encoding record, composed
from exact equalities in Prop; every line is unconditional and costs zero.

Interfaces: interpreter through `pgl27_procs_deck_abs` and `pgl27_full_p*`;
threshold privacy through `ttrans_view_indep_gen`; infotheo through
`centropy1_uniform_over_set` inside `lib/support_posterior.v`; the group table
through `pgl27_table_bridge.v`.

## Build rules (unchanged from the 2026-09-17 plan)

- NEVER run a full `make`. Single targets only:
  `make -f Makefile.rocq -j1 instances/pgl27/<file>.vo`.
- Before building, check the closure: `make -f Makefile.rocq -n -j1 <target>`.
  If it lists anything under `protocol/`, `instances/psl211/`, or
  `pgl27_mixing`, `pgl27_secrecy`, `pgl27_orbit`, `pgl27_trace`, STOP and
  report.
- After `_CoqProject` edits:
  `rocq makefile -f _CoqProject -o Makefile.rocq` and
  `rocq dep -vos -dyndep var -f _CoqProject > .Makefile.rocq.d`.
- Do not edit: `lib/proba_entropy_ext.v`, `pgl27_orbit.v`, `pgl27_secrecy.v`,
  `pgl27_mixing.v`, `pgl27_trace.v`, `pgl27_run.v`, `pgl27_exec.v`,
  `reconstruct/transitivity_privacy.v`, anything under `protocol/` or
  `instances/psl211/`.
- zsh does not word-split variables. Use `bash -c` for multi-flag commands.
- Never delete anything under `notes/probes/`.
- Commit before writing `Admitted`. No `Admitted` in a final commit.
- Banned words: apex, gate/gated/gating, posit/posited. No metaphor words.
- Statement comments: one sentence fact, one sentence domain position.

## Tasks

| id | task | owner | depends |
|----|------|-------|---------|
| P0 | Probe: vm_compute the `_r5` collisions (48, 72, 0, 0, 0) and uniq views at the five representatives; prove the executed-trace lemma at an arbitrary deck; check that the chain's generic steps typecheck over an encoding record. Files under `notes/probes/2026-09-18-pgl27-encoding-parameter/`. | rocq-prover (Opus) | none |
| A0 | Independent audit of the flow sketch against the real files. Verdict GO / NO-GO with fixes. | rocq-auditor (Opus) | none |
| E1 | `pgl27_encoding.v`: record `pgl27_encoding` (decks, deck_ok, class recovery, nat table, agreement). | rocq-prover | P0, A0 |
| E2 | `pgl27_encoding_r7.v`, `pgl27_encoding_r5.v`: the two instances, headers listing the decks. | rocq-prover | E1 |
| G1 | Generalise `pgl27_leakage_census.v` (collisions take the deal), `pgl27_table_bridge.v`, `pgl27_view_census.v`, `pgl27_mutual_info.v` over the record. | rocq-prover | E1 |
| T1 | `pgl27_trace_encoding.v`: executed trace at an encoding, seat trace = dealt card, coalition trace = coalition view, run recovers the class. | rocq-prover | E1 |
| R7 | `pgl27_leakage_r7.v` (rename of `pgl27_leakage_ramp.v` + the `_r7` values): vm_compute facts, view closed form, executed-trace closed form, zero iff at most three, r_info = 7. | rocq-prover | G1, T1, E2 |
| R5 | `pgl27_leakage_r5.v`: same for `_r5`; closed form 0, 6/7 or 11/14, 1, 1, 1; r_info = 5. | rocq-prover | G1, T1, E2 |
| C1 | `pgl27_encoding_compare.v`: same heart positions hence same decoded secret; r_info 7 versus 5; possibilistic r = 7 for both. | rocq-prover | R7, R5 |
| S1 | Style audit per changed file, Print Assumptions, fixes. | rocq-auditor + rocq-prover | C1 |
| D1 | Design note, Obsidian note, old/new name table for the paper footnotes. | main session | S1 |

## Out of scope

A second `ThresholdScheme`/`ReconPlug`/`ExecutionPlug`; word-shuffle privacy
for `_r5`; manifest rows; the four-profile classification and the
non-existence of `r_info = 4` stay script evidence.
