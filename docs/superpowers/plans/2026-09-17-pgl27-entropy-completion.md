# PGL(2,7) view entropy completion plan

Date: 2026-09-17. Spec: `notes/20260915-pgl27-view-census-entropy-design.md`.
Probe evidence: `notes/probes/2026-09-15-pgl27-view-entropy/` (never deleted,
never imported by permanent source).

## Flow

```
flow pgl27_view_mutual_infoE            // known about I(secret ; view C): nothing
object census := pgl27_collisions S / 336                    // nat ratio, S in {harmonic, equianharmonic, five, six, seven}
change census -> shuffles  by pgl27_table_perm_{mem,inj,surj}, pgl27_view_codesE     // same ratio over pgg_G pgl27_M; cost 0
step   count -> event      by pgl27_ambiguous_probabilityE   [needs uniq code_views] // Pr[view in ambiguous S] = c(S)/336
step   inj -> posterior    by support_posterior_entropy_ambiguousE                   // H[secret | view = v] = [v ambiguous], v reachable
eval   representative      by mutual_info_binary_ambiguityE + pgl27_secret_uniform   // I at rep S = 1 - c(S)/336
step   rep -> orbit        by coalition view transport [NEW] + subset orbit lemmas   // every C with 4 <= |C| <= 7
join   |C| <= 3            by pgl27_view_indep                                       // I = 0
join   |C| = 8             by pgl27_view_leakage_le + I <= H(secret) = 1             // I = 1
final  pgl27_view_mutual_infoE                                // every C
post   outside: I = 0 <-> |C| <= 3; value 5/7 at pgl27_leak_coalition
```

No monad. Category-like composition of exact equalities in Prop. Every step is
unconditional, so the loss is zero on every line.

## Build rules (all tasks)

1. Never run a full `make`. `instances/psl211/psl211_endpoints.v` has an
   uncommitted edit from another session and costs 900 s and 17 GB.
   Build one target at a time: `make instances/pgl27/<file>.vo`.
2. Do not edit any existing file outside the list below. In particular do not
   touch `lib/proba_entropy_ext.v`, `reconstruct/transitivity_privacy.v`,
   `instances/pgl27/pgl27_secrecy.v`, `instances/pgl27/pgl27_mixing.v`,
   `instances/pgl27/pgl27_orbit.v`, or anything under `protocol/` or
   `instances/psl211/`. Editing them invalidates expensive `.vo` files.
3. Never delete anything under `notes/probes/`.
4. No `Admitted`, no `Axiom`, no import of a probe file.
5. Commit before replacing any working proof. Coordinator commits.

## Tasks

| # | Item | Deliverable | Depends |
|---|---|---|---|
| T0 | 2 | Branch `feat/pgl27-view-entropy`; commit `mutual_info_binary_ambiguityE` | none |
| T1 | 1 | `lib/support_posterior.v`: Section `support_posterior` copied from `posterior_entropy.v` | T0 |
| T2 | 1 | `instances/pgl27/pgl27_table_bridge.v`: C1 to C5 copied from `table_group_bridge.v`, mutation checks left in the probe | T0 |
| T3 | 1 | `instances/pgl27/pgl27_view_census.v`: shared definitions, C6, C7, C8 copied from `probe_view_definitions.v`, `view_collision_probability.v`, `ambiguous_probability.v`; generic `pgl27_ambiguous_probabilityE` made public | T2 |
| T4 | 1 | `instances/pgl27/pgl27_mutual_info.v`: posterior instantiation, `_memE` forms, `pgl27_secret_uniform` PROVED, four mutual-information equations with the closed values 5/7, 11/14, 25/28, 27/28; header rewritten | T1, T3 |
| T5 | 4 | `reconstruct/coalition_view_transport.v`: for g in G, the coalition view at `g @: C` shares the same mutual information with the dealt secret as the view at C | T0, parallel with T1 to T4 |
| T6 | 3 | `rep_seven`, `pgl27_views_uniq_seven` in the census file; seven-position probability 0, posterior entropy, mutual information 1 | T4 |
| T7 | 4 | pgl27 transport corollaries: every C of size 4 (split by `subset_class`), 5, 6, 7; `pgl27_seven_subset_orbit` | T5, T6 |
| T8 | 5 | `pgl27_view_mutual_infoE` for every C; `I = 0 <-> #|C| <= 3`; value 5/7 at `pgl27_leak_coalition`; header of `pgl27_secrecy.v` is NOT edited, the new file's header names the threshold theorems it joins | T7 |
| T9 | all | rocq-auditor style pass, `Print Assumptions` sweep, fixes, design note status update | T8 |

T7 and T8 live in a new file `instances/pgl27/pgl27_leakage_ramp.v`.
