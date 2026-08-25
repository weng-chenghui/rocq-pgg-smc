# Non-Abelian genus-1 AG recovery: contents and results (2026-07-01)

Index for the investigation into whether a non-Abelian, non-dihedral group can carry
algebraic-geometry-code `(k, T)` recoverability, or whether the `S_5` no-go theorems rule it
out. Entry point to the design, the worked example, the scripts, and the background.

## The question and the verdict

Question: is there a group with AG-code recoverability that is non-Abelian and not the trivial
dihedral case, or is this rejected by the theorems behind the `S_5` no-go?

Verdict: NOT rejected. The `S_5` no-go is `2`-transitivity on few points at genus `0`. Dropping
`2`-transitivity and moving to genus `1` escapes it. A concrete witness exists and is
machine-checked.

## Key results

- Witness: `E : y^2 = x^3 - x` over `GF(9)` (supersingular, char 3). Recovery group
  `Dic_3` (dicyclic, order 12, non-Abelian, non-dihedral, unique involution), realized as the
  point-stabilizer `Stab(T0)` of the secret `T0 = (0,0)`.
- Code: functional AG code `C_L(D)` for the divisor `D = O + (1,0) + (2,0)` (the size-3 group
  orbit). Parameters `[13, 3, 10]`, almost-MDS with defect `1 = g`, dual distance `3`.
- Secret sharing (Massey): secret at the fixed coordinate `T0`, twelve shares. Thresholds
  derived, not asserted: privacy `t = 1`, reconstruction `r = 4`, gap `2 = 2g`. A ramp, not a
  threshold scheme.
- Group action: `Dic_3` permutes the 13 coordinates, fixes the secret coordinate, and
  preserves the code as a pure permutation (no diagonal twist). Verified.
- Obstruction found and recorded: the existing scaffold `reconstruct/cover_genus1.v` is
  single-pole near-MDS (`n = k + g + 1`) and forces the recon-symmetry to fix both the pole and
  the secret, which on a genus-1 curve is an abelian two-point stabilizer. So it structurally
  cannot host this instance. Formalization needs a new divisor-based `L(D)` scaffold.

## Documents

- [[20260701-nonabelian-ag-recoverable-genus1-design]] — the design spec. Contains the
  obstruction chain (James, wreath, char-3 choice), the adversarial-audit outcome (Section 1a:
  object sound, scaffold-fit refuted, threshold semantics corrected), the deliverables, and the
  scope of the needed `L(D)` scaffold.
- [[20260701-nonabelian-ag-recoverable-genus1-worked-example]] — Deliverable A. The fully
  explicit example: field, curve, points, the `Dic_3` group, the divisor and Riemann-Roch
  basis, the `3 x 13` generator matrix, the concrete deal and recover of secret `s = w`, the
  thresholds, and the four verified properties of the group action.

## Scripts (plain Python 3, no external libraries)

- `ec_worked_example.py` — builds the whole scheme and checks it: points, orbits, generator
  matrix, minimum and dual distance, Massey thresholds, one deal/recover cycle, and the group
  action (permutation, secret-fixing, code-preserving, non-Abelian).
- `ec_spotcheck.py` — `#E(GF(9)) = 16`, the order-12 automorphism group fixing `O`,
  non-Abelian with a unique involution, orbits `{1, 3, 12}`.
- `ec_spotcheck2.py` — the affine placement: `E(GF(9))` order 16, `Stab(T0)` orbits, and that
  `O` sits in the size-3 orbit so the 13 evaluation points are all affine.
- `ec_pole_check.py` — the obstruction: for the single-pole model, the pole-and-secret-fixing
  subgroup is always abelian (max non-Abelian order `0`).
- `ec_coalition_profile.py` — the full security profile: for each coalition size, how many
  coalitions reconstruct versus learn nothing. Confirms `1`-private, reconstruction at `4`,
  mixed zone of width `2` at sizes `2` and `3`.
- `ec_tune_privacy.py` — privacy tuning: same curve, same `Dic_3`, same 13 points, divisor
  `m(O+T1+T2)` for `m = 1,2,3` gives privacy `t = 1,4,7` with gap fixed at `2`. Shows `t` is a
  divisor knob, not hardwired to the curve or group.

## Memory

- `project_ag_singlepole_abelian_obstruction` — the single-pole-forces-abelian obstruction and
  the divisor-orbit `L(D)` fix, with the verified witness parameters. In the user auto-memory.

## Background this builds on

- [[20260630-170155-s5nogo-james-submodule-report]] — the James Submodule Theorem framing and
  the obstruction/possibility/existence trichotomy.
- [[20260602_135732_nogo_escape_groups_security_ladder]] — which transitive groups escape and
  the Riemann-Hurwitz tension.
- [[20260606T143722Z-wreath7-failure-and-s5x5-comparison]] — the wreath incoherence (the
  non-Abelian generator was the recovery-breaker), the lesson that shaped this design.
- [[20260630-192036-bring-and-pgl-routes-rejected]] — the rejected `S_5` genus-0 PGL and
  Bring-curve routes.
- [[20260607T015612Z-concrete-recovery-mechanisms-survey]] — which repo recoveries are
  concrete versus shelved.

## Open next steps

- Commit these notes and scripts to the pgg-smc repo.
- Scope and build the divisor-based `L(D)` genus-1 Rocq scaffold (the object cannot use
  `cover_genus1.v`).
- Optional stronger-privacy variant: a higher-degree `Dic_3`-invariant divisor raises the
  privacy threshold at the cost of a larger generator matrix.
