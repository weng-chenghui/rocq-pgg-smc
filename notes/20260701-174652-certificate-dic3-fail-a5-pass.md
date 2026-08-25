# Verification certificates: Dic_3 (FAIL) vs A5=PSL(2,5) on 6 points (PASS)

Date: 2026-07-01

Runs of the corrected shuffle-matters template
([[20260701-173005-shuffle-matters-verification-template]]) on two candidates. Script:
`notes/ec_verify_shuffle_matters.py`. Both certificates are exhaustive computations over the full
group and all coalitions, not sampling.

## Candidate 1: Dic_3 hearts on 12 points  ->  FAIL

Tuple: G = Dic_3 (order 12) on the 12-point orbit; deck 3 hearts / 9 clubs; secret bit = "are the
hearts a rotation triple (a C_3-orbit)"; shuffle uniform over Dic_3.

```
[R0] well-formed & composition-blind         PASS
[R1] correct & shuffle-invariant recovery    PASS
[R2] shuffle-sourced privacy (k=1)           PASS
[R3] genuine ramp (k=1, T=9, gray 2..8)      PASS
[R4] non-trivial                             PASS
[R5] non-cyclic: k_G=1 vs C_12 benchmark k=1 FAIL
CERTIFICATE: R0=P R1=P R2=P R3=P R4=P R5=F   OVERALL: FAIL
```

Rejected at R5. Dic_3 achieves privacy k=1, exactly what the equal-order cyclic C_12 achieves.
Its only edge is a reconstruction number T=9 vs 11, which depends on the chosen generic triple, so
it is not a security property. Dic_3 is cyclic-grade in the shuffle-matters direction. This is the
solvable-group prediction confirmed: a non-cyclic shuffle group does not make a non-cyclic scheme.

## Candidate 2: A5 = PSL(2,5) hearts on 6 points  ->  PASS

Tuple: G = PSL(2,5) = A5 (order 60) acting on P^1(F_5) = 6 points by Mobius maps (generators
x -> x+1 and x -> -1/x, verified to close to 60 elements); deck 3 hearts / 3 clubs; secret bit =
which of the two A5-orbits of 3-subsets the hearts form; shuffle uniform over A5.

```
[R0] well-formed & composition-blind          PASS
[R1] correct & shuffle-invariant recovery     PASS
[R2] shuffle-sourced privacy (k=2)            PASS
[R3] genuine ramp (k=2, T=5, gray 3..4)       PASS
[R4] non-trivial (2 triple-orbits, sizes 10,10) PASS
[R5] non-cyclic: k_G=2 vs C_6 benchmark k=1   PASS
CERTIFICATE: R0=P R1=P R2=P R3=P R4=P R5=P    OVERALL: PASS
```

Clears every gate. A genuine nonlinear, non-trivial, non-cyclic, shuffle-matters (k=2, T=5)
threshold on a non-solvable group.

### Why it works (the mechanism, and why it is robust)

- PSL(2,5) is 2-transitive on the 6 points but not 3-transitive (PGL(2,5) is the 3-transitive
  overgroup). Two consequences fall out with no tuning:
  - 2-transitivity forces every pair's view distribution to depend only on the fixed composition,
    so pairs are secret-blind and k >= 2. A regular cyclic group is only 1-transitive, so it caps
    at k = 1. This is the non-cyclic privacy advantage, and it is structural, not a numerical
    accident.
  - not-3-transitive leaves the 3-subsets in two orbits (10 + 10), the PSL/PGL chirality split, so
    a 3-heart secret carries a genuine invariant. That invariant is not a cyclic invariant.
- The best proper cyclic subgroup (C_5) still gives only k = 1; the full non-solvable group is
  needed for k = 2. So A5 clears R5(i) non-trivially, unlike Dic_3.

This is exactly the Goldilocks window made concrete: 2-transitive enough to hide pairs, not so
transitive that the invariant collapses (which is what sinks the full symmetric group on few
points).

## Bottom line

The template now discriminates correctly. Solvable Dic_3 is cyclic-grade and fails R5;
non-solvable A5 on 6 points is the first candidate to pass all six, and it passes for a structural
reason (2-transitive but not 3-transitive) rather than by tuning. This confirms the whole
trajectory: shuffle-matters beyond cyclic lives with non-solvable groups, and A5 on 6 points is a
concrete, exhaustively verified witness of a (k,T) = (2,5) nonlinear shuffle-matters threshold.

## Open follow-ups

- The A5-on-6 invariant is the PSL/PGL triple-chirality; identify whether this matches a known
  card-based construction before claiming novelty.
- Probe whether larger non-solvable actions (A5 on 10, A6, PSL(2,7) on 8) push k higher and widen
  the usable ramp.
- The scheme is a computation/reveal-all protocol at heart (den Boer lineage); a formalization
  would follow the five_card_* scaffold, not the AG scaffold.
