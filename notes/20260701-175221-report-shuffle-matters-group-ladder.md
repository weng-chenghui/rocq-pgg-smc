# Report: the shuffle-matters group ladder (Dic_3 FAIL, A5 PASS, PGL(2,7) PASS)

Date: 2026-07-01

Three candidates run through the corrected shuffle-matters verification template
([[20260701-173005-shuffle-matters-verification-template]]). All results are exhaustive
computations over the full group and all coalitions, not sampling. Script:
`notes/ec_verify_shuffle_matters.py`. Supersedes the two-candidate certificate
[[20260701-174652-certificate-dic3-fail-a5-pass]] by adding the larger PGL(2,7) case and the
pattern they reveal.

## The three certificates

### Dic_3 on 12 points (solvable, order 12) -> FAIL
Secret = "are the hearts a rotation triple (C_3-orbit)"; deck 3 hearts / 9 clubs.
```
R0=P R1=P R2=P R3=P R4=P R5=F     k=1, T=9
```
Rejected at R5. Privacy k=1 equals the equal-order cyclic C_12 benchmark. Cyclic-grade.

### A5 = PSL(2,5) on 6 points (non-solvable, order 60) -> PASS
Secret = which of the two A5-orbits of 3-subsets; deck 3 hearts / 3 clubs.
```
R0=P R1=P R2=P R3=P R4=P R5=P     k=2, T=5, gray 3..4
```
2-transitive on 6 points, not 3-transitive. 3-subsets split 10+10 (PSL/PGL chirality).

### PGL(2,7) on 8 points (non-solvable, order 336) -> PASS  [the larger one]
Secret = which of the two PGL-orbits of 4-subsets (cross-ratio class); deck 4 hearts / 4 clubs.
```
R0=P R1=P R2=P R3=P R4=P R5=P     k=3, T=7, gray 4..6
```
Sharply 3-transitive on 8 points, not 4-transitive. 4-subsets split 42+28 by cross-ratio.

## The ladder

| candidate    | group        | order | points | transitivity        | invariant on   | k | T | verdict |
|--------------|--------------|------:|-------:|---------------------|----------------|--:|--:|---------|
| Dic_3        | dicyclic     |    12 |     12 | 1 (regular)         | 3-subsets      | 1 | 9 | FAIL    |
| PSL(2,5)=A5  | non-solvable |    60 |      6 | 2-transitive        | 3-subsets      | 2 | 5 | PASS    |
| PGL(2,7)     | non-solvable |   336 |      8 | sharply 3-transitive| 4-subsets      | 3 | 7 | PASS    |

The pattern is exact and structural:

- Privacy threshold `k` equals the degree of transitivity of the shuffle action. A `t`-transitive
  group makes every `t`-subset's view depend only on the fixed composition, so all coalitions up to
  size `t` are secret-blind.
- The invariant survives precisely because the group is NOT `(t+1)`-transitive, leaving the
  `(t+1)`-subsets in at least two orbits. That is the secret-carrying invariant, and it is not a
  cyclic invariant.
- Reconstruction sits at `T = N-1` for the passing schemes: revealing all but one card forces the
  last by the known composition, fixing the arrangement and hence the invariant.

So the recipe for privacy `k` is: take a `t`-transitive but not `(t+1)`-transitive group,
`k = t`, secret = orbit-class of a `(t+1)`-subset. `PSL(2,q)` gives `t=2`, `PGL(2,q)` gives `t=3`.
A regular cyclic group is 1-transitive, so it is stuck at `k=1`, which is why every cyclic scheme
and the solvable Dic_3 are cyclic-grade and fail R5.

## Why this closes the question the investigation asked

The original pivot asked for a nonlinear (shuffle-matters), non-trivial, non-cyclic `(k,T)`
recovery beyond the cyclic den Boer trick, and whether it can be had for groups other than cyclic.
Answer, now with verified witnesses:

- It cannot come from an AG/linear scheme (the shuffle is inert there), and it cannot come from a
  solvable group in the shuffle-matters direction (cyclic-grade, Dic_3 confirms).
- It does come from non-solvable multiply-transitive groups, and the privacy threshold is tunable
  by climbing the transitivity ladder: `PSL(2,5)` gives `k=2`, `PGL(2,7)` gives `k=3`.

This also recovers the S_5 thread from a new angle: S_5 fails as an AG recovery group (the no-go),
but in a multiply-transitive action its overgroup structure is exactly what powers a
shuffle-matters scheme. Note `PGL(2,5) = S_5` acting sharply 3-transitively on 6 points would give
`k=3` on 6 points by the same mechanism, so S_5's exceptional action is on the passing side here.

## Honest caveats

- The internal diagnostic showed a cyclic subgroup of PGL(2,7) reaching `k=2` on the specific
  secrets (a homometric-set coincidence), while the choice-robust `C_N` benchmark stays at `k=1`.
  The decisive gate compares against the `C_N` benchmark, and `k=t` is structural (needs
  `t`-transitivity, which no cyclic group has for `t>=2`), so the passes are sound. The homometric
  subtlety is why R5 is stated on the benchmark, not on internal subgroups.
- Novelty is unconfirmed. The A5-on-6 chirality and the PGL(2,7) cross-ratio schemes are natural
  enough that they may already appear in card-based cryptography (regular-polygon / dihedral /
  Shinagawa lineage). Verify against the literature before claiming these as new.
- These are computation / reveal-all protocols in the den Boer lineage. A formalization follows the
  `five_card_*` scaffold (bool-or-small secret, positions as shares, invariant read-off, case-based
  privacy), not the AG scaffold.

## Open follow-ups

- Push further up the ladder: `PGL(2,q)` on `q+1` points for larger `q`, or Mathieu groups
  (`M_11`, `M_12`) for `t=4,5`, to test whether `k = t` holds without a transitivity ceiling.
- Quantify the reconstruction / gray-zone cost as `k` climbs (gray width `N-2-k`).
- Decide whether any of these is worth a den-Boer-style Rocq instance alongside the existing
  `denboer1989` and `kim2025` families.
