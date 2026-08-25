# Rocq formalization spec: non-Abelian genus-1 AG recovery in pgg-smc (full framework migration)

Date: 2026-07-01
Status: revised after adversarial audit (2026-07-01). Scope decided: full framework migration.
Companions: [[20260701-nonabelian-ag-recoverable-genus1-design]],
[[20260701-nonabelian-ag-recoverable-genus1-worked-example]], [[20260701-nonabelian-ag-genus1-CONTENTS]].

## 0. Goal

Machine-check that `Dic_3` (order 12, non-Abelian, non-dihedral) carries genuine AG-code
secret-sharing recovery on `E : y^2 = x^3 - x` over `GF(9)`, at three privacy levels
(`t = 1, 4, 7`), and that the pgg-smc rigidity framework is extended to express it. The S_5
instance's recovery is vacuous (`sum_mod`, no gap); ours is the first real recovery instance and
the first to exercise the gap machinery, which forces the framework changes below.

## 0a. Audit findings folded in

The naive plan (instantiate the existing records, "fix cs_gap in place", "full mixing", prove by
reflection) was rejected. The migration below reflects these facts:

- `CoveringScheme.cs_gap` (`ts_T <= ts_k + 2g`, covering_scheme.v:139) uses the full share-tuple
  length `ts_T = n-1 = 12` and is FALSE for every high-privacy code. It is fixed by replacing
  `ts_T` with a reconstruction-threshold field (P4/P5), a genuine record migration touching ~83
  sites across 15 `reconstruct/` files and 8 instances.
- The reconstruction threshold `r` is new content (massey's `ts_recon` reads the full tuple). It
  must be added to `ThresholdScheme`, with a subset decoder and its correctness (P4).
- Security "mixing to uniform" is impossible for an intransitive secret-fixing group: the secret
  coordinate is fixed, so `var_dist` to `fdist_uniform 13` has a permanent floor. The honest and
  achievable claim is uniform-on-the-12-share-orbit with an explicit `sa_eps_inf` floor (P8).
  Dic_3 is transitive on the 12 shares, so one uniform group draw already gives
  uniform-on-orbit; the walk is trivial, the floor is the fixed secret.
- The repo's `GF q m` is a choice-based splitting field with an opaque carrier; nothing reduces
  under `vm_compute`. Reflection requires a SEPARATE concrete GF(9) model (P0).
- Achievable core (verified): `ts_recon_perm_invariant` under Dic_3 via `massey_perm_compatible`
  needs only `sigma_fix0` + `code_auto`, no morphism, no fdist (P3).

## 1. The three concrete instances

All on `E : y^2 = x^3 - x` over `GF(9)`, secret at `P_0 = (0,0)`, recon-symmetry
`Dic_3 = Stab(P_0)` (12 explicit permutations of `'I_13`, fixing coordinate 0). Divisor
`D_m = m(O + T1 + T2)`, code `C_L(D_m)`. All data and checks in `notes/ec_worked_example.py`,
`ec_coalition_profile.py`, `ec_tune_privacy.py`.

| case | m | code | privacy t | recon r | ts_k=d_perp-1 | r <= ts_k+2g |
|---|---|---|---:|---:|---:|:--|
| A | 1 | [13,3,10] | 1 | 4 | 2 | 4 = 2+2 (equality) |
| B | 2 | [13,6, 7] | 4 | 7 | 5 | 7 = 5+2 (equality) |
| C | 3 | [13,9, 4] | 7 | 10 | 8 | 10 = 8+2 (equality) |

The redefined `cs_gap` (`r <= ts_k + 2g`) holds at equality for all three: the AG signature.

## 2. Reusable machinery (verified)

- `massey_scheme` (massey.v:431): `ThresholdScheme` from any code with `C_not_trivial`, `Hd2`,
  `privacy_surj`. No `Hparam`.
- `massey_perm_compatible` + `transport_perm_compatible` (coord_perm_compatible.v:266,310): yield
  `ts_recon_perm_invariant` from `sigma_code`/`sigma_fix0`/`code_auto`. No morphism, no fdist.
- `Gen_PGGTypes` (pgg_interface.v:535): builds a `MonodromyReprType` from an explicit permutation
  tuple. Supplies `dic3_M`.
- The records: `ThresholdScheme`, `ReconPlug`, `CoveringScheme`, `CoveringData`,
  `ThresholdWitness`, `SecurityWitness`, `AlgebraicRigidity`, `DropoutWitness`.

## 3. Sub-projects (migration order)

### P0 — Concrete computable GF(9) model

Build `GF9` as a SEPARATE concrete `finFieldType` (not the repo's opaque `GF 3 1`), e.g.
`{poly 'F_3} %% (X^2 + 1)` with explicit reduction, or an `'F_3 * 'F_3` pair with `w^2 = -1` and
HB field instances. `+`, `*`, `==`, inverse must reduce under `vm_compute`. Prove `finFieldType`,
`#|GF9| = 9`, char 3. Optional transport iso to `GF 3 1` only if interop is needed.
New. Spike first (extension-field HB + `vm_compute` sanity). Blocks P1, P2, P8.

### P1 — Monodromy object and concrete data

`dic3_M := Gen_PGGTypes` over the 12 permutations of `'I_13` (`N = 13`). The three generator
matrices `evD_m : 'M[GF9]_(k_m,13)`. `dic3 : {group {perm 'I_13}}` with `#|dic3| = 12`,
`~ abelian dic3`, unique involution (non-dihedral), `dic3_fix0`. New. Depends on P0.

### P2 — Code properties + code_auto (reflection on the concrete field)

For each case: `min_dist = 10/7/4`, `d_perp = 3/6/9`, `privacy_surj`, `C_not_trivial`, `Hd2`,
and `code_auto : forall g in dic3, coord_perm_compatible (C_L(D_m)) g`. Discharged by
`vm_compute` on `GF9` (works because P0 is concrete). Depends on P0, P1.

### P3 — Headline: ThresholdScheme + recovery invariance

`ts_m := massey_scheme ...` and `recon_inv_m : ts_recon_perm_invariant dic3_M ts_m (id-monodromy)`
via `massey_perm_compatible` + `transport_perm_compatible`. Proves: recovery is invariant under
the non-Abelian, non-dihedral `Dic_3` shuffle fixing the secret. This is sound and independent of
the migration; land it first. Depends on P2.

### P4 — Framework migration: reconstruction threshold + subset decoder

Add to `ThresholdScheme` a field `ts_recon_threshold : nat` and an obligation
`ts_recon_threshold_correct` (a coalition of size >= `ts_recon_threshold` determines the secret),
realized by a subset decoder. Provide a `massey_recon_from_subset` decoder (solve
`sum_{i in A} lambda_i g_i = g_0` over `GF9`, return `sum lambda_i share_i`) and its correctness.
Supply the new field for EVERY existing `ThresholdScheme` constructor (`sum_mod_scheme`,
`product_scheme`, `massey_scheme`, `transport`), where for the near-MDS/exact ones it equals
`ts_T` with trivial correctness. Regression: whole repo compiles, `Print Assumptions` clean.
Highest-risk sub-project. Depends on P3.

### P5 — Redefine cs_gap and re-verify all instances

Redefine `CoveringScheme.cs_gap` to `ts_recon_threshold (cs_scheme) <= ts_k (cs_scheme) + 2 *
cd_genus`. Re-prove `cs_gap` (and dependents `security_threshold_tradeoff`, `gap_bound`,
`genus0_exact`, `ar_gap_bound`, `dw_dropout_leq_gap`) for all 8 instances (s5, s5x5, denboer1989,
kim2025, wreath7, oc, star, and ours). For our three cases it holds at equality. Depends on P4, P6.

### P6 — CoveringData (genus-1 Riemann-Hurwitz)

`cdata_dic3 : CoveringData dic3_M` with `cd_base_genus = 0`, `cd_total_ramif = 24`,
`cd_genus = 1`, discharging the nat identity `2*1 + 2*12 = 12*0 + 24 + 2` and
`cd_ramif_ge_n_branch`. Filled as an arithmetic record like s5's data (the genus is the real
value 1; `R = 24` and `g_base = 0` are recorded, optionally justified from fixed-point data).
Depends on P1.

### P7 — First DropoutWitness instance

`MkDropoutWitness` per case: `dw_min_revealed = r_m`, the P4 subset decoder as
`dw_recover_from_revealed`, `dw_recover_uses_revealed_only`, and `dw_recover_shuffle_invariant`
(from P3's code invariance). The framework's first `DropoutWitness` instance: the genuine
`T - k` dropout capability S_5 lacks. Depends on P4, P5.

### P8 — Floor-security witness (uniform-on-orbit, not mixing)

`SecurityWitness`/`SecurityAsymptotic` for the `Dic_3` action, restated honestly:
- Design the `Dic_3` shuffle model (physical moves for the 12 group elements acting on the deck);
  this is an open design sub-question, since Dic_3 comes from curve automorphisms, not card swaps.
- Dic_3 is transitive on the 12 shares (single orbit) and fixes the secret, so one uniform group
  draw gives uniform-on-the-12-share-orbit; the walk is essentially one step.
- `sw_bound` / `sa_convergence` certify `var_dist` to uniform ON THE SHARE ORBIT, with an explicit
  `sa_eps_inf` floor for the fixed secret coordinate (as s5x5 does with `sa_eps_inf = 1`).
- Non-involutive generators mean the s5 symmetric-walk lemmas do not apply; a small direct
  var_dist bound (order-12 group) replaces them.
Honest deliverable: within-share anonymity with a secret-card floor, not mixing to full uniform.
Depends on P0, P1.

### P9 — AlgebraicRigidity assembly + tradeoff

For each case: `AlgebraicRigidity` with `ar_security = ` the P8 floor witness and `ar_threshold =`
the `ThresholdWitness` over the P5 `CoveringScheme`; plus the attached P7 `DropoutWitness`; plus a
tradeoff lemma (genus-positive branch, real gap). Depends on P3-P8.

## 4. Dependency graph and phasing

```
P0 -> P1 -> P2 -> P3            (headline: land first)
                   \-> P4 -> P5 -> P7 -> P9
             P1 -> P6 ----------/
             P1 -> P8 ----------------------/
```

Phases: (1) P0-P3 headline. (2) P4-P5 framework migration + whole-repo regression. (3) P6, P7
recovery records. (4) P8 floor security. (5) P9 assembly. Each phase checkpointed (compiles,
axiom-free).

## 5. Cross-cutting requirements

- Regression gate after P4/P5: the entire `pgg-smc` repo compiles and `Print Assumptions` is clean
  for every existing instance under the migrated records.
- The concrete `GF9` (P0) is the reflection substrate; all P2 finite checks run there.
- Security is a floor claim (P8), documented as such everywhere it appears.
- Three concrete instances, no parameterized-family proof.

## 6. Risks

- P4/P5 migration blast radius (~83 sites, 8 instances): the dominant risk; a mis-placed field or
  a broken instance blocks the whole repo. Mitigate with an incremental field addition + per-file
  compile.
- P8 has no shuffle model yet; designing one (and confirming the floor is the honest ceiling) is
  an open sub-question, possibly its own brainstorm.
- P0 concrete field + `vm_compute` performance on `[13,k]` codes and `C(13,<=k)` subset checks;
  fall back to targeted lemmas if reflection is slow.
- P6 rigor of `R = 24` if a fixed-point justification is demanded rather than the arithmetic record.

## 7. Out of scope

- General divisor / Riemann-Roch AG theory (bypassed by the code-generic `massey_scheme`).
- Characteristic-2 `SL_2(F_3)` and genus >= 2 variants.
- Larger fields to raise the privacy ceiling.
- Mixing-to-full-uniform security (impossible for the intransitive secret-fixing group).
