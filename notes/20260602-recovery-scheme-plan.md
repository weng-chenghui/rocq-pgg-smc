# Plan: Executable, formalized AG-code / Massey recovery scheme with T > k

## Context

The PGG-SMC framework already proves the **structure** of a genus-driven threshold gap
(`ag_massey_bridge.v`: `ag_massey_gap : ts_T <= ts_k + 2*g`), and already has a **concrete,
executable instantiation pattern** for genus 0 (`rs_massey_bridge.v`: Reed-Solomon over a real
Galois field `GF`). What is missing is the one thing the user wants: a **concrete instance with
`g > 0`**, so that `T > k` strictly, that actually **runs under `vm_compute`** and is **wired into
the S_5 / Bring monodromy** (and an `S_5 x S_5` two-instance version).

User decisions (this session):
- Positive genus **certified by computation** (compute minimum distance; no Riemann-Roch).
- Instance must serve **S_5** and **S_5 x S_5** (the latter as two composed instances).
- **Wire into the S_5 / Bring monodromy** covering.
- "Executable" = **`vm_compute` inside Coq** (brute-force `pick` decode is acceptable).

### Verified current state (first-hand reads)

| Artifact | File | Status |
|---|---|---|
| `ag_massey`, `ag_massey_gap`, `ag_genus_scheme` | `reconstruct/ag_massey_bridge.v` | Structure done; **abstract `F`, `ev`, `g`**; no instance |
| `ag_code`, `goppa_wt` hyp, `ag_min_dist_lb` | `reconstruct/ag_code.v` | Code-from-matrix + distance bound from `goppa_wt` |
| `massey_scheme`, `massey_reconstruct` (`pick`), `massey_private` | `reconstruct/massey.v` | Decode = brute-force `pick` (computable for concrete F+C); encode uses `xchoose` |
| `rs_massey`, `transport_scheme`, `rs_genus0_scheme` | `reconstruct/rs_massey_bridge.v` | **Template**: concrete `GF` field + `RS.code`; but `rs_massey_exact : ts_T = ts_k` (g=0) |
| `ts_recon_perm_invariant` | `reconstruct/pgg_sharing_framework.v:125` | `forall g s shares, valid -> ts_recon [tuple tnth shares (perm g i)] = s` |
| infotheo ECC reuse: `GF`, `{poly}`, `min_dist`, dual code, RS/GRS/BCH, `alternant`/`Rcode` | `ecc_classic/*`, `lib/ssralg_ext.v` | Executable field + code framework present; **no curves / Riemann-Roch** |

### The obstruction (verified, must design around)

`cs_recon_invariant` demands `ts_recon (shares reordered by perm g) = s` for **every** monodromy
element `g`. Sum-mod satisfies this for *any* permutation (sum is symmetric), which is why s5/s5x5
work today. A Massey/AG decoder satisfies it **only when each `perm g` is a coordinate-permutation
automorphism of the code** (fixing the secret coordinate 0). Because `cs_scheme : ThresholdScheme
'I_N 'I_N` with `N = 5` for the s5 instance, a Massey instance **forces the alphabet field
`F = GF(5)`**. So Phase 2 needs a *positive-genus code over GF(5) whose coordinate-automorphism group
contains a faithful S_5*. The code length `T = n-1` is **not** forced to 5 (cs_monodromy permutes
`T` positions, `T >= 5` suffices for faithfulness), so this is possible in principle, but the honest
realization is an AG code on **Bring's curve over a finite field** (or a GF(5) subfield-subcode of an
AG code over `GF(5^m)`), which reintroduces real algebraic legwork. This is the documented coupling
(`project_pgg_framework_coupling`): the AG bridges currently "build threshold schemes in isolation
only" and have never been composed with a non-trivial monodromy. **Phase 1 is independent of this
obstruction; Phase 2 is where the research risk lives.**

---

## Phase 0 — Feasibility spike (run first, after approval)

De-risk the single load-bearing assumption: that the Massey/AG decode **reduces under `vm_compute`**.

Minimal experiment (scratch file, not committed):
1. `F := GF 1 (prime 5)` (i.e. `'F_5`), a tiny concrete `ev : 'M[F]_(2,3)` of full rank.
2. Build `C := ag_code ev`; pick a concrete `shares : 2.-tuple F`.
3. Test `Eval vm_compute in massey_recon_tuple shares` — confirm it returns an `F` value (no stuck
   `pick`/vspace-membership). Confirm `_ \in ag_code ev` reduces (it is `(linfun (mulmxr ev) @:
   fullv)%VS`; verify vspace membership computes).
4. Test `Eval vm_compute in massey_encode_tuple s` — determine whether `xchoose (first_coord_surj s)`
   blocks (opaque `Qed` proof). **If it blocks**, plan a computational encoder
   `ag_encode_compute : F -> shares` (search a codeword with secret at position 0 via systematic
   form / `pick` over messages) and a lemma that it satisfies `massey_valid_tuple`.

Decision gate: if decode does not `vm_compute`, escalate (the whole "executable" claim depends on it);
if only encode blocks, substitute the computational encoder (decode is what "recovery" needs).

**Effort: hours. Risk: low-medium (this is the make-or-break check).**

---

## Phase 1 — Standalone executable positive-genus AG-Massey scheme (must-deliver)

Mirror `rs_massey_bridge.v` but with a **non-MDS** generator matrix. **No monodromy yet.** This alone
satisfies "AG-code/Massey, executable, formalized, T > k".

New file: `pgg-smc/reconstruct/ag_massey_concrete.v` (register in `_CoqProject`).

Concrete instance (tight regime `n = k + g + 1`, `g = 1`):
- `F := GF` of a small field (e.g. `'F_7`; field chosen for convenient elliptic points).
- `k = 3`, `g = 1`, `n = 5`. Elliptic one-point code: pick `E/F` with `>= 5` affine points; basis of
  `L(3·O) = {1, x, y}`; `ev : 'M[F]_(3,5)` whose columns are `[1; x_i; y_i]` at 5 points `P_i`. This
  is a genuine genus-1 AG code with Singleton defect 1, written as an explicit matrix.
- Targets: `ts_T = n-1 = 4`, `ts_k = k-g = 2`, **`T - k = 2g = 2`**.

Discharge obligations (all by computation where possible):
| Obligation | How |
|---|---|
| `ev_rank : \rank ev = k` | `by vm_compute` (or `by []` after `Eval`) |
| `goppa_wt : forall m != 0, n-(k+g-1) <= wH (m *m ev)` | reflect: prove `[forall m : 'rV[F]_k, (m != 0) ==> (n-(k+g-1) <= wH (m *m ev))]` `by vm_compute` (`|F|^k = 7^3 = 343` enumerations), then `move/forallP` |
| `Hk, Hkn, Hkg, Hkgn, Hparam` | `by []` (arithmetic on literals) |
| `ag_priv_surj : forall S target, #|S| < d_perp -> exists c in ag_code ev, vproj c S = vproj target S` | prove general lemma `proj_surj_of_dual_dist : #|S| < min_dist(dual C) -> projection onto S surjective`, reuse for this code after computing `d(C^perp)` by `vm_compute`; **reuse / generalize `rs_privacy_surj` (`reconstruct/rs_privacy.v`)** which already does this for RS |

Then:
- `Definition conc_ag_massey : ThresholdScheme F F := ag_massey ev ev_rank Hk Hkn Hkg Hkgn goppa_wt ag_priv_surj.`
- `Lemma conc_gap : ts_T conc_ag_massey = ts_k conc_ag_massey + 2.` (or `< `, the strict T>k)
- **Executable demo** (`Example`/`Eval`): encode a secret -> shares -> `massey_recon_tuple` recovers it,
  via `vm_compute`; plus a sub-`k` coalition witness from `massey_private` showing two secrets are
  consistent on the coalition.

**Effort: 2-4 days. Risk: low** (modulo Phase 0; `ag_priv_surj` is the main proof, mitigated by
reusing `rs_privacy`). This is the concrete answer to the user's headline request.

---

## Phase 2 — Wire into the S_5 / Bring monodromy (research-scale)

Goal: a `CoveringScheme R_s5_brings` whose `cs_scheme` is a positive-genus AG-Massey over **GF(5)**
and whose `cs_monodromy = @pgg_rho R_s5_brings` is faithful, with `cs_recon_invariant` discharged by
**each S_5 generator being a verified code automorphism**.

Design:
1. **A positive-genus code over GF(5) carrying a faithful S_5 by coordinate automorphisms.** Honest
   source: Bring's curve over a finite field. Two routes:
   - (a) Bring over `GF(5)` directly: enumerate `GF(5)`-rational points, S_5-permuted, with an
     S_5-fixed point `P_0` as the secret coordinate. **Risk: char 5 may be degenerate, and
     Hasse-Weil allows as few as 0 points; must verify by computation that enough usable points
     exist.**
   - (b) GF(5) **subfield-subcode / alternant** of an AG code over `GF(5^m)` (where Bring has many
     points), using infotheo's `alternant.v` / `Rcode` restriction. Alphabet stays `GF(5)`; S_5 acts
     on the `GF(5^m)`-points inducing automorphisms of the subfield subcode. **This is the principled
     fallback if (a) is point-starved.**
2. **`cs_recon_invariant` by computation:** prove `ts_recon_perm_invariant cs_scheme (@pgg_rho ...)`
   by reducing to: each of the 4 path-transposition generators of S_5 is a code automorphism fixing
   coordinate 0. Check via `vm_compute` that permuting `ev`'s columns by the generator preserves the
   row space (and fixes position 0). 4 checks over GF(5).
3. **Assemble** `s5_ag_covering : CoveringScheme R_s5_brings` with `cs_scheme := <transported AG
   scheme on 'I_5>`, `cs_monodromy := @pgg_rho R_s5_brings`, `cs_gap` from `ag_massey_gap`,
   `cs_recon_invariant` from step 2.
4. **Framework touch (likely minimal):** the existing `cs_*` fields appear sufficient (no new field
   needed — the automorphism content lives inside the `cs_recon_invariant` proof). Confirm during
   implementation; only add a `cs_code_aut` witness field if the proof cannot be expressed otherwise.

Files: `pgg-smc/reconstruct/bring_gf5_code.v` (the GF(5) code + S_5 automorphism checks) and
`pgg-smc/instances/s5/rigidity_s5_ag_instance.v` (the covering wiring; sits alongside, does not
replace, the current sum-mod `s5_brings_covering`).

**Effort: weeks to months. Risk: high.** The genuine research risk: whether a positive-genus code
over GF(5) with faithful S_5 coordinate-automorphisms and *genus 4 specifically* is reachable.
Realistic first target is **smaller genus** (g = 1 or 2) over GF(5) via route (b); genus-4 Bring over
GF(5) is the stretch goal. Be explicit in the deliverable about which genus was achieved.

---

## Phase 3 — S_5 x S_5 via two instances

Compose two Phase-2 per-pile AG-Massey schemes, mirroring the existing
`s5x5_ts := product_scheme (sum_mod 3 4) (sum_mod 3 4)`:
- `product_scheme` over two copies of the Phase-2 GF(5) AG scheme (the alphabet is now `'I_10` via the
  product's `combine_secret`, so re-check the product's secret-space arithmetic).
- `cs_recon_invariant` via `product_*_perm_compatible`, generalized from `product_sum_mod_perm_compatible`
  to require *per-pile code automorphism* instead of sum symmetry (the pile-preservation hypothesis
  carries over; the within-pile step changes from "sum invariant" to "code automorphism").
- Record per-component genus with the existing `MultiCoveringData` (two components, genus = Phase-2
  genus each), reusing `multi_covering.v`.

File: `pgg-smc/instances/s5x5/rigidity_s5x5_ag_instance.v`.

**Effort: days-to-weeks after Phase 2. Risk: medium** (the product perm-compatibility generalization
is the new proof; everything else mirrors existing s5x5).

---

## Verification (end-to-end)

- **Phase 0:** `Eval vm_compute in massey_recon_tuple <concrete shares>` returns a value; record
  whether encode blocks.
- **Phase 1:** `make -j1 pgg-smc/reconstruct/ag_massey_concrete.vo`; the demo `Example`s reduce by
  `vm_compute`; `conc_gap` proves `ts_T > ts_k`. Axiom check: `Print Assumptions conc_ag_massey`
  shows no custom axioms (only the standard ones from infotheo/mathcomp).
- **Phase 2:** `make -j1` the s5 AG instance; `Print Assumptions s5_ag_covering` — the curve
  realisation may remain a documentation axiom (`realised_by_curve`), but `cs_recon_invariant` must be
  axiom-free (computed automorphisms). Confirm `cs_monodromy` is the real faithful `pgg_rho`, not
  trivial.
- **Phase 3:** `make -j1` the s5x5 AG instance; gap `ts_T = 10 > ts_k`, recon-invariance proved.
- Pre-commit: the two-stage `rocq-audit` gate must pass on every staged `.v` (naming I-series,
  comment H-series). Use `make -j1` only (memory: concurrent rocqworkers crash the machine).

## Key risks / open feasibility questions

1. **`vm_compute` of decode** (Phase 0) — make-or-break; resolved by the spike.
2. **`ag_priv_surj`** — needs a dual-distance surjectivity lemma; mitigated by reusing `rs_privacy`.
3. **GF(5) point scarcity for Bring** (Phase 2) — may force route (b) subfield-subcode, and likely a
   genus smaller than 4 as the first real instance. This is the dominant research risk.
4. **Genus-4-over-GF(5) specifically** may be out of reach; the plan delivers a *positive-genus*
   S_5-wired instance, with genus 4 as a stretch goal, not a guarantee.

## Recommended sequencing

Ship **Phase 1** first (it fully answers "executable + formalized + T > k, AG/Massey"), then attempt
**Phase 2** with route (b) and a modest genus, then **Phase 3**. Treat Phase 2's genus-4/Bring-over-GF(5)
as a research stretch, not a committed deliverable.
