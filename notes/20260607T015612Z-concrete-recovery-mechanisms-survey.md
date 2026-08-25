# Concrete recovery mechanisms survey

Note date: 20260607T015612Z

Question surveyed: which secret-sharing recovery mechanisms in the codebase
concretely (computably) recover a secret from shares, versus which exist only as
abstract / parameterized characterizations. Verified by reading the code, not
from memory.

The recovery interface is `ts_recon : ts_T'.+1.-tuple shareT -> secretT` on the
`ThresholdScheme secretT shareT` record (`reconstruct/pgg_sharing_framework.v:47`).
A mechanism is "concrete" here if `ts_recon` is a definable, computable function
returning the secret (no `Axiom`/`Admitted`, no undischarged abstract code).

---

## Concrete, computable recovery mechanisms (in use)

### 1. Sum-mod-N
- `sum_mod_recon shares = (Sum_i shares_i) mod N`
  (`reconstruct/pgg_sharing_framework.v:148`).
- Encode is `[0, ..., 0, s]` (`:191`). Correctness `sum_mod_scheme_correct`
  (`:160`).
- `T = k` (no threshold gap).
- In use: `s5` plugs it directly as its covering scheme
  (`cs_scheme = s5_ts = @sum_mod_scheme 3 4`,
  `instances/s5/rigidity_s5_instance.v:299,336`).

### 2. Product of sum-mods (the only working T > k mechanism)
- `product_recon` (`reconstruct/product_threshold.v:209`): split the share
  tuple into two piles, run each factor's `ts_recon` (= sum-mod) per pile to get
  `(s1, s2)`, then `combine_secret s1 s2 = (s1 + N1*s2) mod N` (`:72`).
- Concrete and computable when both factors are sum-mod.
- `T = T1 + T2`, `k = min(k1, k2)`, so the pile structure yields `T > k`.
- In use:
  - `s5x5`: `cs_scheme = @product_scheme 3 3 (@sum_mod_scheme 3 4) (@sum_mod_scheme 3 4)`
    on `'I_10` (`instances/s5x5/rigidity_s5x5_instance.v:358,388`).
    `T = 5+5 = 10`, `k = min(5,5) = 5`, so `T = 10 > k = 5`. Recovery: sum each
    5-pile mod 5, combine via `(s1 + 5*s2) mod 10`.
  - `wreath`: same shape on two piles of 7 (`wreath2_scheme`, `T = 14`,
    `k = 7`).

### 3. Den Boer three-consecutive-hearts (boolean)
- `fc_three_consec` (`instances/denboer1989/five_card_program.v:93`),
  `secretT = shareT = bool`: scan the cyclic 5-card row for three adjacent
  hearts, return `a AND b`.
- Concrete; `fc_correct` checks all 20 cases (`five_card_program.v:105`).
- This is the den Boer PROTOCOL scheme (`fc_threshold_scheme`,
  `five_card_pismc.v:241`, `T = 5`, `k = 2`). NOTE: it is NOT what den Boer's
  rigidity record uses; that uses RS5 (item 4).

### 4. RS / Massey decode (concrete over GF(5))
- `massey_recon_tuple shares = massey_reconstruct (tuple_to_rV shares)`
  (`reconstruct/massey.v:369`), where
  `massey_reconstruct shares = odflt 0 [pick s0 : F | massey_codeword s0 shares \in C]`
  (`massey.v:183`). This is a brute-force `pick` over the field: decidable,
  hence computable.
- The generic `massey_scheme` (`massey.v:431`) is built over an abstract code
  `C : Lcode0.t F n` plus hypotheses (`C_not_trivial`, `Hd2`, `privacy_surj`),
  BUT it is concretely instantiated by `RS5_witness_trivial`
  (`reconstruct/rs_code_5sheets.v:171`) as a real Reed-Solomon code over GF(5)
  (`prime5`, `prim4_GF5`, length parameters), transported to `'I_5 'I_5` via
  `rs_genus0_scheme` (`rs_massey_bridge.v:246`).
- There are NO `Axiom`/`Admitted` in the massey/rs path
  (`massey.v`, `rs_massey_bridge.v`, `rs_code_5sheets.v` verified clean). So the
  RS recovery is concrete and computable.
- In use: `kim` (`instances/kim2025/rigidity_kim_instance.v:74`) and den Boer's
  rigidity (`instances/denboer1989/five_card_security.v:288`), both via
  `genus0_covering_witness ... (RS5_witness_trivial ...)`.

### Honesty correction (vs an earlier hedge)
The RS/Massey decoder is NOT merely abstract. It is concrete and axiom-free over
GF(5), with a computable `pick`-based decode. The only vacuity is that these
instances pass `trivial_sigma` (`rs_code_5sheets.v:179-181`), so the
MONODROMY / shuffle coupling is the identity. That makes the security
equivariance trivial, not the recovery. The recovery computes.

---

## Abstract / shelved (not concretely instantiated by any live instance)

### Positive-genus AG codes
- `reconstruct/cover_genus1.v` (elliptic) and `cover_genus2.v` (hyperelliptic):
  the `ThresholdScheme` (`ag_genus_scheme`, `ag_massey_bridge.v:111`) is built
  over abstract section hypotheses: `Variable ev` (generator matrix),
  `ev_encode`, `dual_ev_encode`, `code_auto`, curve `Variable`s and
  `Hypothesis`es.
- No live instance instantiates these with a concrete curve. This is the
  genuinely abstract recovery path.
- This is exactly the route excluded by Section 9 of the protocol-merge spec
  (`docs/superpowers/specs/2026-06-07-pgg-protocol-merge-design.md`): the AG
  route is excluded by design (`D_*`/Frobenius automorphism family only,
  `s5_nogo.v`), so the merge does not depend on this shelved path.

---

## Bottom line

Beyond sum-mod-N, the codebase has multiple concrete, computable recoveries:
sum-mod-N, its product (the `T > k` workhorse), RS/Massey decode over GF(5)
(used only with trivial sigma), and den Boer's three-consec. The only purely
abstract recovery is the positive-genus AG path (`cover_genus1`/`cover_genus2`),
which is shelved.

For the merge's active instances specifically:
- `s5`: sum-mod-N, `T = k = 5`.
- `s5x5`: product of two sum-mod-5, `T = 10 > k = 5`, the gap coming entirely
  from the pile (product) structure (`T = T1+T2`, `k = min(k1,k2)`).
