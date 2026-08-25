# S_5 × S_5 threshold is curve-independent: two-Bring's vs single connected curve

**Date:** 2026-05-19

This note answers the follow-up question to
`20260516_s5x5_recovery_feasibility.md`: does the operational
two-disjoint-Bring's realisation of `S_5 × S_5` give a WEAKER
`(k, T)`-threshold than the (fictional) single connected curve at
`g = 173`? The short answer is no. The gap `T - k = 5` is invariant
under the curve choice, because the threshold parameters come from
the recovery primitive, not from the curve. This note records the
reasoning, the code-level evidence, and the position relative to
the secret-sharing literature.

---

## 1. Short answer

In pgg-smc, the threshold parameters `T` and `k` are arithmetic
properties of the recovery primitive. The curve enters only
through the framework's `cs_gap` obligation
`ts_T <= ts_k + 2 · g`, and the obligation is met with large slack
in both the single-component view (`cd_genus = 173`) and the
multi-component view (`mcd_total_genus = 8`). Neither view
changes `T` or `k`, so the gap stays at `5`.

The Chen-Cramer strong-ramp identity `T - k = 2g` does NOT apply
here. That identity is for an AG-code-on-curve recovery primitive,
which pgg-smc's `s5x5_pile` instance does not use.

---

## 2. Code-level evidence

The instance file `pgg-smc/instances/s5x5/rigidity_s5x5_instance.v`
wires the threshold scheme as

```coq
Let s5x5_ts : ThresholdScheme 'I_5 'I_5 :=
  @product_scheme 3 3 (@sum_mod_scheme 3 4) (@sum_mod_scheme 3 4).
```

with the comment block

```
sum_mod_scheme on 'I_5 with 5 parties: ts_T = ts_k = 5.
Product: ts_T = 10, ts_k = min(5,5) = 5.
```

So `ts_T = 10`, `ts_k = 5`, and the gap is `T - k = 5`. Both
`product_scheme` and `sum_mod_scheme` are purely arithmetic
constructions over `'I_5`. They never read any curve invariant.

The `cs_gap` obligation is discharged by

```coq
Lemma s5x5_cs_gap :
  (ts_T s5x5_ts <= ts_k s5x5_ts + 2 * 3)%N.
```

at `rigidity_s5x5_instance.v:363`. The literal `2 * 3` shows the
obligation is satisfied at any genus `>= 3`. The recorded values
sit comfortably above this:

- Single-component view: `cd_genus = 173`, slack `2 · 173 = 346`.
- Multi-component view: `mcd_total_genus = 8`, slack `2 · 8 = 16`.
- Per-component view: `mcd_max_genus = 4`, slack `2 · 4 = 8`.

All three satisfy `>= 5`. None changes `ts_T` or `ts_k`.

---

## 3. Why this is the same principle as random-walk security

The previous note observed that pgg-smc's privacy bound comes from
random-walk mixing on the deck group's Cayley graph, not from any
curve invariant. The threshold parameters `T` and `k` exhibit the
same decoupling. Both security and threshold are determined by
constructions over the deck group and the share alphabet, and the
curve enters the framework only via algebraic rigidity. The
`cs_gap` inequality is a sanity check that the rigidity-side curve
is large enough to support the threshold-side parameters, not a
mechanism that derives one from the other.

In particular, swapping the rigidity realisation from a single
connected curve at `g = 173` to two disjoint Bring's curves at
`g = 4` each loosens the `cs_gap` slack but does not move the
operational `(k, T) = (5, 10)`.

---

## 4. Cross-instance check at the framework rigidity layer

Among the four in-scope instances of pgg-smc, only `s5x5` exhibits
a strict threshold gap at the framework `cs_scheme` layer:

- `kim2025`: `cs_scheme` wires through `RS5_witness_trivial`,
  `cd_genus = 0`, `T - k = 0`.
- `denboer1989`: `fc_covering` wires through `RS5_witness_trivial`,
  `cd_genus = 0`, `T - k = 0` at the framework layer. The protocol
  layer's own `fc_ts` (the five-card AND scheme,
  `@MkThresholdScheme bool bool 4 1`, hence `ts_T = 5, ts_k = 2`)
  has gap `3`, but that is a protocol-layer object not wired into
  `fc_covering.cs_scheme`.
- `s5`: `cs_scheme = sum_mod_scheme 3 4` with `ts_T = ts_k = 5`,
  `cd_genus = 4` (Bring's), `T - k = 0`.
- `s5x5`: `cs_scheme = product_scheme ... sum_mod ... sum_mod`,
  `ts_T = 10, ts_k = 5`, `cd_genus = 173` (or
  `mcd_total_genus = 8`), `T - k = 5`.

So `s5x5` is the framework's first concrete instance with a
strictly positive `cs_scheme`-layer threshold gap.

---

## 5. Position relative to Chen-Cramer and the literature

The literature splits into two regimes for the threshold-gap
question.

**Regime A: recovery is AG-code on the curve.**
Chen-Cramer 2006 establishes the strong-ramp identity
`T - k = 2g` for an AG-code on a connected curve `C` of genus `g`.
The convention used here is the endpoint-distance one, matching
pgg-smc's own `cs_gap : ts_T <= ts_k + 2 · g`. Privacy holds at any
`u <= T - 1` shares and recovery at any `u >= T + 2g` shares, so
the unresolved gap region is `[T, T + 2g - 1]` of cardinality
`2g + 1`. Peng-Chen-Zhao 2021 refines this over large fields: the
gap region splits at `T + g`, with almost all subsets in
`[T, T + g - 1]` fully private and almost all subsets in
`[T + g, T + 2g - 1]` fully reconstructing, so the scheme is
asymptotically threshold. Both results bind the gap parameter
directly to the genus of the recovery curve. In this regime,
switching curve genus DOES change `T - k`.

**Regime B: recovery is curve-independent.**
Standard ramp constructions (packed Shamir, sum-mod, the
`product_scheme` combinator used by pgg-smc) define `T` and `k`
purely from the share alphabet and the access structure. The curve
is a separate object that supplies rigidity or symmetry, not the
threshold parameters. Stinson's *Ideal Ramp Schemes and Related
Combinatorial Objects* and Cramer-Damgård-Nielsen's textbook treat
ramp schemes as linear-algebra objects on the share space, with
the geometric realisation orthogonal to the threshold parameters.
pgg-smc's `s5x5_pile` operates in this regime.

The `s5x5_pile` instance therefore inherits Regime B's threshold
behaviour: switching the rigidity curve from one realisation to
another keeps the `(k, T)` pair at `(5, 10)`.

---

## 6. Counterfactual: what if we DID bind recovery to an AG-code?

This is not the protocol pgg-smc currently runs, but it answers
the natural follow-up question.

- Single connected curve, Hurwitz floor `g = 173`. An
  AG-code recovery gives `T - k = 346`. The secret splits
  into `2g = 346` components.
- Two disjoint Bring's, `g_1 = g_2 = 4`. A per-component AG-code
  on each Bring's gives a per-component gap of `8`. The combined
  scheme's global gap depends on the combinator:
  - Disjoint-union code with one secret per component, parties
    indexed by component: global gap is
    `max(2 g_1, 2 g_2) = 8`.
  - Product code combining both secrets into a tuple: global gap
    is the sum or the max of per-component gaps depending on the
    composition, but still bounded by `O(g_1 + g_2) = O(8)`.

In either case the disconnected realisation is dramatically better
than the connected `g = 173` alternative under Regime A
recovery. The disconnected realisation is also strictly worse than
the current Regime B arithmetic recovery's gap of `5`, but only by
a constant factor `O(1)`.

---

## 7. Bottom line for the AIP 2026 prose

If the manuscript phrases the `s5x5` claim as

> first concrete instance exhibiting a strict threshold gap
> `T - k = 5`

with `cd_genus = 173` named alongside, the claim is correct
provided the surrounding prose makes clear that `173` is the
single-connected-curve Hurwitz floor (a rigidity-side number) and
that the operational realisation is the two-disjoint-Bring's
multi-cover at total genus `8`. The gap `5` is the
`product_scheme`-of-two-`sum_mod` value, fixed by the recovery
primitive, and would remain `5` under any other curve realisation
admitted by the framework.

---

## 8. Citations

- **[Chen-Cramer 2006]**, *Algebraic Geometric Secret Sharing
  Schemes and Secure Multi-Party Computations over Small Fields*,
  CRYPTO 2006, LNCS 4117, pp. 521-536.
  https://link.springer.com/chapter/10.1007/11818175_31
- **[Peng-Chen-Zhao 2021]**, *Algebraic Geometric Secret Sharing
  Schemes over Large Fields Are Asymptotically Threshold*,
  arXiv:2101.01304. https://arxiv.org/abs/2101.01304. The earlier
  Cascudo-Cramer-Xing line on threshold-gap bounds appears in
  *Bounds on the threshold gap in secret sharing*, IEEE Trans.
  Inform. Theory 59 (2013), no. 9, pp. 5600-5612, and is a
  separate paper that this note does not invoke directly.
- **[Stinson]**, *Ideal Ramp Schemes and Related Combinatorial
  Objects*. https://cs.uwaterloo.ca/~dstinson/IdealRampSchemes.pdf
- **[Cramer-Damgård-Nielsen]**, *Secure Multiparty Computation and
  Secret Sharing*, Cambridge University Press.
  https://www.cambridge.org/core/books/secure-multiparty-computation-and-secret-sharing/4C2480B202905CE5370B2609F0C2A67A
- **[Hurwitz 1893]**, *Ueber algebraische Gebilde mit eindeutigen
  Transformationen in sich*, Mathematische Annalen 41, pp. 403-442.
  DOI: 10.1007/BF01443420.

---

## Cross-references inside the framework

- `pgg-smc/reconstruct/covering_scheme.v`: `CoveringScheme`,
  `cs_gap` obligation, `sum_mod_scheme`.
- `pgg-smc/reconstruct/product_threshold.v`: `product_scheme`
  combinator.
- `pgg-smc/reconstruct/multi_covering.v`: `MultiCoveringData`,
  `mcd_total_genus`, `mcd_max_genus`.
- `pgg-smc/instances/s5x5/rigidity_s5x5_instance.v`: `s5x5_ts`,
  `s5x5_cs_gap`, `s5x5_covering`, `s5x5_multi_data`,
  `mcd_total_genus_s5x5_E`.
- `pgg-smc/instances/s5/rigidity_s5_instance.v`: comparison case
  with `T - k = 0` at genus 4.
- `pgg-smc/notes/may18aipv2026/20260516_s5x5_recovery_feasibility.md`:
  the precursor note that established the rigidity-vs-security-vs-recovery
  decoupling.
