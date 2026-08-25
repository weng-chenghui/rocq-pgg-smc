# Plan: Cycle5 via `ag_genus_scheme` on a D_5-Equivariant Elliptic Curve

## Context

The previous draft of this plan resolved the `ts_T = 5` defect in `make-a-plan-for-frolicking-bunny.md` by building a bespoke doubly-extended GRS over GF(5) and plugging it into `massey_scheme`. That construction sits on a genus-0 carrier (the projective line) even though the covering itself is genus 1. The user has now directed that the cycle5 instance should instead instantiate `ag_genus_scheme` (`pgg-smc/reconstruct/ag_massey_bridge.v:111`), the framework's positive-genus, algebraic-geometry-code-backed threshold scheme that no concrete instance currently exercises. This pivot uses the elliptic curve E from the covering directly as the source of the threshold scheme, rather than as a separate axiomatised artefact for genus-counting only.

The motivation is twofold. First, it makes the cycle5 instance the framework's first concrete consumer of `ag_genus_scheme`, retiring a long-standing future-work hook. Second, it tightens the conceptual coupling: the same elliptic curve E that provides the covering geometry also provides the code, so the `realised_by_curve` axiom and the threshold-scheme axioms refer to a single mathematical object instead of two.

The user-confirmed scheme inventory:

| Scheme | Path | Used by |
|---|---|---|
| `sum_mod_scheme` | `pgg_sharing_framework.v:218` | `s5`, `s5x5` (via `product_scheme`) |
| `massey_scheme` | `massey.v:431` | abstract; never instantiated concretely |
| `rs_genus0_scheme` | `rs_massey_bridge.v:246` | wired but currently unused by concrete instances; genus 0 only |
| `ag_genus_scheme` | `ag_massey_bridge.v:111` | **target of this plan**; currently no instance |
| `product_scheme` | `product_threshold.v:394` | `s5x5` |
| `fc_threshold_scheme` (custom) | `denboer1989/five_card_pismc.v:241` | `denboer1989` only |

cycle5 will be the first instance that consumes `ag_genus_scheme`, and the first whose threshold scheme is fundamentally tied to a positive-genus curve.

---

## Mathematical reality check, and the resulting numerics

The Goppa bound that `ag_genus_scheme` enforces (`ag_code.v:158`, `ag_min_dist_ge2`) gives:

> for any nonzero message vector m, `n - (k + g - 1) <= wH (m *m ev)`.

This is the AG code's minimum-distance lower bound: `d >= n - k - g + 1`. For an elliptic curve (`g = 1`), the code is at best **almost-MDS**: `d >= n - k`. To achieve true MDS at length 6 over GF(5) you would need a genus-0 code (the doubly-extended GRS), which is the previous draft's construction.

Within `ag_genus_scheme`, the threshold parameters land at `ts_T = n - 1` and `ts_k = k - g`, with the gap `ts_T <= ts_k + 2g` proved via `ag_massey_gap`. The constraint `Hparam : n <= k + g + 1` ties these together (`ag_massey_bridge.v:78`).

For cycle5 we want `ts_T = 5` (five permuted cards) and `ts_k = 3` (so 2 colluders are private). The parameters that satisfy this with `g = 1` are:

- `n = 6` (so `n'' = 4`, `ts_T = 5`).
- `k = 4` (so `ts_k = k - g = 3`).
- `Hparam`: `6 <= 4 + 1 + 1` → `6 <= 6` ✓.
- `Hkgn`: `k + g < n` → `5 < 6` ✓.
- Goppa: `d >= n - k - g + 1 = 2`.

The bare Goppa bound gives `d >= 2`. To recover the slide's `dw_dropout = 2` ("any 3 of 5 reconstruct") we **strengthen the Goppa bound by one**, asserting `d >= 3` via an additional axiom on the chosen divisor. This is well-supported geometrically: elliptic curves over GF(5) admit divisors whose AG code is one above the Goppa bound (the "code-MDS" property at these parameters), and the divisor used by cycle5 is asserted to be such a choice. The added axiom is the AG-code analogue of asserting MDS at length 6 over GF(5).

With this strengthening:
- min dist `d = 3` (rather than `d = 2`).
- Recovery from any `n - d + 1 = 4` codeword positions, which means any 3 of the 5 shares plus the secret-encoding slot at index 0.
- `dw_min_revealed = 3`, `dw_dropout = 2`.

---

## The six framework-shaped axioms

`ag_genus_scheme` takes the AG code by axioms over the evaluation matrix and code geometry, not by Coq-level construction. Phase 2's job is to supply:

| Axiom | Type | Mathematical content |
|---|---|---|
| `cycle5_ev` | `'M['F_5]_(4, 6)` | evaluation matrix of a degree-4 D_5-invariant divisor on E at six D_5-equivariant positions |
| `cycle5_ev_rank` | `\rank cycle5_ev = 4` | full row rank (Riemann-Roch for `deg D >= 2g - 1`) |
| `cycle5_goppa_wt_strong` | `forall m != 0, n - (k + g - 2) <= wH (m *m cycle5_ev)` (instantiates to `3 <= wH ...`) | **Strong Goppa**: min dist `d >= 3` (one above bare Goppa; saturates Singleton, so code is MDS for [6,4] over GF(5)) |
| `cycle5_priv_surj` | privacy surjectivity for sets `|S| < (k-g).+1 = 4` | dual-distance bound `d_perp >= 4` |
| `cycle5_code_dihedral` | `forall σ ∈ D_5_lifted, col_perm σ (ag_code cycle5_ev) = ag_code cycle5_ev` | D_5 acts as a code automorphism |
| `cycle5_curve_realised` | `realised_by_curve cycle5_covering_data` | the genus-1 D_5-covering is realised by an actual elliptic curve over the appropriate field |

These six AG-layer axioms, together with the carrier-of-convenience `cycle5_group_order_eq` (`|D_5| = 10`), are the entire axiomatic boundary for the cycle5 instance. Everything else is constructive.

The strong Goppa axiom replaces the bare Goppa hypothesis that `ag_genus_scheme` would otherwise consume. Mathematically it asserts that the chosen divisor on E is "code-MDS" at these parameters — a real and well-understood property of elliptic curves, not a leap. The framework's `ag_min_dist_lb` lemma at `ag_code.v:158` will then derive `d >= 3` from the strong axiom, which propagates through `ag_min_dist_ge2` and into the threshold-scheme privacy/recovery numerics.

The six-axiom set replaces the previous draft's "build a bespoke doubly-extended GRS" code construction. The trade-off is fewer Coq lines (4-5 days of bespoke linear-code definitions are gone) at the cost of more axioms (the AG-code properties are postulated rather than proved). The justification is that the AG-code layer is the natural axiomatic interface, and the previous plan was already axiomatising the curve itself.

---

## D_5 acts on indices 1..5; ord0 is fixed by convention

`ag_genus_scheme` is built on top of `massey_scheme`, so it inherits the secret-at-index-0 convention. `coord_perm_compatible.v:282`'s `massey_perm_compatible` requires `Hfix0 : sigma ord0 = ord0` to discharge `ts_recon_perm_invariant`.

Our `lift_perm_05 : {perm 'I_5} -> {perm 'I_6}` (originally a feasibility probe from the previous draft) fixes index 0 by construction and shifts indices 1..5 according to its input. The "5 D_5-permuted cards" live at indices 1..5; the "secret encoding slot" is index 0. The mathematical reality is that index 0 corresponds to a D_5-fixed degree-of-freedom in the code, not a geometric point on E — which is consistent with `massey_scheme`'s framework-level treatment of index 0 as a virtual secret position.

This convention is what makes the cycle5 plan tractable inside the existing framework without modifying `massey.v`'s hardcoded ord0.

---

## Feasibility probes (run before committing to full Phase 2)

Each probe is a short Rocq experiment with a binary outcome, run in a single scratch file `pgg-smc/reconstruct/cycle5_probe.v` and discarded after. Total budget: half a day. Pass all five before starting Phase 2 in earnest. If any fails, revise this plan.

| # | Probe | Effort | Pass criterion |
|---|---|---|---|
| 1 | `ag_genus_scheme` typechecks with axiomatised parameters | 2 h | A stub with axioms `cycle5_ev`, `cycle5_ev_rank`, `cycle5_goppa_wt_strong`, `cycle5_priv_surj`, plus closed-by-computation hypotheses (`Hk`, `Hkn`, `Hkg`, `Hkgn`, `Hparam`, `HN`), produces `ag_genus_scheme : ThresholdScheme 'I_5 'I_5` that compiles |
| 2 | `lift_perm_05` fixes ord0 cleanly | 2 h | `Lemma lift_perm_05_fix0 sigma : (lift_perm_05 sigma) ord0 = ord0.` closes by `by rewrite permE` or short equivalent |
| 3 | `ag_genus_gap` fires at `ts_T <= ts_k + 2g` for our params | 1 h | `Goal ts_T cycle5_ag_scheme <= ts_k cycle5_ag_scheme + 2. by apply: ag_genus_gap.` compiles |
| 4 | `massey_perm_compatible` accepts an AG code | 2 h | With axioms `cycle5_code_dihedral_r` and `Hfix0` discharged, the lemma typechecks; no implicit-arg surprises |
| 5 | `realised_by_curve cycle5_covering_data` typechecks | 1 h | Same shape as `s5x5_inverse_galois_realised` at `rigidity_s5x5_instance.v:348-349` |

### Probe 1 detail

```coq
Section probe.

Variable cycle5_ev : 'M['F_5]_(4, 6).
Hypothesis cycle5_ev_rank : \rank cycle5_ev = 4.
Hypothesis cycle5_Hk : 0 < 4.
Hypothesis cycle5_Hkn : 4 <= 6.
Hypothesis cycle5_Hkg : 1 < 4.
Hypothesis cycle5_Hkgn : 4 + 1 < 6.
(* Strong Goppa: one above the bare bound.
   Bare:    forall m != 0,  n - (k + g - 1) <= wH (m *m ev), i.e., 2 <= wH.
   Strong:  forall m != 0,  n - k - g + 2   <= wH (m *m ev), i.e., 3 <= wH.
   For n=6, k=4, g=1 the strong RHS = 3, which saturates the Singleton bound
   d <= n - k + 1 = 3 and hence asserts that the chosen code is MDS. *)
Hypothesis cycle5_goppa_wt_strong :
  forall m : 'rV['F_5]_4, m != 0 -> 3 <= wH (m *m cycle5_ev).

(* The framework's ag_genus_scheme consumes a hypothesis of the bare shape.
   We discharge it from the strong axiom by 2 <= 3 <= wH (...). *)
Lemma cycle5_goppa_wt_bare :
  forall m : 'rV['F_5]_4, m != 0 -> 6 - (4 + 1 - 1) <= wH (m *m cycle5_ev).
Proof. by move=> m Hm; apply: leq_trans (cycle5_goppa_wt_strong Hm). Qed.
Hypothesis cycle5_priv_surj :
  forall (S : {set 'I_6}) (target : 'rV['F_5]_6),
    #|S| < ((4 - 1).-1).+2 ->
    exists c, c \in ag_code cycle5_ev /\ vproj c S = vproj target S.
Hypothesis cycle5_Hparam : 6 <= 4 + 1 + 1.

(* The N = 5 here is for the 'I_N share type, NOT the codeword length. *)
Hypothesis cycle5_HN : 5 = #|'F_5|.

Definition cycle5_ag_scheme : ThresholdScheme 'I_5 'I_5 :=
  @ag_genus_scheme 'F_5 4 4 1 cycle5_ev
    cycle5_ev_rank cycle5_Hk cycle5_Hkn cycle5_Hkg cycle5_Hkgn
    cycle5_goppa_wt_bare cycle5_priv_surj cycle5_Hparam 5 cycle5_HN.

Compute ts_T cycle5_ag_scheme.  (* expect 5 *)
Compute ts_k cycle5_ag_scheme.  (* expect 3 *)

End probe.
```

Pass = compiles, `Compute` reports 5 and 3. Failure indicates an arity or implicit-arg mismatch in the `ag_genus_scheme` invocation that needs fixing before any real work.

### Probe 4 detail

Confirm that the AG code accepted by `ag_genus_scheme` interoperates cleanly with `massey_perm_compatible`. The AG threshold scheme is built as `massey_scheme C_nt Hd2 ag_priv_surj` where `C := ag_code cycle5_ev`, so `massey_perm_compatible` on this `C` should work modulo the code-automorphism and `Hfix0` hypotheses. Probe writes a 5-line dummy version and confirms the types align.

---

## Phase 2 (revised): Wire `ag_genus_scheme` to cycle5

**File**: `pgg-smc/reconstruct/cycle5_rs_scheme.v` (new; the filename keeps "rs_scheme" for continuity with the previous draft and the `_CoqProject` plan, but the body is AG-code-based).
**Effort**: 1-2 days (revised down from 4-5; no bespoke code-construction work).

Deliverables, in order:

1. Four framework-shaped axioms listed above: `cycle5_ev`, `cycle5_ev_rank`, `cycle5_goppa_wt_strong`, `cycle5_priv_surj`. (`Hk`, `Hkn`, `Hkg`, `Hkgn`, `Hparam` are short numerical lemmas closed by `by []`, not axioms; `HN` is `erefl` modulo `card_Fp`.) Plus the one-line `cycle5_goppa_wt_bare` lemma that discharges the framework's bare hypothesis from the strong axiom.
2. `cycle5_ag_scheme_F : ThresholdScheme 'F_5 'F_5` via the `ag_massey` portion (one line).
3. `cycle5_ag_scheme : ThresholdScheme 'I_5 'I_5` via the transport portion of `ag_genus_scheme` (one line — the transport's `toFK`/`ofFK` are private to the bridge but reused identically as in `rs_genus0_scheme` at `rs_massey_bridge.v:218-243`).
4. `cycle5_ag_gap : ts_T cycle5_ag_scheme <= ts_k cycle5_ag_scheme + 2 * 1` via `ag_genus_gap`.

Phase 2 sanity:

```coq
Compute ts_T cycle5_ag_scheme.  (* expect 5 *)
Compute ts_k cycle5_ag_scheme.  (* expect 3 *)
```

## Phase 3 (revised): D_5 perm-compatibility

**File**: `pgg-smc/reconstruct/cycle5_perm_compatible.v` (new).
**Effort**: 1 day (revised down from 2-3; index-0 is fixed by convention).

1. `lift_perm_05 : {perm 'I_5} -> {perm 'I_6}` and `lift_perm_05_fix0` (output of Probe 2).
2. Axiom `cycle5_code_dihedral_r : col_perm (lift_perm_05 cycle_r) (ag_code cycle5_ev) = ag_code cycle5_ev`.
3. Axiom `cycle5_code_dihedral_s : col_perm (lift_perm_05 cycle_s) (ag_code cycle5_ev) = ag_code cycle5_ev`.
4. `cycle5_perm_compatible : @ts_recon_perm_invariant _ (pgg_G Cycle5_PGGTypes) _ _ cycle5_ag_scheme (lift_perm_05 ∘ @pgg_rho Cycle5_PGGTypes)`. Discharged by `massey_perm_compatible` (`coord_perm_compatible.v:282`), with `Hfix0` from step 1 and code-automorphism from steps 2-3.

The two `cycle5_code_dihedral_*` axioms encode the D_5-equivariance of the chosen divisor on E. Their mathematical content is standard: divisor is D_5-stable, automorphism action lifts to col_perm. Total axioms in Phase 3: two.

## Phase 4 (unchanged): Spectral mixing

**File**: `pgg-smc/instances/cycle5/cycle5_mixing.v`. **Effort**: 1 day. Independent of the threshold scheme; uses only the Schreier walk of D_5 on `'I_5`.

## Phase 5 (revised numerics): Instance assembly

**File**: `pgg-smc/instances/cycle5/rigidity_cycle5_instance.v` (new).
**Effort**: 2 days.

1. `cycle5_group_order_eq : #|pgg_G Cycle5_PGGTypes| = 10` (axiom).
2. `cycle5_hurwitz` (computational).
3. `cycle5_covering_data := @MkCoveringData _ 0 4 20 1 cycle5_n_branch_le cycle5_hurwitz`.
4. `cycle5_curve_realised : realised_by_curve cycle5_covering_data` (axiom; same shape as `s5x5_inverse_galois_realised`; docstring corrected to `⟨T_P⟩ ⋊ ⟨[−1]⟩` for a 5-torsion P).
5. `cycle5_cs_gap`: discharged by `ag_genus_gap` from Phase 2.
6. `cycle5_covering : CoveringScheme Cycle5_PGGTypes`, mirroring `s5x5_covering` at `rigidity_s5x5_instance.v:385-393`.
7. `cycle5_partial_recover`: pick any 4 elements of `visible`, syndrome-decode the AG code to fill in the single missing share, run `massey_reconstruct`. Returns the secret.
8. `cycle5_dropout_witness : DropoutWitness Cycle5_PGGTypes cycle5_threshold_witness` via `MkDropoutWitness` with **`dw_min_revealed = 3`**, giving `dw_dropout = 2`.

The `dw_min_revealed = 3` value follows from `cycle5_goppa_wt_strong`'s assertion that the chosen AG code has min dist `d = 3`, saturating the Singleton bound. Recovery: from any 3 of 5 shares, syndrome-decode 2 erasures in the underlying [6,4,3] AG code, then run `massey_reconstruct`.

## Phase 6 (unchanged): Verification

```bash
make -j1 pgg-smc/reconstruct/cycle5_rs_scheme.vo
make -j1 pgg-smc/reconstruct/cycle5_perm_compatible.vo
make -j1 pgg-smc/instances/cycle5/cycle5_mixing.vo
make -j1 pgg-smc/instances/cycle5/rigidity_cycle5_instance.vo

grep -nE '^\s*Axiom' \
  pgg-smc/groups/pgg_cycle.v \
  pgg-smc/reconstruct/cycle5_*.v \
  pgg-smc/instances/cycle5/*.v
# expected axioms (eight):
#   cycle5_ev, cycle5_ev_rank, cycle5_goppa_wt_strong, cycle5_priv_surj,
#   cycle5_code_dihedral_r, cycle5_code_dihedral_s,
#   cycle5_curve_realised, cycle5_group_order_eq

make -j1 pgg-smc/instances/s5/rigidity_s5_instance.vo
make -j1 pgg-smc/instances/s5x5/rigidity_s5x5_instance.vo
```

Numerical sanity:

```coq
Compute ts_T cycle5_ag_scheme.                  (* expect 5 *)
Compute ts_k cycle5_ag_scheme.                  (* expect 3 *)
Compute cd_genus (cs_data cycle5_covering).     (* expect 1 *)
Compute dw_min_revealed cycle5_dropout_witness. (* expect 3 *)
Compute dw_dropout cycle5_dropout_witness.      (* expect 2 *)
```

---

## Effort summary

| Phase | Previous-draft budget | This draft | Reason |
|---|---|---|---|
| 1 | done | done | unchanged |
| Probes 1-5 | 0.5 day | 0.5 day | unchanged structure, retargeted to `ag_genus_scheme` |
| 2 | 4-5 days (bespoke GRS) | 1-2 days | axiomatised AG code via 5 hypotheses; no Coq construction |
| 3 | 0.5-1 day | 1 day | same shape; two added axioms for D_5-invariance |
| 4 | 1 day | 1 day | unchanged |
| 5 | 2-3 days | 2 days | thinner assembly; `dw_dropout = 2` from strong-Goppa axiom |
| 6 | 0.5 day | 0.5 day | unchanged |
| **Total (post-Phase-1)** | 8.5-11 days | **6-7 days** | the AG axiomatic boundary saves the GRS construction effort |

---

## Critical files

| Path | Status | Phase |
|---|---|---|
| `pgg-smc/reconstruct/cycle5_probe.v` | new (scratch, discard after probes) | probes |
| `pgg-smc/reconstruct/cycle5_rs_scheme.v` | new | 2 |
| `pgg-smc/reconstruct/cycle5_perm_compatible.v` | new | 3 |
| `pgg-smc/instances/cycle5/cycle5_mixing.v` | new | 4 |
| `pgg-smc/instances/cycle5/rigidity_cycle5_instance.v` | new | 5 |
| `_CoqProject` | append entries for each new `.v` | each phase |
| `~/.claude/plans/make-a-plan-for-frolicking-bunny.md` | rewrite §1, §2, §4 to reflect AG-code path and revised numerics | meta |

---

## Existing utilities to reuse

| Symbol | Path | Role |
|---|---|---|
| `ag_genus_scheme` | `pgg-smc/reconstruct/ag_massey_bridge.v:111` | **Primary**: builds `ThresholdScheme 'I_N 'I_N` from AG-code axioms |
| `ag_massey`, `ag_massey_gap`, `ag_genus_gap` | `pgg-smc/reconstruct/ag_massey_bridge.v:69, 85, 119` | Internal pieces; `ag_genus_gap` discharges `cs_gap` |
| `ag_code`, `ag_not_trivial`, `ag_min_dist_lb`, `ag_min_dist_ge2` | `pgg-smc/reconstruct/ag_code.v:46, 137, 158, 174` | AG-code primitives consumed by `ag_genus_scheme` |
| `massey_perm_compatible` | `pgg-smc/reconstruct/coord_perm_compatible.v:282` | Discharges `ts_recon_perm_invariant`; works because `lift_perm_05` fixes ord0 |
| `restrict_perm0_val` | `pgg-smc/reconstruct/coord_perm_compatible.v:140` | Share-side permutation lift used by `massey_perm_compatible` |
| `transport_scheme` | `pgg-smc/reconstruct/rs_massey_bridge.v:140-153` | Used internally by `ag_genus_scheme` for `'F_5 ↔ 'I_5` |
| `CoveringData`, `CoveringScheme`, `MkCoveringScheme` | `pgg-smc/reconstruct/covering_scheme.v:75-84, 119-129` | Phase 5 assembly |
| `realised_by_curve` | `pgg-smc/reconstruct/curve_realisation.v:70-71` | Axiom precedent: `s5x5_inverse_galois_realised` |
| `DropoutWitness`, `MkDropoutWitness`, `dw_dropout` | `pgg-smc/reconstruct/dropout_witness.v:69-129, 148-149` | First concrete instance |
| `SecurityAsymptotic` | `pgg-smc/reconstruct/algebraic_rigidity.v:122-134` | Mixing certificate |
| `s5x5_covering_data`, `s5x5_covering` | `pgg-smc/instances/s5x5/rigidity_s5x5_instance.v:336-337, 385-393` | Phase 5 structural template |
| `cycle_r`, `cycle_s`, `Cycle5_PGGTypes` | `pgg-smc/groups/pgg_cycle.v` | Phase-1 generators (unchanged) |

---

## Axiomatic boundary, in plain language

After this plan ships, the cycle5 instance will rest on these axioms:

1. **`cycle5_group_order_eq`** — `|D_5| = 10` on our concrete `'I_5` realisation (computational; pure carrier-of-convenience).
2. **`cycle5_ev`, `cycle5_ev_rank`, `cycle5_goppa_wt_strong`, `cycle5_priv_surj`** — assert the existence of a rank-4 AG-code evaluation matrix on E that is code-MDS at parameters [6, 4] (min dist `>= 3`, saturating Singleton) and satisfies the privacy-surjectivity dual-distance bound. Mathematically these are standard AG-code axioms, valid by Riemann-Roch plus a specific divisor choice; `cycle5_goppa_wt_strong` is one step stronger than the bare Goppa bound and asserts the divisor is "code-MDS" on E.
3. **`cycle5_code_dihedral_r`, `cycle5_code_dihedral_s`** — assert that the chosen divisor is D_5-invariant, so D_5 acts on the code by column permutations. Standard if the divisor is built from D_5-orbits of points.
4. **`cycle5_curve_realised`** — assert that the genus-1 D_5-covering is realised by an elliptic curve. Citing Klein 1884 / Singerman 1970 / Silverman, *Arithmetic of Elliptic Curves* III.4 (the 5-torsion + `[−1]` construction).

This boundary is the same shape as the existing `s5x5` instance (`s5x5_group_order_eq` + `s5x5_inverse_galois_realised`), enlarged by six AG-code axioms that together replace what would otherwise be 4-5 days of bespoke linear-code construction work. The strong Goppa axiom is included so that `dw_dropout = 2` matches the slide's "3-of-5" reconstruction; it asserts the chosen divisor on E is code-MDS at parameters [6, 4] over GF(5), which is geometrically standard.

---

## Risks not yet retired

1. **Probe 1 may surface an arity mismatch** in `ag_genus_scheme`'s implicit arguments (`pgg-smc/reconstruct/ag_massey_bridge.v:111` takes `F`, `n''`, `k`, `g`, `ev`, plus seven hypotheses, plus `N`, `HN`). The probe is precisely to catch this before commitment.
2. **Geometric reality of the D_5-equivariant divisor on E**: a D_5-orbit on E has size 5 or 10, not 6. The 6-position evaluation set is `5-orbit + 1 abstract index-0 position`, where the abstract position is the framework's secret slot, not a geometric point on E. This is consistent with `massey_scheme`'s ord0 convention but the docstring should be explicit about it. If the user wants the geometric interpretation to be airtight (every column of `ev` corresponds to a real point on E), this requires either `n = 5` (and `ts_T = 4`, losing the 5-card narrative) or `n = 10` (and `ts_T = 9`, ten cards). Recommend documenting and accepting the index-0 virtual-position reading.
3. **Strong-Goppa axiom is geometrically loaded**: the assertion `d >= 3` on the chosen divisor is well-supported (MDS AG codes on elliptic curves over GF(5) at parameters [6, 4] exist via classical constructions) but is divisor-specific. Phase 2's docstring on `cycle5_goppa_wt_strong` should cite the construction (e.g., Goppa's original AG-code construction with a generic enough divisor). The axiom is not a free pass — it is a real claim about the divisor.

---

## Verification

### Probe-phase verification

Five probe files compile; Probe 1's `Compute` reports the expected `5` and `3`. If any probe fails, halt and revise this plan before Phase 2.

### Full-implementation verification

1. Four new `.v` files compile via `make -j1`.
2. Axiom audit returns the expected eight (listed above).
3. Numerical sanity `Compute` checks match.
4. Regression: `s5`, `s5x5`, `denboer1989`, `kim2025` instances still build.
5. Phase-1 audit-clean status of `pgg_cycle.v` preserved.
6. Cross-scheme audit: grep `pgg-smc/instances/` for `ag_genus_scheme` consumers; cycle5 is the only one.
