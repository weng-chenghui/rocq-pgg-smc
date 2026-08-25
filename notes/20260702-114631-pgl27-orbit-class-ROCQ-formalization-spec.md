> STATUS (2026-07-12): IMPLEMENTED. All eight files landed on branch pgg-smc, all Qed; see docs/superpowers/plans/2026-07-11-pgl27-orbit-class.md and memory project_pgl27_instance_landed. Axioms: pgl27_3transitive (justified L2) + boolp trio; pgl27_card deleted in the same-day audit follow-up (zero consumers). orbit_class_split (42/28) proven axiom-free. Note: landed orbit_class true = 28-orbit (equianharmonic), inverting the labeling in sections 2 and 6 below. The ramp is two-sided: coalition privacy for size <= 3, monotone leakage under coalition inclusion (pgl27_view_leakage_le), and a concrete four-card coalition with positive mutual information (pgl27_view_leak_k4); recovery still reads all 8 revealed cards (no sub-8 recovery).
# ROCQ formalization spec: PGL(2,7) orbit-class-secret PGG instance + the transitivity-privacy bridge

Date: 2026-07-02
Status: design validated (all shapes typecheck against live framework; see the
probe verdict in [[20260702-100428-orbit-class-secret-plain-english]]). Ready to
plan implementation.

Companion research: the ladder report [[20260701-175221-report-shuffle-matters-group-ladder]],
the verification template [[20260701-173005-shuffle-matters-verification-template]],
the plain-English explainer [[20260702-100428-orbit-class-secret-plain-english]].

## 1. Scope and non-goals

In scope:
- A new PGG instance `pgl27`: a card scheme on 8 points whose secret is the PGL(2,7)
  orbit-class (cross-ratio class) of the dealt 4-heart-subset, shuffled by a uniform
  draw from PGL(2,7).
- A reusable framework bridge: t-transitivity of the shuffle group discharges the
  threshold privacy field `ts_private`. Stated once, reusable for A5 and Mathieu.
- The security direction only: privacy for coalitions of size <= 3 (k=3), and
  reconstruction from the full dealt row.

Explicit non-goals:
- No gray-zone (coalition size 4,5,6) leakage witness. Those exact mutual-information
  values are the infeasible enumeration; they are not proved.
- No AG-code / covering-curve recovery. Recovery is reveal-all. The Klein /
  Riemann-Hurwitz / `pgl_bound` machinery is a different role of PGL and is not used.
- No Mathieu (t=4,5) rung. Future work; the bridge is written to accept it.
- The report's "T=7, revealing N-1 determines the secret" is finer than the
  framework's all-N reconstruction and is not modelled natively.

Governance: PGL(2,7) is outside the current documented instance scope
(kim2025 / denboer1989 / s5 / s5x5). Building it is a scope-expansion decision.

## 2. The scheme (precise)

- Points: `'I_8` identified with the projective line P^1(F_7) = F_7 cup {infinity}
  by 0..6 -> field elements 0..6, 7 -> infinity.
- Deck: a fixed multiset of 4 hearts and 4 clubs placed on the 8 points. Colour is
  read by a face map from the position code.
- Arrangement: a choice of which 4 positions carry hearts (a 4-subset of `'I_8`).
- Secret `s : bool`: the PGL(2,7) orbit-class of the heart-4-subset. The 70 = C(8,4)
  4-subsets split into two PGL-orbits, sizes 42 and 28, separated by cross-ratio class
  (harmonic vs equianharmonic). `false` |-> the 28-orbit, `true` |-> the 42-orbit.
- Shuffle: one uniformly random `g in PGL(2,7)` acting on the 8 points, applied to the
  arrangement. |PGL(2,7)| = 336.
- Privacy k = 3: every coalition of <= 3 revealed cards has a colour distribution
  identical across the two secrets (PGL(2,7) is sharply 3-transitive).
- Recovery: the full revealed row determines the heart-4-subset, hence its orbit-class.

## 3. Locked design decisions (from the shape probe)

| # | Decision | Rationale |
|---|----------|-----------|
| D1 | Monodromy via `@Gen_PGGTypes 2 6 pgl27_gens`, pgg_rho = identity inclusion into S_8. | The `pgl2` quotient action is ~hundreds of lines; `Gen_PGGTypes` gives the morphism free. |
| D2 | `pgl2` (from `pgl_bound.v`) used ONLY for the cardinality fact `#|PGL(2,7)| = 336`. | Its role is the Klein ceiling, not a shuffle. Do not conflate. |
| D3 | Secret type `bool`; scheme `ThresholdScheme bool 'I_8`, mirroring den Boer's `fcI_scheme` at N=8. | Probe: typechecks with zero friction. |
| D4 | `ts_T' := pgg_N' pgl_M` (= 7), `ts_k' := 3`, `shareT := 'I_(pgg_N' pgl_M).+1`. | Makes `rp_scheme` / `rp_monodromy` types match definitionally, no transport. |
| D5 | Privacy witness is RE-DEALING, not group-masking. | Sharp 3-transitivity => trivial 3-point stabiliser; a coalition-fixing g is the identity and cannot flip the orbit bit. `rp_monodromy` powers correctness only. |
| D6 | Proved abstractly over the group; no `vm_compute` on permutations. | Same reason s5/s5x5 are abstract; keeps it feasible. |
| D7 | Security witness `sw_bound_eps = 0`, `sw_exact` populated. | Uniform draw over a transitive group => single-card marginal exactly uniform, axiom-free (cleaner than s5's Schreier walk). |
| D8 | Instance is s5-style secret-sharing (empty input prologue), not a den Boer function-evaluation family. | The dealer picks the orbit secret; there are no committed inputs. |

## 4. File and module plan

New instance directory `pgg-smc/instances/pgl27/`, mirroring `s5/`, mapped in
`_CoqProject` by `-R pgg-smc/instances/pgl27 pgg_smc`. The reusable bridge lives in
the reconstruct layer (`pgg_reconstruct`).

| File | Purpose | Key contents |
|------|---------|--------------|
| `pgg-smc/reconstruct/transitivity_privacy.v` | REUSABLE bridge (framework). | Theorem A (monotone ramp), Theorem B (t-transitivity => hypergeometric secret-independence => `ts_private`). Group-agnostic. |
| `pgg-smc/instances/pgl27/pgl27_group.v` | The shuffle group. | The 8-point / P^1(F_7) identification, the generators `pgl27_gens`, `pgl_M := @Gen_PGGTypes 2 6 pgl27_gens`, `pgl27_card` (336), `pgl_3transitive`. |
| `pgg-smc/instances/pgl27/pgl27_orbit.v` | The secret invariant. | `orbit_class : 8.-tuple 'I_8 -> bool` (cross-ratio classifier), the 42/28 split, `orbit_class_invariant` (PGL-invariance), `orbit_encode` + `orbit_encodeK`. |
| `pgg-smc/instances/pgl27/pgl27_scheme.v` | The threshold scheme + plug. | `orbit_scheme : ThresholdScheme bool 'I_8`, `orbit_correct`, `orbit_private` (via the bridge), `orbit_plug : ReconPlug pgl_M bool`, `orbit_recon_invariant`. |
| `pgg-smc/instances/pgl27/pgl27_profile.v` | Framework assembly. | `pgl27_PI : PGGInterface`, `pgl27_security : SecurityWitness` (eps=0 exact), `pgl27_profile : MonodromyProfile`. |
| `pgg-smc/instances/pgl27/pgl27_secrecy.v` | Secrecy witness. | `pgl27_view_indep` (from Theorem B), `pgl27_trace_secrecy : H(secret | trace) = H(secret)` via `trace_secrecy_of_view`. |
| `pgg-smc/instances/pgl27/pgl27_run.v` | Correctness end-to-end. | `pgl27_run_recovers`: recon of the dealt-then-shuffled encoding returns the secret. |

## 5. Framework record instantiation (concrete field values)

| Record (file:line) | Field | Value |
|--------------------|-------|-------|
| `PGGTypes` / `isMonodromyRepr` (pgg_interface.v:38,56) | via `@Gen_PGGTypes 2 6 pgl27_gens` | pgg_gT = {perm 'I_8}, pgg_N' = 7, pgg_G = <<pgl27_gens>>, pgg_rho = inclusion. |
| `ThresholdScheme bool 'I_8` (pgg_sharing_framework.v:47) | ts_T' | 7 (= pgg_N' pgl_M) |
| | ts_k' | 3 |
| | ts_valid s sh | `orbit_class sh = s` |
| | ts_recon | `orbit_class` |
| | ts_encode | `orbit_encode` |
| | ts_correct | `by []` (valid means orbit_class sh = s) |
| | ts_private | `orbit_private` (bridge) |
| | ts_encode_valid | from `orbit_encodeK` |
| `ReconPlug pgl_M bool` (covering_scheme.v:117) | rp_scheme | `orbit_scheme` |
| | rp_content | face map (position code -> heart/club); `id` acceptable if colour folded into orbit_class |
| | rp_monodromy | `fun g => @pgg_rho pgl_M g` |
| | rp_recon_invariant | `orbit_recon_invariant` |
| `PGGInterface pgl_M` (pgg_interface.v:379) | pi_T' | 7 |
| | pi_starts | `ord_tuple 8` |
| | pi_starts_uniq | `ord_tuple_uniq` |
| `SecurityWitness` (algebraic_rigidity.v:147) | sw_bound_eps | 0 |
| | sw_rho_dist | uniform on the pgg_rho image |
| | sw_bound | exact: transitive uniform => single-card marginal is uniform |
| | sw_exact | `Some ...` |
| `MonodromyProfile` (pgg_monodromy_profile.v:50) | (mp_M, mp_secretT=bool, mp_PI, mp_security, mp_plug) | the above |

## 6. Definitions and lemmas (statement + strategy + risk)

Strategy/risk columns are PLANNING notes; they do NOT go into the eventual code
comments (which follow the terse-statement rule).

### pgl27_group.v

- `pgl27_gens : 3.-tuple {perm 'I_8}` — the three Möbius generators of PGL(2,7) on
  P^1(F_7): translation `z |-> z+1`, scaling by a primitive root `z |-> 3z`, and
  inversion `z |-> -1/z` (infinity handled by the P^1 identification).
  Note: two generators lying in PSL (translation, inversion) give only the
  2-transitive PSL(2,7); the non-square scaling `z |-> 3z` is required to reach the
  full sharply-3-transitive PGL(2,7). Hence three generators.
- `pgl_M := @Gen_PGGTypes 2 6 pgl27_gens`.
- `pgl27_card : #|pgg_G pgl_M| = 336`. Strategy: relate to `card_pgl2`/`card_Fp`;
  or `order`-of-generated-subgroup. RISK: MEDIUM. May need a justified computational
  axiom (s5 precedent, [[project_s5_group_order_axiom]]).
- `pgl_3transitive : ntransitive 3 (@pgg_rho pgl_M @* pgg_G pgl_M) [set: 'I_8] 'P`.
  Strategy A (structural): the Möbius action on P^1(F_q) is sharply 3-transitive
  (three distinct points determine a unique Möbius map); combine with
  `<<pgl27_gens>> = full Möbius group` (via `pgl27_card` = 336). Strategy B
  (fallback): justified computational axiom, as s5 does for its group order.
  RISK: HIGH. This is the load-bearing group-theory obligation.

### pgl27_orbit.v

- `cross_ratio : 'I_8 -> 'I_8 -> 'I_8 -> 'I_8 -> F_7 cup {undef}` — the projective
  cross-ratio of four points (partial; total on distinct 4-tuples).
- `orbit_class : 8.-tuple 'I_8 -> bool` — reads the heart-4-subset from the tuple
  (via the face map) and returns its cross-ratio class (`true` = 42-orbit,
  `false` = 28-orbit). Concretely, a decidable predicate on the 4-subset.
  RISK: MEDIUM (defining a total, decidable, well-behaved classifier).
- `orbit_class_split : #|[set S | orbit_class ... S] | = 42` and `= 28` for the two
  classes. Strategy: orbit-stabiliser under PGL; or direct count. RISK: MEDIUM.
- `orbit_class_invariant : forall g in pgg_G pgl_M, forall sh,
     orbit_class [tuple tnth sh (@pgg_rho pgl_M g i) | i] = orbit_class sh`.
  The cross-ratio class is PGL-invariant. Strategy: cross-ratio is a PGL-invariant
  of 4-tuples; lift to the 4-subset. RISK: MEDIUM. Feeds `orbit_recon_invariant`.
- `orbit_encode : bool -> 8.-tuple 'I_8` — a canonical representative arrangement in
  each orbit. `orbit_encodeK : orbit_class (orbit_encode s) = s`. RISK: LOW.

### pgl27_scheme.v

- `orbit_scheme : ThresholdScheme bool 'I_8` — fields per section 5. `orbit_correct`
  `by []`. RISK: LOW (probe confirmed the shape).
- `orbit_private : ts_private orbit_scheme` — instantiate the bridge (Theorem B)
  with `pgl_3transitive`, `orbit_class_invariant`, deck-stability, and the 42/28
  non-triviality. RISK: MEDIUM, gated on Theorem B.
- `orbit_plug : ReconPlug pgl_M bool` — per section 5.
- `orbit_recon_invariant : ts_recon_perm_invariant ...` — from
  `orbit_class_invariant`. RISK: LOW given the invariance lemma.

### pgl27_profile.v / pgl27_run.v / pgl27_secrecy.v

- `pgl27_security` : `sw_bound` discharged exactly (eps=0) because the uniform draw
  over the transitive `pgg_G` pushes forward to the uniform single-card marginal.
  Strategy: orbit-stabiliser / transitive-uniform. RISK: LOW.
- `pgl27_run_recovers : ts_recon orbit_scheme (dealt-then-shuffled encoding) = s`.
  Strategy: `orbit_recon_invariant` + `orbit_encodeK`, mirroring `s5_run_recovers`.
  RISK: LOW.
- `pgl27_view_indep` : the <= 3-coalition view is independent of the secret. From
  Theorem B. `pgl27_trace_secrecy : H(secret | player_trace) = H(secret)` via
  `trace_secrecy_of_view` (pgg_trace_secrecy.v:38), mirroring `s5_trace_secrecy`.
  RISK: MEDIUM, gated on Theorem B.

## 7. Reusable theorems (the library contribution)

In `pgg-smc/reconstruct/transitivity_privacy.v`. Group-agnostic; instantiated by
`pgl27` now, by A5 / Mathieu later.

- Theorem A (monotone leakage ramp). For position-subsets `A subset B`,
  `mutual_info (Secret, ViewA A) <= mutual_info (Secret, ViewA B)`. Because `ViewA A`
  is a deterministic sub-tuple of `ViewA B`, so `Secret - ViewA B - ViewA A` is a
  Markov chain. Anchor: infotheo `data_processing_inequality`
  (information_theory/entropy.v:1634) plus `mutual_infoEcentropy1`. Role: makes the
  privacy region down-closed, so (k,T) is well-defined. Plumbing: lift the
  fdist-level DPI to the RV/`ViewA` level. RISK: MEDIUM. Priority: framework
  completeness (not strictly required to discharge `ts_private`).
- Theorem B (transitivity privacy bridge). If the shuffle group acts t-transitively
  on the N positions and the deck multiset is fixed across secrets, then every
  coalition `C` with `#|C| <= t` has a view distribution identical across secrets;
  and for a secret that is an orbit-class invariant, this discharges `ts_private`
  (a matching alternative sharing exists by equal support of the <= t hypergeometric
  marginals). Anchors: mathcomp `ntransitive`/`dtuple_on`
  (solvable/primitive_action.v:159) and orbit-stabiliser. RISK: HIGH. This is the
  load-bearing new proof and the novel formal contribution.
  Side-hypotheses (exact, from the probe): `Htrans` (t-transitivity), `Hinv`
  (orbit_class is invariant under the coordinate action), `Hdeck_stable` (deck
  preserved by the action), `Hpopulated` (both orbit values attained), `#|C| < t+1`.

Naming discipline (from the literature audit, load-bearing):
- Call the group / permutation set "t-transitive" or "t-wise uniform"; call the
  colour distribution "sampling without replacement / hypergeometric marginal".
  Do NOT name the marginal "t-wise uniform".
- Do NOT phrase Theorem B as "independent of which orbit": the t-design incidence is
  per-orbit (PGL(2,7)'s two 4-subset orbits are 3-(8,4,3) and 3-(8,4,2)). The truth
  is that the <=t POSITION-marginal of a fixed deck sees only the colour counts.
- Cite Cameron (Handbook of Combinatorics, Thm 5.2) and design theory; present the
  privacy corollary as our application, not new mathematics.

## 8. Proof-obligation risk ranking and strategies

| Obligation | Risk | Primary strategy | Fallback |
|-----------|------|------------------|----------|
| `pgl_3transitive` | HIGH | sharp-3-transitivity of Möbius on P^1(F_7) + `<<gens>>=PGL` via card 336 | justified computational axiom (s5 precedent) |
| Theorem B (bridge => ts_private) | HIGH | orbit-stabiliser => uniform t-tuple => hypergeometric marginal => equal support => re-dealing witness | prove the equal-support existence combinatorially over the 70 subsets |
| `orbit_class_invariant` | MED | cross-ratio is a PGL-invariant of 4-tuples | per-generator invariance check |
| `pgl27_card` = 336 | MED | `card_pgl2` bridge or generated-subgroup order | justified axiom |
| `orbit_class` / `orbit_class_split` | MED | decidable cross-ratio predicate; orbit-stabiliser counts | finite decision |
| Theorem A (monotone ramp) | MED | DPI lift to RV level | conditioning-reduces-entropy route |
| scheme/plug/profile/run assembly | LOW | mirror s5 / den Boer | — |
| `pgl27_security` (eps=0) | LOW | transitive-uniform marginal | — |

Axiom-hygiene policy: target boolp-only (like the other instances). Any custom
axiom (candidate: the group-order / 3-transitivity computation) must be isolated,
named, and justified in-file with the s5 precedent, and reported at merge. Prefer a
structural proof; accept an axiom only if the computation is intractable in-kernel.

## 9. Build, audit, and verification plan

- `_CoqProject`: add `-R pgg-smc/instances/pgl27 pgg_smc`.
- Compile order: `transitivity_privacy` -> `pgl27_group` -> `pgl27_orbit` ->
  `pgl27_scheme` -> `pgl27_profile` -> `pgl27_run` -> `pgl27_secrecy`.
- Build single-file only: `make -j1 <path>.vo`. Never concurrent (RAM).
- Validate with rocq-mcp (`rocq_check` / `rocq_step_multi`) during proof; reserve
  `make -j1` for dependency refreshes.
- Audit gate: H-series (role tags on every Lemma/Definition) and I-series (naming:
  no metaphor identifiers, canonical MathComp suffixes) must pass. Statement comments
  follow the terse declarative rule.
- Axiom check: `rocq_assumptions` on the final targets; report the axiom set.

## 10. Milestones

1. `transitivity_privacy.v`: Theorems A and B (the reusable core). Gate: B typechecks
   and its `ts_private` conclusion matches the framework field.
2. `pgl27_group.v`: generators, card, `pgl_3transitive`. Gate: 3-transitivity closed
   (structural or justified axiom).
3. `pgl27_orbit.v`: `orbit_class`, invariance, 42/28 split, encode.
4. `pgl27_scheme.v`: `orbit_scheme` + `orbit_private` (instantiate B) + `orbit_plug`.
5. `pgl27_profile.v` + `pgl27_run.v`: assembly + correctness (mirror s5).
6. `pgl27_secrecy.v`: `pgl27_trace_secrecy` via the keystone.
7. Audit + axiom report + commit.

## 11. Novelty positioning (for a later write-up)

Novel: the orbit-class secret (Item 1), the machine-checked formalization (Item 4),
and the named privacy bridge (Item 3). Scoped-novel: the coalition-privacy framing
of the transitivity ladder (Item 2 is otherwise prior art: Kaplan-Naor-Reingold
2005/2009; Finucane-Peled-Yaari 2015). Cite Cameron + design theory for the
mathematics, Koch-Walzer-Härtel / Koch-Walzer for the uniform-closed-shuffle
primitive, den Boer for the lineage.

## 12. Open items deferred to implementation

- Whether `pgl_3transitive` and `pgl27_card` close structurally or need a justified
  axiom (decide once the Möbius action is in place).
- The exact `rp_content` face map vs folding colour into `orbit_class` (choose the
  one that keeps `orbit_recon_invariant` cheapest).
- Whether Theorem A is upstreamed to infotheo or kept local (default: local, note as
  upstreamable).
