# Plan: new "Prototyping Result" section between Vnzil and bjHmm

## Context

The user is preparing a poster (`pgg-smc/notes/may18aipv2026/poster.pen`) and noticed
that the audience never receives an explicit statement of what the framework actually
delivers. They want a new section inserted between slides `Vnzil` ("01 / The Idea")
and `bjHmm` ("02 / Prototyping Results") that explains the *outcome of the inverting
flow*. Two existing framing slides currently sitting at the bottom of the canvas
(`ioEmi`, `KTtZU`) should be moved into this new section. New pages explaining the
six concrete outcomes the user typed will extend horizontally from the same row.

The user explicitly asked, in this order:

1. Split their (long, mixing) sentences into succinct one-idea items.
2. Read the code to honestly grade the current status of each item, flagging vacuous
   / axiomatized / interface-only content.
3. Per item produce a table: how to phrase it on a slide (or skip if too vacuous),
   plus what to improve in the codebase.
4. Once the plan is written, run an adversarial-but-honest audit agent on it.

Layout planning of the actual Pencil slides is **deferred** to the implementation
phase; this plan is about *content honesty* only.

## Phase-1 evidence base

Three parallel Explore agents read the framework spine, the four in-scope
instances (kim2025, denboer1989, s5, s5x5; per memory the other instance
directories are out of scope), and the `reconstruct/` machinery. The
findings below are quoted with line numbers where load-bearing.

### Framework spine
- `protocol/pgg_interface.v` accepts any morphism `pgg_rho : G -> {perm 'I_N}`
  including the trivial one. The only enforced obligation is
  `pgg_sigmas_gen` (generators span `G`), and that is satisfiable even by a
  trivial sigma. No faithfulness, no transitivity.
- `protocol/card_protocol.v` is a **utility-lemma file**: it never bundles a
  protocol record. `g_commutes_endpoint` is a `Hypothesis` left to callers.
- `protocol/card_exchange_pismc.v` proves **session duality**
  (`native_compute` channel-matching), which is syntactic. `CertifiedSolution`
  is opaque; no end-to-end security proof lives here.

### Instance witnesses (in-scope only)
| Instance | SecurityWitness | ThresholdWitness | Monodromy | Recovery |
|---|---|---|---|---|
| kim2025 | REAL (exact `(8/5)*kim_slev^L`) | VACUOUS (`RS5_witness_trivial` + `trivial_sigma`) | trivial | P^1 / RS-5, vacuously wired |
| denboer1989 | REAL (`eps=0` perfect, C_5 regular) | VACUOUS (`trivial_sigma`) | trivial | none / P^1 boundary |
| s5 | SPLIT: L=1 fiber bound is real; L=285 needs `Axiom s5_rayleigh_Qsq_R` and `Axiom s5_group_order_eq` | AUTHENTIC (genuine S_5 action), but Bring's-curve realisation is an opaque `Axiom s5_brings_covering_realised` | authentic (S_5) | sum-mod on I_5 at genus 4 |
| s5x5 | SPLIT (fiber real, spectral axiom reused) | AUTHENTIC (reducible product action) | authentic but reducible | product sum-mod on disjoint piles; multi-component Bring's option at genus 4 each |

### `reconstruct/` machinery
- `security_threshold_tradeoff` (`cover_tradeoff.v:140-159`): **proved**.
- `hurwitz_bound`: **classical Axiom** (Hurwitz 1893, cited).
- `pgl_bound := maxn(2*N, 60)`: this is the **Klein finite-subgroup bound**.
  Commit `418bc81` tightened the older `N*(N^2-1)` formula. Memory note
  `project_pgl_bound_offbyone` is now stale; the current bound is correct.
- `curve_realisation`: opaque `Parameter realised_by_curve : ... -> Prop`.
  No curve is constructively built in Coq; realisation claims are axioms
  grounded in published geometry (Edge 1978 for Bring's curve).

### Cross-cutting honesty issues
- A) `trivial_sigma` collapses every group element to identity. Three of the
  four instances (kim, denboer, RS5-side of s5) discharge their threshold
  obligation by routing through this. Calling them "AG-code recovery
  witnesses" on a poster overclaims.
- B) The framework imposes **no faithfulness or transitivity contract** at
  the interface level (verified directly in `pgg_interface.v`). Therefore
  the line "the framework characterizes monodromy as a random walk" is
  honest only at the *Schreier-walk* layer used by spectral bounds, not at
  the protocol level.
- C) `card_protocol.v` does not define a CardProtocol record; the "card
  vocabulary" exists, but downstream consumption is via the session-type
  programs in `card_exchange_pismc.v`, which carry no security proof.

## Phase-2 split: atomic items extracted from the user's text

The user's six numbered points contain about fourteen distinct claims. The
table below atomises them. Each row has one main idea.

| # | Atomic claim | Source in user's text |
|---|---|---|
| A1 | Framework characterizes abstract groups (e.g. S_5) | (1) |
| A2 | Framework characterizes concrete presentations of those groups (e.g. via Coxeter generators) | (1) |
| B1 | Computation is specified as a monodromy action | (2) |
| B2 | That action is a random walk among group elements | (2) |
| C1 | Outputs a secret-sharing protocol | (2) |
| C2 | Protocol works via deck transformation among parties | (2) |
| C3 | Protocol uses a masked permutation matrix | (2) |
| D1 | Formalised security results for distinct group instances | (3) |
| E1 | Beyond collusion-security, framework has an *orthogonal* design for plug-able recovery schemes | (4) |
| F1 | Non-AG-code recovery example: sum-mod-N | (4) |
| F2 | Non-AG-code recovery example: product-mod-N for S_5 x S_5 | (4) |
| G1 | AG-code recovery is a family: genus-0 (Massey, Reed-Solomon) ... | (4) |
| G2 | ... up to higher curves (Bring's curve) | (4) |
| H1 | Witnesses are produced for: den Boer (uniform shuffle) | (4) |
| H2 | Witnesses for Kim (biased shuffle) | (4) |
| H3 | Witnesses for S_5 (classic card-game example, inside AG-code scope) | (4) |
| H4 | Witnesses for S_5 x S_5 (classic card-game example, beyond AG-code scope) | (4) |
| I1 | Two witness families: SecurityWitness | (4) |
| I2 | ThresholdWitness | (4) |
| J1 | Framework characterizes a trade-off between security and recoverability for AG-code-based schemes | (5) |
| J2 | The upper side of that trade-off is a PGL gate | (5) |
| J3 | The lower side is the Hurwitz automorphism floor | (5) |
| J4 | The trade-off bundle is called AlgebraicRigidity | (5) |
| K1 | Agent helped discover relevant math knowledge | (6) |
| K2 | Agent helped formalise that knowledge | (6) |
| K3 | Agent verified soundness of realisation path | (6) |
| K4 | Agent flagged wrong / dead-end exploration | (6) |
| K5 | Agent evaluated completeness / progress | (6) |
| L1 | This is bottom-up knowledge exploration from an intuitive seed | (6) |
| M1 | Agent identified the research domain (card-game-based security) | (6) |
| M2 | Agent pivoted the work after Shamir-comparison frustration | (6) |
| N1 | Shamir cannot be beaten because the PGG protocol is NC^1-bounded | (6) |
| N2 | The PGG protocol is less efficient than Shamir | (6) |
| N3 | The PGG protocol reconstructs as a *ramp* threshold, not a sharp (k,T)-threshold | (6) |

## Phase-3 honesty table

Column legend.
- **Status**: REAL = genuinely proved in code, used downstream. PARTIAL = real
  in some instances or only at one layer. VACUOUS = exists as a record/axiom but
  not load-bearing. AXIOM = held as Coq `Axiom`, classically grounded. META = a
  process claim with no formal-proof obligation. SKIP = too vacuous to mention.
- **Slide phrasing**: a one-sentence draft the user can paste, or `DROP` with
  a reason.
- **Codebase action**: minimal next step to upgrade Status, if it's worth doing.

| # | Claim | Status | Slide phrasing | Codebase action |
|---|---|---|---|---|
| A1 | Abstract groups | REAL (with caveat) | "Admits any finite group through `PGGTypes`; the four in-scope instances cover three distinct groups: C_5 (used by both den Boer and Kim), S_5, and S_5×S_5." | Memory note `project_pgg_framework_coupling`: the interface allows a trivial morphism, so "admits" is honest but "characterises" would not be. |
| A2 | Concrete presentations (Coxeter) | PARTIAL | "S_5 uses the adjacent-transpositions generators s_0..s_3 of Coxeter type A_4, but only the RAAG commutations `s_i s_j = s_j s_i` for `|i-j| >= 2` are imposed; the braid relation `s_i s_{i+1} s_i = s_{i+1} s_i s_{i+1}` is NOT encoded in the framework." | Add a `CoxeterPresentation` record (small upgrade) that carries a Coxeter matrix and emits the commutation+braid relations as obligations. Today the framework's RAAG-on-P_4 (`pgg_raag_path.v:11-14`, `pgg_raag_s5.v:13-17`) is *strictly weaker* than a Coxeter presentation: it lets word equality be coarser than group equality. The user's "Coxeter presentation" claim is not yet supported by code. |
| B1 | Monodromy action | PARTIAL | "Group elements act as deck permutations via a fixed morphism `pgg_rho : G → S_N`." | `pgg_interface.v` does not require `pgg_rho` to be faithful or transitive. Either (a) add an optional `faithful_pgg_rho` field as a *gradient* obligation that real instances discharge, or (b) on the slide, drop "random walk among group elements" and replace with "deck permutations." |
| B2 | Random walk | REAL (with axioms cited) | "Three random walks are implemented: a uniform Schreier walk (S_5), a weighted Schreier walk (Kim's biased cut), and a lazy Schreier walk on a reducible block graph (S_5×S_5). Den Boer uses no walk — its security is a single-shot uniformity argument." | None for kim2025 (no axiom in its walk); for s5 / s5x5 the slide must footnote `Axiom s5_rayleigh_Qsq_R` (`s5_mixing.v:188-195`, externally certified by an LDL^T script). The Markov chain is on `'I_N`, not on G; the equality with the endpoint distribution is `schreier_walk_eq_endpoint` (`pgg_schreier.v:476-529`). |
| C1 | Secret-sharing protocol (split / share / compute / reconstruct) | PARTIAL (loop CLOSING for den Boer; OPEN for kim, s5, s5x5) | "The protocol skeleton has a session-typed share/reveal pair (`exchange_dealer` / `exchange_player` / `exchange_verifier`) whose duality is `native_compute`-checked for the idealised representation. The den Boer instance has a closed end-to-end bridge: its SecurityWitness's `sw_bound` plugs into `dealer_encode_correct`. For Kim, S_5, and S_5×S_5 the bridge is future work." | Implementation in Phase-6: add `denboer_bridge.v` that (a) builds a `PGGInterface M_denboer`, (b) invokes `exchange_dealer_from_words` with a uniform word from the denBoer SecurityWitness, and (c) composes `dealer_encode_correct` with `fc_security_uniform`'s `sw_bound`. Den Boer chosen because its one-shot perfect security is the simplest to wire. |
| C2 | Deck transformation among parties | REAL | "Players exchange card positions via session-typed `Deal` / `Announce` / `Finish` primitives." | None. |
| C3 | Masked permutation matrix (party i sees row i) | UNIMPLEMENTED | The "party_i sees row_i of the permutation matrix" design is **not in the codebase**. The actual implementation is column-wise: `dealt_hand PI W i = [seq rho(w)(tnth starts i) | w <- W]` (`pgg_interface.v:454-455`) — each party observes one endpoint per generator, i.e. one COLUMN of generator-applications at their own starting position. There is no per-party row-extraction and no information-theoretic per-party-view lemma. The collusion bound (`pgg_collusion_bound.v`) gives a marginal at a single endpoint, not a row. | If "row i for party i" is the intended security mechanism, the protocol record needs (1) a per-party view function `view : 'I_T -> seq 'I_N` extracting row i of a per-generator permutation matrix, (2) an information-theoretic lemma `view_secrecy` showing party i's view is independent of `s` given fewer than `ts_k` participants, and (3) a wiring from this view function into `exchange_player`. None of these exist. The slide must either drop the "masked permutation matrix" wording (current code is column-wise) OR present it as a *design intent* the codebase has not yet realised. |
| D1 | Security results across instances | REAL (with axiom caveats) | "All four in-scope instances ship security witnesses with explicit bounds: Kim has both exact and asymptotic (`fc_kim_security_witness` populates `sw_exact` AND `sw_asymptotic`, `five_card_kim.v:505-515`); S_5 has fiber bound at L=1 and Schreier asymptotic at L=285 (`s5_security_witness_schreier`, `rigidity_s5_instance.v:202-209`); S_5×S_5 has fiber bound and Schreier asymptotic at L=591 with an honest non-zero floor (`rigidity_s5x5_instance.v:274-288`); den Boer has perfect one-shot security (eps=0)." | The s5 / s5x5 spectral gaps rely on `Axiom s5_rayleigh_Qsq_R` (Rayleigh on Q^2, externally certified by `s5_spectral_certificate.py`). Slide must footnote this and the `s5_group_order_eq` / `s5x5_group_order_eq` axioms (true facts, HB-stack lifting deferred). Den Boer needs no axioms for its security side. |
| E1 | Plug-able recovery, orthogonal to security | REAL | "Security and recovery are decoupled records (`SecurityWitness`, `ThresholdWitness`) bundled by `AlgebraicRigidity`; any AG-code data satisfying `cs_gap` may be plugged in." | None. |
| F1 | sum-mod-N | PARTIAL | "S_5 plugs sum-mod-5 reconstruction through a Bring's-curve `CoveringData` with `cd_genus = 4`." | The slide should say sum-mod is **routed through** AG-code data, not labelled "non-AG-code". A true non-AG-code path would need a new `RecoveryScheme` interface separate from `CoveringScheme`. Cheap upgrade: add a `combinatorial_recovery` constructor in `algebraic_rigidity.v` that wraps sum-mod-N without the curve detour. |
| F2 | product-mod-N for S_5×S_5 (claimed AG-code recovery) | OVERCLAIM in current code | "S_5×S_5 uses a *sum-mod product scheme* (`product_scheme (sum_mod I_5) (sum_mod I_5)`) for reconstruction, giving `(ts_k, ts_T) = (5, 10)`. The framework labels two genus-4 Bring's curves as the *geometric realisation* (`s5x5_multi_data`), but **no AG-code recovery algorithm is actually wired in**; the (5, 10) threshold comes from modular sums, not from a genus-4 code." | **Honest fix**: the slide must not credit Bring's curves with the recovery work. With `n = 5` shares per pile and `g = 4`, the Chen-Cramer range `2g+1 ≤ m ≤ n-1` collapses to `[9, 4]` (empty), so **no valid AG-code (k, T)-ramp with k < T exists on this parameter set**. The codebase has only the gap inequality `ts_T ≤ ts_k + 2g` (`covering_scheme.v:119-129`) and an opaque `Axiom realised_by_multi_curve` (`multi_covering.v:140-146`), not an executable recovery. Two real options: (a) collapse to a single 10-point curve giving a (k=2, T=10) ramp at gap 8; (b) raise the per-pile evaluation count above 10 (Bring's curve has many more rational points over `F_q` for `q ≥ 11`) and instantiate a genuine Goppa-style decoder. Neither is in tree. |
| G1 | Genus-0 / Reed-Solomon | DECORATIVE-BUT-LOAD-BEARING-FOR-TYPECHECK | "Kim and den Boer do not (and need not) carry a real recovery scheme: Kim's security is exact, den Boer's is perfect (eps=0). The `RS5_witness_trivial` placeholder sits in the threshold slot only so `AlgebraicRigidity` typechecks." | Two options: (a) refactor `AlgebraicRigidity` to make `ar_threshold : option (ThresholdWitness M)`, retiring the placeholder. (b) Keep the placeholder and rename it `decorative_threshold_witness` with a comment block explaining why no genuine threshold is needed for one-shot perfect/exact security. Option (b) is cheaper and the user prefers it ("Do nothing about the code but just make sure comments show they are vacuous"). |
| G2 | Higher curves (Bring's) | AXIOM (load-bearing for s5 / s5x5) | "S_5 lives on a Bring's curve of genus 4 (Edge 1978); the curve is admitted by axiom, the Riemann-Hurwitz arithmetic is checked." | Optional long-term: build an executable divisor / coordinate representation of Bring's curve. Short-term: keep the `Axiom` and footnote the citation on the slide. |
| H1 | den Boer witness | REAL (security) + VACUOUS (threshold) | "den Boer (1989) five-card trick: perfect security ε=0 from C_5 regularity; threshold-witness is decorative." | None for the slide; consider dropping the decorative `RS5_witness_trivial` line from the den Boer file to remove ambiguity. |
| H2 | Kim witness | REAL (security) + VACUOUS (threshold) | "Kim et al. (2025): exact variation distance `(8/5)·kim_slev^L` for the biased cyclic cut (one rest-position has probability `1/5 - eps`, the other four positions each `1/5 + eps/4`)." | Same as H1. **Audit correction**: the original draft said "two-coin shuffle"; the file `five_card_kim.v:5-13` describes a single multinomial cut over five cyclic positions. |
| H3 | S_5 witness | SPLIT-REAL | "S_5 (classic shuffle): fiber bound at L=1; Schreier spectral bound at L=285; reconstruction on Bring's curve." | Replace the spectral axiom with computed eigenvalue, OR cite `Axiom s5_rayleigh_Qsq_R` in a footnote so the slide is not silently overclaiming. |
| H4 | S_5×S_5 witness | SPLIT-REAL | "S_5×S_5 (product shuffle, multi-component cover): per-pile fiber security; reconstruction by two Bring's curves." | Replace `Axiom s5_group_order_eq` (cardinality 14400 should be computable) and clarify on slide that the spectral bound includes a non-vanishing inter-pile floor. |
| I1 | SecurityWitness type | REAL | (covered by E1) | None. |
| I2 | ThresholdWitness type | PARTIAL | "Threshold witnesses are real for S_5 / S_5×S_5; for Kim and den Boer they are placeholders (decorative; no recovery is required since their security is one-shot)." | Keep the code; add a comment block at each `_threshold_witness` declaration explaining (a) why the slot is structurally required by `AlgebraicRigidity`, (b) why no real recovery is needed for one-shot security, and (c) that the trivial sigma is a code-automorphism placeholder, not an instance bug. Per user direction, do not modify the code itself. |
| J1 | Trade-off security ↔ recoverability | REAL | "`security_threshold_tradeoff` is proved: either genus 0 with |G| ≤ Klein bound, or genus > 0 with T ≤ k + 2·genus." | None. |
| J2 | PGL gate | REAL (formula corrected) | "PGL gate uses the Klein finite-subgroup bound `max(2N, 60)` (corrected in commit 418bc81 from an earlier off-by-one)." | None. **Update the stale memory note `project_pgl_bound_offbyone`** outside of plan-mode work. |
| J3 | Hurwitz floor | AXIOM | "Hurwitz automorphism floor `|G| ≤ 84(g-1)` is taken as a classical axiom (Hurwitz 1893)." | Long-term: import from a future MathComp / mathcomp-analysis Hurwitz formalisation. Short-term: keep the axiom and cite. |
| J4 | AlgebraicRigidity bundle | REAL (with new field) | "`AlgebraicRigidity M` bundles a `SecurityWitness`, a `ThresholdWitness`, and an `ar_consistency` field enforcing `tw_covering ar_threshold = sw_covering ar_security`." | **User directive**: add `ar_consistency : tw_covering ar_threshold = sw_covering ar_security` to the `AlgebraicRigidity` record at `algebraic_rigidity.v:187-190`. Then re-discharge the four existing bundles (`kim_rigidity`, `fc_rigidity`, `s5_rigidity`, `s5x5_rigidity`) with the new obligation. Because all four instances ALREADY construct both witnesses against a single CoveringScheme, the consistency proof should be `erefl` or one rewrite. |
| K1 | Agent discovered math | META | "Agent surfaced Bring's curve, the Hurwitz bound, and the Klein finite-subgroup classification when the original framing did not name them." | None; this is poster narrative. |
| K2 | Agent helped formalise | META | "Agent drafted lemma statements, picked MathComp idioms, and ran the Rocq audit pipeline." | None. |
| K3 | Soundness verification | META | "Agent caught the original PGL off-by-one and the `RS5_witness_trivial` vacuity." | None; footnote both as concrete examples. |
| K4 | Dead-ends flagged | META | "The Shamir-comparison frame was abandoned after the agent showed the protocol is NC^1-bounded and ramp." | None. |
| K5 | Completeness / progress evaluator | META | "The `rocq-audit` pipeline runs catalog-based style audits at every commit." | None. |
| L1 | Bottom-up exploration | META | "Started from an intuitive cover-then-lift sketch; the formal framework is the *consequence*, not the goal." | None. |
| M1 | Identified domain | META | "Re-classified the work as card-protocol security, not generic SMC." | None. |
| M2 | Pivot after Shamir frustration | META | (Covered by K4.) | None. |
| N1 | NC^1-bounded reason | META (process narrative) | "Permutation-action computation lives in NC^1, while Shamir-style threshold schemes reach P; the framework cannot beat Shamir on expressivity, which is why the design pivoted toward a card-game-shuffle security narrative." | None; this is a process-narrative claim that explains why the original "compete with Shamir" framing was abandoned. Not a Coq-proved theorem; the slide should phrase it as a complexity-class observation, not a result of this formalisation. |
| N2 | Less efficient than Shamir | META-OK | "Each share is a permutation (Θ(log\|G\|) bits), not a field element; communication cost is higher than Shamir." | None; this is an honest qualitative tradeoff. |
| N3 | Ramp, not sharp threshold | PARTIAL | "The protocol parameters satisfy a *structural* ramp inequality `T - k ≤ 2·genus` (`gap_bound`); operationalising this as 'any T or more shares reveal, fewer than k give nothing' would need a partial-erasure decoder which is future work." | **Audit correction**: `covering_scheme.v:161-163` proves the structural inequality only; the comments at lines 159-180 explicitly defer the decoder. Slide must not claim partial-erasure reconstruction. |

## Phase-3 short answer to the user's "evaluate honesty" ask

If the user keeps the six bullets they typed verbatim, they overclaim in
three places:

1. **"AG-code recovery for kim2025 and den Boer"** is decorative
   (`RS5_witness_trivial`).
2. **"NC^1 computation only"** is a structural intuition, not a proven
   theorem in this codebase.
3. **"Masked permutation matrix"** does not match what the protocol files
   build (encode/decode plus session types).

The phrasings in the *Slide phrasing* column above re-tighten each of the
problematic claims to what the code can actually back.

## Phase-4 next step (adversarial audit)

Before exiting plan mode, an adversarial-but-honest audit agent will check:
- Whether any "REAL" row in the table is in fact backed by an `Axiom`,
  `Admitted`, or trivial proof that an earlier reader missed.
- Whether any "VACUOUS" verdict can be defended by a downstream caller
  that the explorer missed.
- Whether the user's verbatim text contains other overclaim risks not
  captured above (e.g., "framework characterizes" might imply more than
  the interface actually does).
- Whether the slide phrasings are still misleading after the rewrite.

Audit findings will be appended below as a "Phase-4 audit response"
section, with `[ACCEPTED]` / `[REJECTED]` per finding, before
ExitPlanMode.

## Critical files for any implementation phase

- `pgg-smc/protocol/pgg_interface.v` — root record; faithfulness gap.
- `pgg-smc/protocol/card_protocol.v` — utility lemmas; commutation hypothesis.
- `pgg-smc/protocol/card_exchange_pismc.v` — session protocol, duality only.
- `pgg-smc/reconstruct/algebraic_rigidity.v` — witness records, tradeoff theorem.
- `pgg-smc/reconstruct/cover_tradeoff.v` — `security_threshold_tradeoff`, `pgl_bound`.
- `pgg-smc/reconstruct/curve_realisation.v` — opaque `realised_by_curve`.
- `pgg-smc/instances/{kim2025,denboer1989,s5,s5x5}/...` — see per-instance verdicts above.
- `pgg-smc/notes/may18aipv2026/poster.pen` — the poster being edited.

## Verification of plan correctness (without making edits)

- For each "REAL" or "PARTIAL" row, the cited file and line range exists
  in the working tree (verified via the three explorer agents).
- The poster slides at `Vnzil`, `bjHmm`, `ioEmi`, `KTtZU` exist
  (verified via `mcp__pencil__batch_get`); their current vertical
  positions (4720, 5900, 26640, 27820) confirm the user's intended move
  of `ioEmi`/`KTtZU` is a move upward of roughly 21k px.
- The two stale-memory items (`pgl_bound_offbyone`, the assertion that
  `s5` "sneaks into genus 0") are explicitly noted as stale in commit
  `418bc81`.

## Phase-4 audit response

An adversarial auditor read the framework spine, the four in-scope
instance files, and the seven `reconstruct/` files line by line. The
auditor produced 33 row-level verdicts. The summary below records which
verdicts I accept and how the table above has been amended.

### Confirmed and amended (REJECT → AMEND)

- **A1**: Amended. The original draft said "four instances ... C_5, S_5,
  S_5×S_5, plus the cyclic-shuffle abstraction Kim et al.", which would
  let a reader count four distinct groups. The corrected phrasing says
  "four in-scope instances cover three distinct groups: C_5 (for both
  kim2025 and denboer1989), S_5, S_5×S_5." Status downgraded to REAL
  (with caveat) because the framework "admits" rather than "characterises"
  any group at the interface level (no faithfulness obligation).

- **H2**: Amended. Original wording "biased two-coin shuffle" mis-named
  the protocol. The corrected wording mirrors `five_card_kim.v:5-13`:
  a single biased multinomial cut over five cyclic positions.

- **J4**: Amended. The plan originally said `AlgebraicRigidity` bundles
  witnesses "consistent on the same `CoveringScheme`". The record at
  `algebraic_rigidity.v:187-190` has two independent fields with no
  shared `CoveringScheme` and no equality obligation. The slide now
  says "parameterised on the same monodromy `M`; the two fields are
  independent — no Coq obligation ties the security distribution to
  the threshold covering." The codebase column proposes a one-field
  `ar_consistency` upgrade if the user wants the stronger semantics.

- **G1**: Amended. Original "VACUOUS, DROP" understated the role of
  `RS5_witness_trivial`. It is mathematically vacuous (trivial sigma,
  trivial covering) but **load-bearing for typechecking** of
  `kim_threshold_witness` and `fc_threshold_witness`. Status changed
  to DECORATIVE-BUT-LOAD-BEARING-FOR-TYPECHECK; the slide phrasing now
  says the kim / den Boer threshold witnesses satisfy the *interface*
  with a placeholder; their genuine content is the security witness.

- **N3**: Amended. The proof at `covering_scheme.v:161-163` gives only
  the structural inequality `ts_T - ts_k ≤ 2 * cd_genus`; the
  partial-erasure decoder that would turn this into a true ramp is
  explicitly future work per comments at `covering_scheme.v:159-180`.
  Status downgraded from REAL to PARTIAL; the slide phrasing now says
  "structural ramp inequality" and not "partial-erasure reconstruction".

### Accepted as written

- C1 (session duality verified by `native_compute` at
  `card_exchange_pismc.v:391-503` — for the idealised representation;
  duality of instance-specific protocols still rides on the same proof).
- A2, B1, B2, C2, D1, E1, F1, F2, G2, H1, H3, H4, I1, I2, J1, J2, J3.

### Additional unflagged findings reported by the auditor

- `card_word_decode_correct` (`card_protocol.v:129`) has no downstream
  consumer. Not currently a plan claim; flagged for future cleanup.
- The `kim_rigidity`, `fc_rigidity`, `s5x5_rigidity` bundles are
  terminal — built but never consumed by a further theorem. The
  `algebraic_rigidity.v` quartet (`ar_tradeoff`, `ar_gap_bound`,
  `ar_complexity`, `ar_protocol_correct`) is the only downstream
  surface. Memory note `feedback_load_bearing_verification` applies:
  the poster should not credit "rigidity bundles" as a result without
  citing one of those four `ar_*` lemmas.
- A `TODO: populate sw_exact` comment at `five_card_security.v:21-24`
  is stale (the field is now populated via `uniform_security_witness`);
  outside-of-plan-mode cleanup.

### Sanity checks (all PASS)

- `pgl_bound = maxn (2 * N) 60` at `cover_tradeoff.v:120`.
- No code consumer of the old `N*(N^2-1)` formula; one stale comment
  at `denboer1989/five_card_security.v:265`.
- Kim is one multinomial cut, not "two coins".
- No `Admitted` in `reconstruct/`.

### Net effect on the poster plan

Three rows changed grade (A1, J4, N3), two rows changed slide wording
(H2, G1). No row was found to silently rely on an `Admitted` or a
missed axiom; the Hurwitz and curve-realisation axioms were already
flagged. The plan now passes the auditor's 33-row check.

## Phase-5 user-feedback re-audit (round 2)

After the user rejected the first ExitPlanMode and supplied detailed
in-line feedback, three more parallel Explore agents re-read the
codebase to ground the answers. The findings below correct, refine,
or add to the table above. Affected rows have already been amended
in place.

### Cross-cutting issue (re-audited)

**The framework spine is genuinely disconnected from the in-scope
instances.** None of `kim2025`, `denboer1989`, `s5`, `s5x5`
imports `card_protocol` or `card_exchange_pismc`. The only
in-tree consumer of `exchange_dealer_from_words` is the
out-of-scope `star` instance (`rigidity_star_instance.v:251`).
The bridge lemma `dealer_encode_correct`
(`pgg_dealer_bridge.v:83-98`) exists but is unused. So the
"one protocol flow, many group instances" design is
*architecturally* present but *operationally* absent: no
instance produces an end-to-end "this concrete dealing is
secure after L rounds" theorem that consumes both its
SecurityWitness and the protocol's session structure.

This is the single most important honesty correction. The
slide phrasing for C1 has been changed accordingly. The
slide must NOT claim "the protocol is secure when you plug
in any of the four instances"; the claim that holds today
is "the protocol *structure* and the *security witnesses*
are both formalised, but the wiring between them is
generic-bridge-only and never invoked per-instance."

To close this, the minimum work is, per instance:
1. Build a `PGGInterface M_instance` (currently absent).
2. Call `exchange_dealer_from_words` with a word drawn from
   the instance's `sw_distribution`.
3. Compose `dealer_encode_correct` with the instance's
   `sw_bound` to produce a final security theorem.

The user can decide whether to list this as future work on
the poster or to invest now.

### Per-user-question answers

#### Cross-cutting A — How to make "AG-code recovery" honest

The threshold side uses `trivial_sigma` only for kim/denboer.
Their security is one-shot (perfect for den Boer, exact for
Kim), so they do not need a real recovery scheme: the placeholder
fulfils the `AlgebraicRigidity` record's structural obligation
and nothing else. For S_5 / S_5×S_5 the recovery is real (sum-mod
through a Bring's-curve covering; multi-component for S_5×S_5).
**`trivial_sigma` does not break plug-ability** because plug-ability
is at the `CoveringScheme` level, not at the `code automorphism`
level: any `CoveringScheme` with a genuine `cs_gap` proof can
replace the trivial one. Slide row G1 has been updated.

#### Cross-cutting B — Does "protocol level" need a word-alphabet step?

Yes, but it is *already* present in the dealer: the dealer draws a
word `w \in 'I_Tg^L` (or one with weights, per Kim) and applies
it via `word_eval`. The alphabet is `'I_Tg` (the generator index).
The "choosing of alphabet" step is `exchange_dealer_from_words w`
(`card_exchange_pismc.v:273-275`). What is NOT present per instance
is the *distribution* on words wired into the session program;
the SecurityWitness records the distribution but no instance plumbs
it through to the protocol invocation. See cross-cutting note above.

#### Cross-cutting C — Carrying security proof to the protocol

The claim "plug an instance with a SecurityWitness into the protocol
and the protocol is secure" is the *intended* design. Today, code-wise:
- Instance-side: `kim_security_witness` and analogues are real records
  whose `sw_bound` is a closed Coq lemma.
- Protocol-side: `exchange_dealer_from_words` is parameterised on a
  `MonodromyReprType`, so it can in principle accept any instance.
- Bridge: `dealer_encode_correct` proves correctness of the encoded
  dealing relative to the threshold scheme.
- Missing: NO theorem of the form `forall (R : MonodromyReprWithGeneratorType)
  (sw : SecurityWitness R M), session_runs (exchange_dealer_from_words ...) -> var_dist <= sw_bound sw`.
  Such a theorem would be the load-bearing plug-ability lemma.

The slide must say "security analysis exists at the group-instance layer;
the protocol's structural duality is also proved; the combined statement
is future work". This is what row C1 now says.

### Per-row clarifications added by round 2

- **A2** Concrete presentation: S_5 is RAAG-on-P_4 (Coxeter type A_4
  generators), without the braid relations. The framework lacks a
  Coxeter typeclass. A small upgrade (a `CoxeterPresentation` record)
  would let other instances supply full Coxeter relations.
- **B2** Random walk taxonomy: four walk types in code (Schreier,
  weighted Schreier, lazy, uniform-endpoint). Den Boer uses no walk
  (one-shot uniform); Kim uses weighted Schreier; S_5 uses uniform
  Schreier on P_5; S_5×S_5 uses lazy walk on two disjoint P_5 blocks.
- **D1** All four instances DO have asymptotic / spectral bounds (not
  just S_5 and S_5×S_5). My round-1 grading was too pessimistic. Row
  upgraded from PARTIAL to REAL (with axioms cited).
- **F2** The earlier "two Bring's curves is weaker security" claim was
  imprecise. Security lives at the random-walk layer (`s5x5_security_witness_schreier`
  quantifies over the monodromy `M`, not over the covering). The
  reducibility floor comes from the Schreier graph being two disjoint
  blocks, not from the curve choice. The previous AG-codes-on-surfaces
  Künneth argument is mathematically correct but tangential to the
  current security proof (which never uses AG-code function spaces).
- **G1** Kim and den Boer do not need a real recovery scheme. Per
  user direction, the code stays; only comments are added explaining
  why the threshold-witness slot is decorative for these instances.
- **I2** Threshold witness type: per user direction, no code edit; add
  documentation comments at the placeholder declarations.
- **J4** Add `ar_consistency` field as the user requested. Each of the
  four `*_rigidity` bundles will need an `erefl`-style proof.
- **N1** Reclassified as META: NC^1 vs P is a complexity-class
  observation, not a Coq theorem.

### One earlier conflation corrected

My round-1 phrasing said Kim's monodromy was `trivial_sigma`. This
is wrong as stated. There are **two** sigmas in Kim:
- The **security-side generators** `fc_kim_sigmas` are the five cyclic
  rotations of the deck (`five_card_kim.v:110-115`). They are not
  trivial; they drive the weighted Schreier walk.
- The **threshold-side code automorphism** is `trivial_sigma`
  (`RS5_witness_trivial` in `rigidity_kim_instance.v:73-74`). It is
  trivial in the literal sense.

The same two-layer story holds for den Boer. Slide rows H1, H2 have
been written to reflect this distinction; the auditor's H2 amendment
remains correct (the *shuffle* is one biased multinomial cut, not
"two coins").

### Items the user marked "do nothing about code"

- **I2**: documentation comments only.
- **G2**: curve formalisation out of scope.
- **K1..M2**: META rows, no formal-proof obligation.

### Items the user marked "code change requested"

- **J4**: add `ar_consistency` field.

### User-decided open question (resolved)

The user chose: **add a minimum bridge for one instance** (den Boer)
and **add `ar_consistency` now** in the implementation phase. Both
move from "design intent" to "in-tree code". See Phase-6.

### Memory-update todo (after ExitPlanMode)

- Update memory `project_rs5_witness_trivial_vacuity` to clarify that
  the trivial sigma is on the THRESHOLD side only; kim/denboer
  security-side generators are non-trivial cyclic rotations.
- Update memory `project_pgl_bound_offbyone` to mark it stale (commit
  `418bc81` corrected the formula).
- Add a new memory: `project_protocol_instance_loop_open` documenting
  that no in-scope instance currently invokes the protocol files; the
  bridge `dealer_encode_correct` exists generically but is unused.
  After Phase-6 lands, amend to note den Boer is the first closed
  bridge.

## Phase-6 implementation tasks (user-approved)

These tasks were committed during plan review and will run after
ExitPlanMode. They are scoped to two changes only; no broader
refactor is in scope.

### Task 6.1 — Add `ar_consistency` field to `AlgebraicRigidity`

**Edit**: `pgg-smc/reconstruct/algebraic_rigidity.v` near lines 187-190.
Add a field `ar_consistency : tw_covering ar_threshold = sw_covering ar_security`
to the `AlgebraicRigidity` record.

**Re-discharge bundles**: each of the four `*_rigidity` constructors
must be updated to supply the new field:
- `kim_rigidity` (`pgg-smc/instances/kim2025/rigidity_kim_instance.v:108-111`)
- `fc_rigidity` (`pgg-smc/instances/denboer1989/five_card_security.v:324-327`)
- `s5_rigidity` (`pgg-smc/instances/s5/rigidity_s5_instance.v`, search for
  `MkAlgebraicRigidity` invocation)
- `s5x5_rigidity` (`pgg-smc/instances/s5x5/rigidity_s5x5_instance.v`, same)

**Discharge tactic**: all four instances already construct both
witnesses against the same `CoveringScheme` (or its threshold
side / security side projection), so the consistency proof should
close with `erefl` or `by []` or at most one rewrite.

**Verification**: compile each instance file with `make -j1`.
Per project `CLAUDE.md`, never use `-j` higher than 1.

### Task 6.1.5 — Document column-wise security reasoning (C3 follow-up)

**Direct verdict: column-wise splitting IS secure.** It is not broken.
The argument has four steps that the codebase already discharges.

1. **Encoding**. Secret `s in I_N` is sum-mod encoded so party `i` starts
   at `(s + i) mod N`. Each party knows its own identity `i`, not `s`.

2. **Dealer step**. The dealer draws a random word `w` of length `L`
   from `sw_rho_dist`, applies the monodromy `rho(w)`, and party `i`'s
   final view is the single sheet `rho(w)(s + i)`.

3. **What a `(T-1)`-coalition sees**. They observe `T-1` output sheets
   `rho(w)(s + i_j)` plus their own identities. They do NOT see `s` and
   do NOT know `rho(w)` directly.

4. **Why `s` stays hidden**. The Schreier-walk spectral bound
   (`pgg_uniform_security.v`, `pgg_schreier.v:294-298`) says
   `rho(w)`'s distribution is within `sw_bound_eps` of uniform on the
   orbit. Under a uniformly-random permutation `pi`, the joint
   distribution of `(pi(s + i_1), ..., pi(s + i_{T-1}))` is the image
   of `T-1` distinct inputs and is **invariant under translation of
   the input set**, so it does not depend on `s`. Hence the coalition
   view is independent of `s` up to `var_dist <= sw_bound_eps`. The
   coalition gains no information about `s` beyond that error.

**Equivalence with the row-wise mental model**. Party `i`'s view
`rho(w)(s + i)` is simultaneously: (a) the `(s+i)`-th column of the
permutation matrix `rho(w)`, (b) the row indexed by `s + i` of the
inverse-permutation matrix `rho(w^{-1})`, and (c) the trajectory of
the start position under the shared word. All three views are the
same datum re-indexed. The "row-i for party-i" formulation the user
had in mind is content-equivalent to the implemented column-wise
formulation; the security guarantee does not depend on which
presentation is drawn.

**What column-wise sharing does NOT give**:
- Exact information-theoretic independence at finite `L`. You get
  `sw_bound_eps`-close to independence; for Schreier walks
  `sw_bound_eps -> 0` only as `L -> infty`.
- Per-party share unlinkability. Each party still knows its own
  identity; the parties are not anonymous to one another.

**No code change**. Add a comment block above `dealt_hand`
(`pgg-smc/protocol/pgg_interface.v:454-455`) recording the four-step
reasoning above and citing the load-bearing lemmas
(`pgg_uniform_security.v`'s uniform-endpoint lemma,
`pgg_collusion_bound.v`'s coalition marginal,
`pgg_schreier.v:294-298`'s spectral convergence).

### Task 6.2 — Add minimal protocol bridges (user-approved: all four instances)

The user upgraded the scope from one bridge (den Boer only) to
**all four in-scope instances**. The bridge pattern is uniform across
all four; the differences are the SecurityWitness type and the
`G_stable` discharge. The minimum work per instance is below.

**Shared bridge pattern (from `pgg_dealer_bridge.v:31-100`):** the
bridge takes
- `M : MonodromyReprWithGeneratorType` (the instance's monodromy),
- `PI : PGGInterface M` (per-party starting positions),
- `ar : AlgebraicRigidity R M` (the instance's witness bundle),
- `HT : ts_T' covering = pi_T' PI` (parameter match),
- `G_stable` hypothesis (covering monodromy commutes with `pgg_rho` on
  starts)
and provides `dealer_words_correct` (correctness) and
`dealer_words_epsilon_bound` (security at each secret position).

The per-instance work is to provide the four inputs and a final theorem
of the form
```
Theorem <instance>_protocol_secure :
  forall s : I_N, var_dist (run-distribution s) (uniform on orbit) ≤ sw_bound_eps.
```

#### Per-instance bridge files

| Instance | New file | PI difficulty | G_stable difficulty | sw_bound at runtime |
|---|---|---|---|---|
| den Boer | `instances/denboer1989/denboer_bridge.v` | trivial: T=5 starts on `I_5` | trivial: C_5 acts regularly, monodromy is the same C_5 action | 0 (perfect security, one-shot) |
| Kim | `instances/kim2025/kim_bridge.v` | trivial: T=5 starts on `I_5` | trivial: same C_5 action as den Boer's, but with weighted walk distribution | `(8/5) * kim_slev^L` at L from solver |
| S_5 | `instances/s5/s5_bridge.v` | T=5 starts; needs cast through Bring's-curve `cs_monodromy` | needs `s5_brings_covering`'s monodromy compatibility lemma (likely 1-2 rewrites) | `sqrt(5) * (1 - s5_gap_R)^L` at L=285 |
| S_5×S_5 | `instances/s5x5/s5x5_bridge.v` | T=10 starts on `I_10`; per-pile structure must be threaded through the cast | needs the pile-preserving monodromy lemma already proved in `pgg_s5x5.v` | `1 + sqrt(10) * lazy_alpha^L` at L=591 (note: non-zero floor) |

#### Risks per instance

1. **Den Boer** (easiest): the `ts_encode` precondition of
   `dealer_encode_correct` requires the protocol's `pi_starts` to be
   `ts_encode s` for the secret `s`. Den Boer's threshold scheme is the
   trivial decorative one, so `ts_encode` is essentially identity, and
   the precondition is just `pi_starts = (s, s+1, s+2, s+3, s+4)` or a
   permutation thereof. Discharge with one `rewrite` and `ts_encode_valid`.
   The closing theorem should give `var_dist = 0` for any secret.

2. **Kim**: structurally identical to den Boer (same group C_5, same
   covering), but the SecurityWitness's `sw_rho_dist` is the weighted
   distribution `kim_weights`, not the uniform one. The bridge theorem
   closes via `sw_bound` from `fc_kim_security_witness` once
   `dealer_words_epsilon_bound` is invoked at `L = 1` (or whatever the
   solver chose). No extra spectral work needed in the bridge.

3. **S_5**: the cast `HT : ts_T' covering = pi_T' PI` requires
   matching the threshold-side ts_T to the protocol's T. For s5,
   `ts_T = 5` (from `s5_brings_covering`) and `pi_T' PI = 4` if T=5
   parties (off-by-one in `PGGInterface`). Verify with one `rewrite`.
   `G_stable` should follow from `s5_brings_covering`'s
   coordinate-permutation lemma (must be located; likely
   `s5_brings_monodromy_compat` or similar).

4. **S_5×S_5**: the harder case because the monodromy is reducible
   (two piles), so `G_stable` has two cases (pile-1 generator fixes
   pile-2 sheets, vice versa). The lemma `pgg_s5x5_orbit_preserve`
   (search for it) likely exists; if not, it's a 5-line case split.
   The final security theorem will have a non-zero `var_dist` floor;
   the slide must say this honestly.

#### Estimated effort

- 6.1 (`ar_consistency` field + 4 erefl discharges): 30-60 minutes.
- 6.1.5 (column-wise comment block): 15 minutes.
- 6.2 den Boer bridge: 1-2 hours including compile.
- 6.2 Kim bridge: ~1 hour (clone den Boer, swap distribution).
- 6.2 S_5 bridge: 2-3 hours (covering cast, G_stable discharge).
- 6.2 S_5×S_5 bridge: 3-4 hours (pile-preserving G_stable, floor handling).

Total: roughly one focused day, more if `G_stable` requires new lemmas.

#### Fallback ordering for partial completion

If only some of the four bridges close, the order of value is:
1. Den Boer (proves the bridge pattern works at all).
2. Kim (proves the same pattern lifts to a weighted distribution).
3. S_5 (proves the pattern lifts to a genuine Schreier walk).
4. S_5×S_5 (proves the pattern lifts to a reducible walk with floor).

The slide can say "bridges land for 1..k of 4 instances; the remaining
3-k are future work."

#### Original skeleton (den Boer; same shape applies to others)

**New file**: `pgg-smc/instances/denboer1989/denboer_bridge.v` (~80 lines).

**Skeleton**:
```rocq
From mathcomp Require Import all_ssreflect.
Require Import infotheo.proba.
Require Import pgg_smc.protocol.pgg_interface.
Require Import pgg_smc.protocol.card_exchange_pismc.
Require Import pgg_smc.reconstruct.pgg_dealer_bridge.
Require Import pgg_smc.instances.denboer1989.five_card_group.
Require Import pgg_smc.instances.denboer1989.five_card_security.

Section DenBoerBridge.
  (* Build a PGGInterface from M_denboer. *)
  Definition denboer_PI : PGGInterface M_denboer := ...
  
  (* Invoke the dealer with a uniform single-step word. *)
  Definition denboer_run : ... := exchange_dealer_from_words denboer_PI 1 ...
  
  (* Compose dealer_encode_correct with sw_bound = 0. *)
  Theorem denboer_protocol_secure :
    var_dist (run_distribution denboer_run) (uniform ...) = 0%R.
  Proof. ... Qed.
End DenBoerBridge.
```

**Why den Boer is the easy entrypoint**: `fc_security_uniform`'s
`sw_exact = endpoint_exact = 0` means the bridge theorem closes
without a spectral inequality; the den Boer case is one-shot
perfect security. Kim, S_5, S_5×S_5 require composing an
asymptotic bound, which is harder.

**Verification**:
- `make -j1 pgg-smc/instances/denboer1989/denboer_bridge.vo`
- Ensure the `var_dist = 0` claim closes via `endpoint_exact`.
- Update `_CoqProject` to include the new file.

**Risk**: the existing `dealer_encode_correct` expects a `ts_encode`
precondition (`pi_starts PI = ts_encode(...)`). The den Boer instance
must instantiate this; if it cannot (because den Boer's threshold
scheme is the trivial decorative one), the bridge degenerates to
"security holds for the trivial threshold case" which is still a
genuine first plug-in but should be flagged honestly in the
theorem statement comment.

**Fallback if 6.2 cannot be closed**: revert C1 row to PARTIAL
(loop still OPEN) and update the slide phrasing to "instance-side
witnesses and protocol-side duality exist; combined plug-ability
is future work."

### Phase-6 ordering and dependencies

1. Run 6.1 first (record field addition). It touches one record
   declaration and four constructor sites. Smallest blast radius;
   compiles each touched file with `make -j1`.
2. Run 6.1.5 (comment-only). Zero compile risk.
3. Run 6.2 four times (one per instance), in the order den Boer →
   Kim → S_5 → S_5×S_5. Stop at the first failure and document.
4. Each new bridge file must be added to `_CoqProject`.
5. Verify each step with `make -j1` per project safety rules
   (`CLAUDE.md`: never `-j` higher than 1).

### Task 6.3 — F2 honesty correction in code comments

Per Phase-5 F2 finding: the multi-component AG-code recovery is
**not realisable** at the current parameter set (`n = 5, g = 4`).
The s5x5 (k=5, T=10) ramp it claims actually comes from the
`product_scheme (sum_mod I_5) (sum_mod I_5)` and not from any
AG code on Bring's curves; the `Axiom s5x5_multi_realised` is a
geometric-realisation claim, not a recovery claim.

**Edit**: add a comment block at
`pgg-smc/instances/s5x5/rigidity_s5x5_instance.v:530-546`
clarifying that:
- `s5x5_multi_data` is *geometric* data (Riemann-Hurwitz on two
  Bring's curves), not threshold-scheme data.
- The actual recovery is via `product_scheme sum_mod sum_mod`, a
  modular-sum scheme, which works because the threshold check is
  `ts_T ≤ ts_k + 2g` (10 ≤ 5 + 8 = 13) and `sum_mod` happens to
  satisfy `ts_T = ts_k = n` per pile.
- An honest Goppa-style decoder on Bring's curve **cannot** exist
  at n=5, g=4 (Chen-Cramer range `[2g+1, n-1]` is empty);
  realising a real AG-code ramp on these curves would require more
  rational points per pile.
- The slide that talks about Bring's curve recovery should say
  "the *geometry* is Bring's curve at genus 4; the *recovery
  algorithm* used is modular sum, which is operationally a degenerate
  AG code at genus 0."

No proof obligation. Comment-only edit.

### Phase-7 (deferred) — Pencil slide edits

Out of scope for THIS plan. After Phase-6 lands, a separate
implementation pass will:

1. Insert a new horizontal row between `Vnzil` (y=4720) and
   `bjHmm` (y=5900) in `poster.pen`.
2. Add a subtitle slide "Prototyping Result" at the start of
   the row.
3. Move `ioEmi` and `KTtZU` from y=26640 / y=27820 into the new row.
4. Add new content slides for the 33 atomic items, using the
   Phase-3 honesty-table phrasings as the canonical text.

That layout pass requires Pencil tooling not yet exercised here
(`mcp__pencil__batch_design`, `mcp__pencil__find_empty_space_on_canvas`),
and the user has not yet specified row direction (extend rightward
from x=1800 or leftward into the negative-x region used by
`d8d2Vw` at x=-225). A second plan-mode pass after Phase-6 is the
right place for that decision.
