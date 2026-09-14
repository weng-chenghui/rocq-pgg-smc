# PSL(2,11) Plan B: the executed cone on the all-decks dealer (design, 2026-09-15)

Decision (user, 2026-09-15): option 1 of the Plan B fork. The psl211 Tableau row
is certified through `ExactIndependence` under the ALL-DECKS dealer, supplied
inputs mode, ledger row L24. Not chosen: a colour-observer arm in the Tableau
(framework code owned by the Tableau session) and an Observed-only row.

Evidence this note rests on: `notes/probes/2026-09-15-psl211-planb/PROBE-REPORT.md`
(P0-P4, 2026-09-15) and `notes/probes/2026-09-14-psl211/AUDIT-SOUNDNESS.md`
finding 5. Plan A record: `docs/superpowers/plans/2026-09-14-psl211-chirality-instance.md`.

## 1. The problem

The Tableau's two security arms are stated on the raw code reading
`static_coalition_obs C x g` of the coalition (manifest/pgg_tableau.v:114-147).
Under the dealt mode (`dealt_secret_params`, the fixed encoder deck
`psl211_orbit_encode b` cut by a uniform g) the raw reading of C = {0,1,2} has a
support difference between the two chiralities (probe P2, reading (0,1,6) occurs
under hexad and never under mirror), so `ew_indep` and `sc_const` are refuted at
#|C| = 3 below the threshold 6. The colour headline of Plan A
(`psl211_colour_view_indep`) has no Tableau arm.

Under the all-decks dealer the deck is uniform over every valid deck of the class:
a block of the class's Steiner system carries the six heart codes in a uniform
labelling and the complement carries the six club codes in a uniform labelling.
The raw code reading is then independent of the class for every coalition of at
most five positions (L24), because the number of class-`b` decks producing a
given reading is the block count `N_A(b)` of the pattern times two factorials,
and the block counts agree between the classes (`psl211_pattern_transfer`).

## 2. Flow (adopted sketch)

```
start    psl211_algebra                                          by algebra { ... }                        // Algebraic (P0 GO)
supplied inputs (bool * psl211_deal) layout psl211_alldecks_layout expecting fst fuel 220                 // Executable (P3 GO)
execute  terminates by vm_compute (0.4 s)                                                                  // Observed:
         endpoints by psl211_alldecks_endpoints := supplied_endpointsE psl211_profile_endpoints (900 s, 17 GB, once)
         recon     by psl211_alldecks_recon := supplied_static_recon psl211_algebra psl211_alldecks_valid   //   Hv new, bookkeeping
sample   psl211_exact_family  (index unit; law `U input `x `U G)                                          // Sampled
certify  ExactIndependence psl211_exact_witness  by L24 = bridge + fiber counts                            // AnalysisBridged, new mathematics
|> publish BaselineClassicalOnly                                                                          // manifest row psl211_row_alldecks
```

Roles. Objects: the five stack levels. Step justifications: the three run facts,
the witness. Terminal: `publish`. Observation change at cost 0: the identification
of `static_coalition_obs` with the position reading of the laid deck
(`static_coalition_obsE`, pgg_instance.v:496). External components and their
interfaces: `psl211_profile` enters as the `algebra` block's image (by `[]`);
`psl211_pattern_transfer` (psl211_orbit.v:1118) enters as the step justification
of the block-count equality; `perm_of_eq_card` (lib/perm_exchange.v) enters in the
extension count; `inde_RV`/`fdist_prod` (infotheo) enter through the new bridge
lemma. Outside the flow: the fixed-dealer colour result of Plan A (stays in
psl211_secrecy.v, no Tableau arm), the word walk (no spectral row: `sc_const` is
per-input and is not claimed here), trace secrecy (not built, see section 6).

Monad: the Tableau's own `;;;` bind, a parameterised structure indexed by
completion level with the accumulated proposition `StackProp`; laws as landed in
manifest/pgg_tableau.v. Nothing new.

## 3. Definitions fixed here

- `psl211_deal := 'I_132 * {perm 'I_6} * {perm 'I_6}`; input carrier
  `bool * psl211_deal` (the class bit FIRST and separate, so the secret is `fst`
  and the bridge lemma is stated on `X * G` with `s := fst`). The probe's
  left-nested quadruple is replaced by this pair; everything else in
  probe_p3_alldecks.v transfers with `x.1.1.1` becoming `x.1`.
- `psl211_alldecks_seq (b, (j, ph, pc))`: position p in row j of the class-b
  table carries heart code `ph (rank of p in the row)`, every other position
  carries `6 + pc (rank of p in the complement)`; ranks by `index` in the
  ascending row (probe_p3_alldecks.v:54-62). `psl211_alldecks_layout` casts it to
  `12.-tuple 'I_12` through `Imod12`.
- `psl211_alldecks_valid : forall x, ts_valid (pga_scheme psl211_algebra) x.1
  (psl211_alldecks_layout x)`, i.e. `psl211_orbit_valid x.1 (layout x)`: distinct
  codes, heart set a block of one system, class bit recovered.
- Sample space `(bool * psl211_deal) * pgg_gT psl211_M`, law
  `psl211_alldecksP := (`U psl211_alldecks_gt0) `x (`U psl211_G_pos)`; secret
  `psl211_alldecks_secret u := u.1.1`; family index `unit` as pgl27_exact_family.
- Fuel 220 (P1b2: sufficient, cost flat).
- Files: `psl211_alldecks.v` (layout, validity, fiber counting, L24 at the
  probability layer; imports psl211_blocks/orbit/scheme and design_privacy),
  `psl211_exec.v` (players cache, algebra block, both parameter records,
  termination, recon), `psl211_endpoints.v` (ONLY `psl211_profile_endpoints`, its
  own file, header records 900 s / 17 GB / no concurrent rocqworker),
  `psl211_models.v` (observed execution, sample adapter, static-obs
  identification, executed content reader, exact family, witness ingredients),
  `psl211_rows.v` (Tableau program, published row, rowE), `psl211_analysis.v`
  (facade `PSL211Analysis`, seven sections), manifest and client edits.
  `reconstruct/design_privacy.v` gains the generic bridge (section 4, C3).

## 4. Claim ledger

| # | claim | kind | passes when | status |
|---|---|---|---|---|
| A1 | `algebra { ... }` block at the psl211 names; `instance_profile psl211_algebra = psl211_profile` and `profile_k = 6` by `[]` | probed | P0 | GO (P0) |
| A2 | termination of the dealt and the all-decks run by `vm_compute` | probed | P1a, P3 | GO |
| A3 | `profile_endpoints_stmt psl211_algebra 220` by `vm_compute`, 562 s + 331 s Qed, 17 GB, no axioms | probed | P1b2, P1d | GO, measured |
| A4 | `supplied_endpointsE` carries A3 to the all-decks mode; `supplied_static_recon psl211_algebra Hv` gives recon | probed | P3 Checks | GO (shape) |
| B1 | validity, distinct codes: `uniq (psl211_alldecks_layout x)` for all x, proved symbolically in j from the table certificates (rows uniq, size 6, entries < 12: psl211_blocks.v) | new proof shape | miniature Qed over the real tables, no vm_compute over inputs | to probe |
| B2 | validity, heart set: `psl211_heart_set (layout x) = list_to_set (row j)` and it lies in the system of x.1 | new proof shape | Qed | to probe |
| B3 | validity, class: `psl211_orbit_class (layout x) = x.1`, from `psl211_subset_class` on rows and `psl211_blocks_disjoint` | precedent shape (psl211_orbit_encode_valid) | Qed | to probe |
| C1 | sample adapter `MkSampleAdapter` with `sa_sampleT := (bool * psl211_deal) * pgg_gT psl211_M`, `sa_arg := fst`, `sa_cut := snd` elaborates at `instance_exec psl211_alldecks_params` | precedent (pgl27_fixed_sample) | elaborates | to probe |
| C2 | `static_coalition_obs C x g = [ffun i => if i \in C then tnth (layout x) (pgg_rho g i) else <default>]` in supplied mode, via `static_coalition_obsE` | precedent (pgl27_static_obsE, P2 dealt version) | Qed | to probe |
| C3 | generic bridge (design_privacy.v): for finTypes X, G, A : {set G} nonempty, s : X -> bool with `#\|[set x \| s x]\| = #\|[set x \| ~~ s x]\|`, and f : X -> G -> T with, for every v, equal counts of `[set u : X * G \| s u.1 == b & u.2 \in A & f u.1 u.2 == v]` over b, the law `(`U HX) `x (`U HA)` makes `fun u => f u.1 u.2` independent of `fun u => s u.1` | new proof shape | miniature Qed at a toy X, G; mutation: drop the equal-class-sizes premise, must fail | to probe |
| C4 | extension count at 'I_6: for K : {set 'I_6} and t : 'I_6 -> 'I_6 injective on K, `#\|[set ph : {perm 'I_6} \| [forall k in K, ph k == t k]]\| = (6 - #\|K\|)`!`; existence of one extension (through `perm_of_eq_card` or a mathcomp lemma the probe names) and the coset bijection with `perm_on (~: K)` (`card_perm`) | new proof shape | Qed at 'I_6, with the mutation t non-injective giving 0 | to probe |
| C5 | fiber decomposition: for fixed g, C with 0 < #\|C\| <= 5, and a reading v, `#\|[set y : psl211_deal \| reading (b, y) g == v]\| = #\|[set B in blocks b \| B :&: P == A]\| * e_h * e_c` with P := pgg_rho g @: C (or its inverse image, fixed by C2), A the heart positions of v inside P, `e_h`, `e_c` the two extension counts, or 0 when v is not colour-consistent; the block count equal across b by `psl211_pattern_transfer` (empty C separately) | new proof shape | decomposition probe: headline L24 derived to Qed from the supporting statements Admitted; C4 miniature; the per-g count stated and Qed on ONE fixed g and ONE small coalition by vm_compute as a sanity check | to probe |
| C6 | L24 at the probability layer: `psl211_alldecksP \|= (fun u => static_coalition_obs C u.1 u.2) _\|_ psl211_alldecks_secret` for #\|C\| <= 5, from C3 with C5 summed over g in G | composition | decomposition probe Qed | to probe |
| C7 | `ExactWitness` for `amf_sample psl211_exact_family R tt` built as pgl27_exact_witness (eq_ind_r over the viewE identification) | precedent (pgl27_rows.v:187-196) | typechecks with C6 Admitted | to probe |
| D1 | executed content reader and `content_traceE` in supplied mode (pgl27_models.v:168-215 shape), reading the endpoint fact from the probe's `.vo` | precedent | typechecks | to probe |
| E1 | Tableau row: `supplied inputs ... expecting ... fuel 220`, `execute terminates by vm_compute endpoints by psl211_alldecks_endpoints recon by psl211_alldecks_recon`, `sample`, `certify ExactIndependence`, `\|> publish BaselineClassicalOnly`; named obligations only (no inline applications in notation slots) | precedent (pgl27_rows.v:124-129, 270-275; five_card_rows.v:117-135 for a non-dealt mode) | typechecks with the witness Admitted | to probe |
| E2 | facade `PSL211Analysis` with one alias per section (1 profile, 2 exec plug, 3 content reader, 4 exact family, 5 observed_recovers, 6 exec_exact_view_indep, 7 StaticExecutedOnly status), manifest `Require Export`, row `psl211_row_alldecks`, checker pins, client Checks | precedent (pgl27_analysis.v, manifest 655-670, client) | plan task | precedent |
| F1 | every published object BaselineClassicalOnly: Print Assumptions of the row, the witness and L24 report exactly the boolp trio; the run facts and validity closed | invariant | rocq repl over the .vo chain | plan task |
| G1 | `ExactLeakAt 6` under the all-decks dealer | optional | not claimed in this plan; tightness stays with `psl211_colour_view_dep_k6` at the fixed dealer | not claimed |

## 5. Soundness invariants

- No new axiom, hypothesis or assumed constant anywhere; the classical trio of
  boolp is the baseline and is the whole assumption set of every published
  object (F1).
- The row's claim is about the all-decks dealer: deck uniform over the
  `132 * 720 * 720` valid decks of a class, class uniform (index `unit`, so the
  secret prior is uniform, and ExactProp's entropy forms are at that prior),
  cut uniform on the 660-element group. It is an average over decks and cuts,
  per coalition, single observation. It neither implies nor is implied by
  Plan A's fixed-dealer colour result; both stand, and the row file says which
  dealer it is about in its header.
- Quantifier order: for every coalition C with #|C| < 6, the reading random
  variable is independent of the class random variable under the fixed law
  `psl211_alldecksP`. Not per input, not per cut.
- Vacuity: both classes have `132 * 6! * 6!` inputs (`psl211_alldecks_cardE`,
  P3), the group has 660 elements (`psl211_G_pos`), every coalition of size 1..5
  is covered by `psl211_count_ok` through `psl211_pattern_transfer`, the empty
  coalition is trivial. The threshold is the profile's own `profile_k = 6`.
- Cited library objects, one line each: `static_coalition_obs`,
  `static_coalition_obsE`, `supplied_input_params`, `supplied_static_recon`,
  `supplied_endpointsE`, `instance_observed` (protocol/pgg_instance.v);
  `MkSampleAdapter`, `sa_coalition_view` (security/pgg_sample_adapter.v);
  `MkAnalysisModelFamily` (manifest/pgg_analysis_status.v); `ExactWitness`,
  `MkExactWitness`, `tableau_start`, the `supplied inputs`, `execute`, `sample`,
  `certify`, `publish` notations (manifest/pgg_tableau.v, pgg_tableau_syntax.v);
  `inde_RV`, `fdist_prod`, `fdist_uniform`, `fdistmap` (infotheo);
  `uniform_fdistmap_fiberE` (reconstruct/design_privacy.v); `perm_on`,
  `card_perm`, `perm_of_eq_card` (mathcomp perm.v, lib/perm_exchange.v);
  `psl211_pattern_transfer`, `psl211_mirror_blocks`, `psl211_hexad_blocks`,
  `psl211_blocks_disjoint`, `psl211_subset_class`, `psl211_orbit_valid`
  (instances/psl211).

## 6. Not built, with reasons

- No spectral (word) row: `sc_const` is per input and fails at three positions
  under the dealt mode; under the all-decks mode it is a different statement
  nobody has measured. The corollaries `psl211_endpoint_mixing`,
  `psl211_joint_mixing` stay as cut-level results.
- No `psl211_run.v` / `psl211_trace.v`: trace secrecy is not a field of the
  manifest row; the executed content reader (D1) is what the facade's observer
  section needs. Recorded as a follow-up.
- No `leaks at 6` on the row (G1).

## 7. Audit verdicts

(filled after the soundness and naming audits of 2026-09-15)
