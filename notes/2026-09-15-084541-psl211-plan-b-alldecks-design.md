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
most five seats (L24), because the number of class-`b` decks producing a
given reading is the block count `N_A(b)` of the pattern times two factorials,
and the block counts agree between the classes (`psl211_pattern_transfer`).

## 2. Flow (adopted sketch)

```
start    psl211_algebra                                          by algebra { ... }                        // Algebraic (P0 GO)
supplied inputs (bool * psl211_deal) layout psl211_alldecks_layout expecting fst fuel 220                 // Executable (P3 GO)
execute  terminates by psl211_alldecks_terminates (named lemma, proved by vm_compute, 0.4 s)              // Observed:
         endpoints by psl211_alldecks_endpoints : instance_endpoints_stmt psl211_alldecks_params
                      := supplied_endpointsE psl211_profile_endpoints  (cost 0 here; psl211_profile_endpoints itself is the 900 s, 17 GB fact, paid once)
         recon     by psl211_alldecks_recon := supplied_static_recon psl211_algebra psl211_alldecks_valid   //   Hv new, bookkeeping
sample   psl211_exact_family  (index unit; law psl211_alldecks_sampleP := `U input `x `U G)               // Sampled
certify  ExactIndependence psl211_exact_witness  by L24 = bridge + fiber counts                            // AnalysisBridged, new mathematics
|> publish StaticExecutedOnly BaselineClassicalOnly                                                       // manifest row psl211_row_alldecks
```

Roles. Objects: the five stack levels. Step justifications: the three run facts,
the witness. Terminal: `publish`. Observation change at cost 0: the identification
of `static_coalition_obs` with the position reading of the laid deck
(`static_coalition_obsE`, pgg_instance.v:496). External components and their
interfaces: `psl211_profile` enters as the `algebra` block's image (by `[]`);
`psl211_pattern_transfer` (psl211_orbit.v:1118) enters as the step justification
of the block-count equality; `card_prescribed` (lib/perm_uniform.v:117) enters as
the extension count; `inde_RV`/`fdist_prod` (infotheo) enter through the new bridge
lemma `uniform_prod_inde_fiber`. Outside the flow: the fixed-dealer colour result of Plan A (stays in
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
- `psl211_alldecks_seq (b, (j, ph, pc))`: position p in block line j of the
  class-b table carries heart code `ph (rank of p in the line)`, every other
  position carries `6 + pc (rank of p in the complement)`; ranks by `index` in
  the ascending line (probe_p3_alldecks.v:54-62). `psl211_alldecks_layout` casts
  it to `12.-tuple 'I_12` through `psl211_code12` (the probe's `Imod12`, renamed
  under the psl211_ prefix decision). The cast to the framework's
  `(ts_T' (pga_scheme psl211_algebra)).+1.-tuple 'I_(pga_n psl211_algebra).+2`
  is by conversion (audit-naming N35, compiled both ways).
- `psl211_alldecks_valid : forall x, ts_valid (pga_scheme psl211_algebra) x.1
  (psl211_alldecks_layout x)`, i.e. `psl211_orbit_valid x.1 (layout x)`
  (`ts_valid (pga_scheme psl211_algebra) = psl211_orbit_valid` by erefl): distinct
  codes, heart set a block of one system, class bit recovered. `expecting fst` is
  what makes `supplied_static_recon`'s premise `ts_valid _ (expected x) (layout x)`
  and this statement one term.
- Sample space `(bool * psl211_deal) * pgg_gT psl211_M`, law
  `psl211_alldecks_sampleP := (`U psl211_alldecks_gt0) `x (`U psl211_G_pos)`
  (second-mode spelling as `s5_rand_sampleP`; Plan A keeps `psl211P`); adapter
  `psl211_alldecks_sample := MkSampleAdapter sampleT psl211_alldecks_sampleP fst snd`;
  secret `psl211_alldecks_secret u := u.1.1`; family `psl211_exact_family` with
  index `unit` as pgl27_exact_family.
- Fuel 220 (P1b2: sufficient, cost flat).
- Files: `psl211_alldecks.v` (layout, validity, the per-cut fiber counting C5,
  stated on the layout alone; imports psl211_blocks/orbit/scheme and
  lib/perm_uniform; no framework import),
  `psl211_exec.v` (players cache, algebra block, both parameter records,
  termination, recon), `psl211_endpoints.v` (ONLY `psl211_profile_endpoints`, its
  own file, header records 900 s / 17 GB / no concurrent rocqworker),
  `psl211_models.v` (observed execution, sample adapter, static-obs
  identification C2, L24 at the probability layer C6 through the bridge C3,
  executed content reader, exact family, witness ingredients),
  `psl211_rows.v` (Tableau program, published row, rowE), `psl211_analysis.v`
  (facade `PSL211Analysis`, seven sections), manifest and client edits.
  `reconstruct/design_privacy.v` gains the generic bridge `uniform_prod_inde_fiber`
  (section 4, C3).
- `_CoqProject`: every psl211 line (now 193-201, after the manifest) moves above
  `manifest/pgg_analysis_manifest.v` (187) next to `instances/pgl27/pgl27_analysis.v`
  (186), in the order blocks, group, closure, orbit, scheme, profile, secrecy,
  recovery, mixing, alldecks, exec, endpoints, models, analysis; `psl211_rows.v`
  goes after `manifest/pgg_tableau_syntax.v` beside the other row files.
  `reconstruct/design_privacy.v` (170) already precedes all of them.
- The claim ledger's status and pass columns stay in this note; no statement
  comment in a landed file carries a status marker.

## 4. Claim ledger

| # | claim | kind | passes when | status |
|---|---|---|---|---|
| A1 | `algebra { ... }` block at the psl211 names; `instance_profile psl211_algebra = psl211_profile` and `profile_k = 6` by `[]` | probed | P0 | GO (P0) |
| A2 | termination of the dealt run (fuel 380 and 220) and of the all-decks run by `vm_compute`; the all-decks run at fuel 220, the row's fuel, is measured in PROBE-REPORT-2 | probed | P1a, P1b2, P3, PROBE-REPORT-2 | GO at 380; 220 measured in the second probe pass |
| A3 | `profile_endpoints_stmt psl211_algebra 220` by `vm_compute`, 562 s + 331 s Qed, 17 GB, no axioms | probed | P1b2, P1d | GO, measured |
| A4 | `supplied_endpointsE` carries A3 to the all-decks mode; `supplied_static_recon psl211_algebra Hv` gives recon | probed | P3 Checks | GO (shape) |
| B1 | validity, distinct codes: `uniq (psl211_alldecks_layout x)` for all x, proved symbolically in j from the table certificates (rows uniq, size 6, entries < 12: psl211_blocks.v) | new proof shape | miniature Qed over the real tables, no vm_compute over inputs | to probe |
| B2 | validity, heart set: `psl211_heart_set (layout x) = psl211_list_to_set (block line j of class x.1)` and it lies in the system of x.1 | new proof shape | Qed | to probe |
| B3 | validity, class: `psl211_orbit_class (layout x) = x.1`, i.e. `psl211_subset_class (psl211_heart_set (layout x)) = x.1` with `psl211_subset_class` the boolean membership in `psl211_mirror_blocks` (psl211_orbit.v:123), from B2 and `psl211_blocks_disjoint` for the hexad side | precedent shape (psl211_orbit_encode_valid) | Qed | to probe |
| C1 | sample adapter `MkSampleAdapter` with `sa_sampleT := (bool * psl211_deal) * pgg_gT psl211_M`, `sa_sampleP := psl211_alldecks_sampleP`, `sa_arg := fst`, `sa_cut := snd` elaborates at `instance_exec psl211_alldecks_params` | precedent (pgl27_fixed_sample) | elaborates | to probe |
| C2 | `static_coalition_obs C x g = [ffun i => if i \in C then tnth (layout x) (pgg_rho g i) else ord0]` in supplied mode: `static_coalition_obsE` gives the right side with a `tcast` (vanishes by conversion) and `tnth (pi_starts _) i` (one `tnth_ord_tuple`), audit-naming N2 | precedent (pgl27_rows.v:142-150, P2 dealt version) | Qed | to probe |
| C3 | generic bridge `uniform_prod_inde_fiber` (design_privacy.v): for finTypes X, G, A : {set G} nonempty (`HA : 0 < #\|A\|`), `HX : (0 < #\|[set: X]\|)%N` (the whole carrier; at a proper subset the statement is false, audit-soundness 7), s : X -> bool, and f : X -> G -> T with, for every v, equal counts of `[set u : X * G \| s u.1 == b & u.2 \in A & f u.1 u.2 == v]` over b, the law `(`U HX) `x (`U HA)` makes `fun u => f u.1 u.2` independent of `fun u => s u.1`. Nearest landed results, neither applicable: `colour_view_indep_fibers` (design_privacy.v:110, secret is the literal first coordinate, counts over G alone) and `inde_prod_fst` (transitivity_privacy.v:88, second RV is `fst`, premise a conditional law equal for every value); here the secret is `s \o fst` and the view is not independent of `fst` | PROVED by the soundness audit: `c3_bridge` in notes/probes/2026-09-15-psl211-planb/audit-soundness/audit_c3.v (Qed, boolp trio), with `c3_classes_from_counts` showing the equal-class-sizes condition FOLLOWS from the count premise (Closed), so the landed lemma carries no such premise; mutation that does falsify it: drop the `u.2 \in A` restriction from the counts, or take f a function of u.1 alone | copied verbatim into design_privacy.v | GO (compiled) |
| C4 | extension count at 'I_6: ALREADY PROVED, `card_prescribed` (lib/perm_uniform.v:117: `injective s -> injective v -> k <= N -> #\|prescribed s v\| = (N - k)`!`, with `prescribed` :33, `Sn_k_transitive` :58, `prescribed_coset` :92, `prescribed_extend` :210). What remains is one restatement from a set `K : {set 'I_6}` with a map `t` to the `'I_k -> 'I_6` sequence shape `prescribed` takes, and the zero case when the prescribed values are not injective | precedent (audit-naming N26) | restatement Qed at 'I_6 | to probe |
| C5 | fiber decomposition: for fixed g, C with 0 < #\|C\| <= 5, and a reading v, `#\|[set y : psl211_deal \| reading (b, y) g == v]\| = #\|[set B in blocks b \| B :&: P == A]\| * e_h * e_c` with P := pgg_rho g @: C (fixed by C2), `#\|P\| = #\|C\|` by `card_imset` and `perm_inj`, A the heart positions of v inside P (row C5a), `A \subset P`, `e_h`, `e_c` the two extension counts from C4, or 0 when v is not colour-consistent; the block count equal across b by `psl211_pattern_transfer` instantiated at P (premises `0 < #\|P\|`, `#\|P\| <= 5`, `A \subset P`, the two cardinalities transported from C by `card_imset (perm_inj _)`: compiled as `audit_transfer_at_P` in audit-soundness/audit_c2_tcast.v; empty C separately) | new proof shape | decomposition probe: headline L24 derived to Qed from the supporting statements Admitted; C4 restatement Qed. No vm_compute sanity check: the deal carrier does not reduce (`enum 'I_6` is stuck, `enum {perm 'I_6}` killed at 5 GB, audit-soundness 10); the numeric check is audit-soundness/audit_alldecks.py over the tracked tables (sizes 1..3 exhaustive, 1..5 sampled, size 6 witness (0,1,2,3,4,10) with reading (0,1,2,3,4,5) at 720 versus 0) | to probe |
| C5a | the passage from the per-seat reading to the pattern: for a reading v of C at cut g on a deck laid over block B, the set of seats reading a heart code is `[set i in C \| psl211_is_heart (v i)]` and its image under `pgg_rho g` is `B :&: P`; stated through `psl211_heart_set`/`psl211_is_heart` on the image set | new (audit-naming N32) | Qed in the decomposition probe | to probe |
| C6 | L24 at the probability layer (lives in psl211_models.v, needs psl211_algebra): `psl211_alldecksP \|= (fun u => static_coalition_obs C u.1 u.2) _\|_ psl211_alldecks_secret` for #\|C\| <= 5, from C3 with C5 summed over g in G | composition | decomposition probe Qed | to probe |
| C7 | `ExactWitness` for `amf_sample psl211_exact_family R tt` built as pgl27_exact_witness (eq_ind_r over the viewE identification) | precedent (pgl27_rows.v:187-196) | typechecks with C6 Admitted | to probe |
| C7a | the witness is about the recovered value: `psl211_alldecks_secret u = ex_expected psl211_alldecks_params (sa_arg psl211_alldecks_sample u)` by `[]` (the framework's `ExactWitness` does not tie `ew_secret` to `ex_expected`, so a trivial secret would typecheck and say nothing; audit-soundness 13) | new, one-line | Qed by `[]` (compiled as `audit_secret_is_recovered`) | GO |
| D1 | executed content reader and `content_traceE` in supplied mode (pgl27_models.v:168-215 shape), reading the endpoint fact from the probe's `.vo` | precedent | typechecks | to probe |
| E1 | Tableau row: `supplied inputs ... expecting ... fuel 220`, `execute terminates by psl211_alldecks_terminates endpoints by psl211_alldecks_endpoints recon by psl211_alldecks_recon`, `sample`, `certify ExactIndependence`, `\|> publish StaticExecutedOnly BaselineClassicalOnly` (two arguments, pgg_tableau_syntax.v:395); named obligations only: the inline `terminates by vm_compute` form forks the observed execution and the following `sample` is rejected (pgl27_rows.v:362, compiled Fail) | precedent (pgl27_rows.v:124-129, 270-275; five_card_rows.v:123-135 for a non-dealt mode) | typechecks with the witness Admitted | to probe |
| E2 | facade `PSL211Analysis` with one alias per section (1 profile, 2 exec plug, 3 content reader, 4 exact family, 5 observed_recovers, 6 exec_exact_view_indep, 7 StaticExecutedOnly status). Manifest obligations, per audit-naming N33: the `Require Export` (pgg_analysis_manifest.v:74), a documented row block (~65 lines, shape of :121-185), `Definition psl211_row_alldecks` (shape of :659), a per-instance deterministic checker block (~270 lines, shapes at :739-1011, :1012-1303, :1304-1526), and five pins per row (three erefl, `Check (row : AnalysisPathRow)`, `Check (apr_model row : AnalysisModelFamily PSL211Analysis.observed)`, :1535-1541); client: header wording (three facades, eight rows) and one Check per section (pgg_analysis_client.v). Scripts that enumerate facades by hand and need a psl211 entry: scripts/profile_facade_check.sh:87-100 (`EXPECTED` table; `psl211_profile` is a depth-zero Definition, psl211_profile.v:123) and scripts/profile_facade_check_test.py:25-27 | precedent (pgl27_analysis.v, manifest, client) | plan task, sized honestly | precedent |
| F1 | every published object BaselineClassicalOnly: Print Assumptions of the row, the witness and L24 report exactly the boolp trio; the run facts and validity closed | invariant | rocq repl over the .vo chain | plan task |
| G2 | the parametrization `(j, ph, pc) |-> deck` is a bijection onto the valid decks of the class (injective through the heart set and the table uniqueness `psl211_mirror_tbl_uniq`/`psl211_hexad_tbl_uniq`, surjective because a valid deck's heart codes are distinct and below six); checked numerically (audit-soundness/audit_alldecks.out (e), (e')), not proved in Rocq; the row's law is stated on the parameter carrier and does not depend on it | not claimed | recorded in the row file header | not claimed |
| G1 | `ExactLeakAt 6` under the all-decks dealer | optional | not claimed in this plan; tightness stays with `psl211_colour_view_dep_k6` at the fixed dealer | not claimed |

## 5. Soundness invariants

- No new axiom, hypothesis or assumed constant anywhere; the classical trio of
  boolp is the baseline and is the whole assumption set of every published
  object (F1).
- The row's claim is about the all-decks dealer: the deck description
  `(class, block line, heart labelling, club labelling)` uniform on the parameter
  carrier `bool * psl211_deal`, whose class-b half has `132 * 720 * 720` points
  and maps onto the valid decks of the class (G2, numerically checked, not
  claimed); class uniform (index `unit`, so the secret prior is uniform, and
  ExactProp's entropy forms are at that prior); cut uniform on the group
  (`psl211_G_pos` for the law, `psl211_card` for its order 660). It is an average over decks and cuts,
  per coalition, single observation. It neither implies nor is implied by
  Plan A's fixed-dealer colour result; both stand, and the row file says which
  dealer it is about in its header.
- Quantifier order: for every coalition C with #|C| < 6, the reading random
  variable is independent of the class random variable under the fixed law
  `psl211_alldecksP`. Not per input, not per cut.
- Vacuity: both classes have `132 * 6! * 6!` inputs (`psl211_deal` is the
  class-b half for either b, so equal class sizes are `erefl`; the carrier count
  `#|{: bool * psl211_deal}| = 2 * 132 * 6! * 6!` is restated at the pair carrier,
  audit-soundness 16), the group has 660 elements (`psl211_card`,
  psl211_closure.v:703; `psl211_G_pos` is only positivity), every coalition of size 1..5
  is covered by `psl211_count_ok_k_le5` (psl211_orbit.v:1096) through
  `psl211_pattern_transfer`, the empty
  coalition is trivial. The threshold is the profile's own `profile_k = 6`.
- Cited library objects, one line each: `static_coalition_obs`,
  `static_coalition_obsE`, `supplied_input_params`, `supplied_static_recon`,
  `supplied_endpointsE`, `instance_observed` (protocol/pgg_instance.v);
  `MkSampleAdapter` (security/pgg_sample_adapter.v; `sa_coalition_view` enters only
  through the facade's observer section, not the witness);
  `MkAnalysisModelFamily` (manifest/pgg_analysis_status.v); `ExactWitness`,
  `MkExactWitness`, `tableau_start`, the `supplied inputs`, `execute`, `sample`,
  `certify`, `publish` notations (manifest/pgg_tableau.v, pgg_tableau_syntax.v);
  `inde_RV`, `fdist_prod`, `fdist_uniform`, `fdistmap` (infotheo);
  `uniform_fdistmap_fiberE` (reconstruct/design_privacy.v); `prescribed`,
  `card_prescribed`, `prescribed_extend` (lib/perm_uniform.v); `perm_on`,
  `card_perm` (mathcomp perm.v); `perm_of_eq_card` (lib/perm_exchange.v) serves
  Plan A's re-deal only and is not used here;
  `psl211_pattern_transfer`, `psl211_mirror_blocks`, `psl211_hexad_blocks`,
  `psl211_blocks_disjoint`, `psl211_subset_class`, `psl211_orbit_valid`,
  `psl211_card`, `psl211_G_pos` (instances/psl211).

## 6. Not built, with reasons

- No spectral (word) row: `sc_const` is per input and fails at three seats
  under the dealt mode at the group-uniform ideal, the only ideal for which a
  certificate would have a usable `sc_close` (at the uniform law on all of
  `{perm 'I_12}` the reading is a uniform injective tuple and `sc_const` would
  hold, but `sc_close` would not); under the all-decks mode it is a different
  statement nobody has measured. The corollaries `psl211_endpoint_mixing`,
  `psl211_joint_mixing` stay as cut-level results.
- No `psl211_run.v` / `psl211_trace.v`: trace secrecy is not a field of the
  manifest row; the executed content reader (D1) is what the facade's observer
  section needs. Recorded as a follow-up.
- No `leaks at 6` on the row (G1).

## 7. Audit verdicts

Naming/precedent/structure audit (Opus, 2026-09-15,
notes/probes/2026-09-15-psl211-planb/AUDIT-NAMING-2.md): NO-GO, 43 findings, six
blocking (N13 inline terminates rejected before `sample`; N12 publish takes two
statuses; N26 C4 already proved by `card_prescribed`; N37/N33/N34 the fourth
facade's real size, _CoqProject move, scripts tables; N36 C6 cannot live in
psl211_alldecks.v; N28 the bridge had no name). All folded above: sketch lines
rewritten, C1 gains `sa_sampleP`, C2 default `ord0` and the `pi_starts` step, C3
named `uniform_prod_inde_fiber` with the two nearest results cited, C4 reduced to
a restatement, C5 gains `A \subset P` and `card_imset`, C5a added, E1 and E2
rewritten, `Imod12` renamed `psl211_code12`, `psl211_alldecksP` renamed
`psl211_alldecks_sampleP`, `psl211_list_to_set` and `psl211_count_ok_k_le5` cited
by their live names, seat/position/block line/row vocabulary fixed, five_card
cite narrowed to 123-135, lib/perm_uniform.v added to section 5.

Soundness audit (Opus, 2026-09-15,
notes/probes/2026-09-15-psl211-planb/AUDIT-SOUNDNESS-2.md): NO-GO on four ledger
instructions, GO on the mathematics. Confirmed: L24 true at the real tables
(Python over the tracked block tables, per-block closed form against a 720 x 720
brute force, sizes 1..3 exhaustive, 1..5 sampled), sharp at six (witness coalition
(0,1,2,3,4,10), reading (0,1,2,3,4,5): 720 mirror decks, 0 hexad); the generic
bridge proved (`c3_bridge`, boolp trio) with the equal-class-sizes condition a
consequence of the count premise; `card_prescribed` exactly as cited; class
orientation right; the supplied layout is the dealt deck and `ex_expected` is the
class bit (three `[]` conversions); the row's headline restated in English is
non-vacuous. Folded above: C3 loses the class-size premise and pins `HX` to the
whole carrier (findings 6, 7); C5's transfer premises are at P (9); C5's
vm_compute sanity check deleted (10); C7a added (13); `psl211_card` cited for 660
(14); G2 added and the dealer sentence restated on the parameter carrier (15);
the carrier count restated per class at the pair carrier (16); A2's coverage
stated honestly with the 220 all-decks measurement assigned to the second probe
pass (17); the spectral sentence qualified by the ideal (18).

## 8. Second probe pass (2026-09-15, notes/probes/2026-09-15-psl211-planb/PROBE-REPORT-2.md)

Rows B1, B2, B3 (validity, symbolic in j, twelve plus five plus three lemmas,
all closed), C1, C2 (identification closed), C3 (`uniform_pair_indep_of_fibers`,
the class-size premise derived, not assumed), C4 (`perm_ext_count` from
`card_prescribed`, closed), C6/C7 (headline, witness and `psl211_row_alldecks :
PublishedRow` derived to Qed from five named supports), D1, E1 (named
termination lemma, two-argument publish): GO. All-decks termination at fuel 220
measured at about 0.5 s. `Print Assumptions psl211_row_alldecks` in the
decomposition probe lists exactly `psl211_alldecks_fiber_transfer`,
`psl211_alldecks_endpoints` and the boolp trio, so what separates the row from a
finished result is ONE new mathematical statement (the per-cut fiber count summed
over the group, row C5) and the already-measured endpoint reduction.

Corrections to section 3 from the probes, binding on the plan:
- `psl211_deal` and `psl211_inputT` are Notations, not Definitions (a Definition
  hides the finite structure from `#|...|` and `` `U ``).
- `psl211_alldecks_gt0 : (0 < #|[set: psl211_inputT]|)%N`.
- Fuel 220 throughout (`psl211_fuel_small` of the probes becomes `psl211_fuel`).
- The laid deck does NOT reduce under `vm_compute` at any input (`inord`'s
  `insub` is guarded by the Qed-opaque `idP`); every statement about it is
  proved symbolically, including the validity lemmas, which the probes already
  do.
- The bridge consumes the SUMMED count `psl211_alldecks_fiber_transfer` (for
  every reading v, equal counts over `psl211_deal * G` restricted to the group),
  not the per-cut count; the per-cut decomposition (block count times two
  extension counts) is the proof route, not a statement on the path.
- No count below six points separates the two tables (both are S(5,6,12)); the
  only mutation that fails is membership of a six-set.
- The `.vo` of the 900-second endpoint fact is invalidated by ANY rebuild of
  psl211_scheme.v, psl211_profile.v or anything below them, even from identical
  sources (digest change). The plan lands psl211_exec.v and psl211_endpoints.v
  once and then freezes every file below them; any later edit there is budgeted
  at 15 minutes and 17 GB.
- pgl27 keeps `psl211_alldecks_cardE` in the pair shape with a trailing `mulnA`.
