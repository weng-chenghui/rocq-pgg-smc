# PSL(2,11) Plan B: the executed cone on the all-decks dealer

> **For agentic workers:** REQUIRED SUB-SKILL: use `superpowers:subagent-driven-development`
> (recommended) or `superpowers:executing-plans` to implement this plan task by
> task. Steps use checkbox (`- [ ]`) syntax for tracking. Read section 2 (build
> order and the freeze rule) before running any compile, because one declaration
> in this plan costs 900 seconds and 17 GB and is invalidated by a rebuild of
> any file below it.

**Goal:** land the executed-protocol cone of `instances/psl211/` and its
`AnalysisPathRow`, certified through `ExactIndependence` under the ALL-DECKS
dealer in the framework's supplied-inputs mode: the deck description drawn
uniformly over class, block line and the two colour labellings, the cut drawn
uniformly over the 660 elements of the group, and the raw card reading of every
coalition of at most five of the twelve seats independent of the chirality
(ledger row L24).

**Architecture:** the cone mirrors `instances/pgl27/` file for file (exec,
models, analysis, rows plus the manifest and client edits), with three
differences fixed by two probe passes. The dealer is the supplied-layout one
rather than `dealt_secret_params`, because in dealt mode both Tableau arms are
refuted at three seats (probe P2). The endpoint equation lives alone in
`psl211_endpoints.v` because it is the most expensive declaration the
repository would then contain. And independence comes from a new generic
bridge in `reconstruct/design_privacy.v` fed by one new counting theorem,
`psl211_alldecks_fiber_transfer`, which is the only unproved statement on the
path from the tables to the published row.

**Tech stack:** Rocq 9.0, MathComp 2.5 (fingroup, action, perm, finset, bigop),
infotheo 0.9.7 (fdist, proba), the repo's `pgg_smc` / `pgg_reconstruct`
namespaces. Build from the repo root with `make -j1`.

**Spec:** `notes/2026-09-15-084541-psl211-plan-b-alldecks-design.md`, sections 2
to 8. Section 8 lists the corrections binding on this plan; they are applied
throughout and each is named where it bites.

**Probe evidence, the verbatim source for every task:**
`notes/probes/2026-09-15-psl211-planb/`, namely `PROBE-REPORT.md` (P0-P4) with
`psl211_planb_defs.v` and `probe_p1b2_endpoints_small.v`; `PROBE-REPORT-2.md`
(B1-B3, C1-C7, D1, E1) with `planb_alldecks_defs.v`, `probe_b1_uniq.v`,
`probe_b2_heart.v`, `probe_b3_class.v`, `probe_c1_adapter.v`,
`probe_c2_bridge.v`, `probe_c3_bridge.v`, `probe_c4_extcount.v`,
`probe_c5_sanity.v`, `probe_c56_decomposition.v`, `probe_d1_observed.v`,
`probe_e1_row_variants.v`; the two audits `AUDIT-NAMING-2.md` and
`AUDIT-SOUNDNESS-2.md` with `audit-soundness/audit_c3.v`,
`audit-soundness/audit_c2_tcast.v`, `audit-soundness/audit_alldecks_shapes.v`
and `audit-soundness/audit_alldecks.py`. Probe files are never `Require`d;
their code is copied, and every task names the file and the declarations it
copies. Where the design note and a probe disagree on a spelling, the probe's
spelling is used, because the probe compiled it.

**Plan A record:** `docs/superpowers/plans/2026-09-14-psl211-chirality-instance.md`.
Its "As built" paragraphs supply five operating lessons this plan inherits:
`make -j1` (never `-j8` beside a large reduction), `rocq compile` with the
project flags as the fallback when a single target will not resolve, never
`git add -A`, `Local Notation` for a table-valued certificate makes a later
`done` walk into the table (a `Local Notation` for a TYPE is safe and the
probes use several), `%N` on every nat sub-statement under `ring_scope`, and
for assumption checks `rocq repl` over the `.vo` chain rather than the
`rocq-mcp` assumptions tool, which loads `.vos` and reports every opaque lemma
as an axiom.

---

## 0. Flow sketch (DSL-first)

The connecting operation is the Tableau's own `;;;`: each statement adjoins one
payload to a stack and raises the completion level, and the invariant it
preserves is that the accumulated proposition is proved at the level the stack
has reached. The currency is two-valued and both halves are tracked on every
line: the assumption set the line adds, and the reduction the line spends.

```
start    psl211_algebra                                             by algebra { ... }
                                     // Algebraic       | assumptions: none        | reduction: 0
supplied inputs psl211_inputT layout psl211_alldecks_layout
         expecting psl211_alldecks_expected fuel psl211_fuel
                                     // Executable      | assumptions: none        | reduction: 0
execute  terminates by psl211_alldecks_terminates
                                     // Observed        | assumptions: none        | reduction: 0.5 s + 0.5 s Qed
         endpoints  by psl211_alldecks_endpoints
                       := supplied_endpointsE psl211_profile_endpoints
                                     // Observed        | assumptions: none        | reduction: 0 here; 561 s + 331 s at 17 GB
                                     //                                            |   inside psl211_profile_endpoints, paid once
         recon      by psl211_alldecks_recon
                       := supplied_static_recon psl211_algebra psl211_alldecks_ts_valid
                                     // Observed        | assumptions: none        | reduction: 0; rows B1-B3 pay it symbolically
sample   psl211_exact_family
         (index unit; law psl211_alldecksP := `U psl211_alldecks_gt0 `x `U psl211_G_pos)
                                     // Sampled         | assumptions: boolp trio  | reduction: 0
certify  ExactIndependence psl211_exact_witness
         (field ew_indep filled by psl211_alldecks_static_indep)
                                     // AnalysisBridged | assumptions: boolp trio  | reduction: 0;
                                     //                                            |   the new counting theorem is here
|> publish StaticExecutedOnly BaselineClassicalOnly
                                     // PublishedRow    | assumptions: boolp trio  | manifest row psl211_row_alldecks
```

**Roles.** Objects: the five stack levels. Step justifications: the three run
facts and the exact witness. Terminal evaluation: `publish`, which reads the
manifest row off the accumulated stack. Observation change at cost zero:
`psl211_alldecks_static_obsE`, which identifies the framework's
`static_coalition_obs` with the instance's reading of the laid deck at the cut
image of the seat. Invocation of an assumption: none; every line is
unconditional, and the boolp trio that appears from the `sample` line onward is
the `R.-fdist` record's own floor, not a hardness assumption.

**External components and the interface each enters through.**
`psl211_profile` enters as the image of the `algebra { ... }` block, by `[]`
(`psl211_profileE`). `psl211_profile_endpoints` enters as the endpoints step's
justification, through `supplied_endpointsE`. `psl211_pattern_transfer`
(`psl211_orbit.v:1118`) enters as the block-count step of the new counting
theorem, instantiated at the position set `P := pgg_rho g @: C`.
`card_prescribed` (`lib/perm_uniform.v:117`) enters as the labelling count,
through the restatement `psl211_perm_ext_count`. `inde_RV` and `fdist_prod`
enter through the new bridge `uniform_pair_indep_of_fibers`.

**Outside the DSL.** Plan A's fixed-dealer colour result stays in
`psl211_secrecy.v` and has no Tableau arm. The two mixing corollaries stay as
cut-level results in `psl211_mixing.v`. `ExactLeakAt 6` is not claimed. The
parametrization's bijection onto the valid decks of a class (G2) is checked
numerically and is not a theorem; the row's law is stated on the parameter
carrier and does not depend on it.

**Monad verdict.** A parameterised structure indexed by pre- and post-completion
level, graded by the accumulated `StackProp`; the laws hold as landed in
`manifest/pgg_tableau.v`. Nothing new is built here: this plan writes programs
in an existing surface.

---

## 1. Scope

**Built.** One `_CoqProject` reordering, one generic lemma in
`reconstruct/design_privacy.v`, six new files under `instances/psl211/`,
namely `psl211_exec.v`, `psl211_endpoints.v`, `psl211_alldecks.v`,
`psl211_models.v`, `psl211_analysis.v` and `psl211_rows.v`, the manifest's
fourth facade block and ninth row, the client's Checks and header wording, and
two hand-maintained script tables.

**Not built, with the reason.**

- **No spectral (word) row.** `sc_const` is per input and fails at three seats
  under the dealt mode at the group-uniform ideal, the only ideal for which a
  certificate would have a usable `sc_close`. Under the all-decks dealer it is
  a different statement and nobody has measured it.
- **No `psl211_run.v` and no `psl211_trace.v`.** Trace secrecy is not a field
  of the manifest row. The executed content reader in `psl211_models.v` is what
  the facade's observer section needs.
- **No `ExactLeakAt 6`.** Tightness stays with `psl211_colour_view_dep_k6` at
  the fixed dealer. The size-six separation is real and measured
  (`audit_alldecks.out`: coalition `(0,1,2,3,4,10)`, reading `(0,1,2,3,4,5)`,
  720 mirror decks against 0 hexad decks) but is a numeric check, not a Rocq
  theorem.
- **G2, the bijection `(j, ph, pc) |-> deck`, is not claimed.** It is checked
  numerically in `audit_alldecks.out` (e) and (e'). The row file's header says
  the law is uniform on the deck descriptions and that they enumerate the valid
  decks of a class once each as a numeric check.
- **`lib/perm_uniform.v` is not extended.** See Decision 4.

---

## 2. File map, build order, and the freeze rule

| file | responsibility | ledger rows | task |
|---|---|---|---|
| `_CoqProject` | psl211 block moved above the manifest; one line per new file added in the commit that lands it | — | T1, then each task |
| `reconstruct/design_privacy.v` | the generic independence bridge for a secret that is a function of the first coordinate | C3 | T1 |
| `instances/psl211/psl211_exec.v` | seat cache, the `algebra { ... }` block, the fuel, the dealt parameter record and its recon | A1, A2 | T2 |
| `instances/psl211/psl211_endpoints.v` | `psl211_profile_endpoints` and nothing else | A3 | T3 |
| `instances/psl211/psl211_alldecks.v` | the laid deck, its validity, the extension count, the all-decks parameter record with its termination and recon, and the fiber counts | B1, B2, B3, C4, C5, C5a | T4 |
| `instances/psl211/psl211_models.v` | observed execution, sample adapter, the static-obs identification, L24 at the probability layer, the executed content reader, the exact family and its witness | C1, C2, C6, C7, C7a, D1 | T5 |
| `instances/psl211/psl211_analysis.v`, `manifest/pgg_analysis_manifest.v`, `manifest/pgg_analysis_client.v`, `scripts/profile_facade_check.sh`, `scripts/profile_facade_check_test.py` | the fourth facade, the ninth row, the checker block and the two script tables | E2 | T6 |
| `instances/psl211/psl211_rows.v` | the Tableau program, the published row, `rowE` against the manifest row | E1 | T7 |
| — | full build, assumption sweep, as-built record, REVIEWS.md | F1 | T8 |

### Build order, and which files the 900-second fact rests on

`make` derives its order from `coqdep`, not from the order of lines in
`_CoqProject`, so "below the endpoint fact" means "inside the import closure of
`psl211_endpoints.v`", never "earlier in the file list".

That closure was computed twice, once by the plan audit and once here, by
walking the live `Require` lines transitively over `lib`, `protocol`, `groups`,
`security`, `smc`, `reconstruct`, `instances/*` and `manifest`, modelling
`psl211_exec.v` by the import block of `psl211_planb_defs.v` that T2 copies and
`psl211_endpoints.v` by T3's own four `Require` lines. Both runs agree: **35
already-landed files, plus `psl211_exec.v` and `psl211_endpoints.v`
themselves, 37 in all.**

```
groups/pgg_raag.v
instances/psl211/psl211_blocks.v      instances/psl211/psl211_closure.v
instances/psl211/psl211_group.v       instances/psl211/psl211_orbit.v
instances/psl211/psl211_profile.v     instances/psl211/psl211_scheme.v
lib/perm_exchange.v                   lib/perm_uniform.v
protocol/card_exchange_pismc.v        protocol/pgg_algebra_syntax.v
protocol/pgg_execution_plug.v         protocol/pgg_input_commitment.v
protocol/pgg_instance.v               protocol/pgg_interface.v
protocol/pgg_monodromy_profile.v      protocol/pgg_observed_execution.v
protocol/pgg_run.v                    protocol/pgg_session_types.v
reconstruct/algebraic_rigidity.v      reconstruct/cover_tradeoff.v
reconstruct/covering_scheme.v         reconstruct/input_encoding.v
reconstruct/pgg_sharing_framework.v   reconstruct/pgg_sum_mod.v
reconstruct/pgl_bound.v               reconstruct/transitivity_privacy.v
security/pgg_collusion_bound.v        security/pgg_sample_adapter.v
security/pgg_security_solver.v        security/pgg_weighted_words.v
smc/graded_resource.v                 smc/pismc.v
smc/smc_interpreter.v                 smc/smc_session_types.v
+ instances/psl211/psl211_exec.v      + instances/psl211/psl211_endpoints.v
```

Seven of these are reached only transitively and are easy to believe free:
`groups/pgg_raag.v`, `reconstruct/cover_tradeoff.v`,
`reconstruct/pgg_sum_mod.v`, `reconstruct/pgl_bound.v`,
`security/pgg_collusion_bound.v`, `security/pgg_security_solver.v` and
`security/pgg_weighted_words.v`. Editing any one of them costs 900 seconds and
17 GB.

Trimming T2's import list to the minimum (T2 Step 1b) removes exactly two,
`security/pgg_sample_adapter.v` and `security/pgg_weighted_words.v`, measured
here; the other five arrive through `psl211_profile.v` and `psl211_closure.v`
and cannot be trimmed from `psl211_exec.v` at all.

`reconstruct/design_privacy.v` is **not** in the closure: the only psl211 file
that imports it is `psl211_secrecy.v`, which nothing in the executed cone
imports, and a whole-tree scan finds no other file whose transitive closure
reaches it. `psl211_alldecks.v` is **not** in it either, because
`psl211_endpoints.v` imports `psl211_exec.v` alone and `psl211_exec.v` carries
no all-decks declaration. Also outside, and therefore free to edit after T3:
`psl211_mixing.v`, `psl211_secrecy.v`, `psl211_recovery.v`,
`instances/pgl27/pgl27_trace.v`, `manifest/pgg_tableau.v` and
`manifest/pgg_tableau_syntax.v`. Both exclusions are consequences of Decisions
2 and 3 below and they are the reason the plan is ordered as it is.

### Freeze rule

```
+----------------------------------------------------------------------------+
| FREEZE RULE, in force from the moment T3 commits.                           |
|                                                                             |
| psl211_endpoints.vo holds one declaration that costs 561 s of vm_compute,   |
| 331 s of Qed and a true peak of 17.15 GB (probe P1b2, /usr/bin/time -l).    |
| Its .vo is invalidated by ANY rebuild of ANY file in the import closure     |
| listed above, INCLUDING a rebuild from byte-identical sources: the library  |
| digest changes and every dependent reports                                  |
|   "makes inconsistent assumptions over library pgg_smc.psl211_scheme".      |
| PROBE-REPORT-2 records that exact failure killing the probe chain.          |
|                                                                             |
| 1. After T3 commits, do not edit any file in that closure. If one must be   |
|    edited, budget 15 minutes and 17 GB, batch every change to that closure  |
|    into ONE commit, and re-run T3's compile once at the end.                |
| 2. Never run the T3 compile beside a second rocqworker. The machine has     |
|    32 GB; 17 GB alone is survivable and 17 GB twice is not. Use `make -j1`  |
|    for the T3 compile and for any full build that may reach it, and check   |
|    with `pgrep -l rocqworker` that nothing else is running first.           |
| 3. Do not run `make clean`, and do not delete instances/psl211/*.vo.        |
| 4. `rocq makefile -f _CoqProject -o Makefile.rocq` does not invalidate any  |
|    .vo: it regenerates the makefile only. Regenerating it is safe at any    |
|    time and is required after every _CoqProject edit.                       |
+----------------------------------------------------------------------------+
```

---

## 3. Conventions used by every task

**Single-target compile**, from the repo root:

```bash
make -j1 instances/psl211/<file>.vo 2>&1 | tail -3 && echo BUILD-OK
```

The wrapper `Makefile` delegates `%.vo` to `Makefile.rocq`, so dependencies are
rebuilt. If a target does not resolve (a file added to `_CoqProject` after the
last makefile regeneration), regenerate and retry:

```bash
rocq makefile -f _CoqProject -o Makefile.rocq && make -j1 -f Makefile.rocq instances/psl211/<file>.vo
```

As a last resort, compile one file directly with the project's own flags:

```bash
rocq compile -q -w -projection-no-head-constant -w -redundant-canonical-projection \
  -w -notation-overridden -w -ambiguous-paths -w -notation-incompatible-format \
  $PSL211_RFLAGS instances/psl211/<file>.v
```

**Assumption check.** Use `rocq repl` over the compiled `.vo` chain. Do not use
the `rocq-mcp` `rocq_assumptions` tool: it loads `.vos` files, in which every
opaque proof is a hole, and it reports those holes as axioms. Define once per
shell:

```bash
export PSL211_RFLAGS="-R lib pgg_smc -R protocol pgg_smc -R groups pgg_smc \
  -R security pgg_smc -R smc pgg_smc -R reconstruct pgg_reconstruct \
  -R instances/denboer1989 pgg_smc -R instances/kim2025 pgg_smc \
  -R instances/s5 pgg_smc -R instances/pgl27 pgg_smc \
  -R instances/psl211 pgg_smc -R manifest pgg_smc"
```

and then, for each task:

```bash
printf 'From pgg_smc Require Import <module>.\nPrint Assumptions <name>.\n' \
  | rocq repl -q $PSL211_RFLAGS
```

"Closed" below means `Closed under the global context`. "the boolp trio" means
exactly `propositional_extensionality`, `functional_extensionality_dep` and
`constructive_indefinite_description`, and nothing else.

**Commits.** One task, one commit, and the task's compile must pass before the
next task starts. Stage the named files explicitly. **Never `git add -A`**: the
working tree carries thirty untracked note and probe directories that must not
enter a commit.

**Statement comments.** Every `Definition`, `Lemma`, `Theorem` and `Notation`
carries a `(** name — ... *)` block stating what the object is mathematically
and where it sits in the argument. The probe comments are the drafts; strip
from each of them the probe framing ("This is a probe", "ADMITTED HERE ONLY",
"Nothing here is landed"), every status word, and every effort estimate. Where
a probe comment records a proof trap, move that text to a `(* ... *)` source
comment inside the proof, not into the rendered statement body.

**File headers.** The 80-column infotheo header box: two licence lines, the
file name and one-line purpose, a paragraph of what the file is about, a
`Definitions:` list and a `Key results:` list, closed by the rule line. Every
new file below follows `instances/psl211/psl211_profile.v:1-24` for the shape.

---

### Task 1: `_CoqProject` reorder and the generic independence bridge

**Files:**
- Modify: `_CoqProject` (lines 186-202)
- Modify: `reconstruct/design_privacy.v` (header box and a new section at the end)
- Source: `notes/probes/2026-09-15-psl211-planb/probe_c3_bridge.v`, whole file
  below the preamble; `audit-soundness/audit_c3.v` is the independent
  confirmation and is **not** the copy source (Decision 5)

- [ ] **Step 1: Move the psl211 block above the manifest**

Delete lines 193-201 (`instances/psl211/psl211_blocks.v` through
`instances/psl211/psl211_recovery.v`) and reinsert them immediately after line
186, `instances/pgl27/pgl27_analysis.v`, in this order:

```
instances/psl211/psl211_blocks.v
instances/psl211/psl211_group.v
instances/psl211/psl211_closure.v
instances/psl211/psl211_orbit.v
instances/psl211/psl211_scheme.v
instances/psl211/psl211_profile.v
instances/psl211/psl211_secrecy.v
instances/psl211/psl211_mixing.v
instances/psl211/psl211_recovery.v
```

This is the current order of `_CoqProject:193-201` unchanged. The move is a
move and nothing else: do not reorder the nine lines while relocating them, and
in particular keep `psl211_mixing.v` before `psl211_recovery.v` as they stand
today.

Reason: `manifest/pgg_analysis_manifest.v` will need `PSL211Analysis.observed`
to type `apr_model psl211_row_alldecks`, so the whole psl211 cone must precede
it, beside `instances/pgl27/pgl27_analysis.v` (audit N37).
`reconstruct/design_privacy.v` at line 170 already precedes both and does not
move.

Do **not** add the six new file paths now. Plan A's as-built record
(`docs/superpowers/plans/2026-09-14-psl211-chirality-instance.md`, Task 1 Step
2) measured that registering a file that does not yet exist breaks `coqdep` for
the whole tree. Each new file's line is added in the commit that lands that
file, at the position the task names.

- [ ] **Step 2: Regenerate the makefile**

```bash
rocq makefile -f _CoqProject -o Makefile.rocq && echo MAKEFILE-OK
```

- [ ] **Step 3: Add the bridge to `reconstruct/design_privacy.v`**

No import changes. The file already imports `bigop`, `ssralg`, `ssrnum`,
`order`, `boolp`, `reals`, `realType_ext`, `fdist`, `proba` and already opens
`fdist_scope`, `proba_scope` and `ring_scope`, and it already has
`Import GRing.Theory` and `Import Num.Theory`. Add to the header box, after the
existing `Section 2` line:

```
(* Section 3 -- card_fiber_sum, pr_countE, uniform_pair_indep_of_class,      *)
(*   uniform_pair_indep_of_fibers == independence of an observation of both   *)
(*   coordinates from a secret read off the first one.                        *)
```

Then append two sections at the end of the file, copied token for token from
`probe_c3_bridge.v` (which compiled in 3.90 s with zero `Admitted` and zero
`Axiom`): `Section fiber_sum` with `card_fiber_sum`, and `Section bridge` with
its five section variables, the two `Let`s, and `pr_countE`,
`uniform_pair_indep_of_class`, `pair_fibers_class_sizes`,
`uniform_pair_indep_of_fibers`, in that order. The discharged signatures the
rest of the plan cites are:

```coq
Lemma card_fiber_sum (Y W : finType) (g : Y -> W) (Q : pred Y) :
  #|[set y : Y | Q y]| = (\sum_(w : W) #|[set y : Y | Q y && (g y == w)]|)%N.

Lemma uniform_pair_indep_of_fibers :
  (forall v : T,
     #|[set u : X * G | (s u.1 == true) && (u.2 \in A) && (f u.1 u.2 == v)]|
     = #|[set u : X * G | (s u.1 == false) && (u.2 \in A) && (f u.1 u.2 == v)]|) ->
  P |= (fun u => f u.1 u.2 : T) _|_ (fun u => s u.1 : bool).
```

discharging from `Section bridge` as

```
forall (R : realType) (X G T : finType) (s : X -> bool) (A : {set G})
  (HA : (0 < #|A|)%N) (HX : (0 < #|[set: X]|)%N) (f : X -> G -> T),
  (forall v : T, #|[set u | (s u.1 == true) && (u.2 \in A) & f u.1 u.2 == v]|
               = #|[set u | (s u.1 == false) && (u.2 \in A) & f u.1 u.2 == v]|) ->
  (`U HX) `x (`U HA) |= (fun u : X * G => f u.1 u.2) _|_ (fun u : X * G => s u.1)
```

with `X`, `G`, `T` implicit, `R`, `HA`, `HX` explicit, and the `Let P` inlined
rather than left as a redex.

Four things must not be changed while copying.

1. **`HX` is `(0 < #|[set: X]|)%N`, at the whole carrier, not `(0 < #|{: X}|)%N`
   and not at a proper subset.** At a proper subset the statement is false:
   mass outside the subset is zero while the counts still see it
   (AUDIT-SOUNDNESS-2 finding 7). `` `U `` is `fdist_uniform_supp` and takes a
   `{set _}`; `{: _}` belongs with `fdist_uniform`, a different constructor.
2. **The class-size premise is absent.** It follows from the fiber-count
   premise by summing over the reading value and cancelling `#|A| > 0` with
   `eqn_pmul2r`; `pair_fibers_class_sizes` proves exactly that and is landed
   beside the bridge. Two independent proofs agree on this
   (`probe_c3_bridge.v` and `audit-soundness/audit_c3.v`'s
   `c3_classes_from_counts`, written without knowledge of each other).
3. **The `%N` annotations stay.** `design_privacy.v` opens `ring_scope`, under
   which `#|S1| + #|S2|` elaborates to `GRing.add` on `nat` rather than `addn`,
   after which `cardsID`, `sum1_card` and `\sum_(w : W) #|...|` all misfire.
   Every nat sub-statement in the copied code already carries its `%N`; do not
   remove one.
4. **Four smaller spellings recorded by the probe.** The first explicit argument
   of `fdist_uniform_supp_in` is the positivity hypothesis, not the point;
   `eqn_pmul2r` takes only the `0 < m` proof; `-mulr_natl` grabs the numeral
   inside `2^-1` unless pinned with a `[pattern]`; and `rewrite` counts
   occurrences up to conversion, so one rewrite can hit two syntactically
   different but convertible random variables at once.

The two statement comments to write, in the project's style:

```coq
(** card_fiber_sum — the cardinality of a set is the sum of its cardinalities
    over the fibers of any map out of it.  Stated here because every counting
    premise below is a per-value count and every conclusion is a total, and
    this is the only step between them. *)

(** uniform_pair_indep_of_fibers — when a secret is read off the first
    coordinate of a uniform pair and an observation depends on both
    coordinates, equal per-value counts of the observation over the two
    secret classes make the observation independent of the secret.  This is
    the sibling of colour_view_indep_fibers for a secret that is a function of
    the first coordinate rather than the coordinate itself: there the counts
    are taken over the group alone and the conclusion is independence of the
    coordinate, which is false here, because the rest of the first coordinate
    is not independent of the observation.  inde_prod_fst of
    transitivity_privacy.v does not reach it either, since its second random
    variable is fst and its premise is a conditional law equal at every value
    of the first coordinate, not only across the two classes. *)
```

- [ ] **Step 4: Compile and check**

```bash
make -j1 reconstruct/design_privacy.vo 2>&1 | tail -3 && echo BUILD-OK
make -j1 instances/psl211/psl211_secrecy.vo 2>&1 | tail -3 && echo BUILD-OK
```

Expected cost: about 8 s for `design_privacy.v` (the probe's standalone file was
3.90 s; the existing file's two sections are already paid) and about 7 s for
`psl211_secrecy.v`, which is the only psl211 file that imports it. Nothing in
the endpoint closure is touched.

```bash
printf 'From pgg_reconstruct Require Import design_privacy.\nPrint Assumptions card_fiber_sum.\nPrint Assumptions pair_fibers_class_sizes.\nPrint Assumptions pr_countE.\nPrint Assumptions uniform_pair_indep_of_class.\nPrint Assumptions uniform_pair_indep_of_fibers.\n' | rocq repl -q $PSL211_RFLAGS
```

Expected: `card_fiber_sum` and `pair_fibers_class_sizes` Closed; `pr_countE`,
`uniform_pair_indep_of_class` and `uniform_pair_indep_of_fibers` exactly the
boolp trio, which arrives through the `R.-fdist` record and is the F1 baseline.

- [ ] **Step 5: Commit**

```bash
git add _CoqProject Makefile.rocq reconstruct/design_privacy.v
git commit -m "feat(design_privacy): independence from equal fiber counts when the secret is a function of the first coordinate"
```

If `Makefile.rocq` is untracked in this repository, omit it from the `git add`
and stage only the two sources.

---

### Task 2: `instances/psl211/psl211_exec.v`

**Files:**
- Create: `instances/psl211/psl211_exec.v`
- Modify: `_CoqProject` (one line, after `instances/psl211/psl211_mixing.v`)
- Source: `notes/probes/2026-09-15-psl211-planb/psl211_planb_defs.v:8-30` (the
  imports and the flags) and `:32-94` (every declaration; the file is 94 lines),
  plus `probe_p1b2_endpoints_small.v:19-21` for the termination lemma, which the
  probe states as `psl211_dealt_terminates_small` against
  `psl211_dealt_params_small`. Decision 8 collapses the two fuels, so the
  probe's `_small` twin and the lemma landed here are one statement. The probe
  writes `Proof. Time by vm_compute. Time Qed.`; the `Time` wrappers are
  dropped here and the measurement lives in the file header

This file is deliberately minimal. Everything it contains is something
`psl211_endpoints.v` or `psl211_alldecks.v` needs, and nothing else, because
from T3 onward every edit to it costs 15 minutes and 17 GB (see the freeze
rule). The all-decks parameter record, its termination and its recon are
**not** here; they are in `psl211_alldecks.v` (Decision 2).

- [ ] **Step 1: Write the file**

Header box: name, the sentence that the file carries the algebraic record of
the twelve-card chirality instance and the dealt run over it, the `Definitions:`
list (`psl211_players`, `psl211_algebra`, `psl211_fuel`, `psl211_dealt_params`,
`psl211_dealt_recon`) and the `Key results:` list (`psl211_players_enumE`,
`psl211_profileE`, `psl211_profile_kE`, `psl211_dealt_terminates`). Add one
paragraph naming the freeze rule as a fact about the file, not as a status
marker:

```
(* This file and its whole import closure lie below psl211_endpoints.v, whose*)
(* single declaration costs 561 seconds of vm_compute, 331 seconds of Qed and *)
(* a 17 GB peak.  Rebuilding this file from byte-identical sources changes    *)
(* the library digest and invalidates that .vo.                              *)
```

Every line of a landed `instances/psl211/*.v` file is at most 80 columns wide,
measured across all ten of them, so each header-box line above is exactly 80
including the closing `*)`. Keep that width in every file this plan lands, and
rewrap the copied code where a probe exceeded it: `probe_c3_bridge.v` has six
lines over 80 (`:73`, `:119`, `:122`, `:127`, `:159`, `:190`, up to 83), and
`reconstruct/design_privacy.v`, its destination, measures 80.

Imports, copied verbatim from `psl211_planb_defs.v:8-30`, which is the whole
block from `From HB Require Import structures.` through the second
`Local Open Scope`:

```coq
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_weighted_words.
From pgg_smc Require Import pgg_observed_execution pgg_sample_adapter.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import pgg_instance pgg_algebra_syntax.
From pgg_smc Require Import psl211_group psl211_closure psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
```

Declarations, verbatim from `psl211_planb_defs.v:32-94` with `psl211_fuel := 380`
and `psl211_fuel_small := 220` replaced by the single `psl211_fuel := 220` and
`psl211_dealt_params_small` deleted, plus `psl211_dealt_terminates` from
`probe_p1b2_endpoints_small.v:19-21` at the collapsed fuel:

```coq
Definition psl211_players : seq 'I_(pi_T' psl211_PI).+1 :=
  [:: @Ordinal 12 0 isT; @Ordinal 12 1 isT; @Ordinal 12 2 isT;
      @Ordinal 12 3 isT; @Ordinal 12 4 isT; @Ordinal 12 5 isT;
      @Ordinal 12 6 isT; @Ordinal 12 7 isT; @Ordinal 12 8 isT;
      @Ordinal 12 9 isT; @Ordinal 12 10 isT; @Ordinal 12 11 isT].

Lemma psl211_players_enumE : psl211_players = enum 'I_(pi_T' psl211_PI).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

Definition psl211_algebra : PGGAlgebraic := algebra {
  mount   << psl211_gens >> ;
  walk    along psl211_moves by psl211_gen3_eq ;
  seat    players (ord_tuple 12) by psl211_starts_uniq ;
  secret  bool ;
  deal    psl211_orbit_scheme
          encode psl211_orbit_encode
          read   psl211_orbit_class
          private by psl211_private
          shuffled_by pgg_rho by psl211_orbit_recon_invariant ;
  cache   seats psl211_players by psl211_players_enumE }.

Lemma psl211_profileE : instance_profile psl211_algebra = psl211_profile.
Proof. by []. Qed.

Definition psl211_fuel : nat := 220.

Definition psl211_dealt_params : ExecutionParams psl211_algebra :=
  dealt_secret_params psl211_algebra psl211_fuel.

Definition psl211_dealt_recon : instance_recon_stmt psl211_dealt_params :=
  dealt_static_recon psl211_algebra psl211_fuel.

Lemma psl211_dealt_terminates : instance_terminates_stmt psl211_dealt_params.
Proof. by vm_compute. Qed.

Lemma psl211_profile_kE : profile_k (instance_profile psl211_algebra) = 6.
Proof. by []. Qed.
```

Statement comments: the probe's for `psl211_players`, `psl211_players_enumE`,
`psl211_algebra`, `psl211_profileE`, `psl211_dealt_params` are already in the
house style and transfer unchanged. The fuel comment is rewritten, because the
probe's two-budget comment describes an experiment rather than the object:

```coq
(** psl211_fuel — the interpreter budget of the fourteen-process run: the
    dealer, the verifier and the twelve seats.  220 steps, the budget the
    eight-card instance uses.  The interpreter halts once no process advances,
    so a budget past the number of communication rounds is never spent. *)

(** psl211_dealt_terminates — every process of the dealer-dealt run reaches
    Finish inside that budget.  The reduction is symbolic in the cut, so it
    does not enumerate the group. *)

(** psl211_profile_kE — the privacy threshold the derived profile declares is
    six, so every arm of a row over this algebra quantifies over coalitions of
    at most five of the twelve seats. *)
```

- [ ] **Step 1b: Trim the import list, before T3 commits**

The declaration list above is minimal, but the import block copied from the
probe prelude is not, and every import widens the closure that T3 freezes. Drop
each import in turn, recompile, and keep the drop if the file still compiles.
The candidates are `pismc`, `smc_session_types`, `pgg_session_types`,
`card_exchange_pismc`, `pgg_input_commitment`, `pgg_run`, `pgg_weighted_words`,
`pgg_observed_execution`, `pgg_sample_adapter`, `pgg_execution_plug`,
`variation_dist`, `realType_ext`, `fdist`, `proba`, `boolp`, `reals`,
`algebraic_rigidity`, `input_encoding`, `covering_scheme` and
`pgg_sharing_framework`; what the file genuinely needs is `smc_interpreter` for
the reduction, `pgg_interface`, `pgg_instance`, `pgg_algebra_syntax` for the
`algebra { ... }` surface, and the five psl211 files.

Measured here, this trim removes exactly two files from the closure,
`security/pgg_sample_adapter.v` and `security/pgg_weighted_words.v`, taking it
from 37 to 35. The other five transitively reached files arrive through
`psl211_profile.v` and `psl211_closure.v` and cannot be trimmed away from this
file at any import list. Re-measure the closure after the trim and correct the
number in the header box and in section 2 before T3 commits, because after T3
this file cannot be touched for the price of a measurement.

- [ ] **Step 2: Register, compile, check**

Add `instances/psl211/psl211_exec.v` to `_CoqProject` after
`instances/psl211/psl211_recovery.v`, regenerate the makefile, then:

```bash
rocq makefile -f _CoqProject -o Makefile.rocq
make -j1 instances/psl211/psl211_exec.vo 2>&1 | tail -3 && echo BUILD-OK
```

Expected cost: about 5 s (the probe's file measured 3.50 s; `psl211_dealt_terminates`
adds the P1b2 measurement of 0.958 s of `vm_compute` and 0.62 s of `Qed`).
Expected peak: 1.6 GB.

```bash
printf 'From pgg_smc Require Import psl211_exec.\nPrint Assumptions psl211_players_enumE.\nPrint Assumptions psl211_profileE.\nPrint Assumptions psl211_profile_kE.\nPrint Assumptions psl211_dealt_recon.\nPrint Assumptions psl211_dealt_terminates.\n' | rocq repl -q $PSL211_RFLAGS
```

Expected: Closed for all five. Four of them were read back directly from the
probe `.vo` chain by the plan audit. The fifth, `psl211_dealt_terminates`,
could not be, because `probe_p1a_terminates.vo` is stale and reports
inconsistent assumptions over `planb.psl211_planb_defs`; its all-decks twin,
the same `by vm_compute` at the same fuel, measured Closed twice.

- [ ] **Step 3: Commit**

```bash
git add _CoqProject instances/psl211/psl211_exec.v
git commit -m "feat(psl211): the algebraic record of the twelve-card instance and its dealer-dealt run"
```

---

### Task 3: `instances/psl211/psl211_endpoints.v` — the 900-second fact

**Files:**
- Create: `instances/psl211/psl211_endpoints.v`
- Modify: `_CoqProject` (one line, after `instances/psl211/psl211_exec.v`)
- Source: `notes/probes/2026-09-15-psl211-planb/probe_p1b2_endpoints_small.v:15-17`,
  with the `_small` suffixes dropped from both the lemma name and the fuel
  constant under Decision 8, which makes the probe's statement and this one one
  statement

- [ ] **Step 0: Check the machine before starting**

```bash
pgrep -l rocqworker || echo NO-ROCQWORKER
```

Expected `NO-ROCQWORKER`. If anything is listed, wait. 17 GB beside a second
rocqworker does not fit in 32 GB.

- [ ] **Step 1: Write the file**

The whole file, header box apart, is:

```coq
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From pgg_smc Require Import smc_interpreter pgg_instance.
From pgg_smc Require Import psl211_exec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** psl211_profile_endpoints — at every content readout, the executed
    endpoints of a run over this profile are its static group-action reading.
    Keeping the readout a variable removes the dealt card from the statement,
    so the equation holds of every run driven over this profile: the
    dealer-dealt mode reads it through profile_endpointsE and the
    supplied-layout mode through supplied_endpointsE.  This is what carries a
    claim about the interpreter's messages to a claim about the group action,
    and every security statement of this instance is made on the group-action
    side. *)
Lemma psl211_profile_endpoints :
  profile_endpoints_stmt psl211_algebra psl211_fuel.
Proof. Time by vm_compute. Time Qed.
```

The header box carries the cost and the freeze rule as facts about the file:

```
(******************************************************************************)
(* psl211_endpoints: the endpoint equation of the twelve-card instance        *)
(*                                                                            *)
(* One declaration, alone in its own file.  Deciding it costs 561 seconds of  *)
(* vm_compute, 331 seconds of Qed and a true peak of 17.15 GB, measured with  *)
(* /usr/bin/time -l on a 32 GB machine.  The cost is the twelve-card,         *)
(* fourteen-process interpreter trace and not the budget: the same reduction  *)
(* at fuel 380 measured 562 s and 343 s, a difference inside the noise.  The  *)
(* reduction is symbolic in the cut; were it enumerating the 479001600        *)
(* permutations of twelve points it would not finish at any per-element cost. *)
(*                                                                            *)
(* Do not run this compile beside a second rocqworker.  Use make -j1.         *)
(*                                                                            *)
(* This .vo is invalidated by any rebuild of psl211_exec.v, psl211_profile.v, *)
(* psl211_scheme.v, psl211_orbit.v, psl211_closure.v, psl211_group.v,         *)
(* psl211_blocks.v, lib/perm_exchange.v, lib/perm_uniform.v or the framework  *)
(* under them, INCLUDING a rebuild from byte-identical sources: the library   *)
(* digest changes and every dependent then reports inconsistent assumptions.  *)
(*                                                                            *)
(* Definitions: none.                                                         *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_profile_endpoints == the executed endpoints of a run over this    *)
(*                               profile are its static group-action reading  *)
(******************************************************************************)
```

The file is split off from `psl211_exec.v` against the pgl27 precedent, which
keeps the analogue inline at `pgl27_exec.v:383` (audit N38, a deliberate and
documented departure). See Decision 3.

- [ ] **Step 2: Register and compile**

```bash
rocq makefile -f _CoqProject -o Makefile.rocq
/usr/bin/time -l make -j1 instances/psl211/psl211_endpoints.vo 2>&1 | tail -20
```

Expected: about 900 s wall, a `Time` line near 561 s for the tactic and near
331 s for the `Qed`, and a `maximum resident set size` near 17.15 GB. Record
the three numbers in the as-built section at T8; if any differs from the
measurement by more than ten percent, record the new number rather than the
probe's.

```bash
printf 'From pgg_smc Require Import psl211_endpoints.\nPrint Assumptions psl211_profile_endpoints.\n' | rocq repl -q $PSL211_RFLAGS
```

Expected: Closed. Probe P1d measured Closed for this statement at **fuel 380**,
over `probe_p1b_endpoints.vo`. The fuel-220 run,
`probe_p1b2_endpoints_small.v`, carries no `Print Assumptions` and was never
read back, so this is the first reading at the fuel the row uses. The two
statements differ only in a `nat` literal and the reduction is the same, so a
result other than Closed would be a surprise worth stopping for.

- [ ] **Step 3: Commit, and start the freeze**

```bash
git add _CoqProject instances/psl211/psl211_endpoints.v
git commit -m "feat(psl211): the endpoint equation of the twelve-card profile, decided once"
```

From this commit on, the freeze rule of section 2 is in force.

---

### Task 4: `instances/psl211/psl211_alldecks.v` — the laid deck and the fiber counts

**Files:**
- Create: `instances/psl211/psl211_alldecks.v`
- Modify: `_CoqProject` (one line, after `instances/psl211/psl211_endpoints.v`)
- Source: `planb_alldecks_defs.v:34-106` (the carrier, the layout, the
  parameters and the two cardinalities; `:108-118` is T5's and must not be
  copied here, or `psl211_alldecksP` and `psl211_alldecks_secret` land in two
  files and the second will not compile); `probe_b1_uniq.v` (the whole file
  below the preamble); `probe_b2_heart.v`; `probe_b3_class.v`;
  `probe_c4_extcount.v`; `probe_c5_sanity.v:48-55`
  (`psl211_alldecks_read_setE` alone; `psl211_alldecks_read_position` at
  `:37-46` is T5's); `probe_c2_bridge.v:32-42` (the view definition, docstring
  through the closing `else ord0].`);
  `probe_c56_decomposition.v:107-128` (the two fiber statements with their
  docstrings at `:94-128`; their proofs are new)

This is the largest task and the only one with an unproved statement in it.
The file is outside the endpoint fact's import closure, so it may be edited and
recompiled freely at about 20 seconds a pass.

- [ ] **Step 1: Carrier, layout and cardinalities**

Copied from `planb_alldecks_defs.v:34-106`, which runs from the `psl211_deal`
docstring to the `Qed.` of `psl211_alldecks_cardE` and stops there. `:108-118`,
the law and the secret, belongs to T5 Step 1 and is not copied here. `Imod12`
is renamed `psl211_code12` and exported (audit N24: `Imod12` is probe-only and
off-convention), and `psl211_fuel_small` is renamed `psl211_fuel`:

```coq
Notation psl211_deal := (('I_132 * {perm 'I_6} * {perm 'I_6})%type).
Notation psl211_inputT := ((bool * psl211_deal)%type).

Definition psl211_code12 (k : nat) : 'I_12 := Ordinal (ltn_pmod k (ltn0Sn 11)).

Definition psl211_class_tbl (b : bool) : seq (seq nat) :=
  if b then psl211_mirror_tbl else psl211_hexad_tbl.

Definition psl211_alldecks_row (x : psl211_inputT) : seq nat :=
  nth [::] (psl211_class_tbl x.1) (val x.2.1.1).

Definition psl211_alldecks_corow (x : psl211_inputT) : seq nat :=
  [seq p <- iota 0 12 | p \notin psl211_alldecks_row x].

Definition psl211_alldecks_seq (x : psl211_inputT) : seq nat :=
  let: (b, (j, ph, pc)) := x in
  let H := psl211_alldecks_row x in
  let K := psl211_alldecks_corow x in
  [seq (if p \in H then val (ph (inord (index p H)))
        else 6 + val (pc (inord (index p K)))) | p <- iota 0 12].

Definition psl211_alldecks_layout (x : psl211_inputT)
  : (ts_T' (pga_scheme psl211_algebra)).+1.-tuple 'I_(pga_n psl211_algebra).+2
  := [tuple psl211_code12 (nth 0 (psl211_alldecks_seq x) (val i)) | i < 12].

Definition psl211_alldecks_expected (x : psl211_inputT) : bool := x.1.

Definition psl211_alldecks_params : ExecutionParams psl211_algebra :=
  supplied_input_params psl211_algebra psl211_inputT
    psl211_alldecks_layout psl211_alldecks_expected psl211_fuel.

Lemma psl211_alldecks_gt0 : (0 < #|[set: psl211_inputT]|)%N.
Proof. by apply/card_gt0P; exists (true, (ord0, 1%g, 1%g)); rewrite inE. Qed.

Lemma psl211_alldecks_cardE : #|{: psl211_inputT}| = 2 * 132 * 6`! * 6`!.
Proof. by rewrite !card_prod card_bool card_ord !card_Sn mulnA. Qed.
```

Five spellings are load-bearing and must not be normalised away.

1. **`psl211_deal` and `psl211_inputT` are `Notation`s, not `Definition`s.** A
   `Definition psl211_deal := (...)%type` was tried first and the `#|...|` and
   `` `U `` uses did not elaborate through it: the product's finite structure is
   not found behind the definition.
2. **The class bit is first and separate**, so the secret is `fst` and the
   generic bridge of T1 applies with `s := fst`. The probe P3 left-nested
   quadruple is gone; `x.1.1.1` of P3 is `x.1` here.
3. **`psl211_alldecks_gt0` is stated at `[set: _]`**, not at `{: _}`, because
   `` `U `` is `fdist_uniform_supp` and takes a `{set _}`.
4. **`psl211_alldecks_cardE` is left-factored and ends with `mulnA`.** The
   product written as one `nat` literal is a `Nat.of_num_uint` term whose unary
   expansion of 136857600 successors the kernel would have to build; the
   trailing `mulnA` is what the pair shape needs and the left-nested quadruple
   did not.
5. **The layout keeps its ascription to the framework's carrier**,
   `(ts_T' (pga_scheme psl211_algebra)).+1.-tuple 'I_(pga_n psl211_algebra).+2`.
   Both `.+1` and `.+2` are 12 by `[]` (audit N35, compiled in both
   directions), and `12.-tuple 'I_12` unifies with it by conversion at `apply:`
   with no `tcast` and no measurable cost.

The statement comments of `planb_alldecks_defs.v` are already in the house
style and transfer unchanged, except that `psl211_alldecks_params` gains the
sentence naming the mode:

```coq
(** psl211_alldecks_params — the run-level data of the all-decks run: the run
    argument is a whole deck description rather than a bare secret, the layout
    lays that description as the dealt deck, and the value the run recovers is
    the class bit of its input.  This is the supplied-layout mode of the
    framework; the dealer-dealt mode of psl211_exec.v is this mode at the
    canonical encoding, which is why the endpoint equation serves both. *)
```

- [ ] **Step 2: Distinctness (ledger row B1)**

Copy `probe_b1_uniq.v` from `ad_code` to `psl211_alldecks_uniq` verbatim, less
its `Print Assumptions` block and its `Fail Definition mut_b1`. Make every
`ad_*` declaration `Local` (`Local Definition ad_code`, `Local Lemma
ad_heart_lt12`, and so on for `ad_club_lt12`, `ad_inordK`, `ad_class_tbl_size`,
`ad_class_tbl_asc6`, `ad_row_mem`, `ad_row_asc6`, `ad_asc6_uniq`,
`ad_asc6_size`, `ad_asc6_lt12`, `ad_size_filter_split`, `ad_corow_size`,
`ad_corow_mem`, `ad_tnthE`, `ad_seqE`, `ad_entryE`, `ad_idx6`, `ad_idx_inj`,
`ad_uniq_gen`), so that the file-wide `psl211_` prefix rule that audit N30
verified is not broken by twenty exported unprefixed names. The precedent for
Local unprefixed helpers is `psl211_scheme.v` (nineteen) and
`psl211_recovery.v` (fourteen).

Keep the probe's comment `(* Implicit arguments are deliberately left off in
this file, as psl211_orbit.v leaves them off: every helper below is applied at
explicit block rows and explicit labellings, and a stolen leading parameter is
the most expensive mistake to diagnose in that position. *)` and do **not** put
`Set Implicit Arguments` above this block.

The exported statement:

```coq
(** psl211_alldecks_uniq — the all-decks layout deals twelve distinct cards,
    for every class bit, every block line and every pair of labellings.  The
    hearts are distinct because the heart labelling and the rank map are
    injective on the block, the clubs likewise on the complement, and no heart
    code equals a club code because the club codes start at six.  This is
    psl211_deck_ok of the layout, the first of the three conjuncts of the
    orbit scheme's validity predicate, and it is what lets the dealer be
    driven by a uniform draw over the whole input carrier instead of by a
    chosen representative deal. *)
Lemma psl211_alldecks_uniq (x : psl211_inputT) :
  uniq (psl211_alldecks_layout x).
```

Four traps the probe paid for, each to be carried as a source comment at the
site, not as a statement comment:

- `val` on an ordinal and `nat_of_ord` are convertible but not syntactically
  equal. `psl211_orbit.v` writes `psl211_is_heart c := (val c < 6)%N` and
  `psl211_list_to_set L := [set x : 'I_12 | val x \in L]` through
  `isSub.val_subdef`, while the layout is read through `nat_of_ord`; `rewrite`
  between them fails with "does not match any subterm". The one-line bridge
  `ad_valE` of Step 3 is the fix and must be rewritten before the entry
  equation.
- The numeral 6 is a subterm of the numeral 12. A backwards rewrite with
  `size H = 6` on a goal containing `iota 0 12` rewrites the 6 inside the 12
  and the symptom surfaces four lines later as an unrelated `Cannot apply
  lemma`. `ad_corow_size` transports the row size through `perm_size`
  instead; never backwards.
- `psl211_alldecks_seq` only reduces at a destructured input, because of its
  `let: (b, (j, ph, pc)) := x in`. `ad_seqE` and `ad_entryE` are therefore
  stated at `(b, (j, ph, pc))`; everything above them is stated at abstract `x`
  and only the proofs open it.
- `sorted_uniq` carries a section transitivity hypothesis and does not take
  `ltn_trans` as written (`ltn_sorted_uniq_leq` is one rewrite and needs no
  arguments); `count_predC` spells the complement as a `simpl_pred` and does
  not match `fun p => p \notin H` (hence the five-line `ad_size_filter_split`);
  `nth_index` leaves `x` and `s` implicit, so the call is `nth_index 0 Hp`; and
  `apply/hasP; exists R` needs an explicit `exact: eqxx`, since `core` carries
  no `Hint Resolve eqxx`.

- [ ] **Step 3: The heart set (ledger row B2)**

Copy `probe_b2_heart.v` from `ad_valE` to `psl211_alldecks_subset_valid`
verbatim, less its `Print Assumptions` block and its `Fail Definition mut_b2`.
`ad_valE` and `ad_heart_gen` are `Local`; `ad_row_in_mirror_blocks` and
`ad_row_in_hexad_blocks` are `Local` too. The two exported statements:

```coq
Lemma psl211_alldecks_heart_setE (x : psl211_inputT) :
  psl211_heart_set (psl211_alldecks_layout x)
  = psl211_list_to_set (psl211_alldecks_row x).

Lemma psl211_alldecks_subset_valid (x : psl211_inputT) :
  psl211_subset_valid (psl211_heart_set (psl211_alldecks_layout x)).
```

with the probe's comments, which are already declarative. The first says the
dealer's only freedom that touches the secret is the choice of table, since the
block line and the two labellings leave the heart set on the same block; the
second is the second conjunct of `psl211_orbit_valid`. The live name of the
code-list bridge is `psl211_list_to_set` (audit N25).

- [ ] **Step 4: The chirality and validity (ledger row B3)**

Copy `probe_b3_class.v` from `psl211_alldecks_classE` to
`psl211_alldecks_ts_valid` verbatim, less its `Print Assumptions` block and its
two `Fail Definition`s:

```coq
Lemma psl211_alldecks_classE (x : psl211_inputT) :
  psl211_orbit_class (psl211_alldecks_layout x) = x.1.

Lemma psl211_alldecks_valid (x : psl211_inputT) :
  psl211_orbit_valid x.1 (psl211_alldecks_layout x).

Lemma psl211_alldecks_ts_valid (x : psl211_inputT) :
  ts_valid (pga_scheme psl211_algebra)
    (psl211_alldecks_expected x) (psl211_alldecks_layout x).
Proof. exact: psl211_alldecks_valid. Qed.
```

`psl211_alldecks_ts_valid` closes by `exact:` because
`ts_valid (pga_scheme psl211_algebra)` IS `psl211_orbit_valid` and
`psl211_alldecks_expected x` IS `x.1`, both by conversion (audit N21, N4), so
no transport stands between B1-B3 and the reconstruction obligation. The
hexad direction of `psl211_alldecks_classE` is the only place the two Steiner
systems are compared, through `psl211_blocks_disjoint` and `disjointFl`; that
sentence belongs in the statement comment and the probe already writes it.

- [ ] **Step 5: The three run facts of the all-decks run**

```coq
(** psl211_alldecks_terminates — every process of the fourteen-process
    all-decks run finishes inside the budget.  The reduction is symbolic in
    the cut and in the deck description: the layout is never destructed, so
    its stuck content is carried through at no cost, and the all-decks mode is
    no more expensive to terminate than the dealer-dealt one. *)
Lemma psl211_alldecks_terminates :
  instance_terminates_stmt psl211_alldecks_params.
Proof. by vm_compute. Qed.

(** psl211_alldecks_recon — decoding the coalition-free endpoints of the
    all-decks run returns the class bit, from validity alone.  The framework
    derives it from the coordinate law, so the whole of what this instance
    owes reconstruction is rows B1 to B3. *)
Definition psl211_alldecks_recon : instance_recon_stmt psl211_alldecks_params :=
  supplied_static_recon psl211_algebra psl211_alldecks_ts_valid.
```

Measured: 0.41 to 0.50 s for the tactic and 0.47 to 0.53 s for the `Qed`,
across three separate probe files at fuel 220. The endpoint fact is not here;
it is assembled in `psl211_models.v`, which is the first file to import both
`psl211_alldecks.v` and `psl211_endpoints.v`.

- [ ] **Step 6: The extension count (ledger row C4)**

Copy `probe_c4_extcount.v` from `Section C4` to `perm_ext_count0`, dropping the
`About` lines, the `Print Assumptions` block and the four `Example`s. Prefix
every name, because these are exported and the file-wide `psl211_` rule applies:
`psl211_prescribed_of_set`, `psl211_perm_ext_count_ord`,
`psl211_perm_ext_count0_ord`, `psl211_perm_ext_count`,
`psl211_perm_ext_count0`. No name collides (a tree-wide grep for
`perm_ext_count` and `prescribed_of_set` returns nothing).

```coq
Section psl211_ext_count.
Variable N : nat.

Lemma psl211_prescribed_of_set (K : {set 'I_N}) (t : 'I_N -> 'I_N) :
  [set ph : {perm 'I_N} | [forall k in K, ph k == t k]]
  = prescribed (@enum_val _ K) (fun i => t (@enum_val _ K i)).

Lemma psl211_perm_ext_count_ord (K : {set 'I_N}) (t : 'I_N -> 'I_N) :
  {in K &, injective t} ->
  #|[set ph : {perm 'I_N} | [forall k in K, ph k == t k]]| = (N - #|K|)`!.

Lemma psl211_perm_ext_count0_ord (K : {set 'I_N}) (t : 'I_N -> 'I_N) :
  ~ {in K &, injective t} ->
  #|[set ph : {perm 'I_N} | [forall k in K, ph k == t k]]| = 0.

End psl211_ext_count.

Lemma psl211_perm_ext_count (K : {set 'I_6}) (t : 'I_6 -> 'I_6) :
  {in K &, injective t} ->
  #|[set ph : {perm 'I_6} | [forall k in K, ph k == t k]]| = (6 - #|K|)`!.
Proof. exact: (@psl211_perm_ext_count_ord 6 K t). Qed.

Lemma psl211_perm_ext_count0 (K : {set 'I_6}) (t : 'I_6 -> 'I_6) :
  ~ {in K &, injective t} ->
  #|[set ph : {perm 'I_6} | [forall k in K, ph k == t k]]| = 0.
Proof. exact: (@psl211_perm_ext_count0_ord 6 K t). Qed.
```

The count itself must not be reproved. `card_prescribed`
(`lib/perm_uniform.v:117`) is exactly

```coq
Lemma card_prescribed (k : nat) (s v : 'I_k -> 'I_N) :
  injective s -> injective v -> (k <= N)%N ->
  #|prescribed s v| = (N - k)`!.
```

and its section's `N_pos` hypothesis is pruned by `Qed`, so no positivity
obligation reaches a caller. The restatement is genuinely needed because
`prescribed` takes two index families and not a set; the bridge is three lines
(`s := @enum_val _ K` injective by `enum_val_inj`, `v := fun i => t (enum_val
i)` injective from the in-injectivity premise with `enum_valP`, and
`#|K| <= N` from `max_card` rewritten by `card_ord`). The zero case is new;
`perm_uniform.v`'s `perm_cond_zero` is a probability statement and not this.

Add the import `From pgg_smc Require Import perm_uniform.` and record its cost
in the file header: citing `card_prescribed` pulls in `all_algebra`, `boolp`,
`reals` and infotheo's `fdist`, `proba`, `jfdist_cond` and `entropy`, measured
at 4.31 s against 0.52 s for a version that used only `perm_exchange`. Note also
that a brute-force `vm_compute` cross-check of the count is not available:
`fun_of_perm` is `HB.lock`ed, `enum {perm 'I_3}` did not reduce in two attempts
of 120 s and 90 s, and `size (enum {perm 'I_6})` was killed at 5019 MB after
2 min 44 s.

Statement comments:

```coq
(** psl211_perm_ext_count — a labelling of the six codes of one colour that is
    prescribed on a set K of ranks, injectively, extends in exactly
    (6 - |K|)! ways.  This is the labelling factor of the deal count: a
    reading pins the labelling on the ranks the coalition sees and leaves the
    rest free, and the factor depends on the size of K alone, so it is the
    same on both sides of the class comparison. *)

(** psl211_perm_ext_count0 — a prescription that is not injective on K has no
    extension at all.  This is the colour-inconsistent branch of the deal
    count: a reading that names one code at two ranks is produced by no deal
    of either class. *)
```

- [ ] **Step 7: The coalition's reading and the positions it covers**

The view definition is copied from `probe_c2_bridge.v:32-42`, docstring through
the closing `else ord0].`, and one reading lemma from
`probe_c5_sanity.v:48-55`. The probe's other reading lemma,
`psl211_alldecks_read_position` at `:37-46`, mentions `static_coalition_obs`
and lands in T5 Step 2 instead:

```coq
Local Notation seatT :=
  ('I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1).
Local Notation cardT :=
  ('I_(pgg_N' (mp_M (instance_profile psl211_algebra))).+1).

(** psl211_alldecks_view C x g — the coalition's reading of the all-decks
    deck, written on the instance's own side: seat i in C reads the card the
    laid deck puts at the shuffle image of i, every other seat reads ord0.
    Every counting argument below is about this function and every security
    statement about the framework's static_coalition_obs; psl211_models.v
    carries one to the other. *)
Definition psl211_alldecks_view (C : {set seatT}) (x : psl211_inputT)
    (g : pgg_gT psl211_M) : {ffun seatT -> cardT} :=
  [ffun i => if i \in C
             then tnth (psl211_alldecks_layout x) (@pgg_rho psl211_M g i)
             else ord0].

(** psl211_alldecks_read_setE — the positions a coalition reads are the image
    of the coalition under the cut, and that image has the coalition's own
    size because a shuffle is a permutation.  The image, not the preimage, is
    the set the block count is taken over, and this equality is the premise
    psl211_pattern_transfer needs at it. *)
Lemma psl211_alldecks_read_setE (C : {set seatT}) (g : pgg_gT psl211_M) :
  #|[set (@pgg_rho psl211_M g i) | i in C]| = #|C|.
Proof. by rewrite card_imset //; exact: perm_inj. Qed.
```

`Local Notation` is safe here and the probes use it in four files. The Plan A
trap it must not be confused with is a `Local Notation` for a table-valued
BFS certificate, which makes a later `done` walk into the table; a notation for
a type has no such body.

Record in the file header, as a fact about the layout rather than as a status
note, that the laid deck does not reduce at any input: the rank enters the
labelling through `inord`, whose `insub` is guarded by the `Qed`-opaque `idP`,
so `vm_compute` stops at

```
match perm (inj_id (A:='I_6))
        (match idP with ReflectT x => Some (Ordinal x) | ReflectF _ => None end)
with Ordinal m _ => m end
```

and every statement about the laid deck is proved symbolically. This is not a
restriction the 136857600-point carrier imposes; it holds at a single fixed
input.

- [ ] **Step 8: The two fiber statements, and the one new proof**

The two statements are copied from `probe_c56_decomposition.v:107-128`, with
their docstrings at `:94-128`, where they were left `Admitted` and where the
headline, the witness and the published row were derived from them to `Qed`.
Their types are therefore pinned by compiled evidence and only the proofs are
new. The copy is verbatim modulo the `cardT` notation: the probe spells the
reading's carrier out as
`{ffun seatT -> 'I_(pgg_N' (mp_M (instance_profile psl211_algebra))).+1}`
and the version below uses this file's own `Local Notation cardT` for it, which
is the same term.

```coq
(** psl211_alldecks_per_cut_count — at one cut, one coalition of at most five
    seats and one reading, the two chiralities have equally many deals
    producing that reading.  The deals of class b producing a reading are
    indexed by the blocks of the class's Steiner system meeting the cut image
    of the coalition in the reading's heart pattern, times one extension count
    for the heart labelling and one for the club labelling; the block counts
    agree between the two systems because both are S(5,6,12) designs and the
    pattern has at most five points, and the two extension counts do not
    depend on the class at all.  This is the per-cut form;
    psl211_alldecks_fiber_transfer is its sum over the group and is the form
    the bridge consumes. *)
Lemma psl211_alldecks_per_cut_count (C : {set seatT}) (g : pgg_gT psl211_M)
    (v : {ffun seatT -> cardT}) :
  (#|C| <= 5)%N ->
  #|[set y : psl211_deal | psl211_alldecks_view C (true, y) g == v]|
  = #|[set y : psl211_deal | psl211_alldecks_view C (false, y) g == v]|.

(** psl211_alldecks_fiber_transfer — the same counts summed over the cuts of
    the group: for every reading of a coalition of at most five seats, the
    deck descriptions and cuts producing it are as many under one chirality as
    under the other.  This is the counting premise the uniform-pair bridge
    consumes, and the only instance-specific input to the published
    independence. *)
Lemma psl211_alldecks_fiber_transfer (C : {set seatT})
    (v : {ffun seatT -> cardT}) :
  (#|C| <= 5)%N ->
  #|[set u : psl211_inputT * pgg_gT psl211_M |
       (u.1.1 == true) && (u.2 \in pgg_G psl211_M)
       && (psl211_alldecks_view C u.1 u.2 == v)]|
  = #|[set u : psl211_inputT * pgg_gT psl211_M |
       (u.1.1 == false) && (u.2 \in pgg_G psl211_M)
       && (psl211_alldecks_view C u.1 u.2 == v)]|.
```

**The route, in numbered steps.** Steps 1, 2, 3, the subset half of step 5, 8,
9 and 10 are **compiled**, in the plan audit's counter-probes
`notes/probes/2026-09-15-psl211-planb/audit-plan/audit_t4_skeleton.v` and
`audit_t4_percut.v`, both rc 0. Steps 5, 6 and 7 have **no compiled support at
all** and carry the whole new mathematics. Step 11 is compiled as a failure and
is the one step with a measured cost. Copy the compiled scripts verbatim; treat
the rest as the implementer's route, and if a step resists, fix that step rather
than changing the two statements above, which are pinned by the decomposition
probe.

For `psl211_alldecks_fiber_transfer` from `psl211_alldecks_per_cut_count`:

1. **Proved outright** as `audit_B1` in `audit_t4_skeleton.v:66-83`. Copy the
   six-line script; neither `card_fiber_sum` nor `card_imset` nor `cardsX` is
   needed, and the class bit is stripped by `reindex_onto`, not by an injection
   lemma. The name `pair_injl` this plan named in its first draft does not
   exist: `Fail Check pair_injl.` succeeds under the full import set and
   `Check pair_inj.` reports the reference not found.

   ```coq
   rewrite -sum1_card.
   rewrite (partition_big (fun u : psl211_inputT * pgg_gT psl211_M => u.2)
                          (fun g => g \in pgg_G psl211_M)) /=; last first.
     by move=> u; rewrite inE => /andP[/andP[_ ->]].
   apply: eq_bigr => g Hg.
   rewrite (reindex_onto (fun y : psl211_deal => ((b, y), g))
                         (fun u : psl211_inputT * pgg_gT psl211_M => u.1.2)) /=;
     last by case=> [[bb y] gg]; rewrite inE /= =>
       /andP[/andP[/andP[/eqP -> _] _] /eqP ->].
   rewrite -sum1_card; apply: eq_bigl => y.
   by rewrite !inE /= !eqxx Hg /= !andbT.
   ```

2. **Proved outright** as `audit_B2` and `audit_fiber_transfer_from_per_cut` in
   `audit_t4_skeleton.v:91-121`: `rewrite !audit_B1`, then
   `apply: eq_bigr => g _; exact: Hcut`. Note what this measured: the summed
   statement follows from the per-cut statement **alone**, and the `#|C| <= 5`
   premise is consumed only in feeding the per-cut count, never in the
   summation.

For `psl211_alldecks_per_cut_count`:

3. Set `P := [set (@pgg_rho psl211_M g i) | i in C]`.
   `psl211_alldecks_read_setE` gives `#|P| = #|C|`, hence `#|P| <= 5` from the
   premise and `0 < #|P|` from `0 < #|C|`. Compiled as `audit_step3` in
   `audit_t4_percut.v:49-50`.
4. Empty coalition first, by `case: (posnP #|C|)`. When `#|C| = 0`, `C = set0`
   by `cards_eq0`, so `psl211_alldecks_view C x g = [ffun _ => ord0]` for every
   `x` by `ffunP`, `ffunE` and `in_set0`; both sides are then `#|[set: psl211_deal]|`
   if `v` is that finite function and `0` otherwise, and `eq_card` closes it
   without touching either table. This case is separate because
   `psl211_pattern_transfer` has `0 < #|C|` as a premise.
5. Read the pattern off the reading (ledger row C5a). Put
   `A := [set (@pgg_rho psl211_M g i) | i in [set i in C | psl211_is_heart (v i)]]`.
   The subset half is compiled as `audit_step5_sub` in `audit_t4_percut.v:52`:
   `by rewrite /A /P imsetS//; apply/subsetP => i; rewrite inE => /andP[]`.
   Note the second half of that script: `A` is the image of a comprehension and
   not of an intersection, so **`subsetIl` does not state the inclusion** and
   the `subsetP` form above is what closes it. The alternative is to restate the
   seat set as `C :&: [set i | psl211_is_heart (v i)]`, after which `subsetIl`
   does apply; pick one spelling and keep it.
   The other half is the pattern equation: for a deal whose hearts sit on the
   block `B`, seat `i \in C` reads a heart exactly when `pgg_rho g i \in B`, so
   `B :&: P == A`. Prove it as a `Local` lemma `ad_pattern_ofE`; it is the
   passage from the per-seat reading to the set-level pattern and it is the one
   step neither row C2 nor row C5 states. **No compiled support.**
6. Colour consistency. Define the two prescriptions the reading forces:
   `th : 'I_6 -> 'I_6` sending the rank in `B` of a position of `A` to the
   heart code `v` reads there, and `tc : 'I_6 -> 'I_6` likewise on the
   complement for `P :\: A`. If `th` is not injective on the corresponding rank
   set, or `tc` is not, the fiber is empty on both sides by
   `psl211_perm_ext_count0`, and `0 = 0` closes the case. Injectivity of `v`
   restricted to `C` is what decides this, and it does not mention the class.
   **No compiled support.**
7. Count at a fixed block line. For a fixed `j : 'I_132` the set of
   `(ph, pc)` producing `v` is the product of the two prescribed sets, so by
   `cardsX`, `psl211_perm_ext_count` twice and step 5's pattern condition,
   its cardinality is `(6 - #|A|)`! * (6 - #|P| + #|A|)`!` when
   `psl211_inter (nth [::] (psl211_class_tbl b) (val j)) P' == A'` holds and `0`
   otherwise, where `P' := map val (enum P)` and `A' := map val (enum A)`.
   State this as a `Local` lemma `ad_fiber_at_row`. **No compiled support, and
   this is where the whole new mathematics sits.** Four things the statement of
   step 7 must get right, each a separate obligation:
   - **State it at the destructured deal**, `(b, (j, pp.1, pp.2))`, never at an
     abstract `y : psl211_deal`. `psl211_alldecks_seq` has a
     `let: (b, (j, ph, pc)) := x in` and only reduces at a destructured input;
     that is the same trap Step 2 records for `ad_seqE` and `ad_entryE`.
   - (a) **`#|K| = #|A|`**, where `K : {set 'I_6}` is the set of heart RANKS the
     coalition pins, the image of `A` under the rank map inside the block. This
     is a `card_imset` along that map, injective on the block because the block
     is an ascending six-list, and it is what turns
     `psl211_perm_ext_count`'s `(6 - #|K|)`!` into the `(6 - #|A|)`!` step 7
     asserts. Without it the two sides carry different factorials and step 11
     cannot close. Name it `ad_heart_rank_card`.
   - (b) **the club decoding.** The reading gives a card code in `'I_12` at a
     club position; the prescription `tc` needs an element of `'I_6`, so the
     decoding `val (v i) - 6` back into `'I_6` must be written and its
     well-formedness proved from `psl211_is_heart (v i) = false`. Name it
     `ad_club_code`.
   - (c) **the injectivity premise.** `psl211_perm_ext_count` demands
     `{in K &, injective t}`. Discharge it from injectivity of `v` on `C`,
     which is the colour-consistent branch of step 6, and note that the
     non-injective branch is where `psl211_perm_ext_count0` is used. Name it
     `ad_prescription_inj`.
8. Sum over the block line. `psl211_alldecks_row` reads the table at `val j`,
   so the deal set splits as
   `\sum_(j : 'I_132) #|[set pp | ...]|` by `partition_big` over
   `fun y : psl211_deal => y.1.1` (`Local` lemma `ad_split_over_row`), and by
   step 7 the summand is a constant times an indicator.
9. Bridge the block-line count to the table count. `psl211_pattern_count tbl C A`
   is `count (fun R => psl211_inter R C == A) tbl` (`psl211_blocks.v:463`) and
   `size (psl211_class_tbl b) = 132` is `ad_class_tbl_size` of Step 2, so
   `#|[set j : 'I_132 | p (nth [::] tbl (val j))]| = count p tbl`
   by `cardE`, `size_filter` and `val_enum_ord`. State it as a `Local` lemma
   `ad_card_index_count`; it is generic in the predicate and in the table.

   Steps 8 and 9 assembled are **compiled** as `audit_step89` in
   `audit_t4_percut.v:85-101`, from `ad_fiber_at_row`, `ad_split_over_row` and
   `ad_card_index_count` as hypotheses. The script is:

   ```coq
   move=> Hsz.
   rewrite ad_split_over_row (eq_bigr _ (fun j _ => ad_fiber_at_row b j)).
   rewrite -big_mkcond /= sum_nat_const.
   congr (_ * _)%N.
   have -> : psl211_pattern_count (psl211_class_tbl b) (map val (enum P))
                                  (map val (enum A))
           = count ptn (psl211_class_tbl b) by [].
   rewrite -(ad_card_index_count ptn Hsz).
   by apply: eq_card => j; rewrite !inE.
   ```

   Two corrections this measured. The lemma that fires on the constant-summand
   sum is **`sum_nat_const`**, not `big_distrl`, `bigID` or `big_const`. And
   the goal after `sum_nat_const` still carries `psl211_pattern_count` rather
   than `count`, so the delta step written out above is needed; it closes
   `by []` but it does not happen on its own.
10. Transfer the table count across the classes. `psl211_pattern_countE`
    (`psl211_orbit.v:998`, premises `all psl211_asc6 tbl` and `uniq tbl`,
    supplied by `psl211_tbl_ok_asc6 psl211_tbl_ok_mirrorT` /
    `..._hexadT` and `psl211_mirror_tbl_uniq` / `psl211_hexad_tbl_uniq`)
    rewrites each finset block count into the table count, and
    `psl211_pattern_transfer` (`psl211_orbit.v:1118`) equates the two finset
    counts at `P` and `A`. Its three premises are `0 < #|P|`, `#|P| <= 5` and
    `A \subset P`, all at `P` and none at `C`; the two cardinality premises are
    transported from `C` by `card_imset (perm_inj _)` (step 3).
    **Compiled twice.** `audit-soundness/audit_c2_tcast.v:35-45`
    (`audit_transfer_at_P`) does it at `C : {set 'I_12}`, and
    `audit-plan/audit_t4_skeleton.v:47-59` (`audit_A1`) does it at
    `C : {set seatT}`, which is the type this route actually has; the same file
    proves `seatT = 'I_12`, `cardT = 'I_12` and `(C : {set seatT}) = C :>
    {set 'I_12}`, each `by []`. The whole of step 10 is compiled as
    `audit_step10` in `audit_t4_percut.v:106-119`:
    `psl211_pattern_countE` **backwards** at both tables with its four premises,
    then `-/psl211_mirror_blocks -/psl211_hexad_blocks`, then
    `psl211_pattern_transfer`. This route never needs `list_to_setK`, which is
    `Local` at `psl211_orbit.v:809` and therefore unavailable.
11. Multiply back. The two labelling factors of step 7 are identical on both
    sides because they depend on `#|A|` and `#|P|` alone, so the class equality
    of step 10 gives the whole equality.

    **This step has a measured cost and a measured failure.** Written as three
    rewrites followed by `exact: erefl`, with the two table-size hypotheses
    `size psl211_mirror_tbl = 132` and `size psl211_hexad_tbl = 132` sitting in
    the context, it was **killed twice, at 280 s and at 420 s, one rocqworker at
    3.3 GB** (`audit_t4_percut.v:121-137`, left in the file commented out with
    its measurement). Steps 8, 9 and 10 in the same file compile in seconds, so
    the cost is in this last step alone. This is the repository's own
    `done`-walks-the-table hazard, the same one Plan A recorded for a `Local
    Notation` over a BFS certificate. Two rules follow: discharge or `clear` the
    table-size hypotheses before the final rewrite, so that nothing table-valued
    is in scope when the goal is closed; and end with an explicit `exact:`,
    never with `by` or `done`, which are free to search the context.

Named mathcomp and repository lemmas the route expects: `partition_big`,
`reindex_onto`, `sum1_card`, `sum_nat_const`, `big_mkcond`, `eq_bigr`,
`eq_bigl`, `eq_card`, `card_imset`, `perm_inj`, `imsetS`, `subsetP`,
`cardsX`, `cardE`,
`size_filter`, `val_enum_ord`, `posnP`, `cards_eq0`, `ffunP`, `ffunE`,
`in_set0`, `congr`; and `psl211_perm_ext_count`, `psl211_perm_ext_count0`,
`psl211_pattern_count`, `psl211_pattern_countE`, `psl211_pattern_transfer`,
`psl211_mirror_tbl_uniq`, `psl211_hexad_tbl_uniq`, `psl211_tbl_ok_asc6`,
`psl211_tbl_ok_mirrorT`, `psl211_tbl_ok_hexadT`, `psl211_is_heart`,
`psl211_heart_set`, `psl211_list_to_set`.

**Budget and fallback.** Steps 1, 2, 3, 5-subset, 8, 9 and 10 are done and cost
only transcription. What is left is steps 5-pattern, 6 and 7 with their three
named sub-lemmas `ad_heart_rank_card`, `ad_club_code` and
`ad_prescription_inj`, plus `ad_split_over_row`, `ad_card_index_count` and the
assembly of step 11 under the two rules above. Estimate 250 to 450 lines of
proof script with eight or nine `Local` helpers, and budget one working day,
of which step 7 is most of it. If step 7 stalls, split this task into two
commits at the natural seam: commit T4a with everything through step 7 plus
`psl211_alldecks_per_cut_count` proved, and commit T4b with the summation and
`psl211_alldecks_fiber_transfer`. Both commits compile, because
`psl211_alldecks_per_cut_count` is a self-contained statement and nothing above
`psl211_alldecks.v` is written yet. The `audit-plan/` counter-probes state the
route's helpers as section `Hypothesis`es and derive the assembly from them, so
they double as a scaffold: land the helpers one at a time against that file
before moving them into `psl211_alldecks.v`.

**What is already known about these statements, so that effort is not spent
re-deciding it.** L24 is true at the real tables: `audit_alldecks.py` checks the
per-block closed form against a genuine 720 by 720 brute force over both
labelling groups, then checks the aggregated fiber counts across the two classes
exhaustively at coalition sizes 1, 2 and 3 and on sampled coalitions at sizes 4
and 5, each class totalling 132 * 720 * 720. It is sharp at six. No count below
six points can separate the two classes, because both tables are S(5,6,12)
systems, so a mutation that changes a count will not fail; the mutation that
does fail is membership of a particular six-set, `[:: 0; 1; 2; 3; 4; 10]`, which
is a mirror block and not a hexad. And no `vm_compute` sanity check over the
deal carrier exists: `enum 'I_6` returns a stuck term in 0.036 s and
`size (enum {perm 'I_6})` was killed at 5019 MB after 2 min 44 s.

- [ ] **Step 9: Register, compile, check**

```bash
rocq makefile -f _CoqProject -o Makefile.rocq
make -j1 instances/psl211/psl211_alldecks.vo 2>&1 | tail -3 && echo BUILD-OK
```

Expected cost: about 20 s, peak about 2 GB. The three B probes measured 4.33 s,
4.22 s and 4.07 s each with 1.59 GB of shared import cost, the C4 probe 3.60 s
with `perm_uniform` included, and the new proofs are symbolic in the block line
and never enumerate the 136857600-point carrier. A compile above 60 s or a peak
above 4 GB means something in the new proof is forcing a table literal; look
first for a `rewrite` or `case` that opens `psl211_class_tbl`.

```bash
printf 'From pgg_smc Require Import psl211_alldecks.\nPrint Assumptions psl211_alldecks_uniq.\nPrint Assumptions psl211_alldecks_heart_setE.\nPrint Assumptions psl211_alldecks_subset_valid.\nPrint Assumptions psl211_alldecks_classE.\nPrint Assumptions psl211_alldecks_valid.\nPrint Assumptions psl211_alldecks_ts_valid.\nPrint Assumptions psl211_alldecks_gt0.\nPrint Assumptions psl211_alldecks_cardE.\nPrint Assumptions psl211_alldecks_terminates.\nPrint Assumptions psl211_alldecks_recon.\nPrint Assumptions psl211_perm_ext_count.\nPrint Assumptions psl211_perm_ext_count0.\nPrint Assumptions psl211_alldecks_read_setE.\nPrint Assumptions psl211_alldecks_per_cut_count.\nPrint Assumptions psl211_alldecks_fiber_transfer.\n' | rocq repl -q $PSL211_RFLAGS
```

Expected: **Closed for the thirteen already measured, and Closed for the two new
counting theorems if their proofs use nothing classical.** The thirteen are read
back from `log-probe_b1_uniq.txt`, `log-probe_b2_heart.txt`,
`log-probe_b3_class.txt`, `log-probe_c4_extcount.txt`, `log-probe_c5_sanity.txt`
and `log-probe_c56_decomposition.txt`, plus `psl211_alldecks_recon`,
`psl211_alldecks_gt0` and `psl211_alldecks_cardE` measured by the plan audit.
The two that are not measured are exactly `psl211_alldecks_per_cut_count` and
`psl211_alldecks_fiber_transfer`, which are `Admitted` in the decomposition
probe at `:112` and `:128`; every lemma the route above uses is itself Closed,
so a boolp axiom appearing on either of them means a classical step crept into
the new proof. Nothing in this file touches
`funext` and nothing sits in a section with a `realType` variable, so a boolp
axiom appearing here is a defect, not a floor. Also confirm the file carries
zero `Admitted`, zero `Axiom`, zero `Hypothesis` and zero `Parameter`:

```bash
grep -cE '^\s*(Admitted|Axiom|Hypothesis|Parameter)\b' instances/psl211/psl211_alldecks.v
```

Expected: `0`.

- [ ] **Step 10: Commit**

```bash
git add _CoqProject instances/psl211/psl211_alldecks.v
git commit -m "feat(psl211): the all-decks layout, its validity, and equal deal counts across the two chiralities"
```

---

### Task 5: `instances/psl211/psl211_models.v`

**Files:**
- Create: `instances/psl211/psl211_models.v`
- Modify: `_CoqProject` (one line, after `instances/psl211/psl211_alldecks.v`)
- Source: `planb_alldecks_defs.v:108-118` (the law and the secret, and nothing
  above `:108`, which is T4's);
  `probe_c1_adapter.v` (the adapter and the cut law);
  `probe_c2_bridge.v:43-100` (the four identifications);
  `probe_c5_sanity.v:37-46` (`psl211_alldecks_read_position`, docstring through
  its `Qed.`);
  `probe_d1_observed.v` (the observed execution, the executed content reader,
  the fuel and row equations, the secret-is-recovered lemma);
  `probe_c56_decomposition.v:134-185` (the headline, the static form, the family
  and the witness, docstring of `psl211_alldecks_view_indep` through the closing
  paren of `psl211_exact_witness`);
  `instances/pgl27/pgl27_models.v:355-376` (the shape of the corollary)

- [ ] **Step 1: The law, the secret and the sample adapter (ledger row C1)**

```coq
Definition psl211_alldecksP (R : realType)
  : R.-fdist (psl211_inputT * pgg_gT psl211_M)%type :=
  (`U psl211_alldecks_gt0) `x (`U psl211_G_pos).

Definition psl211_alldecks_secret (R : realType)
  : {RV (psl211_alldecksP R) -> bool} := fun u => u.1.1.

Definition psl211_alldecks_sample (R : realType)
  : SampleAdapter R (instance_exec psl211_alldecks_params) :=
  @MkSampleAdapter R (instance_profile psl211_algebra)
    (instance_exec psl211_alldecks_params)
    ((psl211_inputT * pgg_gT psl211_M)%type : finType)
    (psl211_alldecksP R) fst snd.
```

with `psl211_alldecks_sampleP_E`, `psl211_alldecks_sample_argE`,
`psl211_alldecks_sample_cutE` and `psl211_alldecks_cut_distE` copied verbatim
from `probe_c1_adapter.v`. The file needs `Import GRing.Theory` and
`Local Open Scope ring_scope` for `psl211_alldecks_cut_distE`'s proof, as the
probe has.

Three spellings are load-bearing.

- `MkSampleAdapter` has four fields, `sa_sampleT`, `sa_sampleP`, `sa_arg`,
  `sa_cut` (audit N8); the law is the second argument and must be written.
- Under this repository's `Set Implicit Arguments` with
  `Unset Strict Implicit`, the projections `sa_arg` and `sa_cut` take the
  adapter IMPLICITLY, because it is inferable from the sample point that
  follows: `sa_arg sa u` does not elaborate and `sa.(sa_arg) u` does.
  `sa_sampleP sa` does elaborate, because there the adapter appears only in the
  return type. Every proof script below uses the dot form for the first two.
- `erefl : ep_inputT (instance_exec psl211_alldecks_params) = psl211_inputT`
  holds, so the two coordinates of a sample point are the plug's own input
  carrier and the group with no coercion between them. Keep that `Check` as a
  landed `Lemma psl211_alldecks_inputTE ... Proof. by []. Qed.` so that the
  agreement is a theorem rather than a comment.

Record in the file header the one naming departure: the law is
`psl211_alldecksP` and not `psl211_alldecks_sampleP`. The repository's only
other instance with a second dealing mode writes the whole family with the mode
prefix and keeps the `_sampleP` suffix (`s5_models.v:106 s5_rand_sampleP`), so
`psl211_alldecks_sampleP` is the conventional spelling; `psl211_alldecksP` is
used because it is the name the probes compiled and the name
`probe_c56_decomposition.v` applies the bridge under. Audit N31 allows either
provided the departure is recorded here.

Statement comment for the law, naming the dealer:

```coq
(** psl211_alldecksP — the law of the all-decks model: the deck description
    uniform over all of them, which is one of the two chiralities, one of the
    132 block lines of that chirality's Steiner system for the six heart
    positions, one of the 720 labellings of the heart codes and one of the 720
    labellings of the club codes; the cut uniform over the 660 elements of the
    group; the two independent.  Every statement the row publishes is an
    average over decks and cuts under this law, per coalition and at a single
    observation.  It neither implies nor is implied by the fixed-dealer colour
    result of psl211_secrecy.v, which is about a different dealer and a
    different observer. *)
```

- [ ] **Step 2: The identification of the coalition's reading (ledger row C2)**

Copy `probe_c2_bridge.v:43-100` verbatim, less its `Print Assumptions` block
and its two `Fail Definition`s, and add the framework-side reading at one seat
from `probe_c5_sanity.v:37-46`, which is that lemma's docstring through its
`Qed.`. The four statements, with
`psl211_alldecks_view` now coming from `psl211_alldecks.v`:

```coq
Lemma psl211_alldecks_static_obsE (C : {set seatT}) (x : psl211_inputT)
    (g : pgg_gT psl211_M) (i : seatT) :
  @static_coalition_obs psl211_algebra psl211_alldecks_params C x g i
  = if i \in C
    then tnth (psl211_alldecks_layout x) (@pgg_rho psl211_M g i)
    else ord0.
Proof.
rewrite static_coalition_obsE.
by case: ifP => // _; rewrite /= tnth_ord_tuple.
Qed.

Lemma psl211_alldecks_static_obs_viewE (C : {set seatT}) (x : psl211_inputT)
    (g : pgg_gT psl211_M) :
  @static_coalition_obs psl211_algebra psl211_alldecks_params C x g
  = psl211_alldecks_view C x g.

Lemma psl211_alldecks_static_obs_funE (C : {set seatT}) (x : psl211_inputT) :
  @static_coalition_obs psl211_algebra psl211_alldecks_params C x
  = psl211_alldecks_view C x.

Lemma psl211_alldecks_exact_viewE (C : {set seatT}) :
  (fun u : psl211_inputT * pgg_gT psl211_M =>
     @static_coalition_obs psl211_algebra psl211_alldecks_params C u.1 u.2)
  = (fun u : psl211_inputT * pgg_gT psl211_M => psl211_alldecks_view C u.1 u.2).

Lemma psl211_alldecks_read_position (C : {set seatT}) (x : psl211_inputT)
    (g : pgg_gT psl211_M) (i : seatT) :
  i \in C ->
  @static_coalition_obs psl211_algebra psl211_alldecks_params C x g i
  = tnth (psl211_alldecks_layout x) (@pgg_rho psl211_M g i).
Proof. by move=> Hi; rewrite psl211_alldecks_static_obsE Hi. Qed.
```

Two things vanish in the first proof and the file header records that they do.
The framework's right-hand side in supplied mode is
`ex_content_obs E x (g, tnth (pi_starts (mp_PI (instance_profile A))) i)`,
which unfolds to
`tnth (tcast (pga_share_card psl211_algebra) (psl211_alldecks_layout x))
      (pgg_rho g (tnth (pi_starts _) i))`.
The share cast disappears by conversion, because the scheme's share count and
the algebra's card count are both twelve; and `tnth (pi_starts _) i = i` is one
`tnth_ord_tuple` rewrite, because this instance seats its players at
`ord_tuple 12`. The default outside `C` is `ord0`, the same as in the dealt
mode (audit N2). The `/=` before `tnth_ord_tuple` is needed and is what the
pgl27 script at `pgl27_rows.v:142-150` does not have.

- [ ] **Step 3: The observed execution**

```coq
Definition psl211_alldecks_endpoints
  : instance_endpoints_stmt psl211_alldecks_params :=
  @supplied_endpointsE psl211_algebra psl211_inputT psl211_alldecks_layout
    psl211_alldecks_expected psl211_fuel psl211_profile_endpoints.

Definition psl211_alldecks_observed : OE.ObservedExecution :=
  instance_observed psl211_alldecks_terminates psl211_alldecks_endpoints
    psl211_alldecks_recon.
```

Every argument of `supplied_endpointsE` is implicit (audit N5), so the
definition must carry its `instance_endpoints_stmt ...` ascription; without it
nothing determines `layout`. `supplied_endpointsE` itself costs the run no
reduction: it is `Proof. by move=> H x w0; exact: (H _ _ x w0). Qed.` at
`pgg_instance.v:772`. The 900 seconds belong to `psl211_profile_endpoints`
(audit N6), which this file merely names.

Add the packaged recovery theorem, in the shape of `pgl27_exec.v:423-428`:

```coq
(** psl211_alldecks_observed_recovers — the packaged all-decks run decodes to
    the chirality its input names, at every deck description and every cut in
    the group.  This is the correctness half of the row: the value the
    coalition is proved to learn nothing about is the value the protocol
    actually reconstructs. *)
Theorem psl211_alldecks_observed_recovers (x : psl211_inputT)
    (w0 : pgg_gT psl211_M) (Gw0 : w0 \in pgg_G psl211_M) : ... = x.1.
Proof. exact: (OE.oe_run_recovers psl211_alldecks_observed x w0 Gw0). Qed.
```

The elided left-hand side is `pgl27_exec.v:423-427`'s with `pgl27_observed`
replaced by `psl211_alldecks_observed`, `s` by `x` and the recovered value by
`x.1`; copy it from there, since it is the framework's own spelling and not an
instance choice.

- [ ] **Step 4: The executed content reader (ledger row D1)**

Copy `probe_d1_observed.v`'s reader block verbatim: `psl211_content_of`,
`psl211_exec_content_trace`, `psl211_alldecks_fuelE`, `psl211_exec_rowE`,
`psl211_content_trace`, `psl211_content_traceE`, `psl211_content_ofE`, and the
two executed-view identifications `psl211_alldecks_exec_viewE` and
`psl211_alldecks_exec_view_instE`, with the section hypothesis `Hprof` deleted
and `psl211_alldecks_endpoints` of Step 3 used directly.

`content_of` lives in `instances/pgl27/pgl27_trace.v` and nothing shared
exports it. **Decision: restate it here as `psl211_content_of` rather than move
it.** Moving it would edit `pgl27_trace.v`, which is not in this plan's scope
and whose dependents include the pgl27 facade and the manifest; restating it is
five lines and keeps the plan's diff inside the psl211 cone and the manifest.
Its shape is pinned in both directions: `psl211_content_ofE` proves the reader
skips one message and takes the head of the hand, and the probe's refuted
mutation shows a reader taking the head of the row reads the wrong message.

Two proof-level facts must be carried as source comments, because each cost a
kill.

- `psl211_exec_rowE` must be stated against `exec_run` and not against a fuel
  literal. The literal version, proved by `exact: erefl`, hangs at `Qed`,
  because the kernel unfolds `run_interp` to decide it and that is the
  561-second reduction. The fuel equation is stated separately as
  `psl211_alldecks_fuelE : ep_fuel eP = psl211_fuel`, where it is instant.
- In `psl211_content_traceE`, an unscoped `rewrite ffunE` reaches inside the
  finfun body and evaluates the interpreter; the `[LHS]`/`[RHS]` scoped form
  fires immediately.

More generally: only a mutation that fails while the STATEMENT is elaborated is
safe at this instance. Two mutations differing from the truth only inside a run
fact were written during the probe and each ran past 110 seconds with no answer
before being killed.

- [ ] **Step 5: L24 at the probability layer, the family and the witness
  (ledger rows C6, C7, C7a)**

Copy `probe_c56_decomposition.v:134-185` verbatim, with the two supports now
real:

```coq
Lemma psl211_alldecks_view_indep (R : realType) (C : {set seatT}) :
  (#|C| <= 5)%N ->
  psl211_alldecksP R |= (fun u => psl211_alldecks_view C u.1 u.2)
                    _|_ psl211_alldecks_secret R.
Proof.
move=> HC.
apply: (@uniform_pair_indep_of_fibers R psl211_inputT (pgg_gT psl211_M) _
          (fun x : psl211_inputT => x.1) (pgg_G psl211_M) psl211_G_pos
          psl211_alldecks_gt0 (psl211_alldecks_view C)).
by move=> v; exact: psl211_alldecks_fiber_transfer.
Qed.

Lemma psl211_alldecks_static_indep (R : realType) (C : {set seatT}) :
  (#|C| <= 5)%N ->
  psl211_alldecksP R
  |= (fun u : psl211_inputT * pgg_gT psl211_M =>
        @static_coalition_obs psl211_algebra psl211_alldecks_params C u.1 u.2)
  _|_ psl211_alldecks_secret R.
Proof.
move=> HC; rewrite psl211_alldecks_exact_viewE.
exact: psl211_alldecks_view_indep.
Qed.

Definition psl211_exact_family : AnalysisModelFamily psl211_alldecks_observed :=
  @MkAnalysisModelFamily psl211_alldecks_observed (fun _ => unit)
    (fun R _ => psl211_alldecks_sample R).

Definition psl211_exact_witness (R : realType) (idx : unit)
  : ExactWitness (amf_sample psl211_exact_family R idx) :=
  @MkExactWitness R psl211_algebra psl211_alldecks_params
    (amf_sample psl211_exact_family R idx) bool (psl211_alldecks_secret R)
    (fun C HC =>
       let H5 : (#|C| <= 5)%N := HC in
       (eq_ind_r
          (fun v => psl211_alldecksP R |= v _|_ psl211_alldecks_secret R)
          (psl211_alldecks_view_indep R H5)
          (psl211_alldecks_exact_viewE C))).

Lemma psl211_alldecks_secret_expectedE (R : realType)
    (u : psl211_inputT * pgg_gT psl211_M) :
  psl211_alldecks_secret R u
  = ex_expected psl211_alldecks_params ((psl211_alldecks_sample R).(sa_arg) u).
Proof. by []. Qed.
```

The `let H5 : (#|C| <= 5)%N := HC` line is where the threshold check bites: the
field's premise is `(#|C| < profile_k (instance_profile psl211_algebra))%N`,
the threshold is six by `psl211_profile_kE`, and the coercion is by conversion.
The headline restated at `#|C| <= 6` does not fill the field.

`psl211_alldecks_secret_expectedE` is the row that keeps the arm non-empty.
`ExactWitness` (`pgg_tableau.v:114-123`) has no field relating `ew_secret` to
`ex_expected`, so `ew_secretT := unit, ew_secret := fun _ => tt` would typecheck
and make `ExactProp` say nothing. pgl27 needs no such lemma because there
`sa_arg` IS the secret; here `sa_arg` is a whole deck description, so the
lemma is what ties the published independence to the chirality the protocol
reconstructs. Its statement comment must say that.

- [ ] **Step 6: The corollary in the pgl27 shape**

```coq
(** psl211_alldecks_exec_exact_view_indep — at five seats the executed
    coalition observation of the all-decks model and the chirality have a
    product joint distribution, for a coalition of at most five of the twelve
    seats.  This is psl211_alldecks_view_indep transported to the executed
    sample layer, so the independence is a statement about what the
    interpreter's messages contain and not only about the instance-side
    reading. *)
Corollary psl211_alldecks_exec_exact_view_indep (R : realType)
    (C : {set seatT}) :
  (#|C| <= 5)%N ->
  fdistmap (fun u => (psl211_alldecks_view C u.1 u.2,
                      psl211_alldecks_secret R u))
           (psl211_alldecksP R)
  = ((@sa_coalition_dist R (instance_profile psl211_algebra)
        (instance_exec psl211_alldecks_params) (psl211_alldecks_sample R) 0 C)
     `x (fdistmap (psl211_alldecks_secret R) (psl211_alldecksP R)))%fdist.
```

The corollary rests on a second lemma, which T6 aliases as
`PSL211Analysis.exact_coalition_distE` and the manifest pins by a spelled type,
so it must be written out here and not left as a step of a proof. No probe
declares it; its statement is `pgl27_models.v:355-361` at this instance:

```coq
(** psl211_alldecks_coalition_distE — the executed coalition distribution of
    the all-decks model is the pushforward of the model's own law along the
    instance-side reading.  This is the equation that makes a counting result
    proved about the laid deck a result about what the interpreter's messages
    carry, so every independence statement below is attached to the executed
    observer and not only to the static one. *)
Lemma psl211_alldecks_coalition_distE (R : realType) (C : {set seatT}) :
  @sa_coalition_dist R (instance_profile psl211_algebra)
    (instance_exec psl211_alldecks_params) (psl211_alldecks_sample R) 0 C
  = fdistmap (fun u => psl211_alldecks_view C u.1 u.2) (psl211_alldecksP R).
Proof.
rewrite /sa_coalition_dist; congr fdistmap.
by apply: boolp.funext => u; exact: psl211_alldecks_exec_view_instE.
Qed.
```

Then the corollary closes, from `pgl27_models.v:370-376`, by
`move=> HC; rewrite psl211_alldecks_coalition_distE` and
`exact: (inde_dist_of_RV2 (psl211_alldecks_view_indep R HC))`.

**Every `*E` constant landed in this file must be stated against `exec_run`,
never against a fuel literal or a second spelling of a run fact.**
`psl211_exec_rowE` already is, and `psl211_alldecks_fuelE` is the separate
statement that lets it be. The reason is T6: the manifest pins each of these
through its alias by a spelled type under a `Timeout 60`, and an alias has no
statement of its own to restate, so a constant stated against a fuel literal
cannot be repaired at T6. It has to be repaired here, and T5 re-run.

- [ ] **Step 7: Register, compile, check**

```bash
rocq makefile -f _CoqProject -o Makefile.rocq
make -j1 instances/psl211/psl211_models.vo 2>&1 | tail -3 && echo BUILD-OK
```

Expected cost: 20 to 30 s, peak about 2 GB. The four probes that this file
merges measured 4.29 s, 4.20 s, 5.61 s and 7.12 s, each carrying about 1.6 GB
of shared import cost that is paid once here.

```bash
printf 'From pgg_smc Require Import psl211_models.\nPrint Assumptions psl211_alldecks_static_obsE.\nPrint Assumptions psl211_alldecks_static_obs_viewE.\nPrint Assumptions psl211_alldecks_static_obs_funE.\nPrint Assumptions psl211_alldecks_read_position.\nPrint Assumptions psl211_alldecks_endpoints.\nPrint Assumptions psl211_alldecks_observed.\nPrint Assumptions psl211_alldecks_observed_recovers.\nPrint Assumptions psl211_exec_rowE.\nPrint Assumptions psl211_alldecks_fuelE.\nPrint Assumptions psl211_content_ofE.\nPrint Assumptions psl211_alldecks_secret_expectedE.\nPrint Assumptions psl211_alldecks_exact_viewE.\nPrint Assumptions psl211_alldecks_coalition_distE.\nPrint Assumptions psl211_content_traceE.\nPrint Assumptions psl211_alldecks_view_indep.\nPrint Assumptions psl211_alldecks_static_indep.\nPrint Assumptions psl211_exact_witness.\nPrint Assumptions psl211_alldecks_exec_exact_view_indep.\n' | rocq repl -q $PSL211_RFLAGS
```

Expected, in three groups, each read off a probe log rather than predicted.

**Closed under the global context**, measured in `log-probe_c2_bridge.txt` and
`log-probe_d1_observed.txt`: `psl211_alldecks_static_obsE`,
`psl211_alldecks_static_obs_viewE`, `psl211_alldecks_read_position`,
`psl211_alldecks_endpoints`, `psl211_alldecks_observed`,
`psl211_alldecks_observed_recovers`, `psl211_exec_rowE`,
`psl211_alldecks_fuelE`, `psl211_content_ofE`.

**Exactly `propositional_extensionality` and `functional_extensionality_dep`,
two axioms and not three**: `psl211_alldecks_static_obs_funE` and
`psl211_alldecks_exact_viewE`. That is what `boolp.funext` alone carries, and
`log-probe_c2_bridge.txt` measures it for both. Do not expect the full trio
here: `pgl27_exact_viewE` does measure the full trio, so the pgl27 analogy
fails on this line, and a result of two axioms is the correct one.

**Exactly the boolp trio**: `psl211_alldecks_secret_expectedE`,
`psl211_content_traceE`, `psl211_alldecks_coalition_distE`,
`psl211_alldecks_view_indep`, `psl211_alldecks_static_indep`,
`psl211_exact_witness`, `psl211_alldecks_exec_exact_view_indep`.
`psl211_alldecks_secret_expectedE` is in this group and not in the first, even
though it closes `by []`: `log-probe_d1_observed.txt` measures the trio for it,
and the cause is structural, since its statement mentions
`psl211_alldecks_secret R`, hence `psl211_alldecksP`, hence `` `U `` and
`fdist_uniform_supp`. A Closed result on that lemma would be the surprise, not
the trio.

- [ ] **Step 8: Commit**

```bash
git add _CoqProject instances/psl211/psl211_models.v
git commit -m "feat(psl211): the all-decks probability model, its executed readers, and independence of the chirality at five seats"
```

---

### Task 6: the fourth facade, the manifest, the client and the two script tables

**Files:**
- Create: `instances/psl211/psl211_analysis.v`
- Modify: `manifest/pgg_analysis_manifest.v`, `manifest/pgg_analysis_client.v`,
  `scripts/profile_facade_check.sh`, `scripts/profile_facade_check_test.py`
- Modify: `_CoqProject` (one line, after `instances/psl211/psl211_models.v` and
  before `manifest/pgg_analysis_manifest.v`)
- Source: `instances/pgl27/pgl27_analysis.v` (the whole file as the shape, and
  `:304-363` for the retention-check rule);
  `manifest/pgg_analysis_manifest.v:86-144` (documented row 1, the shape of a
  row block), `:660-661` (the row `Definition`), `:738-1010` (the pgl27 checker
  block; five-card is `:1011-1302` and s5 `:1303-1525`), `:562-583` (the
  no-capability alias table), `:1535-1541` (the five pins per row),
  `:1604-1628` (the model-family applications);
  `manifest/pgg_analysis_client.v:6`, `:7`, `:22-32`, `:108`, `:137-153`,
  `:168`; `scripts/profile_facade_check.sh:44-50` (the contract) and `:87-100`
  (the `EXPECTED` dictionary with its docstring);
  `scripts/profile_facade_check_test.py:14-23` (`PROFILES`) and `:24-28`
  (`FACADES`)

This task is ordered before the row file because the manifest defines the
`AnalysisPathRow` and `psl211_rows.v` proves that its program publishes that
row. That is the pgl27 layering exactly: `manifest/pgg_analysis_manifest.v` is
`_CoqProject:187` and `instances/pgl27/pgl27_rows.v` is `:190`, and
`pgl27_row_exact_rowE` lives in the row file. See Decision 6.

This is the largest diff in the plan, and audit N33 and N34 measured it: the
manifest owes a `Require Export` line, a documented row block of about 65
lines, a row `Definition`, a per-instance deterministic checker block of about
270 lines and five pins; the client owes its seven-section Checks, its observer
Checks, a row Check and two header edits; and two scripts enumerate the facades
by hand. Budget half a working day of mechanical work.

- [ ] **Step 1: `instances/psl211/psl211_analysis.v`**

Copy the structure of `pgl27_analysis.v`: the header box with the seven fixed
source sections and the facade contract, the exported type vocabulary
(`Require Export`), the imported instance cone (`Require Import`), then
`Module PSL211Analysis.` with one `Definition` per alias and no proof body
anywhere.

**Every `Definition` starts at column 0, under a banner line.** The section
labels below are presentational, for reading this plan only; they must be
written in the landed file as full-width banner comments in the shape of
`pgl27_analysis.v:89-91`, with the `Definition` on its own line at column 0
under them. The reason is mechanical: `scripts/profile_facade_check.sh:258-259`
matches an alias with `re.compile(r'^Definition\s+...', re.M)`, anchored at
column 0, and its `strip_comments` at `:103-145` blanks a comment **to spaces
at the same position**, preserving column numbers on purpose. An inline
`(* 1 Program *)` prefix therefore leaves the `Definition` indented, the match
fails, and the script reports `NO ALIAS` and exits 1. The landed precedent is
`pgl27_analysis.v:93`, `Definition profile := pgl27_profile.` at column 0.

Section by section, the aliases and their targets:

```coq
(* 1 Program *)      Definition profile := psl211_profile.
(* 2 Execution *)    Definition exec_plug :=
                       instance_exec psl211_alldecks_params.
(* 3 Observers *)    Definition observed := psl211_alldecks_observed.
                     Definition prior := @psl211_alldecksP.
                     Definition content_trace := @psl211_exec_content_trace.
                     Definition static_view := @psl211_alldecks_view.
                     Definition coalition_endpoints :=
                       @exec_coalition_endpoints
                         (instance_profile psl211_algebra)
                         (instance_exec psl211_alldecks_params).
                     Definition seat_endpoint :=
                       @exec_seat_endpoint
                         (instance_profile psl211_algebra)
                         (instance_exec psl211_alldecks_params).
                     Definition secret := @psl211_alldecks_secret.
(* 4 Models *)       Definition exact_sample := @psl211_alldecks_sample.
                     Definition exact_family := psl211_exact_family.
                     Definition cut_distE := @psl211_alldecks_cut_distE.
                     Definition exact_coalition_distE :=
                       @psl211_alldecks_coalition_distE.
(* 5 Correctness *)  Definition observed_recovers :=
                       @psl211_alldecks_observed_recovers.
                     Definition secret_expectedE :=
                       @psl211_alldecks_secret_expectedE.
(* 6 Security *)     Definition content_traceE := @psl211_content_traceE.
                     Definition exact_view_indep :=
                       @psl211_alldecks_exec_exact_view_indep.
                     Definition static_indep := @psl211_alldecks_static_indep.
                     Definition marginal_bound := @psl211_marginal_bound.
                     Definition certificate_bundle :=
                       @psl211_certificate_bundle.
(* 7 Transfer *)     Definition exact_transfer_status : TransferStatus :=
                       StaticExecutedOnly.
```

The section placement follows pgl27 rather than a fresh reading: `observed` and
`prior` are in section 3 at `pgl27_analysis.v:152` and `:148`, and
`content_traceE` is in section 6 at `:244`. T6 Step 2 requires the checker
block to be grouped by the same seven dividers, which are real at
`manifest/pgg_analysis_manifest.v:742`, `:746`, `:756`, `:803`, `:873`, `:900`
and `:990`, so a facade that places an alias in a different section forces its
checker block out of step with the other three.

Section 7 carries no theorem at this instance, so its representative is the
typed status alias, which is what `pgg_analysis_client.v:12-14` says a facade
does in that case. `secret_expectedE` goes in section 5 rather than section 6,
because it is a statement about what the run recovers and not about what a
coalition learns.

**Retention checks: only two aliases may be pinned by value.** Copy
`pgl27_analysis.v:304-363` as the shape and repeat its rule. Its banner at
`:304-316` records that `Check (erefl : alias = landed)` **diverges** on every
alias whose body reaches the interpreter, because the unifier unfolds past the
alias into `exec_participant_trace` and evaluates `run_interp`. Only the two
program-layer aliases are checked by value, `:318-319`; every other alias is
retained by a spelled type ascription, one representative per section, each
under a `Timeout 60`. Writing value-level `erefl` for twenty aliases hangs the
build.

The header's check table, in the shape of `pgl27_analysis.v:26-51`, lists the
minimum items and the alias each maps to, and adds one line the pgl27 table does
not have, naming the dealer:

```
(* The dealer this facade is about is the ALL-DECKS one: the run argument   *)
(* is a whole deck description drawn uniformly, not a bare secret.  The      *)
(* fixed-dealer colour results of psl211_secrecy.v are about a different     *)
(* dealer and a different observer and are not aliased here.                 *)
```

Compile:

```bash
rocq makefile -f _CoqProject -o Makefile.rocq
make -j1 instances/psl211/psl211_analysis.vo 2>&1 | tail -3 && echo BUILD-OK
```

Expected cost: 10 to 15 s. The file has no proof body, so its cost is its
import closure.

- [ ] **Step 2: the manifest's fourth facade**

Six edits to `manifest/pgg_analysis_manifest.v`, each at a line verified
against the file.

1. `:74`, the `Require Export` line, becomes
   `From pgg_smc Require Export pgl27_analysis five_card_analysis s5_analysis psl211_analysis.`
2. After `:560`, which is the last line of the eighth documented row block, a
   ninth block of about 65 lines in the shape of documented row 1 at
   `:86-144`, with the same field table (protocol family and model, profile
   alias, execution alias, observed alias, sample alias, observers,
   distribution-to-observer bridges, bound or certificate, final bridge
   theorem, correctness theorem, model transfer, missing premise, completion
   level, transfer status, assumption status, typed row), the capability table
   with one line per (theorem, distribution, observer, notion), and the level
   justification paragraph. Its four capability lines are: `exact_view_indep` at
   the prior of `exact_sample`, observer `coalition_endpoints` through
   `exact_coalition_distE`, notion exact privacy; `static_indep` at the same
   prior, observer `static_view`, notion exact privacy; `observed_recovers`
   with no distribution, observer the executed endpoint list, notion
   correctness; `secret_expectedE` with no distribution, observer the recovered
   value, notion correctness. Transfer status `StaticExecutedOnly`, because the
   cut this model draws is already the uniform one and no idealized shuffle is
   being compared with a real one. Missing premise: none.
3. After `:736`, the row `Definition`, in the shape of `pgl27_row_exact` at
   `:660-661`. The insertion point is `:736` and not `:730`: `:726-732` is the
   `s5_row_word` docstring, `:733-736` is the last row `Definition`, and
   inserting after `:730` would land inside a comment. The constructor's field
   order, read off `:632-650`, is observed, completion, model, transfer,
   assumptions, and the application below matches `pgl27_row_exact` character
   for character:

```coq
(** The AnalysisPathRow for the twelve-card chirality instance under its
    all-decks dealer: PSL211Analysis.observed paired with the unit-indexed
    exact-uniform family, AnalysisBridged, StaticExecutedOnly,
    BaselineClassicalOnly.  exact_view_indep is proved at this row's own
    sample distribution and observer, which is what reaches AnalysisBridged;
    the cut is already the uniform distribution on the group, so no idealized
    model is compared, and the deck description is drawn uniformly too, which
    is what distinguishes this row from the fixed-dealer colour result the
    same instance also carries. *)
Definition psl211_row_alldecks : AnalysisPathRow :=
  @MkAnalysisPathRow PSL211Analysis.observed AnalysisBridged
    PSL211Analysis.exact_family StaticExecutedOnly BaselineClassicalOnly.
```

4. A per-instance deterministic checker block of about 270 lines after the s5
   one, which ends at `:1525`, in the shapes of the pgl27 block `:738-1010`,
   the five-card block `:1011-1302` and the s5 block `:1303-1525`: one
   `Timeout 60 Check` per alias against its spelled type, grouped by the seven
   `(* --- n Section --- *)` dividers, which sit at `:742`, `:746`, `:756`,
   `:803`, `:873`, `:900` and `:990` in the pgl27 block. And five pins in
   the rows block at `:1535-1541`, matching that block field for field:

```coq
Timeout 60 Check (psl211_row_alldecks : AnalysisPathRow).
Timeout 60 Check (apr_model psl211_row_alldecks
  : AnalysisModelFamily PSL211Analysis.observed).
Timeout 60 Check (erefl : apr_completion psl211_row_alldecks = AnalysisBridged).
Timeout 60 Check
  (erefl : apr_transfer psl211_row_alldecks = StaticExecutedOnly).
Timeout 60 Check
  (erefl : apr_assumptions psl211_row_alldecks = BaselineClassicalOnly).
```

5. `:562-583`, the "Aliases carrying no capability yet" table, gains a
   `PSL211Analysis` row beside the three at `:570`, `:573` and `:577`. Its own
   preamble at `:565-566` says the table exists "so that the checker pins the
   whole facade surface, not only the rows", so a fourth facade with no row
   here leaves part of its surface unpinned. The psl211 aliases with no
   capability line are `seat_endpoint`, `coalition_endpoints`, `prior`,
   `cut_distE`, `content_trace` and `exact_transfer_status`.
6. `:1604-1628`, the "model families exercised at their index types" block,
   gains one application. `psl211_exact_family` is unit-indexed, so the line
   goes beside `:1621-1622`, which is the s5 unit-indexed case:

```coq
Timeout 60 Check (fun R : realType =>
  amf_sample (apr_model psl211_row_alldecks) R tt).
```

The four count-bearing sites in this file are `:6` ("the three instance
facades"), `:7-8` (the three instances named one by one), `:564` ("the three
facades") and `:1527` ("the eight typed rows"). Update those four, and no
others: `:56-72` carries no facade count and no row count.

None of the five row pins forces `apr_observed`, so none is a conversion bomb:
the row `Check` is an ascription, `apr_model` is a projection of a constructor
and reduces by one iota step, and the three `erefl` pins project status fields.
The byte-identical pins for the eight existing rows, all of whose observed
executions carry run facts, compile today at `:1535-1602`.

- [ ] **Step 3: the client**

`manifest/pgg_analysis_client.v` gains, at the place the other three facades
have theirs: one `Check` per section of `PSL211Analysis`, seven of them plus
the typed family and the typed status, in the shape of the pgl27 group at
`:22-32`; the observed-execution value; the remaining distinct observers; and
`Check psl211_row_alldecks.` in the rows block.

Its counts sit on **six** lines, not three, and every one of them must change:

| line | today | after |
|---|---|---|
| `:6` | "all three facades" | four |
| `:7` | "the eight typed rows" | nine |
| `:108` | banner, "the typed status vocabulary and the eight rows" | nine |
| `:140` | "The three facades Require Export" | four |
| `:144-145` | "the three modules keep the short names apart" | four |
| `:168` | "what keeps the three facades' short names distinct" | four |

The banner around `:108` is `:107-109`, and the explanatory block the plan
earlier cited as `:136-152` is `:137-153`.

- [ ] **Step 4: the two script tables**

`scripts/profile_facade_check.sh:87-100`, the `EXPECTED` dictionary, gains

```python
  'psl211_profile':    (None, 'pgg-smc/instances/psl211/psl211_analysis.v',
                        'PSL211Analysis'),
```

`instances/psl211/psl211_profile.v:123` declares `Definition psl211_profile :
MonodromyProfile` at depth zero, the only `Section` in that file being
`witness` at `:56-117` and the definition sitting after `End witness`, so the
script's own contract at `:44-50` makes it an unknown top-level profile and
exits 2 until this line is added. The first tuple element is `None` because
`:124` builds the profile with `@MkMonodromyProfile`; a name there is for the
alias case only, as at `:95`.

`scripts/profile_facade_check_test.py` has **no `SOURCES` table**. Its four
tables are `PROFILES` at `:14-23`, `FACADES` at `:24-28`, `LETS` at `:30-33`
and `OUT_OF_SCOPE` at `:34-37`. Two of them gain a psl211 row:

```python
# PROFILES, :14-23
  'pgg-smc/instances/psl211/psl211_profile.v':
    'Definition psl211_profile : MonodromyProfile := @MkMonodromyProfile a b c.\n',
# FACADES, :24-28
  'pgg-smc/instances/psl211/psl211_analysis.v': ('PSL211Analysis', 'psl211_profile'),
```

Adding the `EXPECTED` entry to the shell script without these two sandbox
declarations turns regression cases C0, C3, C10 and C13 from exit 0 to exit 1,
because an unrepresented profile sets `status = 1` at `:302-307`.

The shell script cannot be exercised in this checkout: it resolves the
repository as `<checkout>/..` expecting the `pgg-smc/` monorepo layout and
prints `fatal: not a git repository` here. Run the python regression instead,
which is self-contained:

```bash
python3 scripts/profile_facade_check_test.py && echo SCRIPTTEST-OK
```

This regression **is** live here: the plan audit ran it and it exits 0 with
18 of 18 PASS, so a failure after the edit is a real failure and not an
environment problem. Do not leave the tables unedited on the ground that the
shell script cannot be run: an unedited `EXPECTED` makes it exit 2 on the real
repository, silently for anyone who does not run it here.

- [ ] **Step 5: Compile and check**

```bash
make -j1 manifest/pgg_analysis_manifest.vo 2>&1 | tail -3 && echo BUILD-OK
make -j1 manifest/pgg_analysis_client.vo 2>&1 | tail -3 && echo BUILD-OK
```

Expected cost: unmeasured. The manifest is the repository's largest checker
file at 1680 lines of `Timeout 60 Check` and this task adds about 340 lines to
it. Budget between two and five minutes and record the measured number in the
as-built section.

If any individual `Check` hits its 60-second timeout, the repair is **not** in
this file. An alias is a `Definition x := y.` and has no statement of its own to
restate; what has to change is the landed constant the alias names, in
`psl211_models.v`, which T5 has already committed. Restate that constant
against `exec_run` rather than against a fuel literal, exactly as
`psl211_exec_rowE` is, and re-run T5 and this task. T5's own rule, that every
`*E` constant is stated against `exec_run` up front, exists to keep this from
happening.

```bash
printf 'From pgg_smc Require Import pgg_analysis_manifest.\nPrint Assumptions psl211_row_alldecks.\n' | rocq repl -q $PSL211_RFLAGS
```

Expected: exactly the boolp trio. This prediction is **by analogy and not by
measurement**: no probe ever built a psl211 `AnalysisPathRow`, and the only
measured `psl211_row_alldecks` is the decomposition probe's `PublishedRow`,
which is a different object that happens to share the name. The landed
precedent is what supports it: `pgl27_row_exact_tableau` and
`pgl27_row_exact_rowE` both measure exactly the trio.

- [ ] **Step 6: Commit**

```bash
git add _CoqProject instances/psl211/psl211_analysis.v \
  manifest/pgg_analysis_manifest.v manifest/pgg_analysis_client.v \
  scripts/profile_facade_check.sh scripts/profile_facade_check_test.py
git commit -m "feat(manifest): the twelve-card chirality facade and its all-decks analysis row"
```

---

### Task 7: `instances/psl211/psl211_rows.v`

**Files:**
- Create: `instances/psl211/psl211_rows.v`
- Modify: `_CoqProject` (one line, after `instances/s5/s5_rows.v`)
- Source: `probe_c56_decomposition.v:191-212` (the prefix at `:191-203` and the
  row at `:205-212`) and `:217-236` (the two prefix variants themselves);
  `probe_e1_row_variants.v:31-55` (the two `paramsE` lemmas and the refusal
  `Fail`, which is all that file contains: it has no prefix definition and
  reaches the variants by `Require`ing `probe_c56_decomposition` at `:25`);
  `instances/pgl27/pgl27_rows.v:117-135` (the prefix), `:260-275` (the row),
  `:316-321` (`rowE`), `:342-363` (the inline-prefix demonstration)

- [ ] **Step 1: Write the file**

```coq
(** psl211_alldecks_prefix — the first three statements of the all-decks row:
    the algebra, the run driven in the supplied-layout mode at fuel 220, and
    the three run facts.  What has been proved at this point is run
    correctness and nothing about a coalition. *)
Definition psl211_alldecks_prefix : Tableau Observed :=
  psl211_algebra
    supplied inputs psl211_inputT
             layout psl211_alldecks_layout
             expecting psl211_alldecks_expected
             fuel psl211_fuel
    execute terminates by psl211_alldecks_terminates
            endpoints by psl211_alldecks_endpoints
            recon by psl211_alldecks_recon.

(** psl211_row_alldecks_tableau — the published row.  What the finished row
    carries about a coalition of fewer than six of the twelve seats is
    independence of the chirality, at every real field, with no numeric bound
    in it; the independence is exact, not small, because both the deck
    description and the cut are drawn uniformly and the two Steiner systems
    are met in the same block patterns by every set of at most five
    positions. *)
Definition psl211_row_alldecks_tableau : PublishedRow :=
  psl211_alldecks_prefix
    sample  psl211_exact_family
    certify ExactIndependence psl211_exact_witness
    |> publish StaticExecutedOnly BaselineClassicalOnly.

(** psl211_row_alldecks_rowE — the row this program publishes is the
    manifest's own row for this instance.  Conversion decides it, so the
    descriptive row and the theorem proved about it cannot drift apart. *)
Lemma psl211_row_alldecks_rowE :
  published_row psl211_row_alldecks_tableau = psl211_row_alldecks.
Proof. by []. Qed.
```

Three surface facts are compiled evidence and the plan fixes each.

- **The row must name its termination lemma.** `execute terminates by
  vm_compute` parses and reaches `Tableau Observed`, and
  `psl211_alldecks_prefix_vm_paramsE` proves the forked prefix drives the same
  run by `[]`, but the analysis model family is typed against the observed
  execution the NAMED prefix builds and is rejected over the forked one with
  `The term "psl211_exact_family" has type "AnalysisModelFamily
  psl211_alldecks_observed" while it is expected to have type "FamPayload
  (tableau_at psl211_alldecks_prefix_vm)"`. This is `pgl27_rows.v:362`
  reproduced at twelve cards. The design note's section 2 sketch wrote
  `terminates by vm_compute`; that line is wrong and this plan's sketch
  corrects it (audit N13).
- **`publish` takes two arguments, transfer status first.**
  `manifest/pgg_tableau_syntax.v:395` is
  `Notation "s |> 'publish' t a" := (s ;;; publish a of t)`. The one-argument
  spelling of the design note is a PARSE error, which `Fail` does not catch,
  so it cannot be recorded inside a compiling file; the probe recorded it in a
  file that is expected not to compile (audit N12).
- **The fuel clause takes either the literal or the named budget.**
  `psl211_alldecks_prefix_lit_paramsE` proves `fuel 220` and
  `fuel psl211_fuel` name the same run by `[]`. The named one is used, so that
  the budget is stated once.

Land the variants and the refusal at the end of the file. **They come from two
probe files, not one.** The two prefix definitions themselves,
`psl211_alldecks_prefix_vm` and `psl211_alldecks_prefix_lit`, are
`probe_c56_decomposition.v:217-236`; the two `paramsE` lemmas
(`psl211_alldecks_prefix_vm_paramsE` at `probe_e1_row_variants.v:35-38`,
`psl211_alldecks_prefix_lit_paramsE` at `:43-46`) and
`Fail Definition psl211_row_vm_reuse` at `:54-55` are in the other file, which
reaches the definitions by `Require`. Copying from `probe_e1_row_variants.v`
alone yields two lemmas over undefined constants.

The pgl27 demonstration this mirrors is `pgl27_rows.v:342-363` and it has
**four** items, not five, and pgl27 has no literal-fuel prefix and no second
`paramsE`: `pgl27_inline_dealt` at `:342-347`,
`Fail Definition pgl27_inline_neq : pgl27_inline_dealt = pgl27_dealt := erefl.`
at `:350`, `pgl27_inline_paramsE` at `:354-356`, and
`Fail Definition pgl27_inline_reuse` at `:362-363`. The non-identity `Fail` is
the one item that records that the two prefixes are different terms, which is
the whole point of the demonstration, so land its psl211 twin as well:

```coq
(** The two prefixes are not the same term. *)
Fail Definition psl211_alldecks_prefix_vm_neq :
  psl211_alldecks_prefix_vm = psl211_alldecks_prefix := erefl.
```

The literal-fuel prefix and its `paramsE` are a psl211 addition over the pgl27
shape, kept because they are what shows `fuel 220` and `fuel psl211_fuel` name
one run. Together these are the record that the row's shape is forced rather
than chosen.

The file header, in the shape of `pgl27_rows.v:1-95`, opens with the security
argument in English and names the dealer, and records under "not claimed" the
three items of section 1 of this plan plus G2: the parametrization
`(j, ph, pc) |-> deck` is injective through the heart set and the tables'
uniqueness and surjective because a valid deck's heart codes are distinct and
below six, it is checked numerically in
`notes/probes/2026-09-15-psl211-planb/audit-soundness/audit_alldecks.out`
(e) and (e'), it is not proved in Rocq, and the row's law is stated on the
parameter carrier and does not depend on it.

- [ ] **Step 2: Register, compile, check**

Add `instances/psl211/psl211_rows.v` to `_CoqProject` after
`instances/s5/s5_rows.v`, beside the other row files, then:

```bash
rocq makefile -f _CoqProject -o Makefile.rocq
make -j1 instances/psl211/psl211_rows.vo 2>&1 | tail -3 && echo BUILD-OK
```

Expected cost: 20 to 40 s, dominated by loading the manifest.

```bash
printf 'From pgg_smc Require Import psl211_rows.\nPrint Assumptions psl211_alldecks_prefix.\nPrint Assumptions psl211_row_alldecks_tableau.\nPrint Assumptions psl211_row_alldecks_rowE.\n' | rocq repl -q $PSL211_RFLAGS
```

Expected: **all three exactly the boolp trio**, including
`psl211_alldecks_prefix`. The prefix is not Closed and was never expected to be
by anything measured: over the compiled decomposition probe it carries
`psl211_alldecks_endpoints` plus the full trio, and the trio enters through the
Tableau machinery rather than through the three run facts, since in the same run
`psl211_alldecks_observed` printed `psl211_alldecks_endpoints` and nothing else.
The landed precedent agrees: `Print Assumptions pgl27_dealt` prints the full
trio. Once the endpoint equation is proved, which it is from T3, the trio alone
is what remains on all three names.

In the decomposition probe `Print Assumptions psl211_row_alldecks` listed
exactly `psl211_alldecks_fiber_transfer`, `psl211_alldecks_endpoints` and the
trio; with both of those now proved, the trio is what remains. A name outside
the trio is worth tracing with `Print Assumptions psl211_exact_witness` and then
down through `psl211_alldecks_view_indep`.

- [ ] **Step 3: Commit**

```bash
git add _CoqProject instances/psl211/psl211_rows.v
git commit -m "feat(psl211): the all-decks row as a Tableau program, publishing the manifest's row"
```

---

### Task 8: full build, assumption sweep, as-built record

- [ ] **Step 1: Full build**

```bash
pgrep -l rocqworker || echo NO-ROCQWORKER
make -j1 all 2>&1 | tail -5 && echo BUILD-OK
```

`-j1`, not `-j8`: a parallel build may schedule `psl211_endpoints.v` beside
another worker and the machine has 32 GB. If the build reports that
`instances/psl211/psl211_endpoints.vo` is being remade, stop and find out which
file in its import closure was touched; the rebuild costs 15 minutes and 17 GB
and there should be no reason for it after T3.

Expected: everything current except what T4 to T7 landed, and
`BUILD-OK`. Do not run `make clean`.

- [ ] **Step 2: Assumption sweep**

Every published object and every new statement, over the `.vo` chain:

```bash
printf 'From pgg_reconstruct Require Import design_privacy.\nFrom pgg_smc Require Import psl211_exec psl211_endpoints psl211_alldecks psl211_models psl211_rows pgg_analysis_manifest.\nPrint Assumptions uniform_pair_indep_of_fibers.\nPrint Assumptions psl211_profile_endpoints.\nPrint Assumptions psl211_alldecks_fiber_transfer.\nPrint Assumptions psl211_alldecks_valid.\nPrint Assumptions psl211_alldecks_terminates.\nPrint Assumptions psl211_alldecks_recon.\nPrint Assumptions psl211_alldecks_endpoints.\nPrint Assumptions psl211_alldecks_observed.\nPrint Assumptions psl211_alldecks_observed_recovers.\nPrint Assumptions psl211_alldecks_secret_expectedE.\nPrint Assumptions psl211_alldecks_view_indep.\nPrint Assumptions psl211_alldecks_static_indep.\nPrint Assumptions psl211_exact_witness.\nPrint Assumptions psl211_row_alldecks_tableau.\nPrint Assumptions psl211_row_alldecks_rowE.\nPrint Assumptions psl211_row_alldecks.\n' | rocq repl -q $PSL211_RFLAGS
```

Expected (ledger row F1): the run facts, validity and the new counting theorem
Closed; every published object exactly the boolp trio and nothing else. Then:

```bash
grep -rcE '^\s*(Admitted|Axiom|Hypothesis|Parameter)\b' \
  instances/psl211/*.v reconstruct/design_privacy.v | grep -v ':0$' || echo NO-HOLES
```

Expected: `NO-HOLES`.

- [ ] **Step 3: Append the as-built section to this plan**

Add a section "As built" recording, for each task: every statement or route
that differed from the text above, with before, after and why; the measured
compile time and peak of each new file; the measured `Time` lines and peak of
`psl211_profile_endpoints`; whether `scripts/profile_facade_check_test.py`
could be exercised; and the final assumption table, one line per published
object. Record the numbers that were measured, not the numbers predicted here.

- [ ] **Step 4: Add the rows to REVIEWS.md**

`notes/probes/2026-09-14-psl211/REVIEWS.md` has a "## Plan B (branch
feat/psl211-plan-b, 2026-09-15)" section whose table already carries B1
(`lib/perm_exchange.v`) and B2 (`instances/psl211/psl211_mixing.v`). Continue
it with one row per task of this plan, in the same six columns (task, file,
landed commits, spec review, quality review, assumptions):

| this plan | REVIEWS.md row |
|---|---|
| T1 | B3, `reconstruct/design_privacy.v` and `_CoqProject` |
| T2 | B4, `instances/psl211/psl211_exec.v` |
| T3 | B5, `instances/psl211/psl211_endpoints.v` |
| T4 | B6, `instances/psl211/psl211_alldecks.v` |
| T5 | B7, `instances/psl211/psl211_models.v` |
| T6 | B8, the facade, the manifest, the client and the two scripts |
| T7 | B9, `instances/psl211/psl211_rows.v` |

Every task runs implementer, then an independent Opus spec-compliance review
that compiles, then an Opus code-quality review against the mathcomp reference,
then fixes and a re-review, as Plan A's Task rows record. Sonnet output is never
final: any task carried out by a Sonnet agent is audited by an Opus reviewer
before its result counts, and the REVIEWS.md row says who did the audit.

- [ ] **Step 5: Commit**

```bash
git add docs/superpowers/plans/2026-09-15-psl211-plan-b-alldecks.md \
  notes/probes/2026-09-14-psl211/REVIEWS.md
git commit -m "docs(psl211): as-built record of the all-decks executed cone"
```

---

## Decisions fixed here (not left to implementation)

1. **The all-decks parameter record, its termination and its recon live in
   `psl211_alldecks.v`, not in `psl211_exec.v`.** The design note's file map
   put both parameter records in `psl211_exec.v`. Moving the all-decks half out
   keeps `psl211_alldecks.v` outside the import closure of
   `psl211_endpoints.v`, so the one file with an unproved statement in it can
   be edited and recompiled at 20 seconds a pass instead of 15 minutes and
   17 GB. Nothing else changes: `psl211_endpoints.v` needs `psl211_algebra` and
   `psl211_fuel` alone, which is why probe P1b2 decided the endpoint equation
   in a file that had no all-decks declaration at all.

2. **`psl211_exec.v` is minimal by design.** It carries the seat cache, the
   algebra block, the fuel, the dealt parameter record with its recon and
   termination, and the two conversion lemmas. Every declaration in it is
   something `psl211_endpoints.v` or `psl211_alldecks.v` needs. Reason: from T3
   onward an edit to this file costs 15 minutes and 17 GB.

3. **`psl211_profile_endpoints` lives alone in `psl211_endpoints.v`**, against
   the pgl27 precedent, which keeps the analogue inline at `pgl27_exec.v:383`.
   Reason: it is the single most expensive declaration the repository would
   then contain, and putting it as close to the leaves as its statement allows
   is what keeps an unrelated edit from re-triggering it. Recorded as a
   deliberate departure in audit N38.

4. **`lib/perm_uniform.v` is not extended.** The three generic restatements of
   `card_prescribed` land in `psl211_alldecks.v` under the `psl211_` prefix
   instead of beside `card_prescribed` where they belong mathematically.
   Reason: `reconstruct/algebraic_rigidity.v` imports `perm_uniform.v` and
   `psl211_profile.v` imports `algebraic_rigidity.v`, so `perm_uniform.v` is
   inside the endpoint fact's import closure and is frozen from T3. If the
   generic lemmas are wanted in the library later, move them in a commit that
   budgets the 15 minutes.

5. **The C3 bridge is copied from `probe_c3_bridge.v`, not from
   `audit-soundness/audit_c3.v`.** The two are the same mathematics and were
   written without knowledge of each other, which is the strongest evidence
   available that the statement is right. The probe's form is copied because it
   is already discharged into standalone lemmas with `X`, `G`, `T` implicit and
   its `Let P` inlined, and because `probe_c56_decomposition.v` consumes it in
   that form. The name is `uniform_pair_indep_of_fibers`, the probes' and
   design note section 8's spelling, not audit N28's proposed
   `uniform_prod_inde_fiber`. Recorded departure: the name carries an `_of_`
   connective, which the psl211 naming convention bars and which its nearest
   neighbour `colour_view_indep_fibers` in the same file does without. The
   probe's name wins because the probe compiled it and the decomposition probe
   applies it under it.

6. **The manifest is edited before the row file is written.** `psl211_rows.v`
   proves `published_row psl211_row_alldecks_tableau = psl211_row_alldecks`,
   so the manifest's `AnalysisPathRow` must exist first. This is the pgl27
   layering: manifest at `_CoqProject:187`, `pgl27_rows.v` at `:190`,
   `pgl27_row_exact_rowE` in the row file.

7. **Two row names, not one.** The manifest's `AnalysisPathRow` is
   `psl211_row_alldecks` and the program's `PublishedRow` is
   `psl211_row_alldecks_tableau`, mirroring `pgl27_row_exact` and
   `pgl27_row_exact_tableau`. The probe's `psl211_row_alldecks : PublishedRow`
   is renamed to the second.

8. **Fuel 220 throughout, under the single name `psl211_fuel`.** The probes'
   `psl211_fuel = 380` and `psl211_fuel_small = 220` collapse to one constant.
   Reason: the endpoint reduction measured 561.4 s at 220 against 562.0 s at
   380, a difference inside the noise, so the cost is the twelve-card,
   fourteen-process trace and not the budget; and termination holds at 220 in
   both modes.

9. **`psl211_deal` and `psl211_inputT` are `Notation`s.** A `Definition` hides
   the products' finite structure from `#|...|` and `` `U ``. The class bit is
   first and separate, so the secret is `fst` and the generic bridge applies
   with `s := fst`.

10. **`psl211_alldecks_gt0` is stated at `[set: psl211_inputT]`.** `` `U `` is
    `fdist_uniform_supp` and takes a `{set _}`; at a proper subset the C3
    bridge is false, because mass outside the subset is zero while the counts
    still see it.

11. **The block count is taken over the IMAGE `pgg_rho g @: C`**, not the
    preimage: seat `i` reads the card the laid deck puts at position
    `pgg_rho g i`. `psl211_pattern_transfer` is instantiated at that image with
    the premises `0 < #|P|`, `#|P| <= 5` and `A \subset P`, all at `P` and none
    at `C`, the two cardinality premises transported by
    `card_imset (perm_inj _)`.

12. **Every statement about the laid deck is proved symbolically.** The rank
    enters the labelling through `inord`, whose `insub` is guarded by the
    `Qed`-opaque `idP`, so `vm_compute` cannot decide even
    `head 0 (psl211_alldecks_seq (true, (ord0, 1%g, 1%g))) = 0`, which is true.
    There is no `vm_compute` sanity check over the deal carrier: `enum 'I_6`
    returns a stuck term and `size (enum {perm 'I_6})` was killed at 5019 MB.
    The numeric check lives outside the kernel, in `audit_alldecks.py`.

13. **`content_of` is restated as `psl211_content_of` rather than moved out of
    `instances/pgl27/pgl27_trace.v`.** Moving it would edit a file outside this
    plan's scope whose dependents include the pgl27 facade and the manifest;
    restating it is five lines, and its shape is pinned by a proved positive
    and a refuted mutation.

14. **The row names its termination lemma and publishes two statuses.** The
    inline `terminates by vm_compute` form forks the observed execution and the
    following `sample` is rejected; `|> publish` takes a `TransferStatus` and
    an `AssumptionStatus`, in that order.

15. **The claim ledger's status and pass columns stay in the design note.** No
    statement comment in a landed file carries a status marker, an effort
    estimate or a probe reference.

## Self-review

**Spec coverage.** Design note section 3's definitions are fixed in T2, T4 and
T5; section 4's ledger rows A1 to A4 in T2 and T3, B1 to B3 in T4, C1 to C7a in
T4 and T5, D1 in T5, E1 in T7, E2 in T6, F1 in T8, G1 and G2 recorded as not
claimed in section 1 and in the row file's header. Section 8's corrections are
each applied and named: the `Notation` spelling (Decision 9), `[set: _]`
positivity (Decision 10), fuel 220 under one name (Decision 8), symbolic proofs
about the laid deck (Decision 12), the summed rather than per-cut premise (T4
Step 8), no count below six separating the two tables (T4 Step 8), the endpoint
invalidation rule (section 2's freeze rule), and the pair-shaped
`psl211_alldecks_cardE` with its trailing `mulnA` (T4 Step 1).

**Placeholder scan.** Exactly one proof body in this plan is a route rather
than compiled code: `psl211_alldecks_per_cut_count` and
`psl211_alldecks_fiber_transfer` in T4 Step 8, marked as the implementer's
route and given in eleven numbered steps with every expected lemma named. Their
two statements are verbatim from `probe_c56_decomposition.v`, where the
headline, the witness and the published row were derived from them to `Qed`, so
the types are pinned by compiled evidence and only the proofs are new. Every
other code block in this plan is copied from a probe file that compiled.

**Type consistency.** `psl211_alldecks_view` has carrier
`{ffun seatT -> cardT}` at `seatT := 'I_(pi_T' (mp_PI (instance_profile
psl211_algebra))).+1` and `cardT := 'I_(pgg_N' (mp_M (instance_profile
psl211_algebra))).+1` in T4, T5 and T7, both twelve by `[]`; the layout is
ascribed at `(ts_T' (pga_scheme psl211_algebra)).+1.-tuple 'I_(pga_n
psl211_algebra).+2`, also twelve both ways; `psl211_alldecks_expected x` and
`x.1` are one term, which is what makes `supplied_static_recon`'s premise and
`psl211_alldecks_ts_valid` one statement; the threshold is `#|C| <= 5` from the
bridge through the witness to the row, the framework's own premise being
`#|C| < profile_k = 6`.

**Order consistency.** `psl211_alldecks.v` needs `psl211_exec.v` for
`psl211_algebra` and `psl211_fuel`, so T4 follows T2; `psl211_endpoints.v`
needs only `psl211_exec.v`, so T3 may follow T2 immediately and does, which is
what puts the freeze line below the new mathematics rather than above it.
`psl211_models.v` needs both `psl211_alldecks.v` and `psl211_endpoints.v`, so
T5 follows T3 and T4. `manifest/pgg_analysis_manifest.v` needs
`psl211_analysis.v`, which needs `psl211_models.v`, so T6 follows T5; and
`psl211_rows.v` needs the manifest, so T7 follows T6.

## Plan audit fold (AUDIT-PLAN-B.md, 2026-09-15, NO-GO -> folded)

Adversarial audit of this plan at its first draft:
`notes/probes/2026-09-15-psl211-planb/AUDIT-PLAN-B.md`, 63 findings, 8 blocking,
verdict NO-GO on the citation layer with the mathematics and the task skeleton
confirmed. Two compiled counter-probes under
`notes/probes/2026-09-15-psl211-planb/audit-plan/`, both rc 0:
`audit_t4_skeleton.v` and `audit_t4_percut.v`. Every finding below was
re-verified against the files here before being applied; the closure count of
finding 21 was recomputed independently and agrees.

**The eight blocking findings and where each is now fixed.**

1. **#4, T4 and T5 both claimed `planb_alldecks_defs.v:108-118`.** Following
   both Source lines literally landed `psl211_alldecksP` and
   `psl211_alldecks_secret` in two files, and the second would not compile.
   T4's range is now `:34-106` and T5's is `:108-118`, each stated twice, in the
   Source line and at the copy instruction, with a sentence in each naming the
   other file's half.
2. **#21, the freeze rule's closure list said "exactly" and omitted seven
   members.** Section 2 now carries the measured list: 35 already-landed files
   plus `psl211_exec.v` and `psl211_endpoints.v` themselves, 37 in all,
   recomputed here from the live `Require` lines and agreeing with the audit's
   count. The seven that were missing are named as the ones easiest to believe
   free: `groups/pgg_raag.v`, `reconstruct/cover_tradeoff.v`,
   `reconstruct/pgg_sum_mod.v`, `reconstruct/pgl_bound.v`,
   `security/pgg_collusion_bound.v`, `security/pgg_security_solver.v`,
   `security/pgg_weighted_words.v`.
3. **#27, `manifest/pgg_analysis_manifest.v:730` is inside the `s5_row_word`
   docstring.** The insertion point for the ninth row `Definition` is `:736`,
   and T6 Step 2 item 3 now says why.
4. **#28, the facade alias listing defeats the `^Definition` anchor.** T6 Step 1
   now opens with the column-0 rule and the mechanism:
   `scripts/profile_facade_check.sh:258-259` anchors at column 0 and
   `strip_comments` at `:103-145` preserves column position on purpose, so an
   inline section marker makes the checker exit 1 with `NO ALIAS`.
5. **#39, `scripts/profile_facade_check_test.py` has no `SOURCES` table.** T6
   Step 4 now names `PROFILES` at `:14-23` and `FACADES` at `:24-28`, gives both
   rows verbatim, and records that omitting them turns regression cases C0, C3,
   C10 and C13 from exit 0 to exit 1.
6. **#43, `probe_e1_row_variants.v` contains no prefix definitions.** T7 now
   cites both sources: the two variants at `probe_c56_decomposition.v:217-236`,
   the two `paramsE` lemmas and the refusal at `probe_e1_row_variants.v:31-55`.
7. **#48, T7 predicted `psl211_alldecks_prefix` Closed.** It carries the boolp
   trio, which enters through the Tableau machinery and not through the run
   facts; `Print Assumptions pgl27_dealt` prints the trio too. The prediction is
   corrected to all three names at the trio and the sentence calling any other
   result a defect is gone.
8. **#49, T5 predicted `psl211_alldecks_secret_expectedE` Closed.**
   `log-probe_d1_observed.txt` measures the trio, structurally: the statement
   mentions `psl211_alldecks_secret R`, hence `psl211_alldecksP`, hence
   `fdist_uniform_supp`. It is moved to the trio group with that reason.

**The three near-blocking findings.** #19, the one part of the new mathematics
with no compiled support: T4 route steps 5, 6 and 7 are now labelled **no
compiled support**, step 7's three unnamed sub-steps are named
`ad_heart_rank_card` (the `#|K| = #|A|` bridge that turns
`psl211_perm_ext_count`'s factorial into the one step 7 asserts),
`ad_club_code` (the decoding of a club card code back into `'I_6`) and
`ad_prescription_inj` (the discharge of the `{in K &, injective t}` premise),
and step 7 is required to be stated at the destructured deal
`(b, (j, pp.1, pp.2))`, since `psl211_alldecks_seq` only reduces there. #33,
`psl211_alldecks_coalition_distE` was aliased and pinned but never stated: it is
now a displayed `Lemma` with its proof in T5 Step 6. #29, the manifest header
counts are at `:6`, `:7-8`, `:564` and `:1527`, not at `:56-72`.

**The citation layer, finding by finding.** Every probe range was re-verified
here by reading the first and last line of the quoted code out of the file, not
by trusting the audit. #1 T2 source is `psl211_planb_defs.v:32-94`, the file
being 94 lines, plus `probe_p1b2_endpoints_small.v:19-21` for the termination
lemma, which the probe names `psl211_dealt_terminates_small`. #2 T2 imports are
`:8-30`. #3 T3's source gains the `_small`-under-Decision-8 note. #5 the view
definition is `probe_c2_bridge.v:32-42`. #6 and #7 the two reading lemmas split:
`psl211_alldecks_read_setE` at `probe_c5_sanity.v:48-55` to T4,
`psl211_alldecks_read_position` at `:37-46` to T5. #8 the two fiber statements
are `probe_c56_decomposition.v:107-128`, with the docstrings at `:94-128`, and
the copy is verbatim modulo this file's `cardT` notation. #9 T5's headline block
is `:134-185`. #10 T7's prefix and row are `:191-212`. #30 the documented row
block's shape is `:86-144` and its insertion point `:560`. #31 the three checker
blocks are `:738-1010`, `:1011-1302`, `:1303-1525`. #40 the script contract is
`:44-50`. #41 the client's six count sites and three ranges are corrected and
"two header edits" becomes six. #46 `rowE` is `pgl27_rows.v:316-321`. #44 the
pgl27 inline demonstration is `:342-363` and has four items, and its
non-identity `Fail` is added to T7 as `psl211_alldecks_prefix_vm_neq`.

**The route corrections.** #11 `pair_injl` does not exist and is gone, together
with the whole step it justified. #12 route step 1 is replaced by the six-line
script proved outright as `audit_B1`, using `partition_big` and `reindex_onto`
and needing neither `card_fiber_sum` nor `card_imset` nor `cardsX`. #13 route
step 2 is `audit_B2`, and the summed statement follows from the per-cut one
alone. #14 `audit_A1` is cited beside `audit_transfer_at_P`, because it is the
instantiation at `C : {set seatT}`, the type the route actually has. #15
`subsetIl` does not state the inclusion, since `A` is the image of a
comprehension; the compiled `subsetP` form replaces it and the
restate-as-intersection alternative is named. #16 the lemma that fires on the
constant-summand sum is `sum_nat_const`, and the `psl211_pattern_count`-to-`count`
delta step is written out. #18 route step 11 is budgeted with its measurement,
killed twice at 280 s and 420 s at 3.3 GB with the table-size hypotheses in
context, and two rules are added: clear those hypotheses first, and end with
`exact:` and never `by`.

**The other assumption predictions.** #50 `psl211_alldecks_exact_viewE` and
`psl211_alldecks_static_obs_funE` carry exactly two axioms,
`propositional_extensionality` and `functional_extensionality_dep`, which is
what `boolp.funext` alone carries; they now have their own group, and the note
that the pgl27 analogy fails there is kept. #51 the T5 `printf` gains
`psl211_alldecks_static_obs_funE` and `psl211_alldecks_coalition_distE`. #52 T4
expects Closed for the thirteen measured and Closed for the two new counting
theorems only if their proofs use nothing classical. #54 four of T2's five were
read back directly and the fifth through its all-decks twin, because
`probe_p1a_terminates.vo` is stale. #55 P1d measured at fuel 380 and the
fuel-220 run was never read back. #56 the row's prediction is by analogy, since
no probe ever built a psl211 `AnalysisPathRow`.

**The comment-rule findings.** #57 the `psl211_fuel` comment loses the
cross-declaration measurement and the file-layout word. #58
`psl211_profile_endpoints` loses the cost narration and the organisational
claim and keeps the domain position. #59 `psl211_alldecks_fiber_transfer` loses
the probe reference and the status marker, which Decision 15 of this plan
forbids. #60 `psl211_alldecks_per_cut_count` loses "not a statement the
published row rests on". #61 the corollary's comment says "at most five" and
drops the used-by pointer.

**Confirmations that changed nothing.** #13, #17, #20, #22, #25, #32, #34, #38,
#45, #47, #53, #63. Two are worth restating because they are load-bearing: the
`MkAnalysisPathRow` field order is observed, completion, model, transfer,
assumptions and the plan's application matches `pgl27_row_exact` character for
character (#32); and none of the five row pins forces `apr_observed`, so the
manifest block is not a conversion bomb (#38).

**Partially applied, with the reason.**

- **#62, the 80-column rule**, is applied to every block this plan asks an
  implementer to land as Rocq source, and the rule itself is stated in T2 Step 1
  beside the header box. Two categories are deliberately left over 80. The flow
  sketch of section 0 is a pseudo-DSL display with a two-column running total
  and is not Rocq source, so the file-width rule does not reach it. And the
  quoted discharged signature of `uniform_pair_indep_of_fibers` in T1 is the
  probe's own text, reproduced so that an implementer can compare byte for byte
  against `probe_c3_bridge.v`; rewrapping it in the plan would make the
  comparison harder, and the instruction to rewrap on landing is stated in T2
  Step 1 with the probe's six over-80 lines named.
- **#23, trimming T2's import list**, is added as T2 Step 1b, but the audit's
  description of it as "the one cheap way to shrink the freeze" is corrected by
  measurement rather than repeated: the trim removes exactly two files,
  `security/pgg_sample_adapter.v` and `security/pgg_weighted_words.v`, taking
  the closure from 37 to 35. The other five transitively reached files arrive
  through `psl211_profile.v` and `psl211_closure.v` and no import list on
  `psl211_exec.v` can remove them. The step is kept because two files is still
  two files, and the plan says what it buys.

Nothing else was rejected.
