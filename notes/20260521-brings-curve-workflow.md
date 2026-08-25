# Plan (Worked Example): Formalize Bring's Curve in `infotheo-pgg`

> **This is a teaching plan**, not an implementation directive. It shows how the merged `rocq-skills` + custom-agents toolflow handles a multi-month formalization task. Each stage names the exact commands, agents, and reference docs to invoke.

## Critical caveats (incorporated from adversarial audit)

Three load-bearing facts the rest of this plan relies on. If any is wrong, the corresponding stage will misfire:

1. **Cross-project memory does NOT load automatically.** Claude Code memory is per-project. The merge work from the previous plan landed under `~/.claude/projects/-Users-cheng-huiweng-Projects-coq-infotheo-itp/memory/`. A session opened in `infotheo-pgg` will load `~/.claude/projects/-Users-cheng-huiweng-Projects-coq-infotheo-pgg/memory/` instead, which has a different (overlapping but not identical) ruleset. Before executing this plan in `infotheo-pgg`, either (a) copy the seven new memory entries from `itp` to `pgg`, or (b) execute Stage -1 below to rewrite them in place for the pgg project.

2. **Project command surface differs.** `~/.claude/commands/rocq-prove.md` is user-global (works anywhere). The `infotheo-pgg` project also has its own command set under `.claude/commands/`: `prove-lemma.md`, `rocq-apply-fixes.md`, `rocq-fix-plan.md`. The plan distinguishes them explicitly below. Do not assume any user-global command auto-replaces a project command of similar role.

3. **Plugin agents live in the plugin namespace, not `~/.claude/agents/`.** The four plugin subagents (`proof-golfer`, `proof-repair`, `axiom-eliminator`, `admitted-filler-deep`) are loaded by the plugin manifest under `~/.claude/plugins/rocq-skills/plugins/rocq/agents/`. They are visible via the Agent tool's subagent list but do not appear in `~/.claude/agents/` directory listing. This is normal; the plan's references are correct, but `ls ~/.claude/agents/` will only show your custom agents.

## Context

**Task.** Formalize Bring's curve — the smooth projective curve of genus 4 defined in **P^4** by
```
x_1 + x_2 + x_3 + x_4 + x_5 = 0
x_1^2 + x_2^2 + x_3^2 + x_4^2 + x_5^2 = 0
x_1^3 + x_2^3 + x_3^3 + x_4^3 + x_5^3 = 0
```
with an `S_5` action by coordinate permutation.

**Project.** `/Users/cheng-huiweng/Projects/coq/infotheo-pgg`, branch `pgg-smc`. This is a fork of infotheo augmented with the PGG-SMC framework (permutation-group games for secure multi-party computation).

**Why it matters.** PGG-SMC parametrizes its S_5 instance by Bring's curve. Currently the curve is **axiomatized opaquely** (Edge 1978 cited externally) in `pgg-smc/reconstruct/curve_realisation.v`. Deepening that axiom into actual MathComp polynomial geometry would (a) remove an opaque appeal to literature, (b) connect PGG-SMC's security argument to verifiable algebraic content, (c) yield a reusable algebraic-geometry layer on top of MathComp.

**Why this is a workflow example.** A task of this size touches every part of the merged tool stack: `/rocq:learn`, `/rocq:draft`, `rocq-prover`, `rocq-expert-prover`, `proof-repair`, `/rocq:refactor`, `/rocq:golf`, `/rocq:checkpoint`, the cycle engine, the audit gate, and the memory routing rules. The plan below shows the canonical invocation for each.

---

## Survey results (Stage 0 output — already gathered during planning)

### What `infotheo-pgg` already has

- `pgg-smc/reconstruct/curve_realisation.v` — axiomatic `realised_by_curve` predicate; Bring's curve named explicitly in comments (lines 25-29) but treated as a black box.
- `pgg-smc/reconstruct/covering_scheme.v` — Riemann-Hurwitz formula, genus / ramification constraints. Usable for genus-4 derivation.
- `pgg-smc/reconstruct/cover_genus0.v` — genus-0 (projective line) covering scaffolding.
- `pgg-smc/instances/s5/rigidity_s5_instance.v` — S_5 instance parametrized on the curve axiom.
- `pgg-smc/groups/pgg_raag.v` — monodromy / RAAG / free-group balls.
- `pgg-smc/reconstruct/algebraic_rigidity.v` — "one algebraic choice determines complexity, security, threshold."
- `lib/poly_ext.v`, `lib/ssralg_ext.v`, `lib/bigop_ext.v` — wrappers over MathComp's polynomial / ring / bigop tooling.
- 213 `.vo` files present — the project is currently built locally.

### What MathComp gives us

- ✅ Univariate polynomial ring `{poly R}` (`mathcomp/algebra/poly.v`)
- ✅ Polynomial division (`polydiv.v`), Sylvester matrices and resultants (`mxpoly.v`)
- ✅ Bivariate polynomials (`polyXY.v`)
- ✅ Field extensions, Galois groups, finite fields (`field/galois.v`, `field/algC.v`, `field/finfield.v`)
- ✅ Finite group + automorphism theory (`fingroup/`, `field/galois.v`)
- ❌ Projective space `P^n` — **absent**
- ❌ Algebraic varieties / schemes — **absent**
- ❌ Multivariate polynomials in 3+ variables — **absent**
- ❌ Symmetric polynomials — **absent**
- ❌ Riemann surfaces / genus formula generally — **absent**

**Implication.** Two scope cuts available:

| Phase | Scope | Effort |
|---|---|---|
| **A** (recommended first) | Tighten the axiom interface in `curve_realisation.v`: enrich `realised_by_curve` to record the S_5 action structure and the genus contract, **without** introducing multivariate polynomials (those are Phase B). Keep smoothness and the defining-ideal entries axiomatized; expose them as discharge hooks. | ~1-2 weeks of agent-assisted work, plus mathematical-design overhead the agent cannot estimate. The original "2-4 weeks" was speculative. |
| **B** (deeper) | Build the missing infrastructure: define multivariate `R[x_1,…,x_n]`, symmetric polynomials, homogeneous polynomials, P^n, zero loci. Then realize Bring's curve concretely. This is a months-long project on its own; comparable in scale to a small MathComp contribution. | Indeterminate; depends on how much existing MathComp algebra can be reused vs. invented. |
| **C** (capstone) | Use the concrete realization from Phase B to discharge the axioms in Phase A. Connect to PGG-SMC's security argument. | Days-to-weeks after B lands. |

The plan below walks through Phase A end-to-end and sketches Phase B/C interfaces. Phase A is enough work to exercise every tool in the merged stack.

**Caveat (audit M3):** the "tighten the axiom interface" framing only saves Phase B work if you accept that the ideal and smoothness predicates remain opaque. If you decide the ideal must be a real multivariate polynomial in Phase A, Phase A absorbs the Phase B prerequisites and becomes months, not weeks.

---

## Stage -1 — Memory migration (do this BEFORE Stage 0 if starting in `infotheo-pgg`)

The merged-flow memory rules were written in `infotheo-itp`. Migrate the routing-critical ones to `infotheo-pgg` so a session there picks up the same routing:

```
# Source: ~/.claude/projects/-Users-cheng-huiweng-Projects-coq-infotheo-itp/memory/
# Target: ~/.claude/projects/-Users-cheng-huiweng-Projects-coq-infotheo-pgg/memory/

Files to copy verbatim:
  feedback_rocq_skills_installed.md
  feedback_proving_routing.md
  feedback_cycle_engine_adopted.md
  feedback_new_subagents.md
  feedback_audit_still_mandatory.md
  feedback_guardrails_kept.md
  reference_rocq_skills_usage_examples.md

Files to ADAPT for pgg:
  feedback_proving_routing.md   ← rewrite the "Multi-phase audit + parallel
                                  prove" row to point at pgg's own commands
                                  /prove-lemma, /rocq-apply-fixes,
                                  /rocq-fix-plan (NOT /rocq-prove, which is
                                  user-global but project-itp-tuned).
  feedback_audit_still_mandatory.md ← update path: pgg's audit script is at
                                       .claude/audit/audit.sh, NOT
                                       .claude/audit/bin/audit.sh.

Files NOT to copy (already in pgg or itp-specific):
  feedback_atomic_tasks.md      ← pgg has its own commit-cadence rule
                                  (project_pgg_framework_coupling.md
                                  governs); reconcile manually.
  feedback_rocq_check_is_done.md ← pgg may want a different verification
                                   policy; leave pgg's default in place.

Append to pgg's MEMORY.md index after copy/adapt.
```

After Stage -1, Stage 0 surveys in a pgg session will route correctly.

---

## Stage-by-stage walkthrough

### Stage 0 — Environment & survey refresh

Before any editing:

```
/rocq:doctor                    # confirms rocq-mcp connectivity, opam switch,
                                # _CoqProject load path, .vo currency for
                                # infotheo-pgg deps
/rocq:learn --mode=repo         # repo tour: re-confirm the pgg-smc reconstruct/
                                # tree and the existing curve_realisation.v
/rocq:learn --mode=library "multivariate polynomial mathcomp"
                                # confirm MathComp has no native MV-poly
                                # → forces Phase B if you want concrete realization
/rocq:learn --mode=library "Galois theory Galois group mathcomp"
                                # confirm field/galois.v is the right base for
                                # the S_5 ↔ K(Bring)/K(P^1) story
```

Output: a short Stage-0 note saved to `pgg-smc/notes/20260521-brings-curve-survey.md` per the project's dated-notes convention (memory: `feedback_plan_persistence_as_notes`).

### Stage 1 — Drafting from informal sources

**Manual prerequisite (cannot be automated).** Read Edge 1978 (paper), Klein 1879 (icosahedron book), and the curve's Wikipedia entry. Hand-write a short markdown file at `pgg-smc/notes/bring_informal_phaseA.md` listing the definitions and theorems you want to formalize — one per heading, with the informal statement underneath. The merged toolflow has no automated literature-extraction step; `/rocq:draft` consumes the markdown you produce, it does not produce it. Plan ~half a day for this prerequisite (more if you're new to the literature).

Once `bring_informal_phaseA.md` exists, Phase A draft:

```
/rocq:draft --source=pgg-smc/notes/bring_informal_phaseA.md \
            --out=pgg-smc/reconstruct/brings_curve.v
```

Expected skeleton (Admitted bodies):

```coq
(* In pgg-smc/reconstruct/brings_curve.v *)

(* Section parameters reused from curve_realisation.v.  Note: Bring's curve
   is defined over Q (or even Z); requiring algebraic closure here would
   exclude the field of definition.  Use fieldType, or split into
   fieldOfDefinition + splittingField parameters if the discharge needs
   roots over an extension. *)
Variable K : fieldType.

Definition bring_ideal_gens : seq {poly K * nat} :=
  [:: power_sum 5 1 ; power_sum 5 2 ; power_sum 5 3].

Definition brings_curve : Type := { …axiom interface… }.

Lemma brings_curve_S5_action :
  exists rho : 'S_5 -> {aut brings_curve}, faithful rho.
Admitted.

Lemma brings_curve_genus : genus brings_curve = 4.
Admitted.

Lemma brings_curve_realises_S5 :
  realised_by_curve 'S_5 brings_curve.
Admitted.
```

*Audit note:* `power_sum` here is a placeholder — MathComp has no native multivariate symmetric polynomial, so in Phase A this would be an opaque section parameter or a degenerate univariate stand-in. Phase B builds the real multivariate scaffolding.

Phase B draft (further out, separate file):

```
/rocq:draft --source=pgg-smc/notes/bring_informal_phaseB.md \
            --out=pgg-smc/algebraic_geometry/multivariate_poly.v
/rocq:draft --source=pgg-smc/notes/projective_space.md \
            --out=pgg-smc/algebraic_geometry/projective_space.v
/rocq:draft --source=pgg-smc/notes/symmetric_polys.md \
            --out=pgg-smc/algebraic_geometry/symmetric_polynomials.v
```

The draft command emits Admitted bodies only; statements and headers are the real artifact. The proofs happen in Stage 2.

### Stage 2 — Per-lemma proof cycles

This is the bulk of the work. The memory routing table (`feedback_proving_routing`) decides where each Admitted goes.

#### Example 2a: a project-aware lemma (default route)

> *Goal:* prove `bring_ideal_gens` is `S_5`-invariant.

```
You: "prove bring_ideal_gens_S5_invariant in pgg-smc/reconstruct/brings_curve.v"
```

Routing → `rocq-prover` agent (default for `.v` edits in this project).

Agent execution under the cycle engine:

```
Phase: Plan
  - rocq_start(file="pgg-smc/reconstruct/brings_curve.v",
               theorem="bring_ideal_gens_S5_invariant")
  - rocq_query("Search (perm_eq (map _ _) _).", file=...)
  - rocq_query("Check power_sum_perm.", file=...)
  - candidates: rewrite with power_sum_perm; case-split on permutation
Phase: Work
  - rocq_step_multi(tactics=[
      "apply: power_sum_perm.",
      "elim/big_ind: _ => /=.",
      "rewrite -perm_sym.",
    ])
  - winner: power_sum_perm
  - rocq_check(body="apply: power_sum_perm.")
  - proof_finished=true
Phase: Checkpoint
  - rocq_compile(source=<file>)
  - passes
Phase: Review
  - rocq-auditor Stage 2 (mandatory pre-commit)
  - verdict: pass (respects MathComp naming, no opaque tactics)
Phase: Continue
  - atomic commit; next Admitted
```

#### Example 2b: a hard algebraic lemma (escalation route)

> *Goal:* `brings_curve_genus : genus brings_curve = 4`.
> Riemann-Hurwitz applied to the **degree-120 cover of P^1 by Bring's curve, induced by the S_5 quotient**. (Earlier draft conflated S_5 with the icosahedral rotation group; the icosahedral group is A_5 of order 60, NOT S_5. Bring's curve carries an S_5 action; the relevant ramification data is the S_5 quotient. The A_5 sub-cover of order 60 with the classical 12+20+30 ramification is the icosahedral case, not Bring's-curve-over-the-line.)

This is a published derivation but mechanically involves a lot of arithmetic. Two paths:

Project-aware:
```
You: "/rocq-prove pgg-smc/reconstruct/brings_curve.v brings_curve_genus"
```
Routes to the existing project tool (`/rocq-prove` is the user's multi-phase audit + prove flow). This will dispatch internally and respect the audit catalog.

Or, if the user wants the cycle-engine-guided experience:
```
You: "/rocq:prove pgg-smc/reconstruct/brings_curve.v brings_curve_genus"
```

For very hard subgoals: route to `rocq-expert-prover` directly (memory: routes to expert when project-aware idioms dominate). The expert's prompt has the delegation-to-`admitted-filler-deep` rule.

#### Example 2c: mechanical bookkeeping lemmas (autonomous batch)

> *Goal:* fill ~30 `Admitted` for symmetric-polynomial bookkeeping in Phase B's `symmetric_polynomials.v`.

```
You: "/rocq:autoprove pgg-smc/algebraic_geometry/symmetric_polynomials.v \
                      --max-cycles=15 --max-time=60m"
```

Routes to the cycle-engine autonomous mode + `admitted-filler-deep`. Auto-commits per fill. Hard-stops on max cycles / time / stuck.

**Caveat from memory `feedback_atomic_tasks`:** autoprove auto-commits, which conflicts with the atomic-task-with-verify cadence. Use `--commit=none` if you want to gather all fills before manually committing:

```
You: "/rocq:autoprove pgg-smc/algebraic_geometry/symmetric_polynomials.v \
                      --max-cycles=15 --commit=none"
```

Then run `/rocq:checkpoint` at the end of the batch.

#### Example 2d: when stuck

> Suppose `brings_curve_genus` has been spinning. Same failure pattern 3 times: candidate uses Riemann-Hurwitz but the agent can't find a MathComp lemma named `riemann_hurwitz`.

Cycle engine triggers Replan:

```
Phase: Replan (stuck)
  - failed candidates: [riemann_hurwitz, riemannHurwitz, Riemann_Hurwitz]
  - error signatures: "reference X not found" × 3
  - Diagnosis: MathComp has no Riemann-Hurwitz; project has its own at
                pgg-smc/reconstruct/covering_scheme.v.  The actual lemma names
                (verified via grep) are `genus_from_hurwitz`, `hurwitz_base0`,
                `genus0_ramif`, `ramif_forces_genus`, plus the `cd_hurwitz`
                record field on the covering-data structure.  The closest
                match to "Riemann-Hurwitz equation" is `genus_from_hurwitz`.
  - Revised plan: import covering_scheme.v; rewrite the proof to instantiate
                   the covering-data record `cd_hurwitz` with degree=120
                   (|S_5|) and the appropriate ramification multiset, then
                   apply genus_from_hurwitz.
```

Strategy-switching detection (global CLAUDE.md rule) blocks silent thrashing here. The agent surfaces the dead-end and waits for confirmation before changing approach.

### Stage 3 — Maintenance during the bulk

Two situations come up repeatedly in a multi-week formalization:

#### 3a. Definition change breaks downstream proofs

> *Scenario:* You refine `brings_curve : Type` to `brings_curve : closedFieldType -> Type` (parametrize over the base field). Twelve downstream proofs break with "expected `brings_curve` to take 0 args, got 1".

```
You: "fix the proofs broken by the brings_curve parametrization"
```

Routes to `proof-repair` subagent.

Subagent execution:
```
1. make -j1 2>&1 | tee /tmp/build.log
2. python3 $ROCQ_SCRIPTS/parse_rocq_errors.py /tmp/build.log
3. cluster: all 12 errors have signature
     "expected 0 args, got 1 — at <file>:<line>:<column>"
4. dispatch rocq-prover to add the `K` argument at each call site
5. re-run make -j1; verify 0 errors
6. rocq-auditor Stage-2 audit
7. atomic-commit
```

This saves the user from manually editing 12 call sites.

#### 3b. Library leverage opportunity

> *Scenario:* You realize your `power_sum 5 k` definition duplicates MathComp's `\sum_(i < 5) x_i^k`. Worth refactoring before more code depends on the custom definition.

```
You: "/rocq:refactor pgg-smc/algebraic_geometry/symmetric_polynomials.v"
```

Routes to `/rocq:refactor` (a plugin command).

Flow:
```
1. $ROCQ_SCRIPTS/smart_search.sh "power_sum" mathcomp
2. find: \sum_(i < n) X_i^k  in algebra/poly.v
3. consult $ROCQ_REFS/tactics-reference.md  for bigop manipulation tactics
4. propose refactor: replace `power_sum` with `\sum_(i < 5) X_i ^+ k` notation
   - reverse-dep scan via $ROCQ_SCRIPTS/find_usages.sh power_sum
   - 18 call sites identified
5. present proposal to user
6. user approves
7. rocq-prover executes the rename across 18 sites
8. rocq-auditor audits
9. atomic-commit
```

### Stage 4 — Quality pass per milestone

After completing Phase A (axiom interface tightened), before pushing:

```
/rocq:checkpoint
```

Gate flow:
```
1. python3 $ROCQ_SCRIPTS/admitted_analyzer.py pgg-smc/reconstruct/ \
            --format=summary
   → "12 Admitted remaining (3 in brings_curve.v, 9 elsewhere)"
2. bash $ROCQ_SCRIPTS/check_axioms.sh pgg-smc/reconstruct/brings_curve.v
   → "no non-standard axioms"  OR  "WARN: custom axiom 'bring_smooth' at line 87"
3. make -j1
   → build passes
4. .claude/audit/audit.sh on changed files     # NOTE: pgg's audit script is
                                                # at .claude/audit/audit.sh,
                                                # NOT .claude/audit/bin/audit.sh
                                                # (corrected per audit M1).
   → audit verdict (project-rule conformance)
5. report: ready-to-commit / blockers
```

For verbose algebraic proofs (Riemann-Hurwitz expansions tend to balloon):

```
/rocq:golf pgg-smc/reconstruct/brings_curve.v brings_curve_genus
```

`proof-golfer` subagent runs `find_golfable.py`, consults `proof-golfing-patterns.md`, proposes shortenings, tests via `rocq_step_multi`, then audit + commit. Per memory `feedback_audit_still_mandatory`, the audit gate fires regardless of which subagent wrote the edits.

If `check_axioms.sh` flagged a custom axiom:

```
/rocq:doctor   # confirm whether it's intended (e.g., Edge 1978 placeholder)
# then if it should be discharged:
You: "discharge bring_smooth using the smoothness proof in covering_scheme.v"
# → routes to axiom-eliminator subagent
```

### Stage 5 — Wind-down

After all Phase A milestones are checkpointed:

```
/rocq:checkpoint                                # final gate
/rocq:autoprove pgg-smc/reconstruct/ \
                --max-cycles=0 --dry-run         # report any remaining Admitted
/rocq:review --mode=batch pgg-smc/reconstruct/brings_curve.v
                                                # optional informational read-out
```

Then a normal `git push`. The `guardrails.sh` hook gates `git push`; bypass with `ROCQ_GUARDRAILS_BYPASS=1` after confirming locally. Per memory `feedback_guardrails_kept`, this is expected behavior.

---

## Tool-to-stage reference table

| Stage | Primary tool | Subagents involved | Reference docs |
|---|---|---|---|
| 0 Env/survey | `/rocq:doctor`, `/rocq:learn` | — | `~/.claude/refs/rocq-skills/cycle-engine.md` |
| 1 Drafting | `/rocq:draft` | (skill-only) | `~/.claude/refs/rocq-skills/admitted-filling.md` |
| 2 Proving (default) | `rocq-prover` agent, `/rocq-prove` | `rocq-auditor` | `cycle-engine.md`, `tactic-patterns.md` |
| 2 Proving (hard) | `rocq-expert-prover`, `/rocq:prove` | `admitted-filler-deep` | `tactics-reference.md` |
| 2 Proving (batch) | `/rocq:autoprove` | `admitted-filler-deep` | `cycle-engine.md` §Deep Mode |
| 3a Repair | (default routing → `proof-repair`) | `rocq-prover` | `compiler-guided-repair.md` |
| 3b Refactor | `/rocq:refactor` | `rocq-prover`, `rocq-auditor` | `tactics-reference.md` |
| 4 Golf | `/rocq:golf` | `proof-golfer`, `rocq-auditor` | `proof-golfing-patterns.md` |
| 4 Axiom check | `/rocq:checkpoint` | `axiom-eliminator` (if flagged) | `axiom-elimination.md` |
| 4 Gate | `/rocq:checkpoint` | `rocq-auditor` | (project rules at `.claude/audit/template/rules/`) |
| 5 Wind-down | `/rocq:checkpoint`, `/rocq:review`, `git push` | — | `cycle-engine.md` §Safety |

Helper scripts (under `~/.claude/scripts/rocq-skills/` or `$ROCQ_SCRIPTS`):

| script | when |
|---|---|
| `admitted_analyzer.py` | Stage 4 gate; also "where am I" mid-bulk |
| `check_axioms.sh` | Stage 4 gate; before pushing |
| `find_golfable.py` | Stage 4 golf |
| `find_usages.sh` | Stage 3b refactor reverse-dep |
| `parse_rocq_errors.py` | Stage 3a repair |
| `smart_search.sh` | Stage 3b refactor library leverage |

---

## What this plan does NOT cover

- **The actual mathematical content.** This plan is a workflow demonstration. The mathematical decisions (which axioms to keep, which to discharge, how aggressively to formalize Phase B) require domain choices the user makes during execution.
- **Phase B implementation.** Building multivariate polynomials, symmetric polynomials, projective space, and zero loci is its own multi-month project. The plan sketches the interface only.
- **Performance tuning.** Algebraic-geometry proofs can be RAM-heavy; the `-j1` rule (memory: `feedback_proving_routing` + `rocq-prover.md` safety rules) and the `rewrite !` ban on arithmetic lemmas apply throughout.
- **Connecting back to PGG-SMC security.** That's Phase C; depends on Phase A axiom interface + Phase B realization.

---

## Verification (how to confirm the plan works)

Since this plan is illustrative (not implementation), verification means running concrete artifact checks. **Do not trust self-confirming "✅" rows; verify by command.**

| Claim | How to verify |
|---|---|
| All 11 `/rocq:*` commands resolve | `claude plugin details rocq` — should list 11 skills (autoformalize, autoprove, checkpoint, doctor, draft, formalize, golf, learn, prove, refactor, review) + the core `rocq` skill |
| All 4 plugin subagents resolve | Same command — should list `proof-repair`, `axiom-eliminator`, `proof-golfer`, `admitted-filler-deep` |
| Helper scripts present | `ls ~/.claude/scripts/rocq-skills/` — six files |
| References present | `ls ~/.claude/refs/rocq-skills/` — fourteen files |
| Custom agents present | `ls ~/.claude/agents/` — should include `rocq-prover.md`, `rocq-expert-prover.md`, `rocq-auditor.md` (the plugin agents are NOT here; they live under `~/.claude/plugins/.../agents/`) |
| Bring's curve axiomatized in pgg | `grep -n "Bring" pgg-smc/reconstruct/curve_realisation.v` — should hit around line 25 |
| `genus_from_hurwitz` exists in covering_scheme | `grep -n "genus_from_hurwitz" pgg-smc/reconstruct/covering_scheme.v` — should hit; the original draft's `riemann_hurwitz_eq` does NOT |
| pgg's audit script path | `ls pgg-smc/../.claude/audit/audit.sh` — should exist at this exact path (not `bin/audit.sh`) |
| pgg's commands | `ls pgg-smc/../.claude/commands/` — should list `prove-lemma.md`, `rocq-apply-fixes.md`, `rocq-fix-plan.md`; these are distinct from the user-global `~/.claude/commands/rocq-prove.md` |
| pgg memory directory | `ls ~/.claude/projects/-Users-cheng-huiweng-Projects-coq-infotheo-pgg/memory/` — confirm exists; the Stage -1 migration writes here |
| MathComp absence claims | `find /Users/cheng-huiweng/Projects/coq/_opam/lib/coq/user-contrib -name 'projective*'` (empty), `... -name 'variety*'` (empty), `... -name 'symmetric*'` (empty) — confirms Phase B is from scratch |

Mathematical sanity checks (also verified during audit):
- Bring's curve has genus 4 ✓ (matches comment in `curve_realisation.v` lines 25-29)
- S_5 has order 120, A_5 (icosahedral rotation group) has order 60 ✓
- Bring's curve carries an S_5 action by coordinate permutation ✓
- The S_5/P^1 quotient has degree 120, NOT 60 ✓ (the 12+20+30 ramification multiset is the A_5 case, see `project_klein_cap_vs_riemann_hurwitz.md` in pgg memory)

To use this plan as a template for a different big-task formalization:
- Replace "Bring's curve" with your target
- Re-run Stage 0 surveys for your specific algebraic / mathematical domain
- Keep the stage structure and tool routing — they are domain-agnostic
- **Run Stage -1 memory migration first if the target project is not `infotheo-itp`**

---

## Critical files (referenced; would be modified if executed)

If Phase A were executed:
- `pgg-smc/reconstruct/brings_curve.v` — new file
- `pgg-smc/reconstruct/curve_realisation.v` — extended axiom interface
- `pgg-smc/reconstruct/covering_scheme.v` — Riemann-Hurwitz invocations may need new lemmas
- `pgg-smc/instances/s5/rigidity_s5_instance.v` — update to use new interface
- `pgg-smc/notes/20260521-brings-curve-survey.md` — Stage-0 survey note (new file)
- `pgg-smc/notes/bring_informal_phaseA.md` — informal source (new file)
- `_CoqProject` — register new file(s)

If Phase B were executed:
- `pgg-smc/algebraic_geometry/multivariate_poly.v` — new
- `pgg-smc/algebraic_geometry/symmetric_polynomials.v` — new
- `pgg-smc/algebraic_geometry/projective_space.v` — new
- `pgg-smc/algebraic_geometry/zero_locus.v` — new

If Phase C were executed:
- `pgg-smc/reconstruct/algebraic_rigidity.v` — connect realization to security argument
- `pgg-smc/security/*` — propagate the no-axiom discharge

**This plan does NOT execute any of these edits.** It is a workflow demonstration only.
