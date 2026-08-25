⏺ ═════════════════════════════════════════════════════════════════════════
    PHASE 1 — DESIGN  (Superpowers plugin: brainstorming + writing-plans)
  ═════════════════════════════════════════════════════════════════════════

    ┌────────────────────────────────────────────┐
    │ INPUT:  "I want to formalize Bring's curve" │
    │         (vague, no concrete tasks)          │
    └──────────────────┬─────────────────────────┘
                       │
                       ▼
             ╔══════════════════════╗
             ║   /brainstorm        ║  ← auto-triggers per skill frontmatter
             ║                      ║     (HARD-GATE: refuses to write code
             ║   Superpowers skill  ║      until you approve a design)
             ╚══════════╤═══════════╝
                        │
                        │  ① explores context: reads infotheo-pgg layout,
                        │     finds pgg-smc/reconstruct/curve_realisation.v,
                        │     surveys MathComp's algebra coverage
                        │
                        │  ② asks ONE question at a time:
                        │     Q: "Is this Phase A (axiom-tightening),
                        │         Phase B (concrete realization), or both?"
                        │     → you answer: Phase A
                        │     Q: "Optimize for landing in PGG-SMC fast,
                        │         or for a reusable AG layer?"
                        │     → you answer: PGG-SMC fast
                        │     Q: "S_5 action: structural or computational?"
                        │     → you answer: structural for now
                        │
                        │  ③ proposes 2-3 axiom-interface designs:
                        │     A. minimal: just enrich `realised_by_curve`
                        │     B. medium: + record genus + S_5 action
                        │     C. heavy: + defining-ideal placeholder
                        │     → you pick B
                        │
                        │  ④ presents design in sections, you approve each
                        │
                        ▼
    ┌─────────────────────────────────────────────────────────────┐
    │ OUTPUT:  pgg-smc/notes/2026-05-21-brings-curve-design.md     │
    │          - Goal: enrich realised_by_curve for Bring's curve  │
    │          - Approach B (chosen)                               │
    │          - Decomposition into sub-projects:                  │
    │            • S1: extend realised_by_curve record fields      │
    │            • S2: state brings_curve_genus axiom              │
    │            • S3: prove brings_curve_S5_action faithful       │
    │            • S4: rewire rigidity_s5_instance.v               │
    │          - Out of scope: multivariate polynomials (Phase B)  │
    └──────────────────────────────┬──────────────────────────────┘
                                   │
                                   ▼
                         ╔════════════════════╗
                         ║   /writing-plans   ║  ← Superpowers skill
                         ╚═════════╤══════════╝
                                   │  converts design doc → ordered task list
                                   ▼
    ┌─────────────────────────────────────────────────────────────┐
    │ OUTPUT:  implementation plan (concrete task list):           │
    │          T1: add `cd_S5_action` field to realised_by_curve   │
    │          T2: state brings_curve_genus : … = 4                │
    │          T3: prove brings_curve_S5_action via permutation    │
    │          T4: update rigidity_s5_instance.v to use new fields │
    │          T5: discharge old `realised_by_curve` axiom         │
    └──────────────────────────────┬──────────────────────────────┘
                                   │
  ═════════════════════════════════╪═══════════════════════════════════════
    PHASE 2 — PLAN MODE  (Claude Code built-in)
  ═════════════════════════════════╪═══════════════════════════════════════
                                   │
                                   ▼
                         ╔══════════════════════╗
                         ║   Plan Mode          ║  ← Shift+Tab to enter
                         ║   (Shift+Tab toggle) ║
                         ╚═════════╤════════════╝
                                   │
                                   │  ① Phase 1: Explore — runs Explore
                                   │     subagents to inventory files cited
                                   │     in the task list
                                   │
                                   │  ② Phase 2: Design — Plan subagent
                                   │     refines task-by-task implementation
                                   │
                                   │  ③ Phase 3: Review — clarify with user
                                   │
                                   │  ④ Phase 4: Write plan file
                                   │
                                   │  ⑤ Adversarial audit
                                   │     (memory: feedback_adversarial_audit
                                   │      _before_exit_plan_mode)
                                   │
                                   │  ⑥ ExitPlanMode
                                   ▼
    ┌─────────────────────────────────────────────────────────────┐
    │ OUTPUT:  ~/.claude/plans/<session-slug>.md                   │
    │          finalized, audited, ready for execution             │
    └──────────────────────────────┬──────────────────────────────┘
                                   │
  ═════════════════════════════════╪═══════════════════════════════════════
    PHASE 3 — EXECUTION  (the merged rocq-skills + custom-agents stack)
  ═════════════════════════════════╪═══════════════════════════════════════
                                   │
                                   ▼
                  ╔══════════════════════════════════╗
                  ║   rocq-prover  dispatched        ║
                  ║   (default per memory routing)   ║
                  ╚═════════════════╤════════════════╝
                                    │
                                    │  FIRST ACTION on a multi-stage task:
                                    │  consult the TOOL-USE DOC
                                    │
                                    ▼
                ┌─────────────────────────────────────────────┐
                │ ~/.claude/refs/local/                        │
                │   merged-flow-execution-playbook.md          │
                │   (the playbook — prescribes which tool at   │
                │    which stage, cited from rocq-prover.md)   │
                └────────────────────┬────────────────────────┘
                                     │ reads stage table, follows routing
                                     ▼
    ┌──────────────────────────────────────────────────────────────┐
    │ STAGE 0  Survey & env                                         │
    │   /rocq:doctor       (env / MCP / opam check)                 │
    │   /rocq:learn        (mode=repo + mode=library)               │
    │ Output: pgg-smc/notes/2026-05-21-brings-curve-survey.md       │
    └──────────────────────────┬───────────────────────────────────┘
                               │
    ┌──────────────────────────▼───────────────────────────────────┐
    │ STAGE 1  Drafting                                             │
    │   /rocq:draft --source=…phaseA.md --out=brings_curve.v        │
    │ Output: skeleton .v file with Admitted bodies for T1..T5      │
    └──────────────────────────┬───────────────────────────────────┘
                               │
    ┌──────────────────────────▼───────────────────────────────────┐
    │ STAGE 2  Per-task proof cycles  ← BULK OF THE WORK            │
    │                                                               │
    │  ┌──── cycle engine (per Admitted) ──────────────────────┐    │
    │  │                                                       │    │
    │  │   Plan ──► Work ──► Checkpoint ──► Review ──► Replan  │    │
    │  │     ▲                                          │      │    │
    │  │     └──────────────  Continue  ─────────────── ┘      │    │
    │  │                                                       │    │
    │  │  Routing per task:                                    │    │
    │  │   T1 (struct change)  → rocq-prover                   │    │
    │  │   T2 (axiom state)    → rocq-prover                   │    │
    │  │   T3 (S_5 faithful)   → rocq-expert-prover (hard)     │    │
    │  │   T4 (mechanical)     → /rocq:autoprove batch         │    │
    │  │   T5 (axiom discharge)→ axiom-eliminator              │    │
    │  └───────────────────────────────────────────────────────┘    │
    │                                                               │
    │  Review sub-phase ALWAYS → rocq-auditor Stage 2 (mandatory)   │
    │  Atomic commit per closed task (memory: feedback_atomic_tasks)│
    └──────────────────────────┬───────────────────────────────────┘
                               │
    ┌──────────────────────────▼───────────────────────────────────┐
    │ STAGE 3  Maintenance (fires on-demand, parallel to Stage 2)  │
    │   build broke after rename       → proof-repair subagent     │
    │   library-leverage opportunity   → /rocq:refactor            │
    └──────────────────────────┬───────────────────────────────────┘
                               │
    ┌──────────────────────────▼───────────────────────────────────┐
    │ STAGE 4  Quality pass (per milestone)                         │
    │   /rocq:checkpoint  — gate: admits + axioms + build + audit  │
    │   /rocq:golf        — shorten verbose proofs (proof-golfer)  │
    │   axiom-eliminator  — only if check_axioms.sh flagged one    │
    └──────────────────────────┬───────────────────────────────────┘
                               │
    ┌──────────────────────────▼───────────────────────────────────┐
    │ STAGE 5  Wind-down                                            │
    │   /rocq:checkpoint  (final gate)                              │
    │   /rocq:review      (informational read-out, NOT a substitute │
    │                      for rocq-auditor)                        │
    │   git push          (guardrails.sh prompts; bypass once with  │
    │                      ROCQ_GUARDRAILS_BYPASS=1)                │
    └──────────────────────────┬───────────────────────────────────┘
                               │
                               ▼
                          ✓ committed work in infotheo-pgg

  Reading the diagram

  Three boundaries split the flow into the three roles of the merged stack:

  ┌─────────────────────────┬────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
  │        boundary         │                                                        what changes                                                        │
  ├─────────────────────────┼────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
  Reading the diagram

  Three boundaries split the flow into the three roles of the merged stack:

  ┌─────────────────────────┬────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
  │        boundary         │                                                        what changes                                                        │
  ├─────────────────────────┼────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
  │ Phase 1 → 2             │ Vague idea → ordered task list. The Superpowers skill is the only thing that can do this; Plan Mode assumes tasks already  │
  │                         │ exist.                                                                                                                     │
  ├─────────────────────────┼────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
  │ Phase 2 → 3             │ Task list → finalized plan file. Plan Mode runs Explore agents, drafts the plan, audits it, then ExitPlanMode triggers     │
  │                         │ execution.                                                                                                                 │
  ├─────────────────────────┼────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
  │ Phase 3 (start) → Stage │ Executing agent → must read the playbook before doing work. The agent's own system prompt cites the playbook path.         │
  │  0                      │                                                                                                                            │
  └─────────────────────────┴────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘

  The two docs and what each contains

  ┌───────────────────────┬────────────────────────────────────────────────────────────────────┬─────────────────────────────────────────────────────────┐
  │          doc          │                             located at                             │                     when consulted                      │
  ├───────────────────────┼────────────────────────────────────────────────────────────────────┼─────────────────────────────────────────────────────────┤
  │ Brainstorm design doc │ pgg-smc/notes/YYYY-MM-DD-<topic>-design.md (or                     │ one-shot output of /brainstorm; input to /writing-plans │
  │                       │ docs/superpowers/specs/ default)                                   │                                                         │
  ├───────────────────────┼────────────────────────────────────────────────────────────────────┼─────────────────────────────────────────────────────────┤
  │ Plan file             │ ~/.claude/plans/<slug>.md                                          │ one-shot output of Plan Mode; ephemeral after           │
  │                       │                                                                    │ ExitPlanMode                                            │
  ├───────────────────────┼────────────────────────────────────────────────────────────────────┼─────────────────────────────────────────────────────────┤
  │ Tool-use doc /        │ ~/.claude/refs/local/merged-flow-execution-playbook.md             │ permanent instruction set; consulted by every executing │
  │ execution playbook    │                                                                    │  agent at the start of any multi-stage task             │
  └───────────────────────┴────────────────────────────────────────────────────────────────────┴─────────────────────────────────────────────────────────┘

  The brainstorm doc and plan file are task-specific (one per project per task). The playbook is universal (one for all tasks of this shape).

  Key insight you were missing

  /brainstorm and Plan Mode are not the same step. They do different work:

  - /brainstorm answers: "what are the concrete tasks?"
  - Plan Mode answers: "how do I execute each task, in what order, with what files?"

  Without the brainstorm step, you arrive at Plan Mode with a vague target, and Plan Mode is forced to invent tasks (which is what happened earlier in this
  conversation when I improvised a Bring's curve plan from a one-line user prompt). The brainstorm step elicits the decisions that turn vague → concrete.

  The playbook then says: once you have a concrete plan, here is how to use the tools to execute it. It does not replace the cycle engine or the audit gates
  — it organizes them into a stage-by-stage program with explicit routing.
