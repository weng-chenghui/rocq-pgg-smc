# Knowledge-audit pipeline: defending against bound-vs-value confusion

## Context

In the 2026-05-15 to 2026-05-17 poster conversation, the agent returned a
succession of wrong-but-tightening answers for the minimum genus of a
connected Riemann surface carrying `S_5 × S_5` as a Galois deck group:

1. `g = 3` (framework's `cd_genus`; violated Hurwitz's automorphism bound).
2. `g = 173` (Hurwitz floor `1 + |G|/84`; unreachable because `S_5 × S_5`
   is not a Hurwitz group, no order-7 element).
3. `g = 15,121` (fiber product `Bring × Bring`; an UPPER bound on
   `sigma^0(S_5 × S_5)`, not the value, which sits in an open interval
   `[361?, 15,121]` and is unpublished).

The user diagnosed the root pattern: at each step the agent **conflated a
bound with a value**, applying a constraint, treating the resulting bound
as the answer, and only revising when forced. The agent never enumerated
the full set of relevant constraints, never tracked lower and upper
bounds separately, and never abstained when the interval failed to close.

The user proposes an auditing pipeline that enforces:

- feasibility checks
- lower-bound and upper-bound tracking
- premises and constraints behind each bound
- soundness reasoning over the assembled bounds
- web search and math-knowledge-database lookup when needed

This plan extends the user's list with findings from the LLM-failure
literature, proposes a full pipeline architecture with per-domain
modularity, and incorporates an adversarial-audit pass before being
treated as final.

## 1. Evaluation of the user's points

The user's intuition matches established LLM failure modes. The
web-research subagent surfaced four named pathologies:

- **Anchoring bias** (Lou et al. 2024, ICLR HCAIR Workshop 2026
  arXiv:2412.06593 / 2505.15392): the first numeric or structural
  commitment biases all subsequent reasoning. Exactly the `g = 3` -> 173
  trajectory.
- **Premature convergence / single-hypothesis fixation** (Schmidgall et
  al. 2025, PMC12246145): clinical-reasoning literature documents
  identical pattern.
- **Sycophantic correction** (Sharma, Perez et al. 2024, ICLR
  arXiv:2310.13548): agent revises in the direction the user pushes,
  without independent verification. Each correction in the conversation
  was triggered by user pushback rather than the agent's own audit.
- **Abstention collapse under reasoning fine-tuning** (Wen et al. 2025,
  TACL aclanthology 2025.tacl-1.26): ~24% degradation in abstention.
  Matches the agent's failure to say "the value is open in `[361?, 15,121]`"
  rather than committing to 15,121.

Existing architectures relevant to mitigation:

- **SelfCheckGPT** (Manakul, Liusie, Gales 2023, EMNLP, arXiv:2303.08896)
  -- self-consistency sampling on numeric outputs.
- **Chain-of-Verification** (Dhuliawala et al. 2024, ACL Findings,
  arXiv:2309.11495) -- generates verification questions and answers
  before committing.
- **Tree of Thoughts** (Yao et al. 2023, NeurIPS, arXiv:2305.10601) --
  branching reasoning with backtracking.
- **ToRA** (Gou et al. 2024, ICLR, arXiv:2309.17452) -- mandatory
  tool delegation for verifiable subroutines.
- **Process Reward Models** (Lightman et al. 2023, arXiv:2305.20050)
  -- step-level grading of reasoning transcripts.

The user's points make sense. They cover the core epistemic discipline
that the failure case violated. Five literature-derived additions
extend the list (incorporated into Section 2).

## 2. Extended pipeline requirements

The pipeline must enforce the following discipline at every claim
intake:

1. **Claim-type classification.** Is the question asking for an exact
   value, a bound, an existence statement, a classification, or an open
   problem? Different types demand different evidence.
2. **Constraint enumeration.** For the claim's domain, list every
   theorem or constraint that might apply, not just the first one the
   agent thinks of. Drawn from a curated per-domain catalogue.
3. **Dual-bound ledger.** Track lower bounds and upper bounds
   separately. Each entry carries `{type, value, source, premises,
   tightness-witness}`.
4. **Premise audit.** For each constraint, verify its hypotheses hold
   in the situation. Hurwitz's bound applies only at `g >= 2`; the
   `(2,3,7)` Hurwitz floor is attained only for Hurwitz groups; etc.
5. **Tightness witness.** A bound is reported as the answer only if a
   witness shows the bound is attained for the specific instance, not
   just for the generic theorem.
6. **Aggregation.** The reported answer is the interval `[max(lower),
   min(upper)]`. A single value is reported only when `max(lower) =
   min(upper)`.
7. **Abstention.** If the interval is open beyond a tolerance threshold,
   the agent must abstain or report the interval, not commit to a
   value. Threshold is part of the per-domain config.
8. **Sycophancy guard.** On user pushback, the agent regenerates the
   entire bound ledger from scratch, not by editing the prior chain.
   Anchoring bias is explicitly prevented.
9. **Mandatory tool delegation.** For known math objects (group orders,
   automorphism groups, Hurwitz status, strong symmetric genus,
   well-studied curves), the pipeline must consult an external
   database (GAP, Magma, LMFDB, Conder catalogue, Paulhus's database,
   OEIS) before committing.
10. **Web search for primary sources.** Every citation in the final
    output must be web-verifiable. Hallucinated citations are caught at
    this stage.
11. **Step-level transcript.** The full bound-ledger derivation is
    preserved as a transcript, so a later auditor or PRM can grade each
    step.
12. **Domain dispatch.** Different domains have different constraint
    catalogues and different abstention thresholds. The pipeline picks
    the right module per-claim.

## 3. Proposed pipeline architecture

The pipeline lives at `.claude/knowledge-audit/`, parallel to the
existing rocq-audit at `.claude/audit/` (which audits code style and is
left untouched). Per-domain modules live in subdirectories so adding a
new domain is purely additive.

### Directory layout

```
.claude/knowledge-audit/
├── README.md
├── config.yaml                 # daily/per-claim token caps, model selection
├── bin/
│   ├── audit.sh                # entry: `audit.sh "<claim text>"`
│   ├── classify.py             # Stage 0: claim type + domain dispatch
│   ├── enumerate-constraints.py# Stage 1: agent run with domain catalogue
│   ├── ledger.py               # Stage 2: bound book-keeping
│   ├── premise-audit.py        # Stage 3: premise verification
│   ├── aggregate.py            # Stage 4: interval aggregation
│   ├── tool-delegate.py        # Stage 5: GAP/Magma/LMFDB/OEIS calls
│   ├── web-verify.py           # Stage 6: citation verification
│   ├── adversary.py            # Stage 7: adversarial recheck
│   └── format-report.py        # Stage 8: final output
├── domains/
│   ├── README.md               # how the dispatcher picks a domain
│   ├── math/
│   │   ├── algebraic-geometry/
│   │   │   ├── constraints.yaml    # R-H, Hurwitz, signatures, Singleton
│   │   │   ├── databases.yaml      # LMFDB, Conder, Paulhus URLs/APIs
│   │   │   ├── premises.md         # hypotheses for each constraint
│   │   │   └── abstention.yaml     # interval-width thresholds
│   │   ├── combinatorics/
│   │   ├── number-theory/
│   │   └── group-theory/
│   ├── cs-theory/
│   │   ├── complexity/
│   │   └── coding-theory/
│   ├── history/
│   └── science/
├── prompts/
│   ├── auditor.md              # system prompt: dual-bound ledger discipline
│   ├── adversary.md            # find missing constraints, hallucinated citations
│   └── tool-instructions.md
├── runs/
│   └── <YYYYMMDD-id>/
│       ├── claim.txt
│       ├── classification.json
│       ├── ledger.json         # lower/upper bounds + premises + witnesses
│       ├── premise-audit.json
│       ├── tool-results.json   # database/web responses
│       ├── adversary-report.md
│       ├── verdict.json        # final interval or value or abstention
│       └── transcript.md       # full step-level reasoning trace
└── central-state/
    ├── known-failures.ndjson   # log of past wrong answers + diagnoses
    └── domain-config.json
```

### Pipeline stages

**Stage 0: Intake (`classify.py`).**
Reads the claim text, decides:
- Claim type: `exact-value | bound | existence | classification | open`.
- Domain: dispatch to `domains/<domain>/<subarea>/`.
- Initial extracted quantity (if any).
Output: `classification.json`.

**Stage 1: Constraint enumeration (`enumerate-constraints.py`).**
Reads `domains/<...>/constraints.yaml` into the agent's context. Asks the
agent to list every constraint that COULD apply to the claim. The agent
must enumerate, not pick the first one. Output: a list of
candidate-constraint identifiers.

**Stage 2: Bound ledger (`ledger.py`).**
For each candidate constraint, compute the bound it gives. Record
`{constraint, type=lower/upper, value, source-citation, premises-list,
tightness-claim}`. No constraint may be skipped without an entry. Output:
`ledger.json`.

**Stage 3: Premise audit (`premise-audit.py`).**
For each entry in the ledger, verify the premises hold for THIS
situation. Example checks: does the group have an order-7 element (for
`(2,3,7)` Hurwitz)? Does the curve genus satisfy `g >= 2` (for the
automorphism bound)? Output: `premise-audit.json` with pass/fail per
entry.

**Stage 4: Aggregation (`aggregate.py`).**
Reads only ledger entries whose premises passed. Computes
`L = max(passing lower bounds)`, `U = min(passing upper bounds)`. Three
outcomes:
- `L = U`: exact value.
- `L < U`: open interval, return `[L, U]`.
- `L > U`: inconsistency, flag and abort.
Output: `aggregated.json`.

**Stage 5: Tool delegation (`tool-delegate.py`).**
For known database queries (group orders from GAP, surface entries
from LMFDB, Hurwitz status from Conder), invoke the external tool and
cross-check the ledger. Catches cases where the agent's enumeration
missed an entry in the database.

**Stage 6: Web verification (`web-verify.py`).**
Web-fetches each citation. Confirms the paper exists, the authors and
venue match, and the cited section actually states the claim. Catches
hallucinated citations.

**Stage 7: Adversarial recheck (`adversary.py`).**
A separate agent reads the ledger and verdict and tries to find:
- A missing constraint.
- A premise that was waved through.
- A tightness witness that doesn't apply.
- A citation that doesn't say what the agent claims.
Output: `adversary-report.md` with action items.

**Stage 8: Final report (`format-report.py`).**
Emits the verdict using the rigid template:

```
Question: <verbatim>
Domain: <math/algebraic-geometry>
Type: <bound | value | existence | open>
Lower bound: L  -- from <theorem>, premises: <list>, tightness: <witness or "none">
Upper bound: U  -- from <theorem>, premises: <list>, tightness: <witness or "none">
Reported answer: <interval [L, U] | "exactly L" | "open">
Caveats: <list>
Citations: <web-verified bibliography>
```

### Domain dispatch

`domains/README.md` documents the dispatcher rules:

- Each domain directory contains `constraints.yaml`, `premises.md`,
  `databases.yaml`, and `abstention.yaml`.
- Sub-domains are nested directories. The classifier picks the deepest
  matching subdirectory.
- A new domain is added by creating a directory and populating four
  files. No pipeline-script changes are needed.
- Cross-domain claims trigger a "multi-domain" run that loads multiple
  catalogues; this is rare and explicitly flagged.

### Switching domains

- Domain detection runs in `classify.py` via a keyword + entity
  classifier. Math claims with group-theoretic vocabulary route to
  `math/group-theory/`; with curve vocabulary to
  `math/algebraic-geometry/`.
- If the classifier abstains (no domain matches with high confidence),
  the pipeline reports "out-of-scope" and the agent is required to
  answer with a manual epistemic disclaimer instead of running the
  audit.

### Hook into Claude Code

- Manual: `/knowledge-audit "<claim>"` slash command invokes
  `bin/audit.sh`.
- Automatic: an optional `PreToolUse` hook can run the audit on agent
  outputs that contain a numeric claim. Default off, to avoid token
  burn on every message.

## 4. Adversarial audit (to be run as Phase 4 of this plan workflow)

After the initial plan is written, an adversarial subagent will read it
and report:

- Missing pipeline stages.
- Wrong stage ordering.
- Domain catalogues that are infeasible to maintain.
- Tool-delegation gaps.
- Cases where the pipeline would not have caught the original `S_5 × S_5`
  failure.
- Cases where the pipeline would falsely flag a correct answer.

Findings are integrated into Section 5 below.

## 5. Adversarial-audit fixes (incorporated)

The adversarial subagent flagged ten concrete issues. Each fix is folded
into the architecture above; this section records the issue, the fix,
and the section it touches.

**A1. Parametric constraints (touches Section 2 item 3, Section 3 Stage 2).**
The original schema would record one "Hurwitz lower bound" entry,
collapsing all signatures into a single number. Fix: ledger entries
become parametric. A constraint with a free parameter (signature,
character, divisor type) enumerates admissible parameter values and
yields one entry per value. Reported lower bound is the MIN over
admissible parameters; reported upper bound is the MAX (or attained
upper, per construction).

**A2. Three-part premise audit (Section 3 Stage 3).**
Original premise audit only checked theorem hypotheses. The original
`g = 173` failure passes hypothesis check; what fails is "G admits a
`(2,3,7)`-generating triple," a separate realisability condition. Fix:
split Stage 3 into

- **3a. Theorem hypotheses** (e.g., `g >= 2` for the Hurwitz aut bound).
- **3b. Realisability of the parameter for THIS instance** (e.g., G has
  elements of required orders; the character / surjectivity-of-Hurwitz-map
  condition holds).
- **3c. Tightness witness** (a citation that the bound is attained for
  THIS instance).

A ledger entry is admitted to Stage 4 aggregation only if 3a and 3b
pass. 3c is required only to convert the entry into a "value
candidate"; without 3c it remains a bound.

**A3. Triviality bypass (Section 3 Stage 0).**
The classifier emits a `triviality_score` in `[0, 1]`. Below threshold
(default 0.2 for "single canonical lookup" claims like `|S_5| = 120`),
the pipeline runs Stage 5 only (one tool call), bypasses enumeration,
and logs the bypass to `central-state/`. A per-claim token cap and a
fast-path counter prevent token burn on routine claims.

**A4. Classifier with ranked confidence (Section 3 "Switching domains").**
Original "keyword + entity classifier" was underspecified. Fix: emit a
ranked list with confidence scores. If top-2 confidences are within a
delta (default 0.15), run BOTH domain catalogues and union the
constraints. On no-match, route to `domains/_generic/`, which holds
only "abstain and require web verification."

**A5. Tool availability matrix (Section 3 Stage 5).**
Magma is paid; GAP needs install; LMFDB has gaps. Fix:
`databases.yaml` per domain declares
`{tool, availability, fallback, coverage-domain}`. Missing tools yield
a degraded-mode warning logged into the verdict, never silent skip.
`bin/tool-delegate.py` implements an adapter pattern over
`lmfdb-api`, `gap-cli`, `magma-stub` (returns "unavailable"),
`oeis-api`, `conder-static-table`.

**A6. Catalogue-completeness audit (Section 3 `constraints.yaml`).**
Catalogue gaps cannot be self-detected by the pipeline itself. Fix:
introduce `bin/audit-catalogue.py`. Every entry in
`central-state/known-failures.ndjson` records the missing constraint
name; the audit refuses to close the failure until a catalogue PR
adds the entry. Catalogues cite a survey as coverage baseline.
Algebraic-geometry baseline: Breuer 2000, *Characters and Automorphism
Groups of Compact Riemann Surfaces*, LMS Lecture Note Series 280.
Catalogue review is triggered when the cited survey edition changes.

**A7. Typed pushback channel (Section 2 item 8).**
Original "regenerate from scratch on pushback" loses legitimate
user-supplied premises. Fix: pushback enters a typed channel
`{new_fact, citation, counter_example, vibe_only}`. Only `vibe_only`
triggers full regenerate; `new_fact` and `citation` are added as
ledger entries with Stage 3 re-run incrementally; `counter_example`
forces Stage 7 adversary re-run with the counter-example as input.
Reference: Sharma et al. 2024, arXiv:2310.13548, Section 5
(calibrated revision).

**A8. Citation-NLI (Section 3 Stage 6).**
"Confirms the paper exists" is necessary but insufficient. Fix:
`bin/web-verify.py` extracts a 200-word window around each citation
anchor. `bin/citation-nli.py` invokes a separate agent (different
model, fresh context) with ONLY the claim plus the window, and
returns `{entails, contradicts, unrelated}` per claim. The verdict is
blocked if any citation returns `contradicts` or `unrelated`.
Reference for the faithfulness metric pattern: Es et al. 2024,
*RAGAS*, arXiv:2309.15217.

**A9. PRM-graded transcript (Section 3 Stage 7).**
The original adversary was free-form. Fix: Stage 7 returns a step-by-step
PRM-style grading conforming to a JSON schema:

```
{
  "steps": [
    {"step_id": "S2.entry-3", "verdict": "correct|suspect|wrong", "reason": "..."},
    ...
  ]
}
```

Verdict is blocked if any `wrong` is present. A configurable threshold
(default 2) on `suspect` count also blocks. Reference: Lightman et al.
2023, *Let's Verify Step by Step*, arXiv:2305.20050.

**A10. DAG instead of serial pipeline (Section 3 stages).**
Stages 5 (tool delegation) and 6 (web verification) are independent of
Stages 2-4 once constraints are listed; Stage 7 (adversary) depends on
the ledger and on Stages 5-6 but not on each other. Fix: declare the
pipeline as a DAG.

```
                ┌─> Stage 3 ─┐
                │            │
Stage 0 -> 1 -> 2            ├─> Stage 4 ─┐
                │            │            │
                ├─> Stage 5 ─┤            ├─> Stage 7 -> Stage 8
                │            │            │
                └─> Stage 6 ─┘            │
                                          │
```

Stage 7 joins on Stages 4, 5, 6. Parallel execution roughly halves
cold-run latency. The DAG is encoded in `bin/audit.sh` (or a small
Makefile-style dependency declaration).

### How the fixed pipeline catches the original failure

Trace on "What is `sigma^0(S_5 × S_5)`?":

- Stage 0: classifier routes to `math/algebraic-geometry/`,
  `triviality_score = 0.05` (not a lookup claim), no bypass.
- Stage 1: enumerator lists Riemann-Hurwitz, Hurwitz aut bound,
  Fuchsian-signature realisation, fiber-product construction,
  Greenberg's realisation theorem.
- Stage 2 (parametric): for Fuchsian-signature realisation, enumerates
  admissible `(p, q, r)` with `p, q, r ∈ orders(S_5 × S_5) =
  {1,2,3,4,5,6,10,12,15,20,30}`, yielding entries for `(2,3,7) [order-7
  inadmissible]`, `(2,3,8) [order-8 inadmissible]`, `(2,4,5) [admissible,
  g >= 361]`, ... and a separate entry for the fiber-product
  construction with `g = 15,121`.
- Stage 3a-c: rejects `(2,3,7)` and `(2,3,8)` at 3b (no order-7 or
  order-8 element). For `(2,4,5)`, 3a/3b pass but 3c (tightness) returns
  "no witness for generation by (2,4,5)-triple of S_5 × S_5", so the
  entry stays as a lower-bound CANDIDATE only.
- Stages 5+6: tool delegation queries LMFDB and Conder for any S_5xS_5
  entry; receives "no match"; logs that no named curve realises the
  group; web verification confirms Conder URL and Paulhus 2022 paper.
- Stage 4: lower = max(361 conditional, ...) = 361 conditional;
  upper = min(15,121) = 15,121; interval `[361, 15,121]` is open.
- Stage 7: adversary verifies the ledger; finds no missing constraint;
  confirms `(2,3,7)` and `(2,3,8)` rejection.
- Stage 8: reports `interval [361, 15,121]` with both ends labelled
  conditional; abstains from a single value.

This is the verdict that should have been delivered the first time.

## Critical files (to be created)

- `.claude/knowledge-audit/` directory tree as in Section 3.
- `bin/` scripts including (post-fixes): `classify.py`,
  `enumerate-constraints.py`, `ledger.py`, `premise-audit.py`,
  `aggregate.py`, `tool-delegate.py` (adapter pattern from A5),
  `web-verify.py`, `citation-nli.py` (A8), `adversary.py` (PRM-graded
  per A9), `audit-catalogue.py` (A6), `format-report.py`.
- Initial domain catalogue: `domains/math/algebraic-geometry/constraints.yaml`
  populated with the failure-case constraints: Riemann-Hurwitz, Hurwitz
  automorphism bound (parametric on signature per A1), Fuchsian
  signature admissibility, strong-symmetric-genus bounds, Greenberg's
  realisation theorem, fiber-product compositum genus.
- `domains/_generic/` (A4): minimal abstain-and-web-verify catalogue
  for unclassified claims.
- README files at the root and in `domains/` documenting the dispatcher
  and the catalogue-completeness audit cycle.
- `central-state/known-failures.ndjson` seeded with the S_5 × S_5
  failure for the regression test.

## Verification

1. **Regression test on the failure case.** Run the pipeline on the
   claim "What is `sigma^0(S_5 × S_5)`?". Expected verdict:
   `Reported answer: [361 conditional, 15,121]`, with both bounds and
   their premises listed, and a "value open" abstention. The pipeline
   must NOT commit to any of `3, 173, 15,121`. See Section 5's
   "How the fixed pipeline catches the original failure" trace.
2. **Smoke test on a positive case.** Run on the claim "What is
   `sigma^0(S_5)`?". Expected verdict: `Reported answer: exactly 4`,
   citing Bring's curve as the tightness witness and Conder's catalogue
   for confirmation.
3. **Triviality bypass test (A3).** Run on a routine claim with a
   single canonical lookup (e.g., "How many elements does `S_5` have?").
   Expected: `triviality_score >= 0.8`, Stage 5 only, single GAP call,
   `Reported answer: exactly 120`, total cost under one Stage-5 token
   budget. No enumeration or premise audit runs.
4. **Domain switch test (A4).** Run a non-math claim (e.g., "When was
   the first paper on inverse Galois published?"). The dispatcher
   should route to `history/`, or to `domains/_generic/` if `history/`
   is empty, with the "abstain and web-verify" catalogue.
5. **Pushback test (A7).** After Stage 8 emits a verdict, simulate a
   user pushback `{type: counter_example, content: ...}`. The pipeline
   should add the counter-example as a ledger entry and re-run Stage 7
   incrementally, not regenerate from scratch.
6. **Catalogue audit (A6).** Run `audit-catalogue.py` against
   `central-state/known-failures.ndjson` with the seeded
   `S_5 × S_5` entry. The audit should refuse to close the failure
   until `constraints.yaml` lists "Fuchsian-signature realisation".
7. **Adversarial-audit incorporation (this plan's Section 5).** All
   ten issues from Phase 4 have been folded into the architecture
   (A1-A10). No outstanding pipeline-design flaw.

## Out of scope

- Implementing the pipeline scripts (this plan only designs the
  architecture).
- Populating the full domain catalogue beyond `math/algebraic-geometry/`.
- Integrating with the existing rocq-audit pipeline (separate concern).
- Replacing existing agent behaviour without an opt-in flag.
