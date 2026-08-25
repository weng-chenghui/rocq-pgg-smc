# Rocq audit pipeline — architecture and value

## Context

AI-assisted Rocq development tends to produce proofs that close but drift
from MathComp and Infotheo style conventions. The drift is systematic:
tactic choices fall back to vanilla Coq primitives, lemma names grow
extra components that describe the proof rather than the role, preceding
comments are either absent or reduce to a single English sentence, and
hypotheses accumulate in `Section` blocks without a tight coupling to the
entity that needs them. Peer reviewers catch these issues repeatedly.
This note describes the pre-commit audit pipeline we built to catch the
same class of issues before a human reviewer ever sees the diff, and
documents the two commits that served as the trial run.

## Architecture

The pipeline runs on every `git commit` that stages at least one `.v`
file. It is installed as a Claude Code `PreToolUse(Bash)` hook plus a
native `.git/hooks/pre-commit` symlink, so both tool-initiated and
terminal-initiated commits are gated.

A commit moves through four phases in series.

**Tier 0 extraction.** Reads `git diff --cached`, identifies the touched
`.v` files, and expands each touched line to its enclosing Rocq entity.
Each entity carries its kind (`Lemma`, `Theorem`, `Definition`, and so
on), name, declaration header, full body, the list of `touched_lines`
within the staged diff, and the immediately-preceding comment block.
This manifest is a single JSON file consumed by every later phase.

**Stage 1 regex.** A deterministic shell pass driven by `fast_pattern`
and `fast_check` fields in the rule catalog. Rules in this phase use the
RE2 engine through Python's `re` module so no rule can cause catastrophic
backtracking. Stage 1 catches literal violations that need no semantic
reasoning, for example a line that matches `^\s*pose proof\b` or a
`Lemma` declaration whose identifier contains five or more underscore
components without a canonical MathComp suffix at the tail. Stage 1 is
fast enough to finish in under two seconds on any realistic commit.

**Stage 2 agent audit.** A Claude subagent named `rocq-auditor` runs
with Read, Grep, and Glob tools only. It receives the Tier 0 manifest,
the Stage 1 findings, the full enabled rule catalog, and the contents of
`AUTHORITY.md`. For each touched entity and each enabled rule, the agent
produces a finding that includes a closeness-to-target verdict
(`idiomatic`, `near`, `far`), an evidence quote, a prose explanation
citing authority entries, and a fix sketch. Stage 2 chunks the entities
at an adaptive size and runs the chunks in parallel through a thread
pool whose worker count scales with the chunk count up to a configurable
cap. A soft wall-clock budget emits a warning at eighty percent and
stops dispatching at one hundred percent, so a very large commit
degrades to a partial audit rather than stalling.

**Tier K kernel grounding.** Any Stage 2 finding that claims something
provable against the Rocq kernel (for example "hypothesis X is unused"
or "the goal closes at line N") carries a `kernel_contract` field.
Tier K opens a rocq-mcp session and verifies the claim against the real
proof state. Refuted claims are dropped before the report reaches the
operator. This is how the agent is prevented from hallucinating
semantic conclusions.

The four phase outputs are merged by a single script that renders
`.claude/audit/reports/latest.md` and computes the exit code. Stage 1
errors and Stage 2 errors both block the commit at exit code 2.
Warnings are reported but do not block.

## Division of labour

| Step | Who does it | Why |
|---|---|---|
| Hook dispatcher for `git commit` | shell | deterministic, cheap, runs once per commit |
| Entity extraction and diff expansion | shell plus Python AST scan | parsing Rocq headers and body spans is a regular task |
| Catalog JSON-schema validation | Python with `jsonschema` | keeps rule authors from shipping broken rules |
| Fixture and snapshot self-tests | Python plus shell | required in CI-parity contexts and in human-driven lint runs |
| Stage 1 regex rules | shell plus Python regex | literal violations do not need a model |
| First-attempt oscillation-log truncation and age-based reap | shell | pure state hygiene |
| Token budget, cost cap, adaptive chunk size, parallel pool | Python | control flow benefits from a real programming language |
| `ROCQ_AUDIT_BYPASS=fast` short-circuit | shell | skips Stage 2 entirely for emergencies |
| Stage 2 agent reasoning about closeness-to-target | Claude subagent | fuzzy comparison between code and an idiomatic target requires language reasoning that regex cannot do |
| Grep-verified consumer citations in comments | Claude subagent using Grep | the agent proposes a downstream consumer and the subagent itself confirms or refutes via `Grep` |
| Kernel contract evaluation | rocq-mcp kernel queries orchestrated by a headless Claude call | only the kernel can authoritatively say whether a hypothesis is unused or a goal has closed |
| Report merge, Markdown rendering, cost estimate | Python | deterministic templating |
| Bypass log, git notes audit trail, attempt counter | shell | trivial persistence |
| Fix-plan drafting with per-edit justification | Claude `rocq-prover` agent through a slash command | the plan is prose and needs to cite the rule authority |
| Operator approval of the fix plan | human via `AskUserQuestion` | this is the only point where final judgement must be held by a human |
| Fix application under cumulative turn and compile budget | Claude `rocq-prover` agent | the fixer needs to compose multi-file edits and check compile |
| Rule authoring and catalog edits | human | the catalog is the ground truth against which everything else is measured |

The table makes the shape of AI involvement explicit. The agent appears
in three well-scoped places: the Stage 2 auditor, Tier K verification,
and the fix-plan and fix-application flow. Everything else is
deterministic Python or shell. The audit can run Stage 1 alone in an
air-gapped environment; the adaptive budget and the fast-bypass flag
together let the operator trade Stage 2 fidelity for latency when
needed.

## Value observed on two trial commits

The pipeline was exercised against two existing commits from the
`pgg-smc` branch after it was installed. Both commits predate the
pipeline, so neither was gated at the time of writing. The trial ran
each commit through the full pipeline and captured the report.

The older of the two, commit `7b935d9`, "Close six gaps in PGG
formalisation", changed twelve `.v` files, added four hundred and
twenty lines, and introduced roughly twenty top-level declarations.
The pipeline reported sixteen errors and fourteen warnings. The
dominant error class was H001, the rule that forbids a `Lemma` without
a preceding comment block. Several of the new lemmas in this commit sit
immediately below a `Hypothesis` declaration whose own preceding
comment describes the hypothesis rather than the lemma. The Tier 0
scanner refuses to attribute a comment across a non-entity line, so the
lemma is correctly flagged as undocumented. The Stage 2 pass on this
commit also produced multiple G001 findings against non-canonical
suffixes such as `_automorphism`, `_correct`, `_witness_concrete`, and
`_crypto`; the agent mapped each to a suggested MathComp alternative
with authority citations.

The newer of the two, commit `3547f28`, "Add pile-2 preservation and
identity coord-perm compatibility lemmas", changed two `.v` files,
added thirty-one lines, and introduced two lemmas. The pipeline
reported zero errors and six warnings. Both lemmas carry preceding
comments that paraphrase what the lemma says, so H001 does not fire.
Stage 1 fires F001 on both identifiers because each has four
underscore-separated lowercase components. Stage 2 adds the deeper
findings: G001 classifies `_proved` on `s5x5_preserves_pile2_proved`
as equivalent to the banned `_proof` kind-suffix and suggests
`s5x5_preserves_pile2` or `s5x5_pile2_stab`. G001 classifies `_id` on
`coord_perm_compatible_id` as a MathComp-table mismatch because
MathComp uses the numeric suffix `1` for unit elements, as in `perm1`,
`mul1g`, and `comp1f`; it suggests `coord_perm_compatible1`. The same
Stage 2 pass used Grep against the repository and confirmed that the
downstream consumer is `rs_code_5sheets.v` line one hundred and
twenty, where the lemma is invoked as `apply: coord_perm_compatible_id`.
The H002 finding for the same lemma notes that the preceding comment
paraphrases the statement but does not identify the lemma as a helper,
does not give motivation, and does not name the Grep-confirmed
downstream consumer.

The two commits sit at different points on the drift spectrum. The
larger commit embodies the "add lemma and move on" pattern that
accumulates as a project ages: new declarations without dedicated
comments, names whose suffix encodes the method rather than the role,
and `Hypothesis` blocks whose own comments are mistaken by a reader
for lemma-level documentation. The smaller commit represents a
deliberate improvement attempt: both lemmas carry preceding comments
and the author thought about what the lemma does. The pipeline
recognises the improvement, produces zero errors for the smaller
commit, and refines the target by pointing at the remaining drift in
naming and the missing Kind, Why, and Used-by content in the comments.

The value shown by this trial is not that the pipeline is catching
nothing a careful reviewer would miss. A careful reviewer would catch
all of these. The value is that the pipeline catches them before the
reviewer's time is spent, produces concrete fix sketches with
authority citations rather than one-word verdicts, verifies semantic
claims against the kernel before reporting them, and records every
decision in a machine-readable form that supports longitudinal
analysis of where drift accumulates. The larger commit would have
taken a human reviewer an hour or more to walk through; the pipeline
produced its equivalent report in two minutes and four seconds on the
parallel Stage 2 pass, at an estimated Anthropic API cost of
approximately two dollars.

## What the trial suggested changing

The trial surfaced three operational rough edges that a first-pass
design had not anticipated. First, a single fixed chunk size and a
single fixed parallelism value are the wrong shape for a workload
whose commit sizes range from one entity to one hundred entities. The
pipeline now scales the chunk size as a function of the entity count
and the worker count as a function of the chunk count, so a
single-entity commit pays no thread-pool overhead and a large commit
fans out to the configured ceiling. Second, the bypass flag still ran
the full audit before exiting, which defeats its purpose in an
emergency. The pipeline now accepts `ROCQ_AUDIT_BYPASS=fast`, which
runs Tier 0 and Stage 1 only and logs the skip in the audit trail.
Third, all limits are overridable per commit either through an
environment variable or through a git trailer, so a commit that
genuinely needs a larger token budget or a different worker count can
opt into it while recording the deviation for later review.

These three refinements follow from a single principle that the
operator articulated during the trial: for an audit pipeline applied
to a heterogeneous workload, soft adjustable limits that scale with
input size or accept per-invocation overrides serve the work better
than hard uniform caps.

## Footnotes

Rule identifiers cited above: A001 through A004 cover deprecated
SSReflect tactics; B001 covers one verbose `boolP` idiom; C001, D001,
E001 cover opaque signatures, unused hypotheses, and over-long proofs
respectively; F001 and G001 cover naming drift with Stage 2 semantic
verification; H001 and H002 cover preceding comments; I001 covers the
"conform to MathComp or justify the deviation with a `Naming:` line"
gate. The full catalog with fixtures and authority references lives
under `.claude/audit/rules/`. The canonical MathComp convention
reference loaded into the agent is in `.claude/audit/rules/AUTHORITY.md`.

Commits referenced: `7b935d9`, "Close six gaps in PGG formalisation
(Fixes 1, 2, 3, 5, 6, 7)", authored 2026-04-17. And `3547f28`, "Add
pile-2 preservation and identity coord-perm compatibility lemmas",
re-committed 2026-04-21 during the trial from the same tree as the
original `ab86310`.
