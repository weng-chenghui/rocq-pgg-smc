# rocq-pgg-smc quality catalog

Date: 2026-08-26. Scope: the 153 `.v` files in `_CoqProject`.
Focus: EXPRESSIVENESS and READABILITY of statements and files, not
proof golf (proof-concision passes are separate; see mathcomp-skills
reference.md §22-§32).

Authorities, in priority order:
1. The user's global rules (statement comments: fact + position, no
   meta/status; naming: mathcomp vocabulary, no opaque project
   abbreviations, no metaphor words for results).
2. mathcomp-skills `reference.md` §1-§37 (local install), and its
   mechanical scanner `scripts/audit-quick.sh`.
3. math-comp `CONTRIBUTING.md` conventions (hypothesis naming,
   80-char semantic cuts, on-demand implicit arguments,
   `Prenex Implicits`).

Findings are reported, never auto-fixed. Format per finding:
`[RULE] file:line — evidence (quote) — suggested fix (one line)`.
Severity: A (hurts every reader), B (hurts statement consumers),
C (local polish).

## E: Expressiveness of statements

**E1 (A) — Section-hoisted hypotheses.** A `Lemma`/`Theorem` whose
statement carries three or more named premises `(h1 : ...) (h2 : ...)`,
or a `forall` prefix spanning more than two lines, or premises repeated
verbatim across two or more lemmas in the same file, must move its
context into a `Section` with `Variables`/`Hypothesis` declarations —
a dedicated section per lemma or per lemma cluster sharing the
context. The statement then reads as the bare mathematical fact.
Detection: count parenthesized premise binders in statements; diff
premise text across lemmas in a file; flag statements > 4 lines.
Fix shape: `Section <cluster_name>. Variables ... Hypothesis h_... .
Lemma ... End <cluster_name>.` with meaningful hypothesis names
(`n_gt0` style, never `H1`).

**E2 (B) — Implicit Types.** A file or section that binds the same
carrier repeatedly (`(g : gT)`, `(w : seq gT)`, `(d : fdist A)` in
many statements) should declare `Implicit Types` once and drop the
per-binder annotations. Detection: same typed binder in 3+ statements
of one section/file without an `Implicit Types` line.

**E3 (A) — Notation for group actions and object combinations.**
Recurring multi-argument applications that denote a single
mathematical operation — action/evaluation shapes like
`endpoint M g s`, `compute PI P i`, `rho g s`, word/trace
compositions, fdist/RV combinations — deserve a scoped notation, OR
(better, when the object literally is a group action) packaging as a
mathcomp `action` to inherit the standard fingroup notation family
(`x ^ y`, `'C_G[x]`, `[acts A, on S | to]`). Thresholds to avoid
over-notation: flag a combinator only when it is applied 10+ times
across the tree or nested 2+ deep inside statements. New notations
must be `Local Notation` or scope-controlled, declared with explicit
levels, documented in the file header, and use mathematical symbols
(not ASCII soup). Detection: grep application counts of the known
combinators; look for statement lines where the same function head
appears twice nested.

**E4 (B) — Name repeated statement fragments.** A proposition
fragment repeated verbatim in 3+ statements (e.g. a coalition-bound
premise, a well-formedness side condition) becomes a named
`Definition`/predicate with its own statement comment; lemmas then
read as domain sentences. Detection: longest-common-substring across
statement texts within a file; premise phrases > 40 chars appearing
3+ times.

**E5 (C) — Statement generality and reflection.** Statements over a
fixed carrier that hold at a mathcomp structure level should
generalize (reference.md §21); decidable properties stated as `Prop`
with no boolean/`reflect` companion where the file then does casework
on them are flagged. Do not flag when the concrete carrier is the
mathematical point (an instance file about S5 stays about S5).

## R: Readability

**R1 (B) — 80-character lines, semantic cuts** (reference.md §1;
mathcomp CONTRIBUTING). Mechanical: `awk 'length > 80'`.

**R2 (A) — Statement comments.** Every `Definition`, `Lemma`,
`Theorem`, `Record`, `Instance`, `Axiom` carries a comment stating
its mathematical fact AND its position in the file's argument; no
status markers, effort notes, plan tokens, or type restatements.
Axioms additionally carry a literature citation. Flag missing and
meta-style comments; do NOT rewrite them (the formal-comment-review
skill is the fixing pass).

**R3 (A) — Hypothesis and variable naming** (reference.md §14;
CONTRIBUTING). No `H`, `H'`, `Hfoo` with scope beyond ~5 lines;
premise names encode content (`n_gt0`, `coalition_le_k`); induction
hypotheses `IHx`. Carrier conventions: `m n p` naturals, `x y z`
ring elements, `A B M N` matrices, `p q r` polynomials.

**R4 (B) — File headers and section structure** (reference.md §4).
Each file opens with a header block documenting its objects and the
argument the file makes; `Section` names describe content (not
`Section sec1`); one topic per section. Long tutorial prose pinned to
a single declaration moves to the header.

**R5 (B) — Proof-script reader hygiene** (reference.md §8, §26-27).
Bullets for 3+ subgoals, two-space indent + `last first` for 2;
goal-closing lines start `by`/`exact:`; no `Focus`, no `{ }`, no
numerical occurrence selectors. Mostly mechanical via audit-quick.sh.

**R6 (C) — Qualified names and import order** (reference.md §3, §23).
No `module.lemma` qualification in bodies when an import resolves it
(exception: deliberate disambiguation, e.g. `proba.inde_RV_comp` vs a
local homonym — flag only when unambiguous); imports in canonical
order: HB, mathcomp core, analysis, infotheo, project.

**R7 (C) — Scope and visibility discipline** (reference.md §6, §18).
`Local Open Scope` only; auxiliary results `Local`/`Let`/`Fact`;
main results bare. Flag non-Local `Open Scope` and obviously
auxiliary bare lemmas (used once, in the next proof).

**R8 (A) — Identifier naming** (reference.md §10-11; user rules).
`mainSymbol_suffixes` order; mathcomp abbreviation vocabulary only
(`card`, `inj`, `le`, `gt0`, ...); no opaque project abbreviations a
mathcomp reader cannot parse; no metaphor words (`escape`, `beats`,
`smash`) for mathematical results.

**R9 (B) — Duplication.** The same fact proved in two places, or a
proof block of 5+ lines copy-pasted across files (the instances/
directories are the suspects: s5 vs s5x5 vs pgl27 rows). Detection:
identical statement modulo carrier; identical proof-script windows.
Fix shape: factor into the shared parametric file, instances
instantiate.

**R10 (C) — Dead weight.** Commented-out proof blocks, `Let`s never
used, imports whose removal keeps the file compiling (flag only
obvious cases textually; do not compile-test in the scan pass),
scratch names (`_test`, `debug_`) inside the build.

## Out of scope for this scan
Proof-length golf, `Admitted`/axiom hunting (already gated),
performance, and the monodromy-vocabulary question (explicitly
deferred by the user 2026-08-26).
