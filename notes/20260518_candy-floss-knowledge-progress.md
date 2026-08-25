# Plan: "Candy Floss" working-process slides

## Context

The user wants to present their working process on this project as a
"Candy Floss" (Watagashi) methodology. The naïve but true core idea is
the stick. Every new piece of math or formalisation knowledge is a
strand of sugar floss. Each iteration sticks more floss around the
growing centre. They drafted ~700 words describing the process and
asked for:

1. English correction of the draft.
2. Splitting the 6 points (plus weakness) into atomic items, one idea
   each.
3. A 16:9 slide-layout proposal that presents the items briefly, not
   as long sentences.
4. An adversarial presentation-designer audit of the proposal before
   ExitPlanMode.

The slides extend the existing poster section that introduces the work
("WHAT THIS WORK IS" / "WHAT THIS PROJECT IS" at `ioEmi`, `KTtZU`),
with this methodology block as a deeper-dive companion. Register must
match: section label in orange `#E8573F`, title in navy `#0E2747`,
sub-text in gray `#5B6680`, card fills `#FAFAF6` and `#F0EBDD`,
background `#F6F1E7`, Inter font.

Per project memory:
- `feedback_prose_style`: no em-dashes, no parenthetical asides, no
  semicolons in slide prose.
- `feedback_methodology_notes_generality`: methodology prose stays
  framework-agnostic; specific Rocq identifiers and instance names go
  into footnote-style annotations only.
- `feedback_writing_audit_first`: draft over 500 words requires an
  audit before approval.
- `feedback_pencil_diagram_via_latex`: if the stick-and-floss diagram
  needs precise curves, author the visual in LaTeX/TikZ and insert as
  image fill rather than fighting Pencil primitives.

## Phase-1 corrected English version

The version below preserves the user's voice and metaphor while
fixing grammar, punctuation, and small word choices. Where the user
wrote "central" I corrected to "centre" and "surgar" to "sugar".
Parenthetical asides and em-dashes were replaced with period breaks
or commas to match the project's prose style.

> My working process on this project resembles Candy Floss, the
> Japanese watagashi. The naïve but true core idea is the stick.
> Every other piece of mathematical knowledge is a strand of sugar
> floss. Each iteration sticks more floss to the growing centre until
> the whole candy takes shape.
>
> The core idea (the stick): "Every covering space gives you an MPC
> protocol", arrived at by observation.
>
> Each new strand of knowledge enters the candy through one of the
> sources below. Every source has a workflow. The common rule is that
> something must stay grounded: the core idea, the formalised and
> proven parts of the codebase, and accepted mathematical knowledge.
> Plans, work in progress, retrospectives, and unproven agent output
> must be reasoned to extend the grounded parts, and the agent must
> show why and how.
>
> 1. Related work. Ask the agent to search related work and explain
>    how each candidate is designed. List the reasons each matches
>    the core idea. Force the agent to quote text verbatim as
>    evidence that the related work really addresses the core idea.
>
> 2. Formalisation by matching an existing model. The MPC model has
>    parties, secret inputs, shares, and public output. First, ask
>    the agent to identify what plays each of these roles in the
>    covering-space picture, with a reason for every mapping. Then,
>    if every mapping holds, ask the agent to formalise the protocol
>    in Rocq, and to audit its own work for why the result really is
>    an MPC protocol.
>
> 3. Pivots from negative findings. Both human and agent learn while
>    formalising, so missing knowledge can produce dead ends. The
>    agent often discovers a negative result late. Even so, any clue
>    extracted from a negative result can pivot the original idea and
>    save earlier formalisation, because proven parts remain true and
>    only their interpretation changes. One example: the genus of the
>    S_5 × S_5 covering curve was computed as 3, then 173, then
>    15,121, each iteration adding a new constraint that pushed the
>    genus higher. Neither agent nor human can guarantee correctness
>    without complete knowledge, but each iteration adds reasons that
>    enlarge the candy. From the most recent negative result a new
>    direction emerged: instead of one curve, use two Bring's curves
>    of genus 4. The path still needs more iterations to verify
>    soundness and meaning. A second example: when the agent turns
>    overly pessimistic, ask "even if some parts turn out unsound,
>    what survives from the proven parts?" The earliest version of
>    this work had no idea of splitting the permutation matrix. The
>    agent realised that without splitting, any party could invert
>    the permutation easily and security collapsed. The rescue was
>    to split. The grounded fact is that permutation actions can
>    carry security. The defect is the easy inversion. Asking the
>    agent to search for or rethink an improvement pushed the work
>    until it pivoted.
>
> 4. Audits on hypotheses and axioms. Periodically ask the agent to
>    justify every unproven hypothesis and axiom in the codebase.
>    This pressure surfaces overclaims, unsound logic, and false
>    assumptions. Sometimes it triggers a whole refactor, because a
>    fundamental piece turned out wrong. Auditing hypotheses is
>    faster than auditing proven-but-vacuous lemmas, because the
>    surface to question is smaller.
>
> 5. Audits on proven yet vacuous lemmas. After the agent claims a
>    proof, run another auditor or several. The auditor checks
>    whether the proof closes with only a reasonable set of
>    hypotheses, whether the result is proven yet vacuous, and if
>    non-vacuous, what each lemma means for the roadmap descending
>    from the core idea.
>
> 6. Pure mathematics study notes. Sometimes the human studies a
>    topic without formalising. The Q&A session is kept as a note.
>    These notes feed the agent when planning a later formalisation.
>    For example, a note on AG codes and other recovery-scheme
>    candidates was used when the recovery layer was formalised.
>
> Weakness: connection and comprehensiveness. The flow risks
> producing "true everywhere but not useful or comprehensive as a
> whole", like passing every unit test while failing integration.
> One mitigation: in selected iterations, ask the agent to draw the
> overall flow or component architecture in detail and ask why some
> parts look disconnected.

## Phase-2 atomic items split

Each item is one idea, written as a short noun phrase or imperative.

### Frame
- F1. Core idea: "Every covering space gives you an MPC protocol",
  observed.
- F2. Metaphor: stick is the core idea; floss is new math knowledge;
  iteration spins the candy.

### Grounded vs extension (the principle)
- P1. Grounded set 1: the core idea.
- P2. Grounded set 2: formalised and proven code.
- P3. Grounded set 3: accepted mathematical knowledge.
- P4. Extension set 1: plans and drafts.
- P5. Extension set 2: retrospectives.
- P6. Extension set 3: unproven agent output.
- P7. Rule: every extension must justify how it extends a grounded
  set, with reasons.

### Source 1: related work
- S1a. Ask the agent to search related work.
- S1b. Ask why each candidate matches the core idea.
- S1c. Force verbatim quotation as evidence of the match.

### Source 2: model matching
- S2a. List the MPC roles: parties, secret inputs, shares, public
  output.
- S2b. Ask the agent to identify what plays each role in the
  covering-space picture.
- S2c. Demand a reason for each mapping.
- S2d. If mappings hold, formalise the protocol in Rocq.
- S2e. Audit the formalisation: "is this really an MPC protocol?"

### Source 3: pivots from negatives
- S3a. Late negative results are still informative.
- S3b. Proven parts remain true; only interpretation changes.
- S3c. Example: S_5 × S_5 covering genus iterated 3 → 173 → 15,121,
  then pivoted to two Bring's curves of genus 4.
- S3d. Anti-pessimism prompt: "what survives from the proven parts?"
- S3e. Example: permutation-matrix splitting rescued security after
  the agent noticed single-matrix exposure invites trivial inversion.

### Source 4: audit hypotheses and axioms
- S4a. Audit every unproven dependency for justification.
- S4b. Surfaces overclaims, unsound logic, false assumptions.
- S4c. Sometimes triggers a whole-codebase refactor.
- S4d. Cheaper than auditing proven-but-vacuous lemmas.

### Source 5: audit proven yet vacuous lemmas
- S5a. After every proof, run a second auditor.
- S5b. Check: does the proof close with a reasonable hypothesis set?
- S5c. Check: is the result proved yet vacuous?
- S5d. If non-vacuous, ask what it means for the roadmap from the
  core idea.

### Source 6: pure mathematics notes
- S6a. Some sessions are pure Q&A without formalisation.
- S6b. Q&A sessions are kept as notes.
- S6c. Notes feed later formalisation planning.
- S6d. Example: an AG-code note fed the recovery-layer formalisation.

### Weakness and mitigation
- W1. Risk: every part is true in isolation but the whole is not
  comprehensive (unit tests pass, integration fails).
- W2. Mitigation: ask the agent to draw the overall flow or component
  architecture.
- W3. Question every part that looks disconnected.
- W4. Iterate the architecture diagram.

Total atomic items: 2 + 7 + 3 + 5 + 5 + 4 + 4 + 4 + 4 = **38 items**.

## Phase-3 slide-layout proposal (16:9, 1920 × 1080)

**Four slides** (compressed from five after audit) extend the
existing horizontal "Prototyping Result" row to the right of the
three status tables (after `RP5hY` at x=16640). Each new slide sits
at y=4720, width 1920, height 1080, with 200-px horizontal gap.

Register matches the existing poster: background `#F6F1E7`, section
label in `#E8573F` 22pt 700 letterSpacing 3, **title in `#0E2747`
44pt 800** (raised from 38pt per audit, to match `bjHmm`), sub-text
in `#5B6680`, card fills `#FAFAF6` and `#F0EBDD`, Inter font.

### Slide M1 — Candy Floss (intro, no diagram)

Section label: `04 / WORKING PROCESS`
Title: `Candy-floss methodology`
Sub-line: `Stick is the core idea. Floss is new math. Iteration spins it.`

Body, vertical stack:
- Core-idea quote, italic 28pt navy, centre-aligned:
  > "Every covering space gives you an MPC protocol", arrived at by
  > observation.
- A single horizontal chip row of six source labels, each chip
  orange-outlined navy text:
  `RELATED WORK` · `MODEL MATCHING` · `PIVOTS FROM NEGATIVES`
  · `HYPOTHESIS AUDIT` · `VACUITY AUDIT` · `STUDY NOTES`

No stick illustration (audit: chips next to a navy column would
read as "column plus buttons", not as candy-floss). Metaphor lives
in the words.

Foot mark bar: 80 × 6 `#E8573F` rectangle bottom-left.

### Slide M2 — Grounded vs extension

Section label: `04A / WORKING PROCESS`
Title: `Always grounded, must justify the rest`
Sub-line: `Name what stays true. Prove the rest extends it.`

Body, two cards side-by-side:
- Left card (`GROUNDED`, fill `#FAFAF6`, padding 28):
  - P1. The core idea.
  - P2. Formalised, proven code.
  - P3. Accepted mathematical knowledge.
- Right card (`MUST JUSTIFY`, fill `#F0EBDD`, padding 28):
  - P4. Plans and drafts.
  - P5. Retrospectives.
  - P6. Unproven agent output.

Below the two cards, one full-width italic line:
`P7. Every extension must show how it extends a grounded part.`

### Slide M3 — Six floss sources (merged from old M3 + M4)

Section label: `04B / WORKING PROCESS`
Title: `Six floss sources`
Sub-line: `Three bring math in. Three question what is already stuck.`

Body, **two rows of three cards**, each card padding 18, three lines
per card.

Row 1, outward floss:

- Card S1 `RELATED WORK`:
  - Search related work.
  - Why does each match the core idea?
  - Force verbatim quotation as evidence.

- Card S2 `MODEL MATCHING`:
  - Name MPC roles: parties, inputs, shares, output.
  - Map each role onto the covering-space picture.
  - Demand a reason for every mapping, then formalise and re-audit.

- Card S3 `PIVOTS FROM NEGATIVES`:
  - Late negatives still inform.
  - Anti-pessimism prompt: "what survives from the proven parts?"
  - Sub-label (12pt grey): `Example: a genus that climbed, then pivoted to a different curve.`

Row 2, inward floss:

- Card S4 `HYPOTHESIS AND AXIOM AUDIT`:
  - Justify every unproven dependency.
  - Surfaces overclaims, false assumptions, sometimes a refactor.
  - Cheaper than auditing vacuous proofs.

- Card S5 `VACUITY AUDIT`:
  - Run a second auditor on every proof claim.
  - Is the hypothesis set reasonable? Is the result vacuous?
  - If non-vacuous, what does it mean for the roadmap?

- Card S6 `STUDY NOTES`:
  - Some sessions are pure Q&A, no formalisation.
  - Save the Q&A as notes.
  - Sub-label (12pt grey): `Example: an algebraic-geometry-code note fed the recovery layer.`

### Slide M4 — Weakness and mitigation

Section label: `04C / WORKING PROCESS`
Title: `True everywhere, comprehensive nowhere`
Sub-line: `Parts pass unit tests. The whole may fail integration.`

Body, two cards side-by-side:

- Left card `RISK`:
  - Each part proved in isolation.
  - The whole may fail integration.
  - Hard to notice from inside any single iteration.

- Right card `MITIGATION`:
  - Ask the agent to draw the overall flow.
  - Question every part that looks disconnected.
  - Iterate the architecture diagram, not only the lemmas.

Footer mark bar.

### Cross-cutting design choices

- Title font 44pt 800 navy (raised from 38pt per audit, matches `bjHmm`).
- Section-label format `04 / WORKING PROCESS` continues the existing
  `00..03` poster scheme. M1 is `04`, M2-M4 are `04A`, `04B`, `04C`.
- Card padding 18-28; corner radius 12; chip corner radius 18.
- All slide text follows the project prose rule: no em-dashes, no
  parenthetical asides, no semicolons.
- Each slide carries one visual anchor: chip row on M1, italic line
  under cards on M2, two-row card grid on M3, side-by-side cards on
  M4.
- Six-source consolidation on M3 trades depth for scan budget; the
  full per-item list is recorded in Phase-2 above for reference.

## Phase-4 presentation-designer audit response

The audit ran in this conversation. Findings and how the plan was
amended below.

### Accepted and applied

1. **Five slides too many for a methodology aside.** Merged M3
   (outward) and M4 (inward) into a single "Six floss sources"
   slide with two rows of three compact cards. Final count: 4
   slides (M1, M2, M3, M4).
2. **Stick-and-floss diagram on M1 will not read as candy floss at
   poster scale.** Replaced the navy column plus chip cluster with
   clean typography: large title, italic core-idea quote, single
   horizontal chip row of six source labels. Metaphor stays in the
   words.
3. **Title size mismatch.** Bumped title font from 38pt to 44pt to
   match `bjHmm` (the nearest comparator in the existing poster).
4. **M2 sub-line too long.** Rewrote 20-word sub-line to "Name what
   stays true. Prove the rest extends it." (10 words).
5. **M2/P7 reads as a sentence not a card line.** Rewrote to "Every
   extension must show how it extends a grounded part." (10 words).
6. **M1 sub-line re-balanced.** Rewrote "Stick = core idea. Floss =
   new math knowledge. Iteration spins the candy." to "Stick is the
   core idea. Floss is new math. Iteration spins it." (11 words,
   parallel structure).
7. **Genus-chain jargon overload.** Replaced
   `S_5×S_5 genus 3 → 173 → 15,121 → two Bring's at g=4` with a
   12pt grey sub-label "Example: a genus that climbed, then pivoted
   to a different curve." Specific numbers and curve name dropped.
8. **AG-code abbreviation in M4/S6.** Expanded to
   `algebraic-geometry-code note fed the recovery layer` per
   memory note `feedback_no_abbreviations_in_prose`.

### Accepted, no change required

- Section label format already matches.
- Card fills, padding, corner radius already match.
- Chip palette subset of `ioEmi` palette, already continuous.
- M5 (now M4) kept as a standalone slide; it is the most
  differentiating idea in the methodology.

### Rejected

- None. Every audit finding was either applied or already aligned.

### Net effect on the poster plan

Slide count: 5 → 4. Title size: 38 → 44pt. M1 dropped the visual
diagram in favour of typography. M3 and M4 merged into one
six-card slide. Two sub-lines rewritten for scan-budget. Two
jargon chips softened.

## Phase-5 implementation tasks (post-ExitPlanMode)

1. Insert slides M1..M4 at `(x = 18760, 20880, 23000, 25120, y = 4720)`
   so they continue the horizontal row to the right of the three
   status tables. Each slide width 1920, height 1080, 200-px gap.
2. Build slides in 4 batch_design calls (one per slide), reusing the
   row-and-cell pattern from the status tables (cells need
   `layout:"vertical"` for auto-height to work; learned in the prior
   cycle).
3. Verify each slide with `mcp__pencil__get_screenshot` after build.
4. Remove `placeholder: true` from each slide as it is finalised.

Critical files:
- `pgg-smc/notes/may18aipv2026/poster.pen` (target).

Verification:
- Visual screenshots for each slide.
- `mcp__pencil__snapshot_layout` to confirm no overlap with the
  existing horizontal row at y=4720.

## Out of scope

- Code edits to the Rocq tree.
- Edits to other poster sections.
- Updating user memory; queued for after ExitPlanMode.
