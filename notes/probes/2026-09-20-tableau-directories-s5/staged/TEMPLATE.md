# The per-instance `tableau/` directory: the pattern, as ruled

Written from the S5 pilot after its audit (`audit-s5-pilot.md`, findings F1 to
F24 and the nine pattern rulings). Everything here was measured, not assumed.
The prover of PGL(2,7), five-card or PSL(2,11) starts from this page.

## Files and module names

```
instances/<inst>/tableau/
  <inst>_tableau_algebraic.v
  <inst>_tableau_executable.v
  <inst>_tableau_observed.v
  <inst>_tableau_sampled.v
  <inst>_tableau_analysis_bridged.v
  <inst>_tableau_checks.v
```

The module name is the base name. The 24 names the four instances produce are
distinct from each other and from the 204 logical names reachable from the
`-R` directories of `_CoqProject`.

## The load path, settled by compile

`-R` is recursive, so under the existing `-R instances/<inst> pgg_smc` a file
in `tableau/` is bound **`pgg_smc.tableau.<inst>_tableau_<phase>`**, and
`From pgg_smc Require Import <inst>_tableau_<phase>.` resolves it, because a
`Require` matches a prefix of the root against a suffix of the name. In that
shape the compile emits **no warning at all**.

**Add no `-R` line for the subdirectory.** Adding
`-R instances/<inst>/tableau pgg_smc` emits `overriding-logical-loadpath`
(a different warning from `ambiguous-paths`, so `_CoqProject`'s
`-arg -w -arg -ambiguous-paths` does not silence it) and then fails against a
`.vo` built without it: `contains library pgg_smc.tableau.X and not library
pgg_smc.X`.

`_CoqProject`: replace the `instances/<inst>/<inst>_rows.v` line with the six
file lines in phase order, at the same position, so they still precede any
file that imports them. No `-R` line is added or removed.

## Naming, per phase

`<inst>_<discriminator>_<phase>`, the discriminator being the run mode at
Executable, the model at Sampled, and nothing at Algebraic.

| Phase | Scheme | S5 | Existing names it keeps |
|---|---|---|---|
| Algebraic | `<inst>_algebraic_start` | `s5_algebraic_start` | none exist |
| Executable | `<inst>_<mode>_executable` | `s5_dealt_executable`, `s5_supplied_executable` | none exist |
| Observed | `<inst>_<mode>`, phase word elided | `s5_dealt`, `s5_supplied` | `pgl27_dealt`, `five_card_committed`, `psl211_alldecks_prefix` |
| Sampled | `<inst>_<model>_sampled` | `s5_rand_sampled` | `pgl27_word_sampled` |
| Published row | `<inst>_row_<model>_tableau` | `s5_row_rand_tableau` | `pgl27_row_exact_tableau`, `psl211_row_alldecks_tableau` |

`_start` at Algebraic names the framework statement that builds the value,
`tableau_start`, and keeps the value one word away from `<inst>_algebra`, which
sits in the same file.

Conversion lemmas are named after their non-canonical side, as the tree does
(`pgl27_inline_paramsE`, `pgl27_row_word39_bindE`, `s5_supplied_paramsE`), not
after the edit that produced them:

| Equation | S5 name |
|---|---|
| the Executable line builds the parameter record | `<inst>_<mode>_executable_paramsE` |
| the named Executable value with the run facts is the Observed value | `<inst>_<mode>_executableE` |
| the named Sampled value with the payload and the terminal is the row | `<inst>_row_<model>_sampledE` |

Five-card note: `five_card_row_repeated_tableau` and
`five_card_row_biased_tableau` are `Tableau Sampled` values wearing the
published-row suffix. They are existing names and stay; the five-card `_sampled`
header says so.

## The import chain, without `Export`

Each file requires and imports the phases whose names it uses, and **no file
uses `Require Export`**. `Require Import` is not transitive for `Import`, so a
file needing a name two levels down names that level too. At S5:

```
algebraic <- executable <- observed <- sampled <- analysis_bridged <- checks
analysis_bridged also imports observed        (it states the row from the Observed value)
checks also imports observed and sampled
```

Production's importer names one module, the phase that declares the name it
wants. Record in each `_analysis_bridged.v` header which phase declares which
kind of name, so an importer does not have to guess.

Every phase file's first mathcomp line includes **`ssrfun`**, because
`exact: erefl` is this pattern's standard proof and `erefl` does not resolve
without it. See trap 4.

## What a header must say, and must never say

Must say, in this order: what the level holds and what proposition it carries
(read `StackProp` and `StackAt` in `manifest/pgg_tableau.v`); what this
instance names at that level and why the instance branches there if it does;
then a `Definitions:` and a `Key results:` table indexing every non-`Fail`
declaration of the file and no `Fail`. Box lines are exactly 80 columns. The
first two lines are the project's licence lines, copied.

Must never say:

- **that a row does not exist because a program does not.** The manifest
  publishes rows this development reaches by other routes:
  `manifest/pgg_analysis_manifest.v` carries `s5_row_word` at
  `AnalysisBridged` over the dealer-dealt run, published from a mixing
  theorem. A phase header says what this development's programs do and names
  separately what the manifest publishes another way. This was audit findings
  F1 and F2, and PGL(2,7), five-card and PSL(2,11) all have the same shape.
- **a universal read off one refused term.** A `Fail` rejects one written
  term. "The kernel decides the tolerated coalition size" is not what
  `Fail Definition F : s5_F = MkFunctionality id 5 := erefl` shows; what it
  shows is that the equation as written is refused, the size itself being read
  off the algebra by `algebra_functionality`. Audit F12.
- **what a lower level proves.** `ex_expected` is the value a run is *meant*
  to recover; the reconstruction fact arrives at Observed. Write "meant to
  recover" below Observed. Audit F4 and F6.
- **"nothing else enters"** unless the closure was computed. Name the class:
  "no other security statement of the instance enters the row". Audit F5.
- **history**: no "moved from", "formerly", "now", and no probe, stage or
  landing words.

One word per concept: "reading" is the instance's word for what a coalition
observes, so it is not also the word for a spelling of a term; "view" survives
only inside moved docstrings and identifiers. Drop a forward-looking
justification that names a capability nothing exercises. No metaphor noun for
a bound, and none of the banned vocabulary.

## The three verification rules

1. **Declaration-level token identity.** Comment-strip both sides, slice by
   declaration name, compare token streams, statement and proof. The name sets
   must be equal with nothing lost and nothing duplicated across the six files.
   Any intended token difference is listed by name in the script with its
   reason and printed on every run, so it cannot become invisible.
2. **Each recorded `Fail` is compiled un-`Fail`ed in the preamble of the file
   it sits in,** on both sides, and the two `Error:` messages are compared;
   neither may contain `was not found in the current environment`. Splitting
   one file's import list across six is exactly what makes a `Fail` start
   failing for an unresolved name, and it happened twice in the pilot.
3. **The innermost `Local Open Scope` line is the same in all six files.** A
   phase file with a shorter scope list could otherwise resolve a numeral
   differently from the file the declaration came from. Do not force the lower
   files to import `fdist`, `proba` and `entropy` merely to open scopes they do
   not need; assert the innermost entry instead. Keep reprice constants in the
   AnalysisBridged file, which has the full block.

Also: `Print Assumptions` every published row, lemma and theorem on both
sides and diff as text; the moved names must be byte-identical. Ascribe every
production statement in a fidelity file, and print the assumptions of the new
definitions too, since a type ascription alone would pass on a wrong body.

Every new equation closes by `exact: erefl` and never `by []` or `done`: a
`by []` over a `published_at` equation has been measured at 683 s against
0.13 s. Read `-time` for anything over 5 s.

## Four traps, each of which produced a green result that tested nothing

1. **zsh does not word-split `$FLAGS`.** `rocq compile $FLAGS f.v` reports
   `Unknown option -w -projection-...` as if the whole string were one flag.
   Write `${=FLAGS}`, or pass a list from Python.
2. **`**)` at 80 columns.** Repairing a 79-column box line by stripping one
   character and appending `*)` leaves `**)`, which is exactly 80 columns, so
   a length check passes and a green compile hides it. Check the shape, not
   only the width.
3. **A stale mid-chain `.vo`.** Rebuilding a lower phase after a higher one is
   already built gives `makes inconsistent assumptions over library`. Rebuild
   the chain in phase order after any edit.
4. **`erefl` not in scope.** Without `ssrfun` on the mathcomp line, `erefl`
   does not resolve; a `Fail … := erefl` then passes for the wrong reason, and
   an honest `exact: erefl` fails outright. The pilot hit both halves.

## Order of work at one instance

Load-path probe with one placeholder file; Algebraic and Executable, with one
parameter equation per named Executable value; Observed, with one
`_executableE` per mode; Sampled, one named value per model a program
continues from; AnalysisBridged, with one `_sampledE` per re-cut row; the
checks file; the importer's `Require`; then `verify.py`, the fidelity and
baseline compile, the assumption diff and the scans. Never `make`, one Rocq
process at a time, nothing written into a production directory.

## Addendum after PSL(2,11) (2026-09-20)

Rules added by the second instance; its scripts are the ones to copy:
`notes/probes/2026-09-20-tableau-directories-psl211/` (`verify.py`,
`gen_fidelity.py`, `stage_edits.py`, `compile.py`).

1. The pilot's docstring regex ran past a `Local Notation`, which is not in its
   declaration alternation, and attached that notation's docstring to the next
   declaration. Use the PSL(2,11) `verify.py`, whose pattern stops at the first
   `*)`. PGL(2,7) and five-card have `Local Notation` blocks.
2. When an instance has a second source file that imports the rows file (a
   proximity file), that file is CUT: certificate values, published rows and
   statements about them go to `<inst>_tableau_analysis_bridged.v`, recorded
   failures about them to the checks file; lemmas about laws and distances
   stay, and the reduced file loses its `Require` of the rows file, so the
   surviving arrow runs from the mathematics up into the tableau. The reduced
   file is staged under `staged/` in its production position.
3. Comment-only repoints of OTHER production files that cite a retired file
   name are staged under `staged-comments/`, never under `staged/`: `staged/`
   is an `-R` root and a copy there shadows the module it copies.
4. Declarations that move from a file whose last `Local Open Scope` differs
   from the phase files' are re-read under another scope block. Pin it: the
   baseline file ascribes each of them at its production statement under the
   phase files' block.
5. A phase header names separately what the manifest publishes and what this
   development's programs do; check which manifest rows belong to the instance
   by reading the manifest, not by the row's number.

## Second addendum: the twelve rulings of the PSL(2,11) audit (2026-09-20)

Read `notes/probes/2026-09-20-tableau-directories-psl211/audit-psl211.md`,
section "Rulings to carry to PGL(2,7) and five-card", before writing any header.
In one line each: "the value the run is meant to recover" below Observed, never
"recovers"; a record no program continues still carries statements, so say "the
only security statement made at it is" after a grep; one premise, one
rejection, and a `Fail` about an existing term is not a refusal of a term nobody
wrote; the Sampled obligation is about the run argument and the cut, not the
layout; in an AnalysisBridged header write "every statement here that
quantifies over a coalition"; the reduced mathematics file stays a file of its
own and is not folded into the model file; earn every phase import and re-run
the `Fail` check if one is dropped; a box content line ends with a space before
`*)`, which a width check does not see; `Print Assumptions` every new
definition; a published row is a program, not a claim; `baseline.v` (production
modules, the phase files' scope block) is the scope pin, `fidelity.v` is not;
regenerate every count in STATUS.md from the script's output.
