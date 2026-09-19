# Landing the PSL(2,11) constancy result

Date: 2026-09-19. Spec: `notes/20260919-psl211-spectral-nogo-landing-design.md`
(flow sketch and ledger there). Source of every byte that lands:
`notes/probes/2026-09-19-psl211-nogo-landing/` after fix pass 3, audited three
times (round 3: GO, Opus auditor; the four should-fix sentences of round 3 were
checked against the statements by the main session).

Operation: copy one audited file into the tree and compile it alone; the
invariant is that production code other than the new file is unchanged once
comments are stripped.
Monad: no such structure; two independent copies and two compiles.
DSL: none needed; the steps do not compose results, they move text.

## What lands

| Probe file | Permanent file | Change |
|---|---|---|
| `psl211_spectral_constancy.v` | `instances/psl211/psl211_spectral_constancy.v` | new, 46 declarations |
| `psl211_rows.v` | `instances/psl211/psl211_rows.v` | header comment only |

The landing copy of the new file imports production logical paths only, so it
is copied byte for byte. Nothing imports either file, so nothing else is
recompiled. `instances/psl211/psl211_endpoints.vo` is loaded and never rebuilt.

## Steps, one commit each

1. `_CoqProject`: insert the line
   `instances/psl211/psl211_spectral_constancy.v` directly before
   `instances/psl211/psl211_rows.v`. Reason: the file lists a file after the
   files it imports, and this keeps the four rows files together.
2. `cp` the new file. Compile it alone with the production flags through the
   shared Rocq lock. Pass: return code 0, no sentence above 10 s (the probe
   measured three at 5 to 7 s).
3. `cp` the rows copy over `instances/psl211/psl211_rows.v`. Before the copy,
   check that the probe copy equals production once comments are stripped.
   Compile it alone. Pass: return code 0.
4. As-built fidelity, by a rocq-prover subagent: a copy of
   `psl211_nogo_fidelity.v` named `psl211_asbuilt_fidelity.v` in the probe
   directory, importing `pgg_smc.psl211_spectral_constancy`. Pass: the same
   48 `Print Assumptions` results as the probe's fidelity file, 28 closed and
   20 within the three `boolp` axioms.
5. Record: the closure section of the probe's `STATUS.md`, the memory note,
   the status line of the spec.

## Not done here, recorded for later

- Eighteen sentences of `instances/psl211/psl211_models.v` use "deck
  description" for the deal. That file's reverse closure holds the manifest
  and every rows file, so it is not edited in this landing. The list is in
  the probe's `STATUS.md`.
- The Kim landing and the extensions probe each hold a copy of
  `psl211_rows.v` taken before this landing. Whichever lands next takes this
  landing's header as its base. The Kim landing does not copy that file at
  all; the extensions probe does.
- A move of the new file into `instances/psl211/tableau/` belongs to the
  directory batch.
