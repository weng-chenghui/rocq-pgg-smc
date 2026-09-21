# Manifest paths for the two programs over the PSL(2,11) dealer-dealt model (2026-09-21)

Spec with claim ledger, written before any probe. Left over from the reading
landing (tracker 4.5; reminder note, item 9): the two programs of
`instances/psl211/tableau/psl211_tableau_dealt.v` publish paths that are not
among the manifest's twelve, and their header says so.

## 1. The problem

The manifest is the list a reader audits: a path names the observed execution,
the level, the model family and the two statuses, and its capability lines
name theorem, distribution, observer and notion. Two published programs are
outside it:

- `psl211_colour_exact_published`: exact independence of the chirality from
  the colour reading, below six seats, over the dealer-dealt model, at every
  prior on the chirality;
- `psl211_dealt_obstruction_published`: the same model is input
  distinguishable of the coalition's endpoint reading at 1/660 at three seats
  (advantage at least 1/1320 for a distinguisher comparing the two run
  arguments).

The obstacle is the one the twelfth path met: the manifest sits BELOW the
Tableau (`manifest/pgg_tableau.v` requires it) and names only facade aliases of
`instances/psl211/psl211_analysis.v`, while today the dealer-dealt sample
adapter, its model family and both theorems live above the manifest
(`psl211_colour_reading.v` and `psl211_tableau_dealt.v` require the Tableau).

## 2. Design

1. A new file below the manifest,
   `instances/psl211/psl211_dealt_model.v` (name provisional), requiring
   nothing above `psl211_models.v`-level files: the adapter
   `psl211_dealt_sample` with its four law lemmas, the model family over
   `psl211_dealt_observed` indexed by the prior on the chirality, the colour
   map on endpoints (`psl211_colour_of_reading`) if the raw theorem needs it,
   and two RAW theorems stated with no Tableau definition:
   (a) at every coalition below the threshold, the colour map of the
   coalition's endpoints is independent of the chirality (`_|_` on the
   adapter's sample space), at every prior;
   (b) the inequality `1/660 <= var_dist ...` between the endpoint laws of the
   two chiralities at `psl211_perdeck_coalition` under the adapter's cut law.
2. `psl211_analysis.v`: facade aliases for the dealer-dealt model (observed
   execution, sample, family, the two theorems, the correctness theorem),
   named so that a reader cannot take them for the all-decks aliases.
3. `manifest/pgg_analysis_manifest.v`: Path 13 (colour reading, exact privacy;
   AnalysisBridged; StaticExecutedOnly; observer column: the colour map of the
   coalition's endpoints) and Path 14 (input distinguishability at 1/660;
   AnalysisBridged; NegativeTransfer), typed paths, the `Check` pins, every
   count of paths updated, `pgg_analysis_client.v` likewise.
4. `psl211_colour_reading.v` and `psl211_tableau_dealt.v`: what moved is
   required from below; the Tableau-level statements are derived from the raw
   ones; the two programs' `_pathE` equate the published path with the
   manifest's typed path by `exact: erefl`; the header sentence "not among the
   manifest's twelve" is replaced by what is the case.

## 3. Soundness invariants

1. No new axiom, no `Admitted`; `Print Assumptions` on both raw theorems and
   both programs: the three classical axioms only.
2. Statements do not change meaning: the raw theorem (a) is the independence
   field of the colour witness unfolded, and the raw (b) is the inequality the
   obstruction proves; each Tableau-level statement stays what it is today
   (checked by `Check` against today's statement in the fidelity file).
3. Capability labels are the narrowest the statements support: "exact privacy"
   for (a) WITH the observer named as the colour reading, never as the
   endpoints; "input distinguishability at 1/660" for (b).
4. Path 13's level justification must say the secret is the run argument over
   these parameters, and that the threshold six is sharp
   (`psl211_colour_reading_dep_k6`).
5. No frozen file is edited; `psl211_endpoints.v` is not compiled.
6. At PSL(2,11): no `rewrite` with a mass lemma in a goal holding both
   chiralities; the reading wrapper discharged in a `have` naming one
   chirality.

## 4. Claim ledger

| id | claim | passes when |
|---|---|---|
| M1 | the adapter, its four lemmas and the family need nothing above the manifest | a probe file with only below-manifest Requires compiles them, proofs verbatim |
| M2 | raw theorem (a) is provable below the manifest with the existing proof | `Qed` in the probe, no Tableau Require; say which lemmas of `psl211_colour_reading.v` must move with it |
| M3 | raw inequality (b) likewise | `Qed`, term-mode steps kept |
| M4 | `AnalysisModelFamily psl211_dealt_observed` typechecks below the manifest and its link lemma (`sampled_viewE_prop`) stays provable at the Tableau level from it | family in the probe; the Sampled program rebuilt against it |
| M5 | no Require cycle: new file <- `psl211_analysis.v` <- manifest <- Tableau <- colour and dealt Tableau files | the chain compiles in a staged tree |
| M6 | the two programs' published paths equal the two typed manifest paths | `exact: erefl`, each timed under `Timeout 300`, one at a time |
| M7 | every existing statement of the two files is unchanged | `Check (name : today's statement)` for each, in a fidelity file against the staged tree |
| M8 | reverse closure of the landing holds no frozen file | `closure.py` prints "frozen files met: none" |
| M9 | capability vocabulary suffices: "exact privacy" and "input distinguishability" | no new label; if the colour line needs one, stop and report |

## 5. Order of work

Probe (staged tree under `notes/probes/2026-09-21-dealt-manifest-paths/`), one
Opus audit of spec and probe (soundness and naming together, asked what is
worth landing), rulings, landing by an Opus rocq-prover, main-session
recompile of the closure and of the fidelity file, one audit of the landed
comments, fix pass, commit.

## 6. Probe and audit, folded (2026-09-21)

Records: `notes/probes/2026-09-21-dealt-manifest-paths/` (`LEDGER.md`,
`AUDIT.md`, `RULINGS.md`, the staged tree, `fidelity.v`). All nine rows GO.
`AnalysisModelFamily` is defined in `manifest/pgg_analysis_status.v`, below
the manifest, so the family moves down with no obstacle; 26 declarations move
verbatim into `instances/psl211/psl211_dealt_model.v`; the raw theorems are
`psl211_dealt_colour_indep` (the unfolding of `ReadingExactIndependence` at
the colour map, at the adapter's SAMPLE law) and
`psl211_dealt_perdeck_reading_ge` (the bare inequality at 1/660, twin of the
all-decks one); 35 existing statements unchanged; closure 34 files, no frozen
file. The audit's corrections are to the manifest prose: the distribution of
Path 13's theorem is the sample law and not the cut law, the two failure
sentences carry the premise that the prior gives mass to both chiralities,
and the comparison with Path 12 is restated. Landing: one commit, source the
staged tree with the rulings applied.

