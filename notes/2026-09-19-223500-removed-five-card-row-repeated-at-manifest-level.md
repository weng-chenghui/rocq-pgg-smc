# Removed: `five_card_row_repeated_at_manifest_level`

Date of this note: 2026-09-19. It corrects the record of
`notes/20260919-dealer-law-and-kim-rows-summary.md`, which lists the
declaration as built. That summary is a dated record and is left unchanged.

## What the declaration was

Added by commit 8dc3ba0 in `instances/kim2025/five_card_rows.v`:

```coq
Definition five_card_row_repeated_at_manifest_level
  : Tableau (apr_completion five_card_row_repeated) :=
  five_card_row_repeated_tableau.
```

It ascribed the repeated row's `Sampled` program at the completion level that
the manifest row `five_card_row_repeated` stated. At that commit the manifest
level was `Sampled`, so the ascription was accepted by conversion and said that
the manifest's level term and the program's level index were one term.

## Why it was removed

Commit 871a4c3 moved the manifest row `five_card_row_repeated` from `Sampled`
to `AnalysisBridged`, because the repeated row became certified by the arm now
named `InputIndistinguishability`. The `Sampled` program
`five_card_row_repeated_tableau` no longer has the manifest's level, so the
ascription stopped typechecking and was deleted in that commit. Decision 4 of
`notes/20260919-kim-spectral-landing-design.md` records the choice.

## What says the same thing now

The row equation of the certified program,
`five_card_row_repeated_indistinguishability_rowE` in
`instances/kim2025/five_card_rows.v`: the row published by the certified
program is the manifest row, level included. For the biased row the recorded
`Fail` on the same ascription and `five_card_row_biased_levelE` are unchanged.
