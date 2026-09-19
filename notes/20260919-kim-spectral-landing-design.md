# Landing Kim's two five-card rows through the spectral arm

Date: 2026-09-19

Status: LANDED on 2026-09-19. Production commits `3b9e463`
(`lib/var_dist_supp.v`) and `871a4c3` (the new
`instances/kim2025/five_card_mixing.v`, the facade, the manifest, its client
and the rows file, with two `_CoqProject` lines). Three audit rounds on the
landing probe `notes/probes/2026-09-19-kim-spectral-landing/`; what they
changed is the section "Changes after the audits" below. Plan:
`docs/superpowers/plans/2026-09-19-kim-spectral-landing.md`. As-built record:
the last section of that probe's `STATUS.md`. Follows
[[20260919-kim-spectral-arm-probe-design]], whose probe
`notes/probes/2026-09-19-kim-spectral-arm/` (SRC below) is the verbatim source
of every declaration. Summary of what was found:
[[2026-09-19-112500-spectral-arm-at-kim-and-psl211-summary]].

## Problem

The paper tells one story about every instance: an ideal model with a uniform
cut, which is private, and an actual model with a biased cut, which is close to
it. The five-card instance has the ideal row as a program. Its two actual
models, Kim's one biased cut and Kim's seven biased cuts, stop at `Sampled`, and
the manifest records the repeated one at `Sampled` with no model comparison.
The probe proved the two certificate fields that were missing, so both rows can
be certified by the existing arm. What remains is to put that into the
permanent files without leaving a sentence, a pin or a status that says
otherwise. The feasibility probe could not test that, because a declaration
meets a new context when it moves, and because the manifest, the instance's
analysis facade and the rows file each state these rows' levels in their own
words.

## Decisions, each with its reason

1. **Both forms of each row land**, as at PGL(2,7), which has
   `pgl27_row_word_tableau` and `pgl27_row_word39`. The program that publishes
   the manifest row carries the certificate's own number: `kim_centi_cert` and
   `kim_biased_cert`. Beside it a repriced program publishes the number a paper
   cites: `2^-39` for the repeated row and the exact `1/25` for the one-cut
   row. Reason: the first shows the spectral number the row proved, the second
   is what the text quotes, and the pair is the tree's existing pattern. When
   `conclude` takes an inequality the certificate `kim_centi_cert40` becomes
   unnecessary, and that is recorded as a later simplification, not done here.
2. **The mixing and constancy theorems live below the analysis facade**, in a
   new `instances/kim2025/five_card_mixing.v`, which holds the whole dependency
   cone of the theorems the facade aliases, as computed in SRC `STATUS.md`.
   Reason: a row at `IdealFinite` whose base premise the manifest cannot name
   contradicts the manifest's own convention, and PGL(2,7) does it this way
   (`pgl27_mixing.v`, aliased at `pgl27_analysis.v:267`). All four mixing
   statements go there, those of both forms, so that the rows file holds
   certificates and programs only. The facade aliases the three the published
   manifest rows rest on.
3. **Generic lemmas go to a new `lib/var_dist_supp.v`**, with one line in
   `_CoqProject` after its dependencies. Reason: they are library facts with no
   PGG content, and their subject-matter neighbour
   `security/pgg_collusion_bound.v` has `psl211_endpoints` among its
   reverse-dependants, so it must not be edited.
4. **The two `Tableau Sampled` programs stay as they are.** The certified
   programs are added beside them and start from `five_card_committed`, as the
   probe compiled them. Reason: the prefix and model lemmas and the recorded
   `Fail` keep compiling for their present reasons, and continuing from a named
   `Sampled` value is another batch's question.
   `five_card_row_repeated_at_manifest_level` cannot stay: it ascribes the
   `Sampled` program at the manifest's level, which moves. It is replaced by
   the row equation of the certified program.
5. **The leakage bound, the endpoint lemma and `kim_centi_small` stay where
   they are.** They remain true and say other things.
6. **The permanent text is produced in the landing probe and copied with
   `cp`.** Reason: it is the text the audits read and the text that compiled.

## Flow

The running value is the number the row publishes.

```
flow land_kim_rows                                                // number
object  five_card_committed : Tableau Observed                    // none, on main
file    lib/var_dist_supp.v, five generic lemmas                  // none
file    five_card_mixing.v below the facade, the cone             // none
alias   facade section 7 gains three aliases, one status alias splits // none
row     manifest: repeated to AnalysisBridged, IdealFinite        // none
row     manifest: biased to IdealFinite, seven erefl pins follow  // none
program repeated: certify SpectralDecay kim_centi_cert |> publish // 2*sqrt 5*(1/80)^7
program biased: certify SpectralDecay kim_biased_cert |> publish  // sqrt 5 / 40
program repeated39, biased_inv25, repriced                        // 2^-39, 1/25
outside the leakage bound, the endpoint lemma, the two Sampled programs
```

Roles. Objects: the prefix and the two sampled families. Step justifications:
the five certificate fields of each row, of which the mixing field enters
through `kim_centi_cut_mixing` or `kim_biased_cut_mixing` and the constancy
field through `five_card_static_obs_const`. Terminals: `publish`, and
`conclude` for the repriced pair. Assumptions invoked: none. Structure:
unchanged, the landing supplies payloads to existing statements.

## Pinned carrier

As in the feasibility spec: `amf_sample kim_centi_family R tt` and
`amf_sample kim_biased_family R tt` over an abstract `R : realType`.

## Claim ledger

| ID | Checkable claim | Passing evidence |
|---|---|---|
| L1a | The generic file compiles alone. | `lib/var_dist_supp.v` as a landing copy in the probe, importing no PGG file it does not need. `var_dist_point`-style duplicates of infotheo are not included. |
| L2 | The cone compiles below the facade. | A landing copy of the new `five_card_mixing.v` that imports neither the manifest, the Tableau files, nor the facade. The cone is recomputed by SRC's script and every member is present. |
| L3 | The facade with three aliases and the split status alias. | A full landing copy of `instances/kim2025/five_card_analysis.v` compiles, with its pins moved to the new values. The probe reports every line changed. |
| L4 | The manifest with both rows moved. | A full landing copy of `manifest/pgg_analysis_manifest.v` compiles against the facade copy, with all pins, both docstrings, the Row 3, 4 and 5 header tables and the "Absent capabilities" paragraph true of the new state. |
| L5 | Every reverse-dependant of the manifest still compiles. | Landing copies of `pgg_tableau.v`, `pgg_tableau_syntax.v`, `pgg_analysis_client.v`, `s5_rows.v`, `pgl27_rows.v`, `psl211_rows.v`, unchanged except for imports, compile against the manifest copy. `psl211_endpoints` is only loaded. |
| L6 | The rows file. | A full landing copy of `five_card_rows.v`: four certificates, four programs, their row equations by `erefl`, the two recorded failures that show what a row equation rejects, the number lemmas, the repricing identities, and a header true of the new state. `five_card_row_repeated_at_manifest_level` is gone and nothing else landed on 2026-09-19 is removed. |
| L7 | Breakages are found by the compiler. | The probe records every compile error it met on the way, with file and line, and checks the list against SRC `STATUS.md` S8. An error S8 did not predict is reported as such. |
| L8 | Sentences that become false are found by proposition. | A search of the production tree for each of the eleven propositions of SRC `STATUS.md`, in every spelling, and for any further one met in the Row 3, 4, 5 tables and the facade's section 7. Every hit is either changed in a landing copy or listed with the reason it stays. |
| L9 | Nothing else changes. | For each landing copy of an existing file, a diff against the production file, with every hunk explained. Code not part of the landing is byte-identical after comments are stripped. |
| L10 | Assumptions. | `Print Assumptions` on every new declaration, in a fidelity file that imports the landing copies: the three `boolp` axioms or closed. |
| L11 | Names and the barred term. | Names as in SRC after its five naming audits. The section and the lemma that share the name `five_card_static_obs_const` are told apart. The whole-word collision scan is rerun against the production tree. |
| L12 | Cost. | The list of production files a landing recompiles, from `.Makefile.rocq.d`, with measured times from the copies. Expected eleven plus the two new files. `psl211_endpoints` is not among them. |

## Soundness invariants

1. No new axiom, `Admitted` or `Abort`.
2. The certified statement is what SRC `STATUS.md` S9 says: coalitions of at
   most one seat, two committed pairs, the row's own cut law, static endpoint
   readings. No header or docstring says more. In particular none says
   independence from the secret, none speaks of two seats, none of the full
   reveal.
3. Every published number is compared with the ceiling 2 through `var_dist_le2`
   where a comment calls it small.
4. The manifest's transfer status for both rows is `IdealFinite`, and its prose
   names the ideal (the uniform rotation law) and the carrier (the cut group).
5. A row equation is not presented as evidence about a certificate.
6. `instances/psl211/psl211_endpoints.v` is never compiled. No file with it
   among its reverse-dependants is edited.

## Changes after the audits

Recorded on 2026-09-19 after three rounds. The decisions and the ledger above
stand as written, so that what was planned can be compared with what was done.

1. **A bridge theorem below the facade.** The first soundness audit showed that
   a mixing bound on the cut carrier names no observer, so it cannot fill the
   manifest's "final bridge theorem" cell. As at PGL(2,7)
   (`pgl27_word_view_indist_via_transfer`), `five_card_mixing.v` now states the
   conclusion of the transfer: `kim_centi_static_obs_indist` and
   `kim_biased_static_obs_indist`, a bound on the variation distance between
   the static readings of a coalition of at most one seat at two committed
   pairs. Rows 4 and 5 name them, declare the observer `static_obs`, and give
   each a capability line. Decision 2 said the facade aliases three theorems;
   it aliases seven, and the reader.
2. **The fidelity file is honest about direction.** One lemma per row takes the
   proposition the published certified row delivers (`view_indist_of`) to the
   corollary's statement, and one takes the corollary to `SpectralPropAt`; each
   uses the certificate's identification equation and nothing else. The two
   propositions are not convertible.
3. **`kim_biased_sample_cut_witnessE` sits below the facade**, stated at the
   adapter `kim_single_sample`, the shape `kim_centi_cut_distE` has; the
   certificate's identification field typechecks by conversion.
4. **`exec_transfer_status` is `uniform_transfer_status`**, since the facade now
   has three statuses named after their model families.
5. **The manifest's client changed.** Ledger row L5 expected every
   reverse-dependant to change by imports alone; `manifest/pgg_analysis_client.v`
   carried a sentence the landing made false and has four changed lines. Five
   files are recompiled and not copied.
6. **The S_5 sentence of the manifest** says the sum of absolute differences
   from group uniform is at least one, not one.
7. **The landing procedure was mechanical.** The probe's `tools/` hold the
   script that prints the import differences, the one that builds the
   permanent-form files under `staged/`, and the one that proves each staged
   file equals its probe copy outside `Require` sentences. Measured on the
   way: `Require` resolves a logical name to the last matching load-path
   entry, and `Locate Library` does not show what was loaded.
8. **A reverse-dependant the cost row could not list:**
   `instances/psl211/psl211_spectral_constancy.v` landed the same day, imports
   the manifest and the Tableau, and was recompiled (23 s).
9. **Left for stage A of the Tableau extensions:** under the weakened
   obligation of `conclude` the repeated row can publish `2^-39` from
   `kim_centi_cert` itself, which makes `kim_centi_cert40` and its two
   supporting declarations unnecessary; five sentences and three payload sites
   change. The list is in the probe's `STATUS.md`.

## Probe artifacts

Directory `notes/probes/2026-09-19-kim-spectral-landing/`, logical path
`kim_landing_probe`. Landing copies of the two new files and of every existing
file the landing edits or that depends on an edited file, with their imports of
one another pointed at the copies. A fidelity file. `_CoqProject`, `STATUS.md`,
the audit reports. After the audits, a plan under `docs/superpowers/plans/`
that quotes the copies, an implementation by `cp` in dependency order with a
single-file compile after each, and an as-built fidelity file that imports the
permanent modules.

## Sequencing with the Tableau extensions probe

Stage A of [[20260919-tableau-three-extensions-probe-design]] compiles copies
against the production manifest as it is now. The implementation step of this
landing rewrites that manifest's `.vo`, so it runs after stage A has finished
and before stage B starts, and stage B refreshes its copy of
`five_card_rows.v`. The landing probe itself touches no production file and
runs beside stage A through the shared Rocq lock.

## Out of scope

Any change to `manifest/pgg_tableau.v` or its syntax. The new arm of the
extensions probe. The leakage bound as a row. PSL(2,11). The paper.
