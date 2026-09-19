# Landing probe: Kim's two five-card rows through the spectral arm

Date: 2026-09-19. Branch `feat/tableau-extensions-probe`, no commit, no
production file touched. Spec: `notes/20260919-kim-spectral-landing-design.md`.
Source of every declaration: `notes/probes/2026-09-19-kim-spectral-arm/` (SRC).
Logical path of this directory: `kim_landing_probe`.

Home decision taken: **option 2** of SRC `STATUS.md` S10, the new
`instances/kim2025/five_card_mixing.v` below the analysis facade.

## Verdict per ledger row

| ID | Verdict | Evidence |
|---|---|---|
| L1a | GO | `var_dist_supp.v` compiles alone in 4.6 s at mathcomp plus infotheo, requiring no PGG file. None of its five lemmas duplicates infotheo or the tree. |
| L2 | GO | `five_card_mixing.v` compiles in 4.3 s, requires neither the manifest, nor `pgg_analysis_status`, nor the Tableau files, nor the facade. Twenty-one declarations, the recomputed cone. |
| L3 | GO | `five_card_analysis.v` compiles in 4.8 s with three theorem aliases, a split status alias and the moved pins. Every changed line listed below. |
| L4 | GO | `pgg_analysis_manifest.v` compiles in 6.6 s with both rows moved, the five pins following, three new spelled-type pins, both docstrings, the Row 3, 4 and 5 tables and the "Absent capabilities" paragraph rewritten. |
| L5 | GO | `pgg_tableau.v`, `pgg_tableau_syntax.v`, `pgg_analysis_client.v`, `s5_rows.v`, `pgl27_rows.v`, `psl211_rows.v` compile against the manifest copy, each with one code hunk and that hunk an import. `psl211_endpoints.v` is only loaded. |
| L6 | GO | `five_card_rows.v` compiles in 7.2 s with four certificates, four programs, two row equations by `erefl`, three recorded failures, the number lemmas, the repricing identities and a rewritten header. `five_card_row_repeated_at_manifest_level` is gone and nothing else landed on 2026-09-19 is removed. |
| L7 | GO | Five breakages found by the compiler, all five predicted by SRC S8. No unpredicted error; no predicted error missing. Table below. |
| L8 | GO | 195 production `.v` files searched by proposition. Every five-card hit is inside one of the three files this landing changes. Table below. |
| L9 | GO | 35 diff hunks over nine copies; with comments stripped, 16 code hunks, of which 9 are import repoints and 7 are the landing itself. |
| L10 | GO | 62 `Print Assumptions` blocks: 9 closed under the global context, 53 the classical trio and nothing else. No repository axiom. |
| L11 | GO | Names as SRC left them after its five naming audits, except the section rename below. No collision with a production name. |
| L12 | GO | Eleven production files recompile, as S10 predicted for option 2, and `instances/psl211/psl211_endpoints.vo` is in none of their closures. |

## Compile table

Every invocation through the machine-wide `rocq1` lock, driven from Python, in
this directory, with the production flags and `-Q . kim_landing_probe`.

Figures from one clean run over the whole `_CoqProject` list, in that order,
after every file had already been compiled once on its own; the first-run
figures agree with these to within a second.

| file | rc | time |
|---|---|---|
| `var_dist_supp.v` | 0 | 4.4 s |
| `five_card_mixing.v` | 0 | 4.5 s |
| `five_card_analysis.v` | 0 | 4.4 s |
| `pgg_analysis_manifest.v` | 0 | 6.3 s |
| `pgg_tableau.v` | 0 | 13.4 s |
| `pgg_tableau_syntax.v` | 0 | 4.7 s |
| `pgg_analysis_client.v` | 0 | 4.0 s |
| `s5_rows.v` | 0 | 4.4 s |
| `pgl27_rows.v` | 0 | 6.5 s |
| `psl211_rows.v` | 0 | 5.8 s |
| `five_card_rows.v` | 0 | 7.5 s |
| `kim_landing_fidelity.v` | 0 | 22.6 s |
| `l7_fail_messages.v` (diagnostic, expected to fail) | 1 | 7.9 s |

The manifest, the file feared long at 1905 lines, compiles in 6.3 s. The
eleven landing files together are about 66 s, and the whole list including
the fidelity file is about 89 s.

`l7_fail_messages.v` is a diagnostic and is not in `_CoqProject`. It states,
without the `Fail` guard, the declaration `five_card_rows.v` keeps as a
recorded `Fail`, because `rocq compile` prints nothing for a guard that
passes.

## L12: what a landing recompiles

The manifest's reverse-dependants read off `.Makefile.rocq.d`: `pgg_tableau`,
`pgg_tableau_syntax`, `pgg_analysis_client`, `five_card_rows`, `pgl27_rows`,
`s5_rows`, `psl211_rows`. Seven, as SRC S10 says. Eleven files recompile in
all: two new files (`lib/var_dist_supp.v`,
`instances/kim2025/five_card_mixing.v`), two edited
(`instances/kim2025/five_card_analysis.v`,
`manifest/pgg_analysis_manifest.v`), one both edited and following
(`instances/kim2025/five_card_rows.v`), and six following. `_CoqProject` needs
two new lines, one for each new file, after its dependencies.
`instances/psl211/psl211_endpoints.v` is in no closure and was never compiled.

## L7: the breakages, against SRC S8's predictions

The manifest row change was applied first and the pins reverted to their
production text; the copy was then compiled repeatedly, each run fixing the
pin the previous run stopped at. `coqc` halts at the first error, so the pass
is an iteration.

| # | file | line | first message line | predicted by S8 |
|---|---|---|---|---|
| 1 | `pgg_analysis_manifest.v` | 1458 | `The term "erefl" has type` (`FiveCardAnalysis.repeated_transfer_status = NoModelComparison`) | yes, S8 facade item 5 (`:1388-1389`) |
| 2 | `pgg_analysis_manifest.v` | 1849 | `The term "erefl" has type` (`apr_transfer five_card_row_biased = StaticExecutedOnly`) | yes, S8 pin table (`:1779-1780`) |
| 3 | `pgg_analysis_manifest.v` | 1856 | `The term "erefl" has type` (`apr_completion five_card_row_repeated = Sampled`) | yes, S8 pin table (`:1787`) |
| 4 | `pgg_analysis_manifest.v` | 1859 | `The term "erefl" has type` (`apr_transfer five_card_row_repeated = NoModelComparison`) | yes, S8 pin table (`:1788-1789`) |
| 5 | `five_card_rows.v` | 459 | `The term "five_card_row_repeated_tableau" has type "Tableau Sampled" while it is expected to have type "Tableau (apr_completion five_card_row_repeated)".` | yes, S8 `five_card_rows.v` item 1 |

Line numbers are the copies'. Breakage 5 is at production `:456-458`; the copy
carries one extra import line before it.

No error occurred that S8 did not predict. No breakage S8 predicted failed to
occur. The two pins S8 says keep their values,
`apr_completion five_card_row_biased = AnalysisBridged` and the two
`apr_assumptions` pins, did keep them, and
`FiveCardAnalysis.exec_transfer_status = StaticExecutedOnly` kept its value
too, because the split leaves that name on the uniform path (below).

`pgg_analysis_client.v` is safe, as S8 says: its four `Check`s name terms and
assert nothing about their values. Confirmed by compiling it unchanged except
for its import.

## The recorded failures of `five_card_rows.v`

Three, and what each shows.

- `five_card_row_repeated_spectral_uniform_rowE`, new here. It is the row
  equation the task asks be kept, a certified program against the **uniform**
  row. `rocq compile` prints nothing for a passing guard, so
  `l7_fail_messages.v` states it unguarded; the message is
  `The term "erefl" has type "published_row five_card_row_repeated_spectral_tableau = published_row five_card_row_repeated_spectral_tableau" while it is expected to have type "published_row five_card_row_repeated_spectral_tableau = five_card_row_uniform" (cannot unify ...)`.
  The two rows differ in the model family and in the transfer status.
- `five_card_row_repeated39_bare`, copied from SRC: `conclude` asks for one
  identity per real field and per index.
- `five_card_row_biased_at_manifest_level`, already in the file. It still
  fails and for its present reason, the level gap between
  `five_card_row_biased_tableau` at `Sampled` and the manifest's row at
  `AnalysisBridged`. Its docstring and that of
  `five_card_row_biased_levelE` are rewritten: both were true of the path and
  are now true only of that one program.

`five_card_row_s5_family` is untouched.

## Where each declaration went

`lib/var_dist_supp.v`, five lemmas: `var_dist_le2`,
`var_dist_fdistmap_supp_inj`, `fdistmap_inj_uniform_id`,
`fdistmap_neq0_codom`, `card_tnth_count`. SRC's mutation lemma
`var_dist_fdistmap_const_neq` and its recorded `Fail` stay in SRC and do not
land, and the two `Check` lines that were the file's only reason to require
`security/pgg_collusion_bound.v` are dropped with it, so the file sits at
mathcomp plus infotheo.

Checked against duplication: infotheo has no `var_dist_le2`, no
`fdistmap_inj_uniform_id`, no `fdistmap_neq0_codom`, no
`var_dist_fdistmap_supp_inj` and no `card_tnth_count`; the only `var_dist`
lemma its `probability/variation_dist.v` states is `def_var_dist`. The tree
has `var_dist_triangle`, `var_dist_fdistmap`, `var_dist_fdistmap_inj` and
`fdistmap_inj_uniform` in `security/pgg_collusion_bound.v`, and
`leq_var_dist` is infotheo's, used at
`protocol/card_protocol_posterior.v:178`. None of the five duplicates any of
them: `fdistmap_inj_uniform` concludes uniformity on the image of a map
between two types, `fdistmap_inj_uniform_id` concludes the uniform law itself
at an endomap.

**`card_tnth_count` goes in `lib/var_dist_supp.v`.** Its only consumer is
`den_boer_layout_law_const`, which under option 2 is in
`instances/kim2025/five_card_mixing.v`, so the counting fact has to be below
that file. Of the three homes S10 offers, `den_boer_encoding.v` adds that
file and its sixteen reverse-dependants to the landing, taking the recompile
set from eleven to eighteen; a third new `lib/` file costs a third
`_CoqProject` line and a file holding one lemma; and decision 3 of the spec
fixes the name `var_dist_supp.v`, so the fact sits under a file name that
does not cover it. The residual is a name, and it is the cheapest of the
three. It is flagged for the user: the honest alternative is to widen the
file's name, which decision 3 would have to be reopened to allow.

`instances/kim2025/five_card_mixing.v`, twenty-one declarations. SRC's
published closure script was rerun here against SRC's own `.glob` files, with
the roots extended by the two form-2 mixing statements. At the three original
roots it reproduces SRC's published output exactly, 12, 13 and 6 with a union
of 17, and the two added roots have cones of 13 each. The union of all five,
counting the roots, is 25: four generic members, which are the `lib/` file's,
and twenty-one instance-specific ones, which are this file's. The script also
reports zero references into `pgg_analysis_manifest`, `pgg_analysis_status`,
`pgg_tableau`, `pgg_tableau_syntax`, `five_card_analysis` or `five_card_rows`
from anywhere inside the five cones, so nothing in the file could have been
forced to stay above the facade. Decision 2 of the spec therefore adds five
declarations and not two:
`kim_centi_marginal_bound40` and `kim_centi_cut_mixing40`, and
`kim_one_cut_centi_le`, `kim_biased_marginal_bound_exact` and
`kim_biased_cut_mixing_exact`. Nothing in the file mentions `SpectralCert` or
any other manifest-layer record, so nothing had to stay in the rows file for
that reason.

`kim_biased_epsE` and `kim_biased_exact_le_eps` are in SRC's
`kim_sc_close_probe.v` beside the mixing statements but are in no cone, so
they go to `five_card_rows.v`, as S10 option 2 says. That is what brings
`Require Import Lia.` and `From mathcomp Require Import zify.` into the rows
file, spelled as `instances/kim2025/five_card_kim.v:74-75` already spells
them.

## Naming

Names as SRC left them. One rename, the one the spec asks for: SRC's
`Section five_card_static_obs_const` enclosed a lemma of the same name. The
section is now `Section five_card_colour_census`, after what it holds, and
the lemma keeps its name.

The three new facade aliases follow the facade's own convention, which drops
the `five_card_`, `den_boer_` and `kim_` prefixes of their targets:
`centi_cut_mixing`, `biased_cut_mixing`, `static_obs_const`. They sit beside
the existing `centi_sample`, `centi_cut_distE`, `centi_bundle` and
`biased_family`.

The status alias split keeps the name `exec_transfer_status` on the **uniform**
path and adds `biased_transfer_status` for the single-biased path. Keeping the
old name is forced, not chosen: `manifest/pgg_analysis_client.v:48` has a bare
`Check FiveCardAnalysis.exec_transfer_status.`, and renaming it would break a
file this landing must leave alone but for its import, which is what ledger
row L5 exists to show. The residual is that the name says "exec" and no longer
says which of the two exact-cut paths it means; its docstring now says so.

## L8: the propositions, and where the tree states them

195 production `.v` files searched, in the twelve project directories and
`legacy/`, by proposition and not by row name. Fourteen propositions: SRC's
eleven, plus three met while reading the Row 3, 4 and 5 tables and the
facade's section 7.

| proposition | hits | disposition |
|---|---|---|
| no ideal distribution equality at the five-card development | `pgg_analysis_manifest.v:244-248`, `:669-673`, `:753-755`; `five_card_analysis.v:351-358` | all four changed |
| the same proposition at the S_5 path | `s5_analysis.v:340`, `:423`; `s5_models.v:56`; `pgg_analysis_manifest.v:675`; `legacy/instances/s5x5/*` | stays: it is true of S_5, where the constancy a spectral certificate asks for is false |
| the vocabulary that defines the statuses | `pgg_analysis_status.v:70-71` | stays: it defines `IdealFinite` and is the criterion the landing meets |
| both Kim programs stop at `Sampled`, and the level gap | `five_card_rows.v:384`, `:395`, `:462` | all three changed; each is now stated of one named program |
| endpoint marginals only, no security statement attached | `five_card_analysis.v:367`; `pgg_analysis_manifest.v:359` | both changed |
| no model comparison, no transfer-layer result exists | `five_card_analysis.v:351`; `pgg_analysis_manifest.v:669`, `:1381` | all three changed |
| the same words at rows 1, 2, 6, 7 | `pgg_analysis_manifest.v:116`, `:406`, `:460`, `:597` | stay: other paths, untouched |
| nothing to alias, section 7 empty | `five_card_analysis.v:16-17`, `:351-358`, `:431` | all three changed |
| a count of the five-card rows or programs | `five_card_rows.v:4`, `:28-30`, `:413`, `:416` | `:4` and `:28-30` changed; `:413` and `:416` say the three rows share one prefix, which stays true of the three prefixed programs |
| row counts by completion level or transfer status | none at the five-card rows | nothing to change; the two hits in `groups/` and `instances/psl211/` are about tables of a different kind |
| the biased path carries no shuffle certificate | `pgg_analysis_manifest.v:301-302` | changed |
| the repeated path's bound-or-certificate list | `pgg_analysis_manifest.v:351-354` | changed |
| no final bridge theorem | `pgg_analysis_manifest.v:355` | changed; the hit at `:405` is the S_5 deterministic row and stays |
| the bundle does not raise the level | `pgg_analysis_manifest.v:379-380` | changed |
| every `StaticExecutedOnly` or `NoModelComparison` path names what it lacks | `pgg_analysis_manifest.v:664-665` | changed, from "the premise it lacks" to "what it lacks", because row 3 now lacks a second model and not a premise |
| the manifest's criterion met by a theorem no arm takes | `five_card_rows.v:49` | changed; the sentence stays in the file as the description of `s5_row_word` |
| the five-card typed statuses as prose | `five_card_analysis.v:364`, `:368`; `five_card_rows.v:333`; `pgg_analysis_manifest.v:751`, `:758`, `:763`, `:768`, `:772`, `:775`, `:778` | `:364` keeps its value with a new docstring, `:368` moves; `five_card_rows.v:333` stays, it is the uniform row's program and gives the same reason the landing gives for row 3; the manifest's uniform-row lines stay, the biased and repeated lines move |

Outside the `.v` files: `notes/20260919-kim-tableau-sampled-design.md` and
`docs/superpowers/plans/2026-09-19-kim-tableau-sampled.md` are dated as-built
records of an executed batch. They stay. SRC's instruction holds: the landing
plan adds one dated superseding line to the design note's status block and
leaves the plan's as-built table alone. That is a step for the implementation
plan, not for this probe, which edits no file outside this directory.

One further record expires with a landing, as SRC says:
`notes/probes/2026-09-19-kim-spectral-arm/soundness-audit.md:336-337` says no
lemma in the tree proves the ceiling two. That becomes false the moment
`lib/var_dist_supp.v` lands.

## L9: the diffs

Nine copies of existing files, 35 hunks with comments, 16 with comments
stripped.

| copy | hunks | code hunks | what the code hunks are |
|---|---|---|---|
| `pgg_tableau.v` | 1 | 1 | the import of the manifest, repointed |
| `pgg_tableau_syntax.v` | 1 | 1 | the same |
| `pgg_analysis_client.v` | 1 | 1 | the same |
| `s5_rows.v` | 1 | 1 | the same |
| `pgl27_rows.v` | 1 | 1 | the same |
| `psl211_rows.v` | 1 | 1 | the same |
| `five_card_analysis.v` | 5 | 4 | the import of `five_card_mixing`; three alias definitions and the status split; one spelled-type pin; two status pins |
| `pgg_analysis_manifest.v` | 15 | 6 | the import of the facade copy; the two row definitions; three spelled-type pins; the facade status pins; the two biased-row pins; the two repeated-row pins |
| `five_card_rows.v` | 9 | 4 | three import lines; the deletion of `five_card_row_repeated_at_manifest_level`; the twenty-six new declarations and three recorded failures |

Every other code line is identical after comments are stripped. The
comment-only hunks are the header, table and docstring rewrites listed under
L8.

A guard script over every `Require` line of every file in this directory
reports that no copy loads the production `.vo` of a module that also exists
here.

## Changed lines, file by file

`instances/kim2025/five_card_analysis.v`, six edits:

1. `:16-17`, the header sentence "Section 7 is empty for this development and
   is documented as empty rather than omitted" becomes four lines naming what
   the section carries.
2. `:56-57`, the phase-H1 check table gains three rows, for the two cut-law
   distances and the reading constancy.
3. `:86`, one import line added, `five_card_mixing`.
4. `:351-358`, the section 7 header, nine lines replaced.
5. `:361-368`, the two status definitions replaced by three theorem aliases
   and three typed statuses. `exec_transfer_status` keeps
   `StaticExecutedOnly` and gains a docstring saying it is the uniform path's;
   `biased_transfer_status := IdealFinite` is new;
   `repeated_transfer_status` moves from `NoModelComparison` to
   `IdealFinite`.
6. `:431-436`, the retention block: its comment, one spelled-type `Check` on
   `centi_cut_mixing` as the section's representative (the file's own contract
   at `:372-382` asks for one per section), and three status pins in place of
   two.

`manifest/pgg_analysis_manifest.v`, eighteen edits:

1. `:75-76`, the `Require Export` line split, the facade coming from the copy.
2. `:66`, the closed capability vocabulary of convention (3) gains
   "cut-carrier mixing". This is the one term the landing adds to a list the
   file declares closed; the alternative was to leave the Row 4 and Row 5
   capability tables silent about the theorem that raises the rows.
3. `:244-248`, Row 3's missing-premise cell.
4. `:301-302`, Row 4's bound-or-certificate cell.
5. `:305-308`, Row 4's model transfer, missing premise and transfer status.
6. `:314-316`, Row 4's capability table gains a line for `biased_cut_mixing`.
7. `:326-328`, Row 4's level justification gains the transfer sentence.
8. `:351-362`, Row 5's table: bound or certificate, final bridge theorem,
   model transfer, missing premise, completion level, transfer status.
9. `:370-372`, Row 5's capability table gains a line for `centi_cut_mixing`.
10. `:374-380`, Row 5's level justification.
11. `:664-665`, "names the premise it lacks".
12. `:669-673`, the "Absent capabilities" five-card paragraph.
13. `:753-755`, `five_card_row_uniform`'s docstring clause.
14. `:760-768`, `five_card_row_biased`, docstring and `apr_transfer`.
15. `:770-778`, `five_card_row_repeated`, docstring, `apr_completion` and
    `apr_transfer`.
16. `:1381-1389`, the facade-status checker: its comment, three spelled-type
    `Check`s on the new aliases, on the pattern of the `PGL27Analysis`
    `word_mixing` pin at `:1048`, and three status pins.
17. `:1779-1780`, `apr_transfer five_card_row_biased`.
18. `:1787-1789`, `apr_completion` and `apr_transfer` of
    `five_card_row_repeated`.

`instances/kim2025/five_card_rows.v`, fourteen edits: the three import lines,
the file-title line `:4`, the header passage `:28-50`, the two index blocks
`:81-86` and `:109-110` and `:119-122`, the two `Sampled` programs'
docstrings `:383-389` and `:394-400`, the deletion of `:452-458`, the two
level-gap docstrings `:460-464` and `:469-472`, and the new section of
twenty-six declarations and three recorded failures.

## Proofs that needed a fix in the new context

None. Every proof copied from SRC compiles unchanged in its new file. The only
adjustments are declarative:

- `lib/var_dist_supp.v` drops `From pgg_smc Require Import
  pgg_collusion_bound.` and `From mathcomp Require Import fingroup perm.`,
  neither of which any of its five lemmas needs once the two `Check` lines
  and the mutation lemma are left in SRC.
- `five_card_mixing.v` drops `Require Import Lia.` and `From mathcomp Require
  Import zify.`, which SRC's `kim_sc_close_probe.v` carried for
  `kim_biased_exact_le_eps` alone, and that lemma is in the rows file.
- `five_card_rows.v` gains `Require Import Lia.`, `From mathcomp Require
  Import zify.` and `lra`, for `kim_biased_exact_le_eps`,
  `kim_biased_cert_eps_lt2`, `five_card_inv50_split` and
  `five_card_reprice_inv25_lt2`.
- the two lemmas that were inside SRC's `Section five_card_cut_mixing` with a
  `Variable R` are restated with an explicit `(R : realType)` binder, which is
  what discharging that section produces anyway.

## L10: assumptions

`kim_landing_fidelity.v` imports the copies and nothing else, restates the two
row equations, and prints the assumptions of all 62 declarations the landing
adds or moves. Nine are closed under the global context; 53 report the
classical trio `propositional_extensionality`,
`functional_extensionality_dep`, `constructive_indefinite_description` and
nothing else. No repository axiom, no `Admitted`, no `Abort`, no `Parameter`,
no `admit`.

## What the certified statement is

As SRC S9 states it, and no header or docstring in this directory says more:
for each real field, for every coalition of at most one of the five seats and
for every two committed pairs, the variation distance between the law of that
coalition's static endpoint reading under the row's own cut law at one pair
and the same law at the other is at most the row's published number, the
ideal being the uniform rotation law on the cut group. It is not independence
of the reading from the secret, it is not a statement about two or more
seats, and it is not a statement about the full reveal.

## What the spec or SRC got wrong

1. The task text says `five_card_rows.v` "uses `(** ... *)` docstrings that
   begin with the identifier". It does not: every docstring in that file
   begins with a descriptive phrase, for instance `(** The repeated row: ...`
   and `(** A model built over one run does not sample another. ...`. The new
   declarations follow the file as it is. `five_card_analysis.v`,
   `pgl27_mixing.v` and the `lib/` files do begin with the identifier, and
   the new declarations in those two places do too.
2. Decision 2 of the spec says the mixing file takes "the two form-2 mixing
   statements ... and whatever THEIR cone needs". Their cone needs three
   further declarations beyond the two named in the task's parenthesis, not
   two: `kim_one_cut_centi_le` as well as `kim_centi_marginal_bound40` and
   `kim_biased_marginal_bound_exact`. The file holds twenty-one declarations,
   not eighteen.
3. The spec's L12 expects "eleven plus the two new files". The eleven already
   include the two new files; the recompile set is eleven, not thirteen.
4. SRC S10 sends `kim_biased_epsE` and `kim_biased_exact_le_eps` to
   `five_card_rows.v` without noting that this is what moves `Lia` and `zify`
   into that file's imports.
5. SRC S8 does not mention that the facade's own retention-check contract
   (`five_card_analysis.v:372-382`, "one representative per section") obliges
   section 7 to gain a spelled-type `Check` once it has theorems, nor that the
   manifest's convention (3) declares its capability vocabulary closed, so a
   cut-carrier mixing capability line needs that vocabulary widened. Both are
   done here and both are judgement calls a reviewer should confirm.
6. SRC S8 says the facade's status alias "must split in two". It does not say
   that `manifest/pgg_analysis_client.v:48` pins the name
   `exec_transfer_status` with a bare `Check`, so the split cannot rename it
   without editing a file ledger row L5 requires be left alone.
