# The per-instance `tableau/` directories, as built (2026-09-20)

Where each Tableau phase of each instance lives now, which files were retired
or reduced, what a text that cites the code has to change, and what is left.
Design: `notes/2026-09-20-060000-instance-tableau-directory-design.md`.
Template the four instances followed:
`notes/probes/2026-09-20-tableau-directories-s5/staged/TEMPLATE.md`.

## The structure

Every instance has one directory `instances/<inst>/tableau/` with one file per
phase and one file of recorded rejections. The file name carries the phase.

```
<inst>_tableau_algebraic.v          the algebra as a program's first line
<inst>_tableau_executable.v         one named value per run mode, and its parameters equation
<inst>_tableau_observed.v           the observed prefixes, the functionality material
<inst>_tableau_sampled.v            one named value per model a program continues from
<inst>_tableau_analysis_bridged.v   witnesses and certificates, the published rows, the
                                    statements about them
<inst>_tableau_checks.v             recorded Fail terms, comparisons of two rows
```

| Instance | Directory | Commit | Declarations moved | New | Published rows |
|---|---|---|---|---|---|
| S5 | `instances/s5/tableau/` | 1fe5f7b | 21 | 9 | 1 |
| PSL(2,11) | `instances/psl211/tableau/` | 019f3f2 | 24 of 29 (5 stay) | 8 | 2 |
| PGL(2,7) | `instances/pgl27/tableau/` | c58c60f | 68 of 75 (7 stay) | 9 | 7 |
| five-card | `instances/kim2025/tableau/` | 94581dc | 89 of 93 (4 stay) | 10 | 7 |

Modules are `pgg_smc.tableau.<name>`: the directories sit under the recursive
`-R instances/<inst> pgg_smc` roots, a short `From pgg_smc Require Import
<name>` resolves them, and `_CoqProject` gained no `-R` line. No file uses
`Require Export`; each AnalysisBridged header says which phase file an importer
names for which kind of name. The mathematics did not move: `<inst>_exec.v`,
`<inst>_models.v`, the analysis facades and the manifest are unchanged, and no
file in the forward closure of `instances/psl211/psl211_endpoints.v` was
touched, compiled or moved.

## Retired and reduced files

| File | Fate |
|---|---|
| `instances/s5/s5_rows.v` | retired; all 21 declarations in `instances/s5/tableau/` |
| `instances/psl211/psl211_rows.v` | retired |
| `instances/pgl27/pgl27_rows.v` | retired |
| `instances/kim2025/five_card_rows.v` | retired |
| `instances/psl211/psl211_word_proximity.v` | reduced to the distance mathematics (140 lines): `psl211_word_proximity_close`, the two facts about 2^-40, `psl211_word_law_le2`, one recorded rejection |
| `instances/pgl27/pgl27_proximity.v` | reduced (289 lines): `pgl27_static_obsE`, `pgl27_static_obs_funE`, `pgl27_word_secret`, `pgl27_word_proximity_close`, the two facts about 2^-40, `pgl27_word_uniform_ideal_close_false` |
| `instances/kim2025/five_card_proximity.v` | reduced (169 lines): `five_card_uniform_pairE`, `five_card_reading_secretE`, `five_card_arg_cut_prodE`, `kim_biased_proximity_close` |

The three reduced files import no tableau, framework or manifest module: arrows
run upward only, from the mathematics into the tableau files.

## What a text that cites the code has to change

Nothing, as far as identifiers go: every declaration kept its name and its
statement. A scan of `paper/`, `paper-wadt2026/`,
`paper-wadt2026-baseline-application/`, `blueprint/`, `README.md` and
`docs/style/` on 2026-09-20, with and without the LaTeX escape of the
underscore, finds no mention of any of the four retired file names nor of the
three reduced ones. A text that names the FILE of a declaration should use the
table above; the identifiers renamed on 2026-09-19 and 2026-09-20 are listed in
`notes/2026-09-19-230614-renamed-identifiers-input-indistinguishability.md` and
in section "Departures" item 8 of
`notes/2026-09-20-054425-tableau-extensions-as-built.md`.

The new identifiers, all additions: per instance `<inst>_algebraic_start`,
`<inst>_<mode>_executable` with `<inst>_<mode>_executable_paramsE` and
`<inst>_<mode>_executableE`, `<inst>_<model>_sampled`, and one
`<row>_sampledE` per published row that was re-cut at a named Sampled value.

## How each instance was checked

A staged text in `notes/probes/2026-09-20-tableau-directories-<inst>/`,
generated from production by a script from the second instance on, so that a
moved declaration is verbatim by construction; `verify.py` (declaration-level
token identity, name-set equality, docstring word identity, the cut of the
proximity file checked both ways, section scaffolding, one scope block for the
six files, one-content-line banners, no index name touching `==`, box lines
ending in a space before the closing delimiter, and every recorded `Fail`
compiled without `Fail` in the preamble of the file it sits in, on both sides,
with the messages compared); a generated `baseline.v` loading production's
modules and `fidelity.v` loading the staged ones under the same scope block,
printing every non-`Fail` declaration's type, the body of every `Definition`
whose type hides a number, and `Print Assumptions` for every row and lemma,
the two outputs diffed; one Opus audit per instance of the new text, the
placement and the pattern; a fix pass by an Opus `rocq-prover`, audited by the
main session; `cp` with `cmp`; single-file compiles; and the unchanged fidelity
file compiled against production's load path alone after the retired file was
gone, its output byte-identical to the staged run's. `make` was never run:
the makefile regenerates itself when `_CoqProject` changes and would rebuild
`psl211_endpoints.v`.

## What the audits found

Placement and structure passed at every instance. Every NO-GO was on new
header or docstring sentences, and the classes repeated: a header saying what
the manifest does from what this development's programs do, or the reverse;
"recovers" below Observed; one premise made to carry two recorded rejections;
two headers of one directory placing or describing one declaration two ways; a
count that the move made false ("two models", "two levels above"); a hypothesis
dropped from an index entry. From the third instance on the prover ran a
pre-audit pass against the earlier audits' rulings, which removed most of them
before the audit; the rulings are collected in the template's three addenda.

Two defects that a green compile hid and the verification caught: a recorded
`Fail` that passed because `erefl` did not resolve in a file whose import list
lacked `ssrfun`, and a lemma sharing its name with a recorded `Fail`, which
must sit below it because a name's freedom is checked before a body is
elaborated.

## Left open

The closing pass of tracker step 2.5: three deferred comment repoints
(`manifest/pgg_analysis_manifest.v`, `instances/psl211/psl211_models.v`,
`instances/pgl27/pgl27_encoding_r5.v` still cite retired rows files), the
manifest header, and the twelve places where the four instances' phase files
say one thing in different words without a mathematical reason
(`notes/probes/2026-09-20-tableau-directories-five-card/audit-five-card.md`,
last section). The economic words in moved docstrings ("spends", "price",
"currencies") wait for the owner's decision, as does the type name `Reprice`.

Commit d3a1957 is a probe checkpoint that also carries the deletion of
`instances/psl211/psl211_rows.v`, staged one step early; the tree at that one
commit lacks the PSL(2,11) phase files, which the next production commit
019f3f2 adds. HEAD is unaffected. The history was not rewritten while agents
were working in the repository.
