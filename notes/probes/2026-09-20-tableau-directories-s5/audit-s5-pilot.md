# Adversarial audit of the S5 tableau-directory pilot

Read-only audit of the frozen export at
`/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc/493d5ea4-6d9f-45fd-89c2-07339e63cb36/scratchpad/dirs_s5_frozen/notes/probes/2026-09-20-tableau-directories-s5/`
(same path in the repository at `f7287e3`). Nothing in the repository was
edited except this file. Nothing was compiled and `make` was not run. Paths in
the table are relative to that export root; the `.v` files land at
`instances/s5/tableau/`.

The mechanical result already established by the main session (21 of 21
declarations token-identical, 18 of 18 docstrings word-identical, byte-identical
`Print Assumptions`, both `Fail`s rejecting with production's message) was not
redone. This audit is about the seven new declarations, the six new file
headers, the placement of the 21 moved items, and the pattern.

## VERDICT: NO-GO as it stands, GO after F1 to F6

The structure is right and the pattern is sound: one file per phase, the phase
in the file name, the import chain in phase order, no `-R` line, no module-name
collision, a complete retirement inventory, and a fidelity file that pins every
production statement. Nothing in the reorganization is wrong.

What blocks the copy is the new prose. Six sentences in the new headers and
docstrings state something the tree does not support, and two of them are about
the same object: the header of the Observed file says the dealer-dealt run
stops at Observed, and the header of the Sampled file says no row of the
instance continues from the word model, while `manifest/pgg_analysis_manifest.v`
carries `s5_row_word`, an `AnalysisPathRow` at `AnalysisBridged` whose observed
execution is the dealer-dealt run's and whose model is `s5_word_family`. A third
drops the quantifier that makes the impossibility argument in the Sampled header
go through, and that paragraph is the one
`instances/kim2025/five_card_rows.v:59` will cite after the move. These are
exactly the class of defect the campaign exists to catch: a sentence that is
false about the domain while the kernel is green, and this pilot is a template
that would copy each of them into three more instances.

F1 to F6 are single-sentence rewrites in text that nothing depends on. Once
they are applied, the copy may proceed and the pattern may be reused, with the
rulings in the last section applied to the template first.

## Findings

| id | class | file:line | quoted text or object | problem, with evidence | replacement or recommendation |
|---|---|---|---|---|---|
| F1 | MUST | `staged/instances/s5/tableau/s5_tableau_observed.v:14` | "The dealer-dealt run stops here for good: the manifest row s5_row_det it answers has no model and no security payload" | False about the run. `s5_row_det` indeed carries no model (`manifest/pgg_analysis_manifest.v:1034`, `apr_model … None`), but the dealer-dealt run's observed execution is `s5_observed` (`instances/s5/s5_exec.v:432`, aliased `S5Analysis.observed` at `instances/s5/s5_analysis.v:138`), and `s5_row_word` (`pgg_analysis_manifest.v:1056`) is `@MkAnalysisPathRow S5Analysis.observed AnalysisBridged S5Analysis.word_family IdealFinite …`, pinned at `:2168-2174` as `apr_completion = AnalysisBridged`. The dealer-dealt run therefore reaches AnalysisBridged in the manifest under a second model. Production's own header says so: `instances/s5/s5_rows.v:54`, "The manifest carries a third five-seat row, s5_row_word". | "The dealer-dealt run's program stops here: the manifest row s5_row_det it answers carries no model and no security payload, because the canonical encoding it deals puts the whole secret on one card, so the single seat the cut sends that card to reads the secret, as does every coalition containing that seat. The manifest carries a second row over this run, s5_row_word, under a finite-word model; the Sampled file records why no program of this instance continues from that model." |
| F2 | MUST | `s5_tableau_sampled.v:19` | "The instance's other model, the finite word over the four adjacent transpositions, is not named at this level, because no row of the instance continues from it." | Same evidence as F1: `s5_row_word` is a row of this instance, at AnalysisBridged, whose model is `s5_word_family` (`instances/s5/s5_models.v:455`, an `AnalysisModelFamily s5_observed`). What is true is that no *program* of this development continues from it. The word family is also typed over the dealer-dealt run, not the supplied one, so it could not be adjoined to `s5_supplied` in any case, and the header does not say this. | "The instance's other model, the finite word over the four adjacent transpositions, is not named at this level. It is a model of the dealer-dealt run, and the manifest's row over it, s5_row_word, is published from a mixing theorem rather than from a program: two of the five parts of an input-indistinguishability certificate over that model are out of reach." |
| F3 | MUST | `s5_tableau_sampled.v:26` | "Missing too, and for a reason no proof can remove, is the constancy of a coalition's reading of the ideal cut in the secret: under every cut exactly one seat holds the card carrying the whole secret, so that seat's reading law moves with the secret, and the seat in question varies with the cut while the ideal is fixed before any coalition is named." | The clause that makes this an impossibility rather than one awkward seat is missing. Production has it (`instances/s5/s5_rows.v:66-72`): "which the field asks for at every coalition below the threshold and so at every singleton", and "and no choice of ideal avoids it". The certificate's constancy field is quantified over every coalition below the threshold (`manifest/pgg_tableau.v:743`, `ic_const … C HC x x'`, under `#|C| < profile_k`), so the singleton containing the secret-bearing seat is one of the coalitions asked about. Without the quantifier the text asserts "no proof can remove" while exhibiting only one seat. `instances/kim2025/five_card_rows.v:59` cites this paragraph for the claim that the constancy "is false", so the cited text has to carry the argument. | "Missing too, and for a reason no proof can remove, is the constancy of a coalition's reading of the ideal cut in the secret, which the certificate's constancy field asks for at every coalition below the threshold and so at every singleton: under every cut exactly one seat holds the card carrying the whole secret, so that seat's reading law moves with the secret, and no choice of ideal avoids it, the seat in question varying with the cut while the ideal is fixed before any coalition is named." |
| F4 | MUST | `s5_tableau_executable.v:8` | "The proposition is still True, so a reader shown this file has been shown which run is about to be made and nothing about whether it finishes or what it recovers." | The reader has been shown what the run is meant to recover. `ExecutionParams` carries `ex_expected`, "the value the run is meant to recover" (`protocol/pgg_instance.v:299-302`), and `s5_supplied_executable` writes it out as `(fun u => s5_codec (s5_tape_secret u))` at `:75`. The same header contradicts itself eleven lines later: "names the value the run recovers beside it" (`:18`). What is absent at this level is a proof, not the value. | "The proposition is still True, so a reader shown this file has been shown which run is about to be made, and no proof that it terminates or that it recovers the value its parameters name." |
| F5 | MUST | `s5_tableau_analysis_bridged.v:28` | "Nothing else of the instance enters." | False. The two facts the sentence closes are proved from three further instance results: `s5_sample_coalition_viewE` and `s5_supplied_endpoints` in `s5_rand_static_obsE` (`:99-102`), and `profile_k_s5_algebra` in `s5_rand_static_obs_indep` (`:120`). Production makes no such claim; its header (`s5_rows.v:41-46`) says only that the security mathematics reaches the row through the payload and two named facts. | "No other security statement of the instance enters the row." (The only one that does is `s5_exec_coalition_secrecy`.) |
| F6 | MUST | `s5_tableau_executable.v:68` | "the value the run recovers is the tape's secret coordinate carried through the codec" | Asserts at Executable what Observed proves. `ex_expected` is the value the run is *meant* to recover; the reconstruction fact `s5_supplied_recon` is adjoined one level up. The file's own header says the level shows nothing about what the run recovers, so the docstring and the header disagree in the same direction as F4. | "the value the run is meant to recover is the tape's secret coordinate carried through the codec" |
| F7 | SHOULD | `s5_tableau_observed.v:99` and `:139` | "which of the two readings a statement below is made at"; "on the same reading as the dealer-dealt case" | "reading" is this instance's word for what a coalition observes: it is used that way in the new Sampled header (`s5_tableau_sampled.v:8`, "the identification of the two readings of a coalition"), in the new AnalysisBridged header (`:24`), and in the moved `s5_supplied` docstring (`:116`, "a reading of that argument"). Using it here for "spelling of a term" makes one word carry two concepts in one file. The neighbouring moved docstring already has the right word: `s5_supplied_paramsE`, "what keeps the two spellings from parting" (`:132`). | `:99` → "which of the two spellings a statement below is made at". `:139` → "adjoined, in the same sense as the dealer-dealt case". |
| F8 | SHOULD | `s5_tableau_executable.v:6` | "what the run argument is, who commits, what the dealer lays and how much interpreter fuel the run is allowed" | The enumeration covers four of the six fields of `ExecutionParams` (`protocol/pgg_instance.v:281-306`); `ex_content_obs` and `ex_expected` are omitted, and `ex_expected` is precisely the field F4 turns on. A phase header whose job is to say what the level holds should not under-report the record. | "what the run argument is, who commits, what the dealer lays, what a seat observes after a shuffle, what value the run is meant to recover and how much interpreter fuel it is allowed" |
| F9 | SHOULD | `s5_tableau_algebraic.v:44` | "under the empty proposition that level carries" | `StackProp Algebraic = fun _ => True` (`manifest/pgg_tableau.v:555`). "Empty" is the wrong word for `True` and reads, at a glance, like `False`. The header of the same file already uses the right word: "the proposition it carries is True" (`:7`). | "under True, the proposition that level carries" |
| F10 | SHOULD | `s5_tableau_observed.v:24` | "Both are therefore statements of this level and of no level above it" | Ambiguous "Both": the paragraph's nearest plural is "Each run's specification", but the sentence is about the two realisation lemmas, and the middle sentence's subject is "realising one". The clause "and of no level above it" is also loose, since the stack carries every lower level's proposition upward. | "Each realisation lemma is therefore a statement of this level, and neither depends on a probability model." |
| F11 | SHOULD | `s5_tableau_analysis_bridged.v:43` | "coalition's reading is the additive sharing's" | The index entry ends on a genitive with no head noun. Production's reads "is the additive sharing's view" (`s5_rows.v:91`). | "coalition's reading is the additive sharing's own" (the box line must stay at 80 columns) |
| F12 | SHOULD | `s5_tableau_checks.v:17` | "The second is that the coalition size a specification carries is decided by the kernel and not by whoever writes it: five where the sum-mod scheme tolerates four is refused." | A universal read off one refused term. What `Fail Definition s5_F_k5 … := erefl` shows is that `erefl` does not prove `s5_F = MkFunctionality id 5`. The tolerated size is decided by the algebra, through `algebra_functionality` (`s5_tableau_observed.v:158`); the kernel only checks the equation as written. | "The second is that the tolerated coalition size of s5_F is read off the algebra: the equation asserting it is five, where the sum-mod scheme tolerates four, is refused." |
| F13 | SHOULD | `s5_tableau_checks.v:16` | "no evidence stated in one reaches the other" | Too broad as written. The two modes share one algebra, so every fact about `s5_algebra` (`profile_k_s5_algebra`, `s5_profileE`) is stated at one and holds at the other. The claim the types support is about models. Inherited from `s5_rows.v:191`, but repeated here in new text. | "and no statement made at one run's model is a statement about the other's" |
| F14 | SHOULD | `s5_tableau_sampled.v:66` and `s5_tableau_analysis_bridged.v:185` | "Naming the value is what lets a further row over this model be written without repeating the run"; "this equation is what lets a second row over that model be written from the name rather than from the chain" | The same forward-looking justification appears on two declarations in two files, and no second row over `s5_rand_family` exists or is planned at this instance. The wording is carried from `pgl27_word_sampled` (`instances/pgl27/pgl27_rows.v:488`), where it is true: `pgl27_row_word_branch39` (`:493`) is the further row. A justification that names a capability nothing exercises is roadmap, not position. | Keep it on `s5_rand_sampled` only, and state there what the value is for at this instance: "The value is what `s5_row_rand_splitE` continues, so the row and the model are named apart." Drop the clause from `s5_row_rand_splitE`. |
| F15 | SHOULD | across the six files | "view" against "reading"; "sum-mod-5 scheme" against "sum-mod scheme" | Two words per concept inside one directory. "view" survives in the moved docstrings and in the theorem name `s5_rand_view_secrecy`; the new headers say "reading" throughout. Separately, `s5_tableau_algebraic.v:15` writes "the sum-mod-5 scheme" where every other new sentence writes "the sum-mod scheme" (`s5_tableau_observed.v:169`, `s5_tableau_checks.v:19`). | The moved text is frozen by the pure-move rule, so leave "view" where it is and keep "reading" in the new headers, then run one `formal-comment-review` pass over the directory after the copy to settle on one word. Fix "sum-mod-5" to "sum-mod" now; it is new text. |
| F16 | SHOULD | `s5_tableau_checks.v:55` | `Check (s5_supplied sample s5_rand_family : Tableau Sampled).` | The checked term is now, character for character, the body of `s5_rand_sampled` (`s5_tableau_sampled.v:69`), and the checks file imports that module (`:32`). A bare `Check` that restates a definition in scope records no boundary. The prover kept it as the positive half of the pair whose negative is the `Fail` beneath it, which is the right instinct. | Replace with `Check (s5_rand_sampled : Tableau Sampled).` The contrast with `Fail … s5_dealt sample s5_rand_family` survives and reads better, because the two lines then differ in exactly the run. This is a token change, so it falls outside the pure-move rule and needs the orchestrator's word; recommend taking it. |
| F17 | SHOULD | `s5_tableau_observed.v:134` | `s5_supplied_paramsE` placed in Observed | The placement is correct and forced: the statement names `s5_supplied`, an Observed value, so the Executable file cannot state it without changing tokens or inverting the imports. But the design note's table puts an Executable-level parameter equation in the Executable file (`notes/2026-09-20-060000-instance-tableau-directory-design.md`, Candidate A: "the equation that it is the run pgl27_dealt_params names"), and the Executable file as staged states nothing at all about its own two values. | Keep the moved lemma where it is, and add one new Executable-level equation to `s5_tableau_executable.v`: `Lemma s5_supplied_executable_paramsE : projT2 (tableau_at s5_supplied_executable) = s5_supplied_params.` It is a new declaration, not a move, it states the Executable file's own fact, and it makes the phase file carry a statement of its phase rather than only two definitions. Needs a compile. |
| F18 | NOTE | `STATUS.md:93` | "production `_CoqProject:198` at this HEAD" | The line is `_CoqProject:226` at `f7287e3`. `staged/RETIRED.md` has 226 and is right; `STATUS.md` disagrees with it. Both are probe records, so nothing in production is wrong, but the two documents the main session will work from give different numbers. | Correct `STATUS.md` to 226, or drop the number and cite `RETIRED.md`. |
| F19 | NOTE | `fidelity.v:131-134` | `Check (s5_algebraic : Tableau Algebraic).` and the three siblings | The four new `Definition`s are ascribed at their type only, and their assumptions are not printed; only the three `_splitE` lemmas are (`:154-156`). A type ascription would pass on a wrong body. In fact the three conversion lemmas pin all four bodies by conversion, so nothing is actually unchecked, but the file does not say so. | Add `Print Assumptions` for the four new definitions, and one line of comment saying that the `_splitE` lemmas are what pin their bodies. Cheap, and it is the check a reader of `fidelity.v` will look for. |
| F20 | NOTE | `staged/RETIRED.md` | the retirement inventory | Verified independently. A scan of the whole tree outside `notes/` and `.claude/` finds `s5_rows` at exactly: `_CoqProject:226`, `instances/kim2025/five_card_proximity.v:146`, `instances/kim2025/five_card_rows.v:59`, `instances/s5/s5_rows.v:4`, three dated plans under `docs/`, and the generated `.Makefile.rocq.d`. Nothing under `paper/`, `paper-wadt2026/`, `paper-wadt2026-baseline-application/`, `README.md`, `Makefile`, `Makefile.rocq`, `Makefile.rocq.conf`, `scripts/` or `blueprint/`. `.Makefile.rocq.d` is not tracked by git and is regenerated. `s5_rand_exact_witness` is confirmed the only `s5_rows` name `five_card_proximity.v` uses, in code or in comment. | Complete. No addition needed. |
| F21 | NOTE | `instances/kim2025/five_card_rows.v:59-61` | `(* criteria are met at both Kim rows. instances/s5/s5_rows.v records the      *)` `(* other answer for s5_row_word: there the constancy an                       *)` `(* input-indistinguishability certificate asks for is false.                  *)` | The citation must become `instances/s5/tableau/s5_tableau_sampled.v`, as `RETIRED.md` says, because the reasoning is the third paragraph of that header. The replacement path is longer, so the sentence rewraps across the three lines at 80 columns. This edit is only correct once F3 is applied: as staged, the cited paragraph no longer carries the argument for "is false". | Sequence the two: apply F3 first, then repoint `five_card_rows.v:59`. |
| F22 | NOTE | the six files' preambles | the non-uniform `Local Open Scope` blocks | `s5_tableau_analysis_bridged.v` and `s5_tableau_checks.v` open `fdist`, `proba`, `entropy` and `ring`; the lower four open `ring` alone. The prover's reasoning is right for S5: `ring_scope` is innermost in production too, so every numeral and operator in the moved text resolves as it did. The hazard for the larger instances is that a phase file with a shorter scope list could resolve a numeral differently from the file the declaration came from, and no check in `verify.py` looks at that. | See the pattern rulings. |
| F23 | NOTE | `s5_tableau_sampled.v:16` | "the four shares a coalition of four seats holds are four independent uniform values" | True of a five-of-five additive sharing, and inherited from `s5_rows.v:16-18`, but nothing in this directory proves it and the file's job is to say what its phase shows. It is the AnalysisBridged file that carries the corresponding statement, at `:18`. | Acceptable as inherited framing. If a comment pass is run later, attribute it: "…are four independent uniform values, which is what `s5_exec_coalition_secrecy` turns into the exact arm one level up." |
| F24 | NOTE | `s5_tableau_executable.v:22` | "The rules dealt, encoded and supplied each begin at a PGGAlgebraic" | `dealt` and `supplied` do (`manifest/pgg_tableau_syntax.v:294`, `:351`, both `tableau_start A`). `encoded` begins at a `Targeted` (`:334`, `tableau_start (tg_algebra t)`), whose algebra is a field. The substance of the paragraph is right, and the conclusion that the Algebraic-to-Executable edge is the one edge the surface cannot continue from a name is confirmed by the staged text compiling through the raw bind. | "The rules dealt and supplied begin at a PGGAlgebraic and encoded at a Targeted over one, so the keyword surface has no form that continues a named value at Algebraic." |

## Placement, declaration by declaration

All 21 moved items sit in the file of the phase they are about. The three
placements the prover flagged as deviations are each correct, and two of them
are not deviations from the design at all.

**`s5_supplied_paramsE` in Observed.** Correct and forced. Its statement is
`projT1 (projT2 (tableau_at s5_supplied)) = s5_supplied_params`, and
`s5_supplied` is an Observed value, so no Executable-phase file can state it
without changing its tokens. A better placement does not exist for this lemma;
what is missing is an Executable-phase statement of its own, which is F17.

**The functionality material in Observed** (`s5_F`, `s5_FE`,
`s5_F_thresholdE`, `s5_realises_expected`, and the `rand` trio). Correct, and
it is the design's own stated default, not a deviation: open question 6 reads
"the functionality and its equations to the Observed file". It is also right by
the owner's rule. `s5_F` is typed `Functionality (oe_inputT s5_observed)
(oe_outT s5_observed)`, over the observed execution; `realises_expected
s5_observed s5_F` is a statement about that execution and about no probability
model. Both are Observed-phase objects.

**The two link lemmas and the witness in AnalysisBridged.** Correct, and the
framework settles it. The Sampled level's own obligation,
`sampled_viewE_prop` (`manifest/pgg_tableau.v:410-420`), is that the executed
coalition reader is the static one, and `sample_step` discharges it itself from
`sa_coalition_viewE` (`:669-673`); an instance owes nothing there. What
`s5_rand_static_obsE` proves is a different equation, that the framework's
static computation is the additive sharing's own reader, and what
`s5_rand_static_obs_indep` proves is exactly the `ew_indep` field of
`ExactWitness` (`:176-179`). Both are therefore inputs to `certify_exact`
(`:777`), not to `sample_step`. The AnalysisBridged file is where they belong,
and the file's own header says so correctly at `:22-27`.

**The `Fail`s and the bare `Check` in the checks file.** Correct as a class.
The bare `Check` has become redundant against `s5_rand_sampled`; see F16.

## Pattern rulings for the next three instances

Fix these in the template before it is copied to PGL(2,7), five-card and
PSL(2,11).

1. **Apply F1 to F6 to the S5 text first, then copy.** Each of the six is a
   sentence a template propagates. F1, F2 and F3 are about a model the
   manifest publishes and the program does not, and PGL(2,7) and PSL(2,11) both
   have that shape: `pgl27_row_word_tableau` exists but `psl211_word_proximity.v`
   carries three recorded `Fail`s, and five-card has two Sampled values whose
   rows are published from theorems rather than from an arm
   (`five_card_row_repeated_tableau`, `five_card_row_biased_tableau`, both
   `Tableau Sampled`). The rule to carry over: a phase header says what this
   development's programs do, and names separately what the manifest publishes
   by another route. It never says a row does not exist because a program does
   not.

2. **File names, module names and the load path stand.**
   `<inst>_tableau_<phase>.v` with `analysis_bridged` last, under
   `instances/<inst>/tableau/`, no `-R` line. Checked independently: the 204
   logical names reachable from the `-R` directories of `_CoqProject` are
   pairwise distinct, none of the six new base names collides, and the only
   existing modules with `tableau` in the name are `manifest/pgg_tableau.v`,
   `pgg_tableau_syntax.v` and `pgg_tableau_arm_relations.v`, none of which is
   `<inst>_tableau_<phase>`. The 24 names the four instances will produce are
   distinct from each other and from all 204.

3. **Do not add `Require Export`.** The chain as staged is explicit: each phase
   file requires the phases whose names it uses, and `s5_tableau_checks.v`
   naming three of them is the honest cost. Production's only importer,
   `five_card_proximity.v`, takes exactly one name, `s5_rand_exact_witness`,
   which is declared in `s5_tableau_analysis_bridged.v` itself, so a plain
   `Require Import` of that one module suffices and no re-export is needed
   today. For the larger instances the temptation will be stronger, and the
   answer is still no: the design note settled it (Candidate A, "retired, not
   kept as a re-export facade"), the tree uses that idiom only for the four
   `*_analysis.v` files the manifest imports, and an `Export` chain would change
   what a name resolves to in every downstream file without any measurement
   behind it. Record instead, in each instance's `_analysis_bridged.v` header,
   which phase files an importer must name for which kind of name.

4. **Make the scope block's innermost entry the same in all six files of an
   instance, and check it.** The S5 pilot is safe because `ring_scope` is
   innermost in all six and in production, so no numeral moves. Rather than
   forcing the lower files to import `fdist`, `proba` and `entropy` purely to
   open scopes they do not need, add one assertion to the verification script:
   per instance, the last `Local Open Scope` line of every phase file is the
   same. Keep the design's open-question-7 default, reprice constants in the
   AnalysisBridged file, so the numerals that actually depend on `ring_scope`
   stay in the file with the full block.

5. **Every recorded `Fail` is compiled in the preamble of the file it sits in,
   and its message compared.** The pilot found a `Fail` passing for an
   unresolved `erefl` because `ssrfun` was not imported (`STATUS.md`, defect 1).
   That defect is a property of splitting one file's import list across six, so
   it will recur at every instance, and at PSL(2,11) there are six recorded
   `Fail`s across two files. Carry `verify.py`'s per-file `Fail` check to each
   instance unchanged.

6. **Name the phase values by one scheme.** The scheme that fits every existing
   name is `<inst>_<discriminator>_<phase>`, with the discriminator the run mode
   at Executable and Observed, the model at Sampled, and nothing at Algebraic:
   - Algebraic: `<inst>_algebraic` (S5: `s5_algebraic`).
   - Executable: `<inst>_<mode>_executable` (S5: `s5_dealt_executable`,
     `s5_supplied_executable`; PGL(2,7): `pgl27_dealt_executable`; five-card:
     `five_card_committed_executable`; PSL(2,11):
     `psl211_alldecks_executable`).
   - Observed: `<inst>_<mode>`, the phase word elided. This is established and
     every existing name keeps it: `s5_dealt`, `s5_supplied`, `pgl27_dealt`,
     `five_card_committed`, `psl211_alldecks_prefix`.
   - Sampled: `<inst>_<model>_sampled`. Established by `pgl27_word_sampled`
     (`instances/pgl27/pgl27_rows.v:485`) and followed by `s5_rand_sampled`.
   - Published row: `<inst>_row_<model>_tableau`, established by
     `s5_row_rand_tableau`, `pgl27_row_exact_tableau`,
     `pgl27_row_word_tableau`, `psl211_row_alldecks_tableau`.

   Two warnings the orchestrator should settle before the copy.

   First, `<inst>_algebraic` is one letter from `<inst>_algebra` at every
   instance, and both names appear in the same file, since the definition is
   `Definition s5_algebraic := tableau_start s5_algebra`. This is a real
   readability hazard and the scheme would copy it four times. The alternative
   that keeps every existing name and removes the homograph is `<inst>_start`,
   after the framework statement that builds it, `tableau_start`
   (`manifest/pgg_tableau.v:607`): `s5_start`, `pgl27_start`,
   `five_card_start`, `psl211_start`. It gives up the mirror with the
   `CompletionLevel` constructor, which the Observed names have already given
   up, and the phase is still carried by the file name, which is what the owner
   asked for. Recommend `<inst>_start`. If the mirror is preferred, keep
   `<inst>_algebraic` and accept the hazard knowingly; there is no third
   option that keeps both.

   Second, the tree already spells Sampled two ways: `pgl27_word_sampled` uses
   the phase word, while `five_card_row_repeated_tableau` and
   `five_card_row_biased_tableau` (`instances/kim2025/five_card_rows.v:463`,
   `:475`) are `Tableau Sampled` values wearing the published-row suffix. Those
   two names are existing and stay. The scheme above applies to values the
   phase files introduce, and the five-card `_sampled` file should say in its
   header that the two `_tableau`-suffixed values it holds are Sampled values
   named before the scheme.

7. **Conversion-lemma suffix: reconsider `_splitE`.** The tree has no suffix for
   "this named lower-phase value, continued, is that existing value". The two
   candidates are near misses. `five_card_row_repeated_prefixE` and
   `five_card_row_biased_prefixE` (`five_card_rows.v:492`, `:502`) are
   `_prefixE`, but they state a conjunction of three projection equalities, a
   strictly weaker claim than the whole-term equality the S5 lemmas state;
   reusing the suffix would make one name mean two strengths.
   `pgl27_row_word39_bindE` (`pgl27_rows.v:445`) is a whole-term equality, but
   between the keyword surface and the raw bind, a different axis entirely.
   `_splitE` therefore does not collide, but "split" names the edit that
   produced the lemma rather than the relation it states, which is the kind of
   word the project keeps out of permanent text. The tree's own convention
   names such an equation after its non-canonical side:
   `pgl27_inline_paramsE`, `pgl27_row_word39_bindE`, `s5_supplied_paramsE`.
   Following it gives `s5_dealt_executableE`, `s5_supplied_executableE` and
   `s5_row_rand_sampledE`, each reading "the equation at that named value".
   Recommend those three. If the orchestrator keeps `_splitE`, it must be fixed
   before the copy, because the three larger instances will add roughly a dozen
   more of these.

8. **Add one Executable-phase statement per instance** (F17). As staged, the
   Executable file is the only phase file that states nothing about its own
   phase, which makes it read as a waypoint rather than a phase. One parameter
   equation per named Executable value fixes that and costs one `exact: erefl`.

9. **Keep the pilot's two structural habits.** Every new equation closes by
   `exact: erefl` and never `by []`, and the chain is rebuilt in phase order
   after any edit. Both are recorded in `STATUS.md` with the measurement behind
   them, and both will matter more at PSL(2,11), where the forward closure of
   `psl211_endpoints.v` must not be disturbed.
