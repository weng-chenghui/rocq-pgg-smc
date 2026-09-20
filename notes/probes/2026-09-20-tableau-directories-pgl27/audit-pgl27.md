# Audit of the PGL(2,7) `tableau/` instance

Read-only adversarial audit of the staged PGL(2,7) instance at commit
`d3a1957`, against `notes/probes/2026-09-20-tableau-directories-s5/staged/TEMPLATE.md`
with its two addenda, `audit-s5-pilot.md`, `audit-psl211.md` (F1 to F18 and the
twelve rulings), `notes/2026-09-20-060000-instance-tableau-directory-design.md`,
and production's `instances/s5/tableau/` and `instances/psl211/tableau/`.
Frozen export read at
`/private/tmp/.../scratchpad/dirs_pgl_frozen/notes/probes/2026-09-20-tableau-directories-pgl27/`.
Nothing was compiled and no repository file other than this one was written.
The mechanics already established by `verify.py`, `gen_fidelity.py` and the
compile log were not redone.

## Verdict

**Structure GO. NO-GO on the new text and on `RETIRED.md`.**

- **GO** on placement. All 75 production declarations plus the nine new ones
  are in the right file. The four contested placements the remit names are
  each right on the stated rule, and the reasons in `STATUS.md`'s table are
  the reasons that hold. See "Placement".
- **GO** on the import graph, the module names and the `_CoqProject` edit.
  No cycle, every phase import earned, the two drops correct, and the
  seven-line block matches the file as it stands today at lines 223 to 225 and
  233.
- **GO** on `gen_fidelity.py`'s approach, with one residual risk named and
  shown empty at this instance. See F16.
- **NO-GO** until F1 to F9 are fixed. Two of them are outright false sentences
  of new text (F1, F2), one is a false count (F3), one is a generator artefact
  left in a shipped file (F4), one is a missing entry in `RETIRED.md` that
  leaves a dangling citation in a tracked `.v` file after the `git rm` (F5),
  and four are sentences that misstate what a declaration says (F6 to F9).
- The 950-line AnalysisBridged file: keep one file, do **not** take Candidate
  B. Reasons and the one cheap fix in "The AnalysisBridged file as a text".

## Findings

| id | class | file:line | quoted text or object | problem with evidence | replacement or recommendation |
|---|---|---|---|---|---|
| F1 | MUST | `staged/instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:52-54` | "the executable file the Executable value, the parameter equation and the two identifications of a coalition's reading" | False, and contradicted by a sibling header in the same directory. `pgl27_static_obsE` and `pgl27_static_obs_funE` are in `staged/instances/pgl27/pgl27_proximity.v:97` and `:111`. The Executable header itself says so at `pgl27_tableau_executable.v:23-27`, and the orchestrator's ruling put them there so the mathematics requires no tableau module. A grep of the staged tree for `static_obs` finds the two lemmas only in the reduced file. The same header's last paragraph (`:61-65`) lists what `pgl27_proximity.v` holds and omits them, so the file is wrong twice about the same two lemmas. | Line 53: "the executable file the Executable value and the parameter equation;". Then extend `:61-65` to: "This file requires `instances/pgl27/pgl27_proximity.v`, which holds the reading and the distance mathematics the certificates are built from: the two identifications of the framework's static reading of a coalition with `pgl27_view`, the dealt secret on the word sample space, the distance between the two models' joint laws, and the two arithmetic facts about 2^-40 the conclude obligation is proved with." |
| F2 | MUST | `staged/instances/pgl27/tableau/pgl27_tableau_observed.v:42` | `pgl27_realises_expected == the run recovers the functionality's value` | `realises_expected oe F := OE.oe_expected oe = fn_f F` (`protocol/pgg_functionality.v:144-146`). It is an equation between the value the execution names as the one to recover and the functionality's function. Recovery is the third conjunct of `oe_correct_prop` (`manifest/pgg_tableau.v:380`), a different fact that `pgl27_dealt` carries. PSL(2,11) ruling 1 bars this phrasing, the pre-audit applied it to the body sentence at `:27-28`, and the index entry was left behind. The declaration's own docstring at `:144` already states it correctly. | `(*   pgl27_realises_expected == the value the run is meant to recover is     *)` / `(*                              that functionality's function                *)` |
| F3 | MUST | `staged/instances/pgl27/tableau/pgl27_tableau_algebraic.v:57-58` | "The three probability models the instance analyses part two levels above" | `CompletionLevel` is `Algebraic \| Executable \| Observed \| Sampled \| AnalysisBridged` (`manifest/pgg_analysis_status.v:60-61`). A model is adjoined by the sample step, which reaches Sampled, three levels above Algebraic. The directory's own file order gives the same count. | "The three probability models the instance analyses part three levels above" |
| F4 | MUST | `staged/instances/pgl27/tableau/pgl27_tableau_sampled.v:81` | `(* payload                                                                    *)` | A stray line between the section banner and the docstring. Production's banner at `instances/pgl27/pgl27_rows.v:477-480` runs to two lines. The generator re-indented the first line to the five-space form, kept production's second line inside the box at `:78`, and emitted it a second time outside the box at `:81`. No production tableau file of S5 or PSL(2,11) has a banner longer than one line, so this shape is new here and unguarded. Also, the banner's tail "under an input-indistinguishability payload" is not true of the declaration under it: `pgl27_word_sampled : Tableau Sampled` carries no payload, the payload arrives at the certify statement one level above. | Delete `:81`. Re-wrap the banner to one line that is true of the value: `(*     The word model as a branch point                                      *)`. Add to `verify.py`: a section banner is exactly one content line. |
| F5 | MUST | `staged/RETIRED.md`, table "References that must change, in a comment, DEFERRED" | the table lists `instances/pgl27/pgl27_encoding_r5.v:14` and `manifest/pgg_analysis_manifest.v:723` and `:730` only | A fourth tracked `.v` file cites the retired file. `instances/psl211/psl211_reading_constancy.v:55` reads "PGL(2,7) proves the same field through pgl27_word_view_const of / instances/pgl27/pgl27_rows.v, three-transitivity read as constancy for / coalitions of fewer than four seats." The line is present at `154c742` (as `:53`) and at HEAD (as `:55`), so the scan `RETIRED.md` records missed it. It is neither a note nor a plan, so the "References in notes and plans, which are not edited" paragraph does not cover it. After the `git rm` the citation points at nothing. | Add the row. `pgl27_word_view_const` lands in `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:266`, so the comment becomes that path. Nothing in the tracked tree `Require`s `psl211_reading_constancy`, so its reverse closure is empty and the repoint costs one module. Apply it with this instance rather than deferring it, and say in `RETIRED.md` why this one is not deferred while the other two are. |
| F6 | MUST | `staged/instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:43-48` | "The other four write the same claims again: the word row concluded at 2^-39 in three spellings … and the proximity row, which publishes the manifest's word row a second time" | The proximity row does not write the same claim. `pgl27_row_word_proximity_armE` (`:892`) gives it `IdealProximityArm` and `pgl27_row_word_armE` (`:401`) gives the word row `InputIndistinguishabilityArm`, and `pgl27_row_word_arm_neq` (`pgl27_tableau_checks.v:111`) proves the two differ, its own docstring saying "the pair is two statements about one probability model and not one statement published twice". The header of the AnalysisBridged file therefore asserts what the checks file refutes. | "The other four are the word row concluded at 2^-39 in three spellings, through the surface, through the raw bind and from the named Sampled value, and the proximity row, which publishes the same manifest row under a different arm. An `AnalysisPathRow` holds descriptive metadata and no `Prop`, so one manifest row carrying an input-indistinguishability row and a proximity row says nothing about either claim." |
| F7 | MUST | `staged/instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:26-28` | "The input-indistinguishability certificate spends it once for each of the two dealt secrets it compares" | "spends" is a narrative word for a relation, in new text. The relation is the transfer inequality crossing from the walk to the ideal cut and back, which the moved docstring at `:337-340` states in those terms. | "The input-indistinguishability certificate crosses from the walk to the ideal cut once for each of the two dealt secrets it compares, so its `cert_eps` is that number added to itself, 2^-39." |
| F8 | MUST | `staged/instances/pgl27/pgl27_proximity.v:19-20` | "The bound is an upper bound on a sum of absolute differences and not the distance itself." | Two sentences apart the same quantity is called two things. `:16-18` calls `var_dist(rho_word, uniform)` "the distance between the walk and the uniform cut on the group", and this sentence then says the quantity bounded is "a sum of absolute differences and not the distance itself". A reader cannot tell whether a second quantity has been introduced or whether the point is that 2^-40 is a bound and not a value. The sibling reduced file in production, `instances/psl211/psl211_word_proximity.v:16-18`, states the convention once and unambiguously, and the two siblings are meant to read alike. | Adopt the sibling's sentence: "Every number below bounds a sum of absolute differences, which is twice the total variation distance of the literature, so a bound of 2^-40 here is a distinguishing advantage of at most 2^-41 wherever it is used." |
| F9 | MUST | `staged/instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:105` | `pgl27_word_view_const == two secrets give one reading of the ideal cut` | The entry reads as unconditional and the lemma is not. `pgl27_word_view_const` (`:266-273`) has the premise `(#|C| < profile_k (instance_profile pgl27_algebra))%N`, which is the four-seat threshold. The reduced file's index keeps the threshold on the analogous entry (`pgl27_proximity.v:50-53`, "below the four-seat threshold, the two models' joint laws …"), so the two indexes of this landing apply the rule differently. | `(*   pgl27_word_view_const  == below the four-seat threshold, two secrets    *)` / `(*                              give one reading of the ideal cut            *)` |
| F10 | SHOULD | `staged/instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:39-43` | "Seven rows are published. Three of them are the manifest's own: pgl27_row_exact_rowE, pgl27_row_word_rowE and pgl27_row_prior_exact_rowE discharge …" | "Three of them" ranges over published rows, which are programs, and the three names that follow the colon are lemmas. The counts themselves are right: seven `PublishedRow` and `PublishedRowAt` programs in the file, and exactly three `AnalysisPathRow`s over this instance in the manifest, at `manifest/pgg_analysis_manifest.v:962`, `:973` and `:1085`. Only the apposition is type-dishonest. | "Seven rows are published, and three of them publish the manifest's own. `pgl27_row_exact_rowE`, `pgl27_row_word_rowE` and `pgl27_row_prior_exact_rowE` discharge `pgl27_row_exact`, `pgl27_row_word` and `pgl27_row_prior_exact` of `pgg_analysis_manifest.v` by conversion, and those three are the `AnalysisPathRow`s the manifest carries for this instance." |
| F11 | SHOULD | `staged/instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:97`, `:106`, `:129` | `pgl27_row_word_proximity== the word row as a program …`, `pgl27_row_exact_sampledE== …`, `pgl27_exact_view_secrecy== …` | The name touches `==` with no space. Across every production tableau file of S5 and PSL(2,11) and across production `pgl27_rows.v` and `pgl27_proximity.v`, a scan for `^\(\*\s{3}\S+==` returns zero hits: the house rule is to break the entry when the name fills the column. The file already breaks the longer names this way (`:84`, `:90`, `:117`). | Break the three entries, name on its own line and `== ` starting the next, exactly as `:84-86` does. |
| F12 | SHOULD | `staged/instances/pgl27/tableau/pgl27_tableau_observed.v:32` against `:71-75` | index "the prefix all seven rows share" over a moved docstring reading "the two rows part at the next line" and "common to both" | The two counts sit within forty lines of each other. The docstring is production's and was already loose there, since `pgl27_rows.v` held five rows when it was written. Token fidelity is why it survived, but a reader of the new file meets the contradiction on one screen. | Either add a fourth intended docstring difference, "the two rows" becoming "the rows over the three models" and "both" becoming "all of them", or record in `STATUS.md` that the count is production's and pre-dates the proximity and prior-indexed rows. Do not leave it unrecorded. |
| F13 | SHOULD | `staged/instances/pgl27/pgl27_proximity.v:4-5` | "pgl27_proximity: the reading and the distances the eight-card orbit instance's proximity certificate is built from" | Two of the file's seven declarations are not what the proximity certificate is built from. `pgl27_static_obs_funE` is consumed by `pgl27_word_view_const` (`pgl27_tableau_analysis_bridged.v:276`) and `pgl27_word_bridge` (`:529`), both input-indistinguishability material, and `pgl27_word_uniform_ideal_close_false` refutes a certificate field rather than feeding one. The module name `pgl27_proximity` is still adequate, since the file's largest object is the proximity distance, but the title over-narrows the content. | "pgl27_proximity: the instance's reading of a coalition, and the distances between its two laws of the cut" |
| F14 | SHOULD | `staged/instances/pgl27/tableau/pgl27_tableau_sampled.v:20-25` | "The index types are what separate the unit-indexed exact family from the other two, and they separate two families and not two models" | Three different pairs are named in one sentence: the exact family against the other two, then "two families", then "two models". The content is right, the ruling about families and models is honoured, and only the reference is hard to follow. | "The exact family's index is the unit type and the other two carry a law of the secret, so an index type tells the exact family from the prior-indexed exact family. That is a difference of families and not of models: both draw the uniform cut, and they differ in whether the law of the secret is fixed at the uniform one or carried as an index." |
| F15 | SHOULD | `staged/instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v`, 950 lines, 15 section banners | the owner's rule, one claim with its whole chain per row | Two of the seven published rows share one banner, "The two row programs" (`:302-304`), which holds `pgl27_row_exact_tableau`, `pgl27_row_word_tableau` and their four `_rowE` and `_armE` lemmas interleaved. The exact row's chain then runs across five banners: witness at `:201`, program at `:302`, statement and bridge at `:560`, four conjuncts at `:619`, restatement pair at `:647`. The declaration order is production's, so regrouping would move declarations and cost the as-built fidelity the landing rests on. | Keep one file. Add a locator table to the header, seven lines, one per published row, naming the banner that holds it and its `_sampledE`, `_rowE`, `_armE` and reading statement. It is comment-only, it moves no declaration, and it answers the question Candidate B was raised to answer. Full reasoning below. |
| F16 | SHOULD | `gen_fidelity.py:68-72` and the generated `fidelity.v` and `baseline.v` | `Check @<name>` for all 64 declarations, no `Set Printing All` | A byte-identical print is a sound pin of a **statement** and not of a **body**. `Check @f` makes implicit arguments explicit in the printed type, which closes the implicit-argument half. The notation half is closed in practice here, because neither source holds a `Local Notation` (`verify.py` asserts this, and `STATUS.md` records it) and no staged file declares one, so the two sides print through the same notation set under the same scope block. What remains open is a `Definition` whose type hides its data, for example `pgl27_reprice39 : Reprice`, where a re-elaborated body would print nothing. That risk is empty at this instance and can be shown so: the only declarations whose scope changes are the 21 that leave `pgl27_proximity.v`, of which four are `Definition`s (`pgl27_prior_exact_witness`, `pgl27_row_prior_exact_tableau`, `pgl27_word_proximity_cert`, `pgl27_row_word_proximity`), and none of the four holds a numeric literal in its body. Every re-scoped numeral appears inside the printed statement of `pgl27_word_proximity_cert_epsE`, `pgl27_word_proximity_le39`, `pgl27_word_proximity_cert_eps_lt2` or `pgl27_word_view_proximity`, each closed by conversion. The token identity of the sources then closes the rest. | Write that argument into `STATUS.md` in three sentences, so the soundness is on the page and not in an auditor's head. This is PSL(2,11) ruling 9 applied to the moved declarations rather than to the new ones. For five-card, where the re-scoped set may contain a `Definition` with a literal, add `Print <name>.` for the small `Definition`s to both files. |
| F17 | NOTE | moved docstrings and one moved proof comment | "spends no mixing bound" (`analysis_bridged:265`), "The two currencies are visible in the fields" (`:288`), "each crossing spends the same mixing bound once" (`:340`), "the … arm spends it once" (`:813`), "The number is spent once" (`:866`), "Three costs …", "costs 78.7 s", "costs 24.3 s", "costs 24.1 s" (`checks:115-121`) | Narrative words for relations, and three timings, all in text that is production's and word-identical. Listed once as the remit directs. Out of scope for this landing. | No change now. When the comment pass over the instance files is run, these are the lines to take. |
| F18 | NOTE | `staged/instances/pgl27/tableau/pgl27_tableau_observed.v:14` against `:19-20` | "One run reaches this level and two values name it" against "a prefix that builds its own obligation reaches a second observed execution" | Consistent only if "run" means the run parameter record, which is what `pgl27_inline_paramsE` (`:117`) proves the two share, while the observed executions differ. The reader has to supply that. | Optional: "One run parameter record reaches this level and two values name it." |
| F19 | NOTE | `staged/instances/pgl27/tableau/pgl27_tableau_algebraic.v:54-56` | "One run mode is built on this value, the dealer-dealt one, and pgl27_dealt_executableE is where the prefix all seven published rows continue from is identified with it" | "it" can be read as this value or as the dealer-dealt mode. The equation at `pgl27_tableau_observed.v:88` has `pgl27_dealt_executable` on its left, so only the second reading is right. | "… is identified with that mode." |

## Placement

`STATUS.md`'s table was read in full and every row checked against the
declaration. The four contested rows and the sample of the rest:

**`pgl27_static_obsE` and `pgl27_static_obs_funE` in the reduced mathematics
file: right.** Their statements name `pgl27_algebra`, `pgl27_dealt_params` and
`pgl27_view` and no `Tableau` value, no run fact and no model, so they are
mathematics about the run parameter record. `pgl27_word_proximity_close`'s
proof rewrites with `pgl27_static_obsE` at `pgl27_proximity.v:178` and `:188`,
so the distance and the identification it uses are in one file. The four
consumers above are in the AnalysisBridged file, which requires the reduced
one, so every arrow runs upward. `pgl27_static_obs_funE` has no consumer inside
the reduced file, which is allowed by the rule as stated, since its subject is
the same parameter record. One thing in the staged tree does cite them as
living elsewhere, and that is F1.

**`Lemma pgl27_row_word_arm_neq` in the checks file below its recorded
namesake: right, and the header sentence is true and free of history.**
`pgl27_tableau_checks.v:40-43` states the fact and the reason, with no "moved",
"formerly" or "now". The measurement behind it is in `STATUS.md` under "The
name that is written twice", and the consequence is visible in the verification:
all eleven rejections are byte-identical across the two sides, so the recorded
message is still the one about the arm and not one about an occupied name.

**`pgl27_prior_viewE` at AnalysisBridged: right.** Its one consumer is
`pgl27_prior_exact_witness` (`:716`), and a grep of the staged tree finds no
other. More to the point, its statement names `amf_sample
pgl27_prior_exact_family R secretP`, a model. The rule that keeps
`pgl27_static_obsE` in the mathematics file is that no model appears in it, and
that rule sends this one up.

**`pgl27_reprice39`, `pgl27_reprice41` and `pgl27_word_proximity_le39` at
AnalysisBridged: right.** `Reprice = forall R : realType, option R`
(`manifest/pgg_tableau.v`), a certificate value, and the two lemmas that use
the constants name a certificate: `pgl27_word_reprice41_false` names
`cert_eps (pgl27_word_cert …)` and `pgl27_word_proximity_le39` names
`ipc_eps (pgl27_word_proximity_cert …)`. Neither could be stated in the reduced
file, which holds no certificate.

**Bridges, restated theorems, functionality, and the rest.** `pgl27_word_bridge`
and `pgl27_exact_bridge` quantify over `StackAt AnalysisBridged` and mention
`StackProp`, so they cannot be lower. `pgl27_F` is typed at
`Functionality (oe_inputT pgl27_observed) (oe_outT pgl27_observed)` and
`pgl27_FE` and `pgl27_realises_expected` are about it, so Observed is forced,
which answers design question 6. The seven declarations that stay in the
reduced file are two readings, one random variable on a sample space, one
distance, two arithmetic facts and one refuted distance bound, and none of them
names a `Tableau` value, a certificate or a row, so the rule "lemmas about
laws, readings and distances are mathematics" places all seven.

**One place where the two halves of the rule disagree, for the record.**
`pgl27_word_target` and `pgl27_exact_target` are plain `Prop`s over `var_dist`
and `fdistmap` with no tableau object in them, so the subject test would put
them in the mathematics file, while the consumer test puts them beside the
`restate` terminal that takes them. The landing follows the consumer test,
which keeps each restate chain contiguous and is the right call. It is worth a
ruling so that five-card does not re-litigate it.

## The import graph and `_CoqProject`

No cycle. The reduced `pgl27_proximity.v` requires no tableau module, the
AnalysisBridged and checks files require it, and inside the directory the
arrows are algebraic to executable to observed to sampled to analysis_bridged
to checks, with analysis_bridged also requiring observed and checks also
requiring observed. No `Require Export`.

Every phase import is earned, checked by name set and not by the table alone:
executable uses `pgl27_algebraic_start` (`:71`); observed uses
`pgl27_dealt_executable` (`:89`); sampled uses `pgl27_dealt` (`:73`, `:86`,
`:98`); analysis_bridged uses `pgl27_dealt` and the three named Sampled values
(`:327`, `:357`, `:735`); checks uses `pgl27_dealt` and `pgl27_inline_dealt`
from observed, four AnalysisBridged names, and `pgl27_word_secret` and
`pgl27_word_proximity_close` from the reduced file. The two drops are right:
no Executable name occurs in the AnalysisBridged file, and no Sampled name
occurs in the checks file, where `pgl27_exact_family` and `pgl27_word_family`
come from `pgl27_models` and not from the phase file.

Module names follow the existing twelve. Under the recursive
`-R instances/pgl27 pgg_smc` the six files are `pgg_smc.tableau.pgl27_tableau_*`,
which shares the `tableau` component with S5's and PSL(2,11)'s six each and
clashes with neither, the instance prefix being part of the base name.

The `_CoqProject` block in `STATUS.md` still matches the file as it stands
today: line 223 is `manifest/pgg_tableau_arm_relations.v`, 224 is
`instances/pgl27/pgl27_rows.v`, 225 is `instances/kim2025/five_card_rows.v`
and 233 is `instances/pgl27/pgl27_proximity.v`. The reduced file's new position
at 224 is safe: every module it requires is at or below line 203
(`instances/pgl27/pgl27_models.v`), with `lib/var_dist_supp.v` at 35,
`protocol/pgg_instance.v` at 48, `security/pgg_collusion_bound.v` at 87,
`security/pgg_weighted_words.v` at 99 and `security/pgg_sample_adapter.v` at
110. Nothing between the old position and the new one requires it. The advice
in `STATUS.md` to re-derive both numbers by name at the time of the `cp`
still stands and should be followed even though they have not moved.

## The AnalysisBridged file as a text

950 lines against PSL(2,11)'s 418 and S5's 231, and seven published rows
against PSL(2,11)'s and S5's smaller sets. Fifteen section banners. A reader
can find each row's program, but not each row's chain: F15 records the two
rows that share a banner and the exact row's chain spread over five.

**Recommendation: keep one file. Do not take Candidate B at this instance.**

Reasons, in the order they weigh.

1. The pattern's promise is that the directory listing is the phase list, and
   the design note records that as the owner's objection to the nested
   structure (`notes/2026-09-20-060000-instance-tableau-directory-design.md:337-344`
   and `:388-393`). Two instances are in production with six files each. A
   third instance with a nested `analysis_bridged/` directory breaks the
   promise for the one instance that most needs a reader to recognise the
   shape.
2. The split would not be four files, as the design note's sketch has it, but
   four plus a shared-payload file. `pgl27_word_cert` is consumed by four of
   the seven rows, `pgl27_reprice39` by three, and `pgl27_dealt` by all seven.
   The sketch's `pgl27_bridged_word.v` would hold the certificate, and then
   `pgl27_bridged_word_proximity.v` would require it, which reintroduces
   exactly the cross-file arrow the split was meant to remove.
3. The cost the design note names is real here. Each row file re-imports the
   same instance mathematics, and this instance's import block is the heavy
   one: the measured import sentence in the AnalysisBridged file is 2.29 s of
   a 7.1 s compile, so four or five row files add roughly seven to nine
   seconds of import per build for a file that compiles in seven.
4. Everything that verification currently states per file would have to be
   restated. `verify.py`'s scope rule reads "innermost scope, all six phase
   files", `gen_phase_files.py` emits seven files, the `_CoqProject` block is
   seven lines, and `RETIRED.md`'s reverse-closure count of 22 after the move
   assumes six. None of that is hard, and all of it is work that buys a reader
   nothing the locator table does not buy.

**The cheap fix instead.** Add to the header, after the "Seven rows are
published" paragraph, a seven-line locator: one line per published row naming
the banner that holds it and the names of its `_sampledE`, `_rowE`, `_armE` and
its reading statement where each exists. It is comment-only, it moves no
declaration, it keeps the as-built fidelity the landing rests on, and it is the
one thing a reader of a 950-line file actually needs. If the file grows again
at five-card, revisit Candidate B there with this instance's numbers in hand.

## Rulings to carry to five-card

1. **A directory's headers must agree about where a declaration lives.** F1.
   When the orchestrator moves a declaration out of the phase files, grep the
   whole staged tree for its name and for every paraphrase of it before the
   audit, not only the file it left. Here two headers of one directory
   disagreed about the same two lemmas, and the wrong one was the file that
   does not hold them.
2. **A ruling applied to a header's prose must be applied to its index.** F2.
   PSL(2,11) ruling 1 was applied to the Observed body sentence and not to the
   index entry eight lines below it. Before the audit, re-read the index of
   every header the pre-audit touched and check each entry against the
   declaration's actual statement, not against the body sentence.
3. **A hypothesis survives into the index entry.** F9. If a lemma has a
   coalition premise, the entry says so, in the same words the sibling file
   uses. At this instance one index kept the four-seat threshold and the other
   dropped it on the analogous lemma.
4. **Count the levels, do not say "above".** F3. `CompletionLevel` has five
   constructors and the distance between two of them is a number a reader can
   check. State it or leave it out.
5. **A section banner is one content line.** F4. Production's rows files have
   banners of two lines. The generator re-wraps the first and leaves the
   second, and at this instance it also emitted the second a second time
   outside the box. Add the one-line assertion to `verify.py` and re-wrap any
   production banner that will not fit at the new indent, rather than carrying
   its second line over.
6. **`RETIRED.md`'s scan covers every tracked file, and a cross-instance file
   is the one it misses.** F5. Here a PSL(2,11) file cited the PGL(2,7) rows
   file in prose. Run the scan over the whole tracked tree excluding only
   `notes/` and `.claude/`, and list every hit even when the plan is not to
   edit it, with the reason.
7. **Publishing one manifest row twice is not publishing one claim twice.**
   F6. When two rows discharge the same `AnalysisPathRow` under different arms,
   say "under a different arm" and let the `AnalysisPathRow`-holds-no-`Prop`
   sentence do the rest. The checks file's arm-inequality lemma is the
   statement that would otherwise contradict the header.
8. **A sum of absolute differences gets one sentence, in the sibling's
   words.** F8. `instances/psl211/psl211_word_proximity.v:16-18` is the
   sentence. Copy it and change the numbers. Two reduced mathematics files
   that state the same convention differently are two conventions to a reader.
9. **Break the index entry when the name fills the column.** F11. No
   production file in this tree lets a name touch `==`.
10. **A `Definition`'s body is pinned by an equation, never by `Check`.** F16.
    The fidelity pin is sound for statements. Before declaring it sound for
    bodies, list the `Definition`s whose scope changes, check whether any holds
    a literal, and write the argument down. At five-card, if one does, add
    `Print` for it.
11. **Decide once whether a restate target is placed by its subject or by its
    consumer.** `pgl27_word_target` and `pgl27_exact_target` mention no tableau
    object and are placed with the terminal that takes them. That is right, and
    it is the one place the two halves of the placement rule point different
    ways, so five-card should cite this ruling rather than argue it again.
12. **A 950-line AnalysisBridged file gets a locator table, not a directory.**
    F15. Candidate B remains available and remains unused. Revisit it only with
    a measured import cost and a shared-payload plan, and never as a reflex to
    a line count.
