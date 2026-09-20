# Audit of the five-card `tableau/` directory (read-only)

Audited at `6cbc3a8` on `feat/tableau-extensions-probe`, against the frozen
export of `notes/probes/2026-09-20-tableau-directories-five-card/`. Standard:
`notes/probes/2026-09-20-tableau-directories-s5/staged/TEMPLATE.md` with its
three addenda, and the audits `audit-s5-pilot.md`, `audit-psl211.md`,
`audit-pgl27.md`. Worked examples: `instances/s5/tableau/`,
`instances/psl211/tableau/`, `instances/pgl27/tableau/`,
`instances/pgl27/pgl27_proximity.v`, `instances/psl211/psl211_word_proximity.v`.

Nothing was compiled and `make` was never run. The mechanical results the
prover reports (93 of 93 token-identical, 83 of 89 docstrings word-identical,
the empty `baseline`/`fidelity` diff, the 11 recorded rejections) were taken
as given and not redone.

## Verdict

**Structure, placement, the import graph, the `_CoqProject` edit, `RETIRED.md`
and the one comment repoint: GO.** Six placement questions were re-derived
from the framework and the manifest and all six come out the way the prover
placed them. The import graph is acyclic, every phase import is earned, and
the repoint's new citation is true.

**The new text: NO-GO on six MUST items.** Three of the six are the shapes the
template already rules on and that recurred at every earlier instance: a
header saying the manifest reaches a level only by routes this development's
programs take (F3, template F1/F2), a positive "recovers" below Observed (F2,
PSL(2,11) ruling 1), and two headers of one directory describing one equation
two different ways (F1, PGL(2,7) ruling 1). Two more are counting errors in
sentences the move itself introduced (F4, F6). One is a type-dishonest index
gloss (F5).

None of the six touches a declaration, a statement or a proof. All are one- to
three-sentence repairs inside header or docstring text, so a fix pass plus a
re-run of `verify.py` (which must still report 93 of 93) is enough; nothing has
to be re-staged or re-compiled beyond the two files whose headers change.

## Findings

| id | class | file:line | quoted text or object | problem with evidence | replacement or recommendation |
|---|---|---|---|---|---|
| F1 | MUST | `staged/.../tableau/five_card_tableau_algebraic.v:68` | "five_card_committed_executableE is where the prefix all seven published rows continue from is identified with it" | The equation is `(five_card_committed_executable execute terminates by … recon by …) = five_card_committed` (observed file, 105-110). Its left side is the **Executable** value extended by the three run facts; `five_card_algebraic_start`, the "it" of the sentence, does not occur in the statement at all. The Observed index (37-39) describes the same lemma correctly as "the prefix is its Executable value with the three run facts adjoined", so the two headers of one directory describe one equation two ways (PGL(2,7) ruling 1). | "The Executable file continues this value into five_card_committed_executable, and five_card_committed_executableE identifies that value, with the three run facts adjoined, with the prefix all seven published rows continue from." |
| F2 | MUST | `.../five_card_tableau_executable.v:22` | "which is what keeps the function a row names and the value its run recovers one term" | PSL(2,11) ruling 1: below Observed the phrase is "the value the run is meant to recover", never "recovers"; the reconstruction fact arrives at Observed and this file's own second sentence says the reader has been shown "no proof that it terminates or that it recovers the value its parameters name". The positive use two sentences later takes it back. | "…which is what keeps the function a row names and the value its run is meant to recover one term." |
| F3 | MUST | `.../five_card_tableau_analysis_bridged.v:67-68` | "The manifest publishes none of the three by a route this development's programs do not take." | False for `five_card_row_biased`. `manifest/pgg_analysis_manifest.v`'s docstring for that row names two things reaching AnalysisBridged: `colour_view_leak_bound`, which "bounds a conditional mutual information over that same biased distribution", and the transfer concluding `biased_static_obs_indistinguishability`. Only the second is a payload any program carries; the Sampled header of this same directory (43-44) states that "no arm of certify takes a conditional mutual information as a payload", and `five_card_row_biased_tableau`'s own moved docstring says the manifest's level "rests on that theorem and on the certificate". The uniform row is the same shape: the manifest's route is `exec_trace_secrecy` at `content_trace R ord0`, while the program's statement is `five_card_exact_view_secrecy`, proved by `view_secrecy_of` on the published row. This is the template's F1/F2 failure with the polarity reversed. | Replace with the positive form the template asks for: "Of the three, the repeated row's AnalysisBridged level is the one a program of this file reaches by the same theorem the manifest names. The manifest reaches that level for the one-cut row by two theorems, one of them five_card_colour_view_leak_bound, a conditional mutual information no arm of certify takes; the programs here reach it by the certificate alone. For the uniform row the manifest names exec_trace_secrecy at the row's content trace, and the program's statement is five_card_exact_view_secrecy." |
| F4 | MUST | `.../five_card_tableau_checks.v:96` | "The two models named at Sampled are typed over this prefix's observed execution, so the two statements hold" | One of the six intentionally changed docstrings. Production said "The two models above", which in `five_card_rows.v` pointed at the two Kim values immediately preceding. `five_card_tableau_sampled.v` names **three** Sampled values (`five_card_uniform_sampled`, `five_card_row_repeated_tableau`, `five_card_row_biased_tableau`), the first of them new, so the replacement phrase counts wrong. | "Kim's two models, named at Sampled, are typed over this prefix's observed execution, so the two statements hold." |
| F5 | MUST | `.../five_card_tableau_observed.v:30-31` | "five_card_F_ite == that ideal function, in its conditional spelling" | `five_card_F_ite` is a `Definition` whose **type** is the equation `fn_f five_card_F = (fun ab => if ab.1 then ab.2 else false)` and whose body is `erefl` (136-138). The entry glosses a proof of an equation as if it were a function. Its own docstring is type-honest ("The ideal function is checked up to conversion and not up to spelling"), so only the index is wrong. | "five_card_F_ite == the ideal function is its conditional spelling, up to conversion" |
| F6 | MUST | `.../five_card_tableau_algebraic.v:10-12` | "All seven published rows of this instance begin at that algebra, so five_card_algebraic_start is the one point at which the uniform analysis and Kim's two analyses agree." | Contradicted by the Observed header of the same directory (13-15): "five_card_committed is the prefix all seven published rows and the three named Sampled values of the instance continue from". The three analyses agree at Algebraic, at Executable and at Observed, and first differ at Sampled, where each names its own model. The same sentence shape sits in `instances/pgl27/tableau/pgl27_tableau_algebraic.v` in production, so it also belongs on the cross-instance list. | "All seven published rows of this instance begin at that algebra, and the uniform analysis and Kim's two analyses first differ three levels above, at Sampled, where each names its own model." |
| F7 | SHOULD | `.../five_card_tableau_sampled.v:14` | "Three families are named here, one per model a published row continues from" | The three families are declared in `instances/kim2025/five_card_models.v` (`five_card_uniform_family`, `kim_biased_family`, and `kim_centi_family`) and only used here; what this file names is three `Tableau Sampled` values. "Names" is the template's word for declaring, and the next paragraph uses it that way ("five_card_uniform_sampled follows the naming scheme"). | "Three programs are named here, one per model a published row continues from, and the three model families they sample are those of five_card_models.v: all three sit over the one committed run and are indexed by the unit type." |
| F8 | SHOULD | `.../five_card_tableau_sampled.v:30-31` | "What is proved at this level beside the three models is of two kinds, and no arm of certify takes a payload of either." | The file also proves `five_card_row_repeated_prefixE`, `five_card_row_biased_prefixE`, `five_card_row_repeated_modelE`, `five_card_row_biased_modelE`, `five_card_row_biased_levelE` and `kim_centi_small`; its own index lists eight key results. The universal reads as covering all of them. | "Two of the statements here are about neither a program nor the manifest's row for it, and no arm of certify takes a payload of either kind." |
| F9 | SHOULD | `.../five_card_tableau_sampled.v:40-41` and `.../five_card_tableau_analysis_bridged.v:12-14` | "It is the one security statement this instance makes below AnalysisBridged" / "The one security statement of the instance whose subject is neither is Kim's input-privacy bound" | `kim_biased_proximity_close` (reduced `five_card_proximity.v:143-156`) bounds, at every coalition, the sum of absolute differences between the two models' joint laws of that coalition's reading and the secret. It is at no level, and its subject is neither a payload nor a row. Either it is a security statement, and both universals are false, or the class the two sentences quantify over has to be named. The pair was written precisely so the two headers could not both be read as holding every security statement, so the remaining ambiguity is worth closing. | In both, restrict the class: "of the statements this directory makes" (Sampled) and "of the statements this directory makes, the one whose subject is neither a payload nor a row is …" (AnalysisBridged), with the distance in `five_card_proximity.v` named beside it. |
| F10 | SHOULD | `.../five_card_tableau_checks.v:19-20` | "which differ in two of their five coordinates" | The docstring 16 lines below, production's text, says "the two rows differ in two of their five fields" about the same `AnalysisPathRow`. One word per concept, file-wide; `MkAnalysisPathRow` has five fields. | "which differ in two of their five fields" |
| F11 | SHOULD | `.../five_card_tableau_checks.v:33` against the banner at `:187` | header "The seventh is what a certificate may hold"; banner "What a certificate may name as its ideal" | The seventh group holds four rejections and the header itself says they "have two causes", only one of which is about the ideal; the other three are about the sample adapter. The banner names only the first cause. | Banner: "What a certificate may hold", matching the header sentence. |
| F12 | SHOULD | `.../five_card_tableau_analysis_bridged.v:124-126` | "The six link lemmas of the exact arm are not there but here" | `five_card_colour_fill` is a `Definition` and the same header's index lists it under `Definitions:` (129-130). Five lemmas and one map. | "The map and the five link lemmas of the exact arm are not there but here, because no proof that stays uses them." |
| F13 | SHOULD | `.../five_card_tableau_sampled.v:80-83` | "one starting position's endpoint marginal under the repeated model's cut law is within 2^-40 of uniform" | The lemma is `var_dist … < 2%:R ^- 40`, a strict upper bound on a sum of absolute differences; the index sentence turns it into a distance. The reduced file's own new paragraph (`five_card_proximity.v:21-24`) exists to keep the two apart, and the lemma's docstring says "in variation distance" where the index drops it. | "== one starting position's endpoint marginal under the repeated model's cut law is under 2^-40 of the uniform law, in variation distance" |
| F14 | SHOULD | `.../five_card_tableau_analysis_bridged.v:78-81` and `:101-105` | "five_card_row_uniform_tableau, under The uniform row: … and the reading five_card_exact_view_secrecy."; "five_card_row_biased_proximity, under the same banner: … and the readings five_card_biased_view_proximity and five_card_biased_view_own_marginals." | The locator's job is to say where a name is, and both entries put a reading under a banner it is not under. `five_card_exact_view_secrecy` sits under "The exact arm's four conjuncts at this instance" (521-523), not "The uniform row" (474-476); the two proximity readings sit under "What the proximity row states at this instance" (1087-1089), not "One model, two claims, two rows" (1005-1007). The other five entries name nothing outside their banner. | Name the reading's own banner in both: "…and, under The exact arm's four conjuncts at this instance, the reading five_card_exact_view_secrecy"; "…and, under What the proximity row states at this instance, the readings five_card_biased_view_proximity and five_card_biased_view_own_marginals." |
| F15 | SHOULD | `staged/RETIRED.md:20` | "\| `instances/kim2025/five_card_proximity.v` \| 594 \| 165 \|" | The staged reduced file is 169 lines and `STATUS.md`'s own Lines table says 169. PSL(2,11) ruling 12: regenerate every count from the script's output. | 169. |
| F16 | SHOULD | `.../five_card_tableau_analysis_bridged.v:299-301` | "five_card_biased_indistinguishability_implies_proximity == the input-indistinguishability proposition implies it, its premise discarded" | Neither "it" nor "its" has an antecedent inside the entry; the reader has to carry one down from the preceding entry. The statement is `IndistinguishabilityPropAt (kim_biased_cert R tt) c -> IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 50)` and the discarded premise is the implication's own hypothesis. | "== the input-indistinguishability proposition at any constant implies the proximity proposition at one fiftieth, its hypothesis unused" |
| F17 | SHOULD | `.../five_card_tableau_algebraic.v:19` against `.../five_card_tableau_analysis_bridged.v:53` | "Two is the threshold that algebra names" / "Two is the threshold the derived profile declares" | One object, `profile_k (instance_profile five_card_algebra)`, two names in one directory. The AnalysisBridged wording is the one PSL(2,11) and PGL(2,7) use in production. | Use "the threshold the derived profile declares" in both. |
| F18 | SHOULD | `.../five_card_tableau_observed.v:91-104` | `five_card_committed_paramsE`: "this equation is what keeps the two spellings from parting"; `five_card_committed_executableE`: "this equation is what keeps a reader from having to decide which of the two spellings a statement below is made at" | Two adjacent equations, each said to hold "the two spellings" together, for two different pairs (clauses against `five_card_params`; one-term program against the Executable value). The second is new text and can take the distinguishing wording. | New docstring: "…the Executable file names the parameters they build, and this equation is what lets a statement made at that named value be read as a statement about the prefix." |
| F19 | SHOULD | `STATUS.md:314-317` | "That is the one environment change any moved declaration undergoes" | Seven declarations of `five_card_rows.v` (`five_card_target`, `five_card_committed`, `five_card_committed_paramsE`, `five_card_F`, `five_card_FE`, `five_card_F_ite`, `five_card_realises_expected`) land in the algebraic, executable and observed files, whose scope block is `ring_scope` alone against production's `fdist`, `proba`, `entropy`, `ring`. Template rule 3 sanctions that, the innermost entry being what decides a numeral, and the pin does cover them: all 82 non-`Fail` types are printed on both sides and the diff is empty. Only the sentence is wrong. | "Two environment changes: the 28 declarations that leave five_card_proximity.v are read under the four-scope block of the sampled, AnalysisBridged and checks files, and the seven that land in the algebraic, executable and observed files lose fdist, proba and entropy, keeping ring_scope as the innermost entry. Both are pinned: baseline.v and fidelity.v print all 82 types under one block and the diff is empty." |
| F20 | NOTE | `.../five_card_tableau_analysis_bridged.v:556, 565, 835-837, 876, 982, 1020, 1040` | "spends the number once", "the gap is the price of quoting the bundle's number", "erefl takes spent 147 s here against reflexivity's 0.07 s. Measured on notes/probes/2026-09-19-tableau-extensions/STATUS.md, section F2", "the status it earns", "spends it once", "naming the Sampled value costs", "The number is spent once" | All production text inside moved docstrings, so out of scope for this landing: metaphor and economic words for a relation, and one docstring carrying a timing and a probe path. Listed once, as the remit asks, for the closing comment pass. | No change now. Carry to the comment pass. |
| F21 | NOTE | placement of `five_card_colour_fill` and `five_card_viewS_nth` | — | Neither names a framework term: `five_card_colour_fill` maps a coalition's colour tuple to card positions through `encode_bool`, and `five_card_viewS_nth` is a reindexing of `ViewS` against `arr`. Both are encoding mathematics rather than program-level material, so the reduced file would hold them without strain. They are placed above only because their single consumer, `five_card_static_obsE`, is there. The placement is accepted; the reason is recorded in `STATUS.md` and should not have to be re-derived next time. | No change. |

## Placement, re-derived

Twenty-nine placements were checked against the framework rather than against
the table: the six contested ones, the four that stay, the eleven recorded
rejections, and eight sampled from the rest (`five_card_target`,
`five_card_F`, `five_card_F_ite`, `five_card_realises_expected`,
`five_card_row_biased_levelE`, `five_card_exact_witness`,
`five_card_reprice39`, `five_card_reprice_inv100`). All hold.

- **The six exact-arm link lemmas at AnalysisBridged.** The rule is applied
  consistently. At PGL(2,7) `pgl27_static_obsE` stayed because
  `pgl27_word_proximity_close` rewrites with it twice; here
  `kim_biased_proximity_close`'s proof
  (`five_card_proximity.v:157-167`) names `five_card_reading_secretE`,
  `five_card_uniform_pairE`, `five_card_arg_cut_prodE`,
  `five_card_sample_uniform_prodE`, `kim_single_cut_distE`,
  `five_card_sample_cut_distE`, `kim_biased_sample_cut_witnessE` and
  `kim_biased_cut_mixing_exact`, and no link lemma. The exception therefore
  does not transfer. See F21 for the one reservation.
- **`five_card_target` at Algebraic.** `manifest/pgg_tableau_syntax.v:334-336`
  shows the `encoded` rule taking a `Targeted` and building
  `tableau_start (tg_algebra t)` itself, so the `Targeted` is Algebraic-level
  data and not an Executable line. The Observed file earns its import of the
  algebraic module through `targeted_F five_card_target` (`:124`).
- **The functionality material at Observed.** `five_card_F` is typed over
  `oe_inputT five_card_observed`, the execution this level reaches, so it
  cannot sit lower. `targeted_F` reads the tolerated size from the scheme
  (`pgg_tableau_syntax.v:214-215`, `ts_k' (pga_scheme (tg_algebra t))`), which
  is what the Observed header claims.
- **Kim's input-privacy bound at Sampled, with `five_card_row_repeated_endpoint_lt`
  and `kim_centi_small`: accepted.** The owner's rule is to organize by what a
  phase means. `five_card_row_biased_leak_bound`'s subject is
  `sa_sampleP (amf_sample kim_biased_family R tt)`, the law the named Sampled
  model samples, and `manifest/pgg_tableau.v` has exactly three `certify`
  statements, `certify_exact`, `certify_indistinguishability` and
  `certify_idealproximity` (`:45124`, `:45997`, `:47002`), taking an
  `ExactPayload`, an `IndistinguishabilityPayload` and an
  `IdealProximityPayload`; they are the only producers of a
  `Tableau AnalysisBridged`. So the bound cannot be a payload and Sampled is
  where its subject lives. The one-security-claim-per-row rule is not broken:
  the biased row's chain reaches AnalysisBridged through
  `kim_biased_cert`, and the manifest's own level for that row rests on two
  theorems, the leak bound and the transfer, of which the programs carry the
  second. That is what F3 asks the header to say.
  On the two sentences the remit names: "no arm of certify takes a conditional
  mutual information as a payload" is true and checkable. "So no program can
  carry it one level up" is a universal that the three statements do support,
  since nothing else builds a `Tableau AnalysisBridged`, but it is read off
  three named statements and reads better as them: **recommendation**, "the
  three statements of certify take an ExactWitness, an IndistinguishabilityCert
  and an IdealProximityCert, and nothing else reaches AnalysisBridged".
- **`five_card_row_biased_levelE` at Sampled with its `Fail` in the checks
  file: accepted**, following PGL(2,7)'s split of `pgl27_reprice41` from
  `Fail pgl27_row_word41`. The equation is about the manifest's row, the
  rejection about this program, and each sits with its subject.
- **`five_card_row_biased_arm_neq` in the checks file: accepted.** It compares
  two rows rather than stating something about one, and the header applies
  PGL(2,7) ruling 7 correctly: `five_card_row_biased_proximity_armE` gives
  `IdealProximityArm`, `five_card_row_biased_branch_indistinguishability_armE`
  gives `InputIndistinguishabilityArm`, so one `AnalysisPathRow` published
  twice is two claims and not one claim twice.
- **The `Reprice` constants and the number lemmas at AnalysisBridged:
  accepted.** Template rule 3 keeps them in the file with the full scope block,
  and `five_card_reprice_inv100` arrives with the proximity material it
  refutes a conclusion for.
- **The four lemmas that stay: accepted.** They are the three laws and the
  distance the proximity certificate's last field is built from, and the
  reduced file's header says so.

## The reduced `five_card_proximity.v`

- Its four lemmas are token-identical to production's, the section that scopes
  them travels with them, and its innermost `Local Open Scope` is unchanged
  (`ring`, `fdist`, `proba`).
- Every name the four lemmas and their proofs cite resolves: the file compiles
  clean at rc 0, and the last import was measured by dropping each `From` line
  in turn rather than guessed, with `pgg_instance` kept as the declarer of
  `static_coalition_obs`.
- Its header is true. "This file requires no tableau module" matches the import
  list, and the AnalysisBridged file does require it for the certificate's last
  field, so the arrow runs one way.
- It reads like its two production siblings. It takes
  `instances/pgl27/pgl27_proximity.v`'s "holds the mathematics that separates
  the two, with no program and no published row in it" verbatim and
  `instances/psl211/psl211_word_proximity.v`'s sum-of-absolute-differences
  paragraph with this instance's numbers, as PGL(2,7) ruling 8 asks. One
  residue: the sentence "The distance is the certificate field of the
  proximity arm" names an upper bound a distance, two lines above the
  paragraph that separates the two. PGL(2,7) production says "One distance is
  the certificate field of the proximity arm", so this is the sibling's
  wording and not a new defect; it goes on the cross-instance list.

## The import graph and `_CoqProject`

- No cycle. The chain is algebraic, executable, observed, sampled,
  analysis_bridged, checks, with analysis_bridged also importing observed and
  checks also importing observed and sampled, and the reduced
  `five_card_proximity` entering at analysis_bridged and checks. No file uses
  `Require Export`.
- Every phase import is earned and each was checked by finding the name in the
  importing file: `five_card_algebraic_start` in executable;
  `five_card_target` (through `targeted_F`) and
  `five_card_committed_executable` in observed; `five_card_committed` in
  sampled; `five_card_committed`, the three Sampled values and
  `kim_biased_proximity_close` in analysis_bridged; `five_card_committed`,
  `five_card_F`, the two Kim Sampled values, four payloads,
  `five_card_reprice39`, `five_card_row_biased_proximity` and
  `kim_biased_proximity_close` in checks.
- The two non-phase S5 imports of the checks file are earned as well:
  `s5_rand_family` is declared in `instances/s5/s5_models.v` and
  `s5_rand_exact_witness` in `instances/s5/tableau/s5_tableau_analysis_bridged.v`,
  both used in `Fail kim_biased_cert_s5_ideal`. `S5Analysis.rand_family` of
  `Fail five_card_row_s5_family` resolves through a transitive `Require` of
  `instances/s5/s5_analysis.v`, which is why the recorded rejection does not
  print "was not found in the current environment".
- Module names: the six base names `five_card_tableau_*` occur nowhere else in
  the tracked tree, and the placement of the six lines after
  `instances/kim2025/five_card_proximity.v` is forced by two independent facts,
  that the AnalysisBridged file requires the reduced file and that the checks
  file requires `s5_tableau_analysis_bridged`. The reverse closure of
  `five_card_rows` is `{five_card_proximity}` and the cut removes that arrow,
  so nothing between the two positions breaks. Deriving both positions by name
  at the time of the `cp` is the right instruction, the line having moved from
  225 to 231 under this work.

## `RETIRED.md` and the one repoint

- The scan is the one PGL(2,7)'s F5 asks for: both names, every tracked file,
  only `notes/` and `.claude/` excluded, every hit tabled with its reason. The
  four `docs/superpowers/plans/` hits are dated records and are correctly left
  alone.
- **Applying the `manifest/pgg_tableau_arm_relations.v` repoint with this
  instance is right.** The reason that defers a manifest repoint is batching a
  rebuild, and nothing in the tracked tree requires that module, so there is no
  rebuild to batch. Left unrepointed the comment would name a file that no
  longer holds the lemma it cites.
- **The repointed citation is true.**
  `five_card_biased_indistinguishability_implies_proximity` is declared in
  `five_card_tableau_analysis_bridged.v`, its conclusion
  `IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 50)` is
  `five_card_biased_proximity_prop_holds` in the same file, and its hypothesis
  is unused, so "holds because its conclusion is a theorem there and its
  premise is discarded" survives the move word for word.
- The diff against production is one hunk, comment-only, two box lines, both at
  80 columns. `five_card` occurs nowhere else in that file, so
  `arm_relations` says nothing else about where a five-card statement lives.

## The fidelity pin for bodies

- The claim that the certificates need no re-scoping is confirmed:
  `instances/kim2025/five_card_rows.v` opens `fdist`, `proba`, `entropy`,
  `ring`, which is exactly the block of the sampled, AnalysisBridged and checks
  files. `kim_centi_cert`, `kim_biased_cert` and `kim_biased_cert_exact` are
  parsed under one block on both sides, and their numbers are pinned by printed
  equations anyway (`kim_centi_cert_epsE`, `kim_biased_cert_epsE`,
  `kim_biased_proximity_eps_halfE`).
- No other `Definition` whose type hides data is left unprinted. The four
  printed are the two re-scoped ones holding a literal
  (`kim_biased_proximity_cert`, `five_card_reprice_inv100`) and the two
  `Reprice` constants of the rows file (`five_card_reprice39`,
  `five_card_reprice_inv25`), which are the same risk class because
  `Reprice` is `forall R : realType, option R`. Every other re-scoped numeral
  sits inside a printed statement closed by conversion.
- The one gap is in the record, not the verification: see F19.

## The numbers, each against its certificate and its row

Checked in the staged text and all correct as the AnalysisBridged header
states them.

| Object | Statement | Header's claim |
|---|---|---|
| `kim_centi_cert` | `cert_eps = Num.sqrt 5%:R * (1 / 80) ^+ 7 + Num.sqrt 5%:R * (1 / 80) ^+ 7` | "the square root of five times the seventh power of one eightieth, and its cert_eps is that number added to itself" — correct |
| its row | `kim_centi_cert_eps_lt : cert_eps … < 2%:R ^- 39`, strict | "kim_centi_cert_eps_lt is strict, so the number the row publishes is strictly above the number the certificate proved" — correct; `five_card_pow2_39_split` is `2^-40 + 2^-40 = 2^-39` |
| `kim_biased_cert` | `cert_eps = Num.sqrt 5%:R * (1 / 80) + Num.sqrt 5%:R * (1 / 80)` | "the square root of five over eighty, so its cert_eps is the square root of five over forty" — correct |
| `kim_biased_cert_exact` | `five_card_inv50_split : 1 / 50 + 1 / 50 = 1 / 25`, an equality; `kim_biased_proximity_eps_halfE` ties `cert_eps` to twice `ipc_eps` | "the exact one-cut number, one fiftieth, so its cert_eps is one twenty-fifth", and "five_card_inv50_split is an equality, so there the two numbers are the same" — correct |
| `kim_biased_proximity_cert` | `ipc_eps = 1 / 50` | "carries one fiftieth and compares one law with one law, so that is also what its row publishes" — correct |
| own marginals | `five_card_biased_view_own_marginals` at three fiftieths | "which leaves an advantage of at most three hundredths" — correct |
| the halving | — | "a distinguisher's advantage against a row is at most half the number that row publishes: one hundredth at the proximity row, one fiftieth at the one-cut row concluded at one twenty-fifth" — correct |
| threshold | `five_card_singleton_below_threshold : #\|[set i]\| < profile_k (instance_profile five_card_algebra)`, and the binder `(#\|C\| < 2)%N` on the arm theorems | "every statement here that quantifies over a coalition quantifies over at most one of the five seats" — correct |
| the seat sentence | `static_coalition_obs` reads `ex_content_obs E x (g, tnth (pi_starts …) i)`, and the five-card proof reduces it to `tnth (den_boer_layout u.1) (pgg_rho g (tnth (pi_starts FiveCardKim_PI) i))`; the algebra declares `seat players (ord_tuple 5)` | "each seat reading the card at the cut image of its own position" — **correct, and an improvement on the other three instances**, which write "at its own position" and drop the cut |

## The rest of the checklist

Every item on the remit's list was run. Clean: no line over 80 bytes in any of
the seven files; no stray `**)`; no box content line abutting `*)`; every
section banner exactly one content line; every non-`Fail` declaration indexed
and no `Fail` indexed, in all seven files, with exact spellings, no
duplicates and no name touching `==`; no proof strategy, history word,
probe, stage or landing word, timing or paper table in new text; no metaphor
or economic word in new text (all such hits are in moved docstrings, F20); no
"view" as a prose noun in new text; no abbreviation of "indistinguishability";
none of the project's banned vocabulary list, the only hits being substrings
inside "proposition", "position" and the framework's own `Reprice`.

Items that are clean and were worth checking because they failed elsewhere:
the level count ("three levels above, at Sampled" is right, `CompletionLevel`
having five constructors); the Sampled obligation, stated as the run argument
and the cut, matching `sampled_viewE_prop`; the `conclude` obligation, stated
as one inequality per real field and per index, matching `ConcludePayload`;
the sharpness sentence, true in both halves, since no staged file uses the
`leaks at` form and no positivity lemma exists for `leak` at two or more
cards; the locator table, every name and banner title of which exists with
that spelling, every "no `_rowE` of its own" and "no reading of its own" being
true, with the one exception at F14; "under a different arm" rather than a
second publication of one claim; and the three manifest rows over this
instance, which are exactly `five_card_row_uniform`, `five_card_row_biased`
and `five_card_row_repeated`.

## Cross-instance list for the closing pass

Places where the four instances say the same thing in different words with no
mathematical reason. Listed only; no rewrite of a production file is proposed
beyond the list.

1. **The Algebraic frame's verb for the group.** S5 "which group acts on the
   deck", PSL(2,11) and PGL(2,7) "which group shuffles the deck", five-card
   "which group cuts the deck". Five-card's is the instance's own word and has
   a reason; the other three do not differ for one.
2. **The Algebraic frame's closing claim.** PGL(2,7) "the value below is the
   one point at which the exact, the word and the prior-indexed exact analyses
   agree" and five-card "the one point at which the uniform analysis and Kim's
   two analyses agree" are both contradicted by their own Observed headers,
   which name a shared Observed prefix. PSL(2,11) stops at "Every twelve-card
   row begins here" and S5 at "the instance's two sharing-family runs agree".
   One form for all four, and it has to be a true one. This is F6.
3. **The Executable frame's list of run-level data.** S5, PGL(2,7) and
   five-card include "what a seat observes after a shuffle" or "after a cut";
   PSL(2,11) omits the clause entirely. And "after a shuffle" against "after a
   cut" is instance vocabulary with a reason, unlike the omission.
4. **The Executable "meant to recover" clause.** All four carry the negated
   form correctly. Two carry a positive "recovers" further down:
   `instances/psl211/tableau/psl211_tableau_executable.v:17` ("the value the
   run recovers is the chirality bit") and five-card at F2. PSL(2,11) ruling 1
   applies to both.
5. **The Sampled obligation sentence.** PSL(2,11), PGL(2,7) and five-card say
   "computed directly from the run argument and the cut", which is what
   `sampled_viewE_prop` states.
   `instances/s5/tableau/s5_tableau_sampled.v` still says "from the layout and
   the cut". The pilot predates the ruling and is the odd one.
6. **The AnalysisBridged coalition sentence.** PSL(2,11) "Six is the privacy
   threshold the derived profile declares, so every statement here that
   quantifies over a coalition quantifies over at most five of the twelve
   seats, each seat reading the card at its own position"; PGL(2,7) the same
   with four and three of eight; five-card the same with two and one of five
   but "each seat reading the card at the cut image of its own position"; S5
   an entirely different paragraph shaped round the sum-mod scheme, with
   "each seat reads the card at its own position". Two things to settle: one
   form of the sentence, and whether the cut image belongs in it. The
   framework applies the group element (`static_coalition_obs` passes
   `(g, tnth (pi_starts …) i)` to `ex_content_obs`), so five-card's is the
   accurate one and the other three understate it.
7. **The threshold's owner.** "the threshold the derived profile declares"
   (PSL(2,11), PGL(2,7), five-card's AnalysisBridged) against "the threshold
   that algebra names" (five-card's Algebraic). One phrase. This is F17.
8. **The checks header's frame and title.** S5 and PSL(2,11) title the file
   "what the <instance>'s phases reject"; PGL(2,7) and five-card "the terms the
   kernel refuses at the <instance>". Both frames also open differently, the
   second with the "one written term … and about no other term" paragraph that
   came out of audit F12. The second is the ruled one and the first two
   predate it.
9. **The locator table.** Only PGL(2,7) and five-card have one, PGL(2,7)
   ruling 12 having arrived third. Their formats differ: PGL(2,7) prints it as
   part of the prose, five-card as an indented block with one entry per row.
   PSL(2,11)'s AnalysisBridged file may not need one; S5's does not.
   Worth one format for the two that have it.
10. **The reduced files' sum-of-absolute-differences paragraph.** PSL(2,11),
    PGL(2,7) and five-card now carry the same sentence with their own numbers,
    which is the outcome ruling 8 wanted. What still differs is the sentence
    before it: PGL(2,7) "One distance is the certificate field of the
    proximity arm", five-card "The distance is the certificate field of the
    proximity arm", PSL(2,11) "it carries the distance the proximity arm of
    this instance takes as its distance field". All three name an upper bound
    a distance, next to a paragraph that separates the two. One form, and it
    should say bound where the statement is a `<=`.
11. **The threshold sentence in the reduced files.** PSL(2,11) "Six is the
    privacy threshold the derived profile declares, and the distance below is
    proved at every coalition of the twelve seats, the threshold entering the
    arm's proposition and not the distance"; five-card "The bound holds at
    every coalition and not only below the threshold of two; the threshold
    enters the arm's proposition and not this distance". Same fact, two
    shapes.
12. **Who owns the word "reading".** Five-card's headers use "reading"
    throughout and keep "view" to moved docstrings and identifiers, which is
    what the template asks. Worth confirming the same of the three production
    directories in the same pass, since their identifiers carry `view` and
    `View` and their headers were written before the ruling settled.
