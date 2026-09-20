# Audit of the prose pass, group kim + pgl27

Read-only audit of `prose_replacements_kim_pgl27.txt`, 464 sites, over the
working tree on top of c07f6a8. No repository file was edited except this one.
Nothing was compiled. The mechanical checks of `check_prose.py` were not
redone: what is audited here is the sense chosen at each site and the truth of
the ruled sentences.

## Verdict

**NO-GO.** Three findings are MUST: T1, T2, T3. T1 is the large one, the 22
sites of `pgl27_profile_privacy.v`, where the noun names a kind of object the
file does not contain and, for the all-decks half, an object that exists
nowhere in the tree. T2 and T3 are one word each and both are decided by a
record definition. The rest of the 464 sites hold up.

## Findings

| id | class | file:line | the sentence now | problem, with the declaration quoted | replacement |
|---|---|---|---|---|---|
| T1 | MUST | `instances/pgl27/pgl27_profile_privacy.v`: 32 (twice), 34, 45, 47, 53, 64, 77, 78, 79, 337, 347, 354, 359, 361, 363, 393, 402, 471, 518, 522, 595 | "by placing the two PGL(2,7) programs in its sample space. The exact program goes through the mixed-law condition ... the all-decks program goes through the per-deck condition" (32-34); "pgl27_dealerPE == the exact program's law pushed along pgl27_dealer_embed is the dealer model's law at the deterministic kernel" (359); "pgl27_alldecks_dealerP == the all-decks program's data in the dealer model's sample space" (595) | The file imports no tableau module. Its imports (lines 85-98) are `pgg_interface`, `pgg_monodromy_profile`, `pgg_sharing_framework`, `covering_scheme`, `transitivity_privacy`, `dealer_privacy`, `pgl27_group`, `pgl27_orbit`, `pgl27_scheme`, `pgl27_profile`, `pgl27_secrecy`, so no `Tableau`, `Published` or `AnalysisPath` value is in scope. The two referents are laws: "the exact row" is `pgl27P` (`instances/pgl27/pgl27_secrecy.v:66`, `Definition pgl27P : R.-fdist (bool * pgg_gT pgl27_M)`), which `pgl27_dealerPE` names on the left of its equation, and "the all-decks row" is `pgl27P_alldecks` (`instances/pgl27/pgl27_trace.v:456`). The sentences give the referent a law (359), a view (393), a secret (402), the deck it lays (471), two coordinates (522) and data in a sample space (347, 595). `Record PublishedAt (c : ConcludedBound) := MkPublished { published_at : StackAt AnalysisBridged ; published_path : AnalysisPath ; published_thm : BridgedProp c published_at }` (`manifest/pgg_tableau.v:932-935`) has none of these. For the all-decks half there is no such value at all: the only all-decks path in the manifest is `psl211_alldecks_path` (`manifest/pgg_analysis_manifest.v:1075`) and the pgl27 tableau file publishes seven values, none all-decks. The sense is none of the sheet's four, so sheet rule 1 asks for these to be listed rather than resolved | "model" file-wide: "placing the two PGL(2,7) models in its sample space", "the exact model's law pushed along pgl27_dealer_embed is the dealer model's law at the deterministic kernel", "the all-decks model's data in the dealer model's sample space". "analysis" reads as well and avoids standing next to "the dealer model"; the choice is the owner's. Not "program", and not "path" |
| T2 | MUST | `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:357` | "Its last line publishes a program whose transfer status is StaticExecutedOnly" | `Definition publish (a : AssumptionStatus) (c : ConcludedBound) (q : StackAt AnalysisBridged) (pf : BridgedProp c q) (t : TransferStatus) := @MkPublished c q (@MkAnalysisPath (ab_obs q) AnalysisBridged (ab_f q) t a) pf` (`manifest/pgg_tableau.v:945-949`): the transfer status is `ap_transfer`, a field of the path the line builds. `PublishedAt` has no transfer status. Both siblings say path: `five_card_tableau_analysis_bridged.v:499` "Its last statement publishes a path whose transfer status is StaticExecutedOnly" and `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:173-174` "Its last line publishes a path whose transfer status is StaticExecutedOnly" | "Its last line publishes a path whose transfer status is StaticExecutedOnly" |
| T3 | MUST | `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:926-928` | "An AnalysisPath holds descriptive metadata and no Prop, so an equation between two published programs says nothing about either certificate, and in particular cannot say which transfer status is the honest one." | The lemma under it is `five_card_biased_forms_pathE : published_path five_card_biased_indistinguishability_published = published_path five_card_biased_published_inv25`, an equation between the two published paths. The inference is valid only of paths: an equation between two `PublishedAt` values carries `published_thm` with it and therefore does say something about the certificates. Base text at c07f6a8 line 915 read "between two published rows", so the sense choice, not the old wording, is what broke it | "so an equation between two published paths says nothing about either certificate" |
| T4 | SHOULD | same file, `:1055` and the index entry at `:286-287` | "The branch publishes the manifest's own path for the biased path." and "== the branch publishes the manifest's path for the one-cut path" | The noun is doubled for two different things, which is exactly the defect ruling R2 removed from the proximity twin at 1076 ("The proximity program publishes the manifest's biased path"). The lemma: `five_card_biased_branch_indistinguishability_published_pathE : published_path five_card_biased_branch_indistinguishability_published = five_card_biased_path`, so the path the branch publishes IS `five_card_biased_path` | 1055: "The branch publishes the manifest's own biased path." Index: "== the branch publishes the manifest's one-cut path" |
| T5 | SHOULD | `instances/kim2025/five_card_mixing.v:16-17` | "Those two are the base premises of the certificates the analysis manifest records for Kim's one-cut and seven-cut paths." | The manifest records no certificate. `Record AnalysisPath := MkAnalysisPath { ap_observed ; ap_completion ; ap_model ; ap_transfer ; ap_assumptions }` (`manifest/pgg_analysis_manifest.v:940-958`), and the docstrings of `five_card_repeated_path` and `five_card_biased_path` name theorems only, for instance "its base premise is FiveCardAnalysis.centi_cut_mixing ... with FiveCardAnalysis.static_obs_const for the reading equality". The certificates `kim_centi_cert` and `kim_biased_cert` are carried by the programs of `five_card_tableau_analysis_bridged.v`. The same phrase in the sibling `five_card_analysis.v:16`, "Kim's one-cut and seven-cut programs", took the other noun, so the pair also disagrees | "Those two are the base premises of the certificates Kim's one-cut and seven-cut programs carry." A second honest form keeps the manifest as the subject: "the base premises of the transfers the analysis manifest records for Kim's one-cut and seven-cut paths", which is what the two path docstrings state |
| T6 | SHOULD | `five_card_tableau_analysis_bridged.v:150`, `:603`, `:681`, `:697`, `:721` and the index at `:215`, `:221`, `:227`; `five_card_tableau_sampled.v:143` | "the repeated program's certificate at its bundle's number" (150), "The input-indistinguishability certificate of the repeated program" (603), "The repeated path's certified program publishes ..." (681), "the repeated certified program continues the named repeated model" (index 215), "The repeated program sampled and not certified" (sampled 143) | One value, `five_card_repeated_indistinguishability_published`, carries three names inside one file, and a fourth value gets one of them. At sampled 143 "the repeated program" is `five_card_repeated_sampled : Tableau Sampled`, and eight lines later the same docstring calls the certified value "the certified program for the same path", so inside one directory "the repeated program" names both the Sampled value and the certified one. The one-cut twins at 152, 621, 691, 710, 734 and sampled 157 have the same shape. The definition docstrings at 641 and 663 are outside this: there "Kim's repeated program" and "Kim's one-cut program" introduce the value being defined | Use "the repeated certified program" at 150, 603, 681, 697, 721 and "the one-cut certified program" at their twins, keeping "the repeated program" for the Sampled value and for the sentences that name the constant a terminal concludes at, as at 42, 82, 250, 823 |
| T7 | NOTE | `instances/pgl27/pgl27_spectral.v:537` (ruling G9) | "This is the one spectral input of the PGL(2,7) path and the only place the certificate tables are used." | A path holds five descriptive coordinates and no certificate, so nothing is an input of it; the spectral input belongs to the certificate's `ic_b` and mixing fields and to the program carrying them. The instance also has three paths, `pgl27_exact_path`, `pgl27_word_path` and `pgl27_prior_exact_path`, so "the PGL(2,7) path" singles none out. The old text said "the PGL(2,7) row" and had the same two problems. The ruling's reason for "path", alignment with `instances/s5/s5_mixing.v:419` "the one spectral input of the S_5 path", is real and is met | If the owner wants it honest and still aligned: "the one spectral input of the PGL(2,7) word analysis", with "the S_5 word analysis" in the twin |
| T8 | NOTE | `instances/kim2025/tableau/five_card_tableau_sampled.v:25-26` | "five_card_repeated_sampled and five_card_biased_sampled are names the instance already had, and they carry the published-program suffix although both are Tableau Sampled values and neither is a published program." | Both names end in `_sampled`. No value in the group is named `five_card_repeated_published` or `five_card_biased_published`, so the premise is not true of the two names it is about. The base text said "the published-row suffix", so the pass did not cause it | None proposed: the owner has to say which suffix the sentence meant before a one-word repair is possible |
| T9 | NOTE | `five_card_tableau_analysis_bridged.v:176-177` | "== the one-cut path as a program at the proximity arm, published at one fiftieth" | `Definition five_card_biased_proximity_published : Published` (line 1071) has no `conclude` line, and `Notation Published := (PublishedAt no_concluded_bound)` (`manifest/pgg_tableau.v:940`), so the value publishes no number. One fiftieth is `kim_biased_proximity_cert`'s own number. The pgl27 twin at 131-132 says "concluded at 2^-39" and its value really is `PublishedAt pgl27_bound39`, so the two entries differ for a true reason. The file's header at 38-39 uses the same loose idiom, "so that is also what its program publishes" | "certified at one fiftieth", or leave it and accept the idiom the header sets |
| T10 | NOTE | sense-4 sweep, 108 occurrences | the word "row" that remains in comments of `instances/kim2025/**` and `instances/pgl27/**` | Every one is a row of a matrix, of a census or code table, of an interpreter trace, or of a dealt deck. Counted per file: `five_card_exec.v` 27, `pgl27_table_bridge.v` 26, `pgl27_view_census.v` 19, `pgl27_models.v` 7, `pgl27_spectral.v` 5, `five_card_kim.v` 4, `pgl27_encoding.v` 3, `pgl27_mixing.v` 3, `five_card_tableau_analysis_bridged.v` 3 (the leakage space's cut row at 392, 395, 429), `five_card_mixing.v` 2, `kim_input_privacy.v` 2, `pgl27_analysis.v` 2, and one each in `five_card_analysis.v`, `five_card_family.v`, `five_card_models.v` ("The program layer rows are empty", a row of the condition table at 60-68), `pgl27_exec.v`, `pgl27_encoding_r5.v`. None is sense 1, 2 or 3 | none |

## The ruled sentences, checked against the code

- **K1** true. `published_thm` is the third field of `Record PublishedAt`
  (`manifest/pgg_tableau.v:932-935`), and `Record AnalysisPath`
  (`manifest/pgg_analysis_manifest.v:940-958`) has five fields and no `Prop`.
  The sentence at `five_card_tableau_analysis_bridged.v:86-88` is true.
- **K2** true, and aligned with G2: the four glosses at 149, 155, 158, 176 read
  "the ... path as a program", as pgl27's 102, 103, 131 do.
- **K3** applied at 681, 697, 710, 721, 734 and `five_card_tableau_checks.v:126`.
  The first sentence at 681 is true: the lemma is
  `published_path five_card_repeated_indistinguishability_published = five_card_repeated_path`.
  The residual cost of the ruling is T6.
- **K4 and R1** true and identical in the two files, at `five_card_...:1078-1080`
  and `pgl27_...:49-51` and `:927-929`.
- **K5** applied at sampled 53 and 219, "also has a certified program", "also
  has a program".
- **K6** applied at checks 18-19.
- **K7** true. `five_card_repeated_path = MkAnalysisPath FiveCardAnalysis.observed
  AnalysisBridged FiveCardAnalysis.centi_family IdealFinite BaselineClassicalOnly`
  (manifest 1029-1031) and `five_card_uniform_path = MkAnalysisPath
  FiveCardAnalysis.observed AnalysisBridged FiveCardAnalysis.uniform_family
  StaticExecutedOnly BaselineClassicalOnly` (manifest 991-993) differ in exactly
  two of five fields, the model and the transfer status, which is what checks
  124-128 says.
- **K8, K9, G6, G7** true and twin-identical: `five_card_proximity.v:11` and
  `pgl27_proximity.v:11` both read "with no program in it, published or not",
  and `five_card_proximity.v:37` and `pgl27_proximity.v:42` both read "The
  certificate itself, the program published over it and the statements about
  them". Both files state, and their imports confirm, that they require no
  tableau module.
- **K10** true: `five_card_mixing.v:29-30` "The manifest sits below the file
  whose programs publish those paths".
- **K11** applied at 156 only. The splits at 172, 227 and 295 remain, which is
  what follow-up R5 decided, so this is not a defect against the rulings.
- **G1, G2** applied at 56, 353, 102, 103, 131.
- **G3** true: the lemma is
  `published_path pgl27_prior_exact_published = pgl27_prior_exact_path`, so
  "the manifest's path for this program" at 804 names it, as P1 does in psl211.
- **G4 and R2** true: `published_path pgl27_word_proximity_published =
  pgl27_word_path` and `published_path five_card_biased_proximity_published =
  five_card_biased_path`, so "the manifest's word path" and "the manifest's
  biased path" name the right values.
- **G5** applied at 51-53.
- **G8** true. `pgl27_word_marginal_bound R` is the first field, `ic_b`, of
  `pgl27_word_cert` (`pgl27_tableau_analysis_bridged.v:341-349`, against
  `Record IndistinguishabilityCert ... { ic_b : ShuffleMarginalBound R
  (instance_M A) ; ... }` at `manifest/pgg_tableau.v:194-206`), and the index at
  100-101 calls `pgl27_word_cert` "the input-indistinguishability arm's
  certificate". The number is that bound's epsilon, 2^-40.
- **G9** applied, see T7.
- **G10** applied, identical to K4.

## Twin pairs

Aligned, checked side by side:

- the docstrings of `*_proximity_published_pathE`, kim 1076-1080 and pgl27
  925-929;
- "one manifest path published by an input-indistinguishability program and by
  a proximity program says nothing about either claim", kim 1078-1080, pgl27
  49-51 and 927-929. Kim's header carries the K1 sentence instead, "two
  programs publishing one AnalysisPath say nothing about each other's claim",
  with the same nouns;
- "The path the ... program publishes is the manifest's own path for ...", kim
  523, pgl27 422;
- "the two programs over the one model carry different arms", kim checks 236,
  pgl27 checks 107;
- "what this file fixes is shared by every program the instance publishes", kim
  algebraic 31, pgl27 algebraic 59;
- "the prefix all seven published programs continue from", kim observed 14 and
  algebraic 70, pgl27 observed 15 and algebraic 57.

Disagreeing: T2 (pgl27 357 against kim 499 and psl211 173) and T5 (mixing 17
against analysis 16).

## The three five-card things

Checked against the declaration each phrase sits on.

- `five_card_repeated_path`, the manifest's path: called "the repeated path"
  (70), "the manifest's repeated path" (681), "the manifest's path" (index
  222). Right everywhere.
- `five_card_repeated_sampled`, the Sampled program: called "the repeated
  program sampled and not certified" (sampled 143). See T6.
- `five_card_repeated_indistinguishability_published`, the certified finished
  program: "the repeated path's certified program" (681, 697, 721), "the
  repeated certified program" (index 215, 221, 227, checks 19, 125), "the
  repeated program" (150, 603). See T6.
- `five_card_repeated_published39`, the concluded program, is a fourth value
  and is consistently "the repeated program concluded at that number" (index
  163) or "the repeated program" in a context that names the constant (42, 250,
  823, 852). No confusion found there.

## Coverage

- Read in the listing: 464 of 464 sites, every line of
  `prose_replacements_kim_pgl27.txt`.
- Opened in the file: about 188 sites. That includes all 48 sites outside the
  `tableau/` directories and all 80 sites tagged `[PATH]`, each read in its
  declaration or header paragraph.
- Also opened for verification, outside the share:
  `manifest/pgg_tableau.v` (the `PublishedAt`, `RestatedTableau` and
  `IndistinguishabilityCert` records, `publish`, `Published`),
  `manifest/pgg_analysis_manifest.v` (the `AnalysisPath` record and the five
  path values of this share),
  `instances/pgl27/pgl27_secrecy.v`, `instances/pgl27/pgl27_exec.v`,
  `instances/pgl27/pgl27_models.v`,
  `instances/psl211/tableau/psl211_tableau_analysis_bridged.v` and
  `instances/s5/s5_mixing.v` for the twins.
- Base text consulted through `git show c07f6a8:<file>` at the six sites where
  the old wording decided the reading.
