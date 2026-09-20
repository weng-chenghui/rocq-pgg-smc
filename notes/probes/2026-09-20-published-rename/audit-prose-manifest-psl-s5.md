# Audit of the noun pass: group manifest + psl211 + s5 (383 sites)

Read-only audit of the sense chosen at each site and of the truth of the ruled
sentences. The mechanical results (only the noun changed, code tokens identical,
80-byte limit) are taken as given and were not redone.

**VERDICT: NO-GO.** Two MUST rows (S1, S2), both one-word fixes in
`manifest/`. Everything else is SHOULD or NOTE. No site outside those two
was found to have taken the wrong sense, and the sense-4 scan is clean.

## Findings

| id | class | file:line | the sentence now | problem, with the declaration quoted | replacement |
|---|---|---|---|---|---|
| S1 | MUST | `manifest/pgg_tableau_syntax.v:362-363` | "What this statement builds is the observed execution, and publish writes it unchanged into the program's ap_observed." | `ap_observed` is the first field of `Record AnalysisPath`, and `publish` writes the observed execution into the path it builds: `@MkPublished c q (@MkAnalysisPath (ab_obs q) AnalysisBridged (ab_f q) t a) pf` (`pgg_tableau.v:948-949`). `PublishedAt` has three fields, `published_at`, `published_path`, `published_thm`, and no `ap_observed`. The tree's own possessor for this field is the path: `pgg_analysis_manifest.v:2215` reads "typed at the execution projected from its own path's observed execution". | "into the path's ap_observed" |
| S2 | MUST | `manifest/pgg_tableau.v:928-929`, docstring of `Record PublishedAt` | "A program's data, the manifest path describing it, and the proposition the program reached. The manifest already publishes the descriptive path; ..." | A manifest publishes nothing; a program publishes a path. The owner ruled this exact phrasing out twice: G5 for the pgl27 header, and R3 for `s5_tableau_sampled.v`, where "What the manifest publishes for that path" became "What the manifest names for that path". This site is the declaration of `PublishedAt`, the type the whole rename is about. The old sentence said the same with the old noun. The manifest's own verb is at `pgg_analysis_manifest.v:9`, "records each analysis path as one typed value". | "The manifest already records the descriptive path;" |
| S3 | SHOULD | `manifest/pgg_analysis_manifest.v:1026`, docstring of `five_card_repeated_path` (ruling M3, second place) | "endpoint_bound and deal_centi_lt stay named in the path as endpoint marginal bounds" | True of the prose entry, where M3's first place sits (`:403-404` and `:425-428` of the Path 5 table name both theorems), but this docstring is attached to the typed value, and the `AnalysisPath` docstring twelve lines above says the opposite of it: "It stores no theorem: theorems stay facade aliases, named separately and pinned by spelled type in the checker below" (`:935-936`). | "endpoint_bound and deal_centi_lt are listed for this path as endpoint marginal bounds" |
| S4 | SHOULD | `instances/s5/tableau/s5_tableau_observed.v:94`, docstring of `s5_dealt_path_observedE` (ruling P2) | "... so the path's description of the run and the proof of run correctness for it are one term, which is the whole of what this path records." | `s5_det_path = @MkAnalysisPath S5Analysis.observed Observed None NoModelComparison (AcceptsAxioms [:: AxS5GroupOrder])`: the path also records the level, the empty model slot and two statuses, so the identification is not the whole of what it records. It is the whole of what the path says about the run. P2's first half is an improvement: with "path" the sentence now states what the equation `ob_obs (tableau_at s5_dealt) = ap_observed s5_det_path` actually says. | "which is the whole of what this path says about the run" |
| S5 | SHOULD | `instances/psl211/psl211_word_proximity.v:12` | "The certificate built on them, the program it certifies and the statements about that program are at AnalysisBridged" | A certificate certifies nothing; a program certifies an arm over a certificate (`pgg_tableau_arm_relations.v:6`, "A Tableau program certifies one of three arms"). The two sibling headers were repaired for the same shape by G7 and K9 and now read "the program published over it" (`instances/pgl27/pgl27_proximity.v:42`, `instances/kim2025/five_card_proximity.v:37`), so this is also a twin pair that disagrees. The old sentence said the same with the old noun. | "the program certified over it" |
| S6 | NOTE | `manifest/pgg_analysis_manifest.v:726, 819, 848, 850` | "none: this program is published through the exact arm ..."; "none: the program's certificate carries its own distance field"; "a distinguisher's advantage against this program is at most 2^-41"; "the model of Path 9 is the ideal this program's certificate is measured against" | Each is true, and each is supported by an idiom that predates the pass: `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:34` and `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:49` both read "advantage against a row" at c07f6a8 in a place where the old noun is plainly the program, and a certificate is carried by a program. What is uncomfortable is only the antecedent: these are the four occurrences of "program" in the two manifest tables, and no program is named anywhere in the Path 10 or Path 11 entry, whose every other referent is "the path's". Reading all four as the path is also true and keeps one word per concept in the file, which otherwise says "path" 107 times. Owner's call. | optional: "this path", "the path's certificate", "against this path", "this path's certificate" |
| S7 | NOTE | `protocol/pgg_functionality.v:141-142` | "... puts functional_extensionality_dep and propositional_extensionality into the program's assumption list ..." | Checked as a candidate error and cleared. "path" would collide with the manifest's own convention at `:50-58`: the classical trio "is NOT listed in an assumption status", so it is precisely what a path's `ap_assumptions` never holds. The raw output that does hold the trio belongs to a term carrying a proof, and of the two nouns only the program is one. The nearby "Print Assumptions on the path reports s5_group_order_eq beyond the classical trio" (`pgg_analysis_manifest.v:495`) is about named axioms beyond the trio, a different claim, so the two are not in conflict. | none |
| S8 | NOTE | `manifest/pgg_analysis_manifest.v:852-854` (ruling M2) | "... and the programs published over them prove different statements, Path 9's exact independence and this path's a bound on the distance to that independent model." | The content is true: over Path 9 `psl211_alldecks_published` proves exact independence, over Path 11 `psl211_word_proximity_published` proves the 2^-40 bound, and the two paths differ exactly in the model family (`PSL211Analysis.exact_family` against `word_family`) and the transfer status (`StaticExecutedOnly` against `IdealFinite`). The elliptical genitives can still be read as the paths' own statements, which is what M2 set out to remove. | optional: "..., prove different statements: exact independence over Path 9, and over this path a bound on the distance to that independent model." |
| S9 | NOTE | `instances/s5/s5_exec.v:903` | "The three obligations below carry the mode word and the plug, the family and the program keep the instance's own word." | The three lines do not decide the referent: `s5_rand_exec_plug`, `s5_rand_family`, `s5_rand_published` and `s5_rand_path` all keep the word, so the sentence is true under either noun. Recorded so that the owner knows the choice is not evidenced. | none |
| S10 | NOTE | `instances/s5/s5_mixing.v:419` (ruling G9) | "This is the one spectral input of the S_5 path, and the only place the certificate tables are used." | The noun is right (the S_5 word analysis carries no program), and the twin `instances/pgl27/pgl27_spectral.v:537` says "the PGL(2,7) path", so the pair agrees. The manifest holds three S_5 paths, `s5_det_path`, `s5_rand_path` and `s5_word_path`, and only the last one uses this bound. The old sentence was ambiguous in the same way. | optional: "the S_5 word path" |
| S11 | NOTE | banners of the four AnalysisBridged files | `psl211_tableau_analysis_bridged.v:165` "The path as a program"; `:336` "The program"; `s5_tableau_analysis_bridged.v:160` "The randomized program"; `pgl27_tableau_analysis_bridged.v:353` "The two paths as programs"; `five_card_tableau_analysis_bridged.v:494` "The uniform program" | Rulings P4 and G1 give two of the four groups the form "the path as a program" while the other banners over the same kind of section name the program directly, and the psl211 file now carries both forms, at `:165` and `:336`, for its two published values. Every twin pair inside the index glosses agrees; this is the one family of sibling headings that does not. | optional: `:165` "The all-decks program", matching `s5:160` and `kim:494` |
| S12 | NOTE | layout | `psl211_tableau_analysis_bridged.v:193` and `s5_tableau_analysis_bridged.v:188` are a bare `    *)`; one-word last lines at `psl211_tableau_executable.v:34` and `s5_tableau_executable.v:27` ("files."), `psl211_tableau_sampled.v:22` ("in both.") | The re-flow pushed the closing delimiter onto its own line in the twin docstring "The certify statement the program wrote settles which arm that is." (the text line is exactly 80 bytes). The sheet asks for no orphan short line. The three checks-file `*)` at column 0 in `psl211_tableau_checks.v` predate the pass. | re-flow the two docstrings so the last text line ends "... that is. *)" |

## The ruled sentences (item 6)

| id | verdict |
|---|---|
| M1 `:9` | TRUE. Eleven `Definition ..._path : AnalysisPath` values, one per analysis path. |
| M2 `:852-854` | TRUE in content; see S8 for the residual reading. |
| M3 `:445` | TRUE: the Path 5 entry names `FiveCardAnalysis.endpoint_bound` and `deal_centi_lt` at `:403-404` and `:425-428`. Second place `:1026`: see S3. |
| M4 `:891` | TRUE. Consistent with `:893-897`, where paths state things in their missing-premise cell. |
| M5 `pgg_analysis_status.v:70` | TRUE, and it repairs a circular sentence. Matches the manifest at `:893-897`. |
| M6 `pgg_analysis_client.v:134` | TRUE. The manifest defines exactly eleven paths and the section now holds eleven `Check` lines, `:154-164`, with `pgl27_prior_exact_path` and `psl211_word_path` added. Not compiled here: the two added `Check` lines are code and need the client rebuilt. |
| M7 `pgg_tableau.v:251` | TRUE. `Record AnalysisPath` has exactly the five fields `ap_observed`, `ap_completion`, `ap_model`, `ap_transfer`, `ap_assumptions`. Small looseness, kept: the first field is the OBSERVED execution, and the third is a slot that may be empty below Sampled, though never at a published program. |
| M8 `pgg_tableau.v:4` | TRUE, and it agrees with the file's own first sentence at `:6`. |
| M9 `:2236-2240` | Applied: the bound variable is `p`, three occurrences, and no `row` token survives anywhere in the file (scan below). |
| P1 `psl211_tableau_analysis_bridged.v:378` | TRUE. `Lemma psl211_word_proximity_published_pathE : published_path psl211_word_proximity_published = psl211_word_path.` The pgl27 twin at `pgl27_tableau_analysis_bridged.v:805` carries the same sentence. |
| P2 `s5_tableau_observed.v:94` | Half right; see S4. |
| P3 `s5_tableau_sampled.v:21` | TRUE. `s5_word_path` appears in no `Published` value anywhere in the tree (the only s5 program is `s5_rand_published`), and the manifest's Path 8 reaches AnalysisBridged through `S5Analysis.exec_endpoint_bound`, a mixing theorem. |
| P4 banners | Applied; see S11. |
| R3 `s5_tableau_sampled.v:34` | TRUE. The Path 8 entry names an endpoint marginal bound against the encoder-image ideal and says at `:603-605` that this path "is observer-level and does NOT discharge" the cut-carrier premise. |

## Type honesty at the sites read (item 3)

No site now says a path proves, publishes, carries a certificate, an arm or a
witness, except the four discussed at S6 (which say the opposite, giving a
program coordinates it does have) and the two MUST rows. Sentences that were
already loose and stayed loose, none of them introduced by the pass: S2 and S5
above, and `pgg_tableau.v:938` "A published program at the program's own bound",
where the second "program" predates the pass and the two now read as one
repetition.

One further site was checked on this point and cleared.
`psl211_tableau_analysis_bridged.v:355` ends "all three stay true beside this
program. Its transfer status is IdealFinite", and a transfer status is a path
coordinate; the definition three lines below writes `|> publish IdealFinite
BaselineClassicalOnly`, so the program's own last line names it and the
possessive holds. The careful form is used twice in the same two files, "Its
last line publishes a path whose transfer status is StaticExecutedOnly"
(`:174` and `s5_tableau_analysis_bridged.v:164`). The manifest's sentence about
the same three refutations took the other noun, "Those refutations stay true
beside this path" (`pgg_analysis_manifest.v:860-861`), which is right there:
its subject is the manifest entry and not the program.

## Twin pairs (item 4)

Agreeing, checked pair by pair: the Algebraic header sentence and the "first
line of a program" banner; the "one edge of a program the surface cannot write"
sentence; the "first level at which a program proves anything" sentence; the
"this file for a payload, a published program or a path equation" sentence,
where the two senses sit in one line and each got its own word; the four index
glosses "== the X path as a program", "== the program publishes the manifest's
path", "== the program carries the exact arm", "== the program is the named
Sampled value ..."; the "descriptive path and the theorem proved about it cannot
drift apart" docstring; the "two spellings of the program's prefix" docstring;
the view-secrecy docstring; the "so the program and the model are named apart"
docstring; and the spectral-input pair (S10).

Disagreeing: S5 (`psl211_word_proximity.v:12` against the pgl27 and five-card
headers) and S11 (the section banners).

## The word left in place (item 5)

Word-boundary scan of all twenty-four files for the old noun: twenty
occurrences, every one a row of a matrix, of an interpreter trace, or of a
block table. Nothing in senses 1 to 3 was missed.

`pgg_analysis_manifest.v:282, 288` (executed seat row, input rows of the
trace); `psl211_analysis.v:112, 124, 125, 215` (interpreter rows, the
instance's row reader); `psl211_reading_constancy.v:374, 809` (a block line's
complement, the representative row of a code table); `s5_exec.v:86, 475, 476,
477, 486, 487` (verifier row, raw interpreter trace rows with their row
indices); `s5_mixing.v:29, 81, 143, 296, 382, 383` (row and column dominance,
a row of the letter table, a real row vector).

## Coverage

- 383 of 383 sites read with their old and new text, through the working-tree
  diff against c07f6a8 for all twenty-four files, so every changed line of the
  share was seen next to what it replaced. 130 of them were also read in the
  listing's three-line form.
- About 91 sites were read with the file open around them: the manifest header
  and tables (`:1-300`, `:705-900`, `:925-1044`, `:1060-1119`), the client's
  `Check` block, `pgg_tableau.v:923-960`, three passages of
  `pgg_tableau_syntax.v`, the header of `psl211_word_proximity.v`,
  `s5_exec.v:889-930`, `s5_mixing.v:404-425`,
  `protocol/pgg_functionality.v:119-150`, `s5_tableau_observed.v:5-45` and
  `:84-100`, and the declarations reached by the greps quoted above.
- Declarations opened to check a claim: `Record AnalysisPath`, `Record
  PublishedAt`, `Definition publish`, the eleven `..._path` definitions, the
  `Check` block of the client, `Lemma psl211_alldecks_published_pathE`, `Lemma
  psl211_word_proximity_published_pathE`, `Lemma s5_dealt_path_observedE`, and
  the `Published` values of the whole tree.
- Compiled nothing, wrote nothing but this file.
