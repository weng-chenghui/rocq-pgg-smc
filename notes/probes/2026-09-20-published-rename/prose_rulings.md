# Main session's rulings on the sentences the prose agents listed

These sentences may change more than the noun; `check_prose.py` will report
them as OTHER CHANGE, and that list must equal this one.

## Group manifest

| id | Place | After the noun change | Ruling |
|---|---|---|---|
| M1 | `manifest/pgg_analysis_manifest.v:9` | "... and records one path per analysis path." | "... and records each analysis path as one typed value." |
| M2 | `manifest/pgg_analysis_manifest.v:852-854` | "The two paths differ in the model family and in the transfer status, and they carry different statements, Path 9 exact independence and this path a bound on the distance to that independent model." | "The two paths differ in the model family and in the transfer status, and the programs published over them prove different statements, Path 9's exact independence and this path's a bound on the distance to that independent model." (A path holds no proposition.) |
| M3 | `manifest/pgg_analysis_manifest.v:445` and the same sentence in the docstring of `five_card_repeated_path` | "endpoint_bound and deal_centi_lt stay in the path for what they are" | "endpoint_bound and deal_centi_lt stay named in the path for what they are" (the header: "Each path names ... its ... theorem"; a path stores none.) |
| M4 | `manifest/pgg_analysis_manifest.v:890` | "No path is filled with a dummy theorem, an option-valued proof, an axiom or a placeholder" | "No path names a dummy theorem, an option-valued proof, an axiom or a placeholder" |
| M5 | `manifest/pgg_analysis_status.v:70` | "... and the manifest path of such a path names the absent premise instead." | "... and a path with such a status names the absent premise instead." |
| M6 | `manifest/pgg_analysis_client.v:134` banner "The typed status vocabulary and the nine paths", with nine `Check` lines under it, while the header says one import reaches the eleven typed paths | true of the section, which lacks two checks | CODE: add `Check pgl27_prior_exact_path.` and `Check psl211_word_path.` after `Check psl211_alldecks_path.`; banner: "The typed status vocabulary and the eleven paths". Recompile the client. |
| M7 | `manifest/pgg_tableau.v:251` | "A published program's manifest path records the path the program ran and no theorem, so ..." | "A published program's manifest path records the execution, the level, the model family and the two statuses, and no theorem, so ..." (the five fields of `AnalysisPath`.) |
| M8 | `manifest/pgg_tableau.v:4` banner | "Tableau: the path program of one protocol instance" | "Tableau: an analysis path of one protocol instance as a program" |
| M9 | `manifest/pgg_analysis_manifest.v:2235` | the bound variable `row : AnalysisPath` in a `Check` | CODE: rename the bound variable to `p` (three occurrences in that one term). Not `path`: mathcomp's `path` is in scope. |

## Tree-wide ruling on the idiom "the X row as a program"

The framework header defines it: "A path of the analysis manifest is written
here as a program." So in "the all-decks row as a program", "the word row as a
program, published at 2^-40", "the randomized row as a program", the noun is
the manifest's entry: **path**. Every group is aligned to this in the fix pass.
A banner "The row program" becomes "The path as a program" (one word added).

## Group psl_s5_rest

| id | Place | After the noun change | Ruling |
|---|---|---|---|
| P1 | `instances/psl211/tableau/psl211_tableau_analysis_bridged.v`, docstring of `psl211_word_proximity_published_pathE` | "so the manifest's path for this path is a claim this equation discharges" | "so the manifest's path for this program is a claim this equation discharges" (the lemma: `published_path psl211_word_proximity_published = psl211_word_path`.) |
| P2 | `instances/s5/tableau/s5_tableau_observed.v`, docstring of `s5_dealt_path_observedE` | "which is the whole of what this path publishes" | "which is the whole of what this path records" (a path publishes nothing; the statement equates `ob_obs` of the program with `ap_observed s5_det_path`.) |
| P3 | `instances/s5/tableau/s5_tableau_sampled.v:21` | "the manifest's path over it, s5_word_path, is published from a mixing theorem rather than from a program" | "the manifest's path over it, s5_word_path, is justified by a mixing theorem and by no program" |
| P4 | banners "The row program" (`psl211_tableau_analysis_bridged.v:164` and siblings in other groups) | "The path program" | "The path as a program" |

Frozen, for the owner: `instances/psl211/psl211_exec.v:127` ("every arm of a
row over this algebra") and `:129` ("The rows' witness"), both the program
sense (`frozen_prose_occurrences.md`).

## Group pgl27

| id | Place | After the noun change | Ruling |
|---|---|---|---|
| G1 | `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:56` and the banner at 351 | "The two path programs" | "The two paths as programs" (the tree-wide idiom) |
| G2 | index entries 102, 103, 131 | "the exact path as a program", "the word path as a program", "the word path as a program at the proximity arm" | keep: the tree-wide ruling |
| G3 | `:804`, docstring of `pgl27_prior_exact_published_pathE` | "so the manifest's path for this path is a claim this equation discharges" | "so the manifest's path for this program is a claim this equation discharges" (as P1) |
| G4 | `:925`, docstring of `pgl27_word_proximity_published_pathE` | "The proximity program publishes the manifest's path for the word path, as ..." | "The proximity program publishes the manifest's word path, as ..." (the statement: `published_path pgl27_word_proximity_published = pgl27_word_path`) |
| G5 | `:51-53`, header | "The manifest carries no fourth path over this instance and publishes none of the three by a route this development's programs do not take." | "The manifest carries no fourth path over this instance, and none of the three is published by a route this development's programs do not take." (a manifest publishes nothing; a program publishes the manifest's path) |
| G6 | `instances/pgl27/pgl27_proximity.v:11` | "with no program and no published program in it" | "with no program in it, published or not" |
| G7 | `instances/pgl27/pgl27_proximity.v:42` | "The certificate itself, the program it publishes and the statements about them" | "The certificate itself, the program published over it and the statements about them" (a certificate publishes nothing) |
| G8 | `instances/pgl27/pgl27_word_privacy.v:89` | "the number a word program's spectral arm carries" | "the number a word program's input-indistinguishability arm carries" (the arm's name since bf42b4d; `pgl27_word_marginal_bound` is the `ic_b` of `pgl27_word_cert`: the prover confirms this before writing) |
| G9 | `instances/pgl27/pgl27_spectral.v:537`, docstring of `pgl27_rayleigh_Q2` | "the one spectral input of the PGL(2,7) program" | "the one spectral input of the PGL(2,7) path": its twin `instances/s5/s5_mixing.v:419` must say "path" (the S_5 word path has no program), and twins say one thing in one word |
| G10 | `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v`, docstring of `pgl27_word_proximity_published_pathE` | "so one manifest path carrying an input-indistinguishability program and a proximity program says nothing about ..." | "so one manifest path published by an input-indistinguishability program and by a proximity program says nothing about ..." (a path carries no program; as K4) |

## Group kim

The group wrote "the uniform program as a program" and "the repeated program's
certified program"; both are aligned to the tree-wide ruling: the noun before
"as a program" and before "'s certified program" is the manifest's entry.

| id | Place | After the noun change | Ruling |
|---|---|---|---|
| K1 | `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:85-88`, header | "A published program is a program, and an AnalysisPath holds descriptive metadata and no Prop, so two programs publishing one AnalysisPath say nothing about each other's claim." | "A published program carries its own theorem, and an AnalysisPath holds descriptive metadata and no Prop, so two programs publishing one AnalysisPath say nothing about each other's claim." (`published_thm` is a field of `PublishedAt`; `AnalysisPath` has no `Prop` field.) |
| K2 | same file, index glosses at about 149, 155, 158, 176 | "the uniform program as a program", "the repeated program as a program at the input- indistinguishability arm", "the one-cut program as a program at that same arm", "the one-cut program as a program at the proximity arm, published at one fiftieth" | "the uniform path as a program", "the repeated path as a program at the input-indistinguishability arm", "the one-cut path as a program at that same arm", "the one-cut path as a program at the proximity arm, published at one fiftieth" |
| K3 | same file, every "the repeated program's certified program" and "the one-cut program's certified program" (docstrings at about 681, 697, 710, 721, 735) and `five_card_tableau_checks.v:126` | | "the repeated path's certified program", "the one-cut path's certified program". At 681 the whole first sentence: "The repeated path's certified program publishes the manifest's repeated path." |
| K4 | same file, docstring of `five_card_biased_proximity_published_pathE` | "so one manifest path carrying an input-indistinguishability program and a proximity program says nothing about either claim" | "so one manifest path published by an input-indistinguishability program and by a proximity program says nothing about either claim" |
| K5 | `instances/kim2025/tableau/five_card_tableau_sampled.v:54` and `:219` | "Each of the two paths also carries a certified program that does reach AnalysisBridged"; "the biased path also carries a program that does reach AnalysisBridged" | "also has a certified program"; "also has a program" |
| K6 | `instances/kim2025/tableau/five_card_tableau_checks.v:19-21`, header | "The third is a path equation written for another path, the repeated certified program against the uniform path, which differ in two of their five fields." | "The third is a path equation written for another path, the repeated certified program's path against the uniform path, which differ in two of their five fields." |
| K7 | same file, `:125-129` | "The repeated program's certified program publishes the seven-cut model at IdealFinite and the uniform path holds the uniform family at StaticExecutedOnly, so the two paths differ in two of their five fields and the equation is refused." | "The repeated path, which the repeated certified program publishes, holds the seven-cut model at IdealFinite and the uniform path holds the uniform family at StaticExecutedOnly, so the two paths differ in two of their five fields and the equation is refused." |
| K8 | `instances/kim2025/five_card_proximity.v`, header | "with no program and no published program in it" | "with no program in it, published or not" (as G6; the same in `instances/psl211/psl211_word_proximity.v` if its header has the sentence) |
| K9 | same header | "The certificate itself, the program it publishes and the statements about them" | "The certificate itself, the program published over it and the statements about them" (as G7; the same in `psl211_word_proximity.v` if present) |
| K10 | `instances/kim2025/five_card_mixing.v:29-30`, header | "The manifest sits below the file that certifies those paths" | "The manifest sits below the file whose programs publish those paths" |
| K11 | layout, `five_card_tableau_analysis_bridged.v` at about 156, 228, 251 | a word split by a hyphen now sits inside a line ("input- indistinguishability", "thirty- ninth") | write the word whole ("input-indistinguishability", "thirty-ninth") and never split it across lines; re-flow the entry |

## Rulings on the audit of the five-card and PGL(2,7) share (`audit-prose-kim-pgl27.md`)

| id | Ruling |
|---|---|
| T1 | ACCEPTED, MUST. `instances/pgl27/pgl27_profile_privacy.v`, all 22 sites: the referent is neither a program nor a path (the file imports no tableau or manifest module; the objects are the laws `pgl27P` and `pgl27P_alldecks` with their view and secret). The noun is **analysis** ("the two PGL(2,7) analyses", "the exact analysis", "the all-decks analysis", "the analysis's orbit secret", "the function the analysis leaves implicit"). Not "model": the file's "the model" is the dealer model of `reconstruct/dealer_privacy.v`, and the two must stay apart. "analysis" is the tree's word already (`pgl27_algebraic_start`: "three analyses"). |
| T2 | ACCEPTED, MUST. `pgl27_tableau_analysis_bridged.v:357`: "Its last line publishes a path whose transfer status is StaticExecutedOnly" (the status is `ap_transfer`, a field of the path; both siblings say path). |
| T3 | ACCEPTED, MUST. `five_card_tableau_analysis_bridged.v:926-928`: "so an equation between two published paths says nothing about either certificate" (the lemma equates two `published_path` values). |
| T4 | ACCEPTED. `:1055`: "The branch publishes the manifest's own biased path."; index 286-287: "== the branch publishes the manifest's one-cut path". |
| T5 | ACCEPTED. `five_card_mixing.v:16-17`: "Those two are the base premises of the certificates Kim's one-cut and seven-cut programs carry." (the manifest records no certificate; the sibling `five_card_analysis.v:16` says programs). |
| T6 | ACCEPTED; it withdraws ruling K3's phrase. One value, one name: `five_card_repeated_indistinguishability_published` is "the repeated certified program" and `five_card_biased_indistinguishability_published` "the one-cut certified program" everywhere in `five_card_tableau_analysis_bridged.v`, `five_card_tableau_sampled.v`, `five_card_tableau_checks.v`; "the repeated program" and "the one-cut program" stay for the Sampled values `five_card_repeated_sampled`, `five_card_biased_sampled`. At 681: "The repeated certified program publishes the manifest's repeated path." The prover decides each site by the declaration it sits on and lists them. |
| T7 | ACCEPTED, and it replaces G9. `pgl27_spectral.v:537`: "the one spectral input of the PGL(2,7) word analysis"; twin `s5_mixing.v:419`: "the one spectral input of the S_5 word analysis". |
| T8 | RULED. `five_card_tableau_sampled.v:24-30`: the identifier rename made the paragraph false (both names end in `_sampled`). It becomes: "five_card_repeated_sampled, five_card_biased_sampled and five_card_uniform_sampled follow one naming scheme, and the five programs written out from the prefix are identified with these three values in five_card_tableau_analysis_bridged.v." The prover checks the count "five" against the `_sampledE` lemmas of that file and reports it. |
| T9 | ACCEPTED. Index entry of `five_card_biased_proximity_published`: "== the one-cut path as a program at the proximity arm, certified at one fiftieth" (no `conclude` line: the value is `Published`, and one fiftieth is its certificate's number). |

## Rulings on the audit of the manifest, PSL(2,11) and S_5 share (`audit-prose-manifest-psl-s5.md`)

| id | Ruling |
|---|---|
| S1 | ACCEPTED, MUST. `manifest/pgg_tableau_syntax.v:362-363`: "publish writes it unchanged into the path's ap_observed". |
| S2 | ACCEPTED, MUST. `manifest/pgg_tableau.v:928-929`, docstring of `PublishedAt`: "The manifest already records the descriptive path". |
| S3 | ACCEPTED. `manifest/pgg_analysis_manifest.v:1026`, docstring of `five_card_repeated_path`: "endpoint_bound and deal_centi_lt are listed for this path as endpoint marginal bounds: ..." (the rest of the sentence unchanged). |
| S4 | ACCEPTED. `instances/s5/tableau/s5_tableau_observed.v:94`: "which is the whole of what this path says about the run". |
| S5 | ACCEPTED. `instances/psl211/psl211_word_proximity.v:12`: "the program certified over it". |
| S6, S7, S9 | No change. |
| S8 | ACCEPTED. `manifest/pgg_analysis_manifest.v:852-854`: "... and the programs published over them prove different statements: exact independence over Path 9, and over this path a bound on the distance to that independent model." |
| S10 | Superseded by T7 ("the S_5 word analysis"). |
| S11 | ACCEPTED, one heading family: a section banner over finished programs reads "The <X> program(s)". `psl211_tableau_analysis_bridged.v:165`: "The all-decks program" (this replaces P4 there); `pgl27_tableau_analysis_bridged.v` banner at about 353 and the header line at about 56 that quotes it: "The exact and the word program" (this replaces G1). The prover lists every other banner of the four analysis-bridged files so the family can be read in one place. |
| S12 | ACCEPTED. Re-flow the five docstrings so no closing delimiter and no single word stands alone on the last line. |
