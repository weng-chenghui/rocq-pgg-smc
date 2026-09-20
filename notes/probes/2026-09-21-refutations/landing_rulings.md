# Rulings on the audit of the obstruction landing (2026-09-21)

Audit: `audit-landing.md` in this directory (one combined Opus audit, verdict
GO after six comment corrections). Rulings by the main session, each
replacement checked against the declaration it sits on. Every change is a
comment, except G10, which adds one `Check` to `landing_fidelity.v`.

Facts checked before ruling:

- `manifest/pgg_tableau.v` has six definitions over a `PublishedAt c`; five
  project out of `published_thm`, and `security_property_of` reads
  `ab_security_property (published_at r) R idx` instead. G1 is right.
- `profile_k_gt0` (`manifest/pgg_tableau_security_property_relations.v`)
  proves `0 < profile_k (instance_profile A)` at every algebra, so the empty
  coalition is below every threshold. The auditor's G2 replacement keeps a
  condition ("a coalition below the threshold") that always holds; the ruled
  sentence drops it and keeps the one condition that can fail, an inhabited
  run-argument type.
- `psl211_alldecks_path` is `MkAnalysisPath PSL211Analysis.observed
  AnalysisBridged PSL211Analysis.exact_family StaticExecutedOnly
  BaselineClassicalOnly`. G4 is right; the auditor's sentence is reworded.

| id | ruling | the text to land |
|----|--------|------------------|
| G1 | ACCEPT, auditor's three sentences as written | `manifest/pgg_tableau.v`, docstring of `obstruction_of`: "It is the whole of what such a value says beyond the Sampled level: every reader of this file that names a security statement or a security property takes a PublishedAt, and PublishedObstruction is a different inductive type, so none of them applies to a value of it." `psl211_tableau_analysis_bridged.v`, docstring of the published obstruction: "It certifies no security property: its data carries no SecurityEvidence, and every reader of manifest/pgg_tableau.v that names one takes a PublishedAt, a different inductive type." `psl211_tableau_checks.v` header: "The fourth is which readers reach a published obstruction. The readers of manifest/pgg_tableau.v that name a security statement or a security property all take a PublishedAt, and PublishedObstruction is a different inductive type with no coercion into it, so none of them applies; the two terms below are the two spellings that were checked." |
| G2 | ACCEPT, AMENDED | Replace the last sentence of the `ObstructionKind` comment ("The one member carries the number ... var_dist being non-negative.") by: "The one member carries the number the model is distinguishable at, and neither this enumeration nor the terminal below constrains its sign. At a number at or below zero the inequality is free, var_dist being non-negative, and the empty coalition is below every threshold, so the member's proposition then holds at every model whose run-argument type is inhabited. It compares two readings of the model only at a positive number." |
| G11 | ACCEPT | Header of `psl211_tableau_analysis_bridged.v`: "Two programs with security evidence are published here and they part at the model." Docstring of `psl211_word_proximity_published_sampledE`: "...so the two programs with security evidence are each written once above the model they branch at." |
| G3 | ACCEPT | "(* The message is the one above, word for word, at the same argument. *)" |
| G4 | ACCEPT, REWORDED | Header of `psl211_tableau_analysis_bridged.v`, last sentence of the paragraph: "It certifies no security property, and its path records NegativeTransfer where psl211_alldecks_path, over the same model, records StaticExecutedOnly." |
| G12 | ACCEPT | "The assumption status is the line's payload, as it is at the two terminals below AnalysisBridged." |
| G5 | ACCEPT | "That reader is the second conjunct of the third field of a PublishedAt, and a published obstruction is ..." (rest of the sentence unchanged). |
| G6 | ACCEPT | "The family is downward closed in c, so the sharpest statement one coalition and one pair of run arguments support is the one at the distance between their two readings." |
| G7 | NO CHANGE | The two readers mirror `run_correct_of_sampled` and `view_identification_of_sampled`; kept by the existing pattern. Recorded in the reminder to the owner as a possible prune, both pairs together. |
| G8 | ACCEPT | "...conditional entropy, mutual information or endpoint marginal mixing, none of which labels a limitation" |
| G9 | ACCEPT | "Obstruction sits in the same position, measured on 2026-09-21 in the same way: ..." (rest unchanged). |
| G10 | ACCEPT | Add to `landing_fidelity.v`, before the constructor's `Check`: `Check (@ObstructionKind : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A), SampleAdapter R (instance_exec E) -> Type).` |

Layout duties for the fix pass: boxed header lines stay exactly 80 bytes with a
space before the closing marker; no line over 80 bytes; reflow the paragraph a
sentence sits in, nothing else. No code token changes outside
`landing_fidelity.v`.
