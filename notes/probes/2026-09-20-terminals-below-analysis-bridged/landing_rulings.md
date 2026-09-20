# Main session's rulings on the audits of the landing (tracker 4.3)

## Naming and style audit (`audit-landing-naming.md`, B1 to B24)

Every finding is ACCEPTED with the auditor's replacement, except:

| id | Amendment |
|---|---|
| B6 | The auditor's replacement writes "the manifest's row for this program". The manifest's record is a PATH (owner's decision of 2026-09-20; the word the replacement uses was taken out of every comment that day). Landed sentence: "A reader of the value therefore holds the manifest's path for this program and the proof of run correctness in one term." |
| B7 | CODE, rename of a map this landing added: `transfer_of_sampled` -> `transfer_of_without_theorem` (four sites and the index entry, all in `manifest/pgg_tableau.v`; the fidelity file follows). |
| B8 | CODE, rename inside a recorded rejection: `s5_dealt_baseline_pathE` -> `s5_dealt_observed_published_baseline_pathE`; its message file in the probe directory is regenerated. |
| B24 | Cite the production uses in the sentence (`Tableau Observed` in `s5_tableau_observed.v`, `Tableau Sampled` in `s5_tableau_sampled.v`); no new probe file. |

## Soundness audit

`audit-landing-soundness.md` (A1 to A13): every finding ACCEPTED with the
auditor's replacement, merged with the naming audit where they meet:

| ids | Merged ruling |
|---|---|
| A1, B5, B6 | One docstring, `s5_dealt_observed_published_pathE`: "Three of its five coordinates are fixed by the terminal, the assumption status is the payload this file writes, and the fifth is the observed execution s5_dealt_path_observedE already identifies. A reader of the value therefore holds the manifest's path for this program and the proof of run correctness in one term. The equation holds only for the assumption status the program was published under, as the recorded rejection in s5_tableau_checks.v shows." (A1's own wording has a history word and a narrative verb; its content is kept.) |
| A2, B1 | B1's sentence (the paragraph's own verb "stays", no "still"), followed by "The count of nineteen is unchanged." |
| A3, B21 | "so a coercion added later out of either record into PublishedAt would turn each recorded rejection into an acceptance." |
| A13, B9 | B9's banner: it also covers the fourth rejection, which is about no reader. |
| A10 | Narrow the sentence to the bare spelling and name the parenthesised form, in one clause; no other change. |

