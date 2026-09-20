# The sixteen recorded rejections, re-checked after the rename

Tree: `feat/tableau-extensions-probe` with the rename applied and the 30-file
closure recompiled; `check_rename.py cca5e24` is ALL OK.

## Procedure

`fail_recheck.py` finds, in the four production files that hold them, every
`Fail` command whose text contains an identifier of `rename_map.tsv`, and for
each writes `fail_recheck/<basename>_<line>.v`: the production file from its
first line up to the line above the command, then the command with the word
`Fail` removed.  Each is compiled once, through the `rocq1` lock wrapper, with
the production flags of `_CoqProject` and `-o` into `fail_recheck/`, capped at
600 s:

    rocq1 600 8000 rocq compile <flags> -o fail_recheck/<slug>.vo fail_recheck/<slug>.v

so the context is the file's own and no production `.vo` is touched.  Sources,
`.vo` and per-command logs stay in `fail_recheck/`.  All sixteen exited
non-zero.  Rocq prints `Error:` alone on its first line and the message on the
next, so the column below gives the message, not that bare word.

## Table

| file:line | command's first line | rc | first error line | intended rejection? |
|---|---|---|---|---|
| instances/kim2025/tableau/five_card_tableau_checks.v:98 | `Fail Definition five_card_s5_family_sampled : Tableau Sampled :=` | 1 | The term "S5Analysis.rand_family" has type "AnalysisModelFamily s5_exec.s5_rand_observed" while it is expected to have type "FamPayload (tableau_at ...)" | yes. The comment says a family over one run does not sample another; the message is exactly that mismatch of observed executions. |
| instances/kim2025/tableau/five_card_tableau_checks.v:114 | `Fail Definition five_card_biased_sampled_at_manifest_level` | 1 | The term "five_card_biased_sampled" has type "Tableau Sampled" while it is expected to have type "Tableau (ap_completion five_card_biased_path)" | yes. The comment says the program reaches Sampled where the path records AnalysisBridged; the message is that level mismatch, and it now reads the renamed path. |
| instances/kim2025/tableau/five_card_tableau_checks.v:128 | `Fail Definition five_card_repeated_indistinguishability_published_uniform_pathE` | 1 | The term "erefl" has type "published_path five_card_repeated_indistinguishability_published = published_path five_card_repeated_indistinguishability_published" while it is expected to have type "... = five_card_uniform_path" | yes. The comment says a program written for another path is refused; the message is the refused conversion, with `published_path` in place of `published_row`. |
| instances/kim2025/tableau/five_card_tableau_checks.v:142 | `Fail Definition five_card_repeated_published39_unindexed` | 1 | In environment R : realType. The term "Order.POrderTheory.ltW (kim_centi_cert_eps_lt R tt)" has type "is_true (cert_eps (kim_centi_cert R tt) <= ...)" while it is expected to have type (the indexed obligation) | yes. The comment says a payload with no index binder is rejected; the message is the terminal's obligation failing for want of the binder. |
| instances/kim2025/tableau/five_card_tableau_checks.v:214 | `Fail Definition five_card_repeated_proximity : Tableau AnalysisBridged :=` | 1 | The term "kim_biased_proximity_cert" has type "forall (R : realType) (idx : unit), IdealProximityCert (amf_sample kim_biased_family R idx)" while it is expected to have type (the seven-cut model's) | yes. The comment says the seven-cut model's named value does not take the one-cut model's certificate; the message is that mismatch of families. |
| instances/pgl27/tableau/pgl27_tableau_checks.v:88 | `Fail Definition pgl27_exact_published_leak7 : Published :=` | 1 | The term "pgl27_exact_leak4" has type "ExactLeakAt 4 (tableau_at (pgl27_dealt sample pgl27_exact_family)) pgl27_exact_witness" while it is expected to have type (the same at 7) | yes. The comment says writing seven where the proof gives four fails on unification of the two sizes; the message is that unification failure. |
| instances/pgl27/tableau/pgl27_tableau_checks.v:102 | `Fail Definition pgl27_word_published_arm_neq (R : realType)` | 1 | In environment R, idx. The term "erefl" has type "security_arm_of pgl27_word_published R idx = ..." while it is expected to have type "... = ExactIndependenceArm" | yes. The comment says recording the word row at the exact arm is rejected by conversion; the message is that refused conversion. |
| instances/pgl27/tableau/pgl27_tableau_checks.v:155 | `Fail Definition pgl27_word_published39_unindexed : PublishedAt pgl27_bound39 :=` | 1 | In environment R : realType. The term "ssr_ext.eqW (pow2_split R)" has type "is_true (2 ^- 40 + 2 ^- 40 <= 2 ^- 39)" while it is expected to have type (the indexed obligation) | yes. Same intent as the kim entry at 142, and the same shape of failed obligation. |
| instances/pgl27/tableau/pgl27_tableau_checks.v:164 | `Fail Definition pgl27_word_published39_unindexed_bind` | 1 | In environment R : realType. The term "ssr_ext.eqW (pow2_split R)" has type "is_true (2 ^- 40 + 2 ^- 40 <= 2 ^- 39)" while it is expected to have type (the indexed obligation) | yes. The comment says the same rejection arrives through the bind; the message is the same failed obligation, so the surface is not what rejects it. |
| instances/pgl27/tableau/pgl27_tableau_checks.v:178 | `Fail Definition pgl27_word_published41 : PublishedAt pgl27_bound41 :=` | 1 | In environment R, a : amf_index (ab_f (tableau_at (pgl27_dealt sample pgl27_word_family certify InputIndistinguishability pgl27_word_cert))) R. The term "ssr_ext.eqW (pow2_split R)" has the 2^-39 bound where 2^-41 is expected | yes. The comment says the row at that number is rejected where its terminal is written; the message is the terminal's obligation failing at 2^-41. |
| instances/pgl27/tableau/pgl27_tableau_checks.v:196 | `Fail Definition pgl27_word_arm_is_not_exact (R : realType)` | 1 | In environment R, secretP, C, HC. The term "HC" has type "is_true (#\|C\| < 4)%N" while it is expected to have type (the second dealt secret) | yes. The comment says the word row expects two secrets before the threshold proof, so a threshold proof handed in the secret's position is refused; the message is that argument mismatch. |
| instances/psl211/tableau/psl211_tableau_checks.v:87 | `Fail Definition psl211_vm_reuse_sampled : Tableau Sampled :=` | 1 | The term "psl211_exact_family" has type "AnalysisModelFamily psl211_alldecks_observed" while it is expected to have type "FamPayload (tableau_at ...)" of the inline-reduction prefix | yes. The comment says the two prefixes hold different termination proofs, so no typed evidence crosses between their observed executions; the message is that mismatch. |
| manifest/pgg_analysis_manifest.v:2272 | `Fail Check (@MkAnalysisPath S5Analysis.observed Sampled None` | 1 | The term "None" has type "option ?A" while it is expected to have type "AnalysisModelSlot S5Analysis.observed Sampled" | yes. The banner says a Sampled path with no model witness must be a compile error; the message is the dependent slot refusing `None`, now under the renamed constructor. |
| manifest/pgg_analysis_manifest.v:2275 | `Fail Check (@MkAnalysisPath S5Analysis.observed Sampled tt` | 1 | The term "tt" has type "unit" while it is expected to have type "AnalysisModelSlot S5Analysis.observed Sampled" | yes. Same guard with the unit witness; the slot refuses it. |
| manifest/pgg_analysis_manifest.v:2278 | `Fail Check (@MkAnalysisPath S5Analysis.rand_observed AnalysisBridged None` | 1 | The term "None" has type "option ?A" while it is expected to have type "AnalysisModelSlot S5Analysis.rand_observed AnalysisBridged" | yes. The same guard at AnalysisBridged. |
| manifest/pgg_analysis_manifest.v:2281 | `Fail Check (@MkAnalysisPath S5Analysis.observed Sampled` | 1 | The term "PGL27Analysis.word_family" has type "AnalysisModelFamily pgl27_exec.pgl27_observed" while it is expected to have type "AnalysisModelSlot S5Analysis.observed Sampled" | yes. The banner's "family over the wrong execution" guard; the message is that mismatch of executions. |

## Negative scan

No log holds `was not found`, `already exists`, `Syntax error`, `Unbound`, or
any load-path complaint.  Every one of the sixteen is a type mismatch, a
refused conversion, a unification failure or a failed terminal obligation, all
inside the term.  So no recorded rejection has decayed into a rejection about
a missing name.

## Comparison with the messages recorded before the rename

The `verify.out` files of the tableau-directory probes keep only the verdict
("same rejection: Error:"), not the message text, so they cannot be compared
word by word.  Eight of the sixteen do have a stored full message, from the
earlier per-command runs in this session's scratch area
(`sbfail/nofail_<old name>.v.log` and `n16unfail_<old name>.log`).  Applying
`rename_map.tsv` to the stored text:

| now | stored under | verdict |
|---|---|---|
| five_card_tableau_checks_128 | n16unfail_five_card_row_repeated_indistinguishability_uniform_rowE | equal up to the map |
| five_card_tableau_checks_142 | sbfail/nofail_five_card_row_repeated39_unindexed | equal up to the map plus two earlier renames |
| five_card_tableau_checks_214 | sbfail/nofail_five_card_row_repeated_proximity | equal up to the map |
| pgl27_tableau_checks_102 | sbfail/nofail_pgl27_row_word_arm_neq | equal up to the map |
| pgl27_tableau_checks_155 | sbfail/nofail_pgl27_row_word39_unindexed | equal up to the map plus two earlier renames |
| pgl27_tableau_checks_164 | n16unfail_pgl27_row_word39_unindexed_bind | equal up to the map plus two earlier renames |
| pgl27_tableau_checks_178 | sbfail/nofail_pgl27_row_word41 | equal up to the map plus two earlier renames |
| pgl27_tableau_checks_196 | sbfail/nofail_pgl27_word_arm_is_not_exact | equal up to the map |

The stored logs predate two earlier campaigns, so four of them also carry the
older spellings `SpectralDecay` (now `InputIndistinguishability`) and
`pgl27_reprice39`, `pgl27_reprice41`, `five_card_reprice39` (now
`pgl27_bound39`, `pgl27_bound41`, `five_card_bound39`).  With those four
substitutions added, all eight messages are word-for-word equal to what the
commands print now.  Nothing else in any of the eight moved.

The other eight have no stored message: the four manifest guards were never
run through a per-command probe, and `five_card_s5_family_sampled`,
`five_card_biased_sampled_at_manifest_level`, `pgl27_exact_published_leak7` and
`psl211_vm_reuse_sampled` were checked by a verify script that kept the verdict
only.  For those the judgement above rests on the message against the comment
the file writes over the command, which is the same standard the probe scripts
applied.
