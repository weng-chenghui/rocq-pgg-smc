# Renamed identifiers of 2026-09-19

Every identifier and file renamed in production on 2026-09-19, for whoever
updates text that cites the code. No `.tex` file was edited by these commits.

Commits: bf42b4d (the arm), dc1321e (comments only), 7bae082 (the abbreviated
names and the file name). Reason for all of them: the arm's old name was a proof
method and its certificate holds no spectral gap; the word "indistinguishability"
is never abbreviated in an identifier.

## 1. What the paper sources cite (the only lines to change)

A scan of `paper/`, `paper-wadt2026/`, `paper-wadt2026-baseline-application/`,
`blueprint/`, `docs/` and `README.md` for every old name of sections 2 to 4,
with and without the LaTeX escape `\_`, finds two names and nothing else:

| Old, as written in LaTeX | New, as written in LaTeX |
|---|---|
| `pgl27\_word\_view\_indist` | `pgl27\_word\_view\_indistinguishability` |
| `pgl27\_word\_trace\_indist` | `pgl27\_word\_trace\_indistinguishability` |

Neither old name is a prefix of another cited name, so a whole-file replace of
each string is safe in these files.

| File | Lines | Which name |
|---|---|---|
| `paper-wadt2026/main.tex` | 134, 1708 | view |
| `paper-wadt2026/main.tex` | 135, 1709 | trace |
| `paper-wadt2026/main.tex` | 1639 | both |
| `paper-wadt2026/analysis/shinagawa21-paragraph-baseline.tex` | 5015 | view |
| `paper-wadt2026/analysis/shinagawa21-paragraph-baseline.tex` | 5016 | trace |
| `paper-wadt2026/analysis/shinagawa21-paragraph-baseline.tex` | 5019, 5022 | both |
| `paper-wadt2026-baseline-application/candidate-main.tex` | 145 | view |
| `paper-wadt2026-baseline-application/candidate-main.tex` | 146 | trace |
| `paper-wadt2026-baseline-application/candidate-main.tex` | 1700, 1762 | both |

One non-paper document also cites the old name and is a dated record, left as
it is: `docs/style/scan-2026-08-26/P0-P1-CLOSEOUT.md` line 172
(`pgl27_word_view_indist`).

Both lemmas are declared in `instances/pgl27/pgl27_word_privacy.v`; their
statements are unchanged.

## 2. The Tableau arm (commit bf42b4d)

Declared in `manifest/pgg_tableau.v` unless another file is named.

| Old | New |
|---|---|
| `SpectralDecay` (constructor of `SecurityPort`, and the keyword after `certify`) | `InputIndistinguishability` |
| `SpectralCert` | `IndistinguishabilityCert` |
| `MkSpectralCert` | `MkIndistinguishabilityCert` |
| `sc_b`, `sc_Hd`, `sc_ideal`, `sc_close`, `sc_const` | `ic_b`, `ic_Hd`, `ic_ideal`, `ic_close`, `ic_const` |
| `SpectralPayload` | `IndistinguishabilityPayload` |
| `SpectralPropAt` | `IndistinguishabilityPropAt` |
| `certify_spectral` | `certify_indistinguishability` |
| `spectral_tail` | `indistinguishability_tail` |
| `view_indist_of` | `view_indistinguishability_of` |
| `mk_spectral` (`manifest/pgg_tableau_syntax.v`) | `mk_indistinguishability` |
| `spectral_cert_reading_constancy` (`instances/psl211/psl211_reading_constancy.v`) | `indistinguishability_cert_reading_constancy` |

In `instances/kim2025/five_card_rows.v`:

| Old | New |
|---|---|
| `five_card_row_biased_spectral_tableau` | `five_card_row_biased_indistinguishability_tableau` |
| `five_card_row_biased_spectral_rowE` | `five_card_row_biased_indistinguishability_rowE` |
| `five_card_row_biased_spectral_publishedE` | `five_card_row_biased_indistinguishability_publishedE` |
| `five_card_row_repeated_spectral_tableau` | `five_card_row_repeated_indistinguishability_tableau` |
| `five_card_row_repeated_spectral_rowE` | `five_card_row_repeated_indistinguishability_rowE` |
| `five_card_row_repeated_spectral_publishedE` | `five_card_row_repeated_indistinguishability_publishedE` |
| `five_card_row_repeated_spectral_uniform_rowE` (a recorded `Fail`) | `five_card_row_repeated_indistinguishability_uniform_rowE` |

Not renamed, because the word names a real spectral-gap or convergence result:
`kim_spectral_gap`, `kim_spectral_gap_le1`, `kim_spectral_gap_pos`,
`kim_spectral_convergence`, `pgl27_spectral_*`, `s5_spectral_*`,
`den_boer_eps0_spectral`, `eps_spectral`, `sa_spectral_gap`,
`SpectralCertificate` with its fields `sc_convergence`, `sc_lambda_gap`,
`sc_lambda_le1`, `sc_lambda_pos`, and the file `instances/pgl27/pgl27_spectral.v`.

## 3. The abbreviated names (commit 7bae082)

The rule is one substitution: the segment `indist` becomes
`indistinguishability`.

| Old | New | Declared in |
|---|---|---|
| `pgl27_word_view_indist` | `pgl27_word_view_indistinguishability` | `instances/pgl27/pgl27_word_privacy.v` |
| `pgl27_word_trace_indist` | `pgl27_word_trace_indistinguishability` | `instances/pgl27/pgl27_word_privacy.v` |
| `pgl27_word_view_indist_restated` | `pgl27_word_view_indistinguishability_restated` | `instances/pgl27/pgl27_rows.v` |
| `pgl27_word_view_indist_via_transfer` | `pgl27_word_view_indistinguishability_via_transfer` | `instances/pgl27/pgl27_models.v` |
| `pgl27_exec_view_indist` | `pgl27_exec_view_indistinguishability` | `instances/pgl27/pgl27_models.v` |
| `pgl27_exec_trace_indist` | `pgl27_exec_trace_indistinguishability` | `instances/pgl27/pgl27_models.v` |
| `kim_centi_static_obs_indist` | `kim_centi_static_obs_indistinguishability` | `instances/kim2025/five_card_mixing.v` |
| `kim_biased_static_obs_indist` | `kim_biased_static_obs_indistinguishability` | `instances/kim2025/five_card_mixing.v` |
| `word_view_indist`, `word_trace_indist`, `word_view_indist_via_transfer`, `exec_view_indist`, `exec_trace_indist` | the same with `indistinguishability` | aliases of module `PGL27Analysis`, `instances/pgl27/pgl27_analysis.v` |
| `centi_static_obs_indist`, `biased_static_obs_indist` | the same with `indistinguishability` | aliases in `instances/kim2025/five_card_analysis.v` |

The last two rows are also the spellings that `manifest/pgg_analysis_manifest.v`
and `manifest/pgg_analysis_client.v` print in their tables.

## 4. The file

| Old | New |
|---|---|
| `instances/psl211/psl211_spectral_constancy.v` | `instances/psl211/psl211_reading_constancy.v` |

Logical name `pgg_smc.psl211_reading_constancy`. Its declarations keep their
names except the one listed in section 2.

## 5. Names that exist only in the extensions probe

`notes/probes/2026-09-19-tableau-extensions/` is being brought to the same
names (tracker step 0.5). Those names are in no production file and in no paper
source; they reach production at the landing of the extensions, already under
the new spelling: `InputIndistinguishabilityArm`,
`certify_indistinguishability_armE`, `indistinguishability_prop_cert_free`,
`five_card_biased_indistinguishability_implies_proximity`.

## How the list was checked

Sections 2 to 4 are the maps the rename scripts applied; after each commit a
script confirmed that comment-stripped code is token-identical to the previous
commit under the map, and a tree-wide scan of `.v` files and `_CoqProject`
outside `notes/` and `docs/` found no old name left. Section 1 is the output of
a scan run on 2026-09-19 at commit 7bae082.
