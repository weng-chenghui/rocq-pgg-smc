# Naming, style and record audit of stage D

2026-09-19. Opus auditor, independent of the prover: I did not write stage D and
checked every claim below against the code.

Object: the frozen export of `notes/probes/2026-09-19-tableau-extensions` at
commit `0a4f4f4`, files `p6_psl211_word_model.v`, `p6_psl211_word_proximity.v`,
`p6_mutations.v`, `assumptions_report_stageD.v`, `STATUS-stageD.md` and the four
`_CoqProject` lines. Compiles ran against the main session's stage D build with
the production flags and `-Q <build dir> tableau_ext_probe` last, under
`rocq1 600 8000 rocq compile -time`. `psl211_endpoints.v` was never touched, no
production file was rebuilt, and no `vm_compute`, `compute` or `simpl` was run.

## Verdict

**GO**, with two SHOULD items that touch what a reader is told a lemma proves
(D2, D5) and one that adds a compiled lemma (D3). Nothing found blocks the
stage: every declaration is correctly named, no name collides with production or
with stages A-C, no banned word appears, no `.v` line exceeds 80 bytes, the
`_CoqProject` order is a dependency order, and no permanent file imports the
probe.

## Findings

| ID | Class | Site | Claim | Evidence | Checked replacement |
|---|---|---|---|---|---|
| D1 | SHOULD | `p6_psl211_word_model.v:27` | Header gloss `psl211_wordP == the law of the word model, decks times words` is type-dishonest: the second factor is a law on group elements, not on words. | `psl211_wordP : R.-fdist (psl211_inputT * pgg_gT psl211_M)` (line 79); its second factor is `psl211_word_cutP R : R.-fdist (pgg_gT psl211_M)` (line 71). The body comment at line 74 already says "the cut". | `(*   psl211_wordP         == the law of the word model, decks times cuts      *)` — 80 bytes, measured. |
| D2 | SHOULD | `p6_psl211_word_proximity.v:205-209`, repeated at `STATUS-stageD.md:212-215` | "the reading of a coalition below the threshold is not constant in the run argument, which `psl211_alldecks_constancy_false` and `psl211_dealt_constancy_false` ... refute" states a proposition the two lemmas do not refute. | `coalition_reading_constancy` (`instances/psl211/psl211_spectral_constancy.v:192-199`) asserts `fdistmap (static_coalition_obs C x) ideal = fdistmap (static_coalition_obs C x') ideal`, an equality of two pushforward **laws**, not constancy of a reading. Both lemmas (`:258-260`, `:953-955`) refute it at the single ideal `` `U psl211_G_pos ``, and `psl211_dealt_constancy_false`'s own comment says "The statement rules out one named ideal and no certificate". | Production `instances/psl211/psl211_rows.v:40-42` already carries the right wording; follow it: "...is not a statement at a fixed deck description: a coalition below the threshold does not read the group-uniform cut the same way at every run argument, which `psl211_alldecks_constancy_false` and `psl211_dealt_constancy_false` of `psl211_spectral_constancy.v` establish in the two run modes, and those refutations stay true beside this row." |
| D3 | SHOULD | `p6_psl211_word_proximity.v:227-231` | The comment on `..._publishedE` gives as its reason that an `AnalysisPathRow` records the model family and this family is new, but the lemma pins three status coordinates and says nothing about `apr_model`. It also points at "the row below" while the row is defined above, at line 212. | `MkAnalysisPathRow` has five fields (`manifest/pgg_analysis_manifest.v:773-791`); the lemma states `apr_completion`, `apr_transfer`, `apr_assumptions` only. Stage C withdrew its `_publishedE` for a full `_rowE` (`p5_pgl27_word_proximity.v:295-297`); p4 keeps both (`p4_kim_biased_proximity.v:279`, `:284`). | Add, beside or in place of `_publishedE`, the full-row equation. **Compiled, rc=0**, `exact: erefl` at 0.001 s and `Qed.` at 0.000 s (`extD_naming/t1_rowE.v`): `Lemma psl211_row_word_proximity_rowE : published_row psl211_row_word_proximity = @MkAnalysisPathRow psl211_alldecks_observed AnalysisBridged psl211_word_family IdealFinite BaselineClassicalOnly. Proof. exact: erefl. Qed.` This is the statement the comment's reason actually asserts. |
| D4 | SHOULD | `p6_mutations.v:64` | `psl211_word_law_le2` is a `Definition` whose type is a proposition. | A scan of every `.v` file under the production `_CoqProject` roots plus the whole probe finds no other `Definition` whose type is a `var_dist` inequality; the tree uses `Lemma`/`Fact` throughout. | `Lemma psl211_word_law_le2 (R : realType) : var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2%:R. Proof. exact: var_dist_le2. Qed.` — **compiled, rc=0** (`extD_naming/t3_lemma_le2.v`). The header gloss at line 22 needs no change. |
| D5 | SHOULD | `STATUS-stageD.md:307-309` | "every one of them mentions an fdist record, and an fdist record carries the three boolp constants" is false for two of the 21 prints. | `psl211_pow2_40_ge1 : (1:R) <= 2%:R^+40` and `psl211_pow2_40_gt0` mention no fdist record, yet blocks 12 and 13 of the report print the same three constants. Probe `extD_naming/t2_realtype.v`, importing `mathcomp ... reals` only and no infotheo, proves the same `Fact` and prints all three: the carrier is `realType`, not `fdist`. | "No declaration printed `Closed under the global context`, which is expected: every one of them is stated at a `realType`, and mathcomp-analysis builds that structure with the three boolp constants. A `Fact` about `2%:R^+40` alone, requiring no infotheo file, prints the same three." |
| D6 | SHOULD | `STATUS-stageD.md:283-286` | "a print on anything that mentions the twelve-card probability model ... costs about 22 s" is false. | From the main session's own `-time` log: `psl211_wordP` 0.056 s, `psl211_word_sample` 0.119 s, `psl211_word_cut_distE` 0.115 s, `psl211_word_lawE` 0.221 s, `psl211_word_proximity_close` 0.266 s, `psl211_word_law_le2` 0.056 s. The 22 s band starts at `psl211_word_family`, the first declaration whose type names `psl211_alldecks_observed`. | "The split follows whether the declaration reaches the observed execution. A print on a real field alone, such as `psl211_pow2_40_gt0`, and a print on the two models' laws, such as `psl211_wordP` and `psl211_word_lawE`, stay under 0.3 s; a print on anything whose type names `psl211_alldecks_observed`, which `psl211_word_family` and every row lemma does, traverses the instance's interpreter tables and costs about 22 s." |
| D7 | SHOULD | `STATUS-stageD.md:369-371` | "`ExactWitness` and `IdealProximityCert` are records of the manifest layer" is false today for `IdealProximityCert`. | `manifest/pgg_tableau.v:114` declares `Record ExactWitness`; the file contains zero occurrences of `IdealProximity`. `Record IdealProximityCert` exists only in the probe's framework copy, `pgg_tableau.v:184`. | "...for the reason that file's header already gives for `ExactWitness`: a record of the manifest layer, which an instance file cannot import without closing a cycle through the analysis manifest. `IdealProximityCert` is not in `manifest/pgg_tableau.v` today, so the landing of the arm itself puts it there first." |
| D8 | SHOULD | `STATUS-stageD.md:358-365` | The D1 recommendation does not record that landing `psl211_word_sample` falsifies a reason written into a production comment. | `psl211_alldecks_constancy_false_word584`'s comment (`instances/psl211/psl211_spectral_constancy.v:765-768`) says it is stated on the cut law "because no weighted-word SampleAdapter exists in this tree, so there is no adapter whose cut is this law and no `sc_Hd` through which a certificate's ideal could be held near it". `psl211_word_sample` is exactly that adapter. | Add one sentence to the recommendation: "Landing `psl211_word_sample` makes the reason `psl211_alldecks_constancy_false_word584` gives for being stated on the cut law, that no weighted-word `SampleAdapter` exists in this tree, no longer true, so that comment is rewritten in the same landing." `psl211_spectral_constancy`'s reverse closure is empty, so the edit rebuilds nothing. |
| D9 | NOTE | `p6_psl211_word_proximity.v:174,178` | `psl211_pow2_40_ge1` / `psl211_pow2_40_gt0` carry an instance prefix for a fact with no instance content; stage C names the same two `pow2_40_ge1` / `pow2_40_gt0` (`p5_pgl27_word_proximity.v:239,243`). | The statements are `(1:R) <= 2%:R^+40` and `(0:R) < 2%:R^+40`. | The prefix is forced: G1 bars stage D from editing stage A's `p1_joint_law_distance.v`, where the pair belongs, and p6 does not import p5. Keep the names and record the reason in `STATUS-stageD.md`, so a landing merges the two copies into one unprefixed pair rather than landing both. |
| D10 | NOTE | `p6_psl211_word_model.v:77` | "a coalition reads a deck laid by the same dealer under a different shuffle" uses "dealer" for the person performing the word shuffle, while at this instance "dealer" also names the dealer-dealt run mode (`psl211_dealt_params`, `psl211_dealer_view`, `psl211_dealt_constancy_false`), which the same stage cites. | `instances/psl211/psl211_spectral_constancy.v:787` heads that mode "The dealer-dealt mode, where the run argument is the secret". The second sense is inherited from `psl211_mixing.v:543`, so the ambiguity is not stage D's invention. | "so a coalition reads a deck drawn from the same law under a different shuffle." |
| D11 | NOTE | `p6_psl211_word_proximity.v:27-29` | "the constancy field a spectral certificate would need being refuted at it" over-claims in the compressed header form. | Both refutations rule out one named ideal; what holds of an arbitrary certificate is `psl211_alldecks_no_small_eps_cert`. `STATUS-stageD.md:38-50` states this correctly. | "...the constancy field a spectral certificate would need being refuted at the group-uniform ideal in both run modes, and every certificate's shuffle bound held at or above 1/1320." |
| D12 | NOTE | `p6_psl211_word_model.v:69-70` | "`psl211_word_mixing` is the whole price of the departure" names a lemma as a number. | `psl211_word_mixing` (`instances/psl211/psl211_mixing.v:545-548`) is a variation-distance bound; the price is `2^-40`. Its own comment says "at a cost of 2^-40". | "...and 2^-40, the bound `psl211_word_mixing` proves, is the whole price of the departure." |
| D13 | NOTE | `p6_psl211_word_proximity.v:120` | The proof comment names "p1", a probe file that dangles after a landing. | `p1_joint_law_distance.v` is probe-local; `STATUS-stageD.md:373-379` says its two lemmas move to `lib/var_dist_supp.v`. | Name the lemma instead: "so `var_dist_fdistmap_pair` applies with no pointwise rewriting of either reader." |
| D14 | NOTE | `assumptions_report_stageD.v:32,41,54,57` | Section comments are 21, 44, 21 and 51 bytes; `assumptions_report_stageC.v:30,39,59` pads its three to 80. | Stage A's and stage B's reports leave theirs unpadded (34-78 bytes), so the tree is split two against two. | Either pad these four to 80 or record that the report files follow stage A's convention. Coordinator's call. |
| D15 | NOTE | `STATUS-stageD.md:4` | Records HEAD `ceb2317`, which is stage B fix pass 1. | Stage D is commit `0a4f4f4`, whose parent is `df6ebfb`, stage C fix pass 1. The concurrency is explained at `:396-402`, but the header line is stale. | "Repository `rocq-pgg-smc`, stage D written at `ceb2317` and committed at `0a4f4f4`, branch `feat/tableau-extensions-probe`." |
| D16 | NOTE | `STATUS-stageD.md:282-283` | "the other ten are between 0.01 s and 0.06 s". | The main session's independent rebuild puts three of the ten at 0.115, 0.221 and 0.266 s. Different runs, so the record is not wrong about its own run, only narrow. | "the other ten are under 0.3 s." |
| D17 | NOTE | `STATUS-stageD.md:360` | The proposed permanent name `instances/psl211/psl211_word_model.v` sits one plural away from `instances/psl211/psl211_models.v`. | The sibling instance avoids this: `instances/pgl27/` holds both `pgl27_models.v` and `pgl27_word_privacy.v`, reusing no stem. | The `<instance>_word_<topic>.v` shape is the established precedent, so the name is admissible; flagging only the adjacency. No rename proposed. |

## Renames

None. Every stage D declaration name is admissible as written, so the rename
table is empty. D4 changes a keyword, not a name; D9 records a reason for a
prefix rather than removing it.

## What checked out

Names. Nineteen declarations, all `psl211_`-prefixed, subject first and
coordinate last, no project-local abbreviation, no narrative or metaphor word.
Checked against every `Definition`, `Lemma`, `Theorem`, `Fact`, `Record`,
`Notation` and constructor in all 198 production `.v` files and in stages A-C
by script: **no collision**. `psl211_word_cut_distE` sits correctly beside
production `psl211_alldecks_cut_distE` (`psl211_models.v:250`), `psl211_wordP`
beside `psl211_alldecksP` (`:200`), `psl211_word_family` beside
`psl211_exact_family` (`:516`, same `(fun _ => unit)` index and the same gloss
wording), `psl211_word_sampleP_E` beside `psl211_alldecks_sampleP_E` (`:230`).
`psl211_word_proximity_cert_idealE` matches stage C's
`pgl27_word_proximity_cert_idealE` exactly; p4's shorter `kim_biased_cert_idealE`
is the outlier. `_armE` matches all three siblings.

"Word" at PSL(2,11). Production already uses it for the generator word and its
cut law (`psl211_word_mixing`, `psl211_word_perm`,
`psl211_alldecks_constancy_false_word584`). Stage D's `psl211_word_*` reads in
that same sense throughout. No meaning collision.

One word per concept. "Deck description" is the whole run argument and "deal"
its three non-secret coordinates, consistently in both p6 files and in the
STATUS; "reading" for the coalition's observation; "the number" for the
certificate's eps; "sum of absolute differences" for `var_dist` with no
appearance of the two-character token for a distance; "at most five of the
twelve seats" everywhere, no stray count. Banned vocabulary: **zero hits** for
apex, gate/gates/gated/gating, posit/posits/posited/positing across all five
stage D files.

Type honesty. "a distinguisher's advantage is therefore at most half of it"
(`:204`) is right: `var_dist` is twice the total variation distance, so the
advantage is at most `2^-41`. The `Fail` comments say "A rejection is of one
written term and is no proof that no term exists" (`p6_mutations.v:16`). Both
recorded `Fail`s exist and both are in the STATUS; the file has exactly two.

Layout. No `.v` line over 80 bytes, every boxed banner exactly 80, no tab, no
trailing whitespace. Header indexes list every declaration in both p6 files
(7 and 11) with glosses that match the statements, D1 excepted. `_CoqProject`
order is a dependency order, verified by script over the `Require` lines. No
permanent `.v` file anywhere in the tree mentions `tableau_ext_probe`.

STATUS as a record. Every back-quoted Rocq identifier resolves, split at dots,
against production plus the frozen probe plus infotheo plus mathcomp; the only
unresolved tokens are Rocq keywords, the commit hash, `psl211_word_secret`
(explicitly marked as not defined) and the proposed file name (marked as
proposed). No line number of itself. Numbers recomputed independently:
`2^-40 = 1/1099511627776`, decimal `9.094947017729282379150390625e-13`,
`2^-41 = 4.5474735088646411895751953125e-13`, `2*132*720*720 = 136857600`, and
"about 4.5e-13 of the ceiling" since the ceiling is two. The paraphrase of
`psl211_alldecks_no_small_eps_cert` as "excludes every shuffle bound strictly
below 1/1320" **is accurate**: the landed statement refutes
`eps + eps < (#|pgg_G psl211_M|)^-1 = 1/660`, which is `eps < 1/1320`, and the
production comment at `:685-686` says the same. Compile table plausible against
the main session's rebuild: 38, 67, 29 and 31 sentences, sums 4.120, 4.872,
4.175 and 247.570 s, 21 `Axioms:` blocks, zero `Closed under`, eleven prints
over five seconds.

D1/D2 closures recomputed by my own Python over the `Require` lines of all files
under the production `_CoqProject` roots: forward closure of `psl211_endpoints`
**34**, member for member the list at `:326-333`; reverse closure of
`psl211_models` **10**, member for member the list at `:349-351`; reverse closure
of `lib/var_dist_supp.v` **11**, not containing `psl211_endpoints`; reverse
closure of `psl211_mixing` **1**; of `psl211_spectral_constancy` and of
`instances/psl211/psl211_rows.v` **0**. Five production sites spot-checked by
line: `lib/var_dist_supp.v:51` (`var_dist_le2`),
`instances/pgl27/pgl27_mixing.v:1077` and `instances/psl211/psl211_mixing.v:577`
(both `Local Lemma var_dist_prodR`, the two a promotion would meet),
`instances/psl211/psl211_models.v:516` (`psl211_exact_family`) and
`instances/psl211/psl211_rows.v:171` (`psl211_exact_witness`). `fdist_prod_snd`
has no infotheo counterpart: infotheo's only such lemma is
`probability/fdist.v:1040`, `fdist_prod1`, the first marginal.

Monad. No stage D file mentions a monad, graded or parameterised, so nothing
contradicts the hand-back's "parameterised monad indexed by pre- and
post-completion level, not graded".

## What I did not check

Soundness of the proofs: whether `psl211_word_lawE`'s `var_dist_prodR` step is
the right decomposition, and whether `var_dist_fdistmap_pair` is applicable at
the two readers, are for the soundness auditor. I did not rerun
`assumptions_report_stageD.v` (248 s) and read its axiom blocks from the main
session's log instead. I did not compile any production file, did not run
`make`, and did not open `psl211_endpoints.v`. I did not audit stages A, B or C
beyond the parallelism comparisons named above, and I did not re-raise the
`IdealProximity*` / `certify_idealproximity` / `ipc_*` name lengths, which the
coordinator has already decided to keep. I did not verify the STATUS's account
of the brief's own wording, having no copy of the brief. Whether the stage C fix
pass now running in the live directory has changed the `p5_*` files I compared
against, I did not check: I read the frozen export only.
