# Soundness audit of stage D — the PSL(2,11) word model and its proximity row

2026-09-19. Opus auditor, independent of the prover who wrote stage D and of
the stage A, B and C auditors. Object: the frozen export at
`<scratchpad>/extD_frozen/notes/probes/2026-09-19-tableau-extensions/`, commit
`0a4f4f4`, branch `feat/tableau-extensions-probe`. The five stage D artifacts
of the frozen export are byte-identical to the live probe directory (`md5`),
so the concurrent stage B fix pass did not touch them.

**What I compiled.** A fresh copy of the frozen sources in my own scratch
directory, with the production `_CoqProject` flags as bare arguments,
`-R <production dir> pgg_smc` / `pgg_reconstruct` for every production
directory, and `-Q <my copy dir> tableau_ext_probe` last, each run under
`rocq1 600 8000 rocq compile -time`. No production `.v` was compiled; the
production `.vo` set was loaded as is, and `instances/psl211/psl211_endpoints.v`
was never opened.

| file | rc | wall | sum of `-time` |
|---|---|---|---|
| `p1_joint_law_distance.v` | 0 | 4.3 s | 4.183 s |
| `pgg_tableau.v` | 0 | 14.3 s | 14.093 s |
| `pgg_tableau_syntax.v` | 0 | 5.1 s | 4.927 s |
| `psl211_rows.v` | 0 | 6.1 s | 5.986 s |
| `p6_psl211_word_model.v` | 0 | 4.3 s | 4.182 s |
| `p6_psl211_word_proximity.v` | 0 | 5.1 s | 5.000 s |
| `p6_mutations.v` | 0 | 4.3 s | 4.220 s |
| `assumptions_report_stageD.v` | 0 | 233.7 s | 233.607 s |

The assumptions report is my own run, not a reading of the prover's log. It
prints 31 sentences, 21 of them `Print Assumptions`, of which eleven exceed
five seconds, the slowest at 22.3 s; every slow one is a `Print Assumptions`
on a declaration that mentions the twelve-card probability model, which the
brief exempts. Scanning it from each `Axioms:` line on with `^([\w'.]+)\s*:`,
which catches a module-qualified name: 21 blocks, every block exactly
`propositional_extensionality`, `functional_extensionality_dep` and
`constructive_indefinite_description`, no fourth name anywhere, and no
declaration `Closed under the global context`. That is what
`STATUS-stageD.md:289-315` claims, and it is the same set the production
`psl211_row_alldecks_tableau` and `psl211_alldecks_view_secrecy` print, which
the report includes for the comparison. Stage D introduces no assumption.

Four experiments of my own, in the same directory and against the same `.vo`
chain, each built from the header of `p6_mutations.v`:

| file | what it asks | rc |
|---|---|---|
| `m3_scope.v` | do `pgl27_exact_family`, `psl211_word_family`, `var_dist_le2` resolve here | 0 |
| `m1_tauto_nofail.v` | the tautology probe with the `Fail` guard removed | 1, error read |
| `m2_cross_nofail.v` | the cross-instance ideal with the `Fail` guard removed | 1, error read |
| `a_checks.v` | the certificate's secret, its witness's carrier, and two non-identities | 0 |

## Findings

| ID | Severity | file:line | Claim | Evidence | Checked replacement |
|---|---|---|---|---|---|
| S1 | SHOULD | `p6_psl211_word_proximity.v:181-183` | "The certificate's number is under two ... so the certificate is not vacuous." | The lemma proves `ipc_eps < 2` and nothing else, which rules out the ceiling tautology only. `audit-stageB-fix1.md` N2 compiled the second vacuity lever: a certificate whose `ipc_ideal` is its own model and whose `ipc_witness` has `ew_secretT = unit` makes `IdealProximityPropAt` true at zero, and `ipc_eps < 2` does not exclude it. The sentence asserts the general property from the narrow fact. | "so the certificate is not the ceiling tautology." Checked: the lemma's statement is `ipc_eps (psl211_word_proximity_cert R idx) < 2%:R`. The stronger sentence would also be defensible here, and my `a_checks.v` (rc=0) supplies it: `ew_secretT (ipc_witness cert) = bool` and `ew_secret (ipc_witness cert) = psl211_alldecks_secret R` by `erefl`, and `ipc_ideal cert = amf_sample psl211_word_family R idx := erefl` is rejected. |
| S2 | SHOULD | `p6_psl211_word_proximity.v:183-185` | "At about 4.5e-13 of that ceiling it is a cryptographic separation and not a weak one, as the proximity certificate of Kim's one-cut model is." | Two problems in one clause. "A cryptographic separation" is a security judgement the file does not prove: the proposition is a variation distance to an ideal at a static coalition of at most five seats, and it quantifies over no adversary class. And it ranks this row's number against another row's over a different model, which is the comparison `soundness-audit-stageB.md` verdict 1 recorded as absent from the five-card comments. The fraction itself is right: `2^-40 / 2 = 2^-41 = 4.5474735e-13`. | "The number is `2^-41` of that ceiling." Checked: `2%:R^-40` halved is `2%:R^-41`, and `2^-41 = 4.5474735088646411895751953125e-13`. Prose only, and it drops the cross-row ranking and the unproved security word. |
| S3 | SHOULD | `p6_psl211_word_proximity.v:26-28` | "this instance has no row carrying a constant for this model to be read in one column with, the constancy field a spectral certificate would need being refuted at it." | Overstates what is refuted. `psl211_alldecks_constancy_false` (`instances/psl211/psl211_spectral_constancy.v:258`) refutes `coalition_reading_constancy psl211_alldecks_params` at the group-uniform cut law `` `U psl211_G_pos `` and at no other ideal; `psl211_alldecks_no_small_eps_cert` (`:703`) excludes only certificates whose shuffle bound doubled is below `1/660`. The production header of that file says the rest of the range is occupied, "so a certificate at that ideal exists with an epsilon near 2" (`:55-59`), and "Nothing here says the word row is excluded outright" (`:67-68`). | "the constancy field a spectral certificate would need being refuted at the group-uniform ideal cut, which excludes every certificate whose shuffle bound is below `1/1320` and leaves the larger ones open." Checked against `psl211_alldecks_constancy_false`'s statement, against `psl211_alldecks_no_small_eps_cert`'s statement, and against `psl211_card : #\|pgg_G psl211_M\| = 660` (`instances/psl211/psl211_closure.v:703`). |
| S4 | SHOULD | `p6_psl211_word_proximity.v:206-209` | The row's average sentence cites `psl211_alldecks_constancy_false` and `psl211_dealt_constancy_false` "in both run modes". | Both cited lemmas are stated at the group-uniform cut law, not at this row's cut law, and the second is stated at `psl211_dealt_params`, a different execution from the one this row runs. The refutation at this row's own cut is in the same production file and is not cited: `psl211_alldecks_constancy_false_word584` (`:769-774`) takes the 584-letter word cut law and refutes the constancy field at every ideal within `eps` of it once `(2^-40 + eps) + (2^-40 + eps) < 1/660`. Neither cited refutation's coalition is named; both are witnessed at the three-seat `psl211_perdeck_coalition`. | Add the third name and the seat count: "... which `psl211_alldecks_constancy_false` refutes at the group-uniform cut, `psl211_alldecks_constancy_false_word584` at the 584-letter word cut this row draws, and `psl211_dealt_constancy_false` in the dealer-dealt run mode, each at a coalition of three seats." Checked by reading the three statements verbatim; I did not compile an instantiation of `_word584` at `eps = 0`. |
| N1 | NOTE | `STATUS-stageD.md:4` | "Repository `rocq-pgg-smc` at HEAD `ceb2317`." | Stage D is commit `0a4f4f4`, whose parent is `df6ebfb` (stage C fix pass 1), two commits after `ceb2317`. The status section at `:396-402` records the concurrent stage C fix pass, so `ceb2317` was probably the HEAD when the work began. | "at `df6ebfb`, the parent of this stage's commit `0a4f4f4`". Checked with `git log --oneline` and `git diff df6ebfb 0a4f4f4 --stat`. |
| N2 | NOTE | `p6_psl211_word_model.v:69-70` | "`psl211_word_mixing` is the whole price of the departure." | A lemma is not a price. The price is the number the lemma proves. | "the bound `psl211_word_mixing` proves is the whole price of the departure". Prose only. |
| N3 | NOTE | `p6_psl211_word_proximity.v:92-94` vs `:99-101` | The comment opens "At every coalition of at most five of the twelve seats" and closes "The bound holds at every coalition and not only below the threshold." | The opening understates the lemma it documents. The lemma discards its threshold premise with `move=> _`, so it is proved at every `C`, all twelve seats included. The closing sentence is the accurate one. | Open with "At every coalition of the twelve seats" and keep the closing sentence; the threshold then appears only where it belongs, in `IdealProximityPropAt`. Checked against the proof script and against `pgg_tableau.v:457-471`. |
| N4 | NOTE | `p6_psl211_word_model.v:74-77` | "the deck description uniform over the 136857600 of them, the cut the 584-letter word law, the two independent." | The independence is a modelling premise about the dealer, that the word's letters are drawn without seeing the deck, and the product `` `x `` encodes it rather than proving it. The sentence states it as a property of the construction. A dealer who peeks breaks it and the row says nothing then. | Add one clause: "the two independent, which is the dealer drawing the word without seeing the deck". The cardinality is right: `psl211_alldecks_cardE : #\|{: psl211_inputT}\| = 2 * 132 * 6`! * 6`!` (`instances/psl211/psl211_alldecks.v:174`), and `2 * 132 * 720 * 720 = 136857600`. |
| N5 | NOTE | `STATUS-stageD.md:373-379` | "A landing would make one copy of each global beside `var_dist_le2` in `lib/var_dist_supp.v` ... That is the one edit to an existing file the landing needs." | True only if the two production `Local` copies of `var_dist_prodR` stay, leaving three copies of one lemma. They are `instances/pgl27/pgl27_mixing.v:1077` and `instances/psl211/psl211_mixing.v:577`. Neither file requires `var_dist_supp` today, so nothing clashes, but neither is the duplication removed. Removing them is also safe under the rule: `psl211_endpoints` is in neither file's reverse closure. | "... the one edit the landing needs, leaving the two `Local` copies at `instances/pgl27/pgl27_mixing.v:1077` and `instances/psl211/psl211_mixing.v:577` in place; retiring those is two further edits, both outside the `psl211_endpoints` closure." Checked with my own closure script. |
| N6 | NOTE | `p6_psl211_word_proximity.v:229-237` | `psl211_row_word_proximity_publishedE` is titled "The three coordinates the row publishes." | An `AnalysisPathRow` is built from five arguments (`manifest/pgg_analysis_manifest.v:907-909`); the lemma pins completion, transfer and assumptions and leaves the observed execution and the model family unpinned. The comment's own claim is nevertheless carried: the transfer coordinate alone separates this row from the manifest's, and my `a_checks.v` compiles `Fail Definition ... published_row psl211_row_word_proximity = psl211_row_alldecks := erefl` (rc=0 for the file, the `Fail` guard passing). | None needed. If a fourth conjunct is wanted, `apr_model (published_row psl211_row_word_proximity) = psl211_word_family` is the coordinate that names the model; I did not compile it. |

No BLOCKING finding. Nothing stage D proves is false, over-numbered, or
vacuous, and no statement of the framework was weakened to let it through.

## Verdict per question

**1. The word model. PASS.** Both adapters are `MkSampleAdapter` over
`instance_exec psl211_alldecks_params`, on the carrier
`(psl211_inputT * pgg_gT psl211_M) : finType`, with readers `fst` and `snd`
(`p6_psl211_word_model.v:87-92`; `instances/psl211/psl211_models.v:222-227`).
Same execution, same sample space, same readers. The run-argument law is
`` `U psl211_alldecks_gt0 `` in both, the uniform law on all of
`psl211_inputT = (bool * psl211_deal)%type`
(`instances/psl211/psl211_alldecks.v:110`, `:166`), so it is uniform on the
whole run argument, secret bit included, and it is the same term the all-decks
model has. Only the cut factor differs: `psl211_word_cutP` is
`@rho_from_words_weighted R 10 2 584 psl211_moves (psl211_Wuni R)`, which is
letter for letter the left side of `psl211_word_mixing`
(`instances/psl211/psl211_mixing.v:545-548`). `psl211_word_cut_distE` is indeed
the statement that the adapter's cut law is that word law: `sa_cut_dist` is
`fdistmap sa_cut sa_sampleP` (`security/pgg_sample_adapter.v:196-197`), which
at this adapter is `fdistmap snd` of a product, closed by P1's
`fdist_prod_snd`. Run argument and cut are independent by construction, the
law being a `` `x `` product; that is what a real execution gives when the
dealer draws the word without seeing the deck, which is a premise and not a
theorem (N4).

**2. The distance field. PASS.** Four steps, each checked against its
statement. `var_dist_fdistmap_pair` (`p1_joint_law_distance.v:61-69`) is
`var_dist_fdistmap` (`security/pgg_collusion_bound.v:126`) under `le_trans`,
and it demands one pair of readers on both sides, which is why the "same two
projections" claim carries weight. It holds by conversion and not by
extensionality: `sa_arg` and `sa_cut` of both adapters are the record fields
`fst` and `snd`, so the two lambdas are one term after iota reduction, no
`funext` appears in the script, and `Print Assumptions
psl211_word_proximity_close` shows the three boolp constants and nothing more.
`var_dist_prodR` (`:84-94`) is an equality, so it neither loses nor gains.
`psl211_word_mixing` closes at `2^-40`. Discarding the threshold premise is
plausible and harmless: the lemma bounds a distance between two models' joint
laws, an information-theoretic fact that holds at all twelve seats, and it is
not a privacy claim, the ideal leaking above the threshold as well. The
threshold is carried by `IdealProximityPropAt` itself
(`pgg_tableau.v:457-471`). The comments say this at `:99-101` and
`STATUS-stageD.md:151-154` and nowhere suggest privacy above the threshold.
N3 is the only wrinkle.

**3. The secret. PASS, with compiled evidence.** `ipc_secret` is
`psl211_alldecks_secret R`, and `ew_secret (ipc_witness cert)` is the same
function: both equations hold by `erefl` in my `a_checks.v`, rc=0. Its carrier
is `bool`, not `unit` (`a2_secretT`, `erefl`). So `ipc_close` compares
`(reading, chirality)` under the word model with `(reading, chirality)` under
the all-decks model with one and the same chirality function on both sides,
and `IdealProximityPropAt` then compares the word model's joint law with the
product of the all-decks model's reading marginal and secret marginal, the
secret being the real chirality bit. Against `audit-stageB-fix1.md` N2: the
vacuity lever there is `ipc_ideal` set to the certified model together with an
`ExactWitness` at a unit secret. Neither holds. The ideal is not the actual
model as a term (`Fail Definition ... := erefl` in `a_checks.v`), and the
witness is `psl211_exact_witness` (`psl211_rows.v:172-181`), whose `ew_indep`
is `psl211_alldecks_view_indep` at `#|C| <= 5`, a proved theorem. This
certificate is not the vacuous kind.

**4. The number and what it buys. PASS, with S1 to S4.** `2^-40` is
`1/1099511627776 = 9.094947017729282379150390625e-13`, and since infotheo's
`var_dist` is the sum of absolute differences
(`variation_dist.v:34`), twice the literature's total variation, a
distinguisher's advantage is at most `2^-41 =
4.5474735088646411895751953125e-13`. No comment presents the number as a
guarantee at a fixed deck: both `:99` and `:205-207` say the claim is an
average over the deck description and the cut. Invariant 3's refutations all
exist under the names given, `psl211_alldecks_constancy_false` (`:258`),
`psl211_dealt_constancy_false` (`:953`) and `psl211_alldecks_no_small_eps_cert`
(`:703`) of `instances/psl211/psl211_spectral_constancy.v`, and stay true
beside this row. The `no_small_eps` paraphrase is exact: the theorem refutes
`sw_bound_eps (sc_b cert) + sw_bound_eps (sc_b cert) < (#|pgg_G psl211_M|%:R)^-1`
and `psl211_card` gives `660`, so every shuffle bound strictly below `1/1320` is
excluded and `1/1320` itself is not, which is what `STATUS-stageD.md:47-48`
says. S3 and S4 are about how the neighbouring sentences describe those
refutations, not about the arithmetic.

**5. P7. PASS.** Recompiled both rejected terms with the `Fail` guard removed.
The tautology probe fails with exactly the text recorded at
`p6_mutations.v:72-74`: `The term "var_dist_le2 ?P ?Q" has type "is_true
(var_dist ?P ?Q <= 2)" while it is expected to have type "is_true (var_dist
(psl211_wordP R) (psl211_alldecksP R) <= 2 ^- 40)"`. The cross-instance ideal
fails with exactly the text at `:91-94`: `The term "amf_sample
pgl27_exact_family R tt" has type "SampleAdapter R (OE.oe_execution
pgl27_exec.pgl27_observed)" while it is expected to have type "SampleAdapter R
(instance_exec psl211_alldecks_params)"`. Neither is a missing-name failure:
`m3_scope.v` compiles `Check pgl27_exact_family`, `Check psl211_word_family`
and `Check var_dist_le2` in the same context, rc=0. Vacuity is clear on both
sides: the accepted half `psl211_word_law_le2` carries no hypothesis beyond
`(R : realType)`, and the rejected certificate applies
`psl211_word_proximity_close` fully, so the rejection is at the ideal field's
type and not at an undischarged hypothesis. The file states the right caveat at
`:15-16`, that a rejection is of one written term and is no proof that no term
exists.

**6. P3 and the row. PASS, with N6.** `split; exact: erefl` equates two
definitional projections. On one side `ipc_ideal cert` is the constructor's
own second argument, so the content of the equation is that
`ab_f (published_at psl211_row_alldecks_tableau)` reduces to
`psl211_exact_family` and `ab_port ...` to
`ExactIndependence (psl211_exact_witness R idx)`; that is real content, it
links the certificate to the published row, but it is definitional by
construction on one side and should not be read as an independent check of the
ideal. `_armE` gives `IdealProximityArm`, consistent with
`certify_idealproximity_armE` (`pgg_tableau.v:975-979`). `_publishedE` gives
`AnalysisBridged`, `IdealFinite`, `BaselineClassicalOnly`. `IdealFinite` is the
right transfer status and matches precedent: the manifest publishes
`PGL27Analysis.word_family IdealFinite BaselineClassicalOnly`
(`manifest/pgg_analysis_manifest.v:813`) and the five-card biased and centi
rows likewise (`:844`, `:863`), while `psl211_row_alldecks` is
`StaticExecutedOnly` because its cut is already the uniform one
(`psl211_rows.v:193-195`). A word shuffle measured against an idealised one is
exactly the `IdealFinite` case. The row does publish a manifest row the
manifest does not hold: the manifest carries only
`psl211_row_alldecks = MkAnalysisPathRow ... PSL211Analysis.exact_family
StaticExecutedOnly BaselineClassicalOnly` (`:907-909`) and no PSL(2,11) word
family, and `Fail Definition ... published_row psl211_row_word_proximity =
psl211_row_alldecks := erefl` passes in `a_checks.v`. This is where PSL(2,11)
differs from PGL(2,7), whose stage C row proves `published_row
pgl27_row_word_proximity = pgl27_row_word` by `erefl`
(`p5_pgl27_word_proximity.v:296-297`). D2 says so, at
`p6_psl211_word_proximity.v:229-231` and at `STATUS-stageD.md:381-386`.

**7. D1 and D2. PASS, with N5.** Recomputed with my own Python over the
`Require` lines of every `.v` under a production `-R` or `-Q` directory,
comments stripped, names resolved by basename; no basename is ambiguous. The
forward closure of `psl211_endpoints` is 34 files, the exact list at
`STATUS-stageD.md:326-333`. The reverse closure of `psl211_models` is ten, the
exact list at `:349-351`. The reverse closure of `lib/var_dist_supp.v` is
eleven, `five_card_analysis five_card_mixing five_card_rows
pgg_analysis_client pgg_analysis_manifest pgg_tableau pgg_tableau_syntax
pgl27_rows psl211_rows psl211_spectral_constancy s5_rows`; `psl211_endpoints`
is not among them, and `var_dist_supp` is not in `psl211_endpoints`' forward
closure. `psl211_mixing`'s reverse closure is one, `psl211_spectral_constancy`'s
is empty, `psl211_rows`' is empty. Every number in D1 is exact. So promoting
`var_dist_prodR` and `fdist_prod_snd` into `lib/var_dist_supp.v` is safe under
the rule: it rebuilds eleven files and none of them is `psl211_endpoints`. Two
of the eleven, `psl211_rows` and `psl211_spectral_constancy`, load
`psl211_endpoints.vo`; loading is cheap, the probe copy of `psl211_rows.v`
compiling in 6.1 s here, and it is not the 900 s rebuild. The two production
`Local` copies are `instances/pgl27/pgl27_mixing.v:1077` and
`instances/psl211/psl211_mixing.v:577`; neither file requires `var_dist_supp`,
so a global copy would not clash with them and they would simply remain, which
is N5.

**8. Invariants 1 to 8. All PASS.** 1: no `Axiom`, `Parameter`, `Hypothesis`,
`Variable`, `Admitted` or `Abort` in any stage D `.v`. 2: every distance is
`var_dist` between `fdist`s, and `psl211_word_mixing` is a counting bound over
the `3^584` words, so no computational assumption enters. 3: the average
sentence is carried at both places that state the claim and the refutations are
cited, subject to S4. 4: `ipc_ideal` is a `SampleAdapter` and `ipc_witness` is
`psl211_exact_witness`, never a bare law. 5: one `certify` and one `publish`,
one claim. 6: no `conclude`, so `PortProp no_reprice` evaluates the proposition
at `odflt (ipc_eps cert) None`, the certificate's own number, and nothing below
it is published. 7: `git diff df6ebfb 0a4f4f4 --stat` shows the probe's
`pgg_tableau.v` untouched, so nothing was removed from the Tableau. 8:
`git diff df6ebfb 0a4f4f4 --stat` lists eight files, 1254 insertions and no
deletion: `STATUS-stageD.md`, the probe `_CoqProject` (+4),
`assumptions_report_stageD.v`, `audit-stageB-fix1.md`,
`history/_CoqProject.11-before-stageD`, and the three new `p6_*.v`. No
production file appears. `instances/psl211/psl211_endpoints.vo` is dated
2026-09-17 16:32, two days before stage D, so it was never rebuilt.

**9. Domain position of the statement comments. PASS, with S1 to S4 and N2 to
N4.** What is present and right: the attack model is named at the file header
and repeated at every statement that carries it, a static coalition of at most
five of the twelve seats reading its own endpoints, with `profile_k_psl211 = 6`
as its source (`instances/psl211/psl211_profile.v:134`); the
average-over-the-run-argument sentence appears at both places that carry the
claim; the unconditional, information-theoretic character of `2^-40` is stated
with its source, the count of `3^584` words, and is not confused with an
assumption-conditional term, there being none in this row; the word gloss is
given once per file and used without drift, "deck description" for the whole
run argument in all three of its uses and "deal" for the three non-secret
coordinates in both of its uses; no barred vocabulary appears. Type honesty
holds where the stage B fix pass's A4 could have recurred: `:202-205` says the
joint law is *within* the number of the product, and the advantage is half of
the number, not half of the distance. The two `Fail`s are labelled as
rejections of written terms and not as refutations (`p6_mutations.v:15`).
What is missing is S1's unearned generality, S2's unproved security word and
cross-row ranking, S3's and S4's imprecision about which refutation holds where,
and N2 to N4.

## Overall: GO

Stage D's result may be folded into the spec. The word model runs the
all-decks row's own execution on the all-decks row's own sample space with the
all-decks row's own run-argument law, and replaces one factor; the distance is
a two-step consequence of P1 and `psl211_word_mixing` with nothing hidden in
between; the certificate's ideal is a model with a proved witness and its
secret is the real chirality bit on both sides; the number is the one proved
and the row publishes it plainly; and the assumptions are exactly the
production all-decks row's. The four SHOULD findings are all sentences in
comments and status prose, none of them load-bearing for a proof, and each has
a replacement checked against the code it describes.

## What I did not check

- I did not compile `instances/psl211/psl211_endpoints.v` and rebuilt no
  production file; the production `.vo` set was loaded as is.
- I did not re-verify the instance mathematics the row stands on:
  `psl211_word_mixing`, `psl211_alldecks_view_indep`,
  `psl211_alldecks_endpoints`, `psl211_alldecks_terminates` and
  `psl211_alldecks_recon` are taken from the compiled production `.vo`.
- I did not establish that `psl211_word_cutP R` and `` `U psl211_G_pos `` are
  provably different laws, so I have not ruled out that the row's `2^-40` is
  slack over an exact statement. Nothing in stage D claims otherwise, and the
  claim is sound either way.
- I did not compile an instantiation of `psl211_alldecks_constancy_false_word584`
  at this row's own cut law; S4's replacement cites that lemma as it stands.
- I did not re-derive STATUS's per-sentence `-time` table beyond confirming
  `rc=0`, the file order and the order of magnitude of each file's cost.
- I did not audit naming, indexing or `Definitions:` headers; that is the
  naming auditor's pass.
