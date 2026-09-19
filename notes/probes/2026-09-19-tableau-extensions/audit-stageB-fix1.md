# Independent audit of stage B, fix pass 1

2026-09-19. Opus auditor with no part in writing stage B or its fix pass, and
independent of the two audits the pass answers. Object: the frozen export at
`<scratchpad>/extB1_frozen/notes/probes/2026-09-19-tableau-extensions/`,
byte-identical to the live directory at the time of this audit (checked file by
file with `cmp`). Nothing in the repository was edited except this file.
`instances/psl211/psl211_endpoints.v` was never opened and never compiled, and
no `make` was run.

## What I compiled

Six experiment files in `<scratchpad>/extB1_audit/work`, one Rocq process at a
time through the machine-wide lock, production `_CoqProject` flags and
`-Q <work> tableau_ext_probe` last. Walls include queueing behind two other
agents, so only the verdicts are attributable.

| file | what it settles | rc |
|---|---|---|
| `x1_bycomp.v` | `five_card_biased_proximity_by_computation` without `Fail` | 1, as recorded |
| `x2_bydone.v` | `five_card_biased_proximity_by_done` without `Fail` | 1, as recorded |
| `x3_s5ideal.v` | `kim_biased_cert_s5_ideal` without `Fail` | 1, as recorded |
| `x5_checks.v` | what `view_proximity_of` gives, `cert_eps` of `kim_biased_cert_exact`, 1/50 < 1/25 | 0 |
| `x7_n2.v` | soundness note N2: a proximity certificate at the number zero | 0 |
| `x8_certeps.v` | `cert_eps` of `kim_biased_cert` | 0 |

I did not recompile the twenty probe files; the main session's recompile from
source is taken as given, and the `.vo` set it produced was used to elaborate
the experiments. Every `.v` of the frozen export was read.

## Findings

| ID | Severity | File:line | Claim | Evidence | Checked replacement |
|---|---|---|---|---|---|
| A1 | SHOULD | `p8_spectral_relation.v:22`; `STATUS-stageB.md:460`, `:582` | Part (c): "no implication holds uniformly in the proximity certificate" | False as stated. `idealproximity_ceiling` (`p7_mutations.v:85-89`) proves `IdealProximityPropAt cert 2%:R` for every `cert` over every model, so the implication from any premise whatever to the proximity proposition *is* uniform in the certificate at the constant two. The same header says so two paragraphs earlier, and the naming audit's B1 replacement supplied the qualifier that makes (c) true ("the relation has to be stated at a constant below two"); the pass dropped it. This is the same universal-without-a-constant shape both audits made blocking. | Insert the constant in all three places: "Argued and not compiled: **at a constant below two**, no implication holds uniformly in the proximity certificate." Checked against `idealproximity_ceiling`'s statement and against `five_card_biased_proximity_prop_holds`, which is the compiled instance at 1/50. Prose only. |
| A2 | SHOULD | `p4_kim_biased_proximity.v:214`; `STATUS-stageB.md:119-120` | "the same model also carries `kim_biased_cert`, a spectral certificate at sqrt 5 over eighty" | The number a spectral certificate carries is `cert_eps`, which is its marginal bound's epsilon twice (`pgg_tableau.v:438-440`). Compiled in `x8_certeps.v`, rc=0: `cert_eps (kim_biased_cert R tt) = Num.sqrt 5%:R * (1 / 40)` and `cert_eps (kim_biased_cert R tt) <> Num.sqrt 5%:R * (1 / 80)`. Sqrt 5 over eighty is `sw_bound_eps (kim_biased_marginal_bound R)` (`kim_biased_epsE`, `instances/kim2025/five_card_rows.v:533`). Three lines above, the same comment uses "the number X carries" for `cert_eps`, and the pass rejected R2's closing sentence for exactly this conflation at `kim_biased_cert_exact`. Stage A's fix 4 already corrected the sibling sentence in production to "sqrt 5 over forty". | "the same model also carries `kim_biased_cert`, whose marginal bound is sqrt 5 over eighty and which therefore publishes sqrt 5 over forty". Both numbers compiled in `x8_certeps.v`. Prose only. |
| A3 | SHOULD | `STATUS-stageB.md:200-205`, `:703-706` | "the whole scan returns four distinct tokens"; "The list of lines matching the scan that are not one of the four expected tokens is empty" | Applying the note's own regular expression `^([\w.]+)\s*:` to `assumptions_report_stageB.cclog`, the log this pass committed, returns five tokens: `Axioms`, `Warning`, and the three boolp constants. The extra one is the `notation-incompatible-prefix` warning the run prints before the first block. The soundness conclusion is untouched. | "the scan, from the first `Axioms:` line on, returns four distinct tokens"; or name the fifth and say it is the parser warning at the head of the log. Re-derived from the committed `.cclog`. |
| A4 | SHOULD | `p9_actual_marginals.v:13-14` | "the published number being the sum of the absolute differences and the advantage half of the bound on it" | The published number *bounds* the sum of the absolute differences; the sum is `var_dist`, and `IdealProximityPropAt` is `var_dist ... <= c`. The pass's companion sentence for the same audit item gets this right at `pgg_tableau.v:447` ("c bounds the sum of the absolute differences"), so the two places it touched disagree, and the loose half is the one the audits flagged as not type-honest. | "the published number bounding the sum of the absolute differences and the advantage being half of that bound". The arithmetic is unchanged and correct: 1.5 × 1/50 = 3/100. Prose only. |
| N1 | NOTE | `p4_kim_biased_proximity.v:171` | "so no slack is carried into the record" | `kim_biased_cut_mixing_exact` is an inequality on the cut group; what is exact is the per-card-position distance, `kim_one_cut_centiE` (`instances/kim2025/five_card_kim.v:661`), and the data-processing step down to the joint law can only lose. No compiled statement makes 1/50 tight for the quantity the certificate bounds. | "and the number is the smallest the tree proves for that distance, so the bundle's overestimate is not carried into the record". Checked against `kim_biased_exact_le_eps` (`five_card_rows.v:542`), which is what "the bundle's overestimate" names. |
| N2 | NOTE | `pgg_tableau.v:187`; soundness note N2 | The pass leaves N2 as "a property the arm inherits from `ExactWitness`" | Correct, and sharper than the note. `ipc_secret` alone is not a lever: the right side of `ipc_close` reads `ew_secret (ipc_witness cert)`, so a constant `ipc_secret` under an honest witness makes the distance larger, not smaller. The vacuity lever is `ipc_witness` together with `ipc_ideal`. Compiled in `x7_n2.v`, rc=0: an `ExactWitness` over Kim's own biased model whose secret is `unit_RV`, an `IdealProximityCert` over that model whose ideal is that same model and whose `ipc_eps` is `0`, and `IdealProximityPropAt` at `0` from `idealproximity_tail`. The arm's proposition is then true at zero and says nothing about the protocol's secret. `SpectralCert`'s `sc_ideal` has the same freedom, so the arm introduces none. | None needed. A landing note in D2 that the domain content of a proximity row lives in its ideal and its witness, not in its number, would be worth one sentence. |
| N3 | NOTE | `p7_mutations.v:123-124` | soundness N3, left open: "the reading it bounds is not the constant finfun and the statement is about a seat that sees a card" | Still uncompiled. The non-emptiness half is compiled (`five_card_singleton_below_threshold`, by `cards1`); the non-constancy of the reading is asserted and nothing proves it. Plausible and unbacked. | None. The pass's disposition ("outside this pass's items") is honest. |
| N4 | NOTE | `p7_mutations.v:97` | The file's `Definitions:` index lists `five_card_biased_proximity_at_singleton` and not the new `five_card_reprice_inv100` | The naming audit's N3 asked for the `Fact` to be indexed and it was, under `Lemmas:`; the new `Definition` was not. | Add one index line for `five_card_reprice_inv100`. |
| N5 | NOTE | `STATUS-stageB.md:591` | "the five five-card production modules" | `p8_spectral_relation.v` gained eight production modules on three `From pgg_smc` lines: `five_card_group`, `five_card_family`, `five_card_exec`, `five_card_models`, `five_card_leakage`, `five_card_kim`, `kim_input_privacy`, `five_card_mixing`. | "eight production modules, seven `five_card_*` and `kim_input_privacy`". Counted from the file. |

## Verdicts by check

**1. The exact certificate.** PASS, with N1. The proof of
`kim_biased_proximity_close` is one data-processing step and one product step
and nothing else: `var_dist_fdistmap_pair` (`p1_joint_law_distance.v:61-65`) is
`var_dist_fdistmap` at the pairing map with no factor, `var_dist_prodR`
(`:85-87`) is an equality, and the four remaining rewrites are identifications
(`five_card_reading_secretE`, `five_card_arg_cut_prodE`,
`five_card_uniform_pairE`, `kim_single_cut_distE`, `five_card_sample_cut_distE`,
`kim_biased_sample_cut_witnessE`). `exact: kim_biased_cut_mixing_exact` closes
at 1/50. No hidden loss, no hidden gain. `ipc_eps` is the literal `1 / 50`
(`erefl`). The prover's reason for publishing plainly is right and compiled:
`PortProp no_reprice` on an `IdealProximity` port is
`IdealProximityPropAt cert (odflt (ipc_eps cert) None)`, and `x5_checks.v`
proves `PortProp no_reprice (ab_port (published_at
five_card_row_biased_proximity) R tt) = IdealProximityPropAt
(kim_biased_proximity_cert R tt) (1 / 50)` by `erefl`. For this row
`view_proximity_of` gives exactly that proposition: at every real field, every
`C` with `#|C| < 2`, the joint law of the coalition's executed view with the
conjunction of the committed bits under Kim's one biased cut is within 1/50 of
the product of the den Boer uniform model's two marginals. Nothing sharper
exists in the tree: `kim_one_cut_centiE` gives the per-position distance as an
equality at 1/50 and every cut-group statement is at that number or above. The
published 1/50 is below the spectral sibling's 1/25 (compiled,
`aud_inv50_lt_inv25`), and no comment presents the two as comparable strengths
of one claim: the p4 header, the row comment and the status section all say the
spectral arm spends the distance twice and the proximity arm once, which is a
statement about two propositions and not a ranking.

**2. `kim_biased_proximity_eps_halfE`.** PASS, with A2. Restated against
`kim_biased_cert_exact`, closed by `exact: erefl`, and its comment states a
relation between two certificates rather than between two arms. R2's closing
sentence is indeed false and the prover was right to reject it: compiled in
`x5_checks.v`, `cert_eps (kim_biased_cert_exact R tt) = 1 / 25` and
`<> 1 / 50`. One fiftieth is that certificate's marginal bound's
`sw_bound_eps`, not the number the spectral arm publishes from it, exactly as
the pass says. The replacement sentence then repeats the conflation for
`kim_biased_cert`; that is A2.

**3. Withdrawn declarations.** PASS. `five_card_sqrt5_le3` and
`kim_biased_proximity_le_inv25` occur in no `.v` file of the frozen probe and
in no status text except `STATUS-stageB.md:547`, which records their deletion
in the past tense and points at the history snapshot. The four stage C files
(`p5_pgl27_prior_ideal.v`, `p5_pgl27_word_proximity.v`, `p5_mutations.v`,
`assumptions_report_stageC.v`) name neither, name no `kim_biased_*`
declaration and mention neither 1/25 nor 1/50, so they cannot depend on the
withdrawn pair. "sqrt 5 over eighty" survives only in stage A's
`five_card_rows.v:547`, `:555` and in the p4 sentence A2 flags.

**4. p7 after the swap.** PASS. Each of the three changed `Fail` sentences was
recompiled without `Fail` in a standalone file with p7's requires. The decisive
lines are the recorded ones: `five_card_biased_proximity_by_computation` gives
`Unable to unify "true" with "var_dist ... <= ipc_eps
(kim_biased_proximity_cert R idx)"`, which is the status's row including the
new tail; `five_card_biased_proximity_by_done` gives `Error: No applicable
tactic.`; `kim_biased_cert_s5_ideal` gives `The term "amf_sample s5_rand_family
R idx" has type "SampleAdapter R (OE.oe_execution s5_rand_observed)" while it
is expected to have type "SampleAdapter R (instance_exec five_card_params)".`
`kim_biased_conclude_below_false` is the negation of the `IdealProximity`
branch of `ConcludePayload` at `five_card_reprice_inv100`, which reduces to
`~ (1 / 50 <= 1 / 100)`; the comment's "false, and not merely beyond what the
probe could prove" is right, and so is its reading that a published number
moves upward only. `five_card_reprice_inv100` is the constant `Some (1 / 100)`,
half of the certificate's number, as its comment says. The ceiling comparison
recomputes: `ipc_eps < 2%:R` by `lra` off the closed form, and 1/50 is one
percent of the ceiling, which is what
`kim_biased_proximity_cert_eps_lt2`'s comment now says.

**5. P8's four-part account.** PASS with A1. (a) and (b) are compiled and
marked "Compiled" in the file header, in the status verdict table ("partial, in
four parts: two compiled and two not"), in the "What in the brief or the spec
turned out wrong" list and in the fix-pass section. (c) and (d) are marked
"Argued and not compiled" and "Not compiled" in every place they appear. The
two new lemmas are `five_card_biased_proximity_prop_holds` and
`five_card_biased_spectral_implies_proximity`; their statements are true of the
code (the first is `view_proximity_of` applied, which `x5_checks.v` confirms
has that exact type), their names carry the model, and their comments say in
terms that the implication carries no information. The requires they need were
added (see N5 for the count). No sentence anywhere in stage B still restates
the old overclaim: "refuted", "cannot follow", "cannot imply" and "whatever the
numbers" return nothing in the nine stage B `.v` files, and in
`STATUS-stageB.md` "refuted" survives only in the sentence saying the verdict
is *not* that, and in the account of the changed auditor sentences. A1 is the
one universal that is still stated without its constant.

**6. The advantage sentences.** PASS with A4. The arithmetic is right
everywhere. `var_dist` is the sum of the absolute differences and
`lib/var_dist_supp.v:45-50` records in the tree's own words that the total
variation distance of the literature is half of it, so an advantage is at most
half the published number: half of 1/50 is 1/100, and half of P9's 3/50 is
3/100, which is "one and a half times the published number". A search for
"advantage" over the nine stage B `.v` files returns `pgg_tableau.v:450` and
`p9_actual_marginals.v:11`, `:14`, `:18` and nothing else; "the whole of what"
survives only at `pgg_tableau.v:667`, about `ExactWitness`, and "exactly as
much" only in the status's record of the sentence it replaced.

**7. The eight auditor sentences.** Seven are true of the code and the change
was warranted in all eight. Sentence 1: dropping R1's "because the two sides
would then vary independently" is right, since `spectral_prop_cert_free` does
not refute the schema, as `idealproximity_ceiling` shows. Sentence 2 states
what `idealproximity_ceiling` states. Sentence 3 is right about
`kim_biased_cert_exact` and carries A2 in its replacement. Sentence 4 matches
the row, which is no longer concluded. Sentence 5's two names are the two
lemmas in the file, at 1/50. Sentence 6's rewriting is sound. Sentence 7 turns
an equality into an upper bound. Sentence 8's added reason is correct: a failed
`by []` shows non-convertibility and no more.

**8. Not applied.** No real defect is left open beyond N1-N5. The rename table
is correctly declined, and D1's first-word rule checks out against the tree:
`SpectralDecay` gives `certify_spectral`, `spectral_tail`, `SpectralPropAt` and
`SpectralPayload`; `ExactIndependence` gives `certify_exact` and `exact_tail`;
and the reason for the departure holds, since `ideal` is a surface keyword of
`pgg_tableau_syntax.v:401`, the field name `ipc_ideal` and the head of
`IdealFinite`. N1 (`fdist_uniform_prod` unused) is confirmed: its only
occurrences are its own statement, its index line and its `Print Assumptions`.
N2 is disposed of correctly and I sharpened it by compiling the vacuity case
(see finding N2). N3 stands as an uncompiled sentence (finding N3). N4 is moot,
as the pass says: the slowest sentence of `p4_kim_biased_proximity.v` is now a
`From mathcomp Require` at 2.28 s and the `Lemma
five_card_row_biased_arm_neq` sentence costs 0.23 s, down from the 3.25 s the
soundness audit measured.

**9. Record.** PASS with A3, N4 and N5. Recomputed by my own script against
`history/pgg_tableau.v.7-before-stageB`: declarations 68 to 75, `wc -l` 836 to
1002, comment-stripped lines 414 to 504, so the table's +7, +166 and +90 are
exact and the "five of those 166 are this pass's comment lines" reconciles with
the naming audit's pre-fix count of 997. The `Definitions:` index gained four
lines and `Key results:` four, as the pass now says. The compile table's
per-sentence figures match the committed `-time` logs exactly: `ab_port` 4.06
s, `ab_f` 3.57 s, p4 2.28 s, p8 2.09 s, p9 2.30 s, p7 2.35 s, and no sentence
outside a `Print Assumptions` above 5 s; the walls are within noise of the main
session's 5.2 / 12.9 / 4.1 / 3.9 / 3.8 / 26.6. The assumptions summary
reconciles: `assumptions_report_stageB.v` holds 36 `Print Assumptions`, none
duplicated, and the log holds 35 `Axioms:` blocks and one `Closed under the
global context`, so 36 blocks is right and the main session's 35 is the
`Axioms:` count. Every back-quoted identifier in the new section resolves
against the probe or the 210 production files; the unresolved fragments are
file names, suffix fragments, the two deleted names cited as deleted, the
auditor's own `aud_conclude_below_false` and R1's two proposed names, all of
which the text marks as such. No line of `STATUS-stageB.md` cites a line number
of itself. No audit or pass narration appears in any `.v` file. Every boxed
header line in the nine stage B files is exactly 80 bytes, including
`p1_joint_law_distance.v:33`, which N1 of the naming audit asked for; the only
lines over 80 are `pgg_tableau_syntax.v:332`, `:370`, `:401`, the three known
ones, whose numbers moved by three because the header gained three lines. No
barred vocabulary anywhere in the probe.

## Overall

**GO** for "stage B is closed", conditional on the four sentences A1, A2, A3
and A4. All four are prose, none touches a proof, and each has a replacement
checked against the code or compiled here. A1 and A2 are the two that matter:
A1 states a universal that the probe's own `idealproximity_ceiling` refutes
without the constant, and A2 attaches a marginal bound's number to a
certificate three lines after the same comment rejected that reading for the
sibling certificate.

## What I did not check

The twenty probe files were not recompiled from source; I relied on the main
session's run and used its `.vo` set. `psl211_rows.v`, `pgl27_rows.v`,
`s5_rows.v`, the two T0 files and `g2_keyword_measure.v` were read but their
recorded failures were not re-run, since the pass changed no line in them. D2's
production line citations were not re-opened; the naming audit did that. The
stage C files were read only for dependence on the withdrawn names. I did not
check whether the eight production requires added to `p8_spectral_relation.v`
are all needed, and I did not check the G2 keyword measurement.
