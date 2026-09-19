# Naming, style and record audit of stage B

2026-09-19. Opus auditor, independent of the prover and of the stage A audit
rounds. Object: the frozen export of `notes/probes/2026-09-19-tableau-extensions/`
at commit `8ea05d5`, under
`<scratchpad>/extB_frozen/notes/probes/2026-09-19-tableau-extensions/`. Every
line number below is a line of that frozen copy. Production line numbers are
marked with their path.

Rocq work: one experiment file and one full renamed copy of the probe, compiled
through the shared lock against the main session's `.vo` set. No repo file was
edited except this one. `instances/psl211/psl211_endpoints.v` was never read,
never compiled, and no `make` was run.

## Findings

| ID | Severity | File:line | Claim | Evidence | Checked replacement |
|---|---|---|---|---|---|
| B1 | BLOCKING | `p8_spectral_relation.v:57-60`, and `STATUS-stageB.md:419-420` | The comment on `spectral_prop_cert_free` ends "A statement about how far that model is from an ideal one therefore cannot follow from it, whatever the numbers are"; the note generalises it to "A proposition that does not mention any ideal cannot imply a bound on the distance to one, at any instance and at any constant." | False, and the probe holds the refutation. `idealproximity_ceiling` (`p7_mutations.v:74-78`) proves `IdealProximityPropAt cert 2%:R` for every certificate, so the implication holds at the constant two from any premise whatever. I compiled the implication directly: `<scratchpad>/extB_naming/x1_p8_overclaim.v`, `Lemma spectral_implies_proximity_at2 (cert : SpectralCert sa) (cert' : IdealProximityCert sa) (c : R) : SpectralPropAt cert c -> IdealProximityPropAt cert' 2%:R`, closed by `by move=> _ C _; exact: var_dist_le2`, `rc=0`, wall 3.6 s. What `spectral_prop_cert_free` establishes is narrower: the spectral proposition does not mention the certificate, so no proof of a proximity bound can read the ideal cut out of it. | For the comment, last sentence: "No ideal the certificate names can be recovered from it, so a bound on the distance to that ideal has to come from elsewhere; `idealproximity_ceiling` shows the implication is not empty at the ceiling." For the note, replace "at any instance and at any constant" with "by reading its ideal out of the premise; at the ceiling the conclusion holds outright, so the relation has to be stated at a constant below two." I re-read both against the two declarations. |
| S1 | SHOULD | `pgg_tableau.v:445-447` | `IdealProximityPropAt`'s comment (the declaration is at `:452`): "so c is the whole advantage a coalition below the threshold has over an observer who sees the two quantities drawn apart." | Type-honest phrasing. `var_dist` is the sum of absolute differences, and `lib/var_dist_supp.v:45-50` states in the tree's own words that "the total variation distance of the literature is half of this quantity". A distinguisher's advantage is therefore at most `c/2`, not `c`. Production says "the number bounds every advantage it has" (`instances/kim2025/five_card_mixing.v:397`), which is an upper bound and sound; "is the whole advantage" is an equality and is not. | "so c bounds the sum of absolute differences between what a coalition below the threshold sees jointly with the secret and two quantities drawn apart, and the advantage of a distinguisher is half of it." Checked against `IdealProximityPropAt`'s body and against `var_dist_le2`. |
| S2 | SHOULD | `pgg_tableau.v:180-181` | `IdealProximityCert`'s comment (the record is at `:182`): "the number is the whole of what the actual model loses against an execution that leaks nothing." | `ipc_close` is an inequality, `var_dist ... <= ipc_eps`, so the number is an upper bound on what is lost and not the whole of it. The same record's own comment two lines earlier correctly says "that number as a bound on the variation distance". | "the number bounds what the actual model loses against an execution that leaks nothing." Checked against the `ipc_close` field. |
| S3 | SHOULD | `p4_kim_biased_proximity.v:123`, `:168`, `:199` against `:41` and `:206-207` | One file uses "the spectral number" for two provably different quantities. At `:41` and `:206-207` it means `cert_eps (kim_biased_cert R idx)`; at `:123`, `:168` and `:199` "the one-cut bundle's spectral number" means `sw_bound_eps (kim_biased_marginal_bound R)`. `kim_biased_proximity_eps_halfE` in the same file proves the first is twice the second. | The qualifier "bundle's" is the only thing separating them, and this is the first file in which both appear and are related by a lemma. `five_card_rows.v:547` already carries the unambiguous term for the second quantity: "The one-cut bundle's marginal bound is sqrt 5 over eighty", and `kim_biased_epsE`'s index line at `five_card_rows.v:148` reads "the one-cut bundle's marginal bound in closed form". Audit round 4's A1 raised exactly this collision in the neighbouring file. | At `:123`, `:168` and `:199` write "the one-cut bundle's marginal bound" for `sw_bound_eps (kim_biased_marginal_bound R)`, keeping "the spectral number" for `cert_eps`. Prose only; I re-read each of the three against the statement it sits above. The three pre-existing uses in `five_card_rows.v` at `:97`, `:579`, `:764` are stage A's and are left to the coordinator. |
| S4 | SHOULD | `STATUS-stageB.md:282-288` | D1: "The tree's pattern is `ExactWitness`/`ew_*`, `SpectralCert`/`sc_*`, `certify_spectral`, `spectral_tail`, `SpectralPayload`, `SpectralPropAt` ... and nothing in the tree's pattern contradicts them." | The tree's pattern in those four slots is the port literal's **first word**, not the whole literal: `SpectralDecay` gives `certify_spectral`, `spectral_tail`, `SpectralPropAt`, `SpectralPayload`, `SpectralCert`; `ExactIndependence` gives `certify_exact`, `exact_tail`, `ExactProp`, `ExactPayload`, `ExactWitness`. Stage B writes the whole literal: `certify_idealproximity`, `idealproximity_tail`, `IdealProximityPropAt`, `IdealProximityPayload`, `IdealProximityCert`. That is a departure, and it is a justified one, because the first word of `IdealProximity` is `ideal`, which is already a surface keyword of `pgg_tableau_syntax.v`, a field name `ipc_ideal`, and the head of `IdealFinite`. Only the sentence claiming there is no departure is wrong. | Replace the clause with: "the tree forms these four names from the port literal's first word, which for `IdealProximity` is `ideal` and is already the surface keyword, the `ipc_ideal` field and the head of `IdealFinite`; stage B therefore takes the whole literal, and stage A's E6 reserved it." Checked against `pgg_tableau.v:205-210`, `pgg_tableau_syntax.v` keyword list, and `STATUS.md:1075-1096`. |
| S5 | SHOULD | `STATUS-stageB.md:279` | "The index gained five lines and the Key results three." | Recounted by script against `history/pgg_tableau.v.7-before-stageB`: the Definitions index gained four lines (`:60`, `:73`, `:74`, `:85`) and Key results gained four (`:92`, `:97`, `:98`, `:99`). | "The Definitions index gained four lines and the Key results four." |
| S6 | SHOULD | `p8_spectral_relation.v:16-17` | "the recorded failure beside it says that replacing the certificate does not leave it the same." | The recorded failure is `Fail Definition idealproximity_prop_cert_free ... := ltac:(by [])`, and `STATUS-stageB.md:202` gives its decisive line as `Error: No applicable tactic.` A failed `by []` shows the two propositions are not convertible. It does not show they differ, since propositional extensionality would still equate logically equivalent ones. | "the recorded failure beside it says that the two are not convertible, so replacing the certificate is not free there as it is for the spectral arm." Checked against the `Fail` at `:69-72` and its recorded error line. |
| N1 | NOTE | `p1_joint_law_distance.v:33` | Header index continuation line is 79 bytes; every other boxed line in the probe is exactly 80. | Byte count by script. The line is `(*                             the uniform laws                              *)`. | Add one space before the closing `*)`. This is the only width defect in the eleven stage B files; the only lines over 80 bytes are `pgg_tableau_syntax.v:329`, `:367`, `:398`, the three known ones that are byte-identical to `manifest/pgg_tableau_syntax.v`. |
| N2 | NOTE | `STATUS-stageB.md:124-128` | Size table gives declarations 67 to 74 and lines 837 to 998. | My own script over the same two files gives 68 to 75 declarations (counting `Definition`, `Lemma`, `Record`, `Variant`, `Notation` at line start after comment stripping) and 836 to 997 lines (`wc -l` convention; 837/998 is the `split('\n')` convention, which counts the empty tail). Both deltas, +7 and +161, are right, the seven named declarations are exactly the new ones, and the four `match` arms are confirmed at `:230`, `:488`, `:802`, `:820`. | Either state the counting convention or use 68/75 and 836/997. Nothing in the argument turns on it. |
| N3 | NOTE | `p7_mutations.v:18` and `:26-33` | "Beside those, three recorded failures fix what a certificate may name." | The section "What a certificate may name as its ideal" holds four `Fail` blocks (`:154`, `:169`, `:175`, `:184`). Three of them are about the proximity certificate and are the three the sentence describes; the fourth, `kim_biased_spectral_from_centi`, is the converse at the spectral arm and appears nowhere in the header. The file's Definitions index also omits the `Fact five_card_singleton_below_threshold` at `:85`. | Add to the header after the second paragraph: "A fourth failure runs the same mutation at the spectral arm, so the two arms are rejected by one coordinate." Add the `Fact` to the index. |
| N4 | NOTE | `pgg_tableau_syntax.v:17-28` and the banner at `:129` | Both stay true: the file has exactly two typed builders, `obs_payload` at `:136` and `mk_spectral` at `:150`. | Verified by reading the whole builders section. But neither the header paragraph nor the banner says why the third arm has none; the reason lives only in the notation comment at `:386-389`. A reader of the header alone, now told there are three arms, expects three builders. | Add to the header paragraph, after the `mk_spectral` sentence: "The proximity rule takes its certificate whole, because four of its five fields are terms of the instance and the fifth is the number, so a builder would display the plumbing." That is the notation comment's own sentence, re-read against `IdealProximityCert`'s five fields. |
| N5 | NOTE | `p8_spectral_relation.v:21-24` | The two index entries sit inside the prose block with no `Lemmas:` or `Key results:` label, unlike every other file of the probe. | Compared with `p1:24`, `p4:28`/`:35`, `p7:26`/`:30`, `p9:17`/`:21`. | Insert a blank comment line and a `(* Lemmas: *)` label before `:21`. |

## Rename table

Offered, not demanded: the long form is stage A's E6 reservation and the choice
belongs to the coordinator. Recorded here because the brief asks whether
`certify_proximity` and `proximity_tail` fit better, and the answer needs
evidence rather than an opinion.

| old | new | reason | precedent in the tree |
|---|---|---|---|
| `IdealProximityCert` | `ProximityCert` | the discriminating word of the literal; `Ideal` is not discriminating here | `SpectralCert` for `SpectralDecay`, `manifest/pgg_tableau.v:131` |
| `MkIdealProximityCert` | `MkProximityCert` | follows its record | `MkSpectralCert`, `manifest/pgg_tableau.v:133` |
| `ipc_*` | `pc_*` | initials of the record name, the rule D1 states | `sc_*` for `SpectralCert`, `ew_*` for `ExactWitness` |
| `IdealProximityPropAt` | `ProximityPropAt` | ditto | `SpectralPropAt`, `manifest/pgg_tableau.v:331` |
| `IdealProximityPayload` | `ProximityPayload` | ditto | `SpectralPayload`, `manifest/pgg_tableau.v:526` |
| `idealproximity_tail` | `proximity_tail` | ditto | `spectral_tail`, `manifest/pgg_tableau.v:561` |
| `certify_idealproximity` | `certify_proximity` | ditto | `certify_spectral`, `manifest/pgg_tableau.v:592` |
| `certify_idealproximity_armE` | `certify_proximity_armE` | ditto | `certify_spectral_armE` |
| `idealproximity_ceiling`, `idealproximity_reading_le` | `proximity_ceiling`, `proximity_reading_le` | ditto | as above |

`IdealProximity` and `IdealProximityArm` are **not** renamed: the first is the
surface literal of `s certify IdealProximity c`, and the second is stage A's
D1 rule, the surface literal plus `Arm`.

Verified, not argued. I built a renamed copy of the whole probe at
`<scratchpad>/extB_naming/ren` by exact-token substitution and compiled all
fourteen `.v` files of the probe's `_CoqProject` order that carry mathematics:
`p1` rc=0 5.7 s, `pgg_tableau` rc=0 13.3 s, `pgg_tableau_syntax` rc=0 4.5 s,
`pgl27_rows` rc=0 10.5 s, `five_card_rows` rc=0 4.6 s, `s5_rows` rc=0 4.0 s,
`psl211_rows` rc=0 5.5 s, `t0_sampled_branch` rc=0 3.8 s,
`t0_sampled_branch_pgl27` rc=0 4.4 s, `p4` rc=0 11.2 s, `p8` rc=0 3.8 s,
`p9` rc=0 3.9 s, `p7` rc=0 3.8 s, `g2` rc=0 3.8 s. Every recorded `Fail` still
fails, since the files compile. None of the fourteen proposed names occurs as
any token in any of the 210 production `.v` files.

`view_proximity_of` is **correct as it stands** and should not be drawn into
the rename. The reader slot in this tree does not carry the arm's word: it
carries the word for what the reader shows. `view_secrecy_of` is the exact
arm's and `view_indist_of` is the spectral arm's, and neither is `view_exact_of`
or `view_spectral_of`. `view_proximity_of` follows that convention, its comment
at `pgg_tableau.v:923-926` is true of the declaration at `:927` (the three names
are one term, `proj2 (published_thm r)`, and the proposition is selected by
`PortProp`'s match on the port), and the addition is warranted.

## What passed

Checked and clean, with the evidence:

- **Barred vocabulary.** No `apex`, no `gate`/`gates`/`gated`/`gating`, no
  `posit`/`posits`/`posited`/`positing`, and no capital-L-digit-one token, in
  any of the nine stage B `.v` files or in `STATUS-stageB.md`. Scanned by
  regular expression, case-insensitive, substrings in other words excluded.
- **Every back-quoted Rocq identifier in `STATUS-stageB.md` exists.** Checked
  mechanically against the token sets of the frozen probe and of all 210
  production `.v` files, dots split. The only non-matches are file names
  (`g2_keyword_measure.v`, `_CoqProject`) and suffix fragments (`_armE`, `Arm`,
  `ew_`, `sc_`), none of which is an identifier claim.
- **The three key statements are verbatim.** All three fenced blocks of
  `STATUS-stageB.md` occur in `pgg_tableau.v` modulo whitespace.
- **The recorded `Fail` list is complete.** 30 `Fail` sentences across the
  probe; 9 new (7 in `p7_mutations.v`, 2 in `p8_spectral_relation.v`), 6 named
  as re-read, 11 named as untouched, 4 cross-instance in the two T0 files.
  9+6+11+4 = 30.
- **No self line-number citation** in `STATUS-stageB.md`.
- **The compile table is plausible.** The main session's own `-time` logs give
  `p1` 4.0 s, `pgg_tableau` 13.9 s slowest sentence 4.16 s, `p4` 12.1 s slowest
  3.53 s, `assumptions_report_stageB` 24.7 s slowest 2.06 s, against the note's
  4.3 / 13.9 / 11.8 / 24.4. `assumptions_report_stageB.v` holds exactly 35
  `Print Assumptions`, as the note says.
- **D2 is accurate.** Every one of the 30-odd production line citations in D2
  was opened and read: `manifest/pgg_tableau.v:610`, `:614`, `:622`, `:628`,
  `:50`, `:149`, `:186`, `:243`, `:365`, `:624`;
  `manifest/pgg_tableau_syntax.v:377`, `:60`, `:68`, `:73`, `:78`;
  `instances/kim2025/five_card_rows.v:59`, `:392`, `:451`, `:598`, `:608`;
  `instances/kim2025/five_card_exec.v:733`, `:745`;
  `manifest/pgg_analysis_manifest.v:1943`, `:1945`, `:1947`;
  `instances/pgl27/pgl27_rows.v:273`, `:284`, `:298`, `:574`;
  `instances/s5/s5_rows.v:278`; `instances/psl211/psl211_rows.v:198`;
  `instances/pgl27/pgl27_mixing.v:1077` and `:1100`;
  `instances/psl211/psl211_mixing.v:577` and `:601`;
  `lib/var_dist_supp.v:51`. Every one says what D2 says it says.
- **The only production name collision is disclosed.** Of the 49 names stage B
  writes, exactly one, `var_dist_prodR`, collides with a production
  declaration, and it is the `Local Lemma` pair D2 item 7 already names.
- **D1's homes are safe.** The dependency closure of
  `instances/psl211/psl211_endpoints.v` is 35 files and contains none of
  `lib/var_dist_supp.v`, `manifest/pgg_tableau.v`,
  `manifest/pgg_tableau_syntax.v`, `instances/kim2025/five_card_mixing.v`,
  `instances/kim2025/five_card_rows.v`,
  `instances/kim2025/five_card_analysis.v`,
  `manifest/pgg_analysis_manifest.v`. No proposed home would force that file to
  rebuild.
- **The five fix-4 items are applied as specified.** A1 at
  `five_card_rows.v:825-831`, A5 the swap at `t0_sampled_branch.v:119-122`, A7
  the three arm-counting sentences, A8 at `five_card_rows.v:794-797`, A9 at
  `five_card_rows.v:737-743`. All are within 80 bytes. After the A5 swap the
  statement reads `published_at five_card_row_uniform_branch = published_at
  five_card_row_uniform_branch_ideal`, mirroring
  `t0_sampled_branch_pgl27.v:115-118`; the docstring above it ("The second
  continuation holds that same coordinate") and the header index line at
  `t0_sampled_branch.v:36-38` are both still true of it, because the sentence's
  subject is the second continuation and the equation still places the shared
  coordinate on the other side.
- **G2.** The new notation at `pgg_tableau_syntax.v:390-392` carries
  `at level 90, left associativity, c at level 0`, byte-identical in its
  parameters to the `certify SpectralDecay` rule at `:383-384`. The keyword
  measurement is repeated for each word that could be new:
  `Check IdealProximity.`, `Check IdealProximityCert.` and a binder
  `idealproximity_stays_bindable (IdealProximity : nat)` in
  `g2_keyword_measure.v:48-58`, all in a file that requires the surface. The
  nineteen-keyword count is unchanged and the reason given is right:
  `IdealProximity` follows the literal `certify`.
- **G3 header sentences.** "There are six statements" is right: `dealt_step`,
  `execute_step`, `sample_step`, `certify_exact`, `certify_spectral`,
  `certify_idealproximity`. The banner over the records is now "The security
  witnesses of the arms". All five new index entries gloss their declarations
  correctly. The F4 rewrites of stage A are present in the probe copies
  (`five_card_rows.v:59`, `:468`, `pgl27_rows.v:673`).
- **Probe hygiene.** No file under `lib`, `protocol`, `groups`, `security`,
  `smc`, `reconstruct`, `instances`, `manifest` or `legacy` mentions
  `tableau_ext_probe`. The probe's `_CoqProject` order is a dependency order:
  every `From tableau_ext_probe Require Import` names a file strictly earlier
  in the list. File names track the ledger rows they test.
- **Statement-comment hygiene.** No status marker, effort estimate, "key
  lemma", "headline", "used by", `[identifier]` bracket, fix-pass or audit
  narration in any stage B statement comment. Proof strategy is confined to
  non-rendered `(* *)` comments (`p4:266-267`, `t0_sampled_branch.v:101-104`).
  The carrier convention is per-file and matches production: `pgg_tableau.v`
  uses `(* *)` as `manifest/pgg_tableau.v` does, the instance-level probe files
  use `(** *)` as `instances/kim2025/five_card_rows.v` does.
- **One word per concept.** "proximity" throughout, never "closeness"; "reading",
  "run argument", "the number", "arm", "identification", "ideal", "actual",
  "model" used as stage A settled them; "coalition below the (privacy)
  threshold" in the framework files and "fewer than two seats" at the instance,
  which is the restatement and not a drift. The one real collision is S3.
- **`IdealProximityCert`/`ipc_*` against the tree.** The field prefix rule D1
  states, initials of the record name, holds: `ExactWitness`/`ew_`,
  `SpectralCert`/`sc_`, `IdealProximityCert`/`ipc_`. The record's comment at
  `pgg_tableau.v:171-181` names all five fields, their attack-model position
  and the coordinate the record refuses to hold, and is accurate about
  `ipc_secret`'s carrier being `ew_secretT ipc_witness`, except for S2.

## Verdict

**GO**, conditional on B1.

The names, the record, the arm plumbing and the index may be folded into the
spec and carried by stages C and D as they stand. B1 must be fixed first,
because it is a false mathematical claim in a rendered statement comment and in
the note, and it would be carried verbatim into the spec; the fix is two
sentences and needs no compile. S1 to S6 should be applied in the same pass and
are all prose. N1 to N5 may ride with them.

The rename table is offered and not required. If the coordinator takes it, the
evidence that it compiles is above; if not, S4 alone repairs the record.

## What I did not check

- The mathematics of the proofs. Whether `idealproximity_tail`,
  `kim_biased_proximity_close`, `var_dist_own_marginals` and
  `idealproximity_reading_le` prove what their statements say is the soundness
  audit's question, not this one. I checked only that each comment describes
  the statement it sits above.
- The axiom scan. I read `STATUS-stageB.md`'s account of the 35
  `Print Assumptions` blocks and confirmed the block count, but I did not rerun
  `assumptions_report_stageB.v` or re-scan its output.
- The recorded `Fail` error lines. I confirmed the list is complete and that
  every named failure exists in the file the note assigns it to. I did not
  recompile any sentence with its `Fail` removed to reproduce the decisive
  line, except through B1's own experiment.
- `instances/psl211/psl211_endpoints.v`, per the brief. I computed its
  dependency closure from source text without opening it.
- Stage A's own names beyond what stage B touches. The three pre-existing uses
  of "the bundle's spectral number" in `five_card_rows.v` are noted under S3 and
  left where stage A put them.
- The renamed copy's `assumptions_report.v` and `assumptions_report_stageB.v`,
  which print and prove nothing; the other fourteen files were compiled.
