# Adversarial audit of fix pass 1, landing 1 of the Tableau extensions

Read-only. Commits 16066cd to d737a46. No file of the repository was edited
except this one, and nothing was compiled: every verdict below is read off a
declaration's text in the frozen staged tree, and anything that would need a
kernel is marked "needs a compile".

## Verdict

**NO-GO.** One MUST and four SHOULDs, all on comment text, none on code. The
code of the pass is clean: the four new `_armE` lemmas are well-formed, their
header entries are exact, the `landing_fidelity.v` ascriptions are at the same
statements, and the four `Print Assumptions` lines are in the right block.
Completeness is clean too: every MUST and SHOULD of the two audit reports is
either applied or declined with a reason, nothing vanished silently, and no
changed passage in the diff maps to no finding.

The MUST is the last clause of the new header paragraph of
`manifest/pgg_tableau.v`. It says a *law* is excluded where the compiled
theorem excludes a *certificate*, and the difference is the certificate's
`ic_Hd` field, which is load-bearing in the proof.

## Findings

| id | grade | file:line | quoted text | problem, with the declaration's type quoted | replacement |
|---|---|---|---|---|---|
| F1 | MUST | `staged/manifest/pgg_tableau.v:50` | "and at some models no law satisfies both below a positive number." | The compiled evidence is `psl211_alldecks_no_small_eps_cert` (`staged/instances/psl211/psl211_reading_constancy.v:703`), whose statement is `forall (R : realType) (cert : IndistinguishabilityCert (psl211_alldecks_sample R)), sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert) < (#|pgg_G psl211_M|%:R)^-1 -> False`. It quantifies over a **certificate**, not a law, and its proof is `apply: (@psl211_alldecks_constancy_false_close R (ic_ideal cert) (sw_bound_eps (ic_b cert)) (psl211_alldecks_cert_ideal_close cert) Heps)`, where `psl211_alldecks_cert_ideal_close` is proved by `etrans (ic_Hd cert) (psl211_alldecks_cut_distE R)`. So a third field, `ic_Hd : sw_rho_dist ic_b = sa_cut_dist sa`, is what turns "close to the bound's own law" into "close to the group-uniform law", and only then does the exclusion follow. The sentence's preceding clause measures against "that bound's own law", and `ic_b : ShuffleMarginalBound R (instance_M A)` is an instance choice, so with `ic_Hd` dropped the bound's own law is unconstrained and no exclusion follows. As written the clause claims a law-level exclusion the tree does not have. | "and at some models no certificate meets both below a positive number." (one word; "certificate" carries `ic_Hd`, and the quantifier then matches the theorem's) |
| F2 | SHOULD | `staged/manifest/pgg_tableau.v:41-43` | "at an ipc_ideal that is the row's own adapter, with ipc_secret that adapter's witness's own secret, ipc_close compares one distribution with itself and holds at the number zero" | The verdict on `ipc_close` is TRUE and checks out: `ipc_close : forall C, (#|C| < profile_k …)%N -> var_dist (fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u), ipc_secret u)) (sa_sampleP sa)) (fdistmap (fun u => (static_coalition_obs C (ipc_ideal.(sa_arg) u) (ipc_ideal.(sa_cut) u), ew_secret ipc_witness u)) (sa_sampleP ipc_ideal)) <= ipc_eps` (`:219-229`). Under `ipc_ideal := sa` and `ipc_secret := ew_secret ipc_witness` the two sides are the same term, at every `C` below the threshold, since `C` occurs identically on both sides; `var_dist X X <= 0` holds. The defect is the subject switch: the sentence opens on `IdealProximityPropAt`, whose right side is `(fdistmap (sa_coalition_view … (ipc_ideal cert) 0 C) (sa_sampleP (ipc_ideal cert))) `x (fdistmap (ew_secret (ipc_witness cert)) (sa_sampleP (ipc_ideal cert)))` (`:496-499`), a **product of two marginals**, and closes on `ipc_close`, whose right side is a **joint law**. Those are not the same statement, which is what the pass's own `landing_idealproximity_propE` was added to record. A reader carries "holds at the number zero" back to the row's published proposition. | "… ipc_close's two sides are one term and the field holds at zero." (keeps the field as the subject of the verdict) |
| F3 | SHOULD | `staged/manifest/pgg_tableau_syntax.v:392-393` | "The proximity rule takes one certificate whole, as the input-indistinguishability rule does, and has no builder." | Literally true under the parse that makes "the proximity rule" the subject of "has no builder". False under the parallel reading a reader takes, because the input-indistinguishability rule **does** have a builder, nine lines below: `Notation "s 'certify' 'InputIndistinguishability' 'at' R idx b 'tied' 'by' Hd 'ideal' u 'mixing' 'by' Hc 'invariant' 'by' Hk" := (s ;;; certify_indistinguishability of (mk_indistinguishability …))` (`:402-408`), and the same file's header calls it one of the two builders: "Two typed builders carry the work … mk_indistinguishability takes the five components of a certificate separately" (`:17`, `:22-27`). | "The proximity rule takes its certificate whole and has no builder, where the input-indistinguishability rule has both this form and the five-clause builder below." |
| F4 | SHOULD | `staged/manifest/pgg_tableau.v:485-486` | "so conclude can state a finished row at any number at or above it, the one a paper cites among them" | `it` resolves to the nearest noun, "The bound [that] is a parameter", which is `c` itself, so the clause reads circularly. The intended referent is the certificate's own number: `ConcludePayload`'s proximity branch is `IdealProximity cert => ipc_eps cert <= odflt (ipc_eps cert) (c R)` (`:863`). The parallel sentence one arm up does have a referent, "at any number at or above **that sum**" (`:451`), because "the certificate's own sum" is named in the clause before it. | "so conclude can state a finished row at any number at or above ipc_eps, the one a paper cites among them" |
| F5 | SHOULD | `staged/manifest/pgg_tableau.v:908-909` | "conclude's target is computed by the framework from that coordinate, this one's is supplied." | `that coordinate` has no antecedent: the comment's only preceding noun phrase is "a row … as a proposition its caller writes out" (`:907`). The word is also overloaded in this very file: it names the `Reprice` at `:466`, `:508`, `:512`, `:926` and `:931`, and the dependent bind's stack index at `:306` ("stack coordinate"), `:583-584` ("the incoming coordinate", "before the coordinate is known") and `:594` ("a growing coordinate"). Declaration: `Definition restate (Q : Prop) (q : StackAt AnalysisBridged) (pf : StackProp AnalysisBridged q) (p : RestatePayload Q q) : RestatedTableau Q`, against `Definition conclude (c : Reprice) …` whose target is `BridgedProp c`. | "conclude's target is computed by the framework from the row's Reprice, this one's is supplied." |
| F6 | SHOULD | `staged/instances/pgl27/pgl27_rows.v:39-41` | "Two further things stay outside the programs: the word row's conclusion at 2^-39, which moves a number and proves nothing new about a coalition, and the two bridge lemmas …" | The conclusion at 2^-39 is a **line of a program**: `Definition pgl27_row_word39 : PublishedRowAt pgl27_reprice39 := pgl27_dealt sample pgl27_word_family certify InputIndistinguishability pgl27_word_cert |> conclude pgl27_reprice39 by (fun R _ => ssr_ext.eqW (pow2_split R)) |> publish IdealFinite BaselineClassicalOnly` (`:424-429`), written in the same surface as every other statement, and the same paragraph opens "No line of a program is a theorem about this instance" (`:28`). The two bridge lemmas genuinely are outside. The intended referent is the two programs that publish the manifest's rows, named at `:23-26`. The same flaw stood before the pass ("the reprice of the word row's bound from 2^-40 + 2^-40 to 2^-39"), so it is carried forward, not introduced. | "Two further things stay outside the two programs that publish the manifest's rows: the word row's conclusion at 2^-39, which moves a number and proves nothing new about a coalition, and the two bridge lemmas …" |
| F7 | NOTE | `landing_fidelity.v:81`, `:85` | "The proposition the proximity arm publishes, restated by unfolding"; "a different statement from the ipc_close field restated above" | The pass removed `restate` from four sites of `pgg_tableau.v` (naming M5) because `restate` is a terminal, `Definition restate (Q : Prop) … : RestatedTableau Q` (`:910`), distinct from `conclude`. The two new fidelity comments use the word in its loose sense. **No action**: the file already used it that way before the pass, at `:60` ("The distance field, restated in full") and `:182` ("The obligation of conclude, restated by unfolding"), so the new text follows the file's own convention, and the file is a probe instrument and not staged text. Recorded only so that the word is not carried into staged text later. | none |
| F8 | NOTE | `staged/manifest/pgg_tableau.v:466`, `:508`, `:512`, `:926`; `staged/instances/psl211/psl211_reading_constancy.v:689` | "when its coordinate names none"; "The coordinate that names nothing"; "at a given coordinate"; "a row whose coordinate names no number"; "at its own coordinate c" | The owner's ruling (STATUS "Declined", soundness S8 superseded) selects "coordinate" for `Reprice`, and `:931` already used it that way before the pass, so the choice is settled and is not reopened here. Recorded because the word carries a third sense in the staged tree that the ruling did not see: "the three coordinates each certified program publishes" (`staged/instances/kim2025/five_card_rows.v:146`, `:685`, `:698`) and the tuple coordinate of `s5_rows.v:21`, `:370`, `:382` and `psl211_reading_constancy.v:20`, `:76`, `:253`, `:526`. With F5's dangling demonstrative fixed the remaining sites each have a possessive that disambiguates them. | none required; F5 removes the one site with no possessive |
| F9 | NOTE | `staged/instances/kim2025/five_card_rows.v:163-164` | "five_card_inv50_split == the identity the one-cut row's terminal discharges" | Direction reversed. `Fact five_card_inv50_split (R : realType) : (1 / 50 : R) + 1 / 50 = 1 / 25` is what **discharges** the terminal's obligation, read through `eqW`: the row is `… |> conclude five_card_reprice_inv25 by (fun R _ => ssr_ext.eqW (five_card_inv50_split R))` (`:865-866`), and the obligation is `cert_eps cert <= odflt (cert_eps cert) (c R)` (`pgg_tableau.v:862`). A terminal does not discharge an identity. | "five_card_inv50_split == the identity that discharges the one-cut row's terminal" |
| F10 | NOTE | `landing_fidelity.v:387-391` | `Lemma landing_pgl27_branch39_armE … Proof. exact: erefl. Qed.` | `staged/instances/pgl27/pgl27_rows.v` has no `pgl27_row_word_branch39_armE`: the only `branch39` occurrences there are the index entry `:59` and the definition `:491`. So this is the one new fidelity lemma that proves a fact rather than ascribing a staged one, and the branch row's arm is therefore checked only in the probe's instrument and never reaches `Print Assumptions`, whose Kim and PGL(2,7) blocks name staged lemmas only (`:402-448`). `pgl27_row_word39_armE` is staged and printed. Worth carrying to landing 2 rather than fixing here. | none; record for landing 2 |

### On the four new `_armE` lemmas (remit 5)

Statements are well-formed copies of the pattern of
`pgl27_rows.v:447-451`, with the row name substituted in all three positions
(the `published_at` inside the index binder, the `security_arm_of` subject, and
nothing else):

- `five_card_row_repeated_indistinguishability_armE` (`five_card_rows.v:656-662`)
- `five_card_row_biased_indistinguishability_armE` (`:667-673`)
- `five_card_row_repeated39_armE` (`:826-830`)
- `five_card_row_biased_inv25_armE` (`:883-887`)

All four conclude `= InputIndistinguishabilityArm`, which is the right
constructor: each row is written `certify InputIndistinguishability …`, and
`certify_indistinguishability_armE` with `conclude_armE` and `publish_armE`
(`pgg_tableau.v:1004`, `:1028`, `:1039`) is what carries that out to the
published row.

They close by `exact: erefl` where the staged `pgl27_row_word39_armE` closes by
`by []`. This is a deliberate deviation, not a copy error: STATUS records the
measured reason and the project memory records `by []` hanging on
`published_at` equations across `conclude`. The pgl27 line is pre-existing and
untouched.

Header index entries are present and exact, at the file's 80-column box, with
the two certified programs sharing one gloss and the two concluded rows sharing
another (`five_card_rows.v:138-143`). `landing_fidelity.v:240-266` ascribes each
at the identical statement, binder for binder, with `Proof. exact:
<staged name>. Qed.` Four `Print Assumptions` lines are added in the Kim block,
in the same order (`:435-438`). That the assumptions come out at the three
classical axioms of `boolp` is STATUS's report and **needs a compile** to
confirm; the main session's rc=0 covers the compile, not the axiom set.

### Deviations the prover recorded (remit 2)

Every deviation in STATUS "Fix pass 1" was checked against the declaration. All
are right, and in four cases the deviation is the better text:

- **naming M1 / soundness S3**, `five_card_pow2_39_split`. Neither proposal
  taken. The written text is true against the single use: `kim_centi_cert_eps_lt`
  (`:737-744`) does `rewrite /cert_eps`, then `have -> : (2%:R : R) ^- 39 =
  2%:R ^- 40 + 2%:R ^- 40` by this identity, then `apply: ltrD; exact:
  kim_bound_centi`. So the identity does put the published constant into
  `cert_eps`'s `a + a` shape, and the two spectral terms are then compared one
  at a time. The prover's reason for dropping the soundness text, that it names
  the bounding lemma inside a statement comment, is right.
- **naming M5**, the four `restate` sites. The prover's reason is right on both
  counts: it is `publish` and not `conclude` that publishes
  (`Definition publish (a : AssumptionStatus) (c : Reprice) (q : StackAt
  AnalysisBridged) (pf : BridgedProp c q) (t : TransferStatus) :
  PublishedRowAt c`, `:933`), and the coordinate is a parameter of
  `Record PublishedRowAt (c : Reprice)` (`:920`) and not of a terminal. F4 and
  F5 are residue of two of these four rewrites, not of the ruling.
- **naming M6 / soundness S4**, `five_card_row_repeated39`. "kim_centi_cert_eps_lt
  is strict, so the number the row publishes is strictly above the number the
  certificate proved" is TRUE: `Lemma kim_centi_cert_eps_lt (idx : unit) :
  cert_eps (kim_centi_cert R idx) < 2%:R ^- 39` (`:737-738`), and the row's
  coordinate is `Definition five_card_reprice39 : Reprice := fun R => Some
  (2%:R ^- 39 : R)` (`:778`). "asserts … no more than that certificate did" is
  TRUE and is the right direction: the published proposition is
  `IndistinguishabilityPropAt cert (odflt (cert_eps cert) (c R))`, monotone
  upward in the number, so a larger number is a weaker claim. Moving the payload
  out of the docstring into `(* The terminal's payload is kim_centi_cert_eps_lt
  weakened by ltW. *)` is correct under the statement-comment rule, and the
  definition does read `by (fun R idx => Order.POrderTheory.ltW
  (kim_centi_cert_eps_lt R idx))` (`:792`).
- **naming S12**, "the direct computation". Right substitution: `ExactWitness`'s
  `ew_indep` is stated on `fun u => static_coalition_obs C (sa.(sa_arg) u)
  (sa.(sa_cut) u)` (`pgg_tableau.v:173-176`), and `pgg_tableau.v` already calls
  that "the direct computation" at `:990`. This is what the exact arm asks for
  as an input, so "the exact arm asks for independence of the direct
  computation from a secret" is TRUE.
- **naming S13**, `five_card_inv50_split`. "equates … with" for "bounds … by" is
  the right repair: the Fact is an equality, `(1 / 50 : R) + 1 / 50 = 1 / 25`.
- **naming S7/S8 with soundness S5**, `psl211_reading_constancy.v`. The written
  plain comment is exact against the framework: `ConcludePayload`'s branch is
  `cert_eps cert <= odflt (cert_eps cert) (c R)` (`pgg_tableau.v:862`) and
  `PortProp`'s is `IndistinguishabilityPropAt cert (odflt (cert_eps cert) (c R))`
  (`:524`). The prover is right that the auditor's `cert c` does not typecheck,
  `c : Reprice` and the second argument is an `R`. The dropped last sentence
  ("The bound below … is therefore the obligation itself") is strategy and its
  content survives in the docstring above.
- **naming M4**, "premise every security arm states". TRUE for all three:
  `ExactProp` (`:429`), `IndistinguishabilityPropAt` (`:458`) and
  `IdealProximityPropAt` (`:491`) each state `(#|C| < profile_k (instance_profile
  A))%N`, as do `ew_indep`, `ic_const` and `ipc_close`. The old two-arm count
  was wrong once the third arm landed.
- **naming M3**, "the three certify statements' arm equations". TRUE: there are
  exactly three, `certify_exact_armE` (`:994`),
  `certify_indistinguishability_armE` (`:1004`) and
  `certify_idealproximity_armE` (`:1017`).
- **naming S6**, the S5 cross-reference. TRUE against
  `staged/instances/s5/s5_rows.v:66-71`: "Missing too, and for a reason no proof
  can remove, is the constancy of a coalition's reading of the ideal cut … no
  choice of ideal avoids it". So "the constancy an input-indistinguishability
  certificate asks for is false" is what that file records. It records it in
  prose and not as a compiled refutation, which the sentence does not claim.
- **soundness S9**, the index entry for `kim_biased_cert_exact`. "at the exact
  number one fiftieth" is TRUE modulo conversion: the row's terminal payload is
  `ssr_ext.eqW (five_card_inv50_split R)` at obligation `cert_eps
  (kim_biased_cert_exact R idx) <= 1 / 25`, which typechecks only if
  `sw_bound_eps (ic_b …)` converts to `1 / 50`. The file compiles, so it does.
- **naming M7**, the two pgl27 docstrings. "the same certificate, the same
  terminal at 2^-39 and the same two statuses as pgl27_row_word39" is TRUE
  token for token: both rows read `certify InputIndistinguishability
  pgl27_word_cert`, `|> conclude pgl27_reprice39 by (fun R _ => ssr_ext.eqW
  (pow2_split R))`, `|> publish IdealFinite BaselineClassicalOnly` (`:424-429`
  against `:491-495`), and `pgl27_word_sampled := pgl27_dealt sample
  pgl27_word_family` (`:487`) is the prefix of the first. F6 is about the header
  sentence, not these two.

### The findings declined (remit 2)

All three declines are acceptable.

- **naming N1 to N10.** The auditor recorded them as notes with no action, and
  they are notes.
- **soundness S8.** Superseded by the owner's ruling on the pending `Reprice`
  decision. Recorded once more as F8, because the ruling was made without the
  third sense of the word being on the table; no action is asked here.
- **naming S9 as written.** It asks for the arm equations to be deferred to
  landing 2; the brief's item E lands four of them here, so the finding is
  closed rather than deferred. The one it was about, `five_card_row_uniform_armE`,
  still stands at `five_card_rows.v:411` with its own index entry at `:132-133`.

### Completeness (remit 3)

Nothing vanished. Every finding of both reports is in STATUS "Fix pass 1",
applied or declined:

- soundness MUST: S1 (header paragraph), S2 (`landing_idealproximity_propE`).
- soundness SHOULD: S3 (with naming M1), S4 (with naming M6), S5 (with naming
  S7/S8), S6 (`landing_pgl27_branch39_atE`, `landing_pgl27_branch39_armE`, the
  existing `landing_pgl27_branch39_rowE` kept).
- soundness NOTE: S7 (STATUS tables), S8 (declined, superseded), S9 (applied),
  S10 (one blank comment line above the new paragraph and one below, verified in
  the diff context at `pgg_tableau.v:35` and `:46`), S11
  (`landing_view_proximity_of`).
- naming MUST: M1, M2, M3, M4, M5, M6, M7, all applied.
- naming SHOULD: S1 (folded into the header-paragraph section with soundness
  S10), S2, S3, S4, S5, S6, S7, S8, S9 (closed, see above), S10, S11, S12, S13.
- naming NOTE: N1 to N10 declined as notes.

### Unrequested changes (remit 4)

None. Every hunk maps to a finding or to the brief's item E:

| hunk | maps to |
|---|---|
| `landing_fidelity.v` `landing_idealproximity_propE` | soundness S2 |
| `landing_fidelity.v` `landing_view_proximity_of` | soundness S11 |
| `landing_fidelity.v` four `landing_five_card_*_armE` | brief item E |
| `landing_fidelity.v` `landing_pgl27_branch39_atE`, `_armE` | soundness S6 |
| `landing_fidelity.v` four `Print Assumptions` lines | brief item E |
| `five_card_rows.v:52` "the direct computation" | naming S12 |
| `five_card_rows.v:59-61` the S5 cross-reference | naming S6 |
| `five_card_rows.v:98-99` `kim_biased_cert_exact` entry | soundness S9 |
| `five_card_rows.v:138-143` four index entries | brief item E |
| `five_card_rows.v:163-165` the two split entries | naming M2 |
| `five_card_rows.v` two certified-program `_armE` | brief item E |
| `five_card_rows.v` `five_card_pow2_39_split` comment | naming M1, soundness S3 |
| `five_card_rows.v` `five_card_row_repeated39` docstring | naming M6, soundness S4 |
| `five_card_rows.v` two concluded-row `_armE` | brief item E |
| `five_card_rows.v` `five_card_inv50_split` comment | naming S13 |
| `pgl27_rows.v:39-41` header | naming S4 |
| `pgl27_rows.v` `pgl27_row_word39` docstring | naming M7 |
| `pgl27_rows.v` `pgl27_row_word_branch39` docstring | naming M7 |
| `psl211_reading_constancy.v:236` | naming M4 |
| `psl211_reading_constancy.v:689` | naming S7 |
| `psl211_reading_constancy.v:697-699` | naming S8, soundness S5 |
| `pgg_tableau.v:36-45` header paragraph | soundness S1, naming S1, S2, S3, S10 |
| `pgg_tableau.v` four `restate` sites | naming M5 |
| `pgg_tableau.v` `no_reprice`, `PortProp`, `restate` | naming S5 |
| `pgg_tableau.v` `publish_armE` | naming M3 |
| `pgg_tableau_syntax.v:259ff` paragraph break | naming S11 |
| `pgg_tableau_syntax.v:392-393` | naming S10 |

## Hunks checked and found correct

Every sentence the pass wrote or changed, walked hunk by hunk against the
declaration it describes.

**`manifest/pgg_tableau.v`, the new header paragraph.** Every clause but the
last two checks out.

- "The exact arm's and the proximity arm's propositions mention terms an
  instance chooses" — TRUE. `ExactProp … (w : ExactWitness sa)` mentions
  `ew_secret w` (`:432`, `:434`, `:438`, `:445`); `IdealProximityPropAt`
  mentions `ipc_secret cert`, `ipc_ideal cert` and `ew_secret (ipc_witness
  cert)` (`:494`, `:497-499`). Both records are instance-supplied.
- "a constant ew_secret satisfies ew_indep at every coalition" — TRUE and
  unchanged from the first pass. `ew_indep : forall C, (#|C| < profile_k …)%N ->
  sa_sampleP sa |= (fun u => static_coalition_obs C …) _|_ ew_secret`
  (`:173-176`); a constant random variable is independent of every other. Not
  compiled anywhere in the tree, and it does not need to be: it is a claim about
  what an instance may field.
- "IndistinguishabilityPropAt mentions neither ic_ideal nor a secret, only the
  readings of the model's own cut law at two run arguments and the number
  bounding their distance, so ic_ideal is a means of proving it" — TRUE, and the
  strongest sentence in the paragraph. The body is `forall (C : …) (x x' :
  ex_inputT E), (#|C| < profile_k …)%N -> var_dist (fdistmap
  (static_coalition_obs C x) (sa_cut_dist sa)) (fdistmap (static_coalition_obs C
  x') (sa_cut_dist sa)) <= c` (`:456-461`), which does not use its `cert`
  parameter at all.
- "ic_close holds ic_ideal within the marginal bound's epsilon of that bound's
  own law" — TRUE, exactly: `ic_close : var_dist (sw_rho_dist ic_b) ic_ideal <=
  sw_bound_eps ic_b` (`:192`).
- "ic_const asks a coalition below the threshold to read it the same at every
  two run arguments" — TRUE: `ic_const : forall C, (#|C| < profile_k …)%N ->
  forall x x' : ex_inputT E, fdistmap (static_coalition_obs C x) ic_ideal =
  fdistmap (static_coalition_obs C x') ic_ideal` (`:193-197`).
- The two blank comment lines around the paragraph are one above and one below,
  as soundness S10 asked.

**`manifest/pgg_tableau.v`, the remaining comment edits.**

- `IndistinguishabilityPropAt`, "conclude can state a finished row at any number
  at or above that sum" — TRUE. `ConcludePayload`'s branch is `cert_eps cert <=
  odflt (cert_eps cert) (c R)` (`:862`), and `cert_eps cert = sw_bound_eps (ic_b
  cert) + sw_bound_eps (ic_b cert)` (`:470`) is the sum named. `conclude` and
  not `publish` is the terminal that names the number.
- `cert_eps`, "the number a row carries when its coordinate names none" — TRUE.
  `PortProp` reads `odflt (cert_eps cert) (c R)` (`:524`), and `no_reprice : =
  fun _ => None` (`:510`).
- `no_reprice`, "Every row that publishes the bound it accumulated carries it" —
  TRUE, and `StackProp AnalysisBridged = fun q => BridgedProp no_reprice q`
  (`:556`) is the default.
- `PortProp`, "at a given coordinate" — TRUE.
- `PublishedRow`, "what a row whose coordinate names no number publishes" —
  TRUE: `Notation PublishedRow := (PublishedRowAt no_reprice)` (`:928`).
- `publish_armE`, "the three certify statements' arm equations" — TRUE, three
  exist (`:994`, `:1004`, `:1017`), and `publish` is the last step
  (`Definition publish … : PublishedRowAt c`, `:933-937`).

**`manifest/pgg_tableau_syntax.v:259ff`.** Pure reflow. The two blocks are
word for word the text of the single block it replaces, with a blank comment
line inserted after "claims about one object rather than two." No claim
changed.

**`instances/kim2025/five_card_rows.v`.**

- The header's "the exact arm asks for independence of the direct computation
  from a secret, which the development states under the uniform cut and not
  under the biased one, and a conditional mutual information is not a variation
  distance" — TRUE, see the M7/S12 note above.
- `five_card_row_repeated39`'s docstring and its plain comment — TRUE, see the
  M6 note above.
- `five_card_inv50_split`'s comment — TRUE.
- `five_card_pow2_39_split`'s comment — TRUE against its single use.
- The four `_armE` docstrings. "a variation distance between the readings of the
  cut at two committed pairs, and not independence of the view from the
  conjunction of the committed bits" (`:650-655`) is the right contrast between
  `IndistinguishabilityPropAt` (`:456-461`) and `ExactProp` (`:428-445`). "The
  two Kim rows publish different manifest rows" (`:664-666`) is consistent with
  `five_card_row_repeated_indistinguishability_rowE` and
  `five_card_row_biased_indistinguishability_rowE` publishing
  `five_card_row_repeated` and `five_card_row_biased` respectively. "Concluding
  at a number at or above the certificate's own leaves the port where the
  certify statement put it" (`:822-825`) is TRUE via `conclude_armE` (`:1028`).
  "It carries the exact certificate where
  five_card_row_biased_indistinguishability_tableau carries the spectral one, so
  the two rows differ in the number they publish and not in what kind of fact
  they state about a coalition" (`:879-882`) is TRUE:
  `five_card_row_biased_inv25` reads `certify InputIndistinguishability
  kim_biased_cert_exact` (`:864`) against the other's `kim_biased_cert`.

**`instances/pgl27/pgl27_rows.v`.** Both docstrings TRUE (see M7 above); the
header sentence is F6.

**`instances/psl211/psl211_reading_constancy.v`.** All three edits TRUE.
"A row publishes odflt (cert_eps cert) (c R) at its own coordinate c" matches
`PortProp` (`pgg_tableau.v:524`) exactly; the plain comment matches
`ConcludePayload` (`:862`) and `PortProp` (`:524`) exactly.

**`landing_fidelity.v`.** `landing_idealproximity_propE`'s comment is TRUE
clause by clause: the left side of `IdealProximityPropAt` is the joint law of
the coalition's executed reading with the secret under the actual model
(`pgg_tableau.v:493-495`), the right side is `` `x `` of the ideal's two
marginals and not a joint law (`:496-499`), and `ipc_close`'s right side **is** a
joint law (`:225-228`), so the two statements differ. `landing_view_proximity_of`'s
comment is TRUE by inspection: `view_secrecy_of`, `view_indistinguishability_of`
and `view_proximity_of` are each `proj2 (published_thm r)` (`:956`, `:964`,
`:972`), so all three names are one term; only the one equation is compiled,
which is enough for the point the comment makes. `landing_pgl27_branch39_atE`'s
and `_armE`'s comments are TRUE, the first clumsily worded ("changes the data
the row carries in nothing").

## Mechanical scans

Run over the 208 added lines of the diff and over the seven staged files.

- **Meta narration** in the staged files' changed text: none. The words
  "renamed", "formerly", "now", "no longer", "probe", "stage", "landing",
  "audit", "fix", "withdraw", "deferred" and "TODO" appear in no added line of
  a staged file. The only hits are the eight `landing_*` lemma names of
  `landing_fidelity.v`, which is the probe's instrument and not staged text.
- **Proof strategy** is in plain `(* *)` comments and not in docstrings at both
  sites where the pass moved it: `five_card_rows.v:786` ("The terminal's payload
  is kim_centi_cert_eps_lt weakened by ltW.") and `pgl27_rows.v:419-421` (the
  `pow2_split`/`eqW` route). The pre-existing plain comments above
  `five_card_pow2_39_split` and `five_card_row_repeated39_atE` are untouched and
  correctly plain.
- **The project's banned vocabulary list**: no hit in any added line.
- **"indistinguishability"**: never abbreviated; no `indist`, no `ind.`, no
  `IID`. The hyphenated adjective "input-indistinguishability" is used
  throughout, matching the rest of the tree.
- **Line length**: every line of every staged file is at most 80 bytes except
  `pgg_tableau_syntax.v:334` (101), `:372` (90) and `:402` (128), which are the
  three notation string literals the brief exempts. The five_card header's new
  index entries are exactly 80, box-aligned.
- **"the sum of the absolute differences"** is written in full wherever the landing
  names that quantity (`pgg_tableau.v:478-481`), and no file writes the
  two-character abbreviation.
