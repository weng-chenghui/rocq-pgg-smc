# Extending the Tableau to hold what the repository has found

Date: 2026-09-19

Status: spec drafted, second version. The first version added constructors
where a `match` happened to exist. The user's direction of 2026-09-19 replaced
that: the Tableau presents what we have, so a finding it cannot hold is a
reason to extend it, and an extension is placed by what each phase means. The
probe starts when the batch of [[20260919-kim-spectral-arm-probe-design]] is
closed and an independent auditor has checked the placement below against the
real infrastructure. This is a probe batch. It edits no permanent file. A
landing is a separate batch and needs the user's decision.

Follows [[20260919-kim-spectral-arm-probe-design]] and
[[2026-09-19-062455-third-certify-arm-for-the-biased-row]].

## Problem

A Tableau program is where a row of the paper becomes one term. A reader who
stops at any line knows what has been proved there. The paper tells one story
about every instance: an ideal model with a uniform cut, which is private, and
an actual model with a biased cut, which is close to the ideal one and so
private up to a small number.

Four findings of the repository cannot be read off any program today.

1. **The ideal and the actual model are related.** At PGL(2,7) the exact row
   and the word row are two programs with no term between them. The ideal
   enters the word row as a bare law inside a certificate, `sc_ideal`, and not
   as the model of another row. At PSL(2,11) the situation is worse: the word
   model has no row at all. `SpectralPropAt` compares the readings at every
   two run arguments and takes no account of the law of the run argument. In
   the all-decks mode the run argument is the public deck description, and the
   reading depends on it even at a fixed chirality, so the proposition is false
   at any small number (`notes/probes/2026-09-19-psl211-sc-const/`, with its
   soundness audit: by a computed diagnostic, not a theorem, a certificate
   would have to publish at least $10/11$). Three seats nevertheless learn
   nothing about the chirality under the all-decks law. What is true, at every
   instance, is that the actual model is within a small distance of a model
   under which the coalition's reading is independent of the secret. In the
   dealer-dealt mode of PSL(2,11) the run argument is the secret alone and the
   constancy field fails for another reason, the group being 2-transitive and
   not 3-transitive. That mode has no private ideal model, so this finding is
   about the all-decks mode there.
2. **A bound in bits at the full reveal.** `five_card_row_biased_leak_bound`
   bounds a conditional mutual information and holds at every reveal. The file
   header of the Tableau says both arms speak only of a coalition below the
   threshold.
3. **A published number that bounds the proved one.** The obligation of
   `conclude` is an equality. A row that proves $2\sqrt5\,(1/80)^7$ cannot
   publish $2^{-39}$ without choosing a weaker epsilon inside its certificate,
   which hides the number actually proved.
4. **Negative findings.** `psl211_fixed_deal_view_dep` shows that a dealer
   laying one fixed deck lets three seats tell the chiralities apart. The
   manifest declares a transfer status `NegativeTransfer` for a theorem of that
   kind, and no row uses it, because no statement of the Tableau can carry a
   refutation. A recorded `Fail` says that one term does not typecheck, which
   is not the same thing.

## Placement by phase

The phases, from the header of `manifest/pgg_tableau.v`. Each statement takes
the data and the proposition accumulated so far and one payload, and raises the
row one level.

| Phase | What the row holds there | What a line at this phase may add |
|---|---|---|
| Algebraic, Executable | the algebra, the run mode, the fuel | run data |
| Observed | the three run facts, run correctness | facts about the interpreter |
| Sampled | a probability model, and the executed reader identified with the static one at every set of seats | a model and its link to the run |
| AnalysisBridged | one security claim about that model | a claim about what an observer learns |
| terminals | the published number, the chosen proposition, the manifest row | nothing about the coalition |

Each finding is placed by asking what it is a fact about.

**Finding 1 is a fact about two models, so it is a step between two rows.** The
ideal model is already a row: the exact program of the instance, finished at
`AnalysisBridged`. The actual row should consume it. The proposed statement
takes, as its payload, a finished exact row over the same observed prefix and
a bound on the distance between the two sampled laws, and concludes that under
the actual model the coalition's reading is within a stated multiple of that
bound of being independent of the secret. The types force the two rows to
share the algebra, the run and the observed execution, which today is a lemma
beside the programs (`five_card_row_repeated_prefixE`). The accumulated number
starts at zero on the exact row, grows by the distance at this step, and is
only restated at the terminal. This is the paper's sentence as one term. It is
not a third constructor beside the other two: it is the missing edge from the
exact arm's rows to the rows of actual models. Whether the existing spectral
arm remains necessary beside it is a question the probe answers (F1.6).

**Finding 2 is a security claim with a wider observer, so it sits at
`AnalysisBridged` and must say who the observer is.** The `Sampled` phase
already identifies the executed reader with the static one at every set of
seats, with no threshold, so the full reveal is an observer the row already
knows. The threshold enters only in the arms. The leakage claim is therefore a
claim of the same phase whose scope is every reveal and whose unit is bits
given the output. Two design consequences follow from the phase and are part
of the probe. A row may have two security claims with different observers,
which means the security phase must be able to adjoin a second claim: the
proposition there is already a left-nested conjunction, and the data slot is
what holds exactly one claim today. And a published row has to show which
claims it carries, or a leakage bound reads as a coalition result.

**Finding 3 is about the published number, so it is the terminal's.**
`conclude` already leaves the data and the claims untouched and moves only the
real. Publishing an upper bound is the same act, and it is sound because every
proposition that carries a number is monotone in it. The obligation becomes an
inequality.

**Finding 4 is a security claim about a model, with the opposite sign.** It
sits at `AnalysisBridged`: a model, a set of seats below the threshold, and a
proof that the reading is not independent of the secret. It publishes a row
whose transfer status is the manifest's `NegativeTransfer`. It needs a row to
stand on, which for the fixed-deck dealer means a model family for that dealer.

## Structure

`Operation:` a statement maps the data and the proposition at one level, with
one payload, to the data and the proposition one level up; from `Sampled`
upwards the proposition grows by one conjunct on the right. The invariant is
that a reader who stops at a line knows exactly what is proved there, and that
the number a row publishes is never below the number it proved.

`Monad:` a parameterised monad indexed by the completion level before and after
a statement, as today, now also graded by the accumulated bound: zero on an
exact row, plus the model distance at the step of finding 1, weakened upwards
at the terminal. The grade is carried propositionally, as the real in the
security claim, and not in the type. The unit and bind laws of `tableau_bind`
are untouched. The step of finding 1 is not a bind: it takes a finished row as
a payload, so rows form the objects of a small category and that step is an
arrow from the ideal row to the actual one.

`DSL:` the Tableau is the DSL. The four findings are four gaps of
expressiveness: a relation between two rows, a second observer, a weakened
number, and a refutation.

## Flow

The running value is the bound the row would publish.

```
flow actual_row(instance)                                           // bound: none yet
object   ideal   := the instance's exact program, AnalysisBridged   // 0
object   prefix  := the observed execution the two rows share       // 0, shared by type
step     sample actual_family                                       // 0
step     certify close to ideal by model_distance                   // k * eps, k found by the probe
step     also certify leakage by leak_bound          (Kim biased)   // k * eps, and a second claim in bits
terminal conclude at a number not below the bound                   // the number the paper cites
terminal publish IdealFinite                                        // the manifest row

flow refuted_row(psl211, fixed deck)                                // no bound
step     sample fixed_deck_family
step     certify dependence by psl211_fixed_deal_view_dep           // a refutation
terminal publish NegativeTransfer

outside  the manifest rows, the paper, every permanent file
```

Interfaces of the external components: the exact program of each instance
enters as a finished row; `pgl27_word_mixing`, `psl211_word_mixing` and the
cut-carrier distances of the Kim probe enter as the model distance, through a
lemma that the distance of two product laws with one common factor is the
distance of the other factors; `five_card_colour_view_leak_bound` enters as the
leakage payload; `psl211_fixed_deal_view_dep` as the refutation payload.
Assumptions invoked: none.

## Pinned carriers

- Finding 1, three instances, each over an abstract `R : realType`: the PGL(2,7)
  word family against `pgl27_row_exact_tableau`; Kim's biased and repeated
  families against `five_card_row_uniform_tableau`; and a PSL(2,11) word model
  on `psl211_inputT * pgg_gT psl211_M`, the uniform law on deck descriptions
  times `rho_from_words_weighted R 10 2 584 psl211_moves psl211_Wuni`, against
  `psl211_row_alldecks_tableau`. That last adapter does not exist in the tree
  and the probe builds it.
- Finding 2: `amf_sample kim_biased_family R tt`.
- Finding 3: the certificate `kim_centi_cert` of
  `notes/probes/2026-09-19-kim-spectral-arm/kim_spectral_rows_probe.v`, and the
  new rows of finding 1.
- Finding 4: `psl211_fixed_dealP` of `instances/psl211/psl211_models.v`.

## Claim ledger

| ID | Checkable claim | Passing evidence |
|---|---|---|
| F1.1 | Generic: if two laws on a sample space are within `eps`, the joint law of two readers under one is within `eps` of their joint law under the other; and two product laws with one common factor are as far apart as their other factors. | `Qed`, from `var_dist_fdistmap`. |
| F1.2 | Generic: if two readers are independent under the ideal law and the actual law is within `eps` of it, the actual joint law is within `k * eps` of the product of its own marginals. | `Qed`, with `k` found and reported. `k` is 2 or 3 according to whether the secret has the same marginal under both laws, and the probe says which holds at each instance and why. |
| F1.3 | The statement that consumes an exact row. | In a full copy of `pgg_tableau.v`: a payload made of a finished exact row and a model distance, a proposition about the actual model only, and a tail lemma ending in `Qed`. The types force the two rows to share the observed prefix. The probe reports how the shared prefix is expressed, and if the type cannot express it, the smallest reason why. |
| F1.4 | The actual models as programs of that shape. | PGL(2,7) word, Kim biased, Kim repeated and PSL(2,11) word each elaborate, each consuming its instance's existing exact program unchanged. |
| F1.5 | The claim is neither vacuous nor trivially true. | Each number is compared with `var_dist_le2`. A mutation with the exact row's independence removed must not give the tail. A mutation consuming another instance's exact row must be rejected by the types. |
| F1.6 | Relation to the spectral arm. | A compiled comparison. `SpectralPropAt` fixes two run arguments, the new proposition averages over the run argument. The probe states for PGL(2,7) and for Kim whether each proposition implies the other, with proofs or counterexamples, and therefore whether the spectral arm still presents something the new step does not. It removes nothing. |
| F2.1 | The leakage claim, its proposition and its statement. | Compiled in the Tableau copy. The claim has no threshold premise and names its observer as every set of seats. |
| F2.2 | The lemma the earlier note names as missing. | The reading indexed by a set of seats and the reading indexed by a list agree at the list that enumerates the set, and conditional mutual information does not grow through `five_card_colour_fill C`. Both `Qed`, or the smallest counter-probe. |
| F2.3 | A second security claim on one row. | The data slot of `AnalysisBridged` holds more than one claim, or a second statement adjoins one, whichever the probe finds keeps every existing program and projection compiling. Kim's biased row then carries the closeness claim and the leakage claim together. |
| F2.4 | A published row shows which claims it carries. | The probe reports what `publish` and `AnalysisPathRow` would need, and whether it can be done without editing the manifest record. It does not edit the manifest. |
| F3.1 | `conclude` with an inequality. | `port_reprice` ends in `Qed` by monotonicity, for every claim that carries a number. |
| F3.2 | A wrong number is still rejected. | Repricing below the proved bound is shown impossible by a compiled negation or a recorded `Fail`. `pgl27_row_word39_bare` still fails. |
| F3.3 | Kim's repeated row publishes $2^{-39}$ from the number it proved. | It elaborates with the certificate's epsilon left at the spectral number. |
| F4.1 | The refutation claim and its statement. | A payload made of a set of seats below the threshold and a proof that the reading is not independent of the secret, under the row's model. Compiled in the Tableau copy. |
| F4.2 | The fixed-deck PSL(2,11) dealer as a refuted row. | A model family for that dealer, a program ending in `publish NegativeTransfer`, the payload from `psl211_fixed_deal_view_dep`. If the landed theorem is stated on a carrier the row cannot use, the probe says what bridge is missing and does not force it. |
| F4.3 | A refuted row cannot be mistaken for a private one. | Its projections do not include `view_secrecy_of`, by type. |
| G1 | Every existing program still compiles after each extension. | Copies of `pgg_tableau_syntax.v`, `s5_rows.v`, `pgl27_rows.v`, `psl211_rows.v` and `five_card_rows.v` against the copy, after each of the four extensions in the order F3, F1, F2, F4. Every payload that had to change is listed with old and new text. |
| G2 | The surface syntax. | Each new statement has a notation in the copy of `pgg_tableau_syntax.v`, and the keyword measurement of that file's header is repeated for every new word: `Check` of each identifier the notation mentions still passes. |
| G3 | The header of `pgg_tableau.v` stays true. | The probe rewrites the header of the copy so that every sentence is true of the extended file: five statements become more, and "both arms speak only of a coalition below the threshold" is no longer the whole story. |
| D1 | Names and homes. | A proposed name and file for each declaration. Closures recomputed from `.Makefile.rocq.d`. `manifest/pgg_tableau.v` has five reverse-dependants and `manifest/pgg_analysis_manifest.v` seven, `pgg_tableau.v` among them. `psl211_endpoints` is in neither closure. Generic lemmas go to a new file under `lib/`, which needs a line in `_CoqProject`. |
| D2 | What each landing would make false. | For each extension, the header sentences and recorded `Fail`s in the six files that a landing falsifies, by file and line. |
| D3 | What the manifest pins. | The manifest pins each row's level and statuses with `Check (erefl : ...)` and names each row's theorems through the instance's analysis facade, which sits below the manifest. For each new program the probe lists the pins and header tables a landing changes and says where the instance theorem has to live to be named by the facade. The previous batch missed both points (`notes/probes/2026-09-19-kim-spectral-arm/soundness-audit-round2.md`, G1 and G4). |

## Cited objects

| Object | File | Required statement shape |
|---|---|---|
| `SecurityPort`, `ab_port`, `PortProp`, `exact_tail`, `spectral_tail`, `certify_exact`, `certify_spectral`, `RepricePayload`, `port_reprice`, `conclude`, `restate` | `manifest/pgg_tableau.v:149`, `:241`, `:363`, `:535`, `:561`, `:577`, `:592`, `:610`, `:622`, `:638`, `:668` | The one slot that holds a claim, the two composition laws, and the terminals. |
| `ExactWitness`, `ExactProp`, `SpectralPropAt`, `cert_eps` | `manifest/pgg_tableau.v:114`, `:304`, `:331`, `:345` | The two existing claims. |
| `TransferStatus`, `NegativeTransfer` | `manifest/pgg_analysis_status.v:63-73` | Declared, used by no row. |
| `pgl27_row_exact_tableau`, `pgl27_row_word_tableau`, `pgl27_word_mixing` | `instances/pgl27/pgl27_rows.v:270`, `:295`, `pgl27_mixing.v:1048` | The instance where both rows exist. |
| `five_card_row_uniform_tableau`, `five_card_exact_witness`, `five_card_static_obs_indep` | `instances/kim2025/five_card_rows.v:338`, `:321`, `:299` | The ideal row of the five-card instance. |
| `psl211_row_alldecks_tableau`, `psl211_exact_witness`, `psl211_alldecks_sample`, `psl211_word_mixing`, `psl211_joint_mixing` | `instances/psl211/psl211_rows.v:175`, `:151`, `psl211_models.v:222`, `psl211_mixing.v:545`, `:595` | The ideal row of PSL(2,11) and the distance of its word model. |
| `psl211_fixed_deal_view_dep`, `psl211_fixed_dealP` | `instances/psl211/psl211_models.v:1158` | The refutation. |
| `five_card_colour_view_leak_bound`, `five_card_row_biased_leak_bound`, `five_card_static_obsE`, `five_card_colour_viewE` | `instances/kim2025/` | The bound in bits and the two view identifications. |
| `var_dist_fdistmap`, `var_dist_le2`, the cut-carrier distances of the Kim probe | `security/pgg_collusion_bound.v:126`, `notes/probes/2026-09-19-kim-spectral-arm/` | Data processing, the ceiling, and the model distances at Kim. |

## Soundness invariants

1. No new axiom, assumed constant, `Admitted` or `Abort`, apart from the one
   decomposition probe the method allows, which stays in the probe.
2. Every distance is a variation distance between exact laws and every leakage
   a Shannon quantity of an exact law. No computational assumption appears.
3. The claim of finding 1 speaks of the actual model and is an average over the
   run argument. It is not a statement at a fixed deck. The refutations at a
   fixed deck stay true and are cited beside it.
4. The claim of finding 2 has no threshold premise. A row that carries only a
   leakage bound is not presented as a coalition privacy result.
5. No row publishes a number below the one it proved.
6. A published number is compared with its trivial ceiling: 2 for a variation
   distance, the entropy of the secret for a leakage.
7. A refuted row has no projection that reads as secrecy.
8. Nothing is removed from the Tableau in this batch. Whether the spectral arm
   is still needed is reported and decided later.
9. No permanent file is edited. Probe files are kept and never imported by a
   permanent file. `psl211_endpoints` is never compiled.

## Probe artifacts

Directory `notes/probes/2026-09-20-tableau-extensions/`, logical path
`tableau_ext_probe`. Full copies of `manifest/pgg_tableau.v`,
`manifest/pgg_tableau_syntax.v` and the four rows files, with their imports of
one another pointed at the copies. One file of generic lemmas. One file per new
program. `_CoqProject`, `STATUS.md`, and the audit reports. The extensions are
applied to the copy in the order F3, F1, F2, F4, and the copy is saved under
`history/` after each, so that the cost of each is read from its own diff.

## Acceptance condition

An independent auditor has checked the placement by phase against the real
infrastructure before any probe file is written. Every ledger row ends in GO
or in NO-GO with an isolating counter-probe. An independent soundness audit and
an independent naming audit end in a verdict. The batch then reports, per
finding, the size of the change to the Tableau, the programs gained, and what a
landing would make false.

## Out of scope

Any edit under `manifest/` or `instances/`. The paper. A bound on mutual
information derived from a variation distance. Removing the spectral arm. The
`s5_row_word` program, beyond one sentence in F1.6 on whether its model has the
shape finding 1 asks for.
