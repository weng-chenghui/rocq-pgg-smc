# Extending the Tableau to hold what the repository has found

Date: 2026-09-19

Status: spec, third version, after the design audit
[[20260919-tableau-extensions-design-audit]] (DESIGN NO-GO on the second
version, with a recommended shape, adopted here). The probe starts when the
batch of [[20260919-kim-spectral-arm-probe-design]] is closed. This is a probe
batch. It edits no permanent file. A landing is a separate batch and needs the
user's decision.

Two directions from the user govern the design. The Tableau presents what we
have, so a finding it cannot hold is a reason to extend it, and an extension is
placed by what each phase means and not wherever a constructor can be added.
And `AnalysisBridged` is one security claim with its whole chain from
`Algebraic` upward, so two models are two rows, and two claims about one model
are two rows as well.

## Problem

A Tableau program is where a row of the paper becomes one term, and a reader
who stops at any line knows what has been proved there. The paper tells one
story about every instance: an ideal model with a uniform cut, which is
private, and an actual model with a biased cut, which is close to the ideal
one and so private up to a small number. The repository has proved that story
at PGL(2,7) and can prove it at PSL(2,11), and no program says it.

- `pgl27_view_mixing` (`instances/pgl27/pgl27_word_privacy.v:233`) states that
  at every Boolean prior and every coalition of at most three seats, the joint
  law of the reading and the secret under the word shuffle is within $2^{-40}$
  of the product of the two exact-shuffle marginals. It is aliased in the
  facade and pinned in the manifest, and it is carried by no row.
- The row PGL(2,7) does have for its word model goes through the spectral arm.
  That arm's certificate holds the ideal as a bare law on the cut group,
  `sc_ideal`, with a constancy field `sc_const` that is the ideal model's
  security claim in all but name. That ideal has no sample adapter, no secret,
  and never passed through `Sampled`. And `spectral_tail` does not consume the
  link lemma of `Sampled`, so the claim a spectral row publishes is about the
  static reading on both sides and never reaches the executed reader, where the
  exact arm's claim does.
- The constancy field asks that the ideal's reading be the same at every two
  run arguments. A privacy argument over a mixed law needs less: constancy in
  the secret, on average over what is public. The field can be proved where the
  run argument is the secret or determines it, at PGL(2,7) and at the five-card
  instance, and it is false at PSL(2,11) in the all-decks mode, where the run
  argument is the whole public deck description
  (`notes/probes/2026-09-19-psl211-sc-const/`). Three seats nevertheless learn
  nothing about the chirality there. So the word model of PSL(2,11), whose cut
  law `psl211_word_mixing` places within $2^{-40}$ of uniform, can have no row
  today, and it is the instance that needs the new claim most.

Two smaller gaps stand in the way of presenting the result. The obligation of
`conclude` is an equality, so a row cannot publish $2^{-39}$ from a bound it
proved below that. And a published manifest row does not say which kind of
claim it carries, so once two rows stand on one model they publish the same
value.

## Placement by phase

| Phase | What the row holds there | What a line at this phase may add |
|---|---|---|
| Algebraic, Executable | the algebra, the run mode, the fuel | run data |
| Observed | the three run facts, run correctness | facts about the interpreter |
| Sampled | a probability model, and the executed reader identified with the static one | a model and its link to the run |
| AnalysisBridged | one security claim about that model | a claim about what an observer learns |
| terminals | the published number, the chosen proposition, the manifest row | nothing about the coalition |

Rows form a tree. The prefix through `Observed` is shared, the tree branches at
`Sampled` by model, and it branches at `AnalysisBridged` by claim. The file
header already says that a row commits to one arm and claims nothing about the
other (`manifest/pgg_tableau.v:22-29`), and the data slot, `BridgedProp` and
the named projections all assume one claim.

**The claim "close to a private ideal model" is a claim about one model, so it
is an arm at `AnalysisBridged`.** Its certificate holds the ideal as a model
that has been through the phases: an ideal sample adapter over the row's own
execution, that ideal's `ExactWitness`, the actual model's secret, and for each
coalition below the threshold a bound on the distance between the two joint
laws of reading and secret. An ideal adapter with its witness is exactly the
data of a finished exact row over the shared observed prefix, so the instance
writes the ideal as its own published program and one `erefl` lemma says the
certificate's ideal and that row are one term. This is the pattern the tree
already uses (`pgl27_row_word_certE`, `five_card_row_repeated_prefixE`). The
dependency of the actual row on the ideal row is then recorded in the evidence
beside the programs, and every type stays a line. The composition law of the
arm consumes the link lemma of `Sampled`, as `exact_tail` does, so the
published claim is about the executed reader. The proposition has the shape
`pgl27_view_mixing` already has, so that the repository keeps one form for one
concept. A certificate holding a bare ideal law with a constancy field would be
`SpectralCert` under another name and is excluded.

**The weaker published number is the terminal's.** `conclude` leaves the data
and the claim untouched and moves only the real. `restate` can already hand
over a weaker number, as `pgl27_word_bridge` does, and what it cannot do is
publish a manifest row. So the obligation of `conclude` becomes an inequality.

**The kind of claim is read off the program, not stored in the manifest.** An
`AnalysisPathRow` describes a path and stores no theorem, by its own header,
and the manifest sits below the programs, so a field there could never be
filled from a program. The Tableau gains a reader that returns the arm of a
finished row, and each program pins it beside its `rowE`.

## Structure

`Operation:` a statement maps the data and the proposition at one level, with
one payload, to the data and the proposition one level up; from `Sampled`
upwards the proposition grows by one conjunct on the right. The invariant is
that a reader who stops at a line knows what is proved there.

`Monad:` dependent sequencing indexed by the completion level before and after
a statement. `tableau_bind` is dependent application with an arbitrary
continuation type, and its one law, the left unit, holds by definition. There
is no grading by the bound: the number is a parameter chosen at the terminal
and the exact arm's proposition mentions none. No further structure is
claimed.

`DSL:` the Tableau is the DSL. The gaps are one missing kind of claim, one
terminal obligation that is too strict, and one missing reader.

## Flow

The running value is the number the row would publish.

```
flow actual_row(instance)                                          // none yet
object   prefix : Tableau Observed                                 // shared by name
object   ideal  := prefix sample ideal_family certify ExactIndependence w |> publish   // 0
step     prefix sample actual_family                               // none yet
step     certify IdealProximity (ideal_family, w, secret, distance) // eps
terminal conclude at c with eps <= c                               // c
terminal publish IdealFinite                                       // c, the manifest row
beside   the certificate's ideal and the ideal row are one term    // erefl
beside   the arm of each row                                       // erefl
outside  the manifest rows, the paper, every permanent file
```

Interfaces of the external components: the instance's exact witness enters as
a field of the certificate; `pgl27_view_mixing`, or a distance derived from
`psl211_word_mixing` or from the cut-carrier distances of the Kim probe,
enters as the distance field. Assumptions invoked: none.

## Pinned carriers

`ep_inputT` is a `Type` and not a `finType` (`protocol/pgg_execution_plug.v:62`),
so there is no joint law of run argument and cut. The carriers on which two
models can be compared are the cut, the reading, and the pair of reading and
secret. The distance field is stated on the last.

- Five-card, the first carrier: the ideal is `uniform_family` with
  `five_card_exact_witness`, the actual is `kim_biased_family`. The two models
  share a sample space and differ only in the law.
- PGL(2,7): the actual is `pgl27_word_family`, indexed by a Boolean prior. The
  existing `pgl27_exact_family` is indexed by `unit` at the uniform prior, and
  the distance to it is not small at another prior. The probe builds an exact
  family indexed by the prior, at `pgl27P_gen secretP`, which is the ideal
  `pgl27_view_mixing` is stated against.
- PSL(2,11): the ideal is `psl211_exact_family` with `psl211_exact_witness`.
  The actual does not exist. The probe builds a sample adapter on
  `psl211_inputT * pgg_gT psl211_M` whose law is the uniform law on deck
  descriptions times `rho_from_words_weighted R 10 2 584 psl211_moves
  psl211_Wuni`. `psl211_joint_mixing` is stated at a Boolean prior and does not
  apply to that carrier, and the generic product lemma `var_dist_prodR` is
  `Local`, so the probe proves what it needs.

## Claim ledger

| ID | Checkable claim | Passing evidence |
|---|---|---|
| T0 | Two programs can continue from one named `Tableau Sampled` value. | One `Definition` of type `Tableau Sampled` and two `certify` continuations from it elaborate, in a copy of `five_card_rows.v`. Nothing in the tree does this today, and everything below assumes it. The hazard is that the payload type is stated at the named value, so `sp_f` has to reduce through the name. |
| P1 | Generic: data processing gives the distance between two joint laws of reading and secret from the distance between two sampled laws on a common sample space; and two product laws with one common factor are as far apart as the other factors. | `Qed`. |
| P2 | The certificate, the proposition and the composition law. | In a full copy of `pgg_tableau.v`: a record with an ideal adapter over the row's execution, its `ExactWitness`, the actual secret typed at the witness's `ew_secretT`, and the distance field below the threshold. A proposition of the shape of `pgl27_view_mixing`, stated at `sa_coalition_view`. A tail lemma ending in `Qed` that consumes the link lemma of `Sampled` for both models. |
| P3 | The ideal in the certificate is the ideal row. | For each instance an `erefl` lemma between the certificate's ideal data and the data of the published exact program. If it does not hold by conversion, the probe reports the smallest reason. |
| P4 | The five-card biased row through the new arm. | It elaborates and publishes. The distance comes from the cut-carrier distance of the Kim probe through P1. |
| P5 | The PGL(2,7) word row through the new arm. | A prior-indexed exact family and its program; the word row consuming it; the distance field is `pgl27_view_mixing` or follows from it in one step. The existing two PGL(2,7) programs are unchanged. |
| P6 | The PSL(2,11) word model and its row. | The adapter and family compile, its cut law is the word law by a lemma, the distance follows from `psl211_word_mixing`, and the row elaborates and publishes at coalitions of at most five seats. |
| P7 | The claim is neither vacuous nor trivially true. | Each number is compared with `var_dist_le2`, which exists only in the Kim probe and is copied. A mutation with the witness's independence removed does not give the tail. A certificate naming another instance's exact family is rejected by the types. |
| P8 | Relation to the spectral arm. | Compiled where cheap, argued where not, and marked which: at PGL(2,7) and at the five-card instance, where the cut is independent of the run argument and the run argument is the secret or determines it, `SpectralPropAt` implies the new proposition with constant 1. The converse. What each arm presents that the other does not: the spectral claim is about static readings at two fixed run arguments, the new one is about the executed reader on average. Nothing is removed in this batch. |
| P9 | The corollary about the actual model alone. | From the proposition, the actual joint law is within `k` times the bound of the product of its own marginals, with `k` reported. |
| C1 | `conclude` with an inequality. | `port_reprice` ends in `Qed` by monotonicity for both arms that carry a number. Every existing `conclude` compiles with its payload changed from an equality to an inequality, each change listed. |
| C2 | A number below the proved one cannot be published. | For one concrete certificate, a compiled proof that the obligation at a smaller number is false. |
| C3 | The repeated five-card row publishes $2^{-39}$ from the number it proved. | It elaborates with the certificate's epsilon left at the spectral number. |
| K1 | The arm of a finished row can be read. | A variant of arm names, a reader on `StackAt AnalysisBridged`, and one `erefl` pin per program in the copies of the four rows files. |
| G1 | Every existing program still compiles after each change. | Copies of `pgg_tableau_syntax.v`, `s5_rows.v`, `pgl27_rows.v`, `psl211_rows.v`, `five_card_rows.v` against the copy of `pgg_tableau.v`, after each of C, K, P in that order. |
| G2 | The surface syntax. | A notation for the new `certify`, and the keyword measurement of the syntax file's header repeated for each new word. |
| G3 | The header of `pgg_tableau.v` stays true. | The header of the copy is rewritten so that every sentence is true of the extended file. The sentences known to change: "There are five statements", "one of the two arms", and the passage at `:39-45` that says an instance's mathematics enters only as a witness or a certificate. |
| D1 | Names and homes. | A name and a file for each declaration, closures recomputed from `.Makefile.rocq.d`. `pgg_tableau.v` has five reverse-dependants, the manifest seven. `psl211_endpoints` is in neither closure. A new file needs a line in `_CoqProject`. |
| D2 | What a landing changes. | By file and line: header sentences and recorded `Fail`s made false, the manifest's `Check (erefl : ...)` pins and header tables, the facade's aliases and pins, and where each instance theorem has to live to be named by its facade. The previous batch needed three audit rounds to get this list right, so the probe builds it by searching the tree and not from memory. |

## Cited objects

| Object | File | Required statement shape |
|---|---|---|
| `SecurityPort`, `ab_port`, `PortProp`, `BridgedProp`, `exact_tail`, `spectral_tail`, `certify_exact`, `certify_spectral`, `RepricePayload`, `port_reprice`, `conclude`, `restate`, `publish` | `manifest/pgg_tableau.v:149`, `:241`, `:363`, `:377`, `:535`, `:561`, `:577`, `:592`, `:610`, `:622`, `:638`, `:668`, `:691` | The one slot that holds a claim, the two composition laws, the terminals. |
| `ExactWitness`, `ExactProp`, `SpectralCert`, `SpectralPropAt`, `sampled_viewE_prop` | `manifest/pgg_tableau.v:114`, `:304`, `:131`, `:331`, `:286` | The existing claims and the link lemma the new tail consumes. |
| `pgl27_view_mixing`, `view_mixing`, its pin | `instances/pgl27/pgl27_word_privacy.v:233`, `pgl27_analysis.v:263`, `manifest/pgg_analysis_manifest.v:1035` | The target proposition, already proved at one instance. |
| `pgl27_exact_family`, `pgl27_word_family`, `pgl27_row_word_certE` | `instances/pgl27/pgl27_models.v:410`, `:417`, `pgl27_rows.v:309` | The two families with different indices, and the `erefl` pattern. |
| `five_card_exact_witness`, `five_card_row_uniform_tableau`, `kim_biased_family`, `kim_centi_family` | `instances/kim2025/five_card_rows.v:321`, `:338`, `five_card_models.v` | The first carrier. |
| `psl211_exact_family`, `psl211_exact_witness`, `psl211_alldecksP`, `psl211_word_mixing` | `instances/psl211/psl211_models.v:516`, `psl211_rows.v:151`, `psl211_models.v:200`, `psl211_mixing.v:545` | The ideal of PSL(2,11) and the distance of its word cut. |
| `var_dist_fdistmap`, `var_dist_le2`, the triangle inequality | `security/pgg_collusion_bound.v:126`, the Kim probe, the PSL(2,11) probe's audit | Data processing, the ceiling, and a lemma infotheo lacks. |

## Soundness invariants

1. No new axiom, assumed constant, `Admitted` or `Abort`, apart from the one
   decomposition probe the method allows, which stays in the probe.
2. Every distance is a variation distance between exact laws. No computational
   assumption appears.
3. The new claim is an average over the run argument. It is not a statement at
   a fixed deck, and the refutations at a fixed deck stay true and are cited
   beside it.
4. The ideal in a certificate is a model with a witness, never a bare law.
5. One claim per row. Two claims about one model are two programs from one
   named `Tableau Sampled` value.
6. No row publishes a number below the one it proved.
7. Nothing is removed from the Tableau in this batch.
8. No permanent file is edited. Probe files are kept and never imported by a
   permanent file. `psl211_endpoints` is never compiled.

## Probe artifacts

Directory `notes/probes/2026-09-20-tableau-extensions/`, logical path
`tableau_ext_probe`. Full copies of `manifest/pgg_tableau.v`,
`manifest/pgg_tableau_syntax.v` and the four rows files, with their imports of
one another pointed at the copies. One file of generic lemmas. One file per new
model and per new program. `_CoqProject`, `STATUS.md`, the audit reports. Order:
T0, then C, K, P2, P4, P5, P6. The Tableau copy is saved under `history/` after
each change to it.

## Acceptance condition

Every ledger row ends in GO or in NO-GO with an isolating counter-probe. An
independent soundness audit and an independent naming audit end in a verdict.
The batch reports the size of the change to the Tableau, the programs gained,
and the list D2.

## What this batch leaves, by phase

The design audit lists fourteen findings that have no place in the Tableau.
This batch covers two of them, `pgl27_view_mixing` and the PSL(2,11) mixing
family. The rest are grouped by the phase they are facts about. Each group is a
later batch with its own spec, because each needs a design decision at its
phase before any probe.

- **Observers, a matter of `Sampled`.** The link lemma of `Sampled` identifies
  one executed reader, the coalition's view at a set of seats. Several findings
  are about another observer: the content trace (`pgl27_coalition_trace_secrecy`,
  `pgl27_word_trace_indist`, `pgl27_exec_trace_indist`, and trace secrecy in
  general), a list of card positions with the output given
  (`five_card_row_biased_leak_bound`, a conditional mutual information, a
  notion the Tableau has no word for at any phase), and coalitions at or above
  the threshold (`pgl27_view_leakage_le`). The question to settle first is what
  it means for `Sampled` to identify a second observer.
- **Refutations and other dealers, a matter of `Sampled` and
  `AnalysisBridged`.** `psl211_fixed_deal_view_dep`,
  `psl211_dealer_view_indep_of_deck_unsat` and `psl211_perdeck_law_neq` are
  stated at the dealer model and not at any sample adapter, so each needs a
  model family and a bridge before a row can publish `NegativeTransfer`. The
  refutation `psl211_dealt_sc_const_false` of the PSL(2,11) probe is already at
  a row's static reading and is the likely first case. The three PGL(2,7)
  theorems under other dealer laws (`pgl27_view_indep_alldecks`,
  `pgl27_view_indep_deck`, `pgl27_view_indep_deck_prior`) need model families
  of their own.
- **Terminals below `AnalysisBridged`.** `publish` exists only at the top
  level, so `s5_row_det` at `Observed` and any row that honestly stops at
  `Sampled` have no publishable program. A restated proposition cannot be
  published, since `RestatedTableau` holds no manifest row. `realises_expected`
  has no place in the accumulated proposition, by a recorded choice.
- **One-position marginal bounds.** `S5Analysis.exec_endpoint_bound` and
  `five_card_row_repeated_endpoint_lt` quantify over no coalition. The manifest
  places `s5_row_word` at `AnalysisBridged` on the first. No arm takes them,
  and whether one should is a question about what that level means.
- **Not the Tableau's.** `ExactLeakAt 6` at PSL(2,11) and the deck
  parametrization are numeric checks and not Rocq theorems. The blockage is at
  the instance.

## Out of scope

Any edit under `manifest/` or `instances/`. The paper. Removing or changing the
spectral arm. Every group of the previous section.
