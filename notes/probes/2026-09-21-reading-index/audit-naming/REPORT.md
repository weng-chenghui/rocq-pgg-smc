# GO-WITH-CHANGES

Naming and surface audit of the reading index and the surface prepositions,
2026-09-21, repository HEAD `400a4cb`, branch `feat/tableau-extensions-probe`.
Read-only. Nothing outside this file was written.

Scope read: the spec
`notes/20260921-reading-index-and-surface-prepositions-probe-design.md`, probe
A's `LEDGER.md`, its staged `pgg_tableau_syntax.v`, its 21 migrated instance
files and its `mini/`, probe B's `LEDGER.md`, its three staged manifest files
and `k5_default_reading.v`, `k7_k11_tails.v`, `k12_k14_psl211.v`,
`k17_vacuity.v`, and for conventions `manifest/pgg_tableau.v`,
`manifest/pgg_tableau_syntax.v`, `manifest/pgg_tableau_reading.v`,
`manifest/pgg_analysis_manifest.v`, `instances/psl211/psl211_colour_reading.v`
and the four `instances/*/tableau/` directories. `index2/` was not opened.

No collision was found: every new identifier of probe B was checked with
`git grep -w` over tracked `.v` files outside `notes/`, and none is already
bound. Every finding below is about what a name says, not about what it
shadows. No barred word occurs in any staged `.v` file of either probe or in
the spec.

## Findings

| id | class | where | finding | rule | replacement |
|---|---|---|---|---|---|
| N1 | MUST | `index/staged/manifest/pgg_tableau.v:320` | `EndpointReading` takes a phrase that already denotes the DEFAULT reading. "a coalition's endpoint reading" means the seat-indexed card positions in 29 tracked comment sites, among them `protocol/pgg_instance.v:73`, `security/pgg_sample_adapter.v:13`, `manifest/pgg_tableau.v:297` and `manifest/pgg_tableau_reading.v:9`. The record is the class of readings that factor through those positions, which is a different object. | 1, one word per concept tree-wide | `EndpointFactoredReading`, fields `efr_readT` and `efr_read`. Every fragment is already in the tree: `factors` in `psl211_colour_reading_factorsE` and in probe B's `reading_factors`. The default keeps `coalition_endpoint_reading`, which is exactly the established phrase and is correct. |
| N2 | MUST | `index/staged/manifest/pgg_tableau.v:323` | `er_of_endpoints` names the reading FUNCTION, but `_of_` in MathComp names a construction from its argument, so the name reads as the reading built from the endpoints. Production's counterpart projection on `StaticReading` is `sr_read`. | 1 | `efr_read`, matching `sr_read`. |
| N3 | MUST | `index/staged/manifest/pgg_tableau.v:644, 685, 732` | In the `...PropAt` family `At` binds the number: `IndistinguishabilityPropAt cert c`, `IdealProximityPropAt cert c`, `InputDistinguishabilityPropAt sa r c`, and `ExactLeakAt k` binds a size. In `IndistinguishabilityPropAtReading sa r c` the same `At` binds the reading while the number stays unnamed, and in `ExactPropAtReading sa r secret` there is no number at all. One word, two meanings, inside one family. | 1 | Put the reading first as a qualifier, which production already does at `manifest/pgg_tableau_reading.v:164` and `:226` with `ReadingIndistinguishabilityPropAt` and `ReadingExactIndependence`. Then `At` keeps one meaning. See N4, which removes the three names outright. |
| N4 | MUST | `index/staged/manifest/pgg_tableau.v:644, 685, 732` against `manifest/pgg_tableau_reading.v:164, 226` | Two names for one proposition. `IndistinguishabilityPropAtReading sa r c` is convertible with `ReadingIndistinguishabilityPropAt sa (static_reading_of_endpoint_reading E r) c`, and probe B proves the identification itself at `index/staged/manifest/pgg_tableau_reading.v:206`. The two names differ only by word order, which is the worst available way to distinguish two things. | 1 | Delete probe B's triple. `pgg_tableau.v` does not need a free-reading form: it uses each only once, inside the evidence-indexed wrapper, so the body can be inlined into `ExactProp`, `IndistinguishabilityPropAt` and `IdealProximityPropAt`. K11 is proved in `k7_k11_tails.v`, which may require `pgg_tableau_reading.v` and use the production names. `IdealProximityPropAtReading` has no consumer at all: probe B's own LEDGER section on K11 recommends stating proximity post-processing on the certificate. If a free-reading form is wanted inside `pgg_tableau.v`, move `StaticReading` there instead: it needs only `ex_inputT`, `pgg_gT`, `instance_profile` and `finType`, all already imported, and its two propositions have four uses outside their file, all in `instances/psl211/psl211_colour_reading.v`. |
| N5 | MUST | `index/staged/manifest/pgg_tableau.v:945, 963, 981` | `exact_of_reading`, `indistinguishability_of_reading`, `idealproximity_of_reading`. `_of_reading` already carries two other meanings in the tree: `psl211_colour_of_reading` at `instances/psl211/psl211_colour_reading.v:239` is a map applied to a reading, and `exact_independence_executed_of_reading` at `manifest/pgg_tableau_reading.v:245` is a statement derived from the reading form. Here it names a payload built from a reading and a witness family, and the head word `exact` names no object. | 1 | `exact_payload_at_reading`, `indistinguishability_payload_at_reading`, `idealproximity_payload_at_reading`, matching the type names `ExactPayload`, `IndistinguishabilityPayload`, `IdealProximityPayload`. The `At`-is-a-number rule of N3 is scoped to the `...Prop*At` family, so `at_reading` here is the `StackAt` sense, a coordinate. |
| N6 | SHOULD | `index/staged/manifest/pgg_tableau.v:1332` | `reading_of` is right by the `security_property_of` precedent at `manifest/pgg_tableau.v:1322`. The defect is the company it keeps: with N5 unfixed the tree holds `reading_of`, `..._of_reading` and `psl211_colour_of_reading`, three shapes from the same two words in three senses. | 1 | Keep `reading_of`, apply N5, so two shapes remain and each has one sense. |
| N7 | MUST | `index/k12_k14_psl211.v:102` | `psl211_dealt_prefix` has type `Tableau Sampled`. In the tree `..._prefix` names a `Tableau Observed`, `psl211_alldecks_prefix` at `instances/psl211/tableau/psl211_tableau_observed.v:74`, and a `Tableau Sampled` is `<model>_sampled`: `psl211_exact_sampled`, `pgl27_word_sampled`, `five_card_repeated_sampled`, `s5_rand_sampled`. | 1 | `psl211_dealt_sampled`. If an Observed value is wanted too, it takes `psl211_dealt_prefix`. |
| N8 | SHOULD | `index/k12_k14_psl211.v:125` | `psl211_colour_witness` omits the property. The tree writes it in: `pgl27_exact_witness`, `s5_rand_exact_witness`. | 1 | `psl211_colour_exact_witness`. |
| N9 | SHOULD | `index/k12_k14_psl211.v:150` | `psl211_colour_published` omits the property where the instance has several programs. The tree writes it in: `psl211_word_proximity_published`, `five_card_repeated_indistinguishability_published`. | 1 | `psl211_colour_exact_published`. |
| N10 | SHOULD | `index/k12_k14_psl211.v:51` | `psl211_colour_endpoint_reading` carries N1's collision into the instance, and it is a second name for the mathematical object `psl211_colour_reading` at `instances/psl211/psl211_colour_reading.v` already names. Two records force two names for one reading at every instance. | 1 | With N4 applied and one record retained the instance keeps one name, `psl211_colour_reading`, of the endpoint-factored type, and its static form is written `static_reading_of psl211_colour_reading`. Cost: the four uses of `psl211_colour_reading` in that file change shape. If both records stay, `psl211_colour_reading_of_endpoints`. |
| N11 | SHOULD | `index/staged/manifest/pgg_tableau_reading.v:273` | `exact_independence_of_witness_at` ends in a preposition with no object. | 1 | `exact_independence_of_witness_at_reading`. |
| N12 | SHOULD | `index/k7_k11_tails.v:128` | `reading_indistinguishability_postprocessing_at` has the same trailing preposition and duplicates `reading_indistinguishability_postprocessing` at `manifest/pgg_tableau_reading.v:187`. | 1 | After N4 there is one post-processing lemma and it keeps the production name. |
| N13 | NOTE | `index/k5_default_reading.v:229` | `blind_reading` is a metaphor for the constant reading, which sends every endpoint map to the constant map at card zero. | 2 | `constant_reading`. |
| N14 | SHOULD | `index/k5_default_reading.v:172, 177, 182` | `indist0_of`, `indist_of0`, `prox0_of` abbreviate indistinguishability and proximity. The ban on abbreviating indistinguishability holds everywhere, a probe file included, and `prox` is a project-local abbreviation a MathComp reader does not know. | 1 and 2 | `indistinguishability0_of`, `indistinguishability_of0`, `idealproximity0_of`. |
| N15 | NOTE | `index/staged/manifest/pgg_tableau.v:321` | `er_` sits one letter from `sr_`, two two-letter prefixes for two records a reader must keep apart. | 1 | N1's `efr_` is three letters and no longer one letter from `sr_`. |
| N16 | NOTE | `index/staged/manifest/pgg_tableau.v:434, 581` | `evidence_reading` and `ab_reading` match `evidence_property` and `ab_security_property`. Accepted. `ab_reading` carries no qualifier where `ab_security_property` carries one, which is correct only because "reading" is the concept word and needs none. | 1 | None. |
| N17 | NOTE | tracked tree | `coalition_endpoints` at `instances/s5/s5_analysis.v:121`, `instances/pgl27/pgl27_analysis.v:129` and `instances/psl211/psl211_analysis.v:139` is the manifest's observer entry for the default reading, so `coalition_endpoint_reading` reads consistently with it. No shadowing: those are section-local to the analysis files and the framework does not import them. | 1 | None. |
| N18 | MUST | `manifest/pgg_tableau_reading.v:9, 36, 109` and `manifest/pgg_tableau.v:297` | Prose collision. Those sites write "a coalition's static endpoint reading" for the DEFAULT. Beside a record named `EndpointReading`, "a coalition's static endpoint reading" and "the static form of an endpoint reading" differ by one word and denote different things. | 1 | N1, plus the vocabulary in the next section. |
| N19 | MUST | `manifest/pgg_analysis_manifest.v:134, 136` against spec line 187 and `index/staged/manifest/pgg_tableau.v:1326` | Two words for one concept, and one of them in two senses. The manifest's third coordinate is "observer" and its entries are reading functions, `PGL27Analysis.coalition_endpoints` at `:108` and `FiveCardAnalysis.colour_view` at `:307`. The spec's invariant 2 says a reading changes what a coalition sees "never who it is", which reads as if observer meant who. Probe B's comment on `reading_of` then calls the reading "the observer". | 1 | Settle it in the landing. Either the manifest's column becomes "reading", or every new text says the observer coordinate holds a reading and stops using "observer" for the party. The fourth coordinate has the smaller version of the same defect: the manifest says "notion", the framework says `SecurityProperty`. |
| N20 | MUST | `surface/staged/instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:411` | Reads as an application. In `certify InputIndistinguishability at R idx pgl27_word_marginal_bound R` the bound follows the slot `idx` with no marker of its own. | 3 | `at R idx by b`. Zero keyword cost, `by` is reserved. Alternative `bound b`, one new keyword. |
| N21 | MUST | `surface/staged/instances/psl211/tableau/psl211_tableau_analysis_bridged.v:539` | Reads as an application. `publish Obstruction psl211_alldecks_obstruction` puts the value straight after the literal. | 3 | `publish Obstruction of o by pf assuming a`. Zero keyword cost, `of` is reserved. |
| N22 | SHOULD | `surface/staged/instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:492` | Reads as an application. `conclude pgl27_bound39 by p` puts the number straight after the action word. | 3 | `conclude at c by p`. Zero keyword cost, and it puts a number behind `at`, which is the decided meaning. |
| N23 | MUST | spec line 139 and `surface/mini/k4e_kind_prefixed.v:18` beside `manifest/pgg_tableau_syntax.v:458` | `Obstruction` and `obstruction` in one language. The kind notation is at level 10 and the publish rule's slot is at level 0, so an inline kind must be parenthesised, giving `publish Obstruction (obstruction InputDistinguishability of r at c) by pf assuming a`, read aloud as "publish obstruction, obstruction input distinguishability of r at c". | 1 and 3 | Two ways out. (a) Keep the opener, apply N21's `of`, and require that a kind be named by a definition before it is published, which is what the tree does today with `psl211_alldecks_obstruction`. Cost: none. (b) Drop the opener and let the publish rule carry it, `publish Obstruction InputDistinguishability of r at c by pf assuming a`, where `InputDistinguishability` follows the literal `Obstruction` and stays an identifier. Cost: no new keyword, and no standalone spelling of a kind. |
| N24 | SHOULD | `surface/staged/instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:385` | Two `by` in one statement. `certify ExactIndependence by w leaks at 4 by H`. Both introduce a proof or a piece of evidence, so the decided table holds, but a reader must decide whether the annotation attaches to the statement or to the witness. In the term it wraps the payload. | 3 | One header sentence saying the annotation attaches to the evidence. No cheaper fix keeps the preposition table. |
| N25 | NOTE | `manifest/pgg_tableau_syntax.v:64-94` | The surface has two categories and the header names only one. Prepositions with one meaning each: `of`, `at`, `by`, `assuming`. Slot names, where the word names the thing and the term after it is that thing: `dealt`, `inputs`, `layout`, `expecting`, `fuel`, `sample`, `ideal`, `tied`, `mixing`, `invariant`, `leaks`, `terminates`, `endpoints`, `recon`, `functionality`, `decoded_by`, `committed_by`. | 3 | Declare the two categories in the header. That removes probe A's recorded defects about `sample f`, `dealt fuel n` and `supplied inputs T layout L expecting e fuel n` at no keyword cost, and leaves exactly N20, N21 and N22, where the term follows a slot or an action word rather than a slot name. |
| N26 | SHOULD | `manifest/pgg_tableau_syntax.v:435, 442, 450, 458` | `publish` is followed by four grammars: a transfer status, the level `Observed`, the level `Sampled`, and the word `Obstruction`. | 1 | N21 and N25 reduce it to two: a level name, or the word `Obstruction` followed by its own `of` clause. |
| N27 | MUST | `surface/LEDGER.md:98-103` | The draft first sentence says twenty and lists `assuming`. The owner's decided obstruction spelling adds `obstruction`, which probe A itself measured to be reserved at `surface/mini/k4e_kind_prefixed.v` and `msg/k4e_opener_binder.after.msg`. If both land the count is twenty-one and the draft does not say so. | 4 | Write twenty-one and list both, or say the count is twenty until the obstruction rule lands and twenty-one after. |
| N28 | MUST | `manifest/pgg_tableau_syntax.v:67` | The draft leaves the header's account of why a token is reserved untouched, and that account becomes false. The header says "Each follows a slot in some rule." `obstruction` follows nothing, being the rule's leading literal, and probe A's own finding is that a leading literal is reserved. | 4 | Add the second position: a token is reserved when it follows a slot in some rule, and also when it opens one. |
| N29 | MUST | `surface/LEDGER.md:76-78` | The text the draft rests on is wrong about one rule. It says `assuming` follows the slot `t` of `publish t assuming a` and the slot `pf` of the obstruction rule, and "In the other two rules it follows a literal." In `s |> publish Sampled t assuming a`, `surface/staged/manifest/pgg_tableau_syntax.v:456`, it follows the slot `t`. Three rules, not two. | 4 | Correct the ledger and the draft sentence to three slot positions and one literal position. |
| N30 | SHOULD | `surface/LEDGER.md:112` against `:80` | "the five files that use the word use it in a comment" drops the distinction the body makes: ten files contain the word and five of them are `.v` files. | 4 | "It is written in no code of the tree. Five `.v` files contain the word and each contains it inside a comment." |
| N31 | SHOULD | `surface/LEDGER.md:107-118` | History narration and a wrong count of rules. "by now also follows", "where before the rule carried it both were accepted", and "each of the four certify rules" when there are five, the fifth being the five-clause rule whose token after the property name is `at`. | 4 | "by follows the literal naming the security property in four of the five certify rules, and the evidence of a certify statement is the term after it. In a file that does not require this one, both uses of assuming are accepted." |
| N32 | SHOULD | `surface/LEDGER.md:93-122` | The draft says nothing about `of`. If probe B's reading clause lands, `of` follows the literal naming the security property and `by` follows the slot `r`. Neither reserves anything new, `of` being an ssreflect keyword and `by` already reserved. The paragraph's job is to account for every literal of every rule. | 4 | Add one sentence naming both positions and stating that neither reserves anything. |
| N33 | NOTE | `surface/LEDGER.md:107` | "measured on 2026-09-21" matches the file's convention at `manifest/pgg_tableau_syntax.v:41, 68, 78, 84`, so it is a fact about the surface and not a status marker. | 4 | None. |
| N34 | SHOULD | `surface/LEDGER.md:23, 303, 355, 563` | "priced", "four spellings priced", "spends it on a generic word", "spends it on `obstruction`". Metaphor words for an engineering result. | 2 | "four spellings measured", "it reserves one keyword, and the keyword is a generic word rather than the kind's own name". |
| N35 | SHOULD | `surface/LEDGER.md:452-456, 565-568` | The claim that the spec's sentence "does not cover `at R idx` as written" is inaccurate. Spec line 55 reads "at a number, a size or a real field with its index", which names that case. Owner question 2 rests on a misreading. | 4 | Withdraw the question and keep the residual point, which is different and real: in `at R idx` the two terms are binders and everywhere else `at` is followed by a value. |
| N36 | NOTE | both ledgers and the spec | "row" occurs only for ledger rows, never for a program or a path. Clean. | 2 | None. |
| N37 | NOTE | both probes' staged `.v` files and the spec | No barred word found: `apex`, `gate` and its forms, `posit` and its forms, `arm`, `port`, the norm abbreviation with the letter and the digit, `beats`, `escapes`, `cap`, `ceiling`, `currency`. | 2 | None. |
| N38 | SHOULD | spec lines 16-18 | The spec says "The observer is fixed" and then names an endpoint reading, which is what the reading coordinate is. See N19. | 1 | Say "the reading is fixed" and name the manifest's column once. |
| N39 | NOTE | spec lines 77-82 | The code block shows `EndpointReading` indexed by nothing and `er_of_endpoints` typed with a free `{ffun seats -> cards}`. Probe B's built record is indexed by the algebra `A`. Section 3.2 is not owner-approved, so this is a fold item. | 4 | Replace the block with the built one at the fold. |
| N40 | MUST | `index/staged/manifest/pgg_tableau.v:338, 357, 381, 416, 717, 933, 951, 970, 1583` | Nine statement comments were not changed while their objects gained a reading coordinate. `ExactWitness` still says "the independence of that coalition's static endpoint reading from it", which is now one case and not the statement. The comment before `IdealProximityPropAtReading` speaks of "the certificate's ipc_eps" and that definition has no certificate. `ExactPayload` and the two other payload comments describe a function family, and the objects are sigmas. `ObstructionKind` says "The one member carries the number the model is distinguishable at" and the member now carries a reading and a number. | 4 | Restate each as what the object is. Under N4 some of these revert, so do the comment pass after the name decisions. |
| N41 | SHOULD | `index/staged/manifest/pgg_tableau.v:325-328`, `surface/staged/manifest/pgg_tableau_syntax.v:393-396`, `index/staged/manifest/pgg_tableau_syntax.v:398-400` | History narration inside statement comments. "before the index was added ... and states what it stated before", "writing it bare read as an application", "the text of a program written before the reading index reads as it read then". | 4 | Restate as facts about the object. For the default reading: "The identity at every coalition. A program that names no reading is a program at this one." |
| N42 | SHOULD | `index/k12_k14_psl211.v:63, 149` | Plan ids inside statement comments: "K12: the static form ..." and "which K15 is about". A probe file may carry them. The landing must not. | 4 | Strip at the fold. |
| N43 | NOTE | `instances/psl211/psl211_colour_reading.v:27-30` | A production header states as a fact that the dealer-dealt parameters carry no endpoints statement, so there is no Observed and no Sampled level, no program and no path. Probe B's K13 builds all four from `profile_endpointsE psl211_profile_endpoints`. The sentence is false of what is provable. | 4 | Correct it at the landing. Probe B already records this. |

## Task B, the vocabulary for `StaticReading` and the new record

The pair as it stands is not clear about the difference, and the phrase
collision of N18 is real and tree-wide. Proposed vocabulary, one word per
concept.

- **reading**: what a coalition is granted to see. The only word for it. Not
  view, not observation, not trace, not observer.
- **a coalition's endpoints**: the seat-indexed card positions that
  `static_coalition_obs` returns. In new text this is never itself called a
  reading, because calling it one is what created the collision.
- **endpoint-factored reading**: a reading that is a function of the
  coalition's endpoints alone. The record `EndpointFactoredReading`, fields
  `efr_readT` and `efr_read`. The domain fact the name carries is the one that
  matters: because such a reading is a function of the endpoints, the link
  lemma of the Sampled level carries it to the executed run with no further
  premise.
- **static reading**: a reading that is a function of the run argument and the
  cut. The record `StaticReading`. Strictly more general, and it is where a
  transcript reading would go if one were ever built.
- **the static form of an endpoint-factored reading**:
  `static_reading_of_endpoint_reading`, renamed `static_reading_of` under N1's
  rename so it does not spell the record's long name twice.
- **the coalition reading**: `coalition_endpoint_reading`, the identity
  endpoint-factored reading. In prose "a coalition's own endpoints". Never "a
  coalition's endpoint reading" in new text, because that phrase already means
  the tuple at 29 tracked sites.
- **observer**: the manifest's word for this coordinate. Settle N19 one way or
  the other before the landing. Two words for one coordinate is the thing the
  reading work was supposed to remove, not add.

## Task C, every distinct program shape read aloud, term by term

Read from probe A's migrated staged files, with prefixes spliced in so each
program is one sentence. The new shapes are read from probe B and from the
spec, in probe A's migrated surface.

### 1. The S_5 program that publishes at Observed

```coq
s5_algebra
  dealt   fuel 150
  execute terminates by s5_dealt_terminates
          endpoints by s5_dealt_endpoints
          recon by s5_dealt_recon
  |> publish Observed assuming (AcceptsAxioms [:: AxS5GroupOrder]).
```

Aloud: the algebra `s5_algebra`, dealt, at fuel 150. Executed, terminating by
`s5_dealt_terminates`, with endpoints by `s5_dealt_endpoints` and
reconstruction by `s5_dealt_recon`. Published at Observed, assuming the axiom
list `[:: AxS5GroupOrder]`.

Every clause reads as a clause. `dealt` is a mode word with no term after it
and `fuel 150` is a slot name with its term, which reads correctly under the
two-category account of N25 and not under the preposition rule alone.

### 2. The S_5 exact program

```coq
s5_algebra
  supplied inputs 'rV['Z_5]_5
           layout s5_rfree_layout
           expecting (fun u => s5_codec (s5_tape_secret u))
           fuel 150
  execute terminates by s5_supplied_terminates
          endpoints by s5_supplied_endpoints
          recon by s5_supplied_recon
  sample  s5_rand_family
  certify ExactIndependence by s5_rand_exact_witness
  |> publish StaticExecutedOnly assuming (AcceptsAxioms [:: AxS5GroupOrder]).
```

Aloud: the algebra `s5_algebra`, supplied, with inputs of type `'rV['Z_5]_5`,
at layout `s5_rfree_layout`, expecting `s5_codec (s5_tape_secret u)`, at fuel
150. Executed, terminating by `s5_supplied_terminates`, with endpoints by
`s5_supplied_endpoints` and reconstruction by `s5_supplied_recon`. Sampled at
`s5_rand_family`. Certified for exact independence by
`s5_rand_exact_witness`. Published at StaticExecutedOnly, assuming the axiom
list `[:: AxS5GroupOrder]`.

No clause reads as an application. Before the migration the last two lines did.

### 3. Kim's input-indistinguishability program

```coq
five_card_algebra functionality (fun ab : bool * bool => ab.1 && ab.2)
  encoded inputs (bool * bool)
          layout den_boer_layout
          by den_boer_assemble_valid
          decoded_by den_boer_decode
          committed_by five_card_commits
          fuel 100
  execute terminates by five_card_terminates
          endpoints by five_card_endpoints
          recon by five_card_recon
  sample  kim_centi_family
  certify InputIndistinguishability by kim_centi_cert
  |> publish IdealFinite assuming BaselineClassicalOnly.
```

Aloud: the algebra `five_card_algebra`, with functionality the conjunction of
the two committed bits, encoded, with inputs of type `bool * bool`, at layout
`den_boer_layout`, by the sharing claim `den_boer_assemble_valid`, decoded by
`den_boer_decode`, committed by `five_card_commits`, at fuel 100. Executed,
terminating by `five_card_terminates`, with endpoints by
`five_card_endpoints` and reconstruction by `five_card_recon`. Sampled at
`kim_centi_family`. Certified for input indistinguishability by
`kim_centi_cert`. Published at IdealFinite, assuming BaselineClassicalOnly.

This reads cleanly. Note that `by den_boer_assemble_valid` in the encoded
clause and `by kim_centi_cert` in the certify clause are the same preposition
for a proof and for a certificate. That is one meaning, because a certificate
is a record whose fields are proofs, and the header should say so, since a
reader meeting `certify ... by` for the first time may read `by` as "by means
of".

### 4. The five-clause input-indistinguishability program, PGL(2,7)

This rule is used at one instance in the tree.

```coq
pgl27_algebra
  dealt   fuel pgl27_fuel
  execute terminates by pgl27_dealt_terminates
          endpoints by pgl27_dealt_endpoints
          recon by pgl27_dealt_recon
  sample  pgl27_word_family
  certify InputIndistinguishability at R idx
          pgl27_word_marginal_bound R
          tied by esym (pgl27_word_cut_distE idx)
          ideal (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M))
          mixing by pgl27_word_mixing R
          invariant by pgl27_word_view_const R
  |> publish IdealFinite assuming BaselineClassicalOnly.
```

Aloud: the algebra `pgl27_algebra`, dealt, at fuel `pgl27_fuel`. Executed,
terminating by `pgl27_dealt_terminates`, with endpoints by
`pgl27_dealt_endpoints` and reconstruction by `pgl27_dealt_recon`. Sampled at
`pgl27_word_family`. Certified for input indistinguishability at the real
field R and the index idx, **`pgl27_word_marginal_bound R`**, tied by the
symmetry of `pgl27_word_cut_distE idx`, with ideal the uniform law on
`pgg_G pgl27_M`, mixing by `pgl27_word_mixing R`, invariant by
`pgl27_word_view_const R`. Published at IdealFinite, assuming
BaselineClassicalOnly.

The bolded term is N20. Said aloud there is no word between `idx` and the
bound, so the sentence reads as the index applied to the bound. `at R idx by
pgl27_word_marginal_bound R` fixes it at no keyword cost.

### 5. The PGL(2,7) exact program with the tightness annotation

```coq
pgl27_algebra
  dealt   fuel pgl27_fuel
  execute terminates by pgl27_dealt_terminates
          endpoints by pgl27_dealt_endpoints
          recon by pgl27_dealt_recon
  sample  pgl27_exact_family
  certify ExactIndependence by pgl27_exact_witness
          leaks at 4 by pgl27_exact_leak4
  |> publish StaticExecutedOnly assuming BaselineClassicalOnly.
```

Aloud: the algebra `pgl27_algebra`, dealt, at fuel `pgl27_fuel`. Executed,
terminating by `pgl27_dealt_terminates`, with endpoints by
`pgl27_dealt_endpoints` and reconstruction by `pgl27_dealt_recon`. Sampled at
`pgl27_exact_family`. Certified for exact independence by
`pgl27_exact_witness`, which leaks at 4 by `pgl27_exact_leak4`. Published at
StaticExecutedOnly, assuming BaselineClassicalOnly.

Two `by` in one statement, N24. The reading "which leaks at 4" attaches the
annotation to the witness, and that is what the term does, since `exact_leaks`
wraps the payload. Nothing in the text says so, and a reader may attach it to
the statement instead. One header sentence closes it.

### 6. The PGL(2,7) word program with `conclude`

```coq
pgl27_algebra
  dealt   fuel pgl27_fuel
  execute terminates by pgl27_dealt_terminates
          endpoints by pgl27_dealt_endpoints
          recon by pgl27_dealt_recon
  sample  pgl27_word_family
  certify InputIndistinguishability by pgl27_word_cert
  |> conclude pgl27_bound39 by (fun R _ => ssr_ext.eqW (pow2_split R))
  |> publish IdealFinite assuming BaselineClassicalOnly.
```

Aloud: the algebra `pgl27_algebra`, dealt, at fuel `pgl27_fuel`. Executed,
terminating by `pgl27_dealt_terminates`, with endpoints by
`pgl27_dealt_endpoints` and reconstruction by `pgl27_dealt_recon`. Sampled at
`pgl27_word_family`. Certified for input indistinguishability by
`pgl27_word_cert`. Concluded **`pgl27_bound39`** by the function that reads
`pow2_split R` as the inequality. Published at IdealFinite, assuming
BaselineClassicalOnly.

The bolded term is N22. "Concluded `pgl27_bound39`" reads as the action applied
to the bound. "Concluded at `pgl27_bound39`" reads as a clause, and `at` before
a number is the decided meaning.

### 7. The PSL(2,11) proximity program

```coq
psl211_algebra
  supplied inputs psl211_inputT
           layout psl211_alldecks_layout
           expecting psl211_alldecks_expected
           fuel psl211_fuel
  execute terminates by psl211_alldecks_terminates
          endpoints by psl211_alldecks_endpoints
          recon by psl211_alldecks_recon
  sample  psl211_word_family
  certify IdealProximity by psl211_word_proximity_cert
  |> publish IdealFinite assuming BaselineClassicalOnly.
```

Aloud: the algebra `psl211_algebra`, supplied, with inputs of type
`psl211_inputT`, at layout `psl211_alldecks_layout`, expecting
`psl211_alldecks_expected`, at fuel `psl211_fuel`. Executed, terminating by
`psl211_alldecks_terminates`, with endpoints by `psl211_alldecks_endpoints`
and reconstruction by `psl211_alldecks_recon`. Sampled at
`psl211_word_family`. Certified for ideal proximity by
`psl211_word_proximity_cert`. Published at IdealFinite, assuming
BaselineClassicalOnly.

Clean.

### 8. The PSL(2,11) obstruction program

```coq
psl211_algebra
  supplied inputs psl211_inputT
           layout psl211_alldecks_layout
           expecting psl211_alldecks_expected
           fuel psl211_fuel
  execute terminates by psl211_alldecks_terminates
          endpoints by psl211_alldecks_endpoints
          recon by psl211_alldecks_recon
  sample  psl211_exact_family
  |> publish Obstruction psl211_alldecks_obstruction
     by psl211_alldecks_obstruction_pf assuming BaselineClassicalOnly.
```

Aloud: the algebra `psl211_algebra`, supplied, with inputs of type
`psl211_inputT`, at layout `psl211_alldecks_layout`, expecting
`psl211_alldecks_expected`, at fuel `psl211_fuel`. Executed, terminating by
`psl211_alldecks_terminates`, with endpoints by `psl211_alldecks_endpoints`
and reconstruction by `psl211_alldecks_recon`. Sampled at
`psl211_exact_family`. Published, obstruction
**`psl211_alldecks_obstruction`**, proved by
`psl211_alldecks_obstruction_pf`, assuming BaselineClassicalOnly.

The bolded term is N21. The migration fixed the terminal's last clause: before
it the line ended `by psl211_alldecks_obstruction_pf BaselineClassicalOnly`,
which read as the proof applied to the status. What is still unfixed is one
clause earlier. `publish Obstruction of psl211_alldecks_obstruction by ...
assuming ...` fixes it at no keyword cost.

### 9. New shape, `certify ExactIndependence of r by w`

From `index/k12_k14_psl211.v:150`, with probe A's terminal:

```coq
psl211_algebra
  dealt   fuel psl211_fuel
  execute terminates by psl211_dealt_terminates
          endpoints by psl211_dealt_endpoints
          recon by psl211_dealt_recon
  sample  psl211_dealt_family
  certify ExactIndependence of psl211_colour_endpoint_reading
          by psl211_colour_witness
  |> publish StaticExecutedOnly assuming BaselineClassicalOnly.
```

Aloud: the algebra `psl211_algebra`, dealt, at fuel `psl211_fuel`. Executed,
terminating by `psl211_dealt_terminates`, with endpoints by
`psl211_dealt_endpoints` and reconstruction by `psl211_dealt_recon`. Sampled
at `psl211_dealt_family`. Certified for exact independence of the colour
reading by `psl211_colour_witness`. Published at StaticExecutedOnly, assuming
BaselineClassicalOnly.

The clause reads as a clause, and "of the colour reading" is what is read,
which is the decided meaning of `of`. This is the best-reading statement in
the whole surface, and it is also the one place where the name itself gets in
the way: "exact independence of `psl211_colour_endpoint_reading`" says
"endpoint reading" where the reading is the colour reading and not the
endpoints, which is N1 and N10 heard aloud. Under the proposed rename it reads
"certified for exact independence of `psl211_colour_reading` by
`psl211_colour_exact_witness`".

### 10. New shape, `obstruction InputDistinguishability of r at c`

Standalone:

```coq
obstruction InputDistinguishability of r at c
```

Aloud: an obstruction, input distinguishability, of the reading r, at the
number c.

Both prepositions carry their decided meaning and nothing reads as an
application. The defect is what happens when this meets the terminal that
publishes it. With the kind at level 10 and the publish slot at level 0, an
inline kind needs parentheses:

```coq
  |> publish Obstruction (obstruction InputDistinguishability of r at c)
     by pf assuming BaselineClassicalOnly.
```

Aloud: published, obstruction, obstruction input distinguishability of the
reading r at the number c, proved by pf, assuming BaselineClassicalOnly. That
is N23. The word appears twice in two grammatical roles inside one clause.

## Summary of the changes the verdict asks for

MUST, before the landing: N1, N2, N3, N4, N5, N7, N18, N19, N20, N21, N23,
N26 by way of N21 and N25, N27, N28, N29, N40.

SHOULD, at the fold: N6, N8, N9, N10, N11, N12, N14, N22, N24, N30, N31, N32,
N34, N35, N38, N41, N42.

NOTE, recorded: N13, N15, N16, N17, N33, N36, N37, N39, N43.

None of the MUST items is a soundness matter, and none needs a measurement
that has not been taken. Every surface fix proposed above costs no keyword
except N20's alternative and N23's option (a), which costs none either. The
one design question the naming audit cannot settle by itself is N4, because
deleting probe B's three propositions changes which file states the
free-reading forms, and that belongs to the landing plan.
