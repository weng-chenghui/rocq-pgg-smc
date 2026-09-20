# Audit of the two reading probes, before one landing plan (2026-09-21)

Two remits. (I) adversarial soundness of the second probe,
`notes/probes/2026-09-21-psl211-colour-reader/` (`c_adapter.v`, `c_reader.v`,
`c_exact.v`, `LEDGER.md`). (II) naming and statement comments of that probe
and of `notes/probes/2026-09-20-readers-and-marginal-bounds/`
(`r_framework.v`, `r_pgl27.v`, `r_marginals.v`), from which the landing will
take its names. The first probe's soundness audit (`audit-soundness.md`) is
not redone.

Vocabulary of this report: a Tableau value is a PROGRAM, the manifest's record
is a PATH, a program certifies a SECURITY PROPERTY with SECURITY EVIDENCE, and
the evidence proves a PROPOSITION.

## Verdict

**GO** for writing one landing plan for both probes, with the MUST items
below carried into it: six on soundness (Q2, Q3, Q5, Q6, Q7, Q9), sixteen on
names (N1, N2, N4, N6, N7, N8, N13, N14, N15, N16, N17, N19, N20, N22, N24,
N26) and eleven on statement comments (S1, S4, S7, S8, S9, S10, S11, S12,
S13, S14, S15). Nothing compiled in the second probe is wrong. Every
MUST is a statement comment that claims more than the file proves, or a name
that states the shape of a type or the tree's concept under a second word.
The crux, `psl211_canonical_reader_not_exact`, is TRUE, is what it seems, and
is consistent with the tree.

Two MUSTs change the landing's shape rather than its prose:

- Q2, the dealer-dealt execution carries no endpoints statement, so nothing
  in the second probe is a statement about an executed run. Three statement
  comments must say so, and the placement must keep this material out of
  `instances/psl211/tableau/`.
- Q9, landing the adapter falsifies two sentences that are in production
  today, in `instances/psl211/psl211_reading_constancy.v`.

## What was compiled for this audit

One file, `.../scratchpad/colour_audit/a_conv.v`, against production `.vo`
only (the probes' own `.vo` are stale against `manifest/pgg_tableau.vo` and
were not rebuilt, no repository file being written by this audit). All of it
compiled, rc 0:

| check | result |
|---|---|
| `a1 : seats = cards := erefl`, `a1b : seats = 'I_12 := erefl` | hold |
| `a2`: `psl211_colour_view secretP C u` = the colour reading's `ffun` body, by `erefl` | holds |
| `a3`: the same shape for `static_coalition_obs`, by `erefl` | `Fail` succeeds |
| `a4`: a one-seat coalition is below `profile_k` | holds |
| `a6`: `pgl27_coalition_trace R C (s, g) = static_coalition_obs C s g` from `pgl27_coalition_trace_E` and `pgl27_static_obsE` | holds, three classical axioms |
| `Print Assumptions s5_exec_endpoint_bound` | `rigidity_s5_instance.s5_group_order_eq` plus the three classical |
| `Print Assumptions five_card_repeated_endpoint_lt` | the three classical only |

## (I) Soundness of the second probe

| id | class | file:line | finding | rule, problem, evidence | replacement |
|---|---|---|---|---|---|
| Q1 | NOTE | `c_adapter.v:77-82` | `psl211_colour_sample` is an honest adapter over the dealer-dealt execution | `SampleAdapter` (`security/pgg_sample_adapter.v:111-123`) has four fields and no coherence condition, so honesty is read off the definition, not typed. Read: the law is exactly `psl211P secretP` (`psl211_colour_sample_lawE`, `by []`), which is `secretP `x (`U psl211_G_pos)` (`psl211_secrecy.v:230`); `sa_arg` is the first coordinate, the chirality, and `psl211_colour_inputTE` shows that coordinate's type is the plug's run-argument carrier `bool`; `sa_cut` is the second, the shuffle. The cut law lemma is right: `sa_cut_dist` is `fdistmap snd (psl211P secretP)`, computed to `` `U psl211_G_pos ``, which is the uniformity the cited colour theorems assume | keep |
| Q2 | **MUST** | `c_adapter.v:71-76`, `c_exact.v:58-67`, `c_reader.v:254-266` | no statement of this probe is about an executed run, and no landed comment says so | Only `psl211_alldecks_params` carries an endpoints statement (`instances/psl211/psl211_models.v:342`); `grep instance_endpoints_stmt instances/psl211/*.v` returns that one line. So the hypothesis `endpoint_eq` of `sa_coalition_viewE` (`security/pgg_sample_adapter.v:265`) cannot be discharged here, there is no Observed or Sampled level over `psl211_dealt_params`, and the probe's propositions are about the model's law and the static reading only. `LEDGER.md` says this under "What is left"; no statement comment does, and the ledger does not land | add to the adapter's comment and to both exactness comments: "The dealer-dealt parameters carry no endpoints statement, so this is a statement about the model's law and the static reading, and not about an executed run." |
| Q3 | **MUST** | `c_reader.v:105-112` | the comment on `psl211_colour_readerE` describes a reconciliation that is not there | It says the two sides "are not the same term: the model's view is indexed by a card position and the reader by a seat of the execution's starting interface, and they agree because this instance's seats start at the twelve card positions in order". Compiled: `a1` shows the seat type and the card-position type are one type here, and `a2` shows the left side is convertible to the reading's own `ffun` body by `erefl`, while the right side reduces to that body by two record projections, so the two sides of the lemma are one term. No `pi_starts` occurs on either side: `colour_view` (`reconstruct/design_privacy.v:122-125`) applies `rho u.2 i` and the probe's reading applies `@pgg_rho psl211_M g i`. The sentence is transplanted from `pgl27_static_obsE` (`instances/pgl27/pgl27_proximity.v:95-101`), where it is true because the left side is `static_coalition_obs`. The probe's own `LEDGER.md` states the correct version | "The model's colour view of a sample point is the colour reading's value at that point's run argument and cut. The two sides are the same term: the reading was written at the position index the model uses, so no seat reconciliation enters here. It enters one step later, at `psl211_colour_reading_factorsE`, where the framework's own reading indexes through `pi_starts`." (`a3` shows that step is real) |
| Q4 | NOTE | `c_reader.v:96-103,143-157` | C2 and C3 are otherwise right | The colour reading is a function of the coalition, the run argument and the cut by construction, and of nothing else. `psl211_colour_reader_funE` gives it as one function, which is what pushing forward along the cut law needs. The factorisation is stated in the direction that holds, card identities determine colours, with the explicit map `psl211_colour_of_reading`, which takes the coalition because the canonical reading returns card zero off the coalition and card zero is a heart | keep |
| Q5 | **MUST** | `c_reader.v:210-215` | `psl211_colour_of_reading_collides` is over-read | The comment ends "the colour reader is strictly coarser than the canonical one". What is compiled is a collision between two CONSTANT finite maps, all cards zero against all cards one; nothing says either is a value the canonical reading takes at this model. The lemma bounds the map, not the two readings | "Two finite maps that give a position of the coalition two different hearts have the same colour value, so the colour map is not injective and the identity of `psl211_colour_reading_factorsE` is a factorisation in one direction only. That the two readings themselves differ is not this lemma's content; it is `psl211_dealt_reading_indep_false`." |
| Q6 | **MUST** | `c_reader.v:186-190` | the negatives cited by `psl211_colour_indistinguishability_of_reading` do not say what the comment says | "over this adapter the canonical reader has no such proposition at any small number, by `psl211_canonical_reader_not_exact` below and by `psl211_dealt_constancy_false`". The first refutes exact independence, not a distance bound. The second refutes constancy, which is the indistinguishability proposition at zero (`coalition_reading_constancy`, `instances/psl211/psl211_reading_constancy.v:202`). The fiber counts give mass zero against mass 1/660 at one value, so the two laws are at sum of absolute differences at least 1/330 apart, and every number at or above that is open | "It transports a bound and produces none. At zero the canonical reading has no such proposition over this adapter, by `psl211_dealt_constancy_false`; at a positive number none is proved and none is refuted." |
| Q7 | **MUST** | `c_reader.v:262-263` | `psl211_canonical_reader_not_exact`'s comment contradicts its own file | "its theorem is not the image of any canonical-reader proposition over this adapter". `psl211_colour_indistinguishability_of_reading`, in the same file, sends a canonical-reading indistinguishability proposition at `c` to the colour reading at `c`. The compiled fact is narrower | "so the colour reading's exact independence is not the image of the canonical reading's, that one being false" |
| Q8 | **GO**, crux | `c_reader.v:267-312` | `psl211_canonical_reader_not_exact` is TRUE and is what it seems | Route checked step by step. `psl211_dealt_raw_countE` gives 0 and 1 by `vm_compute` over the 660 tabulated cuts; `psl211_dealt_fiberE` makes those the fibers' cardinalities, so the true fiber is empty and the false fiber has a witness. Positivity of `psl211P` at `(b, g)` follows from `secretP b != 0` and `g` in the group. Then `Pr[V = psl211_dealt_view] > 0`, `Pr[S = true] > 0`, and the joint is zero because the true fiber is empty; independence at `psl211_perdeck_coalition` (three seats, below six by `psl211_perdeck_coalition_below_k`) would make the joint that positive product. The reading is exactly the card-identity reading of the framework, `static_coalition_obs` at the dealt parameters. So: exact independence of the card-identity reading from the chirality FAILS at one coalition of three seats under the fixed-dealer model | keep the fact; fix Q7 and Q9 in its comment |
| Q9 | **MUST** | `instances/psl211/psl211_reading_constancy.v:57` and `:967` | landing the adapter falsifies two sentences in production | Both say "this tree carrying no dealt-mode sample adapter through which a certificate's ideal could be pinned to it". Landing `psl211_dealt_sample` makes both false. Also, Q8 is the probabilistic form of `psl211_dealt_constancy_false` (same coalition, same fibers, same counts) and its comment does not say so | rewrite both sentences to name the adapter and say what is still open (no certificate over it, the dealt parameters carrying no endpoints statement); add to Q8's comment one sentence placing it against `psl211_dealt_constancy_false` |
| Q10 | GO | `c_exact.v:68-75,87-115` | the thresholds meet exactly and C5 is a statement at six seats | `profile_k = 6` (`profile_k_psl211_algebra`), and `-ltnS` turns `#|C| < 6` into the cited `#|C| <= 5`, so the instance's five-position counting argument and the derived profile meet on the nose. `psl211_leak_coalition_card6` pins the refuting coalition at exactly six positions, equal to `profile_k`, and both positivity premises are present, so C4 and C5 bound each other. Stating C5 pointwise rather than as the negation of the proposition is correct, that coalition being outside the proposition's range | keep |
| Q11 | NOTE | `r_framework.v:99-102,268-273`; `c_reader.v:200-202` | what the landing must preserve from the first probe | The second probe applies `reader_indistinguishability_postprocessing` positionally with all five arguments after `{R A E sa}` are explicit, and uses `StaticReader {A} E`, `sr_read {A E}`, `coalition_reading_reader {A} E`, `ReaderExactPropAt {R A E} sa r {secretT} secret`. It also relies on the value-type field being a function of the coalition, which it instantiates constantly. Any change to the implicit and explicit split breaks these call sites as unification failures rather than as name errors | carry the `Arguments` lines unchanged into the landed file |
| Q12 | NOTE | — | the second probe depends on `r_framework.v` alone | `r_pgl27.v` and `r_marginals.v` are not used by it | — |

## (II) Naming

Rules applied: a name states what the thing is in the domain, never the shape
of its type; spelled out; MathComp's published suffix fragments (`E`, `_le`,
`_of`, `P`, `_false`); one word per concept tree-wide. Every replacement below
was checked free with `git grep -w` over all tracked `.v` files, `legacy`
included and `notes/` excluded, and with a recursive `grep -w` over
`mathcomp` and `infotheo` under
`/Users/cheng-huiweng/Projects/coq/_opam/lib/coq/user-contrib/`. All are free.

### The word for the concept

The tree already has an identifier word for this concept, and it is
"reading": `static_coalition_obs` is documented as "a coalition's static
endpoint reading" (`protocol/pgg_instance.v:476-480`), production carries
`coalition_reading_constancy` and the file
`instances/psl211/psl211_reading_constancy.v`, and the probes' own prose says
"the canonical card-identity reading". "Reader" is a second word for that
concept and buys nothing: to a paper's reader it suggests a person, while the
record is a family of reading functions indexed by the coalition. Decision:
**`Reader` becomes `Reading` everywhere**, and the landed prose says
"reading" and never "reader". The field prefix `sr_` survives the change.

| id | class | name, file:line | rule, problem | replacement |
|---|---|---|---|---|
| N1 | **MUST** | `StaticReader`, `r_framework.v:71` | "static" is the tree's word; "reader" is a second word for a concept the tree already calls a reading | `StaticReading`, constructor `MkStaticReading` |
| N2 | **MUST** | `sr_T`, `r_framework.v:72` | a bare `T` names the shape of the field and not what it is the type of; the tree's precedent is `sa_sampleT`, `ep_inputT`, which name the thing | `sr_readT` |
| N3 | NOTE | `sr_read`, `r_framework.v:73` | states what the field is | keep |
| N4 | **MUST** | `coalition_reading_reader`, `r_framework.v:80` | stutter, and it is precisely `static_coalition_obs` packaged | `static_coalition_reading` |
| N5 | SHOULD | `coalition_reading_readerTE`, `coalition_reading_readE`, `r_framework.v:86,92` | follow N4 | `static_coalition_readingTE`, `static_coalition_readE` |
| N6 | **MUST** | `ReaderIndistinguishabilityPropAt`, `r_framework.v:125` | follow N1; `At` is right, the proposition taking a number, as in the tree's `IndistinguishabilityPropAt` | `ReadingIndistinguishabilityPropAt` |
| N7 | **MUST** | `ReaderExactPropAt`, `r_framework.v:186` | two faults. `At` in this tree marks the number (`IndistinguishabilityPropAt cert c`, `IdealProximityPropAt cert c`, `idealproximity_prop_at2`), and this proposition takes none, the tree's own exact form being `ExactProp` with no `At`. And `ExactProp` (`manifest/pgg_tableau.v:501`) is a four-conjunct statement about the executed view, so a near-identical name for a one-conjunct statement about the static reading invites a reader to take one for the other | `ReadingExactIndependence` |
| N8 | **MUST** | `reader_indistinguishability_canonicalE`, `r_framework.v:137` | "canonical" names no object; the equation is at one named reading | `reading_indistinguishability_static_coalitionE` |
| N9 | SHOULD | `reader_indistinguishability_postprocessing`, `r_framework.v:149` | post-processing is the literature's word for this inequality and states the relation; only the first word needs the N1 change | `reading_indistinguishability_postprocessing` |
| N10 | SHOULD | `reader_exact_of_witness`, `r_framework.v:196` | `_of_` is right; follow N7 | `exact_independence_of_witness` |
| N11 | SHOULD | `reader_exact_executed`, `r_framework.v:205` | names neither direction | `exact_independence_executed_of_reading` |
| N12 | NOTE | `SeatMarginalPropAt`, `CutMarginalPropAt`, `r_framework.v:228,241` | correct as they stand: "marginal" is the law being compared, "seat" and "cut" say which, `At` marks the number. "Proximity" must NOT be used here, it being the name of a security property in this tree | keep |
| N13 | **MUST** | `seat_marginal_at_two`, `cut_marginal_at_two`, `r_framework.v:255,261` | the tree's precedent for this shape is `idealproximity_prop_at2` (`manifest/pgg_tableau_security_property_relations.v:175`), and the spec's own landing plan already writes the names that way | `seat_marginal_prop_at2`, `cut_marginal_prop_at2` |
| N14 | **MUST** | `s5_exec_endpoint_bound_as_marginal`, `r_marginals.v:56` | "as a marginal" marks a restatement rather than stating the claim | `s5_word_seat_marginal` (the spec's own name) |
| N15 | **MUST** | `five_card_repeated_endpoint_as_marginal`, `r_marginals.v:75` | same, and "endpoint" is wrong here: the reading is the position the cut sends one starting position to, not what a seat holds | `five_card_repeated_cut_marginal` |
| N16 | **MUST** | the PGL(2,7) identification lemma, to be landed | the probe states it twice at readings (`pgl27_reading_of_trace`, `pgl27_trace_of_reading`, `r_pgl27.v:97,110`); the landed one carries no reading record | `pgl27_coalition_trace_static_obsE`, sitting beside `pgl27_static_obsE`, whose name it continues. Compiled here as `a6` |
| N17 | **MUST** | `psl211_colour_sample`, `c_adapter.v:77` | the adapter is not colour-specific: `psl211_canonical_reader_not_exact` uses the same adapter for the card-identity reading. The tree names an adapter after its model, `psl211_alldecks_sample` | `psl211_dealt_sample`, and `psl211_dealt_sample_lawE`, `_argE`, `_cutE`, `_cut_distE` |
| N18 | SHOULD | `psl211_colour_inputTE`, `c_adapter.v:67` | nothing about colour; it is the dealt plug's run-argument carrier | `psl211_dealt_inputTE` |
| N19 | **MUST** | `psl211_colour_reader`, `c_reader.v:96` | follow N1 | `psl211_colour_reading` |
| N20 | **MUST** | `psl211_colour_readerE`, `psl211_colour_reader_funE`, `c_reader.v:113,125` | follow N1 | `psl211_colour_readingE`, `psl211_colour_reading_funE` |
| N21 | NOTE | `psl211_colour_of_reading`, `c_reader.v:143` | states what it is, `_of_` idiomatic | keep |
| N22 | **MUST** | `psl211_colour_reader_factorsE`, `c_reader.v:153` | follow N1 | `psl211_colour_reading_factorsE` |
| N23 | SHOULD | `psl211_colour_indistinguishability_of_reading`, `c_reader.v:191` | ambiguous: the colour view is a reading too, so "of reading" does not say which | `psl211_colour_indistinguishability_of_coalition_reading` |
| N24 | **MUST** | `psl211_perdeck_static_view`, `c_reader.v:238` | collides in the reader's mind with `psl211_perdeck_view` (`instances/psl211/psl211_models.v:796`), which is a single finite map and not a random variable | `psl211_dealt_perdeck_reading` |
| N25 | SHOULD | `psl211_canonical_reader_funE`, `c_reader.v:246` | follow N24 | `psl211_dealt_perdeck_readingE` |
| N26 | **MUST** | `psl211_canonical_reader_not_exact`, `c_reader.v:267` | the tree's suffix for a refuted proposition is `_false` (`psl211_dealt_constancy_false`, `psl211_alldecks_constancy_false`); "not_exact" also hides which proposition is refuted | `psl211_dealt_reading_indep_false`, beside `psl211_dealt_constancy_false` in wording and in place |
| N27 | SHOULD | `psl211_colour_reader_exact`, `c_exact.v:68` | the tree's word for this conclusion is `_indep` (`psl211_colour_view_indep`, `psl211_alldecks_static_indep`) | `psl211_colour_reading_indep` |
| N28 | SHOULD | `psl211_colour_reader_dep_at_threshold`, `c_exact.v:102` | the tree's precedent names the size: `psl211_colour_view_dep_k6` | `psl211_colour_reading_dep_k6` |
| N29 | NOTE | `psl211_leak_coalition_not_below_k`, `c_exact.v:87` | `profile_k` is the tree's field name, so `_below_k` is the tree's word | keep |

## (II) Statement comments and headers

Checked against the statement each is attached to.

| id | class | file:line | sentence | problem | replacement |
|---|---|---|---|---|---|
| S1 | **MUST** | `r_framework.v:64-70` | "What a reader omits is the interpreter state: a static reader sees the run argument and the shuffle and nothing of the messages the run exchanged, which is why a statement made at a reader is a statement about a group action." | False of the type, as audit P15 found and as the second probe confirms: the record constrains the arguments and the value type and nothing else. The second clause is a non-sequitur | the sentence drafted at `c_reader.v:86-95`, moved here: "A static reading of an execution is a family of functions of the coalition, the run argument and the cut, valued in a finite type that may depend on the coalition. That is the whole of what the type constrains: it does not say that a reading is a group action, nor that it ignores the interpreter's messages. That a given reading is a function of the dealt deck and the cut alone is a theorem about it." |
| S2 | SHOULD | `r_framework.v:4-19` | "the framework has no name for them. A static reader is that missing name" | roadmap, and the header's job is to say what the file holds | state the object: the propositions of the framework with the reading left free, and the framework's own propositions as their values at the coalition's static reading |
| S3 | SHOULD | `r_framework.v:123-124` | "A finer reader makes the statement stronger" | "finer" is used before anything defines it; the file's own order on readings is "the second factors through the first", fixed by `reading_indistinguishability_postprocessing` below | "A reading through which another factors carries the same number to it" |
| S4 | **MUST** | `r_framework.v:184-185` and `c_exact.v:65-67` | "the entropy forms the framework derives from an exact-independence witness are available at it" | uncompiled. The tree derives the entropy forms inside `ExactProp` at the executed coalition view (`manifest/pgg_tableau.v:501-522`) and `exact_tail` transports them along `sampled_viewE_prop`; neither is available at an arbitrary reading, and this probe compiles no entropy form | either compile one entropy corollary at the colour reading, or write "an independence and not a numeric bound, so it is the conjunct the framework's entropy forms are derived from, and those forms are not restated here" |
| S5 | SHOULD | `r_framework.v:226-227` | "It carries no constructor of the framework's security evidence for that reason." | a proposition does not carry a constructor; type-honest phrasing | "It is not one of the three propositions the security evidence proves." |
| S6 | NOTE | `r_framework.v:231,236` | the `0` in `sa_seat_dist ... 0 i` and the executed layer it indexes are unexplained | a reader cannot tell which run index is meant | name it in the comment |
| S7 | **MUST** | `r_marginals.v:51-55` | the S_5 instance's comment | misses the factor two that the spec's decision requires (the sum of absolute differences is twice the literature's total variation), and misses the assumption: `Print Assumptions s5_exec_endpoint_bound` reports `rigidity_s5_instance.s5_group_order_eq` | add both: the number is in the sum of absolute differences, twice the literature's total variation, and the bound rests on the S_5 group-order axiom |
| S8 | **MUST** | `r_marginals.v:69-74` | the five-card instance's comment | misses that the cited theorem `five_card_repeated_endpoint_lt` is STRICT and the proposition is stated at `<=` through `ltW`, which the spec's decision requires; misses the factor two | add both. `Print Assumptions five_card_repeated_endpoint_lt`: the three classical only, worth saying beside S7 |
| S9 | **MUST** | `c_adapter.v:4-13`, `c_reader.v:4-20`, `c_exact.v:4-16`, and every `(** ... *)` carrying one | "PROBE FILE. Nothing permanent requires it. Ledger row C1 of ..." | status markers and plan tokens | delete on landing; the boxed index of Definitions and Key results is the tree's convention and stays |
| S10 | **MUST** | `c_adapter.v:15-25` | "The all-decks mode does not fit ... which is why this row is construction rather than restatement." | rejected alternatives and effort narration in a rendered comment | keep one declarative sentence, that the run argument of these parameters is the chirality itself and that is what the colour view reads; move the comparison with the all-decks adapter to a source comment |
| S11 | **MUST** | `c_adapter.v:71-76` | "It is the adapter every colour statement of psl211_secrecy.v is read at once that statement is made at a reader." | roadmap, and it omits the position Q2 names | replace with the Q2 sentence plus: "one sample point is a chirality bit and a cut, the bit from the prior and the cut uniform on PSL(2,11), the two independent" |
| S12 | **MUST** | `c_reader.v:10-20` | the whole C7 paragraph, about the first probe's comment being false | history of the probes | delete; the corrected sentence lives on the record (S1) |
| S13 | **MUST** | `c_reader.v:86-95` | the record's replacement sentence, pinned to `psl211_colour_reader` | long exposition pinned to a declaration it does not track | move to the record (S1); leave here only what the colour reading is |
| S14 | **MUST** | `c_reader.v:105-112` | see Q3 | false | see Q3 |
| S15 | **MUST** | `c_reader.v:210-215`, `:186-190`, `:262-263` | see Q5, Q6, Q7 | over-read | see Q5, Q6, Q7 |
| S16 | SHOULD | `c_exact.v:61-63` | "the same theorem, the same model, the same coalitions, and no new mathematics" | effort narration | "It is `psl211_colour_view_indep` of `instances/psl211/psl211_secrecy.v` stated at the colour reading over this adapter." |
| S17 | SHOULD | `c_exact.v:10-16` | "The mathematics is the cited theorems' and none is added here" | effort narration | state what the file holds |
| S18 | NOTE | `c_exact.v:83-86,91-101` | the two C5 comments | accurate, including that the refuting coalition is a block of one of the two Steiner systems and that the positivity premises are part of the mathematics | keep, with the N27 and N28 names |

## Proposed final names

Framework leaf file:

```
StaticReading            MkStaticReading       sr_readT       sr_read
static_coalition_reading static_coalition_readingTE           static_coalition_readE
ReadingIndistinguishabilityPropAt              reading_indistinguishability_static_coalitionE
reading_indistinguishability_postprocessing
ReadingExactIndependence exact_independence_of_witness
exact_independence_executed_of_reading
```

Marginal-bound leaf file:

```
SeatMarginalPropAt   CutMarginalPropAt   seat_marginal_prop_at2   cut_marginal_prop_at2
```

Instances:

```
s5_word_seat_marginal                five_card_repeated_cut_marginal
pgl27_coalition_trace_static_obsE
psl211_dealt_sample   psl211_dealt_sample_lawE   psl211_dealt_sample_argE
psl211_dealt_sample_cutE             psl211_dealt_sample_cut_distE
psl211_dealt_inputTE
psl211_colour_reading     psl211_colour_readingE     psl211_colour_reading_funE
psl211_colour_of_reading  psl211_colour_reading_factorsE
psl211_colour_of_reading_collides
psl211_colour_indistinguishability_of_coalition_reading
psl211_colour_reading_indep
psl211_leak_coalition_not_below_k    psl211_colour_reading_dep_k6
psl211_dealt_perdeck_reading         psl211_dealt_perdeck_readingE
psl211_dealt_reading_indep_false
```

## Placement

`_CoqProject` lists its 224 `.v` files one by one, so each new file needs a
line in it.

| what | where | why, and the arrows |
|---|---|---|
| `StaticReading`, `static_coalition_reading` and its two equations, `ReadingIndistinguishabilityPropAt`, `reading_indistinguishability_static_coalitionE`, `reading_indistinguishability_postprocessing`, `ReadingExactIndependence`, `exact_independence_of_witness`, `exact_independence_executed_of_reading` | new leaf `manifest/pgg_tableau_reading.v` | requires `manifest/pgg_tableau.v` (for `IndistinguishabilityPropAt`, `ExactWitness`, `IndistinguishabilityCert`) and `security/pgg_sample_adapter.v`; nothing in `manifest/` requires it, only the instance files below. Header: what a static reading of an execution is, that the framework's propositions are its values at the coalition's static reading, and that a reading is not by itself security evidence, a program still being the thing that certifies a security property |
| `SeatMarginalPropAt`, `CutMarginalPropAt`, `seat_marginal_prop_at2`, `cut_marginal_prop_at2` | new leaf `manifest/pgg_tableau_marginal_bounds.v`, as the spec's 4.4 plan has it | kept apart from the reading file on purpose: a marginal bound is about one seat or one position, with no coalition, no second run argument and no secret, and is not a statement at a reading. Requires `security/pgg_sample_adapter.v` and `lib/var_dist_supp.v`, not the reading file |
| `s5_word_seat_marginal` | `instances/s5/tableau/s5_tableau_sampled.v` | beside the paragraph that already explains the word model; the file is above the manifest leaf |
| `five_card_repeated_cut_marginal` | `instances/kim2025/tableau/five_card_tableau_sampled.v` | beside `five_card_repeated_endpoint_lt`, which it weakens to `<=` |
| `pgl27_coalition_trace_static_obsE` | `instances/pgl27/pgl27_proximity.v`, immediately after `pgl27_static_obsE` | the lowest file that sees both halves: it defines `pgl27_static_obsE` and reaches `pgl27_coalition_trace_E` through `pgl27_models.v` → `pgl27_trace.v`. No new import, and no import from the framework into a mathematics file. Compiled here as `a6`, three classical axioms |
| `psl211_dealt_sample` and its four equations, `psl211_dealt_inputTE`, `psl211_colour_reading` and its two equations, `psl211_colour_of_reading`, `psl211_colour_reading_factorsE`, `psl211_colour_of_reading_collides`, `psl211_colour_indistinguishability_of_coalition_reading`, `psl211_colour_reading_indep`, `psl211_leak_coalition_not_below_k`, `psl211_colour_reading_dep_k6`, `psl211_dealt_perdeck_reading`, `psl211_dealt_perdeck_readingE`, `psl211_dealt_reading_indep_false` | new file `instances/psl211/psl211_colour_reading.v` | it must see both `psl211_secrecy.v` (for `psl211P`, `psl211_colour_view`, the two colour theorems, `psl211_leak_coalition`) and `psl211_reading_constancy.v` (for `psl211_dealt_static_obsE`, `psl211_dealt_raw_countE`, `psl211_dealt_fiberE`, `psl211_dealt_view`), and no existing file sees both: `psl211_reading_constancy.v` does not require `psl211_secrecy.v`. It requires `manifest/pgg_tableau_reading.v`. Against the freeze: `psl211_endpoints.v` requires only `psl211_exec.v` and two framework files, so the new file is above its forward closure and is required by nothing in it |
| nothing | `instances/psl211/tableau/` | the dealer-dealt parameters carry no endpoints statement, so there is no Observed or Sampled level over them and no program, no path and no manifest row is owed (Q2) |

Arrows stay upward: the two manifest leaves are required only by instance
files; `instances/psl211/psl211_colour_reading.v` is a leaf of its instance
and is required by nothing, in particular not by
`instances/psl211/tableau/*`; the PGL(2,7) lemma adds no import at all.

Two production edits the landing owes, outside the new files: Q9, the two
sentences in `instances/psl211/psl211_reading_constancy.v` that say the tree
carries no dealer-dealt sample adapter.
