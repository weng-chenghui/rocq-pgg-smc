# The reading as a coordinate of the security claim, and one preposition per meaning in the surface (2026-09-21)

Spec with claim ledger, written before any probe. Owner's decision of
2026-09-21, after a discussion in chat: the proposal table below "looks good,
do it". Workflow: probe first (this spec, a probe under
`notes/probes/2026-09-21-reading-index/`, two audits, fold, landing plan,
landing, audit of the landing).

## 1. The problem

The manifest describes a capability by four coordinates: theorem,
distribution, observer, notion. Its definition of AnalysisBridged says the
bridged theorem is "about the same distribution and the same observer". A
Tableau program supplies three of the four: `sample f` names the distribution,
the security evidence is the theorem, the security property is the notion. The
observer is fixed: every proposition of `manifest/pgg_tableau.v` is stated at
a coalition's endpoint reading (`static_coalition_obs`, and the executed
coalition view the link lemma of the Sampled level identifies with it).

Two things the repository has proved cannot be written as programs because of
that:

1. At PSL(2,11), over one model, exact independence holds at the colour
   reading below the threshold of six (`psl211_colour_reading_indep`) and is
   false at the card-identity reading at one coalition of three seats
   (`psl211_dealt_reading_indep_false`). What a designer wants to say is both
   sentences about one model. `manifest/pgg_tableau_reading.v` states the
   propositions with the reading free, and no program reaches them.
2. The manifest's Path 2 has two capability lines with two observers
   (coalition endpoints and the content trace). The Tableau publishes the
   first.

Reading the surface aloud, term by term, found a second problem, independent
of the first: prepositions carry several meanings, and two clauses have no
preposition at all.

- `at` means a coalition size in `leaks at k` and a real field with an index
  in `InputIndistinguishability at R idx b`.
- The evidence of a certify statement is written bare
  (`certify ExactIndependence w`), while every terminal introduces its proof
  with `by`.
- The assumption status is a bare last term. In
  `|> publish Obstruction o by pf a` it reads as `pf` applied to `a`.

## 2. Decisions (owner-approved table)

| Slot | Today | Decided |
|---|---|---|
| evidence of a certify statement | bare | `by e` |
| reading of a certify statement | none | `of r`, omitted means the coalition's endpoint reading |
| reading of an obstruction | none | inline in the terminal: `s \|> publish Obstruction InputDistinguishability of r at c by pf assuming a` (owner, 2026-09-21, second decision: the earlier spelling with a leading `obstruction` keyword read aloud as "publish Obstruction (obstruction ...)" once inlined; the inline rule reserves no new keyword, `InputDistinguishability` follows the literal `Obstruction` and stays an identifier, and the program's own line shows the reading and the number; `c` is a number per real field, as the bound of `conclude` is) |
| number of a conclude terminal | bare after the action word | `s \|> conclude at c by p` (owner, 2026-09-21) |
| marginal bound of the five-clause certify rule | bare after the slot `idx` | `at R idx by b` (main session's ruling on the naming audit's N20, same principle; the owner was asked and answered the other two) |
| assumption status of every publish rule | bare last term | `assuming a` |

One preposition per meaning: `of` introduces what is read, `at` a number, a
size or a real field with its index, `by` a proof or a piece of evidence, `assuming` an
assumption status. `under` was rejected: it is an ssreflect tactic with 363
uses in the tree, and whether a notation token breaks them was not measured.
`assuming` occurs in no code of the tree (five files use the word in
comments).

Every existing program is migrated to the decided surface in the same landing.
The migration is notation only.

## 3. Design

### 3.1 Placement by phase

The reading is a coordinate of the security claim, so it belongs to the step
from Sampled to AnalysisBridged. It is not chosen at Observed: two programs
that differ only in the reading share their Sampled value (the PSL(2,11) case
is exactly that), and choosing the reading earlier would force them apart from
Observed on. It is not a new completion level: it carries no new object, it
indexes the evidence the existing level carries.

### 3.2 First version: a reading is a function of the coalition's endpoints

```coq
Record EndpointReading := MkEndpointReading {
  er_readT : {set seats} -> finType ;
  er_of_endpoints : forall C : {set seats},
    {ffun seats -> cards} -> er_readT C }.
```

The static form is `fun C x g => er_of_endpoints C (static_coalition_obs C x g)`
and the executed form is `er_of_endpoints C \o sa_coalition_view ... 0 C`, so
the link lemma of the Sampled level carries every reading of this kind to the
executed run with no further premise, and every program remains a statement
about an execution. The default is the identity at every coalition. A reading
that is not a function of the endpoints (a transcript with messages) needs a
link lemma of its own and is not built; `StaticReading` of
`manifest/pgg_tableau_reading.v` stays as the general notion and a lemma sends
an `EndpointReading` to it.

Names are provisional until the naming audit.

### 3.3 Where the reading sits in the types (preferred, with a fallback)

Preferred: the three records gain an index, `ExactWitness sa r`,
`IndistinguishabilityCert sa r`, `IdealProximityCert sa r`, their fields are
stated at `r` (`ew_indep`, `ic_const`, `ipc_close`; the ideal's witness of a
proximity certificate is at the same `r`), and each constructor of
`SecurityEvidence sa` packs its reading. `SecurityEvidence sa`, the payloads,
`StackAt` and every terminal keep their types. A reader `reading_of`, beside
`security_property_of`, returns the reading of a published program. With the
index, the clause `of r` of the surface is a type ascription on the evidence,
so a program's text cannot name a reading its evidence is not about.

Fallback, if the index makes existing instance files fail to typecheck in a
way a notation cannot absorb: the reading as a first field of each record.

### 3.4 Propositions

`ExactProp`, `IndistinguishabilityPropAt`, `IdealProximityPropAt` and
`InputDistinguishabilityPropAt` are restated at the reading of their evidence
(the last at an explicit `r`). At the default reading each must be CONVERTIBLE
with today's proposition, which is what keeps every existing `exact: erefl`
equation and every instance proof as it is. `exact_tail`,
`indistinguishability_tail`, `idealproximity_tail`,
`indistinguishability_number_ge_of_input_distinguishability` and
`no_indistinguishability_cert_ideal_close_of_input_distinguishability` are
reproved at a free reading; the number bound AS STATED pairs an obstruction
and a certificate at one reading. Across two readings it needs a
factorisation: an obstruction at a reading that factors through `r` is an
obstruction at `r` at the same number (the soundness audit compiled it), so an
obstruction at any reading is one at the endpoint reading, the finest.
Post-processing: evidence at a reading gives the proposition at every reading
that factors through it, at the same number
(`reading_indistinguishability_postprocessing` is the existing form).

### 3.5 Surface

```coq
s certify ExactIndependence by w                       (* default reading *)
s certify ExactIndependence of r by w
s certify InputIndistinguishability of r by c
s certify IdealProximity of r by c
s |> publish t assuming a
s |> publish Observed assuming a
s |> publish Sampled t assuming a
s |> publish Obstruction InputDistinguishability of r at c by pf assuming a
s |> conclude at c by p
```

The five-clause input-indistinguishability rule is at the default reading and
its header says so; its marginal bound follows `by` (`at R idx by b`). A
`leaks` annotation beside `of r`, and an `of r` form of the five-clause rule,
were struck after the audits: nothing in the tree would call them.

### 3.6 Instances

- PSL(2,11), the motivating pair, over the fixed-dealer colour model
  `psl211_dealt_sample`: a program certifying exact independence of the colour
  reading, and the card-identity sentence. The second is an independence that
  fails, not an inequality between two run arguments, so whether it is an
  obstruction of the existing kind at some number is a ledger row and not
  assumed.
- The all-decks obstruction at 1/660 is restated at the default reading.
- PGL(2,7): the content trace is the endpoint reading under a second name
  (`pgl27_coalition_trace_static_obsE`), so a second program there would be
  the first program's term. Not landed unless an audit finds a sentence it
  adds; recorded.

## 4. Not built, recorded

- One-seat and one-position marginal bounds stay outside the language: they
  have no coalition, no second run argument and no secret, and folding them
  into a reading would present them as security evidence.
- A public reading that does not depend on the coalition (the cards Kim's
  protocol opens at the end) is not a function of one coalition's endpoints.
- Transcript readings with messages.
- The slot after `publish` holds a transfer status in one rule, a level in two
  and the published object in one. `assuming` does not change that; recorded.

## 5. Soundness invariants

1. No new axiom, no `Admitted` in a permanent file; `Print Assumptions` on
   every new theorem reports the three classical axioms, and
   `s5_group_order_eq` only where the cited S_5 theorem already has it.
2. Attack model unchanged: a static coalition of fewer than `profile_k` seats.
   A reading changes what that coalition is granted to see, never who it is.
3. Every number bounds a sum of absolute differences, twice the total
   variation distance of the literature; a distinguisher's advantage is at
   most half of it. A `<=` bound is not the distance.
4. A coarser reading can only help the designer for input
   indistinguishability (post-processing, proved; for ideal proximity it is
   expected and NOT proved), and for exact independence the implication
   runs from the finer reading to the coarser and not back; PSL(2,11) is the
   witness that the converse fails. No comment may say a reading "is secure"
   without naming the reading and the property.
5. The number bound and the exclusion of certificates are STATED at one
   reading. That is a scope of the lemmas and not a fact about obstructions:
   distinguishability is monotone along a factorisation, from the coarser
   reading to the finer, and the endpoint reading is the finest. An
   obstruction at the endpoint reading therefore excludes certificates at that
   reading and leaves certificates at a coarser reading open; every comment
   on such a statement names the reading.
6. At the default reading the four propositions are convertible with
   today's, checked by `erefl` against verbatim copies. The record types are
   distinct inductives, so statements that bind a witness or a certificate
   change their types (43 annotation sites, no proof script), and five of
   them narrow to the default reading.
7. Frozen files are not edited. If a transfer lemma in a frozen file is
   stated at `static_coalition_obs` alone, its generalisation goes in a file
   that is not frozen.

## 6. Claim ledger

| id | claim | passes when |
|---|---|---|
| K1 | `assuming` can be reserved: it follows the slot `t` in `publish t assuming a` | a file requiring the surface with the new rules compiles; every file of the tree that requires the surface still compiles (the landing's closure pass); a grep finds no code use |
| K2 | `of` and `by` after the evidence constructors' names reserve nothing new | the three constructor names stay usable as identifiers in a file requiring the surface (`Check ExactIndependence.`), measured as on 2026-09-19 |
| K3 | `certify X by e` and the old bare rule cannot coexist ambiguously; the bare rule is removed | every program of the tree written in the new surface compiles; a `Fail` records the old spelling's rejection, message read |
| K4 | `InputDistinguishability of r at c` as a notation: whether its leading token becomes a keyword, and what that breaks | measured; if it reserves a twenty-first keyword the ledger says so and the alternative (plain application of the constructor) is compared |
| K5 | `EndpointReading` with the identity default: `ExactProp`, `IndistinguishabilityPropAt`, `IdealProximityPropAt`, `InputDistinguishabilityPropAt` at the default are convertible with today's | four `erefl` equations against verbatim copies of today's definitions |
| K6 | the index design of 3.3 lets one existing instance witness and one existing certificate typecheck with no change to their proof scripts | `pgl27_exact_witness`, `pgl27_word_cert` and `kim` proximity certificate rebuilt in the probe against the probe's framework copy; otherwise the fallback is probed |
| K7 | `exact_tail` at a free reading | `Qed`, from the link lemma and `ew_indep` at `r` |
| K8 | `indistinguishability_tail` at a free reading; which transfer lemma it uses and whether that lemma is stated for an arbitrary function of the cut | `Qed`; the lemma's file and statement recorded; invariant 7 checked |
| K9 | `idealproximity_tail` at a free reading | `Qed` |
| K10 | the number bound and the exclusion of certificates with a close ideal, at a free reading, same reading on both sides | `Qed`; a mutation with two different readings fails to typecheck or to prove |
| K11 | post-processing: evidence at `r` gives each of the three propositions at `r'` whenever `r'` factors through `r` (for exact independence this is the fourth conjunct of `ExactProp`) | `Qed` for the three |
| K12 | the PSL(2,11) colour reading is an `EndpointReading` | a definition and an `erefl` or a one-line lemma equating its static form with `psl211_colour_reading` |
| K13 | `psl211_dealt_sample` is the sample of an analysis model family over the program's own observed execution, with its link lemma, so a Sampled value exists | the family, the Sampled program and `StackProp Sampled` compile |
| K14 | the colour program: `... certify ExactIndependence of psl211_colour_reading by w |> publish ... assuming ...` | compiles; `reading_of` and `security_property_of` equations by `erefl`; `Print Assumptions` |
| K15 | the card-identity sentence as an obstruction: is there a number `c > 0`, a coalition of three seats and two run arguments with readings `c` apart under the fixed-dealer model | proved with its number, or NO-GO with the reason (the known theorem is a failed independence, which does not give two run arguments by itself) |
| K16 | migration is notation only | for one program per instance, old surface term `=` new surface term by `erefl` in the probe |
| K17 | vacuity: the hypothesis set of K7 to K11 is jointly satisfiable | instantiated at the PGL(2,7) exact model with the default reading |
| K18 | every changed record keeps the traps away: no `by []` across terminals, no `rewrite` with the two PSL(2,11) mass lemmas | timings of the PSL(2,11) probe files recorded, each under 120 s |

## 7. Order of work

1. Wait for the landing in flight (positivity of a published obstruction's
   number, the manifest's twelfth path) to be committed: it edits
   `manifest/pgg_tableau.v`.
2. Probe: a copy of the framework files under the probe directory with the
   probe's `-Q` first on the load path, K1 to K18, mutation checks, one Rocq
   process at a time.
3. Two Opus audits of spec and probe (soundness, asked also "what is worth
   landing"; naming and surface, asked to read every program aloud term by
   term).
4. Fold, landing plan, landing in two commits: surface migration (notation
   only), then the reading index with the PSL(2,11) programs.

## 8. Probes and audits, folded (2026-09-21)

Records: `notes/probes/2026-09-21-reading-index/` (`surface/`, `surface2/`,
`index/`, `index2/`, `audit-naming/`, `audit-soundness/`, `RULINGS.md`). The
rulings file is the authority where it and the sections above differ; the
differences are these.

- The record is `CoalitionReading A`, indexed by the algebra alone, fields
  `cr_readT`, `cr_read`; the default is `coalition_endpoint_reading`. One
  record for the tree if the restatement of `psl211_colour_reading.v` is
  annotations only (probe B round 3 measures it).
- The reading does not enter every payload. A payload that is a dependent
  pair made the conversion between two spellings of one program reduce the
  whole Sampled coordinate (64.6 s for one `exact: erefl`). Each property has
  two statements: the one that names no reading keeps production's payload
  and body, and its twin `certify_reading_*` takes the reading. Measured:
  8.6 s against a 6.8 s baseline, every `exact: erefl` at most 0.004 s, no
  raw-bind site changes, 43 annotation changes in all.
- Ledger: K1 GO (`assuming` is the twentieth keyword), K2 GO, K3 GO (66 sites),
  K4 measured (a notation's leading literal is reserved; the owner chose the
  inline obstruction rule, which reserves nothing), K5 to K10 GO, K11 GO for
  input indistinguishability and for the exact witness, NOT proved for ideal
  proximity, K12 to K14 GO, K15 GO at 1/660 with `psl211_perdeck_coalition`
  and the two chiralities, K16 GO, K17 GO as joint inhabitation over one
  algebra (not one model), K18: no file over 120 s after round 2.
- K13 corrected a sentence of the tree: the dealer-dealt parameters do have
  an endpoints statement, `profile_endpointsE psl211_profile_endpoints`, one
  line, so there is an Observed and a Sampled level over them.
- Problem 2 of section 1 (the second observer of the manifest's Path 2) is
  NOT addressed: the content trace is the endpoint reading under a second
  name, and a second program would be the first program's term.
- A manifest path for the colour program is a later unit (the raw theorem
  must sit below the manifest, as for the twelfth path).

## 9. Landing plan

Two commits, each landed by an Opus rocq-prover, verified by the main session
(closure recompile with `scripts/comment_pass/`, fidelity file against
production, `Print Assumptions`), then one combined Opus audit of the landed
comments and a comments-only fix pass.

1. **Surface.** `manifest/pgg_tableau_syntax.v` and every program of the four
   `instances/*/tableau/` directories: certify evidence after `by`, the
   five-clause bound after `by`, `conclude at c by p`, every publish rule
   ends `assuming a`, the obstruction published inline (without the reading
   until commit 2). Source: `surface2/staged/`. Notation only: every existing
   equation still by `exact: erefl`; the header's keyword paragraph from probe
   A round 2's corrected draft, with the two categories of words. Rejections
   of the old spellings recorded with their messages.
2. **Reading index.** `manifest/pgg_tableau.v` (record, default, index on the
   three records, twin statements, tails, `reading_of` and the `_readingE`
   lemmas, `ReadingIndistinguishabilityPropAt`, obstruction kind with its
   reading), `manifest/pgg_tableau_reading.v` (reduced to lemmas about
   readings, with the three monotonicity lemmas),
   `manifest/pgg_tableau_security_property_relations.v` (14 sites, the
   constant-reading record), `manifest/pgg_tableau_syntax.v` (`of r`), the 43
   annotation sites, `instances/psl211/psl211_models.v` (dealer-dealt endpoints
   and observed execution), `instances/psl211/psl211_colour_reading.v`
   (restated, header corrected), new
   `instances/psl211/tableau/psl211_tableau_dealt.v` (family, Sampled value,
   colour program, endpoint-reading obstruction at 1/660), comments of the
   narrowed statements. Source: `index2/staged/` and `index2/k*.v`. Trap for
   the prover: at PSL(2,11) discharge the reading wrapper in a `have` naming
   one chirality before any goal holds both.

