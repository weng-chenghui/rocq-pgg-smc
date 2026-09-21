# Rulings on the two audits of the reading index (2026-09-21)

Audits: `audit-naming/REPORT.md` (N1 to N43), `audit-soundness/REPORT.md`
(S1 to S23), both GO-WITH-CHANGES, both by an Opus agent; each report was
saved by the main session from the auditor's hand-back. Rulings by the main
session. Owner's decisions of the same day are marked OWNER.

## Design rulings

1. **One reading record.** `CoalitionReading A` in `manifest/pgg_tableau.v`,
   fields `cr_readT`, `cr_read`: a reading of a coalition's endpoints, a
   function of them. The default keeps the name `coalition_endpoint_reading`,
   which is the phrase 29 comment sites already use for the endpoints
   themselves. `StaticReading`, `static_coalition_reading` and the bridge are
   retired if probe B's round 3 measures that `psl211_colour_reading.v`
   restates over the one record with annotation changes only; otherwise the
   two records stay and only the duplicate proposition names go. Answers N1,
   N2, N10, N11, N12, N15, N18, S11. The auditor's `EndpointFactoredReading`
   is not taken: with one record there is nothing for "factored" to separate
   it from.
2. **One free-reading proposition**, under the production name
   `ReadingIndistinguishabilityPropAt sa r c` (reading first as a qualifier,
   `At` binds the number, N3), defined in `pgg_tableau.v`. The other two
   wrappers are inlined (N4). Exact independence is post-processed on the
   witness and ideal proximity on the certificate, so neither needs a free
   form; neither post-processing lands (no caller; ideal proximity is not
   proved).
3. **Two statements per property** (probe B round 2): the statement that
   names no reading keeps production's payload type and body, and its twin
   takes the reading. Reading first as a qualifier: `certify_reading_exact`,
   `certify_reading_indistinguishability`, `certify_reading_idealproximity`
   (N5, N6). This is what removed the 64.6 s conversion; measured 8.6 s
   against a 6.8 s baseline.
4. **The observer.** The manifest's word "observer" stays: its column lists
   every random variable a capability line is about, the secret among them,
   so it is wider than a reading. New text says the observer of a capability
   line about a coalition is a reading, and never uses "observer" for the
   party (N19, N38). The spec's invariant 2 keeps "a static coalition of fewer
   than profile_k seats" as who, and the reading as what it is granted to see.
5. **What tells two programs apart (S6, S7, S8).** A program certified at a
   reading that grants the coalition nothing is a well-typed published value
   with the same path and the same security property as the real one;
   `reading_of` is the only coordinate that separates them. Rulings: (a) a
   framework lemma per statement, in the style of `certify_exact_propertyE`,
   says a program whose certify statement names no reading has
   `reading_of ... R idx = coalition_endpoint_reading _`; (b) every program
   that names a reading carries its own `_readingE`; (c) every such equation
   quantifies over the real field and the index; (d) the constant-reading
   vacuity record lands in `pgg_tableau_security_property_relations.v` beside
   the constant-secret ones (S1). The manifest path stays as it is in this
   landing; a manifest path for the colour program, with the colour reading in
   its observer column, is a separate later unit and needs the raw theorem
   below the manifest, as the twelfth path did (S7, S22). Until then the
   colour program's comment says its path is not one of the manifest's.
6. **Monotonicity in the reading (S2, S3, S5, S23).** Land
   `input_distinguishability_prop_finer`,
   `reading_factors_coalition_endpoint_reading` and the corollary at the
   endpoint reading. The spec's sentence "says nothing across two readings"
   and its invariant 5 are rewritten: the number bound AS STATED pairs an
   obstruction and a certificate at one reading; with a factorisation the
   bound carries over, and an obstruction at any reading is an obstruction at
   the endpoint reading, the finest. The index ledger's "holds by typing" is
   wrong and is not repeated anywhere.
7. **Narrowed statements name their reading (S4, S5, S13).** The five
   statements of `psl211_reading_constancy.v` and
   `pgl27_word_input_distinguishability_false` that gain
   `coalition_endpoint_reading` get comments that name it and say what stays
   open (a certificate at a coarser reading is not covered). Invariant 6 is
   split: the propositions are convertible at the default reading; statements
   binding a witness or a certificate change their types, and five narrow.
8. **The PSL(2,11) pair (S16).** The two programs state two different
   properties: exact independence of the chirality at the colour reading, and
   input distinguishability between two run arguments at the endpoint reading.
   Over the dealer-dealt parameters the run argument is the chirality, which
   is why the second is a privacy statement at this model; the comment says so
   and says it does not generalise.

## Surface rulings

| finding | ruling |
|---|---|
| N20 | ACCEPT (main session): `at R idx by b` in the five-clause rule |
| N21, N23, N26 | MOOT by OWNER's decision: the obstruction is published inline, `publish Obstruction InputDistinguishability of r at c by pf assuming a`; no `obstruction` keyword |
| N22 | ACCEPT, OWNER: `conclude at c by p` |
| N24 | ACCEPT: one header sentence, the `leaks` annotation attaches to the evidence |
| N25 | ACCEPT: the header names two categories, prepositions and slot names |
| N27 to N32, N34, N35 | ACCEPT: probe A round 2 rewrites the draft paragraph |
| S10 | ACCEPT: the combined surface is compiled at the landing; `certify ExactIndependence of r by w leaks at k by H` and an `of r` form of the five-clause rule are STRUCK from spec 3.5 (no caller); the five-clause rule is at the default reading and its header says so |

## Names

| finding | ruling |
|---|---|
| N7 | ACCEPT: `psl211_dealt_sampled` |
| N8, N9 | ACCEPT: `psl211_colour_exact_witness`, `psl211_colour_exact_published`, `psl211_colour_exact_published_readingE` |
| N13, N14, N42 | probe files only; they are records and do not land. The landing copies no plan id and no abbreviation |
| N16, N17, N33, N36, N37 | no change |
| N39 | ACCEPT at the fold: the spec shows the record as built, indexed by the algebra alone (S19 agrees nothing is lost) |
| N40, N41 | ACCEPT: every statement comment of an object that gained a reading is restated as what the object is, after the names are fixed, with no history words |
| N43, S14 | ACCEPT: the header of `psl211_colour_reading.v` is corrected; `psl211_endpoints.v` already says the dealer-dealt mode reads its endpoints through `profile_endpointsE` |

## Evidence still owed at the landing

S9 (non-degenerate instances in the fidelity file: the all-decks obstruction
at 1/660 against the number bound), S12 (the missing back map, or a sentence),
S20 (`Print Assumptions` on the three tails, the monotonicity lemma, one
instance witness), the obstruction program's `_pathE` and `Print Assumptions`
measured one at a time (probe B round 2 could not attribute a hang), and the
PSL(2,11) rule: never let the reading wrapper be removed by the conversion
that closes a two-chirality goal; discharge it first in a `have` naming one
chirality.

## What lands, by the owner's rule (claimed by the paper or needed later)

Lands: the record and its default; the index on the three records;
`evidence_reading`, `ab_reading`, `reading_of` and the three `_readingE`
framework lemmas; the three tails at a free reading; the three twin
statements; `ReadingIndistinguishabilityPropAt`;
`reading_indistinguishability_postprocessing` (already in production,
restated); the three monotonicity lemmas; the migration of the relations file
with the constant-reading record; the dealer-dealt endpoints statement and
observed execution in `psl211_models.v`; a new
`instances/psl211/tableau/psl211_tableau_dealt.v` with the family, the Sampled
value, the colour program and the endpoint-reading obstruction at 1/660.

Does not land: `exact_witness_postprocessing`, ideal-proximity
post-processing, a second PGL(2,7) program at the content trace (the same
term as the first), marginal bounds as readings, a manifest path for the
colour program (later unit).
