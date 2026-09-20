# Prose sheet: two barred nouns leave the comments, each site saying what the thing is

Owner, 2026-09-20: the three-letter noun that named a constructor of the
framework's sum type is barred ("the first barred word" below; this sheet does
not write it), and so is "port" for that sum type. There is NO single synonym:
"It is case by case. So you need to say in each case, what they are."
Identifiers are already renamed (`SecurityProperty`, `SecurityEvidence`, ...).

## What the things are (`manifest/pgg_tableau.v`)

- `SecurityEvidence sa` (was `SecurityPort`): what a program certifies with. A
  sum of three kinds of evidence: an `ExactWitness`, an
  `IndistinguishabilityCert`, an `IdealProximityCert`.
- `SecurityProperty`: which of three SECURITY PROPERTIES the evidence proves:
  exact independence, input indistinguishability, ideal proximity. The value
  forgets the witness or certificate.
- `EvidenceProp c e`: the proposition the evidence proves, one per property:
  the exact-independence proposition (four conjuncts), the
  input-indistinguishability proposition `IndistinguishabilityPropAt`, the
  ideal-proximity proposition `IdealProximityPropAt`.
- `certify P w`: the statement of a program that supplies the evidence.
- `exact_tail`, `indistinguishability_tail`, `idealproximity_tail`: the lemmas
  that turn a witness or certificate into its proposition.

## The cases for the first barred word

| # | What it meant at the site | How to tell | Write |
|---|---|---|---|
| 1 | the security property itself | "which X a program commits to", "carry different X", "the same X", "X is named", "a different X", "settles which X that is", "X alone decides" | "security property" / "property"; "which of the three security properties a program certifies", "certify different properties" |
| 2 | the property, used as an adjective carrier: "the exact X", "the proximity X", "the input-indistinguishability X" followed by a verb | "the exact X takes a witness", "the proximity X compares a joint law ..." | name the property: "exact independence takes a witness" is wrong (a property takes nothing): write what acts: "the exact-independence evidence is a witness", "certifying exact independence takes a witness", "the ideal-proximity proposition compares ..." . Decide by the verb: evidence HOLDS fields; a proposition STATES, COMPARES, QUANTIFIES, MENTIONS; a certify statement TAKES a payload; a tail lemma DERIVES |
| 3 | possessive on the evidence: "the exact X's witness", "the proximity X's certificate", "the X's own number" | the noun after it is a witness, certificate, field, number, ideal, secret | drop the noun: "the exact-independence witness", "the proximity certificate", "the certificate's own number" |
| 4 | possessive on the proposition: "the X's proposition", "the exact X's four conjuncts", "the X's security statement" | | "the exact-independence proposition", "its four conjuncts", "the ideal-proximity proposition" |
| 5 | the certify line of a program: "before an X is named", "enters the X", "at the proximity X" (of a program), "through the exact X" | the sentence is about the order of a program's lines or about how a program was published | "before the certify statement", "certified for ideal proximity", "published through exact independence" -> "published with exact-independence evidence" |
| 6 | the tail lemma or the composition it performs: "the X's composition", "the X loses the bound at each of two hops" | the sentence is about a derivation, hops, losses | name the lemma or the derivation: "the input-indistinguishability tail loses that bound at each of two hops" |
| 7 | the function's value: "the row carries the exact X" in an index entry of a `_propertyE` lemma | the entry describes an equation `security_property_of p R idx = ...Property` | "the program's security property is exact independence" |

The three properties are written: "exact independence", "input
indistinguishability", "ideal proximity" (adjectival: "exact-independence",
"input-indistinguishability", "ideal-proximity"; where the tree already says
"the proximity certificate", "the proximity proposition", that short form
stays). "indistinguishability" is never abbreviated.

## The cases for "port"

| # | What it meant | Write |
|---|---|---|
| 1 | a value of `SecurityEvidence` ("the port", "a security port", "the port's proposition", "every port of a family") | "the evidence", "security evidence", "the proposition the evidence proves", "the evidence at every index of a family"; "evidence" is a mass noun: no plural, "a piece of evidence" only if a count is needed |
| 2 | the accumulated security half of a program at AnalysisBridged ("the port's perfect and statistical halves") | "the evidence's ..." or name the certificate's components, by the sentence |
| 3 | a model's port/other sense (check `psl211_reading_constancy.v`) | say what it is there |

## Rules

1. Every site is decided by reading the declaration or header paragraph it sits
   in. Sentences may be rewritten as far as the case requires and no further:
   every claim, hypothesis, number, quantifier and named lemma of the old
   sentence survives; nothing else is improved.
2. Type honesty: evidence holds fields and proves a proposition; a property is
   a name and does nothing; a proposition states; a program certifies and
   publishes; a path records. A sentence that cannot be made true under these
   is listed for the main session, with the declaration, and gets the least
   wrong wording meanwhile.
3. One word per concept per file, and twins in sibling files
   (`*_tableau_analysis_bridged.v`, `*_tableau_checks.v`, `*_proximity.v`) say
   one thing in one way unless the instances differ in the fact.
4. Layout: at most 80 BYTES; boxed lines exactly 80 with a space before the
   closing delimiter; `==` columns and continuation columns kept; docstrings
   4-space continuation; banners one content line; no orphan short line.
5. Never in new text: the owner's barred vocabulary (both nouns of this sheet
   included), tokens made of a capital L and a digit, abbreviations of
   "indistinguishability", history words, metaphor or narrative words, proof
   strategy in docstrings.
