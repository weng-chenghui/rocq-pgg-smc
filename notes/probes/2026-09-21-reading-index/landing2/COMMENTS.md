# Landing commit 2: every comment paragraph written or rewritten

Each entry gives the file, the declaration the comment sits on, and the text
as it is in the file. Comments carried over from the probe's staged copies
unchanged are marked so.

## manifest/pgg_tableau.v

### File header, the paragraph about the fourth terminal (rewritten)

```
(* A fourth terminal hands over an obstruction in place of a security         *)
(* property. Its record holds a program's data at Sampled, a manifest path at *)
(* AnalysisBridged and NegativeTransfer, and one member of a closed           *)
(* enumeration of facts about the model together with the proof of it. The    *)
(* single member is input distinguishability at a reading and a number, and   *)
(* the proposition it stands for is that the number is above zero and that    *)
(* some coalition below the privacy threshold reads two run arguments of the  *)
(* model's own cut law at least that far apart, in the sum of absolute        *)
(* differences. No security property follows from such a value, and two       *)
(* lemmas read consequences off it, both at the obstruction's own reading.    *)
(* Every number at which an input-indistinguishability program over that      *)
(* model and that reading states its proposition is at least the number, and  *)
(* no certificate at that reading has its ideal cut within eps of the model's *)
(* own cut law once eps added to itself stays below the number. The second    *)
(* goes through indistinguishability_prop_of_ideal_close, the composition law *)
(* for input indistinguishability with the number left free.                  *)
```

### File header, the new paragraph on the reading

```
(* The manifest describes a capability by four coordinates: theorem,          *)
(* distribution, observer, notion. A program supplies three of them, the      *)
(* model family being the distribution, the security evidence the theorem and *)
(* the security property the notion. The fourth is a reading of a coalition's *)
(* endpoints: a finite type per coalition and a function of that coalition's  *)
(* seat-indexed card positions into it. Each evidence constructor carries     *)
(* one, each of the three records is indexed by one, and every proposition of *)
(* this file is stated at the one its evidence carries. The attack model is   *)
(* untouched, a static coalition of fewer than profile_k seats; a reading     *)
(* says what that coalition is granted to see and never who it is. The        *)
(* identity reading, coalition_endpoint_reading, is the finest, and a         *)
(* program whose certify statement names none is a program at it. Each        *)
(* property has two statements, one whose payload names no reading and one    *)
(* whose payload is a reading paired with the evidence at it.                 *)
```

### `CoalitionReading` (from the probe's staged copy, unchanged)

```
(* A reading of a coalition's endpoints: a finite type for each coalition and
   a function of that coalition's seat-indexed card positions into it. It is
   the observer coordinate of a security claim. The attack model is untouched,
   a static coalition of fewer than profile_k seats; what a reading fixes is
   what that coalition is granted to see. Because a reading is a function of
   the endpoints alone, the link lemma of the Sampled level carries it to the
   executed run with no further premise, so every claim stated at one stays a
   claim about an execution. A reading that is not such a function, a
   transcript holding messages among them, is outside this record. *)
```

### `coalition_endpoint_reading` (rewritten)

```
(* The identity at every coalition. A program that names no reading is a
   program at this one. Every reading is a function of it, so it is the
   finest of them, and a claim made at it is the strongest claim about a
   coalition of that size the language can state. *)
```

### `ExactWitness` (rewritten)

```
(* The exact-independence witness at a reading: a secret random variable on
   the sampled space, and, at every coalition below the privacy threshold,
   the independence from it of what the reading grants that coalition of its
   endpoints. Independence is the statement rather than a numeric leakage
   bound, and the entropy forms and the closure under post-processing are
   derived from it below, so an instance producing this record has nothing
   further to supply about mutual information. The reading indexes the type,
   so a witness proved at one reading is not evidence at another, and the
   implication between two readings runs from the finer to the coarser
   alone. *)
```

### `IndistinguishabilityCert` (rewritten)

```
(* The input-indistinguishability certificate at a reading: a marginal bound
   on the instance's shuffle, the identification of the bound's law with the
   adapter's cut, an ideal cut law within that bound in variation distance,
   and the constancy, at every coalition below the privacy threshold, of what
   the reading grants that coalition of the ideal cut, in the run argument.
   Five fields and not the two of a marginal bound alone: the transfer
   inequality is stated on the cut carrier, where it needs both a distance
   and the ideal constancy, and a per-position marginal bound holds neither.
   The reading enters the constancy field alone, the other four being about
   the cut law by itself, so a coarser reading asks an instance for less at
   the one field that mentions a coalition. *)
```

### `IdealProximityCert` (rewritten)

```
(* The proximity certificate at a reading: a second sample adapter over the
   program's
   own execution, standing for the ideal run; an exact witness for that ideal
   at the same reading, which is what makes the ideal a model whose own
   privacy is proved and not a bare law; the actual model's secret, typed at
   the carrier the ideal's witness names, so that the two models speak of one
   secret; a number; and, at every coalition below the privacy threshold,
   that number as a bound on the variation distance between the two models'
   joint laws of what the reading grants the coalition and the secret. One
   reading serves both models, so the number measures the distance between
   two models and not between two readings. The comparison is an average over
   the run argument of each model and not a statement at a fixed run
   argument, and the number is an upper bound the instance chooses on what
   the actual model loses against an execution that leaks nothing, not a
   quantity the record determines: any number at which ipc_close is provable
   is a legal field, so a certificate says as much as its number is small and
   no more. *)
```

(Defect to fix in a comments pass: the second line is short, the paragraph
was not reflowed after the first sentence was rewritten.)

### `SecurityEvidence` (sentence added)

```
   ... the three are different statements
   about a coalition, so a program certifying input indistinguishability
   asserts nothing about mutual information. Each constructor carries the
   reading its witness or certificate is indexed by, so the two coordinates
   the manifest's path does not hold, the security property and the
   observer, both sit on this one line of a program. *)
```

### `evidence_reading` (rewritten)

```
(* The reading the evidence is stated at, with its witness or its certificate
   forgotten. It is the observer coordinate of the manifest's description of
   a capability, read off the certify line of a program's text as its
   security property is, and it says what a coalition is granted to see and
   never who that coalition is. *)
```

### `ab_reading` (from the probe's staged copy, unchanged)

```
(* The reading the data at this level carries, at one real field and one
   index, read off the evidence's constructor. It stands beside
   ab_security_property: the property names which of the three statements a
   program proved and this names the observer it proved it about, and the two
   together are the coordinates of the claim the manifest records. *)
```

### `ExactProp` (rewritten; the probe's copy had two paragraphs, merged here)

```
(* The exact-independence proposition of a witness: below the threshold, what
   the witness's own reading grants the coalition of its executed view is
   independent of the secret, its mutual information with the secret is zero,
   conditioning on it leaves the secret's entropy unchanged, and every
   deterministic function of it is still independent. Independence leads and
   the entropy forms follow it, so the information-theoretic reading of exact
   independence is proved from the same fact rather than assumed beside it.
   The reading is a parameter of the witness and not of the proposition, so a
   program's text cannot name a reading its evidence is not about, and the
   post-processing conjunct quantifies over functions of the reading's own
   value type and not of the endpoints. *)
```

### `ReadingIndistinguishabilityPropAt` (rewritten)

```
(* The input-indistinguishability proposition at a reading: below the
   threshold, two run arguments give, of the model's own cut law, readings
   within variation distance c. It is stated at a reading and at no
   certificate, because the certificate's ideal cut and constancy field are
   used inside indistinguishability_tail and have left the claim; that is
   what lets a bound proved at one reading travel to another along a
   factorisation, with no certificate at the far end. The bound is a
   parameter rather than the certificate's own sum, so conclude can state a
   finished program at any number at or above that sum, the constant a paper
   cites among them, without reproving the proposition. The number bounds a
   sum of absolute differences, twice the total variation distance of the
   literature, so a distinguisher's advantage is at most half of it. *)
```

### `IndistinguishabilityPropAt` (rewritten)

```
(* The input-indistinguishability proposition of a certificate: the
   proposition above, at the reading the certificate is indexed by. It is
   what a certify statement for this property proves, and the certificate
   fixes the reading the claim is about while contributing nothing else to
   the claim's text. *)
```

### `IdealProximityPropAt` (rewritten; the probe's copy had two paragraphs)

```
(* The ideal-proximity proposition of a certificate, at the reading the
   certificate is indexed by: below the threshold, the joint law of what that
   reading grants the coalition of the executed run, with the secret, under
   the actual model, is within variation distance c of the product of the two
   marginals the ideal model has, its own reading and its own secret. The
   right side is a product because the ideal's witness makes those two
   independent there, so c bounds the sum of the absolute differences between
   what a coalition below the threshold sees jointly with the secret and two
   quantities drawn apart, and a distinguisher's advantage is at most half of
   c, the sum of the absolute differences being twice the total variation
   distance of the literature. The attack model is a static coalition of
   fewer than k seats, and the reading is what that coalition is granted to
   see of its own endpoints; the claim is an average over the run argument
   and not a statement at a fixed run argument. The bound is a parameter, as
   it is for the input-indistinguishability proposition, so conclude can
   state a finished program at any number at or above the certificate's
   ipc_eps, the one a paper cites among them. *)
```

### `ExactPayload` (sentence added)

```
(* The payload of certify_exact: one exact witness per real field and index of
   the accumulated family, at the coalition's own endpoints. Uniformity in
   the field is what makes the exact-independence conclusion unconditional
   rather than a statement at one chosen field. The reading is written into
   the type and not supplied by the payload, so a program built by this
   statement makes the strongest of the claims the language can state about
   a coalition of that size. *)
```

### `ExactPayloadOfReading` (rewritten)

```
(* The payload of the statement that names a reading: the reading, paired
   with one witness per real field and index at it. It is a second type
   beside the one above, and the statement it feeds is a second statement,
   so that a program naming no reading carries a payload in which no reading
   occurs; the equations between two spellings of one such program are then
   decided by a conversion that does not descend into the program's own
   stack coordinate. *)
```

### `exact_of_reading` (rewritten)

```
(* The pair a statement at a named reading takes. The reading is written
   once and the witness is checked against it where it is written, so a
   program cannot name one reading and certify at another. *)
```

### `IndistinguishabilityPayload` (sentence added)

```
   ... payload is, so the bound the program publishes is a bound at every field
   rather than at one chosen field. The reading is the coalition's own
   endpoints, so the bound is one at the finest reading and travels to every
   coarser one. *)
```

### `IndistinguishabilityPayloadOfReading` (rewritten)

```
(* The reading, paired with one certificate per real field and index at it.
   It stands to the type above as the exact pair stands to the exact
   payload, and for the same reason. *)
```

### `indistinguishability_of_reading` (new)

```
(* The pair the input-indistinguishability statement at a named reading
   takes, the certificate checked against the reading where it is
   written. *)
```

### `IdealProximityPayload` (sentence added)

```
   ... with and the number it loses against that ideal are fixed at every field.
   The reading is the coalition's own endpoints, and whether a proximity
   number travels to a coarser reading is not proved anywhere. *)
```

### `IdealProximityPayloadOfReading` (rewritten)

```
(* The reading, paired with one proximity certificate per real field and
   index at it, on the pattern of the other two. *)
```

### `idealproximity_of_reading` (new)

```
(* The pair the proximity statement at a named reading takes, the
   certificate checked against the reading where it is written. *)
```

### `exact_tail` (sentence added)

```
(* The independence a witness states at the direct computation, transported
   to the view along the link lemma, with its entropy forms and
   its closure under deterministic post-processing. The composition law for
   exact independence, and what makes an ExactWitness the whole of what an
   instance supplies on it. The reading is free: it is applied to both sides
   of the link lemma alike, so a witness at any reading reaches the
   proposition at that reading with the premise the Sampled level already
   proved and nothing more. *)
```

### `indistinguishability_tail` (sentence added)

```
(* The certificate's cut-carrier distance and its ideal constancy, fed to the
   transfer inequality, give the two-argument variation bound at cert_eps, the
   certificate's marginal-bound epsilon twice. The composition law for input
   indistinguishability, and the only place the mixing bound is used. The
   reading is free, and it enters only through the constancy field, so the
   distance the mixing bound supplies is the same whatever a coalition is
   granted to see. *)
```

### `certify_reading_exact` (rewritten)

```
(* Adjoins the exact-independence witness at a reading the program writes on
   its own line. The two statements differ in their payload alone: the data
   they build and the proposition they prove have one shape, and
   evidence_reading reads the reading back off either. A program takes this
   one when what it certifies is independence of less than the coalition's
   whole endpoints, which for exact independence is the weaker of the two
   claims and not a bound at a larger number. *)
```

### `certify_reading_indistinguishability` (rewritten)

```
(* Adjoins the input-indistinguishability certificate at a reading the
   program writes on its own line. A bound proved at one reading holds at
   every coarser one by reading_indistinguishability_postprocessing, so this
   statement records the reading the instance's certificate is built at and
   not the only reading its number holds at. *)
```

### `certify_reading_idealproximity` (rewritten)

```
(* Adjoins the proximity certificate at a reading the program writes on its
   own line. Both models are compared through that one reading, and no
   lemma carries a proximity number from one reading to another. *)
```

### `reading_of` (from the probe's staged copy, unchanged)

```
(* The reading a published program's claim is made at, at one real field and
   one index of its family. It is the fourth coordinate of the manifest's
   description of a capability, the observer, which the path itself does not
   carry: two programs over one model and one pair of statuses are one
   manifest path, and the security property and the reading are where they
   differ. *)
```

### `InputDistinguishabilityPropAt` (rewritten)

```
(* Input distinguishability at a reading and at c: some coalition below the
   privacy threshold reads two run arguments of the model's own cut law at
   least c apart, in the sum of absolute differences. It is the quantitative
   negation of the input-indistinguishability proposition at that reading,
   and no certificate occurs in it, so it is a fact about the model and the
   reading and holds or fails whether or not a certificate over the model
   exists. The attack model is a static coalition of fewer than k seats, and
   the reading is what that coalition is granted to see; the two run
   arguments are named rather than drawn, so a distinguisher told which two
   arguments to compare has advantage at least half of c there, var_dist
   summing the absolute differences and so being twice the total variation
   distance of the literature. The property is monotone in the reading, from
   the coarser to the finer, so distinguishability at any reading is
   distinguishability at the coalition's own endpoints;
   input_distinguishability_prop_finer is where that is proved. *)
```

### `input_distinguishability_prop_le` (rewritten)

```
(* A model distinguishable at c at a reading is distinguishable at every
   smaller number at that reading, the same coalition and the same two run
   arguments witnessing it. The family is downward closed in c, so the
   sharpest statement one coalition and one pair of run arguments support is
   the one at the distance between what the reading grants of them. *)
```

### `indistinguishability_number_ge_of_input_distinguishability` (rewritten)

```
(* Every number at which an input-indistinguishability program over a
   distinguishable model states its proposition is at least the number the
   model is distinguishable at. That proposition bounds the distance between
   what the reading grants of every two run arguments, and distinguishability
   exhibits two whose distance reaches c, so c bounds from below what such a
   program can publish, whatever its certificate. One reading stands on both
   sides: this is a bound between an obstruction and a certificate about the
   same thing seen, and the bound between an obstruction and a certificate at
   two readings related by a factorisation is
   indistinguishability_number_ge_across_readings. *)
```

### `no_indistinguishability_cert_ideal_close_of_input_distinguishability`

```
(* Over a model distinguishable at c at a reading, no input-indistinguishability
   certificate AT THAT READING has its ideal cut within eps of the model's own
   cut law once eps added to itself stays below c. The law is the model's and
   not a free argument: a certificate's second and fourth fields place its
   ideal within its marginal bound of the cut law the model draws and of no
   other law. The route is indistinguishability_prop_of_ideal_close, which
   turns closeness of the ideal into the proposition at eps twice, against
   which the number bound above is then read. A certificate at a reading the
   obstruction's own does not factor through is left open by this, and that
   is a scope of the statement and not a fact about the model. *)
```

### `ObstructionKind` (sentences rewritten)

```
   ... enumeration and not a free proposition: a free proposition is what restate
   hands over, and a reader of a free payload cannot tell what kind of fact
   was published. The one member carries the reading the model is
   distinguishable at and the number it is distinguishable at, the reading
   standing to an obstruction as it stands to security evidence, so the two
   readers of a published program answer the same question of a negative
   result and of a positive one. The proposition that member stands for
   requires the number positive. At a number at or below zero the inequality
   is free, ...
```

### `certify_exact_readingE` (rewritten)

```
(* A program whose exact statement names no reading carries the coalition's
   own endpoint reading, at every real field and every index of its family.
   With the two siblings below and publish_propertyE it settles the observer
   coordinate of a finished program from one line of the program's text, as
   certify_exact_propertyE settles the security property, so the two
   coordinates the manifest path does not hold are both read off the same
   line. *)
```

`certify_indistinguishability_readingE` keeps the probe's one-liner "The same
for the input-indistinguishability statement.";
`certify_idealproximity_readingE` keeps "The same for the proximity
statement."

## manifest/pgg_tableau_syntax.v

### File header, the `by` paragraph (rewritten) and the new `of` paragraph

```
(* also follows the literal naming the security property in four of the       *)
(* eight certify rules, and the evidence of such a statement is the term      *)
(* after it; in the five-clause rule the token after the property's name is   *)
(* at and the marginal bound follows by, and in the three rules that name a   *)
(* reading it follows that reading.                                           *)
(*                                                                            *)
(* of introduces what is read. It follows the literal naming the security     *)
(* property in the three certify rules that name a reading, and the literal   *)
(* InputDistinguishability in one of the two obstruction terminals; the term  *)
(* after it is the reading. It is also the word of the bind of pgg_tableau.v, *)
(* following that rule's slot f, and it reserves nothing, being a keyword of  *)
(* Rocq independently of this file, measured on 2026-09-21 in the same way,   *)
(* so the count stays twenty.                                                 *)
```

### File header, the two-kinds paragraph (one clause changed)

```
(* The surface has two kinds of word. A preposition carries one meaning       *)
(* throughout: at a number, a size or a real field with its index, by a proof *)
(* or a piece of evidence, assuming an assumption status, and of what is      *)
(* read. A slot name names a thing, and the term that is that thing           *)
```

### File header, the binders sentence

```
(* twenty: the two realisation lemmas bind L and n, dealt_params_stepE binds  *)
(* x, q and n, and input_distinguishability_obstruction binds q, r and c.     *)
```

### `mk_indistinguishability` (sentence added)

```
   ... the fourth component is an inequality at the first
   component's epsilon, and the fifth is an equation. The certificate it
   builds is at the coalition's own endpoints, the finest reading, and a
   certificate at any other reading is written through the record. *)
```

### The three `of r` certify rules (new)

```
(* The reading follows the security property's name, and the evidence
   follows by. The clause is a type ascription on that evidence: the
   payload's type is the witness or the certificate at r, so evidence at
   another reading is rejected where it is written and a program's text
   cannot name a reading its evidence is not about. A statement omitting
   the clause is a statement at the coalition's own endpoints and expands
   to the rule above it, whose payload mentions no reading at all. *)
```

### The five-clause rule (sentences added)

```
   ... the two names after at are the binders
   the rule quantifies over and not values. The statement is at the
   coalition's own endpoints and has no form naming a reading, because
   nothing in the tree builds a certificate at another reading out of five
   components. *)
```

### `input_distinguishability_obstruction` (rewritten)

```
(* The one obstruction kind at every real field and every index of a
   program's model family, at one reading and at a number that is a term in
   the field and in nothing else. The framework's payload admits a reading
   and a number that differ at each index; this builder does not, which is
   what lets the terminals below write both in the program's own line
   instead of taking a payload named beside it. An obstruction whose reading
   or number differs at two indices of one family is written through the
   bind and the constructor. *)
```

### The obstruction terminal without `of r` (sentence added)

```
   ... The reading is the coalition's own endpoints, the
   finest, so a program written this way publishes the obstruction that
   refutes the most. *)
```

### The obstruction terminal with `of r` (new)

```
(* The same terminal with the reading written after of, between the kind's
   name and the number. A program uses it when the coalition it exhibits
   tells two run arguments apart through less than the whole of its
   endpoints; by input_distinguishability_prop_coalition_endpoint_reading
   such an obstruction is an obstruction at the endpoint reading too, so the
   clause records what the instance proved and not the limit of what the
   published value refutes. *)
```

## manifest/pgg_tableau_reading.v

The whole file header and every statement comment come from the probe's
staged one-record copy and are landed unchanged. The header:

```
(* pgg_tableau_reading: what one reading of a coalition's endpoints says      *)
(*                      about another                                         *)
(*                                                                            *)
(* A reading of a coalition's endpoints is CoalitionReading of                *)
(* manifest/pgg_tableau.v, and the propositions of the framework are stated   *)
(* at the reading their evidence carries. This file holds what relates two    *)
(* readings of one model.                                                     *)
(*                                                                            *)
(* One reading factors through another when a coalitionwise map sends what    *)
(* the finer grants to what the coarser grants. Along such a map the two      *)
(* distance properties travel in opposite directions, and saying which is     *)
(* the whole content of the file. An input-indistinguishability bound travels *)
(* from the finer reading to the coarser one, which is the data processing    *)
(* inequality: granting a coalition less cannot separate two run arguments    *)
(* further. Input DISTINGUISHABILITY travels the other way, from the coarser  *)
(* to the finer: a coalition granted more still tells the two arguments       *)
(* apart. The coalition's own endpoints are the finest reading of all, every  *)
(* reading factoring through them, so every obstruction is an obstruction     *)
(* there.                                                                     *)
(*                                                                            *)
(* Exact independence at a reading is an independence and not a numeric       *)
(* bound, and an exact-independence witness is that proposition at its own    *)
(* reading with no proof.                                                     *)
(*                                                                            *)
(* Every number below bounds a sum of absolute differences, twice the total   *)
(* variation distance of the literature, so a distinguisher's advantage is at *)
(* most half of it. Naming a reading leaves the attack model as it is, a      *)
(* static coalition of fewer than profile_k seats, and changes what that      *)
(* coalition is granted to see. A reading is not security evidence: what      *)
(* certifies a security property is a program.                                *)
```

## manifest/pgg_tableau_security_property_relations.v

### `coalition_reading_cst_unit` (new)

```
(** The reading whose value type is unit at every coalition: a coalition is
    granted one value and reads it whatever the deal. It is the coarsest
    reading of all, every reading factoring through it. *)
```

### `exact_witness_cst_reading` (new)

```
(** The exact witness at that reading, over an arbitrary model and at an
    arbitrary secret. Its independence field is inde_RV_cst read on the
    reading rather than on the secret, so it uses no property of the model
    and no property of the secret either. Holding exact-independence
    evidence is therefore by itself no statement about what a model hides:
    what a program says depends on the reading it certifies at as much as on
    the property it certifies, and this is the reading at which it says
    nothing. *)
```

## instances/psl211/psl211_reading_constancy.v (five narrowed statements)

### `indistinguishability_cert_reading_constancy` (sentence added)

```
    ... so refuting the proposition at a law refutes every certificate
    whose ideal cut is that law. The certificate is at the coalition's own
    endpoint reading, the finest; a certificate at a coarser reading asks
    constancy of that coarser reading alone and is not covered. *)
```

### `psl211_alldecks_cert_ideal_close` (sentence added)

```
    ... epsilon against that law however its marginal bound record was built. The
    certificate is at the coalition's own endpoint reading; the statement
    leaves a certificate at a coarser reading open. *)
```

### `psl211_alldecks_no_small_eps_cert` (sentence added)

```
    ... It says
    neither that input indistinguishability is unavailable here nor anything
    about what a coalition of at most five seats reads. The certificate is at
    the coalition's own endpoint reading, the finest; what a certificate at a
    coarser reading may hold as its epsilon stays open, and the colour
    reading of instances/psl211/psl211_colour_reading.v is such a reading. *)
```

### `psl211_alldecks_no_zero_eps_cert` (sentence added)

```
    ... so the sharper the shuffle bound the
    less room the certificate has. It is at the coalition's own endpoint
    reading, as the theorem it specialises is, and says nothing of a
    certificate at a coarser one. *)
```

### `psl211_alldecks_input_distinguishability` (sentence added)

```
    ... the two facts stand under
    different quantifiers over the run argument, one drawing it and one fixing
    two of its values. The reading is the coalition's own endpoints, the
    finest, so this is the strongest of the distinguishability statements
    about the model and every coarser reading's obstruction implies it. *)
```

### `psl211_alldecks_indistinguishability_number_ge` (sentences added)

```
    ... A certificate
    whose ideal cut sits further than half of 1/660 from the group-uniform law
    is untouched by both, and a program over it still publishes at least
    1/660. Both the obstruction and the certificate are at the coalition's
    own endpoint reading: this is the framework's number bound at one
    reading, and a program whose certificate is at a coarser reading is
    bounded only through a factorisation, by
    indistinguishability_number_ge_across_readings. *)
```

## instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v

### `pgl27_word_input_distinguishability_false` (paragraph added)

```
    The reading named is the coalition's own endpoints, the finest, and the
    statement covers every reading because of that: by
    input_distinguishability_prop_coalition_endpoint_reading an obstruction
    at any reading of this model is an obstruction at the endpoint reading
    at the same number, so refuting the proposition here refutes it
    everywhere. Nothing is left open at a coarser reading. *)
```

## instances/psl211/psl211_models.v

### `psl211_dealt_endpoints` (new)

```
(** psl211_dealt_endpoints — the interpreter's messages of the dealer-dealt
    run compute the direct computation of the laid deck. It is the twin of
    psl211_alldecks_endpoints over the other mode a run of this instance is
    driven in: the profile's abstract-readout equation quantifies over the
    content readout, so one equation serves both modes and neither costs a
    reduction of its own. *)
```

### `psl211_dealt_observed` (new)

```
(** psl211_dealt_observed — the observed execution of the dealer-dealt run:
    the run finishes inside its fuel, the verifier collects one endpoint per
    seat, and decoding them returns the chirality the dealer dealt. It is the
    twin of psl211_alldecks_observed, and it is the value the programs over
    the fixed-dealer colour model are written at. *)
```

## instances/psl211/psl211_colour_reading.v

### File header, the corrected paragraph

```
(* The dealer-dealt parameters read their endpoints through                   *)
(* profile_endpointsE, as instances/psl211/psl211_endpoints.v states, so      *)
(* psl211_models.v carries an endpoints statement and an observed execution   *)
(* for them and instances/psl211/tableau/psl211_tableau_dealt.v carries the   *)
(* Sampled level and the two programs over them. Every statement in this      *)
(* file is about the model's law and a reading of a coalition's endpoints,    *)
(* and the identification of that reading with the executed one is the link   *)
(* lemma the Sampled level of that file proves.                               *)
```

### `psl211_dealt_sample` (last sentences corrected)

```
    ... chirality is what the colour view reads. Every statement made over this
    adapter is about the model's law and a reading of a coalition's
    endpoints; the Sampled level built over these parameters in
    instances/psl211/tableau/psl211_tableau_dealt.v is what identifies that
    reading with the executed one. *)
```

### `psl211_colour_readingE` (rewritten, the lemma moved below the
reconciliation)

```
(** psl211_colour_readingE — the model's colour view of a sample point is what
    the colour reading grants the coalition of that point's endpoints. It is
    where the instance's seat reconciliation is spent: the colour view is
    written at the position index the model uses and a coalition's endpoints
    index through pi_starts, and psl211_colour_of_reading_obsE is what
    identifies the two. *)
```

### `psl211_colour_reading_indep` (last sentences corrected)

```
    ... entropy form of the framework is restated at it. It is stated of the
    model's law and the colour reading of a coalition's endpoints; the
    program of instances/psl211/tableau/psl211_tableau_dealt.v carries it to
    the executed run along the link lemma of the Sampled level. *)
```

### `psl211_dealt_reading_indep_false` (last sentences corrected)

```
    ... here. It is stated of the model's law and the coalition's own endpoint
    reading, and it is why exact independence at the colour reading does not
    carry back to the endpoint reading. *)
```

### Section banner retitled

```
(******************************************************************************)
(*     What travels from the endpoint reading to the colour reading           *)
(******************************************************************************)
```

`psl211_colour_of_reading`, `psl211_colour_reading`,
`psl211_colour_of_reading_obsE`, `psl211_colour_reading_funE`,
`psl211_colour_indistinguishability_of_coalition_reading` and
`psl211_colour_of_reading_collides` keep the probe's staged one-record
comments.

## instances/psl211/tableau/psl211_tableau_dealt.v (new file)

### File header

```
(* psl211_tableau_dealt: two readings of the fixed-dealer colour model of the *)
(*                       twelve-card chirality instance, as two programs      *)
(*                                                                            *)
(* The dealer-dealt run of the twelve-card chirality instance lays the cards  *)
(* itself from the chirality, so the run argument of these parameters IS the  *)
(* chirality the coalition is not to learn. Over the one model built on that  *)
(* run this file writes two programs, and they state two different            *)
(* properties at two different readings.                                      *)
(*                                                                            *)
(* The first certifies exact independence at the colour reading: below the    *)
(* threshold of six of the twelve positions, the colours a coalition sees at  *)
(* its own positions are independent of the dealt chirality, at every prior   *)
(* on that chirality. The second publishes an obstruction at the coalition's  *)
(* own endpoint reading: three named positions read the two chiralities of    *)
(* one deal 1/660 apart in the sum of absolute differences, 1/660 being the   *)
(* reciprocal of the order of the shuffle group, so a distinguisher told to   *)
(* compare those two run arguments has advantage at least 1/1320 there. Both  *)
(* are unconditional and neither rests on an assumption about an adversary.   *)
(*                                                                            *)
(* Because the run argument is the chirality here, the second program is a    *)
(* privacy statement at this model and not only a statement about two inputs: *)
(* the two run arguments it compares are the two values of the secret. That   *)
(* reading of it is particular to the dealer-dealt mode and does not          *)
(* generalise: at the all-decks mode of this instance, and at every instance  *)
(* whose run argument is a deck description, input distinguishability         *)
(* compares two inputs and says nothing about a secret.                       *)
(*                                                                            *)
(* The two programs share every line up to the Sampled level, and they must:  *)
(* a reading is a coordinate of the security claim and not of the model, so   *)
(* two programs that differ in the reading alone still name one execution,    *)
(* one model family and one link lemma. Neither of the paths they publish is  *)
(* among the manifest's twelve. The obstruction's path differs from the       *)
(* manifest's twelfth in its observed execution, that one being the           *)
(* all-decks run; a manifest path for the colour program needs its raw        *)
(* theorem stated below the manifest and is not written here.                 *)
```

### `psl211_dealt_family`

```
(** psl211_dealt_family — the fixed-dealer colour model as an analysis model
    family: one member per prior on the chirality, at every real field. The
    index is the prior and not the unit type, because the colour theorems of
    this instance hold under every prior and the two facts that refute
    independence need a prior giving mass to both chiralities. *)
```

### `psl211_dealt_sampled`

```
(** psl211_dealt_sampled — the shared prefix of both programs: the algebra,
    the dealer-dealt parameters at the instance's fuel, the three run facts
    and the model family. The two programs below branch here and nowhere
    earlier, which is what a reading being a coordinate of the security claim
    and not of the model means in the text of a program. *)
```

### `psl211_dealt_sampled_viewE`

```
(** psl211_dealt_sampled_viewE — the link lemma this level proves: at every
    real field, every prior and every coalition, the executed coalition
    reader of the dealer-dealt run is the direct computation on that run's
    argument and cut. It is what carries a claim about a reading of the
    endpoints to a claim about an execution. *)
```

### `psl211_colour_exact_witness`

```
(** psl211_colour_exact_witness — the exact-independence witness at the colour
    reading: the dealt chirality as the secret, and, below the threshold of
    six positions, the independence of the colours a coalition sees from it.
    The independence field is psl211_colour_reading_indep and nothing else,
    which is the instance's counting argument on five positions or fewer read
    as a privacy statement about what the colour reading grants. *)
```

### `psl211_colour_exact_published`

```
(** psl211_colour_exact_published — the colour program. What the finished
    value carries about a coalition of fewer than six of the twelve positions
    is independence of the dealt chirality from the colours that coalition
    sees, at every real field and every prior, with no number in it. It says
    nothing about the card identities the same coalition holds, which the
    obstruction below is about. *)
```

### `psl211_colour_exact_published_readingE`

```
(** psl211_colour_exact_published_readingE — the reading the published claim
    is made at is the colour reading, decided by conversion. It is the
    coordinate that separates this program from one certified at the
    coalition's own endpoints, which over this model would be false. *)
```

### `psl211_colour_exact_published_propertyE`

```
(** psl211_colour_exact_published_propertyE — the security property it carries
    is exact independence: an independence and not a bound at a number. *)
```

### `psl211_colour_exact_published_pathE`

```
(** psl211_colour_exact_published_pathE — the path it publishes records the
    dealer-dealt run, the AnalysisBridged level, the family the sample
    statement named and the two statuses. It is not one of the manifest's
    twelve: the manifest's paths for this instance are over the all-decks
    run, and a path whose observer column holds the colour reading needs its
    raw theorem stated below the manifest. *)
```

### `psl211_dealt_input_distinguishable`

```
(** psl211_dealt_input_distinguishable — the fixed-dealer model is input
    distinguishable at the coalition's own endpoint reading, at the
    reciprocal of the order of the shuffle group. The coalition is the three
    positions psl211_perdeck_coalition, below the threshold of six, and the
    two run arguments are the two chiralities of one deal: the encoder deck
    of one puts the three cards of psl211_dealt_view under exactly one cut
    and the other under none, so the two pushforwards of the uniform cut law
    differ at that reading by one cut's mass and the sum of absolute
    differences is at least that. Over these parameters the run argument is
    the chirality, so this is a privacy statement at this model, and that
    does not generalise to a mode whose run argument is a deck description.

    Each mass is pinned in a statement naming one chirality, and the two are
    brought together afterwards: a rewrite with a mass lemma in a goal
    holding both chiralities searches a goal holding both deck tables. *)
```

### `psl211_dealt_number`

```
(** psl211_dealt_number — 1/660, the reciprocal of the order of the shuffle
    group, as a term in the real field and in nothing else. The terminal
    writes this name after at, so the number a reader of the program meets
    and the number the published member carries are one term. *)
```

### `psl211_dealt_obstruction`

```
(** psl211_dealt_obstruction — the obstruction the second program publishes,
    at every real field and every prior: the model is input distinguishable
    at the coalition's own endpoint reading at 1/660. *)
```

### `psl211_dealt_number_gt0`

```
(** psl211_dealt_number_gt0 — the number is above zero, the shuffle group
    being non-empty. At a number at or below zero the distance inequality is
    free and a published member would compare nothing. *)
```

### `psl211_dealt_obstruction_pf`

```
(** psl211_dealt_obstruction_pf — its proof at every field and prior: the
    number is above zero, and the model is input distinguishable at it. *)
```

### `psl211_dealt_obstruction_published`

```
(** psl211_dealt_obstruction_published — the obstruction program. It
    certifies no security property, its data carrying no SecurityEvidence,
    and it denies what its one member names: every number at which an
    input-indistinguishability program over this model AT THIS READING states
    its proposition is at least 1/660, and no certificate at this reading has
    its ideal cut within eps of the model's own cut law once eps added to
    itself stays below 1/660. It leaves the colour reading untouched, where
    psl211_colour_exact_published certifies exact independence over the same
    model; the two are the pair a reading of a coalition's endpoints exists
    to separate. *)
```

### `psl211_dealt_obstruction_published_kindE`

```
(** psl211_dealt_obstruction_published_kindE — the obstruction the program
    hands over is the one written on its own line. *)
```

### `psl211_dealt_obstruction_published_pathE`

```
(** psl211_dealt_obstruction_published_pathE — the path it publishes records
    the dealer-dealt run, the AnalysisBridged level, the model family and
    NegativeTransfer. It is not the manifest's twelfth path, which is over
    the all-decks run, and it is not among the manifest's twelve. *)
```

### One in-proof comment, carried from the probe

```
(* the goal the existential leaves reads the coalition's endpoints through
   the identity reading, and the two masses above are stated at the bare
   reader. The identification is one iota step and one eta step and is
   discharged here, in a statement naming one chirality, rather than left to
   the conversion that closes the goal: a goal holding both chiralities and
   both deck tables is the shape that does not return *)
```
