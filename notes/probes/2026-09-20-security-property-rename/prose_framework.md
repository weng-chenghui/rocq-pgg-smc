# Prose pass, group "framework" (comments only)

Parent commit 77a2c84, branch feat/tableau-extensions-probe. Five files, all
comment text only. Verification below: comment-stripped copies of all five
files are byte-identical to HEAD, so no code token moved. Nothing compiled, no
Rocq process started, no git write, nothing under `notes/probes/` deleted.

Throughout this report the first barred noun is written `[N1]` and "port" is
written `[N2]` in every OLD quotation; nothing else in a quotation is altered.

## Counts per file, per case

| File | `[N1]` | case 1 | 2 | 3 | 4 | 5 | 6 | 7 | `[N2]` (all case 1 unless noted) |
|---|---|---|---|---|---|---|---|---|---|
| `manifest/pgg_tableau.v` | 92 | 38 | 16 | 9 | 14 | 0 | 7 | 8 | 22 |
| `manifest/pgg_tableau_security_property_relations.v` | 17 | 2 | 5 | 1 | 9 | 0 | 0 | 0 | 0 |
| `manifest/pgg_tableau_syntax.v` | 3 | 2 | 0 | 1 | 0 | 0 | 0 | 0 | 2 (one case 1, one case 2) |
| `manifest/pgg_analysis_manifest.v` | 4 | 3 | 0 | 0 | 0 | 1 | 0 | 0 | 0 |
| `security/var_dist_joint_law.v` | 2 | 0 | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| total | 118 | 45 | 22 | 12 | 23 | 1 | 7 | 8 | 24 |

The per-file totals match the counts in the dispatch exactly.

## Vocabulary this group now uses

Set by the declarations in `manifest/pgg_tableau.v` and followed by the other
four files:

- the evidence / security evidence — a value of `SecurityEvidence` (mass noun,
  no plural);
- the security property, or the property — a value of `SecurityProperty`;
- the exact-independence witness, the input-indistinguishability certificate,
  the proximity certificate — the three payloads;
- the exact-independence proposition, the input-indistinguishability
  proposition, the ideal-proximity proposition — the three values of
  `EvidenceProp`;
- the composition law for X — the three tail lemmas.

Cross-file check of the new phrases: "input-indistinguishability proposition"
5 in `pgg_tableau.v` and 6 in the relations file, "ideal-proximity
proposition" 4 and 5, "proximity certificate" 5, 4, 2 and 1 across the four
files that mention it, "security property" 20 and 1, "security evidence" 4.
The two sibling files say each of these one way.

---

## 1. `manifest/pgg_tableau.v` (92 + 22)

### Header paragraphs

**1 (cases 1, 2, 2, 2, 2, 2, 1, 1).**
OLD:
```
(* and certify_idealproximity adjoin a security witness of one [N1]. Each [N1] *)
(* speaks only of a coalition below the privacy threshold, and the [N1]s are   *)
(* not comparable statements: the exact [N1] concludes independence of the     *)
(* coalition's view from the secret, unconditionally and at every real field,  *)
(* the input-indistinguishability [N1] concludes a variation distance between  *)
(* the readings of two run arguments, bounded by the certificate's             *)
(* marginal-bound epsilon twice, one for each argument, and the proximity [N1] *)
(* concludes a variation distance between the joint law of the coalition's     *)
(* view with the secret and the product of the two marginals of an ideal       *)
(* model whose own privacy is exact. A program commits to one [N1] and claims  *)
(* nothing about the rest, and security_property_of names which [N1] a         *)
(* finished program committed to.                                              *)
```
NEW:
```
(* and certify_idealproximity adjoin the security evidence for one of three   *)
(* security properties. Each of the three propositions speaks only of a       *)
(* coalition below the privacy threshold, and the three are not comparable    *)
(* statements: the exact-independence proposition concludes independence of   *)
(* the coalition's view from the secret, unconditionally and at every real    *)
(* field, the input-indistinguishability proposition concludes a variation    *)
(* distance between the readings of two run arguments, bounded by the         *)
(* certificate's marginal-bound epsilon twice, one for each argument, and the *)
(* ideal-proximity proposition concludes a variation distance between the     *)
(* joint law of the coalition's view with the secret and the product of the   *)
(* two marginals of an ideal model whose own privacy is exact. A program      *)
(* commits to one security property and claims nothing about the rest, and    *)
(* security_property_of names which property a finished program committed to. *)
```
Fact: `SecurityEvidence` is the sum of the three payloads, so what a certify
statement adjoins is evidence; what concludes a statement about a coalition is
the proposition, not the name of the property.

**2 (case 4, twice).**
OLD: `The exact [N1]'s and the proximity [N1]'s propositions mention terms an instance chooses, so a program of either says as much as those terms say.`
NEW: `The exact-independence and the ideal-proximity propositions mention terms an instance chooses, so a program of either says as much as those terms say.`

**3 (case 2).**
OLD: `zero. The input-indistinguishability [N1] is different in kind:`
NEW: `zero. The input-indistinguishability proposition is different in kind:`
Fact: what is different in kind is `IndistinguishabilityPropAt`, named in the
next clause.

**4 (case 6).**
OLD: `Each [N1] has one composition law, and those laws are where the mathematics of the program sits.`
NEW: `Each of the three propositions is reached by one composition law, and those laws are where the mathematics of the program sits.`
Fact: `exact_tail`, `indistinguishability_tail` and `idealproximity_tail`
derive `ExactProp`, `IndistinguishabilityPropAt` and `IdealProximityPropAt`.

**5 ([N2] case 1 twice; [N1] cases 1 and 4).**
OLD:
```
(* conclude, which for an input-indistinguishability or a proximity [N2] is   *)
(* an inequality between the number the program's own certificate proved and  *)
(* the number the program publishes and for an exact [N2] is nothing. And of  *)
(* the three terminals only conclude returns a tableau and only it has a      *)
(* step's shape, but it too is outside: it leaves the data and the [N1]s      *)
(* untouched and moves the real an [N1]'s proposition mentions to any upper   *)
(* bound of it.                                                               *)
```
NEW:
```
(* conclude, which for input-indistinguishability or proximity evidence is an *)
(* inequality between the number the program's own certificate proved and the *)
(* number the program publishes and for exact-independence evidence is        *)
(* nothing. And of the three terminals only conclude returns a tableau and    *)
(* only it has a step's shape, but it too is outside: it leaves the data and  *)
(* the security property untouched and moves the real the evidence's          *)
(* proposition mentions to any upper bound of it.                             *)
```

### Index entries

**6 (case 3).** OLD `ExactWitness == the exact [N1]'s security witness`
NEW `ExactWitness == the security witness for exact independence`

**7 (case 3).** OLD `IndistinguishabilityCert == the input-indistinguishability [N1]'s security certificate`
NEW `IndistinguishabilityCert == the security certificate for input indistinguishability`

**8 (case 3).** OLD `IdealProximityCert == the proximity [N1]'s security certificate`
NEW `IdealProximityCert == the security certificate for ideal proximity`

**9 (case 1).** OLD `SecurityEvidence == the [N1] an instance certifies`
NEW `SecurityEvidence == the evidence an instance certifies with`
Fact: the `Variant` holds a witness or a certificate, not a name.

**10 (case 1).** OLD `SecurityProperty == which [N1], with no witness or certificate`
NEW `SecurityProperty == which security property, with no witness or certificate`

**11 (case 1 + [N2] case 1).** OLD `evidence_property == the [N1] a [N2] commits to`
NEW `evidence_property == the security property the evidence proves`
Fact: the definition maps a `SecurityEvidence` to a `SecurityProperty`; the
evidence does not commit to anything, the program does.

**12 (case 1).** OLD `view_secrecy_of == its security statement, exact-[N1] name`
NEW `view_secrecy_of == its security statement, under the exact-independence name`

**13 (case 1).** OLD `view_indistinguishability_of == the same statement, under the input-indistinguishability [N1]'s name`
NEW `view_indistinguishability_of == the same statement, under the input-indistinguishability name`

**14 (case 1).** OLD `view_proximity_of == the same statement, proximity-[N1] name`
NEW `view_proximity_of == the same statement, under the ideal-proximity name`

**15 (case 1).** OLD `security_property_of == which [N1] a published program carries`
NEW `security_property_of == which security property a published program carries`

**16, 17, 18 (case 6).**
OLD `exact_tail == the exact [N1]'s composition law`;
`indistinguishability_tail == the input-indistinguishability [N1]'s composition law`;
`idealproximity_tail == the proximity [N1]'s composition law`
NEW `exact_tail == the composition law for exact independence`;
`indistinguishability_tail == the composition law for input indistinguishability`;
`idealproximity_tail == the composition law for ideal proximity`

**19 ([N2] case 1).** OLD `evidence_conclude == a [N2]'s proposition at a number above its own bound`
NEW `evidence_conclude == the evidence's proposition at a number above its own bound`

**20, 21, 22 (case 7).**
OLD `certify_exact_propertyE == the exact statement writes the exact [N1]`;
`certify_indistinguishability_propertyE == the input-indistinguishability statement writes that [N1]`;
`certify_idealproximity_propertyE == the proximity statement writes the proximity [N1]`
NEW `certify_exact_propertyE == the exact statement's security property is exact independence`;
`certify_indistinguishability_propertyE == that statement's security property is input indistinguishability`;
`certify_idealproximity_propertyE == the proximity statement's security property is ideal proximity`
Fact: each lemma is the equation `ab_security_property (tableau_at (certify_… x q p)) R idx = …Property`.

**23, 24 (case 7).**
OLD `conclude_propertyE == concluding a program leaves its [N1] alone`;
`publish_propertyE == publishing a program leaves its [N1] alone`
NEW `conclude_propertyE == concluding a program leaves its security property alone`;
`publish_propertyE == publishing a program leaves its security property alone`

### Banners

**25 (case 1).** OLD `(*     The security witnesses of the [N1]s                                     *)`
NEW `(*     The security witnesses of the three properties                         *)`

**26 (case 1).** OLD `(*     Where a program's [N1] is decided                                       *)`
NEW `(*     Where a program's security property is decided                         *)`

### Declaration docstrings

**27 (case 3).** OLD `The exact [N1]'s witness: a secret random variable on the sampled space, and, at every coalition below the privacy threshold, …`
NEW `The exact-independence witness: a secret random variable on the sampled space, and, at every coalition below the privacy threshold, …`

**28 (case 3).** OLD `The input-indistinguishability [N1]'s certificate: a marginal bound on the instance's shuffle, …`
NEW `The input-indistinguishability certificate: a marginal bound on the instance's shuffle, …`

**29 (case 3).** OLD `The proximity [N1]'s certificate: a second sample adapter over the program's own execution, …`
NEW `The proximity certificate: a second sample adapter over the program's own execution, …`

**30 `SecurityEvidence` (cases 1, 1, 4, 2).**
OLD:
```
(* Which [N1] an instance certifies, at one real field and one index of its
   analysis family. A program commits to an [N1] here, and the proposition it
   carries from that line on is that [N1]'s own; the [N1]s are different
   statements about a coalition, so a program certifying input
   indistinguishability asserts nothing about mutual information. *)
```
NEW:
```
(* The evidence an instance certifies with, at one real field and one index of
   its analysis family: an exact-independence witness, an
   input-indistinguishability certificate or a proximity certificate. A program
   supplies one of the three here, and the proposition it carries from that
   line on is the one the evidence proves; the three are different statements
   about a coalition, so a program certifying input indistinguishability
   asserts nothing about mutual information. *)
```
Fact: the three constructors are `ExactIndependence of ExactWitness sa`,
`InputIndistinguishability of IndistinguishabilityCert sa`, `IdealProximity of
IdealProximityCert sa`. Every claim, hypothesis and consequence of the old
sentence survives.

**31 `SecurityProperty` (cases 1, 1).**
OLD:
```
(* Which [N1] a program commits to, with the witness and the certificate
   forgotten. … so two programs over one model and one pair of statuses are one
   manifest path; the [N1] is where they differ, and a reader asking what a
   finished program proved about a coalition reads this and not the manifest. *)
```
NEW:
```
(* Which of the three security properties a program commits to, with the
   witness and the certificate forgotten. A published program's manifest path
   records the execution, the level, the model family and the two statuses, and
   no theorem, so two programs over one model and one pair of statuses are one
   manifest path; the security property is where they differ, and a reader
   asking what a finished program proved about a coalition reads this and not
   the manifest. *)
```

**32 `evidence_property` (cases 1, 1; [N2] case 1 twice).**
OLD:
```
(* The [N1] a [N2] commits to, with its witness or its certificate forgotten.
   The constructor alone decides the answer, so a program's [N1] is fixed by the
   certify statement that wrote the [N2] and needs no proof about the model. *)
```
NEW:
```
(* The security property the evidence proves, with its witness or its
   certificate forgotten. The constructor alone decides the answer, so a
   program's security property is fixed by the certify statement that wrote the
   evidence and needs no proof about the model. *)
```

**33 `StackAt` ([N2] case 1).**
OLD `those with a security [N2] at every real field and index.`
NEW `those with security evidence at every real field and index.`

**34 `ab_evidence` block ([N2] case 1 twice, [N1] case 1).**
OLD:
```
(* The same at the AnalysisBridged level, together with the security [N2] at
   every real field and index. The [N2] is a function of the real field
   because the analysis family is, so the [N1] a program certifies is certified
   uniformly and not at one chosen field. *)
```
NEW:
```
(* The same at the AnalysisBridged level, together with the security evidence
   at every real field and index. The evidence is a function of the real field
   because the analysis family is, so the security property a program
   certifies is certified uniformly and not at one chosen field. *)
```

**35 `ab_security_property` (cases 1, 1; [N2] case 1 three times).**
OLD:
```
(* The [N1] the data at this level carries, at one real field and one index.
   The [N2] is a function of both, so the [N1] is read at the arguments the
   [N2] is written at rather than at one chosen field. The certify
   statements build a [N2] whose constructor is the same at every field and
   index, so for a program written in the surface the answer does not depend on
   either argument. *)
```
NEW:
```
(* The security property the data at this level carries, at one real field and
   one index. The evidence is a function of both, so the property is read at
   the arguments the evidence is written at rather than at one chosen field.
   The certify statements build evidence whose constructor is the same at every
   field and index, so for a program written in the surface the answer does not
   depend on either argument. *)
```

**36 `ExactProp` (cases 4, 1).**
OLD:
```
(* The exact [N1]'s proposition: below the threshold, … Independence leads
   and the entropy forms follow it, so the information-theoretic reading of
   the [N1] is proved from the same fact rather than assumed beside it. *)
```
NEW:
```
(* The exact-independence proposition: below the threshold, the coalition's
   executed view is independent of the secret, its mutual information with the
   secret is zero, conditioning on it leaves the secret's entropy unchanged,
   and every deterministic function of it is still independent. Independence
   leads and the entropy forms follow it, so the information-theoretic reading
   of exact independence is proved from the same fact rather than assumed
   beside it. *)
```

**37 `IndistinguishabilityPropAt` (cases 4, 2).**
OLD:
```
(* The input-indistinguishability [N1]'s proposition: below the threshold, two
   run arguments give coalition readings of the cut within variation distance
   c. The bound is a parameter rather than the certificate's own sum, so
   conclude can state a finished program at any number at or above that sum, the
   constant a paper cites among them, without reproving the [N1]. *)
```
NEW:
```
(* The input-indistinguishability proposition: below the threshold, two run
   arguments give coalition readings of the cut within variation distance c.
   The bound is a parameter rather than the certificate's own sum, so conclude
   can state a finished program at any number at or above that sum, the
   constant a paper cites among them, without reproving it. *)
```

**38 `cert_eps` (case 2).**
OLD `…one for each of the two run arguments the [N1] compares.`
NEW `…one for each of the two run arguments the input-indistinguishability proposition compares.`

**39 `IdealProximityPropAt` (cases 4, 2).**
OLD `The proximity [N1]'s proposition: below the threshold, …` and
`The bound is a parameter, as it is for the input-indistinguishability [N1], so conclude can state a finished program at any number at or above the certificate's ipc_eps, the one a paper cites among them.`
NEW `The ideal-proximity proposition: below the threshold, …` and
`The bound is a parameter, as it is for the input-indistinguishability proposition, so conclude can state a finished program at any number at or above the certificate's ipc_eps, the one a paper cites among them.`

**40 `ConcludedBound` ([N2] case 1).**
OLD `A single real will not serve, because the security [N2] quantifies over the real field and the published number is therefore a function of it.`
NEW `A single real will not serve, because the security evidence is given at every real field and the published number is therefore a function of it.`

**41 `EvidenceProp` ([N2] case 1; [N1] cases 2, 2, 2, 1, 4).**
OLD:
```
(* The proposition a [N2] carries at a given coordinate: independence for the
   exact [N1], the variation bound at the named number for the
   input-indistinguishability [N1], the distance to the ideal model's product
   law at the named number for the proximity [N1]. The [N1] selects the
   proposition, so a program cannot state one [N1]'s claim about another's
   witness. *)
```
NEW:
```
(* The proposition the evidence proves at a given coordinate: independence for
   a witness, the variation bound at the named number for an
   input-indistinguishability certificate, the distance to the ideal model's
   product law at the named number for a proximity certificate. The
   constructor selects the proposition, so a program cannot state one
   property's claim about another's witness. *)
```
Fact: the `match` scrutinises the three constructors, so the three branches are
named by the payload they bind.

**42 `BridgedProp` ([N2] case 1).**
OLD `…and at every real field and index the [N2]'s own proposition.`
NEW `…and at every real field and index the proposition the evidence proves.`

**43 `ExactPayload` (case 4).**
OLD `Uniformity in the field is what makes the [N1]'s conclusion unconditional rather than a statement at one chosen field.`
NEW `Uniformity in the field is what makes the exact-independence conclusion unconditional rather than a statement at one chosen field.`

**44 `IndistinguishabilityPayload` (case 2; already untrue, see below).**
OLD `…so the bound the [N1] publishes is a bound at every field rather than at one chosen field.`
NEW `…so the bound the program publishes is a bound at every field rather than at one chosen field.`

**45, 46, 47 (case 6).**
OLD `The composition law of the exact [N1], and what makes an ExactWitness the whole of what an instance supplies on it.`;
`The composition law of the input-indistinguishability [N1], and the only place the mixing bound is used.`;
`The composition law of the proximity [N1]; the two link hypotheses have the shape the previous statement proved, …`
NEW `The composition law for exact independence, and what makes an ExactWitness the whole of what an instance supplies on it.`;
`The composition law for input indistinguishability, and the only place the mixing bound is used.`;
`The composition law for ideal proximity; the two link hypotheses have the shape the previous statement proved, …`

**48, 49, 50 (cases 3 and 4, in each).**
OLD `Adjoins the exact [N1]'s witness at every real field and index, reaching AnalysisBridged with the [N1]'s proposition proved by exact_tail from the previous line's identification.`
NEW `Adjoins the exact-independence witness at every real field and index, reaching AnalysisBridged with the exact-independence proposition proved by exact_tail from the previous line's identification.`

OLD `Adjoins the input-indistinguishability [N1]'s certificate at every real field and index, reaching AnalysisBridged with the [N1]'s proposition proved by indistinguishability_tail.`
NEW `Adjoins the input-indistinguishability certificate at every real field and index, reaching AnalysisBridged with the input-indistinguishability proposition proved by indistinguishability_tail.`

OLD `Adjoins the proximity [N1]'s certificate at every real field and index, reaching AnalysisBridged with the [N1]'s proposition proved by idealproximity_tail.`
NEW `Adjoins the proximity certificate at every real field and index, reaching AnalysisBridged with the ideal-proximity proposition proved by idealproximity_tail.`

**51 `ConcludePayload` ([N2] case 1 three times; [N1] cases 2, 1, 1).**
OLD:
```
(* The obligation of conclude: at every real field and index, the number a
   [N2] carrying one is concluded at is at least that [N2]'s own, and nothing
   for an exact [N2]. A program may therefore publish the constant a paper cites
   whenever that constant is an upper bound of the distance the program proved,
   and may not publish a number below the one its certificate proved. The
   exact [N1] carries no number, so concluding a program leaves it untouched. An
   upper bound is the right obligation because the propositions of the two
   [N1]s that carry a number are monotone in it; an [N1] whose proposition is
   not monotone in the number it carries needs a different obligation here. *)
```
NEW:
```
(* The obligation of conclude: at every real field and index, the number a
   certificate is concluded at is at least that certificate's own, and nothing
   for an exact-independence witness. A program may therefore publish the
   constant a paper cites whenever that constant is an upper bound of the
   distance the program proved, and may not publish a number below the one its
   certificate proved. An exact-independence witness carries no number, so
   concluding a program leaves it untouched. An upper bound is the right
   obligation because the two propositions that carry a number are monotone in
   it; a security property whose proposition is not monotone in the number it
   carries needs a different obligation here. *)
```
Fact: the payload is `unit` in the `ExactIndependence` branch and an inequality
on `cert_eps cert` or `ipc_eps cert` in the other two, so the thing concluded
at a number is a certificate.

**52 `evidence_conclude` ([N2] case 1 twice; [N1] cases 1, 1).**
OLD:
```
(* A [N2]'s proposition at the program's own bound, and a proof that a chosen
   number is at least that bound, give the [N2]'s proposition at the chosen
   number. The step is sound because the propositions of the [N1]s that carry a
   number are monotone in it, which is the condition any future [N1] carrying a
   number must satisfy as well; it is what lets a program state the constant a
   paper cites while asserting about the coalition no more than the
   certificate proved. *)
```
NEW:
```
(* The proposition the evidence proves at the program's own bound, and a proof
   that a chosen number is at least that bound, give that proposition at the
   chosen number. The step is sound because the propositions that carry a
   number are monotone in it, which is the condition any future security
   property carrying a number must satisfy as well; it is what lets a program
   state the constant a paper cites while asserting about the coalition no
   more than the certificate proved. *)
```

**53 `conclude` (cases 1, 4).**
OLD `…the data and the [N1]s are unchanged, only the real the input-indistinguishability [N1]'s proposition mentions moves, and it moves only upward.`
NEW `…the data and the security property are unchanged, only the real the input-indistinguishability proposition mentions moves, and it moves only upward.`
See the open item below: the scope of this sentence was already narrow and I
left the narrowness untouched.

**54 `view_secrecy_of` (case 1).**
OLD `The security statement of a published program, under the name a reader of the exact [N1] expects.`
NEW `The security statement of a published program, under the name a reader of exact independence expects.`

**55 `view_indistinguishability_of` (cases 1, 2).**
OLD `The same projection under the name a reader of the input-indistinguishability [N1] expects. The [N1] is selected only when the result is applied, so naming the one that does not match a program fails at the next application rather than here.`
NEW `The same projection under the name a reader of input indistinguishability expects. The proposition is selected only when the result is applied, so naming the one that does not match a program fails at the next application rather than here.`

**56 `view_proximity_of` (cases 1, 4).**
OLD `The same projection under the name a reader of the proximity [N1] expects. The three names are one term and differ in what a reader is told to expect of it, which is the [N1]'s own proposition and is selected only when the result is applied.`
NEW `The same projection under the name a reader of ideal proximity expects. The three names are one term and differ in what a reader is told to expect of it, which is the proposition the evidence proves and is selected only when the result is applied.`

**57 `security_property_of` (case 1).**
OLD `Which [N1] a published program carries, at one real field and one index of its family.`
NEW `Which security property a published program carries, at one real field and one index of its family.`

**58 `certify_exact_propertyE` (cases 7, 1).**
OLD `A program built by the exact statement carries the exact [N1] at every real field and index of its family. With conclude_propertyE and publish_propertyE below it settles the [N1] of a finished program by one line of the program's text, …`
NEW `A program built by the exact statement carries exact independence at every real field and index of its family. With conclude_propertyE and publish_propertyE below it settles the security property of a finished program by one line of the program's text, …`

**59 `certify_indistinguishability_propertyE` (case 1; [N2] case 1).**
OLD `With certify_exact_propertyE this is what makes the [N1] a property of the program's text: the certify statements are the only ones that build a [N2], and each writes one constructor at every field and index.`
NEW `With certify_exact_propertyE this is what makes the security property readable off the program's text: the certify statements are the only ones that build evidence, and each writes one constructor at every field and index.`
"a property of the program's text" would read after the rename as "a security
property of the program's text"; "readable off the program's text" keeps the
claim and removes the collision.

**60 `certify_idealproximity_propertyE` ([N2] case 1).**
OLD `The three statements are the only ones that build a [N2], and each writes one constructor at every field and index, …`
NEW `The three statements are the only ones that build evidence, and each writes one constructor at every field and index, …`

**61 `conclude_propertyE` (case 7).**
OLD `Concluding a program at a chosen number leaves its [N1] where the certify statement put it.`
NEW `Concluding a program at a chosen number leaves its security property where the certify statement put it.`

**62 `publish_propertyE` (cases 1, 1, 1, 7).**
OLD `Publishing attaches the manifest path and leaves the [N1] alone, so the [N1] a finished program reports is the [N1] its data carried before the last line. This is the step that carries the three certify statements' [N1] equations out to a published program.`
NEW `Publishing attaches the manifest path and leaves the security property alone, so the property a finished program reports is the one its data carried before the last line. This is the step that carries the three certify statements' property equations out to a published program.`

---

## 2. `manifest/pgg_tableau_security_property_relations.v` (17 + 0)

The file's "Not claimed." paragraph is untouched, word for word.

**1 (case 4, title).**
OLD `(* pgg_tableau_security_property_relations: what separates the [N1]s'          *)` / `(* propositions                                                               *)`
NEW `(* pgg_tableau_security_property_relations: what separates the two security   *)` / `(* properties' propositions                                                   *)`

**2 (cases 1, 4).**
OLD `A Tableau program certifies one of three [N1]s, and two of the three carry a number. Both numbers can be read off one variation distance on the cut group, so a reader may take one [N1]'s proposition for a restatement of the other's.`
NEW `A Tableau program certifies one of three security properties, and two of the three carry a number. Both numbers can be read off one variation distance on the cut group, so a reader may take one property's proposition for a restatement of the other's.`

**3 (cases 2, 2).**
OLD `What the two [N1]s share is a carrier. idealproximity_reading_le reads the proximity number as a bound between the two models' reading marginals, which is the carrier the input-indistinguishability [N1] states its own bound on.`
NEW `What the two propositions share is a carrier. idealproximity_reading_le reads the proximity number as a bound between the two models' reading marginals, which is the carrier the input-indistinguishability proposition states its own bound on.`

**4 (cases 2, 4).**
OLD `The [N1]'s mathematics rests on the ideal witness's independence: it turns the ideal joint law into the product of its marginals, and the [N1]'s proposition compares the actual joint law with exactly that product.`
NEW `The mathematics of ideal proximity rests on the ideal witness's independence: it turns the ideal joint law into the product of its marginals, and the ideal-proximity proposition compares the actual joint law with exactly that product.`

**5 (case 4, index entry).**
OLD `idealproximity_prop_at2 == every proximity certificate satisfies the [N1]'s proposition at two`
NEW `idealproximity_prop_at2 == every proximity certificate satisfies the ideal-proximity proposition at two`

**6 (case 4, banner).**
OLD `(*     The two [N1]s' propositions are two propositions                        *)`
NEW `(*     The two security properties' propositions are two propositions         *)`

**7 (case 4, docstring of `idealproximity_prop_at2`).**
OLD `Every proximity certificate satisfies the [N1]'s proposition at two, whatever its model, its ideal and its own number, …`
NEW `Every proximity certificate satisfies the ideal-proximity proposition at two, whatever its model, its ideal and its own number, …`

**8 (cases 4, 2; docstring of `indistinguishability_prop_cert_free`).**
OLD:
```
(** The input-indistinguishability [N1]'s proposition at two certificates over
    one model is one proposition. The certificate is a parameter of the
    statement and occurs nowhere in it, so what the
    input-indistinguishability [N1] claims is a property of the model's own
    cut law and the number, and the ideal law the certificate names has left
    the claim. …
```
NEW:
```
(** The input-indistinguishability proposition at two certificates over one
    model is one proposition. The certificate is a parameter of the statement
    and occurs nowhere in it, so what the input-indistinguishability
    proposition claims is determined by the model's own cut law and the
    number, and the ideal law the certificate names has left the claim. …
```
"is a property of" became "is determined by" for the same collision reason as
item 59 of the first file: after the rename "a property of" reads as a security
property. The claim is unchanged.

**9 (case 4).**
OLD `The proximity [N1]'s proposition mentions its certificate, through the ideal adapter, that ideal's witness and the actual model's secret, …`
NEW `The ideal-proximity proposition mentions its certificate, through the ideal adapter, that ideal's witness and the actual model's secret, …`

**10 (cases 3, 2, 1; docstring of `idealproximity_reading_le`).**
OLD `This is the [N1]'s number read on the carrier the input-indistinguishability [N1] states its own bound on, and it needs no model of one [N1] to be a model of the other.`
NEW `This is the proximity number read on the carrier the input-indistinguishability proposition states its own bound on, and it needs no model of one property to be a model of the other.`
"the proximity number" is the file's own existing phrase, used twice above.

**11 (case 4; the recorded failure at the end of the file).**
OLD `What remains is the certificate's distance between two joint laws and the two link lemmas, and the [N1]'s proposition compares the actual joint law with a product, …`
NEW `What remains is the certificate's distance between two joint laws and the two link lemmas, and the ideal-proximity proposition compares the actual joint law with a product, …`

---

## 3. `manifest/pgg_tableau_syntax.v` (3 + 2)

**1 ([N2] case 1).**
OLD `The tokens inputs, terminates, publish, conclude, vm_compute, ExactIndependence, InputIndistinguishability and IdealProximity follow a literal and stay identifiers, which is what keeps the three [N2] constructors and the conclude terminal usable by name;`
NEW `… which is what keeps the three evidence constructors and the conclude terminal usable by name;`
Fact: the three tokens named in the same sentence are the constructors of
`SecurityEvidence`.

**2 ([N2] case 2; docstring of `mk_indistinguishability`).**
OLD `The split is what makes the [N2]'s perfect and statistical halves visible where it is written: the fourth component is an inequality at the first component's epsilon, and the fifth is an equation.`
NEW `The split is what makes the certificate's perfect and statistical halves visible where it is written: the fourth component is an inequality at the first component's epsilon, and the fifth is an equation.`
Fact: the builder returns an `IndistinguishabilityCert`, whose fourth and fifth
fields are exactly the two halves named.

**3 (case 1, banner).**
OLD `(*     The tightness annotation of the exact [N1]                              *)`
NEW `(*     The tightness annotation of exact independence                         *)`

**4 (case 1).**
OLD `It attaches to the exact [N1] alone, so a program certifying input indistinguishability carries no such claim.`
NEW `It attaches to exact independence alone, so a program certifying input indistinguishability carries no such claim.`

**5 (case 3).**
OLD `The exact [N1]'s witness, with a tightness annotation checked against it and then dropped.`
NEW `The exact-independence witness, with a tightness annotation checked against it and then dropped.`

---

## 4. `manifest/pgg_analysis_manifest.v` (4 + 0)

**1 (case 1, three times).**
OLD:
```
(* A path records no security [N1]. Which [N1] a published program carries is *)
(* read off that program by security_property_of of manifest/pgg_tableau.v,   *)
(* so which [N1] a path carries is told from the certificate its table names  *)
(* and not from a field of the record.                                        *)
```
NEW:
```
(* A path records no security property. Which one a published program         *)
(* carries is read off that program by security_property_of of                *)
(* manifest/pgg_tableau.v, so which property a path carries is told from the  *)
(* certificate its table names and not from a field of the record.            *)
```

**2 (case 5, the `pgl27_prior_exact_path` table row).**
OLD:
```
(* | bound or certificate | none: this program is published through the exact *)
(*                          [N1], whose witness carries independence and no   *)
(*                          number |                                          *)
```
NEW:
```
(* | bound or certificate | none: this program is published with              *)
(*                          exact-independence evidence, whose witness        *)
(*                          carries independence and no number |              *)
```
Case 5 of the sheet, in its own words: "published through the exact X" becomes
"published with exact-independence evidence". The row's claim, that the
program carries a witness and no number, survives.

---

## 5. `security/var_dist_joint_law.v` (2 + 0)

Both sites are in the docstring of `var_dist_fdistmap_pair` and both say which
derivation uses the lemma. Per the group guidance I named the field the lemma
discharges. `var_dist_fdistmap_pair` is applied in
`instances/kim2025/five_card_proximity.v:160` and
`instances/psl211/psl211_word_proximity.v:101`, in both cases to prove the
`ipc_close` field of an `IdealProximityCert`, so `ipc_close` is the accurate
name.

**1 (case 3) and 2 (case 2).**
OLD:
```
    data processing along the map pairing the two readers, and it is the step
    by which the proximity [N1]'s certificate is discharged: the actual and the
    ideal model of one execution differ only in the law they draw a sample
    point from, and the pair the [N1] compares is a deterministic function of
    that point. *)
```
NEW:
```
    data processing along the map pairing the two readers, and it is the step
    by which a proximity certificate's ipc_close field is discharged: the
    actual and the ideal model of one execution differ only in the law they
    draw a sample point from, and the pair ipc_close compares is a
    deterministic function of that point. *)
```

---

## Sentences the sheet's verb rule showed were already untrue

Each was made true; all are in `manifest/pgg_tableau.v` unless noted.

1. `IndistinguishabilityPayload`: "the bound the [N1] publishes". A security
   property publishes nothing; a program publishes. Now "the bound the program
   publishes".
2. `ConcludePayload`: "The exact [N1] carries no number". A property carries
   nothing; the witness is the thing with no numeric field. Now "An
   exact-independence witness carries no number".
3. `ConcludePayload`: "the number a [N2] carrying one is concluded at is at
   least that [N2]'s own, and nothing for an exact [N2]". The payload is `unit`
   in the witness branch, so what is concluded at a number is a certificate.
   Now "the number a certificate is concluded at is at least that
   certificate's own, and nothing for an exact-independence witness".
4. `evidence_property` (index entry and docstring): "the [N1] a [N2] commits
   to". Evidence does not commit; the function returns the property the
   evidence proves. Now "the security property the evidence proves".
5. `EvidenceProp`: "The [N1] selects the proposition". A property selects
   nothing; the `match` selects on the constructor. Now "The constructor
   selects the proposition".
6. `view_indistinguishability_of`: "The [N1] is selected only when the result
   is applied". What `EvidenceProp` selects is the proposition. Now "The
   proposition is selected only when the result is applied".
7. Header: "Each [N1] has one composition law". A property has nothing; each
   proposition is derived by one tail lemma. Now "Each of the three
   propositions is reached by one composition law".
8. `ConcludedBound`: "the security [N2] quantifies over the real field". One
   value quantifies over nothing; the stack component is a function of the
   field. Now "the security evidence is given at every real field".
9. Header, `certify_*` docstrings, `ExactProp`, `IndistinguishabilityPropAt`,
   `cert_eps`, `IdealProximityPropAt`, and the relations file throughout: a
   property "concludes", "compares", "states", "claims", "is different in
   kind". In every such site the subject became the proposition, which is what
   states and compares.

## For the main session

1. **A claim I deliberately left narrow.** `manifest/pgg_tableau.v`, docstring
   of `conclude`: "only the real the input-indistinguishability proposition
   mentions moves, and it moves only upward". `ConcludePayload` and
   `evidence_conclude` also move the number in the `IdealProximity` branch
   (`ipc_eps cert <= odflt (ipc_eps cert) (c R)`), so the sentence names one of
   the two propositions that carry a number. Widening it would add a claim,
   which rule 1 forbids, so I renamed the noun and left the scope as it was.
   The owner may want "the real a proposition carrying a number mentions".
2. **Two "property" collisions resolved by rewording, not by the case table.**
   `certify_indistinguishability_propertyE` ("makes the [N1] a property of the
   program's text" -> "makes the security property readable off the program's
   text") and `indistinguishability_prop_cert_free` in the relations file ("is
   a property of the model's own cut law" -> "is determined by the model's own
   cut law"). In both the English word "property" would now be read as
   `SecurityProperty`. The claims are unchanged; flagging because the wording
   moved further than the noun.
3. **Two adjective spellings coexist, both sanctioned by the sheet.** "the
   proximity certificate" (the tree's existing short form, kept) beside "the
   ideal-proximity proposition" (the sheet's case-4 wording). Likewise "the
   proximity number" in the relations file. If the owner wants one spelling
   everywhere, the short form is the one to promote or retire.
4. **Site outside this group, not edited.** `instances/psl211/psl211_exec.v`
   line 127, in the forward closure of `psl211_endpoints.v`:
   `    declares is six, so every [N1] of a row over this algebra quantifies over`.
   This looks like a third sense (a row's quantified slots), not one of the
   seven cases; it needs the owner's reading.

## Final scan

Word-boundary search for either noun, any inflection, any case, over the whole
text of all five files:

| File | `[N1]` | `[N2]` |
|---|---|---|
| `manifest/pgg_tableau.v` | 0 | 0 |
| `manifest/pgg_tableau_security_property_relations.v` | 0 | 0 |
| `manifest/pgg_tableau_syntax.v` | 0 | 0 |
| `manifest/pgg_analysis_manifest.v` | 0 | 0 |
| `security/var_dist_joint_law.v` | 0 | 0 |

Layout: every boxed line I wrote is exactly 80 bytes with a space before the
closing delimiter; no comment line exceeds 80 bytes in any of the five files
(the three over-length lines the style check reports in
`manifest/pgg_tableau_syntax.v` are pre-existing `Notation` code, lines 333,
371 and 402). One pre-existing 79-byte boxed line at
`manifest/pgg_analysis_manifest.v:618` was not touched, because it is not a
site of this pass. The `==` columns and the continuation columns of every
index entry are preserved, docstring continuations stay at 4 spaces and
`(* … *)` continuations at 3, banners remain one content line.

Code check: with all comments stripped and whitespace normalised, each of the
five files is identical to its version at HEAD. No code token changed.
