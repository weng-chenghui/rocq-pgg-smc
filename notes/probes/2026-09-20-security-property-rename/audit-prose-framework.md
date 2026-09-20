# Adversarial audit, group "framework" (comments-only pass on top of 77a2c84)

Read-only audit. No repository file was edited except this one. Nothing was
compiled, no Rocq process was started, no git command that writes was run.
The first barred noun is written `[N1]` and the second `[N2]` in every OLD
quotation. Nothing else in a quotation is altered.

## Verdict

**GO with fixes.** The pass is sound where it counts. No claim, hypothesis,
number, quantifier or lemma name was lost at any of the 142 sites, by a
reading of every OLD and NEW pair and by a mechanical word-level check of
every hunk. The seven cases were applied as the sheet rules them, and at all
but three sites the thing named is the thing the declaration defines. Those
three are F8, F9 and F17, where a concrete noun replaced a vague one and
landed beside the object it describes rather than on it. Two further classes
of defect should be cleared before the commit.

1. **Two orphan lines of 17 and 18 bytes** in `manifest/pgg_tableau.v`
   (F1, F2). Both were created by this pass: the rewritten lines were
   rewrapped and the untouched trailing line of the same paragraph was not.
   Rule 4 of the sheet bars an orphan short line.
2. **Three predications the sheet's own verb rule forbids, in new text**
   (F3, F4, F7): a security property that "carries" a number, twice, and a
   model "of one property". The pass corrected the same predication three
   lines away from F3, so these are slips and not a reading of the rule.

Everything else below is a SHOULD or a NOTE. The one open item handed over by
the agent, the docstring of `conclude`, is confirmed against the code and a
true sentence is proposed as F5. Its narrowness is inherited from the parent
commit and the agent was right to refuse to widen it unasked, since sheet
rule 1 bars adding a claim. Widening it is the owner's call and the dispatch
asked for the sentence, so it is graded MUST here.

The other two flags the agent raised for the main session are both clean. The
two rewordings that removed a collision with the English word "property"
preserve their claims, see item 5. The coexistence of two adjectival
spellings is not a matter of taste in one file, see F10.

## Findings

| id | grade | file:line | OLD (placeholders) | NEW | problem, with the declaration | replacement |
|---|---|---|---|---|---|---|
| F1 | MUST | `manifest/pgg_tableau.v:1009-1012` | `Which [N1] a published program carries, at one real field and one index of its family. It reads ab_security_property past the publish statement, and` | `... It reads ab_security_property past the publish statement, and` on its own 17-byte line | The pass rewrapped the first two lines and left the old fourth line in place, so line 1011 is `   statement, and`, 17 bytes where the paragraph wraps at 74 to 78. `Definition security_property_of (c : ConcludedBound) (r : PublishedAt c) (R : realType) (idx : ...)`. Sheet rule 4: no orphan short line | see F1 below |
| F2 | MUST | `manifest/pgg_tableau.v:1060-1064` | `Concluding a program at a chosen number leaves its [N1] where the certify statement put it. The terminal moves a real and not the alternative the` | same sentence, rewrapped only down to the changed line | Line 1062 is `   alternative the` (18 bytes). Same half-done rewrap as F1. `Lemma conclude_propertyE (c : ConcludedBound) (q : StackAt AnalysisBridged) ... ab_security_property ... = ab_security_property ...` | see F2 below |
| F3 | MUST | `manifest/pgg_tableau.v:867-869` | `the propositions of the two [N1]s that carry a number are monotone in it; an [N1] whose proposition is not monotone in the number it carries needs a different obligation here.` | `the two propositions that carry a number are monotone in it; a security property whose proposition is not monotone in the number it carries needs a different obligation here.` | A security property is a name and carries nothing. Three lines earlier the same pass replaced "the exact [N1] carries no number" with "An exact-independence witness carries no number" for exactly this reason. `Variant SecurityProperty := ExactIndependenceProperty \| InputIndistinguishabilityProperty \| IdealProximityProperty.` The number lives in `cert_eps cert` and `ipc_eps cert`, and the proposition mentions it: `IndistinguishabilityPropAt cert (odflt (cert_eps cert) (c R))` | see F3 below |
| F4 | MUST | `manifest/pgg_tableau.v:883-885` | `the propositions of the [N1]s that carry a number are monotone in it, which is the condition any future [N1] carrying a number must satisfy as well` | `the propositions that carry a number are monotone in it, which is the condition any future security property carrying a number must satisfy as well` | Same predication as F3, in the docstring of `Lemma evidence_conclude ... EvidenceProp no_concluded_bound p -> (match p with ... \| InputIndistinguishability cert => cert_eps cert <= odflt (cert_eps cert) (c R) ...) -> EvidenceProp c p` | see F4 below |
| F5 | MUST | `manifest/pgg_tableau.v:908-912` | `the data and the [N1]s are unchanged, only the real the input-indistinguishability [N1]'s proposition mentions moves, and it moves only upward.` | `the data and the security property are unchanged, only the real the input-indistinguishability proposition mentions moves, and it moves only upward.` | The open item, confirmed false as an exclusivity claim. `Definition conclude ... := @MkTableau ... (fun R idx => evidence_conclude c (ab_evidence q R idx) (proj2 pf R idx) (p R idx))`, and `EvidenceProp`'s third branch is `IdealProximityPropAt cert (odflt (ipc_eps cert) (c R))`, whose number moves under the same `ConcludePayload` obligation `ipc_eps cert <= odflt (ipc_eps cert) (c R)`. So the real the ideal-proximity proposition mentions moves too, and "only" excludes it. The parent commit carried the same narrowness, so this is an inherited defect the rename made checkable | see F5 below |
| F6 | SHOULD | `manifest/pgg_tableau.v:477` | `without reproving the [N1].` | `without reproving it.` | "it" has no antecedent that makes the clause true: the nearest noun phrases are "the constant a paper cites", "that sum" and "a finished program". OLD named the thing reproved. `Definition IndistinguishabilityPropAt ... (cert : IndistinguishabilityCert sa) (c : R) : Prop := forall C x x', ... var_dist ... <= c` | `... the constant a paper cites among them, without reproving the proposition. *)` |
| F7 | SHOULD | `manifest/pgg_tableau_security_property_relations.v:151-153` | `This is the [N1]'s number read on the carrier the input-indistinguishability [N1] states its own bound on, and it needs no model of one [N1] to be a model of the other.` | `This is the proximity number read on the carrier the input-indistinguishability proposition states its own bound on, and it needs no model of one property to be a model of the other.` | One sentence, one pair of objects, two nouns: the first is "proposition", the second is "property". A model satisfies a proposition, and a property is a name. `Lemma idealproximity_reading_le (cert : IdealProximityCert sa) (c : R) : IdealProximityPropAt cert c -> forall C, ... var_dist ... <= c` | `... states its own bound on, and it needs no model of one proposition to be a model of the other. *)` |
| F8 | SHOULD | `manifest/pgg_tableau.v:860-862` | `at every real field and index, the number a [N2] carrying one is concluded at is at least that [N2]'s own, and nothing for an exact [N2].` | `at every real field and index, the number a certificate is concluded at is at least that certificate's own, and nothing for an exact-independence witness.` | A certificate is not concluded at a number, a program is. The old subject was vague, so the substitution made a loose predication concrete and wrong. `Definition ConcludePayload (c : ConcludedBound) (q : StackAt AnalysisBridged) : Type := forall R idx, match ab_evidence q R idx with \| ExactIndependence _ => unit \| InputIndistinguishability cert => cert_eps cert <= odflt (cert_eps cert) (c R) \| IdealProximity cert => ipc_eps cert <= odflt (ipc_eps cert) (c R) end` | `(* The obligation of conclude: at every real field and index, the number the` / `   program is concluded at is at least the certificate's own, and nothing for` / `   an exact-independence witness. ...` |
| F9 | SHOULD | `manifest/pgg_tableau.v:539-540` | `independence for the exact [N1], the variation bound at the named number for the input-indistinguishability [N1], ...` | `independence for a witness, the variation bound at the named number for an input-indistinguishability certificate, ...` | The other two branches name their payload type, this one says "a witness". The file has a second witness in scope, `ipc_witness cert : ExactWitness (ipc_ideal cert)`, so "a witness" is ambiguous where OLD was not. `match p with \| ExactIndependence w => ExactProp w \| ...` | see F9 below |
| F10 | SHOULD | `manifest/pgg_tableau_security_property_relations.v:37, 56, 91, 128, 193` | five sites of the form `the proximity [N1]'s proposition` / `the [N1]'s proposition` | `the ideal-proximity proposition` | The file already said "the proximity proposition" at six untouched places, lines 18-19, 42, 48, 120, 122 and 141, so the file now names one object two ways, six times the short way and five times the long way. Sharpest at the header, line 18-20, `The proximity proposition does mention its certificate, through the ideal adapter, that ideal's witness and the actual model's secret`, against the docstring at line 128, `The ideal-proximity proposition mentions its certificate, through the ideal adapter, that ideal's witness and the actual model's secret`: one fact, two spellings, in one file | owner's call, one of the two, file-wide. Promoting "ideal-proximity proposition" at the six untouched sites agrees with `manifest/pgg_tableau.v`, which uses that form and no other. Retiring it at the five new sites is what the sheet's parenthetical allows ("where the tree already says ... the proximity proposition, that short form stays") and touches no untouched line |
| F11 | NOTE | `manifest/pgg_tableau.v:77` and `:131` | `moves the real an [N1]'s proposition mentions`, `evidence_conclude == a [N2]'s proposition at a number above its own bound` | `moves the real the evidence's proposition mentions`, `evidence_conclude == the evidence's proposition at a number above its own bound` | "the evidence's proposition" twice against "the proposition the evidence proves" at lines 88, 252, 273, 538, 558, 880 and 1002. The index entry at 131 and the docstring at 880 are the two descriptions of one lemma and they disagree | index entry: `(*   evidence_conclude      == the proposition the evidence proves, at a      *)` / `(*                             number above its own bound                     *)`, both 80 bytes. Line 77 reads correctly as it stands and needs no change if the owner accepts the possessive as a short form |
| F12 | NOTE | `manifest/pgg_tableau.v:72-74` | `for an input-indistinguishability or a proximity [N2] ... and for an exact [N2] is nothing` | `for input-indistinguishability or proximity evidence is an inequality ... and for exact-independence evidence is nothing` | One sentence carries two full adjectival names and one short one. The sheet sanctions the short "proximity", so this is legible, but "exact-independence evidence" and "proximity evidence" side by side read as different registers | optional: `for input-indistinguishability or ideal-proximity evidence` |
| F13 | NOTE | `security/var_dist_joint_law.v:66-70` | `it is the step by which the proximity [N1]'s certificate is discharged ... the pair the [N1] compares` | `it is the step by which a proximity certificate's ipc_close field is discharged ... the pair ipc_close compares` | A narrowing, not a substitution: OLD said the certificate, NEW says one field. Verified true. `var_dist_fdistmap_pair` is applied at `instances/kim2025/five_card_proximity.v:160`, inside `kim_biased_proximity_close`, and at `instances/psl211/psl211_word_proximity.v:101`, inside `psl211_word_proximity_close`, and both goals have the shape of `ipc_close`: `var_dist (fdistmap (fun u => (static_coalition_obs ..., secret u)) ...) (fdistmap ... ) <= eps`. Two residues: the docstring now names an identifier declared in `manifest/pgg_tableau.v`, which `security/var_dist_joint_law.v` does not import and which does not import it either, so a rename of the field would not be caught here, and `ipc_close` compares the two laws of that pair rather than the pair | accept as is, or `the pair whose two laws ipc_close compares is a deterministic function of that point` |
| F14 | NOTE | `manifest/pgg_tableau_security_property_relations.v:117` | (reflow only) | `    ideal a proximity certificate names can therefore not be` | 60 bytes with the next word, "recovered", 9 bytes long, so the line is 10 bytes short of a full one in the middle of a paragraph. Less severe than F1 and F2 but the same cause | rewrap the paragraph from line 112 to line 122 |
| F15 | NOTE | `manifest/pgg_tableau.v:753-756` | `The composition law of the input-indistinguishability [N1], and the only place the mixing bound is used.` | `The composition law for input indistinguishability, and the only place the mixing bound is used.` | The last line of the docstring is `   used. *)` alone. The orphan is in the parent too, and the new text is shorter, so the rewrap could absorb it | end the third line `... the only place the mixing bound is used. *)` |
| F16 | NOTE | `manifest/pgg_analysis_manifest.v:17-21` | `A path records no security [N1]. Which [N1] a published program carries is read off that program by security_property_of ..., so which [N1] a path carries is told from the certificate its table names and not from a field of the record.` | `A path records no security property. Which one a published program carries is read off that program by security_property_of of manifest/pgg_tableau.v, so which property a path carries is told from the certificate its table names and not from a field of the record.` | The first sentence and the third now contradict each other in the reader's eye: a path records no security property, and then a path carries one. The predication is inherited from the parent, but the rename put the two words in adjacent sentences. A path records | see F16 below |
| F17 | NOTE | `manifest/pgg_tableau.v:133-141`, three index entries | `certify_exact_propertyE == the exact statement writes the exact [N1]`, and the two beside it | `== the exact statement's security property is exact independence`, `== that statement's security property is input indistinguishability`, `== the proximity statement's security property is ideal proximity` | A certify statement takes a payload and builds a program, and it is the program that carries a security property. The equation is `ab_security_property (tableau_at (@certify_exact x q p)) R idx = ExactIndependenceProperty`, so the subject is the program. The docstring at line 1023 has it right, "A program built by the exact statement carries exact independence at every real field and index of its family", and only the index entry attributes the property to the statement | `(*                          == a program built by the exact statement carries *)` / `(*                             exact independence                             *)`, and likewise for the other two |

### Item 1, what the rewrites lost or added

Two passes, one by reading and one mechanical. The mechanical one takes every
hunk of `git diff -U0` for the five files, splits the removed and the added
text into words, drops the function words and the words of the rename itself,
and prints the difference both ways. Over all five files it reports no content
word lost that was not replaced in the same clause. The list of removals is
short enough to quote in full: "has" for "is reached by" in the header,
"writes" for the possessive in the three index entries of F17, "commits" for
"supplies" and for "proves" at `SecurityEvidence` and `evidence_property`,
"quantifies over" for "is given at every" at `ConcludedBound`, "carries" for
"proves" at `EvidenceProp`, "carrying one" for "a certificate" at
`ConcludePayload`, "own" for "that proposition" at `evidence_conclude`, and
"through" for "with" in the manifest row. Each is a substitution inside its
own clause and each was checked against the declaration. No number, no
quantifier, no hypothesis and no lemma name was dropped anywhere, and the
additions are the rename's nouns plus "readable off", "determined by",
"ipc_close" and "field", all four of which are covered by F13, item 5 and the
agent's own two flags.

### Sentences flagged by item 3 that this pass did not touch

All but the last are pre-existing and none was a site, so none is a defect of
the pass. They are listed because the same verb rule reaches them and because
the first two sit in docstrings this pass rewrote in their other sentences.

- `manifest/pgg_tableau.v:228`, docstring of `IdealProximityCert`: "any number
  at which ipc_close is provable is a legal field, so a certificate says as
  much as its number is small and no more". A certificate holds fields and
  proves a proposition.
- `manifest/pgg_tableau.v:725`, docstring of `exact_tail`, whose third
  sentence this pass rewrote: "The independence a witness states at the direct
  computation". A witness holds the field `ew_indep`, and it is `ExactProp`
  that states.
- `manifest/pgg_analysis_manifest.v:121`, `:530`, `:668`: "the path compares no
  idealized model", "the path states exact results at its own executed
  observers and compares no idealized model", "so the path compares no
  idealized model". A path records. The comparison and the statement belong to
  the program on the path.
- `security/var_dist_joint_law.v:69`: "the pair ipc_close compares", see F13.

The two neighbours named in the dispatch, a certificate that "compares" and a
certificate that "states", are not in these five files. A subject-verb scan
over every line joined with its successor finds no such pair here. What this
group has instead is the list above: a certificate that "says", a witness that
"states", three paths that "compare" or "state", and the one field that
"compares", which is new text and is F13.

Two sentences the group asked about specifically are clean. `manifest/pgg_tableau_security_property_relations.v:139`, "an input-indistinguishability certificate carries no secret and no ideal model", is a record with no such field and "carries" is right. `manifest/pgg_analysis_manifest.v:818`, "the program's certificate carries its own distance field", is right for the same reason.

### Item 5, the word "property" after the rename

Every occurrence of the English word "property" or "properties" in the five
files is now the `SecurityProperty` sense. Thirty-nine occurrences, 32 in
`manifest/pgg_tableau.v`, 5 in the relations file, 2 in
`manifest/pgg_analysis_manifest.v` and none in the other two, by a
word-boundary scan of all five files, and no residual English use. The one
site in the parent that would have been misread, `manifest/pgg_tableau_security_property_relations.v:113`, "what the input-indistinguishability [N1] claims is a property of the model's own cut law", was reworded to "is determined by the model's own cut law", and the claim survives: both say the claim is a function of the cut law and the number and of nothing the certificate carries. The second rewording, `certify_indistinguishability_propertyE`, "makes the [N1] a property of the program's text" to "makes the security property readable off the program's text", also keeps the claim, which the lemma statement supports: `ab_security_property (tableau_at (certify_indistinguishability x q p)) R idx = InputIndistinguishabilityProperty` by `Proof. by []. Qed.`, that is, by the text alone.

### Item 6, one word per concept

- `manifest/pgg_tableau.v` is internally consistent: "ideal-proximity
  proposition" 4 times and "proximity proposition" never, "proximity
  certificate" for the payload, "security property" for the name.
- `manifest/pgg_tableau_security_property_relations.v` is not, see F10.
- No third spelling exists in either file. "the proximity number" in the
  relations file names a real and not a proposition, and the file used it
  before this pass.
- The split between "the proximity certificate" and "the ideal-proximity
  proposition" is the sheet's, and no single sentence or docstring mixes them
  for one object. Line 91, "Every proximity certificate satisfies the
  ideal-proximity proposition at two", names two different objects and is
  correct.

### Item 4, the defining docstrings

Each was read against its declaration. `SecurityEvidence`, `SecurityProperty`,
`evidence_property`, `ab_evidence`, `ab_security_property`, the three
`_propertyE` lemmas, `publish_propertyE` and `conclude_propertyE` each state
what the object is in one declarative sentence and then what a reader of a
published program learns from it. No meta, no history, no proof strategy, no
plan token. `EvidenceProp` needs F9, `evidence_conclude` needs F4, `conclude`
needs F5, and the index entry for `evidence_conclude` needs F11. The header
paragraph on what a program certifies is accurate: the three propositions it
describes are `ExactProp`, `IndistinguishabilityPropAt` and
`IdealProximityPropAt`, and the epsilon it attributes to the
input-indistinguishability bound is `cert_eps cert = sw_bound_eps (ic_b cert) +
sw_bound_eps (ic_b cert)`, which is the certificate's marginal-bound epsilon
twice as the paragraph says.

### Item 7, layout

- No line of the five files exceeds 80 bytes. The three over-length lines in
  `manifest/pgg_tableau_syntax.v`, at 333, 371 and 402, are `Notation` code and
  predate the pass.
- Every boxed line the pass wrote is exactly 80 bytes with a space before the
  closing delimiter. The one 79-byte boxed line, `manifest/pgg_analysis_manifest.v:618`, predates the pass and was not a site.
- The index of `manifest/pgg_tableau.v` keeps its `==` column at byte 29 and
  its continuation column at byte 32 through all nineteen rewritten entries,
  including those that grew a continuation line, and the one rewritten entry
  of the relations file keeps both columns as well.
- Banners are one content line each.
- Orphan lines: F1, F2, F14, F15.

## Replacement text

### F1, `manifest/pgg_tableau.v:1009`

```
(* Which security property a published program carries, at one real field and
   one index of its family. It reads ab_security_property past the publish
   statement, and publish_propertyE is why the publish statement does not
   change the answer. *)
```

### F2, `manifest/pgg_tableau.v:1060`

```
(* Concluding a program at a chosen number leaves its security property where
   the certify statement put it. The terminal moves a real and not the
   alternative the program committed to, so a program at the constant a paper
   cites states the same kind of fact about a coalition as the program at its
   own bound. *)
```

### F3, `manifest/pgg_tableau.v:866-869`, last sentence of `ConcludePayload`

```
   concluding a program leaves it untouched. An upper bound is the right
   obligation because the two propositions that mention a number are monotone
   in it; a security property whose proposition is not monotone in that number
   needs a different obligation here. *)
```

"mention" rather than "carry" for the propositions is the sheet's verb for a
proposition and a number, and it is what the definitions do:
`IndistinguishabilityPropAt cert c` has `c` free in `var_dist ... <= c`.

### F4, `manifest/pgg_tableau.v:881-887`, docstring of `evidence_conclude`

```
(* The proposition the evidence proves at the program's own bound, and a proof
   that a chosen number is at least that bound, give that proposition at the
   chosen number. The step is sound because the propositions that mention a
   number are monotone in it, which is the condition any future security
   property whose proposition mentions a number must satisfy as well; it is
   what lets a program state the constant a paper cites while asserting about
   the coalition no more than the certificate proved. *)
```

### F5, `manifest/pgg_tableau.v:908-912`, docstring of `conclude`

```
(* The terminal concluding a program at a chosen number, against a proof that
   the number is at least the program's accumulated bound. Post-processing of
   the published constant rather than a step: the data and the security
   property are unchanged, only the real the input-indistinguishability and
   the ideal-proximity propositions mention moves, and it moves only upward. *)
```

This adds no claim that the code does not carry. `ConcludePayload` obliges
`cert_eps cert <= odflt (cert_eps cert) (c R)` in the second branch and
`ipc_eps cert <= odflt (ipc_eps cert) (c R)` in the third, `EvidenceProp`
states the two propositions at `odflt (cert_eps cert) (c R)` and at
`odflt (ipc_eps cert) (c R)`, and the first branch of both is `unit` and
`ExactProp w`, which mention no number.

### F9, `manifest/pgg_tableau.v:539-544`, docstring of `EvidenceProp`

```
(* The proposition the evidence proves at a given coordinate: independence for
   an exact-independence witness, the variation bound at the named number for
   an input-indistinguishability certificate, the distance to the ideal
   model's product law at the named number for a proximity certificate. The
   constructor selects the proposition, so a program cannot state one
   property's claim about another's witness. *)
```

### F16, `manifest/pgg_analysis_manifest.v:17-21`

```
(* A path records no security property. Which one a published program         *)
(* carries is read off that program by security_property_of of                *)
(* manifest/pgg_tableau.v, so which property a program on a path certifies is *)
(* told from the certificate its table names and not from a field of the      *)
(* record.                                                                    *)
```

Five boxed lines instead of four, each 80 bytes. The claim is the parent's:
the property is read from the certificate the path's table names and from no
field of the record.

## Coverage

- 142 sites in the group, that is 118 of the first noun and 24 of the second,
  distributed 114, 17, 5, 4, 2 over the five files. All 142 were read with OLD
  and NEW side by side, from `git diff -U2 77a2c84 -- <file>` for each of the
  five files, cross-read against the 82 numbered OLD/NEW pairs of
  `notes/probes/2026-09-20-security-property-rename/prose_framework.md`. A
  word-boundary count of both nouns over the parent version of each file,
  `git show 77a2c84:<file>`, gives 92 and 22, 17 and 0, 3 and 2, 4 and 0, 2
  and 0, which is the dispatch's 114, 17, 5, 4, 2 and the agent's per-file
  table exactly.
- Declarations opened in the source, not only in diff context: `ExactWitness`,
  `IndistinguishabilityCert`, `IdealProximityCert`, `SecurityEvidence`,
  `SecurityProperty`, `evidence_property`, `IndistinguishabilityPropAt`,
  `cert_eps`, `IdealProximityPropAt`, `ConcludedBound`, `EvidenceProp`,
  `BridgedProp`, `ConcludePayload`, `evidence_conclude`, `conclude`, `StackAt`,
  `ab_evidence`, `ExactProp`, `security_property_of`, `mk_indistinguishability`,
  `var_dist_fdistmap_pair`,
  `idealproximity_prop_at2`, `indistinguishability_prop_cert_free`,
  `idealproximity_reading_le`, and the two instance lemmas that apply
  `var_dist_fdistmap_pair`. For every remaining site the declaration's head,
  its name, its binders and its type, was in the two lines of diff context
  under the docstring.
- Scans run over all five files: word-boundary count of both barred nouns,
  zero in each file, confirming the agent's final table. Every occurrence of
  "property" and "properties". Every occurrence of "proximity". Byte length of
  every line. Width of every boxed line. And a subject-verb scan over
  certificate, witness, evidence, property, path, program and proposition, on
  each line joined with its successor, which produced the item 3 list.
- Not audited, by dispatch: that the code tokens are unchanged, that no barred
  noun remains, and that no line exceeds 80 bytes. The last two were re-run
  here anyway and agree.
