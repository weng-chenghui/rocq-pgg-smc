# Fix pass: the accepted findings of the two audits applied

Comments-only pass over the working tree on top of 77a2c84. Nothing compiled,
no Rocq process started, no git command that writes, nothing deleted under
`notes/probes/`. `[N1]` is the three-letter barred noun and `[N2]` is the
second one wherever old text is quoted.

24 tracked `.v` files changed; all 24 are comment-stripped token-identical to
77a2c84. 45 edits landed. Three findings were amended in application and are
listed under "Applied with a deviation".

## Framework group (`audit-prose-framework.md`)

### F1 — `manifest/pgg_tableau.v`, docstring of `security_property_of`

OLD (lines 1009-1012, the orphan is line 1011)

```
(* Which security property a published program carries, at one real field and
   one index of its family. It reads ab_security_property past the publish
   statement, and
   publish_propertyE is why the publish statement does not change the answer. *)
```

NEW

```
(* Which security property a published program carries, at one real field and
   one index of its family. It reads ab_security_property past the publish
   statement, and publish_propertyE is why the publish statement does not
   change the answer. *)
```

Declaration fact: `Definition security_property_of (c : ConcludedBound)
(r : PublishedAt c) (R : realType) (idx : ...)`. Layout only; the claim is
unchanged.

### F2 — `manifest/pgg_tableau.v`, docstring of `conclude_propertyE`

OLD (the orphan is `   alternative the`, 18 bytes)

```
(* Concluding a program at a chosen number leaves its security property where
   the certify statement put it. The terminal moves a real and not the
   alternative the
   program committed to, so a program at the constant a paper cites states the
   same kind of fact about a coalition as the program at its own bound. *)
```

NEW

```
(* Concluding a program at a chosen number leaves its security property where
   the certify statement put it. The terminal moves a real and not the
   alternative the program committed to, so a program at the constant a paper
   cites states the same kind of fact about a coalition as the program at its
   own bound. *)
```

Declaration fact: `conclude_propertyE` equates `ab_security_property` before
and after the terminal. Layout only.

### F8 and F3 — `manifest/pgg_tableau.v`, docstring of `ConcludePayload`

Both findings sit in one paragraph, so it was rewritten and re-flowed once.

OLD

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

NEW

```
(* The obligation of conclude: at every real field and index, the number the
   program is concluded at is at least the certificate's own, and nothing for an
   exact-independence witness. A program may therefore publish the constant a
   paper cites whenever that constant is an upper bound of the distance the
   program proved, and may not publish a number below the one its certificate
   proved. An exact-independence witness carries no number, so concluding a
   program leaves it untouched. An upper bound is the right obligation because
   the two propositions that mention a number are monotone in it; a security
   property whose proposition is not monotone in that number needs a different
   obligation here. *)
```

Declaration fact, read at `manifest/pgg_tableau.v:869-877`:

```
Definition ConcludePayload (c : ConcludedBound)
    (q : StackAt AnalysisBridged) : Type :=
  forall (R : realType) (idx : amf_index (ab_f q) R),
    match ab_evidence q R idx with
    | ExactIndependence _ => unit
    | InputIndistinguishability cert =>
        cert_eps cert <= odflt (cert_eps cert) (c R)
    | IdealProximity cert => ipc_eps cert <= odflt (ipc_eps cert) (c R)
    end.
```

The obligation is about the number the concluding program is taken to, which
must dominate the certificate's own, so the program is the thing concluded. A
security property is a constructor of `Variant SecurityProperty` and holds no
number; the number is free in the proposition, so the propositions mention it.

### F4 — `manifest/pgg_tableau.v`, docstring of `evidence_conclude`

OLD

```
   chosen number. The step is sound because the propositions that carry a
   number are monotone in it, which is the condition any future security
   property carrying a number must satisfy as well; it is what lets a program
   state the constant a paper cites while asserting about the coalition no
   more than the certificate proved. *)
```

NEW

```
   chosen number. The step is sound because the propositions that mention a
   number are monotone in it, which is the condition any future security
   property whose proposition mentions a number must satisfy as well; it is what
   lets a program state the constant a paper cites while asserting about the
   coalition no more than the certificate proved. *)
```

Declaration fact: the same two `ConcludePayload` branches above, and
`EvidenceProp` puts the number inside the proposition, not inside the property.

### F5 — `manifest/pgg_tableau.v`, docstring of `conclude`

OLD

```
   the published constant rather than a step: the data and the security
   property are unchanged, only the real the input-indistinguishability
   proposition mentions moves, and it moves only upward. *)
```

NEW

```
   the published constant rather than a step: the data and the security property
   are unchanged, only the real the input-indistinguishability and the
   ideal-proximity propositions mention moves, and it moves only upward. *)
```

Declaration fact, both branches read before writing, as the ruling asks.
`ConcludePayload` (quoted above) obliges `cert_eps cert <= odflt (cert_eps
cert) (c R)` in the input-indistinguishability branch and `ipc_eps cert <=
odflt (ipc_eps cert) (c R)` in the ideal-proximity branch. `EvidenceProp`
(`manifest/pgg_tableau.v:545-554`) reads

```
  match p with
  | ExactIndependence w => ExactProp w
  | InputIndistinguishability cert =>
      IndistinguishabilityPropAt cert (odflt (cert_eps cert) (c R))
  | IdealProximity cert =>
      IdealProximityPropAt cert (odflt (ipc_eps cert) (c R))
  end.
```

Two of the three branches carry a number and both numbers move under the same
obligation, so the old "only ... the input-indistinguishability proposition"
excluded a real that does move. The first branch is `unit` and `ExactProp w`
and mentions no number, so "the data and the security property are unchanged"
still holds.

### F6 — `manifest/pgg_tableau.v`, docstring of `IndistinguishabilityPropAt`

OLD: `... the constant a paper cites among them, without reproving it. *)`
NEW: `... paper cites among them, without reproving the proposition. *)`
(paragraph re-flowed from its second line).

Declaration fact: `IndistinguishabilityPropAt ... (cert : ...) (c : R) : Prop
:= forall C x x', ... var_dist ... <= c`. What conclude does not reprove is
this proposition; the nearest noun phrases to the old "it" were the constant,
the sum and a finished program, none of which is reproved.

### F9 — `manifest/pgg_tableau.v`, docstring of `EvidenceProp`

OLD: `independence for / a witness, the variation bound at the named number ...`
NEW: `independence for / an exact-independence witness, the variation bound ...`
(paragraph re-flowed).

Declaration fact: the match above. The branch binds `w : ExactWitness`, and the
file has a second witness in scope, `ipc_witness cert`, so the bare "a witness"
was ambiguous where the other two branches name their payload type.

### F11 — `manifest/pgg_tableau.v`, index entry for `evidence_conclude`

OLD

```
(*   evidence_conclude      == the evidence's proposition at a number above   *)
(*                             its own bound                                  *)
```

NEW

```
(*   evidence_conclude      == the proposition the evidence proves, at a      *)
(*                             number above its own bound                     *)
```

Declaration fact: the lemma's own docstring and lines 88, 252, 273, 538, 558,
880 and 1002 all say "the proposition the evidence proves". The `==` column at
byte 29 and the continuation column at byte 32 are kept; both lines are 80
bytes. Line 77 of the header was left as it stands, which is what the finding
asks.

### F15 — `manifest/pgg_tableau.v`, docstring of `indistinguishability_tail`

The last line was `   used. *)` alone. Re-flowed to four lines ending
`... and the only place the mixing bound is used. *)`. Text unchanged.

### F17 — `manifest/pgg_tableau.v`, three index entries

OLD

```
(*                          == the exact statement's security property is     *)
(*                             exact independence                             *)
...
(*                          == that statement's security property is input    *)
(*                             indistinguishability                           *)
...
(*                          == the proximity statement's security property    *)
(*                             is ideal proximity                             *)
```

NEW

```
(*                          == a program built by the exact statement carries *)
(*                             exact independence                             *)
...
(*                          == a program built by that statement carries      *)
(*                             input indistinguishability                     *)
...
(*                          == a program built by the proximity statement     *)
(*                             carries ideal proximity                        *)
```

Declaration fact: the equations are `ab_security_property (tableau_at
(@certify_exact x q p)) R idx = ExactIndependenceProperty` and its two
siblings, whose subject is the program, and the docstring at line 1023 already
says "A program built by the exact statement carries exact independence at
every real field and index of its family". All six lines are 80 bytes with the
columns kept.

### F7 — `manifest/pgg_tableau_security_property_relations.v`,
docstring of `idealproximity_reading_le`

OLD: `... and it / needs no model of one property to be a model of the other.`
NEW: `... and it needs / no model of one proposition to be a model of the other.`

Declaration fact: `Lemma idealproximity_reading_le (cert : IdealProximityCert
sa) (c : R) : IdealProximityPropAt cert c -> forall C, ... var_dist ... <= c`.
A model satisfies a proposition; a property is a constructor and has no models.

### F10 (ruling 3) — one spelling, file-wide

`manifest/pgg_tableau_security_property_relations.v` now says
"the ideal-proximity proposition" at all eleven sites: the five the pass had
already changed and the six it had not, at the header (two paragraphs) and in
the docstrings before `indistinguishability_prop_cert_free` and the two `Fail`
definitions. Grep after the pass: `(?<!ideal-)proximity proposition` returns 0
lines, `ideal-proximity proposition` returns 10 flattened matches plus the
index entry. "the proximity certificate" and "the proximity number" are
untouched, and "the proximity conclusion" at the header's not-claimed paragraph
is untouched, since it names neither.

### F14 — same file, reflow

The paragraph at 112-122 was re-flowed whole while F10 changed two of its
sentences. Its one remaining short middle line is forced: the following token
is `input-indistinguishability`, 26 bytes.

### F16 — `manifest/pgg_analysis_manifest.v` header

OLD (four boxed lines)

```
(* A path records no security property. Which one a published program         *)
(* carries is read off that program by security_property_of of                *)
(* manifest/pgg_tableau.v, so which property a path carries is told from the  *)
(* certificate its table names and not from a field of the record.            *)
```

NEW (five boxed lines, each 80 bytes)

```
(* A path records no security property. Which one a published program carries *)
(* is read off that program by security_property_of of                        *)
(* manifest/pgg_tableau.v, so which property a program on a path certifies is *)
(* told from the certificate its table names and not from a field of the      *)
(* record.                                                                    *)
```

Declaration fact: a path is an `AnalysisPath` record with no security-property
field, and `security_property_of` takes a `PublishedAt`, so the carrier of a
property is the program, not the path.

### F12, F13 — no change, per the ruling.

## Instance groups (`audit-prose-instances.md`)

### H1 — `instances/pgl27/pgl27_word_privacy.v`, docstring of
`pgl27_word_marginal_bound`

OLD

```
    word, and it is the number a word program's input-indistinguishability
    certificate carries. *)
```

NEW

```
    word, and it is the epsilon of the marginal bound a word program's
    input-indistinguishability certificate carries, half the 2^-39 such a
    program publishes. *)
```

Declaration fact: `Definition pgl27_word_marginal_bound : ShuffleMarginalBound
R pgl27_M := @MkShuffleMarginalBound R pgl27_M 200 (2%:R^-40) rho_word
(@pgl27_endpoint_mixing R)`, so 2^-40 is this record's epsilon, while
`cert_eps cert = sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert)`
(`manifest/pgg_tableau.v`) makes the certificate's own number 2^-39. The
sentence now names which of the two it is and states the other, matching the
five-card sibling at `five_card_tableau_analysis_bridged.v`.

### H2 — the two analysis-bridged openings

kim and pgl27, OLD: `The AnalysisBridged level adjoins one piece of security
evidence to a / Sampled value, and the proposition it carries is the one that
evidence / proves, ...`

NEW, both files byte-identical over the changed lines:

```
(* The AnalysisBridged level adjoins security evidence to a Sampled value at  *)
(* every real field and index, and the proposition it carries is the one that *)
(* evidence proves, ...
```

Declaration fact: `BridgedProp` quantifies the evidence, `forall (R : realType)
(idx : amf_index (ab_f q) R), EvidenceProp c (ab_evidence q R idx)`, and
`StackAt AnalysisBridged` holds `forall R idx, SecurityEvidence (amf_sample f R
idx)`, so the level adjoins one value at every real field and index and not one
value in total. Both paragraphs were re-flowed to their end.

### H3 — `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` header,
as amended

OLD

```
(* number. The input-indistinguishability certificate crosses from the walk   *)
(* to the ideal cut once for each of the two dealt secrets it compares, so    *)
(* its cert_eps is that number added to itself, 2^-39. The proximity          *)
(* certificate compares one law with one law and carries the number itself,   *)
(* 2^-40, and the proximity program concludes at 2^-39, ...
```

NEW

```
(* number. The input-indistinguishability tail makes two hops from the walk   *)
(* to the ideal cut, one for each of the two dealt secrets the proposition    *)
(* compares, so cert_eps is that number added to itself, 2^-39. The           *)
(* ideal-proximity proposition compares one law with one law, and the         *)
(* certificate carries the number itself, 2^-40, and the proximity program    *)
(* concludes at 2^-39, ...
```

Every other clause of the sentence is kept and the paragraph was re-flowed to
its end at "pgl27_exact_leak4 records that four already leak."

Declaration fact, both lemmas read before writing:
`indistinguishability_tail` applies the transfer inequality through `ic_ideal`
once per run argument, which is two hops for the two dealt secrets, and
`cert_eps` is the marginal bound's epsilon added to itself.
`idealproximity_tail` (`manifest/pgg_tableau.v:782-795`) rewrites the ideal
joint law into a product with `inde_dist_of_RV2 (@ew_indep _ _ _ _
(ipc_witness cert) C HC)` and then closes with `exact: (@ipc_close _ _ _ _ cert
C HC)`: it adds no hop of its own, and `ipc_close` is one `var_dist ... <= eps`
comparison. The tree's word "hop" is used throughout.

### H4 — the eight `_propertyE` docstring openers

All eight now open `The security property this program carries, at every real
field and index, is <property>: ...`, except pgl27's proximity lemma, which
keeps its own quantifier word and reads `... at every real field and prior, is
ideal proximity: ...`.

| file | line region | property |
|---|---|---|
| kim AB | uniform | exact independence (already in this form) |
| kim AB | repeated certified | input indistinguishability |
| kim AB | proximity | ideal proximity |
| pgl27 AB | exact | exact independence |
| pgl27 AB | proximity | ideal proximity (`prior`) |
| psl211 AB | all-decks | exact independence |
| psl211 AB | word proximity | ideal proximity |
| s5 AB | randomized | exact independence |

Declaration fact: all eight are the one lemma shape
`security_property_of <program> R idx = <Property>`, so the subject of the
sentence is the program the lemma names and "this program" is unambiguous at
each site.

### H5 — the four-conjuncts docstring, kim and pgl27

OLD (both): `the whole content of exact independence at this instance`
NEW (both): `the whole content of the exact-independence proposition at this
instance`

Declaration fact: the four conjuncts are `ExactProp` instantiated, and the
banner three lines above already reads "The exact-independence proposition's
four conjuncts at this instance". psl211 keeps "here" and s5 keeps "at this
instance", which the audit found accurate.

### H6a — `instances/pgl27/pgl27_proximity.v` header, as amended

OLD

```
(* The other distance runs the other way. A proximity certificate compares    *)
(* two models at one index, so the two have to be read at one law of the      *)
(* dealt secret. ...
```

NEW

```
(* The other distance runs the other way. A proximity certificate holds its   *)
(* ideal at the same index as the model it is about, so the two have to be    *)
(* read at one law of the dealt secret. ...
```

**What "index" is there, as the ruling asks.** It is the analysis-model-family
index, the `idx` of `amf_index (ab_f q) R`. The very next sentence of the same
header fixes the reading: `pgl27_prior_exact_family of pgl27_models.v carries
that law as its index, where pgl27_exact_family is indexed by the unit type`.
So at this site "index" ranges over a family's index type, which for one family
is a law of the dealt secret and for the other the unit type.

Declaration fact: `ipc_ideal : SampleAdapter R (instance_exec E)` and
`ipc_witness : ExactWitness ipc_ideal`, over the same `instance_exec E` and the
same real field as the model the certificate is about, which is `amf_sample f R
idx` at the coordinate where `ab_evidence q R idx` sits. The ideal is therefore
held at the coordinate of the model, which is what the amended sentence says.
The old "compares two models" attributed the comparison to the record; the
comparison is `IdealProximityPropAt`.

### H6b — `instances/psl211/tableau/psl211_tableau_analysis_bridged.v`,
docstring of `psl211_word_proximity_cert_secretE`

OLD: `A proximity certificate whose two / secrets differ compares a coalition's
reading against a product taken in / a different bit, so ...`

NEW: `Where a certificate's two secrets differ, / the ideal-proximity
proposition compares a coalition's reading against a / product taken in a
different bit, so ...`

Declaration fact: `IdealProximityPropAt` mentions `ipc_secret cert` on the left
and `ew_secret (ipc_witness cert)` on the right; the certificate holds the two
secrets and the proposition compares.

### H6c — both proximity-program docstrings, as amended

kim OLD

```
    are independent outright. The certificate hops to the ideal once and so
    loses that number once, where the input-indistinguishability program hops
    twice. Its transfer status is IdealFinite, ...
```

kim NEW

```
    are independent outright. The proximity certificate's closeness field is one
    hop to the ideal, so that number is lost once, where the
    input-indistinguishability tail makes two hops. Its transfer status is
    IdealFinite, the same the input-indistinguishability program carries, and
    the two certificates compare against the same ideal cut. *)
```

pgl27 NEW, same sentence:

```
    marginals. The proximity certificate's closeness field is one hop to the
    ideal, so that number is lost once, where the input-indistinguishability
    tail makes two hops. Its transfer status is IdealFinite, ...
```

Declaration fact: as at H3. The one hop on the proximity side is `ipc_close`, a
single `var_dist ... <= ipc_eps cert` field; `idealproximity_tail` transports
it and adds none. The five-card twin at the certificate section already says
"the comparison through the ideal cut is a two-hop hybrid, one hop for each of
the two committed pairs, and each hop loses that number", so the word and the
counts now agree across the header of the PGL(2,7) file, the two docstrings and
the five-card twin.

### H6d — `instances/psl211/tableau/psl211_tableau_checks.v`

Header OLD: `The third is / which ideal a proximity certificate admits.`
Header NEW: `The third is / which ideal the proximity certificate's type
admits.` (paragraph re-flowed to its end).

Banner OLD: `(*     Which ideal a proximity certificate refuses ...`
Banner NEW: `(*     Which ideal the certificate's type refuses ...` (80 bytes).

Declaration fact: the file's own body says it, "A certificate's ideal is a
sample adapter over the program's own execution, and the two instances run
different executions, so the field is rejected at its type". What admits or
refuses is the type.

Banner-reference check for the renamed banner: `grep -rn` over `instances`,
`manifest`, `security` and `protocol` for the old text returns 0 lines, so no
"under <banner>" reference quoted it.

### H6e — `instances/psl211/psl211_reading_constancy.v`,
docstring of `coalition_reading_constancy`

OLD: `This is what an input-indistinguishability certificate asserts about its
/ idealized cut, and the certificate's variation-distance field is what /
transfers that assertion from the ideal to the real cut.`

NEW: `This is what an input-indistinguishability certificate's constancy field
/ states about its idealized cut, and the certificate's variation-distance /
field is what transfers that statement from the ideal to the real cut.`

Declaration fact: `ic_const` states the constancy and `ic_close` holds the
distance; a certificate holds both fields.

### H6f and H8 — the three `*_proximity.v` files

`instances/psl211/psl211_word_proximity.v`, header OLD: `it carries the bound
this instance's proximity certificate takes as its / distance field`.
NEW: `it carries the bound this instance's proximity certificate holds in its /
closeness field`.

Same file, docstring OLD: `It is the distance field of this instance's
proximity certificate`. NEW: `It is the closeness field of this instance's
proximity certificate`.

Declaration fact: the field is `ipc_close`, which the certificate holds; "takes"
is the certify statement's verb in the sheet.

### H7 and H18 — the psl211 and s5 openings

OLD (both): `the proposition it carries is the proposition / that payload
proves, ... and the / security property decides what it says: ...`

NEW (both): `the proposition it carries is the one that / payload proves, ...
and which / security property the evidence proves is what it says: ...`

Declaration fact: the clause now reads as the kim and pgl27 twins do, and what
selects the claim is the constructor of `SecurityEvidence`, as
`manifest/pgg_tableau.v` states at `evidence_property`. See the deviation note
on H18 below.

### H9 — `instances/pgl27/tableau/pgl27_tableau_checks.v`

Header OLD: `the / security property a program carries is the one its certify
statement / wrote`.
Header NEW: `the / security property a program carries is the one the certify
statement that / wrote its evidence fixes` (paragraph re-flowed to its end).

Docstring OLD: `so the program carries the security property its certify
statement wrote and / no other.`
Docstring NEW: `so the program carries the security property its certify
statement fixed and / no other.`

Declaration fact: a certify statement writes evidence and the property is read
off it, which `manifest/pgg_tableau.v` states as "a program's security property
is fixed by the certify statement that wrote the evidence".

### H10 — kim AB, docstring of `five_card_biased_proximity_prop_holds`

OLD: `It is the / ideal-proximity conclusion standing on its own at this
instance.`
NEW: `It is the / proximity conclusion standing on its own at this instance.`

Declaration fact: the banner two lines above says "The proximity proposition at
this instance, and what implies it", so the short form is this docstring's own
word and the ruling keeps it here.

### H11 — the witness docstring close, kim and pgl27

OLD (both): `and the / witness is therefore all that certifying exact
independence requires of this / instance.`
NEW (both): `so the / witness is all that certifying exact independence
requires of this / instance.`

This restores the four-way twin: all four files now carry the same clause.

### H12, H13, H15 — layout

kim AB: the proximity-program paragraph was re-flowed to its end as part of
H6c, which removes the 59-byte line. pgl27 AB: the docstring of
`pgl27_word_proximity_le39` was re-flowed, which removes the 69-byte line. kim
AB index entry: re-flowed so the banner name begins a line,

```
(*     five_card_uniform_published_propertyE, and, under                      *)
(*     The exact-independence proposition's four conjuncts at this instance,  *)
(*     the reading five_card_exact_view_secrecy.                              *)
```

The banner text is quoted unchanged.

### H14 — `instances/pgl27/tableau/pgl27_tableau_checks.v`, three lines

OLD

```
(* free before it elaborates a body, so a file holding the lemma first would  *)
(* reject the term for an occupied name and not for the security property the *)
(* term asserts.                                                              *)
```

NEW

```
(* free before it elaborates a body, so a file holding the                    *)
(* lemma first would reject the term for an occupied name                     *)
(* and not for the security property the term asserts.                        *)
```

See the deviation note below: a greedy rewrap of this paragraph is a no-op.

### H16 — `instances/psl211/psl211_models.v`, docstring of
`psl211_fixed_deal_view_dep`

OLD: `privacy is a property of the dealer law and not of the / protocol alone`
NEW: `privacy depends on the dealer law and not on the protocol alone`
(docstring re-flowed whole, its two double spaces after a sentence preserved,
its em-dash preserved).

Declaration fact: the lemma refutes independence under one dealer law while the
shuffle group, the design and the coalition are unchanged, which is a
dependence claim and not a use of the framework's `SecurityProperty`. This was
the only ordinary-English "property" left in the instance files.

### H17 — six index entries

kim AB: `== the one-cut path as a program certifying that / same property`
becomes `== the one-cut path as a program certifying / input
indistinguishability`; the three entries reading `property is the same` become
`property is input indistinguishability`.

pgl27 AB: `== the concluded program's security property is / the same` becomes
`... is / input indistinguishability`, and `== the branch program's security
property is the / same as well` becomes `== the branch program's security
property is / input indistinguishability as well`.

Declaration fact: each of the six lemmas equates `security_property_of` of its
program with `InputIndistinguishabilityProperty`. All twelve lines are 80 bytes
and keep the `==` column and the continuation column.

### H19 — kim AB, docstring of
`five_card_biased_published_inv25_propertyE`

OLD: `It carries the / exact certificate where
five_card_biased_indistinguishability_published / carries the spectral one`.
NEW: `It carries the / certificate at the exact one-cut distance where
five_card_biased_indistinguishability_published carries the spectral one`.

Declaration fact: the certificate is `kim_biased_cert_exact`, the one-cut
program's certificate at the exact number one fiftieth, where "exact" elsewhere
in the file means exact independence.

### H20 — kim AB banner

OLD: `(*     The number each certificate publishes ...`
NEW: `(*     The number each certificate carries ...` (80 bytes).

A program publishes and a certificate carries. `grep -rn` for the old text over
`instances`, `manifest`, `security` and `protocol` returns 0 lines, so no
header "under <banner>" reference quoted it.

### H21 — psl211 AB

OLD: `published at 2^-40, the / number the certificate proves`
NEW: `published at 2^-40, the / number the certificate carries`
(one word, the line stays under 80 bytes, no reflow needed).

### H22 — kept, per the ruling. No change.

### H23 — kim AB header

OLD: `the ideal it / names here is the uniform model itself, whose own privacy
is the / exact-independence theorem.`
NEW: `... whose own privacy is / five_card_exact_view_secrecy.`

Declaration fact: the theorem is `five_card_exact_view_secrecy`, and
"the exact-independence theorem" names no declaration in the tree.

### H24 — kim AB header

OLD: `The map / and the five link lemmas the exact-independence witness rests
on are not / there but here`
NEW: `The map / and the five link lemmas five_card_exact_witness is built from
are not / there but here`

Declaration fact: `ExactWitness` has one field, so a reader could take the map
and the five lemmas for fields of the witness; they are what
`five_card_exact_witness` is built from.

### R2 — `instances/psl211/psl211_exec.v` was not opened and not edited.

## Applied with a deviation

1. **H9, second site.** The auditor's replacement is `so the program carries
   the security property that statement fixed and no other`. Inside that
   docstring "that statement" has no antecedent: the docstring's only other
   noun phrases are the word program and exact independence, and the certify
   statement is named only in the file header, forty lines away. Written as
   `so the program carries the security property its certify statement fixed
   and no other`, which keeps the accepted verb "fixed" and the possessive the
   current text already carries. The claim is the auditor's.

2. **H14.** A greedy rewrap of the paragraph from its first line reproduces the
   current five lines exactly, so it cannot remove the short final line: the
   text is 309 bytes of content and five boxed lines hold at most 370, four at
   most 296. The finding says "rewrap the three lines from 43", so those three
   were balanced instead, at 55, 54 and 51 bytes of content, which removes the
   13-byte final line. No word changed.

3. **H18.** Its replacement is written conditionally ("if it is ever touched").
   H7 changes the clause two sentences earlier in the same boxed paragraph and
   the paragraph has to be re-flowed to its end, so the site is touched and the
   replacement was applied in both files. Flagging it because the finding is a
   NOTE the auditor explicitly did not charge.

## Findings not applied

- **F12** and **F13**: the ruling says no change.
- **H22**: the ruling says keep.
- **R2**: the frozen site is out of scope and goes to the owner's list.
- Nothing was found to be false of its declaration, so no accepted replacement
  was refused on those grounds.

## Twin greps, after the pass

Run over the four `*_tableau_analysis_bridged.v` and the three `*_proximity.v`,
with the boxed-comment delimiters joined so a sentence that wraps across lines
is still matched.

| phrase | kim | pgl27 | psl211 | s5 |
|---|---|---|---|---|
| `adjoins security evidence to a Sampled value at every real field and index, and the proposition it carries is the one that evidence proves` | 1 | 1 | 0 | 0 |
| `adjoins one security payload per real field and per index of the model, and the proposition it carries is the one that payload proves` | 0 | 0 | 1 | 1 |
| `and which security property the evidence proves is what it says` | 0 | 0 | 1 | 1 |
| `The security property this program carries, at every real field and (index\|prior), is` | 3 | 2 | 2 | 1 |
| `whole content of the exact-independence proposition at this instance` | 1 | 1 | 0 | 1 |
| `whole content of the exact-independence proposition here` | 0 | 0 | 1 | 0 |
| `witness is all that certifying exact independence requires of this instance` | 1 | 1 | 1 | 1 |
| `The proximity certificate's closeness field is one hop to the ideal, so that number is lost once, where the input-indistinguishability tail makes two hops` | 1 | 1 | 0 | 0 |
| `The input-indistinguishability tail makes two hops` | 0 | 1 | 0 | 0 |

The first two rows are the deliberate split the audit's twin table allows: kim
and pgl27 count the evidence at every coordinate, psl211 and s5 say the same
thing with "payload", which is the word their own files use throughout. The
`_propertyE` opener totals 8, which is the eight lemmas of H4. The
four-conjuncts docstring totals 4, with psl211 keeping "here". The witness
close is now four-way identical. The hop sentence appears once in each file
that has a proximity program.

| file | `closeness field` | `distance field` |
|---|---|---|
| `instances/kim2025/five_card_proximity.v` | 2 | 0 |
| `instances/pgl27/pgl27_proximity.v` | 2 | 2 |
| `instances/psl211/psl211_word_proximity.v` | 2 | 0 |

The two remaining `distance field` in the PGL(2,7) file are at the index entry
for `pgl27_word_uniform_ideal_close_false` and at that lemma's own docstring,
which are refutation sites the pass never touched and no accepted finding
names. A third sits in `instances/psl211/tableau/psl211_tableau_checks.v`.
All three were closed by the follow-up below, which retires the second name
for `ipc_close`.

## The three finishing checks

**(a) Comment-stripped token identity against 77a2c84.** A nested-comment
stripper that also skips string literals was run over every file `git diff
--name-only 77a2c84` reports, then the result was whitespace-tokenised and
compared. 24 `.v` files, all identical, 0 differing:

```
instances/kim2025/five_card_proximity.v                          364 tokens
instances/kim2025/tableau/five_card_tableau_analysis_bridged.v  2161
instances/kim2025/tableau/five_card_tableau_checks.v             431
instances/kim2025/tableau/five_card_tableau_sampled.v            408
instances/pgl27/pgl27_proximity.v                                706
instances/pgl27/pgl27_word_privacy.v                             945
instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v        2038
instances/pgl27/tableau/pgl27_tableau_checks.v                   479
instances/pgl27/tableau/pgl27_tableau_sampled.v                  117
instances/psl211/psl211_analysis.v                               407
instances/psl211/psl211_models.v                                3303
instances/psl211/psl211_reading_constancy.v                     3023
instances/psl211/psl211_word_model.v                             261
instances/psl211/psl211_word_proximity.v                         272
instances/psl211/tableau/psl211_tableau_analysis_bridged.v       725
instances/psl211/tableau/psl211_tableau_checks.v                 251
instances/psl211/tableau/psl211_tableau_sampled.v                133
instances/s5/tableau/s5_tableau_analysis_bridged.v               471
instances/s5/tableau/s5_tableau_sampled.v                         93
manifest/pgg_analysis_manifest.v                                4816
manifest/pgg_tableau.v                                          3459
manifest/pgg_tableau_security_property_relations.v               492
manifest/pgg_tableau_syntax.v                                   1080
security/var_dist_joint_law.v                                    466
```

The 25th path the diff reports is
`notes/2026-09-20-221500-p8-landing-plan.md`, not a `.v` file and not touched
by this pass.

**(b) Barred nouns in the comments of tracked `.v`.** Every tracked `.v`
outside `notes/`, `legacy/` and the frozen closure
(`instances/psl211/psl211_endpoints.v`, `instances/psl211/psl211_exec.v`) was
masked down to its comment text and scanned, case-insensitively and at word
boundaries, for both nouns and their plurals.

**Zero occurrences of either noun.** The main session's own scan agrees and is
the record here: neither noun survives anywhere in the scanned comments.

**(c) Changed lines over 80 bytes.** Over the added side of `git diff -U0
77a2c84`, three lines exceed 80 bytes and all three are in
`notes/2026-09-20-221500-p8-landing-plan.md`, at 82, 81 and 81 bytes. **No
added line in any `.v` file exceeds 80 bytes.** A separate scan of every added
boxed line, meaning one that opens `(*` and closes ` *)`, found 0 that are not
exactly 80 bytes with a space before the closing delimiter.

## Follow-up: one word per concept for `ipc_close`

The main session accepted the three deviations (H9, H14, H18) and retired the
second name for the record field `ipc_close`: it is "the closeness field"
everywhere. The three residues listed above were read before being changed and
all three name `ipc_close`, so all three were changed. Comments only, as
before, nothing compiled and no git command that writes.

### 1. `instances/pgl27/pgl27_proximity.v`, index entry of
`pgl27_word_uniform_ideal_close_false`

OLD

```
(*                           == the distance field is false at every          *)
```

NEW

```
(*                           == the closeness field is false at every         *)
```

It names `ipc_close`: the lemma it labels states `~ (var_dist (fdistmap ...)
(fdistmap ...) <= ...)` at the coalition it quantifies, which is the negation
of the `ipc_close` shape. 80 bytes, `==` column and continuation column kept.
The three continuation lines are untouched: the entry was already at capacity
and the new word is one byte longer, so nothing moves across a line.

### 2. Same file, docstring of `pgl27_word_uniform_ideal_close_false`

OLD

```
(** The distance field of a proximity certificate is false, and not merely
    unwritable, when the ideal is the uniform-secret member of the tree's
    exact family and the actual model is the word walk at the point-mass
    prior. Pushing both joint laws forward along the secret coordinate leaves
    the two priors themselves, one apart, and 2^-40 is below that, so the two
    models are separated by their secrets alone and no reading of the cut can
    bring them together. It says nothing at a prior near the uniform one,
    where the same lower bound is small. It is stated at every coalition and
    not only below four seats, so it refutes more than the field asks. *)
```

NEW

```
(** The closeness field of a proximity certificate is false, and not merely
    unwritable, when the ideal is the uniform-secret member of the tree's exact
    family and the actual model is the word walk at the point-mass prior.
    Pushing both joint laws forward along the secret coordinate leaves the two
    priors themselves, one apart, and 2^-40 is below that, so the two models are
    separated by their secrets alone and no reading of the cut can bring them
    together. It says nothing at a prior near the uniform one, where the same
    lower bound is small. It is stated at every coalition and not only below
    four seats, so it refutes more than the field asks. *)
```

Same field, same lemma. The docstring was re-flowed whole; every claim, number
and quantifier survives, and the bare "the field" of the last sentence still
refers to it. Line widths 75, 79, 73, 78, 80, 77, 77, 76, 58.

### 3. `instances/psl211/tableau/psl211_tableau_checks.v`, header

OLD

```
(* its own model would hold its distance field at zero, the two sides of that *)
(* field being one term.                                                      *)
```

NEW

```
(* its own model would hold its closeness field at zero, the two sides of     *)
(* that field being one term.                                                 *)
```

It names `ipc_close`: the sentence is about a certificate whose ideal is its
own model, where the two laws `ipc_close` compares are one term and the
variation distance of a law from itself is zero. Both lines are 80 bytes with
a space before the closing delimiter. The preceding line of the paragraph is
unchanged, because the reflow starts at the changed line and that line was a
valid break already.

### Checks after the follow-up

- **Token comparison rerun on the two files.**
  `instances/pgl27/pgl27_proximity.v`, 706 vs 706 tokens, identical.
  `instances/psl211/tableau/psl211_tableau_checks.v`, 251 vs 251 tokens,
  identical. The full sweep was rerun as well and still reports 24 `.v` files
  changed and 0 differing.
- **One word per concept.** `distance field` now occurs 0 times in
  `instances/kim2025/five_card_proximity.v`,
  `instances/pgl27/pgl27_proximity.v`,
  `instances/psl211/psl211_word_proximity.v` and
  `instances/psl211/tableau/psl211_tableau_checks.v`; `closeness field` occurs
  2, 4, 2 and 1 times in them.
- **Widths.** No added line in any `.v` file exceeds 80 bytes, and every added
  boxed line is exactly 80 with a space before the closing delimiter. The
  over-80 added lines the sweep reports are all in two `notes/*.md` files that
  this pass never wrote.
