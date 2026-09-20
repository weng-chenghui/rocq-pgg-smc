# Audit: the comments pass at the three instance groups (218 sites)

Read-only adversarial audit of the uncommitted comments-only pass over the
instance groups kim2025, pgl27, psl211 and s5. Working tree on top of 77a2c84.
No repository file was edited except this one, nothing was compiled, no Rocq
process was started. `[N1]` stands for the barred three-letter noun and `[N2]`
for "port" wherever old text is quoted.

## Verdict

**NO-GO as it stands, GO once H1 and H2 are applied.** Both are one-line
edits. Everything else is a SHOULD or a NOTE and none of it blocks a commit.

The pass is accurate at the hard points. Every number survives: one fiftieth,
one twenty-fifth, sqrt 5 over eighty against sqrt 5 over forty, 2^-40 against
2^-39 against 2^-41. Every hop count survives and matches the declarations.
All eleven "under <banner>" references resolve to a banner whose text they
quote exactly, including the four that wrap across lines. The seven cases of
the sheet are applied where they apply, and the case-5 wordings ("before the
certify statement", "certified for ideal proximity", "published with
exact-independence evidence") are used uniformly.

The two MUST items are a number that now reads as two different numbers in one
instance group, and a count of pieces of evidence that the declaration
contradicts.

## Findings

| id | class | file:line | OLD (placeholders) | NEW | problem, with the declaration quoted | replacement |
|----|-------|-----------|--------------------|-----|--------------------------------------|-------------|
| H1 | MUST | instances/pgl27/pgl27_word_privacy.v:88-90 | "2^-40 here bounds the loss of replacing that draw by a finite word, and it is the number a word program's input-indistinguishability [N1] carries." | "... and it is the number a word program's input-indistinguishability certificate carries." | The certificate is `pgl27_word_cert`, and `pgl27_tableau_analysis_bridged.v:352-360` gives its `ic_b` as `pgl27_word_marginal_bound R`, epsilon 2^-40. But `cert_eps cert = sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert)` (manifest/pgg_tableau.v:493-496), so the number the certificate itself carries, in the framework's own sense, is 2^-39. `pgl27_tableau_analysis_bridged.v:877` uses the same phrase for that other value: "The number pgl27_word_cert carries at this model is twice the number pgl27_word_proximity_cert carries". One phrase, two numbers, inside one instance group. The old wording named no record, so the pass created the collision. Kim's sibling keeps the distinction, at five_card_tableau_analysis_bridged.v:594: "the epsilon of the marginal bound the certificate carries and half the number a program built on it publishes". | "and it is the epsilon of the marginal bound a word program's input-indistinguishability certificate carries, half the 2^-39 such a program publishes." |
| H2 | MUST | instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:7-8 and instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:7-8 | "The AnalysisBridged level adjoins one security [N1] to a Sampled value, and the proposition it carries is that [N1]'s own" | "The AnalysisBridged level adjoins one piece of security evidence to a Sampled value, and the proposition it carries is the one that evidence proves" | `BridgedProp` (manifest/pgg_tableau.v:562-566) quantifies the evidence: `forall (R : realType) (idx : amf_index (ab_f q) R), EvidenceProp c (ab_evidence q R idx)`, and `StackAt AnalysisBridged` holds `forall R idx, SecurityEvidence (amf_sample f R idx)`. The level adjoins one value at every real field and index, not one. The old text counted kinds, one of three, and was true. The sheet allows "a piece of evidence" only when a count is needed, and this count is wrong. The psl211 and s5 twins state it correctly: "one security payload per real field and per index of the model". | "The AnalysisBridged level adjoins security evidence to a Sampled value at every real field and index, and the proposition it carries is the one that evidence proves" (repad both boxes to 80 with one space before the closing delimiter) |
| H3 | SHOULD | instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:28-31 against 879-881 | header untouched: "The input-indistinguishability certificate crosses from the walk to the ideal cut once for each of the two dealt secrets it compares, so its cert_eps is that number added to itself, 2^-39. The proximity certificate compares one law with one law and carries the number itself, 2^-40." | body rewritten: "the input-indistinguishability tail loses that bound at each of two hops, one per dealt secret, and the ideal-proximity proposition compares one law with one law" | One file now says one thing twice with different subjects. In the body the tail loses and the proposition compares, which is the sheet's cases 2 and 6. In the header the certificate crosses and compares, which the verb rule reserves for the proposition and the tail lemma (`indistinguishability_tail`, manifest/pgg_tableau.v:758-761, `IdealProximityPropAt`, 514-528). The sheet's rule 3 asks for one word per concept per file. | header: "The input-indistinguishability tail crosses from the walk to the ideal cut once for each of the two dealt secrets the proposition compares, so cert_eps is that number added to itself, 2^-39. The ideal-proximity proposition compares one law with one law, and the certificate carries the number itself, 2^-40." |
| H4 | SHOULD | kim AB:540, 708, 1119, pgl27 AB:447, 956, psl211 AB:194, 370, s5 AB:188 | all eight, one shape: "The [N1] this program carries, at every real field and index: independence of ..." | kim and pgl27: "The security property this program carries, at every real field and index, is exact independence: ..." / "The security property the proximity program carries, at every real field and index, is ideal proximity: ...". psl211 and s5: "The program's security property, at every real field and index, is exact independence: ..." | Two renderings of one docstring shape across four sibling files, with nothing in the instances to justify the split. All eight declarations are the same lemma shape, `security_property_of <program> R idx = <Property>` (manifest/pgg_tableau.v:1013-1017). | adopt one form everywhere. The kim and pgl27 form keeps the old sentence's subject, so it is the cheaper one: "The security property this program carries, at every real field and index, is <property>: ..." |
| H5 | SHOULD | kim AB:560, pgl27 AB:694 against psl211 AB:225, s5 AB:217 | all four: "The four conjuncts are the whole content of the exact [N1] at this instance" (psl211: "here") | kim and pgl27: "the whole content of exact independence at this instance". psl211 and s5: "the whole content of the exact-independence proposition here / at this instance" | The four conjuncts are `ExactProp` instantiated (manifest/pgg_tableau.v:450-470): independence, zero mutual information, unchanged conditional entropy, closure under post-processing. What they are the whole content of is the proposition. A property is a name and has no content, so the kim and pgl27 form puts content on a name. The banner three lines above all four docstrings says "The exact-independence proposition's four conjuncts at this instance". | kim and pgl27: "the whole content of the exact-independence proposition at this instance" |
| H6 | SHOULD | seven sites, listed in the cell | see below | see below | a certificate holds fields and proves a proposition. Comparing, asserting and crossing belong to the proposition and to the tail lemma, admitting and refusing belong to the type, and "takes" is reserved by the sheet for a certify statement taking a payload. Five of the seven are neighbours the agents left alone, two are new text. | per site: |
| H6a | SHOULD | instances/pgl27/pgl27_proximity.v:25 | unchanged | "A proximity certificate compares two models at one index, so the two have to be read at one law of the dealt secret." | the content is a typing fact: `ipc_ideal : SampleAdapter R (instance_exec E)` over the program's own execution (manifest/pgg_tableau.v:230-234), so the ideal is fixed at the model's index. | "A proximity certificate holds an ideal at the same index as the model it is about, so the two have to be read at one law of the dealt secret." |
| H6b | SHOULD | instances/psl211/tableau/psl211_tableau_analysis_bridged.v:292-295 | unchanged apart from the last clause | "A proximity certificate whose two secrets differ compares a coalition's reading against a product taken in a different bit, so what a coalition is shown says nothing about the bit the ideal-proximity proposition names." | the comparison is `IdealProximityPropAt`, which mentions `ipc_secret cert` on the left and `ew_secret (ipc_witness cert)` on the right (manifest/pgg_tableau.v:514-528). The certificate holds the two secrets, the proposition compares. | "Where a certificate's two secrets differ, the ideal-proximity proposition compares a coalition's reading against a product taken in a different bit, so ..." |
| H6c | SHOULD | kim AB:1077-1078 and pgl27 AB:933-934 | unchanged | "The certificate hops to the ideal once and so loses that number once, where the input-indistinguishability program hops twice." | `idealproximity_tail` transports one distance and `indistinguishability_tail` goes through the ideal cut once per run argument (manifest/pgg_tableau.v:758-769, 779-796). The crossing is the tail's, not the record's. | "The ideal-proximity tail crosses to the ideal once and so loses that number once, where the input-indistinguishability tail crosses twice." |
| H6d | SHOULD | instances/psl211/tableau/psl211_tableau_checks.v:19-20 and banner at 90 | "The third is which ideal the proximity [N1] admits." / banner "Which ideal the [N1] refuses" | "The third is which ideal a proximity certificate admits." / banner "Which ideal a proximity certificate refuses" | new text. The file's own body says it correctly at 93-96: "A certificate's ideal is a sample adapter over the program's own execution, and the two instances run different executions, so the field is rejected at its type". What admits or refuses is the type. No header references this banner, so renaming it is safe. | "The third is which ideal the proximity certificate's type admits." / banner "Which ideal the certificate's type refuses" |
| H6e | SHOULD | instances/psl211/psl211_reading_constancy.v:194-196 | unchanged | "This is what an input-indistinguishability certificate asserts about its idealized cut, and the certificate's variation-distance field is what transfers that assertion from the ideal to the real cut." | the record field `ic_const` states the constancy and `ic_close` holds the distance (manifest/pgg_tableau.v:204-215). A certificate holds them. | "This is what an input-indistinguishability certificate's constancy field states about its idealized cut, and the certificate's variation-distance field is what transfers that statement from the ideal to the real cut." |
| H6f | SHOULD | instances/psl211/psl211_word_proximity.v:10-11 | "it carries the bound the proximity [N1] of this instance takes as its distance field" | "it carries the bound this instance's proximity certificate takes as its distance field" | new text. "takes" is the certify statement's verb in the sheet. A certificate holds the bound in `ipc_close`. Fixing this also settles H8. | "it carries the bound this instance's proximity certificate holds in its closeness field" |
| H7 | SHOULD | psl211 AB:8-9 and s5 AB:7-8 | "the proposition it carries is that payload's [N1]" | "the proposition it carries is the proposition that payload proves" | "the proposition ... is the proposition" in one clause, where the kim and pgl27 twins read "the proposition it carries is the one that evidence proves". | "the proposition it carries is the one that payload proves" |
| H8 | SHOULD | instances/psl211/psl211_word_proximity.v:11 and 73 against instances/kim2025/five_card_proximity.v:13 and 136 and instances/pgl27/pgl27_proximity.v:13 and 140 | kim and pgl27: "the certificate field of the proximity [N1]". psl211: "its distance field" | kim and pgl27: "the closeness field of the proximity certificate". psl211: "its distance field" | one record field, `ipc_close`, under two names across the three sibling proximity files. psl211 says "distance field" at both 11 and 73, the two siblings now say "closeness field" at both of theirs. psl211's name is the older one, but the pass is where the three would have been unified and they were not. | psl211: "closeness field", as in H6f |
| H9 | SHOULD | instances/pgl27/tableau/pgl27_tableau_checks.v:15 and 103 | "the [N1] a program carries is the one its certify statement wrote" / "the program carries the [N1] its certify statement wrote and no other" | "the security property a program carries is the one its certify statement wrote" / "so the program carries the security property its certify statement wrote and no other" | a certify statement writes evidence, and the property is read off it. manifest/pgg_tableau.v:274-277 states it exactly: "a program's security property is fixed by the certify statement that wrote the evidence". | "the security property a program carries is the one the certify statement that wrote its evidence fixes" / "so the program carries the security property that statement fixed and no other" |
| H10 | SHOULD | kim AB:1235-1237 | "It is the [N1]'s conclusion standing on its own at this instance." | "The proximity proposition of Kim's one-cut program at the number that program publishes, taken off the published program itself. It is the ideal-proximity conclusion standing on its own at this instance." | two spellings of one thing inside one docstring. The banner at 1232 says "The proximity proposition at this instance, and what implies it", so the short form is the file's word, and the sheet keeps the short form where the tree already says it. | "It is the proximity conclusion standing on its own at this instance." |
| H11 | SHOULD | kim AB:492-493 and pgl27 AB:285-286 against psl211 AB:155 and s5 AB:153 | all four: "so the witness is all the exact [N1] requires of this instance" | kim and pgl27: "and the witness is therefore all that certifying exact independence requires of this instance". psl211 and s5: "so the witness is all that certifying exact independence requires of this instance" | the sheet's rule 1 allows the rewrite only as far as the case requires. Turning "so" into "and ... therefore" is outside the case and splits a four-way twin. | kim and pgl27: restore "so the witness is all that certifying exact independence requires of this instance" |
| H12 | NOTE | kim AB:1079 | layout | "twice. Its transfer status is IdealFinite, the same the" is 59 bytes in the middle of a docstring whose neighbours run to 79 and 80, because the rewrap stopped at the last changed line | rewrap the paragraph to its end |
| H13 | NOTE | pgl27 AB:894 | layout | "publishes for input indistinguishability. It is the obligation of" is 69 bytes mid-paragraph, after the sentence shortened by eight words and the paragraph was not rewrapped | rewrap |
| H14 | NOTE | instances/pgl27/tableau/pgl27_tableau_checks.v:45 | layout | the paragraph now ends on a boxed line holding only "term asserts." | rewrap the three lines from 43 |
| H15 | NOTE | kim AB:96-97 | layout | the index entry breaks as "and, under The" then "exact-independence proposition's four conjuncts at this instance", leaving the article at a line end away from the banner name it opens | rewrap so the banner name begins a line |
| H16 | NOTE | instances/psl211/psl211_models.v:1148 | untouched by the pass | "privacy is a property of the dealer law and not of the protocol alone" | the only ordinary-English "property" left in the nineteen files, in a group where "security property" is now a defined term with three values. A reader can take it for one. | "privacy depends on the dealer law and not on the protocol alone" |
| H17 | NOTE | kim AB:164, 237, 263, 274 and pgl27 AB:167, 170 | "carries that same [N1]" | "== the concluded repeated program's security property is the same" / "== the branch program's security property is the same as well" | six index entries that resolve only against the entry above them, in an index a reader scans out of order. The old entries were anaphoric too, so this is inherited, not introduced. | name the property, which costs no line: "is input indistinguishability as well" |
| H18 | NOTE | psl211 AB:11 and s5 AB:10 | "the [N1] decides what it says: the exact [N1] asserts independence" | "the security property decides what it says: the exact-independence proposition asserts independence" | a property is a name and decides nothing. What decides is the constructor, manifest/pgg_tableau.v:274-277: "The constructor alone decides the answer". Recorded and not charged, because the sheet's case 1 explicitly maps "X alone decides" to "security property". | if it is ever touched: "and which security property the evidence proves is what it says" |
| H19 | NOTE | kim AB:945-946 | rewrapped only | "It carries the exact certificate where five_card_biased_indistinguishability_published carries the spectral one" | in a file where "exact" now means exact independence at every other site, "the exact certificate" here means the input-indistinguishability certificate whose epsilon is the exact one-cut distance. Pre-existing, but the rename makes it newly misreadable. | "It carries the certificate at the exact one-cut distance where five_card_biased_indistinguishability_published carries the spectral one" |
| H20 | NOTE | kim AB:760, banner | untouched | banner "The number each certificate publishes" | a program publishes and a certificate carries. No header references this banner. | "The number each certificate carries" |
| H21 | NOTE | psl211 AB:345 | rewrapped only | "published at 2^-40, the number the certificate proves" | a number is not a proposition. Evidence proves a proposition, per the sheet. | "the number the certificate carries" |
| H22 | NOTE | instances/psl211/psl211_reading_constancy.v:246 | "the threshold premise every security [N1] states" | "the threshold premise every security proposition states" | true at all three: `ExactProp`, `IndistinguishabilityPropAt` and `IdealProximityPropAt` each open with `forall C, (#|C| < profile_k (instance_profile A))%N ->`. "security proposition" is a new collective name that appears once in the tree. | keep, or "the threshold premise all three propositions state" |
| H23 | NOTE | kim AB:51-52 | "whose own privacy is the exact [N1]'s theorem" | "whose own privacy is the exact-independence theorem" | the theorem is `five_card_exact_view_secrecy`, and "the exact-independence theorem" names no declaration in the tree. | "whose own privacy is five_card_exact_view_secrecy" |
| H24 | NOTE | kim AB:145-146 | "the map and the five link lemmas of the exact [N1] are not there but here" | "the map and the five link lemmas the exact-independence witness rests on are not there but here" | `five_card_exact_witness` is built from them, so "rests on" is defensible, but a reader who knows `ExactWitness` has one field may take them for fields. | "the map and the five link lemmas five_card_exact_witness is built from" |

## Twins

The four `*_tableau_analysis_bridged.v`, the three `*_tableau_checks.v`, the
four `*_tableau_sampled.v` and the three `*_proximity.v`. Agent 1 wrote kim and
pgl27, agent 2 psl211 and s5.

| pair | kim / pgl27 | psl211 / s5 | reason in the instances? | id |
|------|-------------|-------------|--------------------------|----|
| analysis-bridged opening | "adjoins one piece of security evidence to a Sampled value ... the proposition it carries is the one that evidence proves" | "adjoins one security payload per real field and per index of the model ... the proposition it carries is the proposition that payload proves" | no. The old texts already differed on payload against [N1], but the count and the "the one that ... proves" clause are new. psl211 and s5 are the correct ones on the count | H2, H7 |
| `_propertyE` docstring opener | "The security property this program carries, at every real field and index, is exact independence: ..." (kim) / "The security property the exact program carries, ..." (pgl27) | "The program's security property, at every real field and index, is exact independence: ..." | no. All eight old docstrings had one shape | H4 |
| four-conjuncts docstring | "the whole content of exact independence at this instance" | "the whole content of the exact-independence proposition here" (psl211) / "... at this instance" (s5) | no. psl211 and s5 are the accurate ones | H5 |
| witness docstring close | "and the witness is therefore all that certifying exact independence requires of this instance" | "so the witness is all that certifying exact independence requires of this instance" | no. All four old texts read "so the witness is all ..." | H11 |
| four-conjuncts banner | "The exact-independence proposition's four conjuncts at this instance" | identical in both | clean, all four files byte-identical | - |
| witness banner | "The uniform family's witness" (kim) / "The exact family's witness" (pgl27) | "The exact-independence witness" (psl211) / "The tape model's witness" (s5) | yes. The old banners already named the instance's family, and only psl211's carried the barred noun | - |
| "before the certify statement" | identical in kim and pgl27 sampled files | identical in psl211 and s5 sampled files | clean, all four byte-identical | - |
| "One model, two claims, two programs" | kim AB:1043, pgl27 AB:922, identical | psl211 has no such banner | clean, untouched | - |
| closeness field of the proximity certificate | "the closeness field of the proximity certificate" (both) | "takes as its distance field" | no | H6f, H8 |
| proximity-cert-ideal docstring | "the evidence built from the certificate's witness is that program's evidence" | "the evidence built from the witness the certificate carries is that program's evidence" | inherited. Both old texts differed the same way | - |
| eps-half docstring | kim "loses that distance at one hop for each of the two committed pairs it compares", pgl27 "loses that bound at each of two hops, one per dealt secret" | no counterpart | inherited, and the instances do differ (committed pairs against dealt secrets). pgl27 matches the sheet's exemplar verbatim | - |
| "certify different properties" | kim checks:236 and pgl27 checks:110, byte-identical | psl211 checks has no counterpart | clean | - |
| index entry "the <program>'s security property is <property>" | kim AB:210, pgl27 AB:159 | psl211 AB:68, s5 AB:61 | clean, one form in all four | - |

## What was checked and is clean

- **Banner references (point 5).** Eleven "under <banner>:" references, six in
  kim AB and five in pgl27 AB, each reconstructed across its line breaks and
  matched against the banner list of its file. All eleven match exactly,
  including "The exact-independence proposition's four conjuncts at this
  instance" (kim AB:96-97 against the banner at 552), "Kim's two programs,
  certified against the uniform rotation law" (99-100 against 648), "The same
  two programs at the constants they publish" (106-107 against 827), "One
  model, two claims, two programs" (116-117 against 1043), "What the proximity
  program states at this instance" (123-124 against 1131), "The same program
  from the named word model" (pgl27 70-71 against 517) and "The ideal: the
  exact shuffle at every prior" (73-74 against 749). psl211 AB and s5 AB carry
  no such reference. No renamed banner is referenced anywhere in
  `instances/` or `manifest/` under its old name.
- **Numbers and hop counts (point 2).** `cert_eps` is the marginal bound's
  epsilon twice (manifest/pgg_tableau.v:493-496), so: kim's
  `kim_biased_proximity_cert` at one fiftieth and `cert_eps
  (kim_biased_cert_exact)` at one twenty-fifth, "twice" correct.
  `kim_biased_cert` at sqrt 5 over eighty publishing sqrt 5 over forty,
  correct. pgl27's `ipc_eps` at 2^-40 and `cert_eps (pgl27_word_cert)` at
  2^-39, "twice" correct and "met strictly" correct. psl211 at 2^-40 with a
  distinguishing advantage of at most 2^-41, correct against the sum of
  absolute differences being twice the variation distance. "The
  input-indistinguishability tail loses that bound at each of two hops" is
  right: `indistinguishability_tail` applies `var_dist_fdistmap_transfer`
  through `ic_ideal` once per run argument. "Hops to the ideal once" at the
  proximity certificates is right: `idealproximity_tail` transports one
  distance. 2^-39 against 2^-40 is never confused except at H1.
- **Property collisions (point 7).** One only, H16. Every other occurrence of
  "property" or "properties" in the nineteen files' comments is the framework
  term.
- **Spelling mixtures (point 6).** One only, H10. "the proximity proposition"
  survives where the tree already said it, at the kim banner 1232, and the
  long adjectival form is used everywhere else consistently.
- **Verb rule at the rewritten sites.** Where the pass touched a sentence it
  got the verb right: evidence carries fields and proves, propositions state,
  compare, quantify and mention, certify statements take payloads, tails lose
  and derive, programs certify and publish. The seven exceptions of H6 are
  five neighbours left alone and two new sentences.
- **Index columns.** The rewritten entries in the four analysis-bridged files
  keep their `==` column and their continuation column. The only layout
  complaints are H12 to H15.

## Coverage

- **218 of 218 sites read with OLD and NEW side by side.** The complete
  `git diff 77a2c84` of all nineteen files was read, hunk by hunk, not
  sampled. kim2025 AB 60, checks 11, sampled 3, five_card_proximity 4. pgl27 AB
  54, checks 13, sampled 2, pgl27_proximity 4, pgl27_word_privacy 1. psl211 AB
  26, checks 2, sampled 3, reading_constancy 10, models 6, word_proximity 4,
  analysis 2, word_model 1. s5 AB 12, sampled 1.
- **Declarations opened.** 26 in `manifest/pgg_tableau.v`: the three record
  types, `SecurityEvidence`, `SecurityProperty`, `evidence_property`,
  `ExactProp`, `IndistinguishabilityPropAt`, `cert_eps`,
  `IdealProximityPropAt`, `ConcludedBound`, `no_concluded_bound`,
  `EvidenceProp`, `BridgedProp`, the three payload types, the three tail
  lemmas, the three certify statements, the conclude obligation,
  `security_property_of` and the four `*_propertyE` lemmas. 14 more in the
  instances beyond the two lines of diff context: `pgl27_word_cert`,
  `pgl27_word_marginal_bound`, `pgl27_word_proximity_eps_halfE`,
  `pgl27_word_proximity_le39`, `pgl27_word_view_const`,
  `kim_biased_proximity_cert_epsE`, `kim_biased_proximity_eps_halfE`,
  `kim_biased_proximity_cert_eps_lt2`, `kim_biased_epsE`,
  `five_card_biased_proximity_published`,
  `five_card_biased_proximity_prop_holds`,
  `psl211_word_proximity_cert_secretE`, `psl211_word_proximity_cert_secretTE`,
  `psl211_fixed_deal_view_dep`. Every other site's declaration head was
  visible in the diff's own context, because each docstring sits directly on
  its declaration.
- **Numeric claims checked against a declaration: 9.** Every site whose
  sentence states a number, a hop count or a field identity.
- Not redone, as instructed: code-token identity, absence of either barred
  noun, the 80-byte ceiling.
