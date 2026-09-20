# prose_kim_pgl27: the two barred nouns leave the Kim and PGL(2,7) comments

Group `kim_pgl27`, nine files, parent commit 77a2c84, branch
feat/tableau-extensions-probe. Comments only. Nothing compiled, no Rocq process
started, no `make`, no writing git command. In this report the first barred noun
is written `[N1]` and the second is written `[N2]` in every OLD line; NEW lines
are verbatim from the files.

The OLD/NEW pairs below were generated mechanically from a line diff of each
file against a `git archive 77a2c84` extraction, with the boxed and docstring
decoration stripped and the placeholders applied by script, so an OLD line is
the parent's text and a NEW line is the landed text. Line ranges are the
parent's and the landed file's. Where a pair differs only in wrapping, the
sentence was re-flowed by a neighbouring rewrite and no word changed.

## Counts per file, per case

| file | 1 | 2 | 3 | 4 | 5 | 6 | 7 | [N2]·1 | total |
|---|---|---|---|---|---|---|---|---|---|
| instances/kim2025/tableau/five_card_tableau_analysis_bridged.v | 12 | 6 | 4 | 5 | 11 | 1 | 16 | 5 | 60 |
| instances/kim2025/tableau/five_card_tableau_checks.v | 6 | 0 | 0 | 2 | 3 | 0 | 0 | 0 | 11 |
| instances/kim2025/tableau/five_card_tableau_sampled.v | 0 | 2 | 0 | 0 | 1 | 0 | 0 | 0 | 3 |
| instances/kim2025/five_card_proximity.v | 0 | 0 | 2 | 2 | 0 | 0 | 0 | 0 | 4 |
| instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v | 9 | 5 | 6 | 5 | 8 | 1 | 13 | 7 | 54 |
| instances/pgl27/tableau/pgl27_tableau_checks.v | 8 | 0 | 0 | 1 | 4 | 0 | 0 | 0 | 13 |
| instances/pgl27/tableau/pgl27_tableau_sampled.v | 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0 | 2 |
| instances/pgl27/pgl27_proximity.v | 0 | 1 | 2 | 1 | 0 | 0 | 0 | 0 | 4 |
| instances/pgl27/pgl27_word_privacy.v | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 1 |
| **total** | **35** | **14** | **15** | **16** | **29** | **2** | **29** | **12** | **152** |

The per-case totals count occurrences, not sentences; a sentence carrying the
noun twice in two senses is counted under both cases. The file totals match the
occurrence counts the brief gave (55/5, 11/0, 3/0, 4/0, 47/7, 13/0, 2/0, 4/0,
1/0).

## Vocabulary settled for the group

- `SecurityEvidence` value: "security evidence", "the evidence"; counted, "one
  piece of security evidence".
- `SecurityProperty` value: "the security property"; the three values are
  "exact independence", "input indistinguishability", "ideal proximity"
  (adjectival "exact-independence", "input-indistinguishability",
  "ideal-proximity").
- `EvidenceProp` at each constructor: "the exact-independence proposition",
  "the input-indistinguishability proposition", "the ideal-proximity
  proposition". The tree's pre-existing short form "the proximity proposition"
  and "the proximity certificate" were left where they already stood and were
  not introduced into new text.
- the certify line: "certified for <property>", "the certify statement".
- tail lemma: "the input-indistinguishability tail".
- `ipc_close`: "the closeness field of the proximity certificate".

## The `*_propertyE` docstrings and their index entries

One shape across both instances, since the fact is the same at both:

- docstring: "The security property <the program> carries, at every real field
  and index, is <property>: <what it says>, and not <what it does not say>."
- index entry (case 7): "the <program>'s security property is <property>", or
  "... is the same" where the old entry said "that same [N1]".

## instances/kim2025/tableau/five_card_tableau_analysis_bridged.v

OLD(7-16) / NEW(7-17), case 1 + [N2]·1 — header paragraph 1.
OLD: `The AnalysisBridged level adjoins one security [N1] to a Sampled value,
and the proposition it carries is that [N1] own, on top of run correctness and
of the identification of the two readings of a coalition. A publish terminal
then turns the value into a Published. Every payload this instance gives an
[N1] is here, ...`
NEW: `The AnalysisBridged level adjoins one piece of security evidence to a
Sampled value, and the proposition it carries is the one that evidence proves,
on top of run correctness and of the identification of the two readings of a
coalition. A publish terminal then turns the value into a Published. Every
payload this instance gives a certify statement is here, ...`
Fact, from `Variant SecurityEvidence` and `certify_exact`: what the level
adjoins is a value of `SecurityEvidence`, and `EvidenceProp` gives the
proposition that value proves. The payload is what a certify statement takes.

OLD(18-28) / NEW(19-30), case 2 (four times) + case 4 — header paragraph 2.
OLD: `Three [N1] are used over the one committed run. The exact [N1] takes an
ExactWitness, ... and the [N1] carries no number. The input-indistinguishability
[N1] takes a certificate ... The proximity [N1] takes a certificate ... whose
own privacy is the exact [N1] theorem.`
NEW: `All three security properties are certified over the one committed run.
Certifying exact independence takes an ExactWitness, ... and the witness carries
no number. Certifying input indistinguishability takes a certificate ...
Certifying ideal proximity takes a certificate ... whose own privacy is the
exact-independence theorem.`

OLD(85-87) / NEW(87-89), case 1. `publishes that same AnalysisPath under a
different [N1]` -> `publishes that same AnalysisPath for a different security
property`.

OLD(94-95) / NEW(96-98), banner reference. `under The exact [N1] four conjuncts
at this instance` -> `under The exact-independence proposition's four conjuncts
at this instance`, quoting the new banner exactly.

OLD(130-133) / NEW(133-136), case 7 + case 1. `the path, [N1] and re-cut
equations, the numbers and the [N1] theorems; ... the comparison of the two
one-cut programs' [N1]` -> `the path, security-property and re-cut equations,
the numbers and the theorems stating the certified properties; ... the
comparison of the two one-cut programs' security properties`.

OLD(142-143) / NEW(145-146), case 3. `the five link lemmas of the exact [N1]`
-> `the five link lemmas the exact-independence witness rests on`.

Index entries, Definitions block:
- OLD(148-149)/NEW(151-152), case 3: `the exact [N1] witness at every field and
  index` -> `the exact-independence witness at every field and index`.
- OLD(157-158)/NEW(160-161), case 5: `the repeated path as a program at the
  input-indistinguishability [N1]` -> `the repeated path as a program certifying
  input indistinguishability`.
- OLD(160-161)/NEW(163-164), case 5: `the one-cut path as a program at that same
  [N1]` -> `the one-cut path as a program certifying that same property`.
- OLD(174-175)/NEW(177-178), case 5: `the one-cut program at the
  input-indistinguishability [N1], continued from the named model` -> `the
  one-cut program certifying input indistinguishability, continued from the
  named model`.
- OLD(178-179)/NEW(181-182), case 5: `the one-cut path as a program at the
  proximity [N1], certified at one fiftieth` -> `the one-cut path as a program
  certifying ideal proximity at one fiftieth`.

Index entries, Key results block:
- OLD(207)/NEW(210-211), case 7: `the uniform program carries the exact [N1]` ->
  `the uniform program's security property is exact independence`.
- OLD(210-211)/NEW(214-215), case 4: `seats, the exact [N1] four conjuncts at
  this instance` -> `seats, the exact-independence proposition's four conjuncts
  at this instance`.
- OLD(229-230)/NEW(233-234), case 7: `the repeated certified program carries the
  input-indistinguishability [N1]` -> `the repeated certified program's security
  property is input indistinguishability`.
- OLD(232-233)/NEW(236-237), case 7: `the one-cut certified program carries that
  same [N1]` -> `the one-cut certified program's security property is the same`.
- OLD(258-259)/NEW(262-263), case 7: `the concluded repeated program carries
  that same [N1]` -> `the concluded repeated program's security property is the
  same`.
- OLD(269-270)/NEW(273-274), case 7: `the concluded one-cut program carries that
  same [N1]` -> `the concluded one-cut program's security property is the same`.
- OLD(275-276)/NEW(279-280), [N2] case 1: `the [N2] built from its witness is
  that program's [N2]` -> `the evidence built from its witness is that program's
  evidence`. Fact: the equation is
  `ExactIndependence (ipc_witness cert) = ab_evidence (...) R idx`.
- OLD(299-300)/NEW(303-304), case 7: `the branch carries the
  input-indistinguishability [N1]` -> `the branch's security property is input
  indistinguishability`.
- OLD(302-303)/NEW(306-307), case 7: `the proximity program carries the
  proximity [N1]` -> `the proximity program's security property is ideal
  proximity`.
- OLD(318)/NEW(322), case 4: `the proximity [N1] proposition at the number the
  program publishes` -> `the ideal-proximity proposition at the number the
  program publishes`.

Body:
- OLD(451-454)/NEW(455-458), case 2, `five_card_exact_viewE`: `The exact [N1]
  compares a coalition's reading with the secret on one probability space` ->
  `The exact-independence proposition compares a coalition's reading with the
  secret on one probability space`. Verb "compares" decides it: a proposition
  compares.
- OLD(482-489)/NEW(486-494), case 3 + case 2, `five_card_exact_witness`: `The
  exact [N1] witness: ...` -> `The exact-independence witness: ...`, and `so the
  witness is all the exact [N1] requires of this instance` -> `and the witness
  is therefore all that certifying exact independence requires of this
  instance`. The connective changed from "so" to "and ... therefore" only to
  keep the closing ` *)` off an orphan line.
- OLD(535-538)/NEW(540-543), case 1, `five_card_uniform_published_propertyE`:
  `The [N1] this program carries, at every real field and index: independence of
  the coalition's view ... The certify statement the program wrote settles which
  [N1] that is.` -> `The security property this program carries, at every real
  field and index, is exact independence: independence of the coalition's view
  ... The certify statement the program wrote settles which property that is.`
  Fact: the lemma is `security_property_of ... = ExactIndependenceProperty`.
- OLD(547)/NEW(552), case 4, banner: `The exact [N1] four conjuncts at this
  instance` -> `The exact-independence proposition's four conjuncts at this
  instance`. Exactly 80 bytes; the header reference at NEW(96-98) quotes it.
- OLD(554-555)/NEW(559-560), case 1: `the whole content of the exact [N1] at
  this instance` -> `the whole content of exact independence at this instance`.
- OLD(646-651)/NEW(651-656), case 5: `certified by the input-indistinguishability
  [N1] and published at IdealFinite` -> `certified for input indistinguishability
  and published at IdealFinite`.
- OLD(668-669)/NEW(673-674), case 5: `certified by the same [N1] and published
  at the same transfer status` -> `certified for the same property and published
  at the same transfer status`.
- OLD(703-707)/NEW(708-712), case 1, twin of the uniform one above.
- OLD(716-718)/NEW(721-723), case 1: `... could not tell which [N1] either
  committed to` -> `... could not tell which property either certifies`.
- OLD(872-875)/NEW(877-880), case 1 + [N2]·1: `leaves the [N2] where the certify
  statement put it, so ... carry the same [N1]` -> `leaves the evidence where the
  certify statement put it, so ... carry the same property`.
- OLD(940-944)/NEW(945-948), case 1.
- OLD(985-986)/NEW(989-990), [N2] case 1, `kim_biased_proximity_cert_idealE`:
  `the [N2] built from the certificate's witness is that program's [N2]` -> `the
  evidence built from the certificate's witness is that program's evidence`.
- OLD(1014-1019)/NEW(1018-1024), case 6 + case 2 + case 1,
  `kim_biased_proximity_eps_halfE`: `the input-indistinguishability [N1] loses
  that distance at one hop ..., and the proximity [N1] compares one law with one
  law. The relation is ... not between the two [N1]: ... so neither [N1]
  determines the number of the other.` -> `the input-indistinguishability tail
  loses that distance at one hop ..., and the ideal-proximity proposition
  compares one law with one law. The relation is ... not between the two security
  properties: ... so neither property determines the number of the other.`
- OLD(1041-1045)/NEW(1046-1050), case 5 + case 1.
- OLD(1067-1074)/NEW(1072-1079), case 5: `certified by the proximity [N1] and
  published at its certificate's own number` -> `certified for ideal proximity
  and published at its certificate's own number`. The "hops to the ideal once
  ... hops twice" sentence carries no barred noun and was left word for word, so
  the twin in the PGL(2,7) file was left word for word too.
- OLD(1101-1102)/NEW(1106-1107), case 1.
- OLD(1114-1116)/NEW(1119-1121), case 1.
- OLD(1232)/NEW(1237), case 4: `It is the [N1] conclusion standing on its own at
  this instance.` -> `It is the ideal-proximity conclusion standing on its own at
  this instance.`

## instances/kim2025/tableau/five_card_tableau_checks.v

- OLD(29)/NEW(29), case 4: `the proximity [N1] proposition is a bound between two
  laws` -> `the ideal-proximity proposition is a bound between two laws`.
- OLD(39)/NEW(39), case 1: `a certificate of either [N1]` -> `a certificate for
  either property`.
- OLD(43-45)/NEW(43-45), case 1: `the two programs over the one-cut model carry
  different [N1]` -> `... certify different properties`.
- OLD(49)/NEW(49), case 1, index entry: same rewrite.
- OLD(168-170)/NEW(168-170), case 4: `The [N1] proposition at Kim's one-cut
  certificate is not closed by conversion.` -> `The ideal-proximity proposition
  at Kim's one-cut certificate is not closed by conversion.`
- OLD(220-225)/NEW(220-225), case 1 + case 1 + already-untrue (below): `The
  converse direction, at the [N1] the tree already carries: ... The proximity
  [N1] and the input-indistinguishability [N1] are rejected at the same argument
  ... so a certificate of either [N1] is rejected ...` -> `The converse
  direction, at the security property the tree already carries: ... The proximity
  certificate and the input-indistinguishability certificate are rejected at the
  same argument ... so a certificate for either property is rejected ...`
- OLD(233)/NEW(233), case 1, banner: `The [N1] two programs over one model carry`
  -> `The security property two programs over one model carry`.
- OLD(236-237)/NEW(236-237), case 1, twin of the five-card 43-45 sentence.

## instances/kim2025/tableau/five_card_tableau_sampled.v

- OLD(12)/NEW(12), case 5: `it is the last thing proved before an [N1] is named`
  -> `it is the last thing proved before the certify statement`.
- OLD(30)/NEW(30), case 2: `no [N1] of certify takes a payload of either kind` ->
  `no certify statement takes a payload of either kind`.
- OLD(158)/NEW(158), case 2: `no [N1] of certify takes a bound of that kind` ->
  `no certify statement takes a bound of that kind`.

## instances/kim2025/five_card_proximity.v

- OLD(13)/NEW(13), case 3: `The bound is the certificate field of the proximity
  [N1]` -> `The bound is the closeness field of the proximity certificate`. Fact:
  `kim_biased_proximity_close` is the fifth argument of `@MkIdealProximityCert`,
  the `ipc_close` field.
- OLD(20)/NEW(20), case 4: `entering the [N1] proposition and not the bound` ->
  `entering the ideal-proximity proposition and not the bound`.
- OLD(136-137)/NEW(136-137), case 3: `It is the certificate field of the
  proximity [N1] at this instance` -> `It is the closeness field of the proximity
  certificate at this instance`.
- OLD(142-143)/NEW(142-143), case 4: `the threshold enters the [N1] proposition
  and not this distance` -> `the threshold enters the ideal-proximity proposition
  and not this distance`.

## instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v

Twins of the five-card file were written to match it word for word wherever the
instances agree in the fact.

- OLD(7-12)/NEW(7-13), case 1 + [N2]·1 — header paragraph 1, twin.
- OLD(14-21)/NEW(15-23), case 2 (four times) — header paragraph 2, twin, with
  this instance's own facts (the dealt secret, three-transitivity, no number).
- OLD(48-49)/NEW(50-51), case 1: `publishes the same manifest path under a
  different [N1]` -> `publishes the same manifest path for a different security
  property`.
- OLD(86-89)/NEW(88-92), case 7 + case 1: `the path and [N1] equations, the
  bridges, the restated theorems and the two [N1] statements; ... the comparison
  of the two word programs' [N1]` -> `the path and security-property equations,
  the bridges, the restated theorems and the two theorems stating the certified
  properties; ... the comparison of the two word programs' security properties`.
- OLD(99-102)/NEW(102-104), case 3 twice: `the exact [N1] witness at every field
  and index` -> `the exact-independence witness at every field and index`; `the
  input-indistinguishability [N1] certificate` -> `the
  input-indistinguishability certificate` (now one line).
- OLD(125-126)/NEW(127-128), case 3: `the exact [N1] witness at the prior-indexed
  exact shuffle` -> `the exact-independence witness at the prior-indexed exact
  shuffle`.
- OLD(132-133)/NEW(134-135), case 5: `the word path as a program at the proximity
  [N1], concluded at 2^-39` -> `the word path as a program certifying ideal
  proximity, concluded at 2^-39`.
- OLD(157)/NEW(159-160), case 7: `the exact program carries the exact [N1]` ->
  `the exact program's security property is exact independence`.
- OLD(159-160)/NEW(162-163), case 7: `the word program carries the
  input-indistinguishability [N1]` -> `the word program's security property is
  input indistinguishability`.
- OLD(164)/NEW(167-168), case 7: `the concluded program carries that same [N1]`
  -> `the concluded program's security property is the same`.
- OLD(166)/NEW(170-171), case 7: `the branch program carries that [N1] as well`
  -> `the branch program's security property is the same as well`.
- OLD(180-181)/NEW(185-187), case 4: `below the four-seat threshold, the exact
  [N1] four conjuncts at this instance` -> `below the four-seat threshold, the
  exact-independence proposition's four conjuncts at this instance`.
- OLD(189)/NEW(195-196), case 7: `the ideal program carries the exact [N1]` ->
  `the ideal program's security property is exact independence`.
- OLD(195-196)/NEW(202-203), [N2] case 1, twin of the five-card entry.
- OLD(211)/NEW(218-219), case 7: `that program carries the proximity [N1]` ->
  `that program's security property is ideal proximity`.
- OLD(258-260)/NEW(266-269), case 2, `pgl27_exact_viewE`, twin.
- OLD(269-270)/NEW(278-279) and OLD(277)/NEW(286-287), case 3 + case 2,
  `pgl27_exact_witness`, twin of the five-card witness docstring.
- OLD(315-316)/NEW(325-326), case 3: `it is the half of the
  input-indistinguishability [N1] that appeals to no mixing bound` -> `it is the
  half of the input-indistinguishability certificate that appeals to no mixing
  bound`. Fact: `pgl27_word_view_const` is the `ic_const` field of
  `MkIndistinguishabilityCert`, and the other half is the mixing bound `ic_close`.
- OLD(331)/NEW(341), case 3: `The input-indistinguishability [N1] certificate at
  each secret prior.` -> `The input-indistinguishability certificate at each
  secret prior.`
- OLD(437-440)/NEW(447-451), case 1, `pgl27_exact_published_propertyE`, twin.
- OLD(446-449)/NEW(457-460), case 1, `pgl27_word_published_propertyE`.
- OLD(462)/NEW(473), [N2] case 1, `pgl27_bound39`: `A single real will not serve,
  because the security [N2] quantifies over the field.` -> `A single real will
  not serve, because the security evidence is given at every real field.` Listed
  below as an already-untrue sentence.
- OLD(495-497)/NEW(506-508), case 1 + [N2]·1, twin of the five-card concluded
  docstring.
- OLD(520-522)/NEW(531-534), case 1 + [N2]·1: `Naming the Sampled value before
  the certify statement leaves the [N2] where that statement put it, so the branch
  program carries the [N1] pgl27_word_published39 carries.` -> `... leaves the
  evidence where that statement put it, so the branch program carries the
  property pgl27_word_published39 carries.`
- OLD(628-631)/NEW(640-644), case 4, `pgl27_exact_bridge`: `The program's first
  conjunct of the [N1] is independence of the executed reader from the secret` ->
  `The first conjunct of the exact-independence proposition the program carries
  is independence of the executed reader from the secret`.
- OLD(673)/NEW(686), case 4, banner, identical to the five-card banner.
- OLD(681-683)/NEW(694-696), case 1, twin.
- OLD(752)/NEW(765), case 3: `The exact [N1] witness at every prior` -> `The
  exact-independence witness at every prior`.
- OLD(772)/NEW(785), case 5: `certified by the exact [N1] and published` ->
  `certified for exact independence and published`.
- OLD(794-795)/NEW(807-809), case 1, `pgl27_prior_exact_published_propertyE`.
- OLD(840-843)/NEW(854-857), [N2] case 1, twin of `kim_biased_proximity_cert_idealE`.
- OLD(864-872)/NEW(878-886), case 6 + case 2 + case 1,
  `pgl27_word_proximity_eps_halfE`, twin of `kim_biased_proximity_eps_halfE`.
- OLD(880)/NEW(894), case 5: `the constant the word program publishes for the
  input-indistinguishability [N1]` -> `the constant the word program publishes
  for input indistinguishability`.
- OLD(911)/NEW(925), case 5: `The word model certified by the proximity [N1] and
  concluded at 2^-39` -> `The word model certified for ideal proximity and
  concluded at 2^-39`. The "hops to the ideal once ... hops twice" sentence in
  the same docstring was left word for word, matching the five-card twin.
- OLD(942-944)/NEW(956-958), case 1, twin.
- OLD(952-954)/NEW(966-968), case 1: `the pair differs in the [N1] and in nothing
  about the algebra, the run or the law` -> `the pair differs in the security
  property and in nothing about the algebra, the run or the law`.

One further hunk, OLD(755-756)/NEW(768-769), changes no word: it is the re-flow
of the paragraph whose first line was edited at OLD(752).

## instances/pgl27/tableau/pgl27_tableau_checks.v

- OLD(15-20)/NEW(15-21), case 1 + case 5 + case 1 + case 4: `[N1] a program
  carries is the one its certify statement wrote, so recording the word program
  at the exact [N1] is refused. ... the two programs over the word model carry
  different [N1] ... refusing to read the exact [N1] four conjuncts off the word
  program.` -> `security property a program carries is the one its certify
  statement wrote, so recording the word program for exact independence is
  refused. ... the two programs over the word model certify different properties
  ... refusing to read the exact-independence proposition's four conjuncts off
  the word program.`
- OLD(43)/NEW(44-45), case 1: `not for the [N1] the term asserts` -> `not for the
  security property the term asserts`.
- OLD(47)/NEW(49), case 1, index entry: `the two programs over the word model
  carry different [N1]` -> `... certify different properties`, matching the
  five-card entry.
- OLD(97)/NEW(99), case 1, banner: `The [N1] a program carries` -> `The security
  property a program carries`.
- OLD(100-101)/NEW(102-104), case 5 + case 1: `Recording the word program at the
  exact [N1] is rejected by conversion, so the program carries the [N1] its
  certify statement wrote and no other.` -> `Recording the word program for exact
  independence is rejected by conversion, so the program carries the security
  property its certify statement wrote and no other.`
- OLD(107-109)/NEW(110-112), case 1, twin of the five-card sentence, word for
  word.
- OLD(122-124)/NEW(125-127), case 1, inside the timing comment of the proof:
  `The equation between the [N1] is therefore assumed first` -> `The equation
  between the security properties is therefore assumed first`. The three
  measured timings are untouched.
- OLD(188)/NEW(191), case 1, banner: `The [N1] are different statements` -> `The
  security properties are different statements`.
- OLD(191-196)/NEW(194-200), case 1: same opening rewrite in the docstring below
  that banner.

## instances/pgl27/tableau/pgl27_tableau_sampled.v

- OLD(12)/NEW(12), case 5: twin of the five-card sampled header, word for word:
  `before an [N1] is named` -> `before the certify statement`.
- OLD(35-36)/NEW(35-36), case 5, index entry: `the word model named at Sampled,
  before any [N1] is chosen` -> `the word model named at Sampled, before the
  certify statement`.

## instances/pgl27/pgl27_proximity.v

- OLD(13)/NEW(13), case 3: `One bound is the certificate field of the proximity
  [N1]` -> `One bound is the closeness field of the proximity certificate`, twin
  of the five-card proximity header.
- OLD(111-112)/NEW(111-112), case 2: `The input-indistinguishability [N1]
  compares two laws obtained by pushing a reader forward along a distribution on
  cuts` -> `The input-indistinguishability proposition compares two laws obtained
  by pushing a reader forward along a distribution on cuts`.
- OLD(140-142)/NEW(140-142), case 3: `It is the certificate field of the
  proximity [N1] at this instance` -> `It is the closeness field of the proximity
  certificate at this instance`, twin.
- OLD(144-148)/NEW(144-148), case 4: `The premise is the [N1] threshold at this
  instance, four seats.` -> `The premise is the ideal-proximity proposition's
  threshold at this instance, four seats.`

## instances/pgl27/pgl27_word_privacy.v

- OLD(89-90)/NEW(89-90), case 3: `it is the number a word program's
  input-indistinguishability [N1] carries` -> `it is the number a word program's
  input-indistinguishability certificate carries`. Fact: the number is
  `sw_bound_eps (pgl27_word_marginal_bound R)`, the `ic_b` field of
  `IndistinguishabilityCert`, so what carries it is the certificate.

## Sentences that were already untrue, and how they were made true

1. `pgl27_tableau_checks.v` OLD(220-225) in the five-card twin, and the same
   shape in the PGL(2,7) file: `The proximity [N1] and the
   input-indistinguishability [N1] are rejected at the same argument, the sample
   adapter each certificate type is indexed by`. A security property is a value
   of an enumeration and is never presented to the kernel, so nothing about it is
   rejected. What the recorded `Fail` rejects is a certificate whose sample
   adapter does not match. Landed as `The proximity certificate and the
   input-indistinguishability certificate are rejected at the same argument, the
   sample adapter each certificate type is indexed by`.

2. `pgl27_tableau_analysis_bridged.v` OLD(462): `A single real will not serve,
   because the security [N2] quantifies over the field.` A value of
   `SecurityEvidence` quantifies over nothing; it is the accumulated family
   `ab_evidence : forall R idx, SecurityEvidence ...` that is given at each real
   field, which is why `ConcludedBound` is `forall R : realType, option R`.
   Landed as `A single real will not serve, because the security evidence is
   given at every real field.` The manifest carries the same sentence at
   `ConcludedBound`; that copy belongs to the agent editing
   `manifest/pgg_tableau.v` and I did not touch it, so the two should be checked
   against each other at merge.

3. Two verb-rule corrections that the case table forces rather than a falsehood
   in the parent, recorded here because they change the subject of the sentence:
   `the exact [N1] takes a witness` became `certifying exact independence takes
   an ExactWitness` (a property takes nothing; a certify statement takes a
   payload), and `the input-indistinguishability [N1] loses that bound at each of
   two hops` became `the input-indistinguishability tail loses that bound at each
   of two hops` (the loss happens in `indistinguishability_tail`, whose
   `cert_eps` is the marginal epsilon added to itself).

## Sentences I could not make true

None. Every site landed with a reading I can defend against the declaration it
sits on.

## One wording left for the main session to confirm

In `five_card_tableau_analysis_bridged.v` the index entry for
`five_card_biased_proximity_prop_holds` now reads `the ideal-proximity
proposition at the number the program publishes`, while the docstring of that
lemma, which carries no barred noun and was therefore not touched, still opens
`The proximity proposition of Kim's one-cut program at the number that program
publishes`. Both spellings are sanctioned by the sheet (the short form stays
where the tree already says it), but a later pass may want the entry and the
docstring to agree.

## Final scan

Script over all nine landed files, word-boundary, any case, over both barred
nouns and their inflections: the singular, the plural, the possessive singular
and plural for the first, and the singular, plural, possessive, past and
progressive for the second.

| file | occurrences of either noun | code tokens vs 77a2c84 |
|---|---|---|
| instances/kim2025/tableau/five_card_tableau_analysis_bridged.v | 0 | identical |
| instances/kim2025/tableau/five_card_tableau_checks.v | 0 | identical |
| instances/kim2025/tableau/five_card_tableau_sampled.v | 0 | identical |
| instances/kim2025/five_card_proximity.v | 0 | identical |
| instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v | 0 | identical |
| instances/pgl27/tableau/pgl27_tableau_checks.v | 0 | identical |
| instances/pgl27/tableau/pgl27_tableau_sampled.v | 0 | identical |
| instances/pgl27/pgl27_proximity.v | 0 | identical |
| instances/pgl27/pgl27_word_privacy.v | 0 | identical |

The code comparison strips every `(* ... *)` region, including nested ones, and
compares the whitespace-normalised remainder against a `git archive 77a2c84`
extraction. All nine are byte-identical outside comments, so no code token
changed.

Layout: every boxed header line and every banner in the nine files is exactly 80
bytes with a space before the closing delimiter, no line anywhere exceeds 80
bytes, the `==` and continuation columns of the index blocks are unchanged, the
docstring continuation is four spaces, each banner is one content line, and no
rewritten paragraph ends on an orphan short line. Six lines that a width check
flags as neither 80 bytes nor over 80 are plain non-boxed source comments and one
pre-existing 81-byte code line, all present verbatim in the parent:
`five_card_tableau_analysis_bridged.v` 769 and 841,
`pgl27_tableau_analysis_bridged.v` 480 and 987, `pgl27_proximity.v` 165,
`pgl27_word_privacy.v` 145 and 179.

## Out of scope, listed for the owner

`instances/psl211/psl211_exec.v` is in the forward closure of
`instances/psl211/psl211_endpoints.v` and holds one site of the first barred
noun. It was not opened and not edited, per the brief.
