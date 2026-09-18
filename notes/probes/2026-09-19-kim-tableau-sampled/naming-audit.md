# Naming and style audit: Kim's two five-card rows as Tableau programs

Date: 2026-09-19. Independent read-only audit.

Auditor wrote none of the audited text. Nothing was compiled, no Rocq process
was started, no file outside this report was written or edited. Every claim
below is backed by a file:line read or by a Python scan re-run in this session,
not by the probe's own reported numbers.

Scope. Spec `notes/20260919-kim-tableau-sampled-design.md`, ledger rows K10 and
K11. Probe `notes/probes/2026-09-19-kim-tableau-sampled/`, principally
`five_card_rows_landing.v`, the full copy that will be committed verbatim over
`instances/kim2025/five_card_rows.v`. Conventions read from the production
original and from `instances/s5/s5_rows.v`, `instances/pgl27/pgl27_rows.v`,
`instances/psl211/psl211_rows.v`, `manifest/pgg_analysis_manifest.v` and
`instances/kim2025/five_card_kim.v`.

Line references of the form `landing:N` are lines of
`notes/probes/2026-09-19-kim-tableau-sampled/five_card_rows_landing.v`.

## Findings

| id | severity | file:line | rule | evidence | pasteable alternative |
|---|---|---|---|---|---|
| B1 | BLOCKING | landing:11-17 | M3, every header sentence true after the change | The unchanged opening paragraph promises "every statement below is about a coalition of at most one of the five seats" and then "input privacy ... is not what this row states". Both are false after the change. `five_card_row_biased_leak_bound` at landing:505 is stated for every `A : seq nat` with no bound on `size A`, `five_card_row_repeated_endpoint_lt` at landing:477 names no coalition at all, and `kim_centi_small` at landing:489 is arithmetic. The biased bound is `five_card_colour_view_leak_bound` of `instances/kim2025/five_card_models.v:360`, which transports `kim_input_private` of `instances/kim2025/kim_input_privacy.v:716`, so the file now states exactly the input privacy the header denies. The file's own new Key results line at landing:118-120 calls it "Kim's input-privacy bound". | Fix B1 below |
| B2 | BLOCKING | landing:404 | metaphor words are barred from identifiers | `five_card_row_alien_tableau` names the rejected mutation by a metaphor rather than by what is wrong with it. The three sibling rejections name the combination instead: `s5_dealt_rand` at `instances/s5/s5_rows.v:192`, `pgl27_inline_reuse` at `instances/pgl27/pgl27_rows.v:362`, `psl211_row_vm_reuse` at `instances/psl211/psl211_rows.v:293`. None uses a figure of speech and none carries `_tableau`. | Fix B2 below |
| S1 | SHOULD-FIX | landing:422, landing:440 | every Definition and Lemma carries a statement comment | `five_card_row_biased_prefixE` and `five_card_row_biased_modelE` have none. Every other declaration in the production file and in all three sibling rows files has one. The short second-of-a-pair form is precedented at `instances/pgl27/pgl27_rows.v:323` and `:562`. | Fix S1 below |
| S2 | SHOULD-FIX | landing:453 | statement comment carries the fact and its position | `(** The manifest's completion level for the biased row. *)` is a bare noun phrase. It is the one declaration whose whole job is to make the level gap readable beside the rejected ascription at landing:462, and it says nothing about that. | Fix S2 below |
| S3 | SHOULD-FIX | landing:29, landing:114, landing:469-476 | one word per concept, type-honest phrasing | The bound's index `s : 'I_5` is called three things in seven lines: "one starting position" at landing:470, "every seat" at landing:472, "one seat's endpoint marginal" at landing:473, while the codomain is "the five positions" at landing:471 and "card positions" at landing:472. The header sentence at landing:29 and the Key results gloss at landing:114 both say "one seat". The seat to card-position identification is not proved in this file: `five_card_static_obsE` at landing:224 keeps `tnth (pi_starts FiveCardKim_PI) i` rather than reducing it to `i`, unlike `pgl27_static_obsE` at `instances/pgl27/pgl27_rows.v:142`, whose comment states the identification explicitly. | Fix S3 below |
| S4 | SHOULD-FIX | landing:384-395 | long exposition belongs at the file header, not pinned to one declaration | The biased program's comment repeats the header paragraph at landing:31-41 almost word for word: both spell out the exact arm's independence request, the spectral arm's variation distance and constancy requests, and the conclusion that neither carries a bound of that kind. Two copies of one argument drift apart on the next edit. | Fix S4 below |
| S5 | SHOULD-FIX | spec:120-124, spec:157, spec:255 | the spec must name every landed declaration and must not contradict the probe | Four items, listed under "M7, the spec" below. | Fix S5 below |
| N1 | NOTE | landing:379, landing:396 | shared suffix at two types | Judgement: keep. Detail under "M1(a)". |
| N2 | NOTE | landing:449 | name of a type-ascription witness | Judgement: keep. Detail under "M1(b)". |
| N3 | NOTE | landing:75-77, landing:110-112 | the levelE and the ascription never appear together | The two halves of the level story sit in different header tables, 35 lines apart. | Fix N3 below |
| N4 | NOTE | landing:477, landing:505 | MathComp suffix vocabulary | `_endpoint_lt` is correct for `<`. `_leak_bound` concludes `<=` where MathComp would write `le`. Detail under "M1(e)". |
| N5 | NOTE | landing:489 | a family split across two files | Judgement: keep the name. Detail under "M1(f)". |
| N6 | NOTE | landing:370, landing:467 | banner register | Detail under "M4". |
| N7 | NOTE | landing:19, landing:43 | singular in a file that now holds three programs | "The row is written in the statement surface" and "No statement of the program is a theorem about this instance". `instances/pgl27/pgl27_rows.v:28` writes the plural form. | Fix N7 below |
| N8 | NOTE | landing:102-109 | header table layout | The `prefixE` and `modelE` pairs stack two names before a single `==`. The file gives every other name its own `==`, and `instances/s5/s5_rows.v:97` shares a gloss by putting both names on one line instead. |

## M1. Names

### (a) `_tableau` at two types

Every `_tableau` name that exists today is a `PublishedRow`, five of five:
`s5_row_rand_tableau` at `instances/s5/s5_rows.v:275`,
`pgl27_row_exact_tableau` at `instances/pgl27/pgl27_rows.v:270`,
`pgl27_row_word_tableau` at `:295`, `five_card_row_uniform_tableau` at
`instances/kim2025/five_card_rows.v:286`, `psl211_row_alldecks_tableau` at
`instances/psl211/psl211_rows.v:175`. Every Tableau value that is not published
is named without the suffix: `five_card_committed` at
`instances/kim2025/five_card_rows.v:123`, `s5_dealt` at
`instances/s5/s5_rows.v:140`, `s5_supplied` at `:166`, `pgl27_dealt` at
`instances/pgl27/pgl27_rows.v:124`, `pgl27_inline_dealt` at `:342`,
`psl211_alldecks_prefix` at `instances/psl211/psl211_rows.v:126`,
`psl211_alldecks_prefix_vm` at `:236`, `psl211_alldecks_prefix_lit` at `:269`.
The checked and rejected `Tableau Sampled` terms are the same: the `Check` at
`instances/s5/s5_rows.v:191` is anonymous, and `s5_dealt_rand` at `:192`,
`pgl27_inline_reuse` at `instances/pgl27/pgl27_rows.v:362` and
`psl211_row_vm_reuse` at `instances/psl211/psl211_rows.v:293` carry no suffix.

So the surface reading is that the landing breaks a perfect invariant. The
deeper reading is that it does not. The rule the five existing names obey is
not "suffix means PublishedRow" but "`<instance>_row_<mode>_tableau` is the
program for the manifest row `<instance>_row_<mode>`", and every one of the
five is a `PublishedRow` only because every program written so far happened to
be a finished row. The new names satisfy that rule exactly, and the suffix is
forced: `five_card_row_repeated` and `five_card_row_biased` are already taken
by the manifest rows at `manifest/pgg_analysis_manifest.v:776` and `:766`, and
the landing's own `modelE` lemmas at landing:437 and landing:442 refer to them
under those names in the same file.

Verdict: acceptable, keep. The type difference is carried where it belongs, in
the Definitions gloss at landing:69-74, which says "stopping at Sampled" for
each. No change requested.

### (b) `five_card_row_repeated_at_manifest_level`

Precedent for the `_at_` connective is local and consistent: `kim_lambda2_at_zero`
at `instances/kim2025/five_card_kim.v:521`, `kim_bound_at_zero` at `:528`,
`kim_security_at_zero` at `:539`, `kim_lambda2_at_centi` at `:584`,
`foata_depth_at_ext` at `groups/pgg_raag.v:128` and two siblings, `ad_fiber_at_row`
at `instances/psl211/psl211_alldecks.v:1188`. In all of them `X_at_Y` reads
"X taken at the parameter value Y", which is what this declaration is.

Precedent for a Definition whose body is trivial and whose type is the content:
`five_card_F_ite` at `instances/kim2025/five_card_rows.v:360` in this very file,
and `pgl27_word_same_statement` and `pgl27_exact_same_statement` at
`instances/pgl27/pgl27_rows.v:550` and `:563`. The shape is established.

One mismatch. The prose says "completion level" throughout, at landing:77,
landing:111, landing:445 and landing:453, tracking the field name
`apr_completion`, while the identifier says `manifest_level`. The identifier
family is internally consistent, `_levelE` and `_at_manifest_level` both using
the bare word, so this is two registers rather than drift inside one. If the
caller wants the identifier to track the field name, the pasteable alternative
is `five_card_row_repeated_at_manifest_completion`, which collides with nothing
in the tree or in installed infotheo or mathcomp.

Verdict: keep `five_card_row_repeated_at_manifest_level`.

### (c) `prefixE`, `modelE`, `levelE`, and the asymmetry

The E suffix on an equation is the tree's own convention and is used correctly
here. None of `_prefixE`, `_modelE` or `_levelE` exists anywhere in the tree
today, so the three are new but consistent with the many existing E names in
the same files.

On the asymmetry. The two rows are in different situations, and each landed
declaration is the sharpest available statement of its own situation. For the
repeated row the fact worth stating is that the program's level index and the
manifest's level term are one term, and the ascription at landing:449 states it
in the strongest form, by making the kernel check it. A
`five_card_row_repeated_levelE` would restate, as a propositional equation,
something the ascription already forces definitionally. For the biased row no
ascription is possible, so a lemma is the only carrier, and the rejected
ascription at landing:462 supplies the other half.

One correction to the reason on record. `notes/probes/2026-09-19-kim-tableau-sampled/STATUS.md:183-191`
gives two reasons for dropping `five_card_row_repeated_levelE`, the second being
that the manifest checks that equation itself. That reason does not distinguish
the two rows: the manifest checks the biased equation too, at
`manifest/pgg_analysis_manifest.v:1778`, by the same `Timeout 60 Check (erefl : ...)`
idiom it uses for the repeated one at `:1787`, and the biased lemma is landed
anyway. Only the first reason, that the ascription already forces the equation,
separates them. The plan should carry the first reason and drop the second.

Verdict: the asymmetry is correct and should stand. Both rows do not need a
`levelE`. What the asymmetry needs is for a header reader to see it as
deliberate, which is finding N3.

### (d) `five_card_row_alien_tableau`

Finding B2. The name is a figure of speech standing in for a type fact. What is
actually being rejected is a model family indexed over a different instance's
observed execution, which the recorded error text at
`notes/probes/2026-09-19-kim-tableau-sampled/STATUS.md:56-59` states precisely:
`S5Analysis.rand_family` has type `AnalysisModelFamily s5_exec.s5_rand_observed`
where `FamPayload (tableau_at five_card_committed)` is expected.

The three sibling rejections name the offending combination rather than a
quality of it, and none carries `_tableau`. The replacement below follows them.
`five_card_row_s5_family` collides with nothing in the tree or in installed
infotheo or mathcomp.

### (e) `_endpoint_lt` and `_leak_bound`

`five_card_row_repeated_endpoint_lt` concludes a strict `<` at landing:481 and
takes `lt`, which is the MathComp suffix for a strict inequality and is also
the suffix of the source lemma `kim_deal_centi_lt` at
`instances/kim2025/five_card_kim.v:646`. Correct on both readings.

`five_card_row_biased_leak_bound` concludes `<=` at landing:517, where MathComp
would write `le`, as in `kim_deal_centi_lt`'s own neighbour
`fc_kim_security_bound` at `instances/kim2025/five_card_kim.v:570`, which also
concludes `<=` and is also named `_bound`. The tree has 38 declarations ending
in `_bound`, and they are split between statements and values: `kim_leak_bound`
at `instances/kim2025/kim_input_privacy.v:78` is the bound's value,
`five_card_colour_view_leak_bound` at `instances/kim2025/five_card_models.v:360`
is the statement. A reader who meets `five_card_row_biased_leak_bound` cold
cannot tell from the name which it is.

The landed pair therefore mixes two principles, `_endpoint_lt` naming its
relation and `_leak_bound` echoing its source. I judge the echo the better
principle here, because the landed lemma is `five_card_colour_view_leak_bound`
restated at another law and nothing else, and a reader chasing the name should
land on the source. The internal asymmetry is the price.

Verdict: keep both names, and have the plan record the principle in one line so
the next such name is not argued from scratch. If the caller prefers internal
symmetry, the pasteable alternative is `five_card_row_biased_leak_le`, which
collides with nothing.

### (f) `kim_centi_small`

The name is not invented here. `instances/kim2025/five_card_models.v:51-75`
already carries a hypothesis-consumption table that names the five-card layer's
four side conditions `lt`, `gt`, `spec` and `small`, and spells out at `:69`
that "small is 0 < 1/5 - |eps|", which is the landed statement at landing:489
instantiated at bias one hundredth. The same table records at `:64` that
`five_card_colour_view_leak_bound` consumes `lt`, `gt` and `small`, which is
exactly the landed proof at landing:518. The name is the tree's own vocabulary
and is the only name that fits.

The split is real. `kim_centi_small` would be the first declaration in
`five_card_rows.v` whose name does not begin with `five_card_`, and the only
`kim_centi_*` outside `instances/kim2025/five_card_kim.v`, where
`kim_centi_lt` at `:595`, `kim_centi_gt` at `:601` and `kim_centi_spec` at
`:612` live in one concrete section.

Would a file-local name be more honest? I judge not. Renaming to
`five_card_centi_small`, which is free, would name the file the declaration
temporarily sits in rather than the mathematics it states, and the mathematics
is not five-card-rows-specific: it is a fact about the number one hundredth.
The honest disclosure is already present, in the statement comment at
landing:485-487, which names the three siblings and the file they live in. What
is missing is that the header gloss at landing:116-117 does not disclose it, so
a reader of the header alone learns nothing. That is a one-line gloss change,
recorded as part of N5 and not requested as a fix.

Verdict: keep `kim_centi_small` in `five_card_rows.v` with its current comment.

### (g) Collisions

Re-run independently in this session, in Python with `\b` word boundaries, over
521 `.v` files: every `.v` under `lib`, `protocol`, `groups`, `security`, `smc`,
`reconstruct`, `instances` and `manifest`, plus every `.v` under
`/Users/cheng-huiweng/Projects/coq/_opam/lib/coq/user-contrib/infotheo` and
`.../mathcomp`. Zero hits for all eleven landed names, for both landed mutation
names, and for `five_card_row_repeated_levelE`. Zero hits also for the four
alternatives proposed in this report. Against the identifiers already declared
in `five_card_rows.v`, zero, checked by the same scan over the production file.

Result confirmed. The probe's K10 figure is accurate.

## M2. Statement comments

Style. `five_card_rows.v` writes `(** prose ... *)` with no leading name.
`instances/psl211/psl211_rows.v` writes `(** name — prose *)`, at `:122`, `:140`,
`:166` and elsewhere, and `instances/kim2025/five_card_models.v` does the same.
The landing uses the no-leading-name form throughout, matching the file it
replaces and not the probe or the neighbours. Correct.

Content, the hard rules. Checked comment by comment over landing:373-518 and
over the new header paragraph at landing:26-41.

- No comment says or suggests that either Kim row gives coalition privacy,
  secrecy or independence. Three comments actively deny it: landing:376-378
  says the endpoint fact is "about where a single starting position is sent and
  not about what any set of seats reads, so no security payload follows it";
  landing:473 says "the statement names no set of seats and no secret";
  landing:502-504 says the biased bound "is about a reading at a list of card
  positions and not about a coalition of seats".
- The repeated row's bound is stated as one seat's endpoint marginal under the
  cut law, at landing:469-476. Correct in substance, and the wording is finding
  S3.
- The biased row's bound is stated as a ceiling on a conditional mutual
  information between the inputs and the executed colour reading given the
  secret, at landing:495-498. Verified against the source: `kim_secret` at
  `instances/kim2025/kim_input_privacy.v:68` is `Secret R`, the output `a && b`,
  so "given the conjunction the run computes" is accurate, and `kim_view A` at
  `:72` is `ViewA R A`, documented at `instances/denboer1989/five_card_leakage.v:78`
  as "the partial view at the fixed list of card positions A", so "at a list of
  card positions" is the source's own wording.
- No comment says the bound is positive, small or informative. landing:501-502
  says the opposite in the right way: "a numeric ceiling on that information and
  not the assertion that the information vanishes", which is a claim about the
  statement and not about the value.
- No comment describes the Tableau as certifying the biased row. landing:393-395
  denies it: "the manifest's higher level for this row rests on that theorem and
  not on any payload of the program".
- Nothing slides from "cannot be supplied from existing theorems" to "cannot be
  proved" or "is false". landing:391-392 writes "neither of which is proved at
  this instance" and landing:389-390 writes "which the development states under
  the uniform cut and not under the biased one". Both are statements about what
  exists. Clean.

Content, the ordinary rules. Scanned for status markers, progress and effort
narration, measurement, "key lemma", proof strategy and rejected alternatives.
The only hits for "rejected" are at landing:402, landing:460 and the pre-existing
landing:557, all of which mean rejected by the kernel, which is this file's own
idiom. No status, no measurement, no effort, no roadmap, no attribution. Naming
the theorem a statement is, as at landing:475 and landing:499, is this file's
established idiom for position, not proof strategy: compare landing:287-288 and
landing:351 in the unchanged text.

Missing comments: finding S1. Comment with a fact but no position: finding S2.
Exposition duplicated between header and declaration: finding S4.

## M3. The header

Title. `(* five_card_rows: the five-card instance's three rows, written as programs   *)`
at landing:4, exactly 80 bytes. "Written as programs" is accurate for a program
that stops before certify: a `Tableau Sampled` is a program in this file's own
vocabulary, and the sibling title at `instances/s5/s5_rows.v:4` says "two
sharing-family runs, as programs" where one of the two, `s5_dealt`, stops at
`Observed` and is not a row at all. "Three rows" is also accurate: the manifest
carries exactly three five-card rows, at `manifest/pgg_analysis_manifest.v:756`,
`:766` and `:776`, and all three now have a program.

Boxed lines. Every non-doc comment line in the file is exactly 80 bytes, checked
byte-wise over all 571 lines. No line anywhere in the file exceeds 80 bytes.
Maximum header body width is 74 characters, and the new lines respect it.

Truth of every sentence. Two sentences are false after the change, finding B1.
Two more are singular where the file is now plural, finding N7. Everything else
checks out, including the new paragraph's account of both arms, which matches
the fields the probe exercised and matches the gap `instances/s5/s5_rows.v:54-73`
records for `s5_row_word`.

Register. The new paragraph reads in the register of the rest: declarative, no
hedging, no first person, no meta. The phrase "the shuffle group" at landing:38
is not drift, it is the sibling's own phrase at `instances/s5/s5_rows.v:63` in
the same sentence shape, and the tree uses it throughout
`instances/pgl27/pgl27_mixing.v`.

Tables. All eleven landed public declarations appear. Definitions gains
`five_card_row_repeated_tableau`, `five_card_row_biased_tableau` and
`five_card_row_repeated_at_manifest_level` at landing:69-77. Key results gains
the two `prefixE`, the two `modelE`, `five_card_row_biased_levelE`,
`five_card_row_repeated_endpoint_lt`, `kim_centi_small` and
`five_card_row_biased_leak_bound` at landing:102-120. Each carries a gloss. Two
glosses cover a pair of names, which is finding N8, and one gloss carries the
seat wording of finding S3.

## M4. Placement and sections

Placement. The two new banners are at landing:369-371 and landing:466-468, after
the exact arm's four conjuncts ends at landing:367 and before the ideal
functionality begins at landing:520. As specified.

Banner style. `(*     Kim's two rows                                                         *)`
and `(*     What the two rows carry beside their programs                          *)`,
both five spaces of lead and both exactly 80 bytes, matching every existing
banner in the file.

Titles, finding N6. Two observations, neither a fix demand.

"Kim's two rows" puts the word Kim into this file's prose for the first time.
The production file's prose never names Kim, only the identifiers do
(`five_card_kim`, `FiveCardKim_M`, `FiveCardKim_PI`), and the existing banner
for the corresponding uniform material is "The uniform row". Kim's is tree
vocabulary elsewhere, at `instances/kim2025/five_card_models.v:346` and
`manifest/pgg_analysis_manifest.v:761`, so this is register drift within one
file rather than an invented word. Parallel alternative:
`(*     The biased and the repeated rows                                       *)`.

"What the two rows carry beside their programs" is a free relative where this
file's other banners are noun phrases, though a full sentence is precedented at
`instances/pgl27/pgl27_rows.v:542`. The section also holds `kim_centi_small`,
which is arithmetic on a number and not something a row carries. Alternative:
`(*     The two bounds, and the side condition one of them needs              *)`.

## M5. One word per concept

Checked across the new text against the production file and the manifest.

- row, program, tableau. Clean. The word tableau never appears in prose, only as
  the type `Tableau` and inside identifiers. "Program" is used for the Tableau
  value and "row" for the manifest row and for the analysis path, exactly as
  the production file does at landing:279-297.
- cut, shuffle, rotation. Clean. "Cut" for the drawn element, "rotation"
  reserved for the uniform model as in the unchanged landing:8 and landing:22,
  "shuffle group" for the group, matching `instances/s5/s5_rows.v:63`.
- seat, position, card. Drift, finding S3. This is the only one.
- colour view, colour reading, reading. Clean. "Colour reading" at landing:496
  matches the production header at landing:53-54, and "a reading" at landing:502
  matches the production landing:307.
- bias one hundredth, centi. Clean. "Centi" appears only inside identifiers, and
  the prose always writes "bias one hundredth", matching
  `manifest/pgg_analysis_manifest.v:762` and `:772`.
- level, completion level. Two registers, each internally consistent. Prose
  always writes "completion level", identifiers always write bare `level`.
  Recorded under M1(b), not a fix.

## M6. Mechanical

All clean.

- 571 lines. Zero lines over 80 bytes. Every non-doc comment line exactly 80
  bytes.
- The banned-vocabulary scan, whole-word and case-insensitive over the whole
  file: zero hits.
- Development words in identifiers: zero. No occurrence of the probe, landing,
  draft, scratch or temporary vocabulary anywhere in the file, in identifiers or
  in prose.
- Metaphor in an identifier: one, finding B2.
- `Print Assumptions` occurs once, at landing:567, inside a pre-existing comment
  carried over unchanged from `instances/kim2025/five_card_rows.v:374`. It is
  prose, not a command.
- No `Time`, no `Timeout`, no `Show`, no `Admitted`, no `Abort`, no `Axiom`, no
  `Parameter`, no `Hypothesis`, no `Variable`, no `Check`.
- `Fail` count three: the two new ones at landing:404 and landing:462, and the
  pre-existing `five_card_F_or` at landing:560. None carries an expected-failure
  marker, and the pre-existing one does not either, so the landing matches its
  own file. Note for contrast that `instances/psl211/psl211_rows.v:246-254`
  quotes the error text inside the comment and
  `instances/s5/s5_rows.v:185-190` uses a plain `(* *)` block rather than a doc
  comment; the landing correctly follows neither, since this file does neither.
- No lone `by [].` line. Every one-tactic proof is written `Proof. by []. Qed.`
  on one line, at landing:438, landing:443 and landing:456, as the file does at
  landing:183, landing:339, landing:549 and landing:570. The two `by split.`
  proofs and the one-line `by rewrite ...; exact: ...` follow the same habit,
  and `kim_centi_small`'s three-line proof matches the file's multi-line habit
  at landing:210-215.

## M7. The spec

Does it name, for each landed declaration, the name, the statement and the home
precisely enough for a plan written verbatim from the landing copy? Mostly yes,
with one real gap.

Named with an exact statement: the two programs, in Coq, at spec:104-110.
Named with a statement in prose: `five_card_row_repeated_endpoint_lt` at
spec:126-129, `five_card_row_biased_leak_bound` at spec:226-229,
`kim_centi_small` at spec:224-226 with its home decision at spec:247-250,
`five_card_row_repeated_at_manifest_level` at spec:207,
`five_card_row_biased_levelE` at spec:208.
Named without a statement: the two `modelE` at spec:117, the two `prefixE` at
spec:197-199.

Not named at all: both landed mutations. spec:255 says only "Landed mutations:
the program sampling another instance's family, and the biased program at the
manifest's level". Neither `five_card_row_alien_tableau` nor
`five_card_row_biased_at_manifest_level` occurs anywhere in the spec. A plan
written from the spec cannot state them, and the identifier this audit rejects
under B2 is one the spec never records.

Contradictions with the probe, both real.

1. spec:120-124 still lists `five_card_row_repeated_levelE` among the proposed
   declarations and still says that for the biased row "the file records the gap
   in a comment and not in a lemma". The probe result at spec:205-212 says the
   opposite on both counts, and the landing bears the probe out: there is no
   repeated `levelE`, and the biased gap is a compiled `Fail` at landing:462
   plus the lemma at landing:454. The "Proposed declarations" block is stale.
2. spec:157 lists `kim_centi_witness_rhoE` in the Cited objects table as a
   required object. K6 does not use it. The spec says so itself at spec:215 and
   `STATUS.md:280-285` says so again. The table is stale.

Two smaller items. spec:160 gives a line for `five_card_row_repeated` and none
for `five_card_row_biased`, which is at `manifest/pgg_analysis_manifest.v:766`.
And the reason recorded at `STATUS.md:183-191` for dropping the repeated
`levelE` includes one clause that does not distinguish the two rows, as set out
under M1(c).

All other cited line numbers were spot-checked and hold:
`five_card_committed` at `instances/kim2025/five_card_rows.v:123`,
`five_card_row_uniform_tableau` at `:286`, `five_card_row_uniform_rowE` at
`:295`, `kim_biased_family` at `instances/kim2025/five_card_models.v:435`,
`kim_centi_family` at `:443`, `five_card_uniform_family` at `:426`,
`kim_centi_witness_rhoE` at `:391`, `kim_centi_cut_distE` at `:402`,
`five_card_colour_view_leak_bound` at `:360`, `kim_deal_centi_lt` at
`instances/kim2025/five_card_kim.v:646`, `five_card_row_biased` at
`manifest/pgg_analysis_manifest.v:766`, `five_card_row_repeated` at `:776`.

## Fixes, pasteable

### Fix B1, landing:11-17, replacing seven lines with nine

```
(* threshold of the five-card scheme, so every coalition statement below is   *)
(* about a coalition of at most one of the five seats, and that restriction   *)
(* is the scheme's own: leak_view_set records the exact leakage of every one  *)
(* of the thirty-two reveal patterns, and sends to zero the patterns of at    *)
(* most one card. Not every statement below is a coalition statement. The     *)
(* other half of den Boer's claim, that the full reveal discloses the         *)
(* conjunction and nothing further about the two bits separately, is input    *)
(* privacy, and five_card_row_biased_leak_bound states a ceiling on it under  *)
(* the biased cut, at a reveal of any list of card positions.                 *)
```

### Fix B2, landing:404-406

```coq
(** A model built over one run does not sample another. The two models above
    are typed over this prefix's observed execution, so the two statements
    hold; a family typed over a different instance's observed execution is
    rejected where it is written. *)
Fail Definition five_card_row_s5_family : Tableau Sampled :=
  five_card_committed
    sample S5Analysis.rand_family.
```

### Fix S1, a comment above landing:422 and one above landing:440

Above `five_card_row_biased_prefixE`:

```coq
(** The same for the biased row. *)
```

Above `five_card_row_biased_modelE`:

```coq
(** The same for the biased row and the manifest's biased row. *)
```

### Fix S2, landing:453

```coq
(** The manifest's completion level for the biased row is AnalysisBridged.
    The program above reaches Sampled, so this equation and the rejected
    ascription below are the two halves of the level gap: the equation is a
    fact about the manifest's row and not about anything the program proves. *)
```

### Fix S3, three places

landing:469-476, the statement comment:

```coq
(** The law of the image of one starting position under the cut the repeated
    row samples is within two to the minus fortieth of the uniform law on the
    five card positions, in variation distance, at every starting position and
    every real field. Both laws are laws on card positions, so this is one
    position's endpoint marginal, and the statement names no seat, no set of
    seats and no secret. It is kim_deal_centi_lt read at the law the program
    names, through kim_centi_cut_distE. *)
```

landing:28-31, four header lines replacing four, spliced so that landing:32
continues unchanged with "places it at AnalysisBridged":

```
(* row stops there because the manifest does: what is proved of the           *)
(* seven-cut model is the endpoint marginal of one starting position          *)
(* under its cut law, which five_card_row_repeated_endpoint_lt carries        *)
(* beside the program rather than inside it. The biased row stops there       *)
(* although the manifest                                                      *)
```

landing:113-115, the Key results gloss:

```
(*   five_card_row_repeated_endpoint_lt                                       *)
(*                           == one starting position's endpoint marginal     *)
(*                              under the repeated row's cut law              *)
```

### Fix S4, landing:384-395

```coq
(** The biased row: the same prefix and the single cut at the same bias. The
    program stops at Sampled, one level below the AnalysisBridged the manifest
    records for this row, because the theorem that carries the manifest's
    level bounds a conditional mutual information and neither arm of certify
    takes a bound of that kind. The header says which request of each arm the
    development does not meet. The manifest's higher level for this row rests
    on that theorem and not on any payload of the program. *)
```

### Fix S5, the spec

1. Delete `five_card_row_repeated_levelE` from the "Proposed declarations"
   block at spec:120-124 and replace the paragraph with the probe's outcome:
   the repeated row's level is carried by the ascription
   `five_card_row_repeated_at_manifest_level`, the biased row's by
   `five_card_row_biased_levelE` beside a rejected ascription.
2. Delete `kim_centi_witness_rhoE` from the Cited objects table at spec:157,
   leaving `kim_centi_cut_distE` alone on its row.
3. Add both landed mutations to "Proposed declarations" by name:
   `five_card_row_s5_family`, the program sampling a family over another
   instance's observed execution, and
   `five_card_row_biased_at_manifest_level`, the biased program ascribed the
   manifest row's completion level.
4. In `STATUS.md:183-191`, drop the clause that the manifest checks the
   repeated equation itself, since the manifest checks the biased one too at
   `manifest/pgg_analysis_manifest.v:1778`. Keep the ascription argument.
5. Add `:766` for `five_card_row_biased` in the Cited objects table at
   spec:160.

### Fix N3, landing:110-112, the biased levelE gloss

```
(*   five_card_row_biased_levelE                                              *)
(*                           == the manifest's completion level for the       *)
(*                              biased row, which its program does not        *)
(*                              reach                                         *)
```

### Fix N7, two words

landing:19, "The row is written in the statement surface" becomes "The uniform
row is written in the statement surface".

landing:43, "No statement of the program is a theorem about this instance"
becomes "No statement of a program is a theorem about this instance", matching
`instances/pgl27/pgl27_rows.v:28`.

## What blocks the landing

- B1. Two sentences of the unchanged header are false after the change, and
  false in the direction of a scope overclaim: a reader is promised that every
  statement below is at most one seat and that input privacy is not stated
  here, and then meets a bound at any reveal pattern that is exactly Kim's
  input-privacy bound.
- B2. `five_card_row_alien_tableau` names a type fact by a figure of speech, in
  an identifier that will be committed.

Both are text-only edits. Neither touches a proof, a statement or a type, so
the file's assumption closure and compile behaviour are unaffected by either.

## What does not block the landing

S1, S2, S3, S4, S5, N1 through N8. S1 through S4 should go in before the commit
because they are the same size of edit as the two blocking ones and the file is
being rewritten anyway. S5 must go in before the plan, since the spec's
acceptance condition requires audit findings folded back into the note. N1, N2,
N4, N5 and N6 record judgements that the landing should keep as they are, and
exist so the plan does not relitigate them. N3, N7 and N8 are cosmetic.

VERDICT: NO-GO
