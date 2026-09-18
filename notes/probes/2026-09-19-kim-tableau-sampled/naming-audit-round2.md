# Naming and style audit, round 2: Kim's two five-card rows as Tableau programs

Date: 2026-09-19. Independent read-only audit, second round, final.

Nothing was compiled, no Rocq process was started, no file was edited. Only
this report was written. Every claim is backed by a file:line read of the
current tree or by a Python scan re-run in this session.

Subject: `notes/probes/2026-09-19-kim-tableau-sampled/five_card_rows_landing.v`
at commit be73f76, 580 lines. Before-fix copies read from
`notes/probes/2026-09-19-kim-tableau-sampled/history/`. Spec read at commits
134f07b and 32798db. References of the form `landing:N` are lines of the
current landing copy.

VERDICT: NO-GO. One blocking finding, three should-fix, all in the header and
all text-only. Everything else from round 1 is resolved and correct.

## 1. Round-1 findings, current state

| id | round-1 subject | state | current file:line |
|---|---|---|---|
| B1 | header promised at most one seat and no input privacy | RESOLVED | landing:11-19, the nine proposed lines byte-exact |
| B2 | `five_card_row_alien_tableau` | RESOLVED | landing:407, now `five_card_row_s5_family`, comment as proposed including "different instance's observed execution"; the probe's second mutation renamed `five_card_row_pgl27_family` at `kim_rows_probe.v:82`, which is consistent and was not asked for |
| S1 | two biased lemmas without a comment | RESOLVED | landing:425 and landing:444, both proposed comments word-for-word |
| S2 | bare noun phrase on `five_card_row_biased_levelE` | RESOLVED | landing:458-462, word-for-word, reflowed to the file's doc width without changing a word, confirmed by reading |
| S3 | seat, position and card drift | PARTIAL | three of four places fixed at landing:31, landing:123 and landing:479-485. The fourth, landing:384, was not in my round-1 list and is now a contradiction. See R2-S2 |
| S4 | biased program comment duplicated the header | RESOLVED | landing:392-398, word-for-word |
| S5 | spec stale and incomplete | RESOLVED, with two leftovers | all five items applied. See section 4 |
| N1, N2, N4, N5, N6 | judgements to keep | RESOLVED as recorded, nothing changed, and the spec records the judgements so they are not relitigated | spec "Kept, by the naming audit's judgement" |
| N3 | longer gloss for `five_card_row_biased_levelE` | OPEN, not applied | landing:119-121. Recommendation in section 5 |
| N7 | two singular-to-plural changes | OPEN, not applied | landing:21 and landing:52. Promoted to SHOULD-FIX, see R2-S4 |
| N8 | one `==` per paired name | OPEN, not applied | landing:111-118. Recommendation in section 5: do not apply |

The fix pass introduced no regression outside the header. I read every changed
passage in place and compared it against the before-fix copy line by line. No
statement, proof or type changed, which I confirmed independently from the diff
rather than from the prover's report: every hunk is inside a comment except the
one rename at landing:407.

## 2. The new eight-line passage, landing:43-50

Read cold, against `manifest/pgg_analysis_status.v:55-59` and against the
statement-comment rules.

The citation is exact. `manifest/pgg_analysis_status.v:55-59` is the comment on
`CompletionLevel`, and line 59 reads "AnalysisBridged adds a theorem about that
distribution and that observer", where "that distribution" and "that observer"
are the sample adapter and bridge added at `Sampled` on line 57-58. So "any
theorem about the sampled distribution and the observer" is a faithful reading:
the definition constrains the subject of the theorem and not its shape.

The substance is right and worth having. The soundness auditor's request is met.

Two problems in the wording, one of them blocking.

### R2-B1, BLOCKING, landing:43-44

> "those is proved at this instance. The two levels are one constructor
> admitted by two criteria."

"The two levels" has one available antecedent: the pair under discussion for
the preceding fifteen lines, `Sampled`, which the program reaches, and
`AnalysisBridged`, where the manifest places the row. Those are two distinct
constructors of `CompletionLevel` at `manifest/pgg_analysis_status.v:60-61`.
The sentence asserts that they are one constructor. That is false, and no
second reading rescues it: reading "levels" as "level assignments" gives two
assignments whose values are still two different constructors.

The content intended is that the single constructor `AnalysisBridged` has two
admission criteria. The sentence as written says the opposite of what the
passage exists to establish, in the one place a reader checks whether the
manifest overclaims. This is the same class of defect as round-1 B1, a false
sentence in the header, and it is in the passage I was asked to read hardest.

### R2-S1, SHOULD-FIX, landing:48-49

> "Both assignments are correct under their own definitions, and the manifest's
> level for this row is not an error."

The first clause is a statement about two definitions and is fine. The second
adds nothing to it, since two assignments correct under their own definitions
cannot be an error, and it is a defence of the project's own artefact rather
than a fact about the mathematics. The statement-comment rule keeps motivation
and defence out of the rendered body, and the rest of this header is uniformly
declarative. A header that says a thing "is not an error" also invites the
reader to ask who said it was.

What the passage needs instead of the reassurance is the reason, which is
checkable and is currently absent: the Tableau's criterion is the stricter of
the two. I verified this by reading both arms. `MkExactWitness` as used at
landing:320-324 carries independence of the static coalition observation from a
secret, stated at `sa_sampleP (amf_sample family R idx)`. `MkSpectralCert` as
used at `instances/pgl27/pgl27_rows.v:248-256` carries a marginal bound tied to
`sa_cut_dist (amf_sample family R idx)`, an ideal, a distance to it, and the
constancy of the coalition reader on the ideal. Each is a theorem about that
sampled distribution and that observer, which is exactly what line 59 of
`pgg_analysis_status.v` names. So an arm of `certify` always meets the
manifest's criterion, and the gap at this row is the manifest's criterion met
by a theorem no arm takes. That sentence does the auditor's work and is
falsifiable, where "is not an error" is neither.

### R2-S2, SHOULD-FIX, landing:384

S3 is partial. The repeated program's own comment still reads

> "What is proved of this model is the law of one seat's endpoint under its
> cut, stated below beside the program, and that is a statement about where a
> single starting position is sent"

which mixes the two words inside one sentence, and, ninety-five lines below,
the endpoint lemma's comment now says at landing:483 that the statement "names
no seat, no set of seats and no secret". The two comments in one file now
contradict each other about whether the bound mentions a seat. The partial fix
made this sharper than it was before, and it is my round-1 finding that was
under-specified, not the prover's application of it. `STATUS.md` records the
three places it changed and this is not one of them.

### R2-S3, SHOULD-FIX, landing:34

> `(* although the manifest                                                      *)`

A twenty-one character line in the middle of a flowing paragraph. Every other
short line in the header is a table row or a paragraph end. This is the tail of
my round-1 S3 block, which I wrote to splice into the following line without
touching it, and the raggedness is the cost of that choice. It should be
re-flowed, and since the paragraph needs re-flowing for R2-B1 anyway the two
fixes are one edit.

### R2-S4, SHOULD-FIX, landing:21 and landing:52, N7 promoted

The coordinator's reading is correct and I withdraw the cosmetic label.

landing:21 heads a paragraph that now runs to landing:50 and spends thirty
lines on all three rows, so "The row is written in the statement surface" is
wrong from its second sentence onward.

landing:52 is worse than ambiguous. "No statement of the program is a theorem
about this instance" opens a paragraph that then enumerates "the first two
statements", "the fourth statement" and "the fifth" at landing:55-58. That is
the uniform program's five-statement shape. The two Kim programs have two
statements each and no fifth, so the paragraph silently describes one program
while its subject reads as all of them. And at landing:58-59, "The security
mathematics reaches the row through that last payload alone" is true of the
uniform row and false read of the other two, whose mathematics reaches them
through nothing at all, both bounds sitting beside the program rather than in
it. `instances/pgl27/pgl27_rows.v:28` writes the plural form for the opening
sentence, and this file now needs it plus one scope word in the enumeration.

## 3. Mechanical re-run

All in Python with `\b` word boundaries, this session, on the current file.

- 580 lines. Zero lines over 80 bytes.
- Every non-doc comment line exactly 80 bytes, all 137 header lines and all
  section banners. Zero deviations.
- The banned-vocabulary scan, whole-word and case-insensitive: zero hits.
- Forbidden vernacular: no `Time`, no `Timeout`, no `Show`, no `Admitted`, no
  `Abort`, no `Axiom`, no `Parameter`, no `Hypothesis`, no `Variable`, no
  `Check`, and no `Print Assumptions` command. The one occurrence of that
  phrase is prose inside the pre-existing comment at landing:576, carried over
  unchanged from `instances/kim2025/five_card_rows.v:374`.
- Three `Fail` statements, at landing:407, landing:471 and the pre-existing
  landing:569. None carries an expected-failure marker and the pre-existing one
  does not either, so the file matches itself.
- Development words in identifiers or prose: zero. The rejected round-1 name
  survives only in `history/`, in `STATUS.md` and in the two audit reports,
  which are records and are correct to keep.
- Collision scan over 521 `.v` files, every file under `lib`, `protocol`,
  `groups`, `security`, `smc`, `reconstruct`, `instances` and `manifest` plus
  installed infotheo and mathcomp under
  `/Users/cheng-huiweng/Projects/coq/_opam/lib/coq/user-contrib`:
  `five_card_row_s5_family` zero hits, `five_card_row_pgl27_family` zero hits,
  and zero again for all eleven landed names and both mutation names.
- One prose line of the header is short mid-paragraph, landing:34. This is
  R2-S3 and is the only layout deviation anywhere in the file.

## 4. Does the spec plus the landing copy support a plan written verbatim?

Yes, once the four findings above are applied. All five S5 items are in.

- The level paragraph at spec:120-144 now describes the ascription and the
  lemma beside a rejected ascription, and no longer proposes a repeated
  `levelE`.
- Ledger row K5 now states both halves and names the mismatch.
- Both mutations are named: `five_card_row_s5_family` in its own bullet and
  `five_card_row_biased_at_manifest_level` in the `levelE` bullet.
- `kim_centi_witness_rhoE` is gone from the Cited objects table, which now
  carries `kim_centi_cut_distE` alone.
- `five_card_row_biased` has its line, `manifest/pgg_analysis_manifest.v:766`.
- The endpoint bound is worded for a starting position in the Problem section,
  in the declaration bullet and in soundness invariant 2, and the bullet adds
  the reason, that the file does not prove the identification of seats with
  card positions.
- A new Cited objects row for the completion levels at
  `manifest/pgg_analysis_status.v:55-59` was added and is accurate.
- The `ExactWitness`, `SpectralCert`, `SecurityPort` row gained per-object
  lines, `manifest/pgg_tableau.v:114`, `:131`, `:149`, which is an improvement
  over the round-1 "and above".

Two leftovers of the seat-to-position pass, neither wrong, both reading as
residue now that everything around them changed. The Cited objects row for
`kim_deal_centi_lt` still says "One seat's endpoint marginal under that
shuffle", and ledger row K6 still says "with the seat replaced by a pair of
seats". The first describes the upstream lemma in `five_card_kim.v` and the
second a probe mutation, so both are outside the landed text and outside this
work's scope to rename. Worth one sentence in the spec saying so, rather than
a silent inconsistency.

One forward dependency. The spec's "Folded in" bullet on the level gap
currently ends "and the manifest does not overclaim", which paraphrases the
landed sentence R2-B1 and R2-S1 replace. If those fixes go in, that bullet
should be reworded to match, to "the Tableau's criterion is the stricter of the
two, and the gap at this row is the manifest's criterion met by a theorem no
arm takes". In a design note, unlike a rendered statement comment, rationale is
in place, so this is a consistency edit and not a rule violation.

## 5. The three deferred notes

- N3, the longer gloss for `five_card_row_biased_levelE`. Apply. The
  declaration comment now carries the position, but the header is where a
  reader meets the asymmetry, and the two halves sit in different tables
  thirty-five lines apart, the ascription at landing:84-86 and the lemma at
  landing:119-121. Three lines become four. Text in section 6.
- N7. Apply, promoted to SHOULD-FIX as R2-S4 above.
- N8, one `==` per paired name. Do not apply. `instances/s5/s5_rows.v:97` and
  `:100-101` establish the shared-gloss form for a pair, and splitting these
  two would produce four near-identical glosses where two carry the same
  information. The current layout stacks the names where s5 puts them on one
  line, which is a difference of shape and not of content. Leave it.

## 6. Fixes, pasteable

Every boxed line below is exactly 80 bytes. Both blocks are drop-in
replacements with the same line count as what they replace, so no other line
of the header moves.

### Fix A, landing:21-50, thirty lines for thirty

Resolves R2-B1, R2-S1, R2-S3 and the first half of R2-S4.

```
(* The uniform row is written in the statement surface of                     *)
(* pgg_tableau_syntax.v over the statements of pgg_tableau.v: the prefix      *)
(* names the ideal function, drives the run in the encoded-run mode and       *)
(* adjoins the three run facts, one further statement adjoins the uniform     *)
(* rotation model, one adjoins the exact witness, and the last publishes the  *)
(* manifest row. The published row is the manifest's five_card_row_uniform,   *)
(* and the rowE lemma below holds by conversion, so the manifest's claim      *)
(* about this instance and the proof of it are one term. The manifest's two   *)
(* further five-card rows are written as programs below, and both stop at     *)
(* Sampled. The repeated row stops there because the manifest does: what is   *)
(* proved of the seven-cut model is the endpoint marginal of one starting     *)
(* position under its cut law, which five_card_row_repeated_endpoint_lt       *)
(* carries beside the program rather than inside it. The biased row stops     *)
(* there although the manifest places it at AnalysisBridged, because the      *)
(* theorem that carries it to that level, five_card_colour_view_leak_bound,   *)
(* bounds a conditional mutual information, and neither arm of certify        *)
(* carries a bound of that kind: the exact arm asks for independence of the   *)
(* static coalition observation from a secret, which the development states   *)
(* under the uniform cut and not under the biased one, and the spectral arm   *)
(* asks for a variation distance to an ideal cut on the shuffle group         *)
(* together with the constancy of a coalition's reading of that ideal, and    *)
(* neither of those is proved at this instance. AnalysisBridged is one        *)
(* constructor with two admission criteria. The manifest admits a row to it   *)
(* on any theorem about the sampled distribution and the observer, which is   *)
(* how manifest/pgg_analysis_status.v:55-59 defines the level and which a     *)
(* leakage bound meets. A program reaches it only through one of the two arms *)
(* of certify, each of which produces a theorem of that same kind, so the     *)
(* Tableau's criterion is the stricter of the two and the gap at this row is  *)
(* the manifest's criterion met by a theorem no arm takes. This is the        *)
(* situation instances/s5/s5_rows.v already records for s5_row_word.          *)
```

### Fix B, landing:52-67, sixteen lines for sixteen

Resolves the second half of R2-S4.

```
(* No statement of a program is a theorem about this instance. What the       *)
(* instance supplies it supplies inside a clause. In the uniform row the      *)
(* algebra, the ideal function, the input carrier, the layout, the decoder,   *)
(* the committers and the budget are the clause arguments of the first two    *)
(* statements; den_boer_assemble_valid and the three run facts are the        *)
(* obligations those same two statements ask for; the probability model is    *)
(* the argument of the fourth statement and one security record the payload   *)
(* of the fifth. The security mathematics reaches that row through the last   *)
(* payload alone, and through two named facts: five_card_static_obsE, which   *)
(* identifies the framework's direct computation of a coalition's view with   *)
(* the leakage space's colour reading encoded back into card positions, and   *)
(* five_card_viewS_indep, where leak_view_set gives that colour reading a     *)
(* leakage of zero at a pattern of at most one card. The sharpness annotation *)
(* pgl27_row_exact_tableau carries, that some coalition at the threshold      *)
(* already leaks, is not written here, because the closed forms of leak at    *)
(* two or more cards are proved positive nowhere.                             *)
```

### Fix C, landing:382-387, the repeated program's comment

Resolves R2-S2. One word changes, "seat" to "starting position", and the
sentence is re-flowed to the file's doc-comment width.

```coq
(** The repeated row: the prefix above and the seven-cut model at bias one
    hundredth. The program stops at Sampled, the level the manifest records
    for this row. What is proved of this model is the law of one starting
    position's endpoint under its cut, stated below beside the program, and
    that is a statement about where a single starting position is sent and
    not about what any set of seats reads, so no security payload follows
    it. *)
```

### Fix D, landing:119-121, three lines for four, N3

```
(*   five_card_row_biased_levelE                                              *)
(*                           == the manifest's completion level for the       *)
(*                              biased row, which its program does not        *)
(*                              reach                                         *)
```

### Fix E, the spec, two consistency edits

1. In the "Folded in" section, replace "Both assignments are correct under
   their own definitions, and the manifest does not overclaim" with "The
   Tableau's criterion is the stricter of the two, and the gap at this row is
   the manifest's criterion met by a theorem no arm takes", so the note and the
   landed header say the same thing.
2. Add one sentence to the Cited objects table or beneath it: the wording "one
   seat's endpoint marginal" in the `kim_deal_centi_lt` row and "a pair of
   seats" in ledger row K6 describe the upstream lemma and a probe mutation,
   both outside the landed text, and are deliberately left as their sources
   write them.

## 7. What blocks, what does not

Blocks: R2-B1 alone. A false sentence in the header, in the passage whose
purpose is to show that the manifest's level for this row is licensed.

Does not block, but should go in with it since Fix A carries three of them at
no extra cost: R2-S1, R2-S2, R2-S3, R2-S4, and N3 by Fix D.

None of the five touches a statement, a proof or a type. Applying all of them
leaves the file code-identical to the current landing copy, so the assumption
closure of the eleven declarations, ten three-axiom blocks and one closed
context, is unaffected and needs no re-derivation. A recompile of
`five_card_rows_landing.v` alone is enough to confirm the comments parse.

On fitness to replace the production file: not as it stands. With Fix A and
Fix B applied, and Fix C and Fix D recommended alongside,
`five_card_rows_landing.v` is fit to replace
`instances/kim2025/five_card_rows.v`. I will say that without qualification
once Fix A is in, since it is the only blocking item and it is thirty lines of
comment.

VERDICT: NO-GO
