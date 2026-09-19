# Audit 2: soundness of the prose and naming, PSL(2,11) landing probe after fix pass 1

**Verdict: NO-GO.** Two blocking findings, A1 and A2. Both are comment and
proof-local-name edits with no effect on any statement. Everything else in the
fix pass is sound, the collision scan is clean, the withdrawal of the corollary
is honestly recorded, and `opaque_vm_test.v` now isolates what `STATUS.md`
says it isolates.

Auditor: second round, independent of the fix pass and of both first-round
reports. Commit 31512bc. Files audited:
`notes/probes/2026-09-19-psl211-nogo-landing/psl211_spectral_constancy.v`,
`psl211_rows.v`, `opaque_vm_test.v`, `psl211_nogo_fidelity.v`, `_CoqProject`,
`STATUS.md`, against
`notes/20260919-psl211-spectral-nogo-landing-design.md` and the pre-fix copies
in `history/`.

## Findings

| ID | Class | Quoted content | Evidence | Exact replacement |
|---|---|---|---|---|
| A1 | BLOCKING | `psl211_spectral_constancy.v` header: "In a proof script a leading C is a fiber cardinality, L a mass, U a mass at the group-uniform law, E a reader identification and H a hypothesis taken as given; ... and a trailing digit is an index and never a value." | The file breaks its own sentence three ways. (i) `psl211_alldecks_constancy_false_supp` names a mass `Ht0`, where `H` is not a mass letter and the trailing `0` is the value the mass takes, which the sentence's last clause forbids. (ii) The same object, a mass at the group-uniform law, is `U` in `psl211_alldecks_constancy_false_close` (`Ut`, `Uf`) and `L` in `psl211_dealt_constancy_false` (`Lt`, `Lf`) and in `psl211_blockline1_law_neq` (`Lj0`, `Lj1`). All six have the shape `fdistmap ... ((`U psl211_G_pos) : R.-fdist cutT) <view> = ...`. No `L` in the file is a mass at any other law, so the distinction the sentence draws is drawn nowhere. (iii) `psl211_alldecks_constancy_false_close` names three chain steps `T1`, `T2`, `T3` with a letter the sentence does not declare. | Three renames plus one sentence. Renames: in `psl211_alldecks_constancy_false_supp`, `Ht0` to `Lt` at its `have` and at its single use in `move: Hfge; rewrite -Hlaw Ht0 => Hle.`; in `psl211_dealt_constancy_false`, `Lt` to `Ut` and `Lf` to `Uf` at their `have` and inside `Hz`; in `psl211_blockline1_law_neq`, `Lj0` to `Uj0` and `Lj1` to `Uj1` at their `have` and inside `Hz`. No name collides inside its proof. Sentence, padded to the header box, replacing lines 78 to 83: see "A1, the replacement text" below. |
| A2 | BLOCKING | `psl211_rows.v` header: "so the field asks for more than the secret-independence this row claims and its failure is not leakage." | "is not leakage" asserts that no leakage occurs. Nothing in the sentence, and nothing in `psl211_spectral_constancy.v`, proves that. What proves it is a separate theorem about the all-decks law: `psl211_alldecks_view_secrecy` of this same file, whose first conjunct is independence of the chirality at `#\|C\| < 6`, proved from `psl211_alldecks_view_indep` of `instances/psl211/psl211_models.v` through the witness. The spec's own wording is the weaker and accurate one: "So its failure is no proof of leakage: under the all-decks law three seats read nothing about the chirality, which is the exact arm's theorem." The over-claim also hides that the field fails at a pair that *does* move the secret, `psl211_alldecks_constancy_false`, which is the case that needs the independence theorem. | Four lines, padded to the 80-column box, replacing lines 60 and 61: see "A2, the replacement text" below. |
| A3 | SHOULD | `psl211_alldecks_no_small_eps_cert` docstring: "the obligation of conclude pins that number to cert_eps cert" | True today, `manifest/pgg_tableau.v` `RepricePayload` giving `cert_eps cert = odflt (cert_eps cert) (c R)`. Stage A of `notes/probes/2026-09-19-tableau-extensions/pgg_tableau.v` weakens it to `cert_eps cert <= odflt (cert_eps cert) (c R)`, and the sentence becomes false in a permanent file when that lands. `PortProp` is `SpectralPropAt cert (odflt (cert_eps cert) (c R))` in both versions, and `publish` carries that same `c`, so the number a row publishes is `odflt (cert_eps cert) (c R)` in both. | Full docstring under "A3, the replacement text" below. It is true under both obligations, because equality implies the inequality, and it keeps both claims the caller asked for. |
| A4 | SHOULD | `psl211_spectral_constancy.v` header: "The second failure moves no secret, so no reading of these refutations gives leakage." | A non-sequitur. "These refutations" is plural and includes the failure between the two chiralities, whose two run arguments differ in the secret. That the *second* failure moves no secret says nothing about the first. What rules out leakage is the next sentence's `psl211_alldecks_static_indep`, which the "so" pre-empts. | Folded into the A5 block below. |
| A5 | SHOULD | `psl211_spectral_constancy.v` header: "The field fails between the two chiralities of one deck description, and the equation it asserts is false again at a pair of run arguments of one chirality differing in the block line alone, psl211_blockline1_law_neq." | The field is a predicate of an ideal law. Neither clause names the ideal. Both cited facts, `psl211_alldecks_constancy_false` and `psl211_blockline1_law_neq`, are at `` `U psl211_G_pos `` and nothing else. A reader who stops at this paragraph reads "the field fails", unqualified, which is the statement soundness invariant 2 bars. The rest of the header corrects it, four paragraphs later. | Nine lines replacing lines 21 to 29, under "A4 and A5, the replacement text" below. It fixes A4 in the same block. |
| A6 | SHOULD | `psl211_blockline1_law_neq` docstring: "at chirality true the deck descriptions psl211_perdeck_deal and psl211_blockline1_deal" | "Deck description" names two different objects in the same landing. The header uses it for the four-coordinate run argument, "The run argument is a whole deck description: one of the two chiralities, one of the 132 block lines ... and two labellings", which is `psl211_inputT = bool * psl211_deal`. Here it names `psl211_deal = ('I_132 * {perm 'I_6} * {perm 'I_6})`, the three public coordinates alone. The statement quantifies over neither: it names the two pairs `(true, psl211_perdeck_deal)` and `(true, psl211_blockline1_deal)`. | Replacement docstring under "A6, the replacement text" below. It names what the statement names and drops the second sense of the word. |
| A7 | SHOULD | `STATUS.md`, ledger row N3: "GO, with the third refutation withdrawn" | The spec's decision 3 says "The corollary the third audit asked for lands: the constancy field refuted from the pair of deck descriptions of one chirality, so that 'the failure does not need the secret to move' is a statement at the field's type." The landing reverses that decision. The reversal is recorded under the ledger and under "Proofs: what needed a fix", but not in "What in the spec or in SRC turned out wrong", which is where a reader looks for reversed spec decisions, and the row's verdict cell still reads GO. | Change the N3 verdict cell to "Deviation from decision 3, recorded below" and add a sixth item to "What in the spec or in SRC turned out wrong": "**The spec's decision 3 is reversed.** The corollary it asked for had the statement of `psl211_alldecks_constancy_false` character for character, so the refutation at one chirality is carried at the law's type by `psl211_blockline1_law_neq` and not at the field's type." |
| A8 | NOTE | `psl211_spectral_constancy.v` header: "The psl211_blockline1_ prefix names the comparison between block line zero and block line one at one chirality" | Six of the nine declarations with that prefix name objects at block line one alone and not a comparison: `psl211_blockline1_deal`, `_view`, `_test`, `_seq`, `_raw_count`, `_fiber`. Only `_raw_countE`, `_seqE` and `_law_neq` carry the comparison. | "The psl211_blockline1_ prefix names block line one and the comparison with block line zero at one chirality, as psl211_perdeck_ of instances/psl211/psl211_models.v names the comparison between the two chiralities at one deck description." |
| A9 | NOTE | `coalition_reading_constancy` docstring: "the field is\n    at least constancy in the secret; where the run\n    argument carries public data as well" | The SA11 edit was inserted without re-wrapping. One line of the docstring is 43 characters where its neighbours are in the seventies. | Re-wrap the five lines of that sentence to the file's width. No wording change. |
| A10 | NOTE | `psl211_rows.v`: "this instance's own marginal bound", against `psl211_spectral_constancy.v`: "this instance's single-card marginal bound" | Two names for one object, `psl211_marginal_bound`, across the two files the landing copies. The constancy file's phrase is the precise one, since `profile_eps_psl211` is about the single-card pushforward. | In `psl211_rows.v` write "single-card marginal bound". |
| A11 | NOTE | `psl211_spectral_constancy.v` header: "the reading multiplicity diagnostics are recorded in notes/probes/2026-09-19-psl211-sc-const/." | A permanent file pointing into `notes/probes/`. It is the provenance of an explicitly uncompiled measurement, and the header block is `(* ... *)` and therefore not rendered by coqdoc, so the statement-comment rule's bar on probe names in docstrings does not reach it. Recorded so the next reader does not have to re-decide it. | None. |
| A12 | NOTE | `STATUS.md`: "The stale `.vo`, `.vos`, `.vok`, `.glob` and `.aux` of the old file name were removed after the new name compiled; they are ignored build products, not records." | Read against the same record's "none is deleted, because nothing under `notes/probes/` is deleted". The distinction between a build product and a record is drawn explicitly and is reasonable, and `psl211_spectral_nogo.v.timelog` was kept. Flagged only so the rule's owner sees that a deletion under `notes/probes/` happened under a stated exception. | None. |
| A13 | NOTE | The two non-rendered comments under `psl211_alldecks_no_small_eps_cert` | Judgement asked for in question 1b. Both belong in the file and neither belongs in the header. See question 1b below. | Trim the first to one sentence once A3 is applied, text below. |

## A1, the replacement text

Replacing header lines 78 to 83. Every line is exactly 80 bytes.

```
(* the comparison between the two chiralities at one deck description. In a   *)
(* proof script a leading C is a fiber cardinality, U a mass at the           *)
(* group-uniform law, L a mass at the ideal, E a reader identification, T a   *)
(* step of an inequality chain and H every other named fact; the suffix names *)
(* the coordinate the quantity is taken at, t and f the chirality and j0 and  *)
(* j1 the block line; and a trailing digit is an index and never a value.     *)
```

Checked against every `have` and every intro pattern in the file after the
three renames. `C` covers `Ct`, `Cf`, `Cj0`, `Cj1`. `U` covers `Ut`, `Uf` in
`_close`, `Ut`, `Uf` in `psl211_dealt_constancy_false` and `Uj0`, `Uj1` in
`psl211_blockline1_law_neq`. `L` covers the one mass at the ideal, `Lt` in
`_supp`. `E` covers `Et`, `Ef`, `Ej0`, `Ej1`. `T` covers `T1`, `T2`, `T3`.
Every remaining named fact begins with `H`. The only digits left in a proof
script are the block-line indices `j0` and `j1`, the chain indices `1`, `2`,
`3`, the witness `g0` and the names built on it, and the three conjunct names
of an `and3P` split, which index the seat. None of them names a value.

## A2, the replacement text

Replacing `psl211_rows.v` lines 60 and 61 with four lines. Every line is
exactly 80 bytes. Line 60 is unchanged, and lines 59 above and 62 below stay
as they are.

```
(* different laws, psl211_blockline1_law_neq, so the field asks for more than *)
(* the secret-independence this row claims, and its failure is no proof of    *)
(* leakage: under the all-decks law a coalition of at most five of the twelve *)
(* seats reads nothing about the chirality, psl211_alldecks_view_secrecy.     *)
```

Checked against the statement of `psl211_alldecks_view_secrecy`, which is in
this file at `(HC : (#|C| < 6)%N)` and whose first conjunct is independence of
`psl211_alldecks_secret R`. "At most five of the twelve seats" is the phrase
this header already uses in its opening paragraph, so no new word enters the
file. `psl211_alldecks_view_indep` of `instances/psl211/psl211_models.v` is
the alternative citation, and it is the lemma the witness at line 177 applies,
but the row's own theorem is the one the sentence is about.

The sentence four lines above, "a row over this model that publishes its
certificate's own bound publishes at least 1/660", needs no change. It is
conditional on the row publishing its certificate's own bound and so survives
the weakened `conclude` of A3 unchanged.

## A4 and A5, the replacement text

Replacing `psl211_spectral_constancy.v` header lines 21 to 29 with nine lines.
Every line is exactly 80 bytes.

```
(* At the group-uniform ideal the field fails between the two chiralities of  *)
(* one deck description, and the equation it asserts is false again at a pair *)
(* of run arguments of one chirality differing in the block line alone,       *)
(* psl211_blockline1_law_neq. The second failure moves no secret, so the      *)
(* field asks for constancy in public data and not for secrecy alone. What a  *)
(* coalition of at most five of the twelve seats reads about the chirality    *)
(* under the all-decks law is psl211_alldecks_static_indep of                 *)
(* instances/psl211/psl211_models.v, which says it reads nothing, exactly, at *)
(* every real field, and that is the theorem the published row carries.       *)
```

## A3, the replacement text

Full docstring of `psl211_alldecks_no_small_eps_cert`. Every line is at most
80 bytes.

```
(** psl211_alldecks_no_small_eps_cert — no spectral certificate over the
    all-decks run of the twelve-card chirality instance has its shuffle bound
    epsilon added to itself strictly below the reciprocal 1/660 of the group
    order, so every such certificate has an epsilon of at least 1/1320, the
    value 1/1320 itself not excluded. A row publishes
    odflt (cert_eps cert) (c R) at its own reprice coordinate c, and cert_eps
    cert is the shuffle bound epsilon twice, so a row over this model that
    publishes its certificate's own number publishes at least 1/660. The
    obligation of conclude bounds the published number below by cert_eps
    cert, so no row over this model publishes less. This fixes from below
    what the spectral arm can publish at this model. It says neither that the
    arm is unavailable here nor anything about what a coalition of at most
    five seats reads. *)
```

Checked against both obligations. Today `RepricePayload` gives
`cert_eps cert = odflt (cert_eps cert) (c R)`, which bounds the published
number below by `cert_eps cert`. Stage A gives
`cert_eps cert <= odflt (cert_eps cert) (c R)`, which bounds it below by the
same value directly. A row that never concludes carries `no_reprice`, so
`c R = None` and `odflt (cert_eps cert) None = cert_eps cert`. In all three
cases the published number is at least `cert_eps cert`, and the theorem gives
`cert_eps cert >= 1/660`. `PortProp` and `publish` are the same in both
versions of `manifest/pgg_tableau.v`, so nothing else moves.

## A6, the replacement text

```
(** psl211_blockline1_law_neq — the run arguments (true, psl211_perdeck_deal)
    and (true, psl211_blockline1_deal) send the group-uniform cut law to two
    different laws on what seats 0, 1 and 2 read. This is the equation the
    constancy field asserts, at a pair of run arguments carrying the same
    secret, and it is false, so the field's failure at the all-decks
    parameters does not need the chirality to move: it is already a failure of
    constancy in the public block line. *)
```

## Question 1: every sentence the fix pass wrote or rewrote

I diffed each of the four files against its `history/*.2026-09-19-before-fix1`
copy and read every changed sentence against the statement under it.

### 1a, the rows header's last claim

The compiled facts are these. `psl211_blockline1_law_neq` refutes the equation
the constancy field asserts at a pair of run arguments carrying one chirality.
`psl211_alldecks_constancy_false` refutes it at a pair carrying two. Neither
says anything about what a coalition learns from the law the row is about. The
theorem that does is separate and is `psl211_alldecks_view_secrecy` of
`instances/psl211/psl211_rows.v`, proved from `psl211_alldecks_view_indep` of
`instances/psl211/psl211_models.v` through the witness at line 177, with
`psl211_alldecks_static_indep` of the same file as the framework-side form the
constancy file's header cites.

So "is no proof of leakage" is the accurate wording and "is not leakage" is
not, and the accurate wording needs the theorem named beside it or it is a bare
assertion. The exact text that should stand is the four-line block under "A2,
the replacement text" above. This is finding A2 and it is blocking.

### 1b, the certificate theorem's docstring and the two comments under it

The docstring's obligation clause is A3 and the replacement is above.

The two non-rendered comments. The first, "Argued and not compiled: the
exclusion survives a weaker conclude ...", belongs in the file and at this
theorem. It is the warrant for the docstring's claim, it is local to one
declaration, it names no probe and no plan, and the header block is not where a
reader checks one theorem's reach. Once A3 is applied it is partly restated by
the docstring, so trim it to:

```
(* Argued and not compiled: the proposition a row carries is
   SpectralPropAt cert c, a variation distance bounded above by c, so an
   obligation weakened from an equality to cert_eps cert <= odflt (cert_eps
   cert) (c R) could only let a row publish a number larger than cert_eps,
   never a smaller one. *)
```

The second, "The excluded range of epsilon is bounded above. The header records
why the larger range is occupied and that the occupancy is argued and not
compiled.", also belongs in the file. Its first sentence is a scope fact about
this theorem that the docstring does not carry. Its second sentence is a
pointer, and a pointer is what keeps the occupancy argument written once, which
is what the first-round naming finding S3 asked for. Moving either comment to
the header would undo that.

### 1c, coalition sizes

Every sentence is right about which size it means. `profile_k_psl211` is `6`
and `psl211_perdeck_coalition` is `[set i | val i \in [:: 0; 1; 2]]`.

- `psl211_rows.v`, "Six is the privacy threshold the derived profile declares,
  so every statement below is about a coalition of at most five of the twelve
  seats": correct.
- `psl211_rows.v`, "it fails at three seats at the group-uniform ideal,
  psl211_dealt_constancy_false": correct, that refutation spends
  `psl211_perdeck_coalition`.
- `psl211_rows.v`, "the coalition of seats 0, 1 and 2": correct.
- constancy header, "a coalition of fewer than profile_k seats": correct, that
  is the quantifier of `coalition_reading_constancy`.
- constancy header, "What a coalition of at most five of the twelve seats reads
  about the chirality under the all-decks law is psl211_alldecks_static_indep":
  correct, that lemma's premise is `(#|C| <= 5)%N`.
- constancy header, "three seats see a reading that one chirality's encoder
  deck reaches under exactly one cut and the other reaches under none":
  correct, `psl211_dealt_raw_countE`.
- `psl211_perdeck_coalition_le3`, "has at most three seats": correct.
- `psl211_perdeck_coalition_below_k`, "those three seats meet the threshold
  premise of both security arms, the derived profile declaring six": correct.
- `psl211_alldecks_no_small_eps_cert`, "nor anything about what a coalition of
  at most five seats reads": correct.

### 1d, soundness invariants 2 to 5

- Invariant 2, nothing says the arm cannot be closed here. Carried, with one
  gap: the header sentence of A5 says "The field fails" with no ideal named,
  and a reader who stops there reads it as unconditional. Everything else is
  explicit, from the file name down to "It says neither that the arm is
  unavailable here" in the certificate theorem's docstring and "What is
  excluded is a range of epsilon and not the arm" in the rows header.
- Invariant 3, nothing says or implies leakage. Carried. The strongest
  leakage-adjacent sentence, in `psl211_perdeck_fiber_true0`, now ends "at this
  fixed deck description, which is not the law the row is about". The only
  defect on this axis runs the other way, A2, which denies leakage more
  strongly than anything compiled.
- Invariant 4, nothing says the all-decks failure is unrelated to the secret.
  Carried. `psl211_alldecks_constancy_false`'s docstring keeps "A change of
  secret is always also a change of the laid deck here, the chirality selecting
  the table the block line indexes." A4's non-sequitur is the one sentence that
  leans toward the barred reading, and the A5 block removes it.
- Invariant 5, the numbers 360, 600 and 10/11. Absent from both `.v` files.
  Machine-checked with a regular expression over both files.

### 1e, `psl211_blockline1_law_neq`'s description in both files

The rows-file clause, "the coalition of seats 0, 1 and 2 reads the group-uniform
cut under two different laws", checks out clause by clause.

- "the coalition of seats 0, 1 and 2": the statement's `psl211_perdeck_coalition`
  is `[set i : seatT | val i \in [:: 0; 1; 2]]` of
  `instances/psl211/psl211_models.v`.
- "two deck descriptions of one chirality": both sides are at `true`.
- "differing in the block line alone": `psl211_perdeck_deal` is
  `(ord0, 1%g, 1%g)` and `psl211_blockline1_deal` is
  `(@Ordinal 132 1 isT, 1%g, 1%g)`, equal in the two labellings.
- "reads the group-uniform cut under two different laws": the statement is a
  `!=` between two `fdistmap (static_coalition_obs ...) ((`U psl211_G_pos))`,
  which is the law of what the coalition reads when the cut is group-uniform.

The constancy-file docstring is accurate but uses "deck description" for the
three-coordinate deal, which is finding A6.

## Question 2: the withdrawal of the corollary

Ledger row N3 asked for "The three refutations at the field's type" with
evidence "`psl211_alldecks_sc_const_false`, the corollary from
`psl211_samechir_law_neq`, and `psl211_dealt_sc_const_false`". The landing
delivers two of the three. The third is carried at the law's type by
`psl211_blockline1_law_neq` and not at the field's type.

Is soundness invariant 4 still honestly carried? Yes. The invariant asks that
the failure not be said to be unrelated to the secret, and that it occur both
between the chiralities and at one chirality. Both occurrences are compiled:
`psl211_alldecks_constancy_false` for the first, `psl211_blockline1_law_neq`
for the second. The second is one `exact:` from the field's type, since
`psl211_perdeck_coalition_below_k` discharges the only premise, and
`psl211_alldecks_constancy_false`'s docstring states the fact in words with the
lemma named. Nothing in either file claims a refutation at the field's type
that is not there.

`STATUS.md`'s record of the withdrawal is true on every checkable claim.

- "had a statement character for character that of
  `psl211_alldecks_constancy_false`": verified against
  `history/psl211_spectral_nogo.2026-09-19-before-fix1.v`. Both are
  `~ coalition_reading_constancy psl211_alldecks_params ((`U psl211_G_pos) : R.-fdist cutT)`
  under `(R : realType)`.
- "removed from the landing copy, with its `Print Assumptions` and its fidelity
  restatement": the name occurs nowhere in `psl211_spectral_constancy.v`,
  `psl211_rows.v`, `psl211_nogo_fidelity.v` or `_CoqProject`. The fidelity file
  has 48 `Print Assumptions` and two restatements, matching the record.
- "its text is kept in `history/`": present.
- "the rows header and the file header now cite that lemma where they cited the
  corollary": both cite `psl211_blockline1_law_neq`.

The one thing the record does not do is list the reversal where a reader looks
for reversed spec decisions. That is finding A7.

## Question 3: names after the fix

**File name.** `psl211_spectral_constancy.v`. It states what the file is about,
the constancy field, and claims nothing the file does not prove. It carries the
instance prefix every file in `instances/psl211/` carries and a subject noun.
The first-round blocking finding B1 is closed.

**`psl211_alldecks_no_small_eps_cert` and `psl211_alldecks_no_zero_eps_cert`.**
Both state their proposition and both carry the condition that makes them true.
`_eps_` is the tree's word for a certificate's number, as in
`kim_centi_cert_eps_lt`. The trailing `0` that fought the file's own convention
is gone. Closed.

**The proof-local scheme.** Not followed. This is finding A1, blocking.

**Collision scan.** Python `re` with `\b`, over 234 `.v` files: the production
tree, `notes/probes/2026-09-19-kim-spectral-landing/` and
`notes/probes/2026-09-19-tableau-extensions/`. Names scanned:
`psl211_alldecks_no_small_eps_cert`, `psl211_alldecks_no_zero_eps_cert`,
`psl211_spectral_constancy` (the module name, since `_CoqProject` maps
`instances/psl211` to the single logical root `pgg_smc`),
`coalition_reading_constancy`, `spectral_cert_reading_constancy`,
`psl211_blockline1_law_neq`, `psl211_blockline1_deal`,
`psl211_alldecks_constancy_false` and its four suffixed forms,
`psl211_dealt_constancy_false`, `psl211_alldecks_constancy_set0`. **Zero hits
for every name.** The scan script is in `audit-2/` only as the inline program
recorded here; no file outside `audit-2/` was written.

## Question 4: the selective header index

The index names thirteen entries: two definitions and eleven results. Against
the file's 46 declarations that is a cut of two thirds, which is where the
tree's larger files sit.

Every name the rows header cites is in the index:
`coalition_reading_constancy`, `psl211_dealt_constancy_false`,
`psl211_alldecks_constancy_false`, `_supp`, `_close`,
`psl211_alldecks_no_small_eps_cert`, `psl211_alldecks_no_zero_eps_cert`,
`psl211_blockline1_law_neq`. The four the index adds are the ones a paper would
cite or a reader needs to parse the rest: `spectral_cert_reading_constancy`,
which is the only evidence that the restated proposition is the record's field;
`psl211_alldecks_cert_ideal_close`, which is where the certificate's
identification field enters; `psl211_alldecks_constancy_false_word584`; and
`psl211_alldecks_constancy_set0`, which is the reason the refutations are not
vacuous. The two definitions are the proposition itself and
`psl211_blockline1_deal`, which the reader needs to read
`psl211_blockline1_law_neq`.

Nothing is stale. Every one of the thirteen names resolves to a declaration in
the file. No entry names the withdrawn corollary or either old certificate
name. The entry for `psl211_alldecks_constancy_false_word584` was rewritten,
"the field is false at every ideal within eps of the 584-letter word shuffle's
cut law", and matches the statement's two hypotheses. The entry for
`psl211_alldecks_constancy_set0` no longer names
`psl211_alldecks_static_obs_set0`, which is now unindexed, so the first-round
note SA14 about an index entry naming a declaration of another file is closed
by removal.

**The occupancy argument is written once**, in the "Not claimed" paragraph of
the header. What sits above the certificate theorem is a two-sentence pointer.
The duplicated passage the first-round naming finding S3 quoted is gone.

**Length.** 126 lines of header on 1012 lines of file, down from 174. Forty-two
of the 126 are the index. The inventory that can drift is the index itself and
four cross-file name citations: `psl211_alldecks_static_indep`,
`psl211_alldecks_uniq`, `profile_eps_psl211` and `pgl27_word_view_const`. All
four exist today, verified by grep, and all are greppable rather than
positional now that the line range is gone. The "Names." paragraph is the only
new inventory and it is the one A1 falsifies.

## Question 5: `opaque_vm_test.v`

Yes, after the fix. I compiled it through the shared lock, exit 0, from a copy
at `audit-2/opaque_check.v`. Its three sentences print, in order:

- `Eval simpl`: `count (eq_op^~ 3) tbl`, with `count` unreduced and `tbl`
  folded.
- `Eval cbv`: the unfolded `count` fixpoint applied to `tbl`, still folded.
- `Eval vm_compute`: `1`.

`STATUS.md` describes exactly that: "`simpl` leaves the count unevaluated with
`tbl` folded, `cbv` unfolds `count` and leaves `tbl` folded, and `vm_compute`
prints `1`." The file's own comment is accurate too. The pre-fix lemma, which
the first-round soundness finding SA7 showed could be closed by `by []` through
kernel conversion and therefore isolated nothing, is gone and its text is in
`history/`. The file is not in `_CoqProject`, as the record says.

## Question 6: first-round items, one line each

| Item | State |
|---|---|
| SA1, the warning passage | Closed. `STATUS.md` now says the warning follows the first infotheo `Require` beside `fingroup`, names the three files of `instances/psl211/` that already emit it, and records that the pre-fix sentence was false in both halves. The two probe files `audit-soundness/warn_with.v` and `warn_without.v` are present. |
| SA2, the rows header citing the corollary | Closed differently. The auditor proposed keeping both names. The fix pass withdrew the corollary and cites `psl211_blockline1_law_neq` alone, which is the stronger fix. |
| SA3, the marginal-error sentence | Closed. The auditor's replacement is in the header verbatim, naming `profile_eps_psl211` of `instances/psl211/psl211_profile.v`, whose statement `sw_bound_eps (psl211_marginal_bound R) = 0%R` I checked. |
| SA4, the self-contradictory exclusion sentence | Closed, and it introduced A3. The new sentence is unambiguous today and is the one Stage A falsifies. |
| SA5, the occupancy of the larger range | Closed. The header now prices the exhibited certificate: `cert_eps` near 4, `var_dist` at most 2, "publishes a number no pair of laws can exceed and bounds nothing". |
| SA6, `psl211_dealt_view`'s uncompiled claim | Closed. The measured claim is gone, replaced by the compiled one from `psl211_dealt_raw_countE`. |
| SA7, `opaque_vm_test.v` | Closed. See question 5. |
| SA8, the line range and the probe row reference | Closed. The range is gone from the header, the probe-row reference went with the comment S3 removed. |
| SA9, the timelog figures | Closed. `STATUS.md` re-measured and added a provenance paragraph saying the figures come from `rocq compile -time` stdout of the fix-pass compile and not from a `.v.timelog`, and why the four stale timelogs are neither regenerated nor deleted. |
| SA10, `psl211_perdeck_fiber_true0` | Closed. Applied verbatim. |
| SA11, `coalition_reading_constancy` | Closed, with a ragged line left behind, finding A9. |
| SA12, `sc_Hd` | Closed. Applied verbatim. |
| SA13, `psl211_blockline1_row_size` | Closed. Applied verbatim, and `_corow_size` with it. |
| SA14, the index claim in `STATUS.md` | Closed differently. The claim is gone because the index is now selective, and the entry that named a foreign declaration is gone too. |
| SA15, the reverse closure of `pgg_collusion_bound` | Closed. `STATUS.md` now says "among its reverse-dependants" and records the forward-closure error. |
| B1, the file name | Closed. Renamed to `psl211_spectral_constancy.v`, recorded in `STATUS.md` with the reason `s5_nogo.v` is not a precedent here. |
| S1, the two certificate names | Closed. |
| S2, the exhaustive index | Closed. See question 4. |
| S3, the occupancy written twice | Closed. The declaration copy is the auditor's one-line replacement. |
| S4, the line range | Closed. |
| S5, `psl211_dealt_raw_countE`'s provenance sentence | Closed. The second sentence is dropped, as the auditor's preferred option. |
| S6, one proof-local scheme | **Not closed.** The scheme is stated and the file does not follow it. Finding A1. |
| S7, `_row_size` and `_corow_size` | Closed. |
| S8, the barred two-character token in `STATUS.md` | Closed. Zero occurrences in the three `.v` files, `_CoqProject` and `STATUS.md`, machine-checked. |

## Question 7: the statement-comment rule and the vocabulary rule

**Rendered docstrings.** Every `(** ... *)` block in the two files was scanned
for "used by", "TODO", "deferred", "plan", "probe", "SRC", `notes/`, a
`file.v:line` reference, "key lemma", "headline" and "machine-check". **No
hits.** The rendered bodies carry a fact and a position and no status, no
effort estimate, no proof strategy and no provenance. Proof strategy lives in
`(* ... *)` comments beside the tactics, which is where the rule puts it.

**Fact then position.** Sampled across the file, the position sentence is there
and it is falsifiable by a domain reader. `psl211_perdeck_coalition_below_k`
says what the premise is for. `psl211_alldecks_cert_ideal_close` says why the
certificate's identification field makes the epsilon an epsilon against this
law. `psl211_alldecks_constancy_set0` says the refutations are not vacuous.
`psl211_alldecks_no_small_eps_cert` says what the theorem does not say. The one
position sentence that does not follow from its fact is A4, in the header.

**One word per concept.** Two breaks. "Deck description" for two objects,
finding A6. "Own marginal bound" against "single-card marginal bound", finding
A10. "Constancy" is used for the field throughout both files and in the file
name, with no synonym anywhere.

**Line width.** No line of `psl211_spectral_constancy.v`, `psl211_rows.v`,
`opaque_vm_test.v` or `psl211_nogo_fidelity.v` exceeds 80 bytes. Checked on
bytes, not characters, so the em-dashes in the docstring headings are counted
at their real width.

**Barred vocabulary.** Zero occurrences of "apex", of "gate" and its
inflections as a whole word, of "posit" and its inflections, and of the
two-character token for a distance, across the three `.v` files, `_CoqProject`
and `STATUS.md`. Machine-checked.

**Metaphor words for mathematical results.** Zero hits for "escape", "beats",
"smash", "dodge" and the attack words in the two `.v` files. "No-go" survives
only in the probe directory name, in `psl211_nogo_fidelity.v` and in the
logical path `psl211_nogo_landing`, none of which lands.

**Invariant 1.** No `Admitted`, no `Abort`, no `Axiom` in any of the three
compiled files. The two `Fail` sentences in `psl211_rows.v` are the pre-existing
recorded failures.

## Question 8: placement under the later `tableau/` directory

The proposal already places the file, "`psl211_spectral_constancy.v` names
`SpectralCert`, so it belongs in `instances/psl211/tableau/` and moves there in
this batch", and of its seven roles the file fits the seventh,
`*_checks.v`, recorded failures, because what it records is that the spectral
arm's fifth field fails here and that no certificate below an epsilon exists.
No eighth role is needed. The one thing worth deciding in that batch is size:
only four of the 46 declarations name `SpectralCert`, so the forty-two that do
not could stay in `instances/psl211/` as instance mathematics, with
`psl211_checks.v` holding `spectral_cert_reading_constancy` and the three
certificate results, which would keep a thousand-line file out of a directory
whose point is that a reader can see the phases at a glance.

## What I did not check

- The mathematics. The brief ruled it out and I took it as given: the field
  proposition against the record's field both ways, the four mutations, the
  numbers, the assumption counts and the comment-stripped equality of the rows
  copy with production.
- I did not recompile `psl211_spectral_constancy.v`, `psl211_rows.v` or
  `psl211_nogo_fidelity.v`. The only compile I ran is the copy of
  `opaque_vm_test.v`, exit 0. My three renames under A1 are therefore proposed
  and not compiled, though each is a proof-local rebind with all uses listed.
- `instances/psl211/psl211_endpoints.v` was not compiled, not edited and not
  opened.
- The timing figures in `STATUS.md`. I read the provenance paragraph and did
  not re-measure.
- The SRC probe `notes/probes/2026-09-19-psl211-sc-const/` and the N5
  disposition table row by row. I checked only that no name in the landing files
  is a name the table marks as staying in the probe.
- The manifest and the paper. The brief puts them outside this landing.
- The first-round audit reports' own reasoning beyond the finding rows I
  needed for question 6.
