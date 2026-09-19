# Naming, style and statement-comment audit of the PSL(2,11) spectral landing

**NO-GO** for "these files may be copied into the permanent tree as they are".

One blocking finding. It is not a proof defect and not an identifier inside the
file. It is the file name, which asserts in every citation the one sentence the
file's own header and the design note's soundness invariant 2 refuse to assert.
Everything else is a should-fix or a note.

Scope: `notes/probes/2026-09-19-psl211-nogo-landing/` (PROBE below), read in
full: `psl211_spectral_nogo.v` (1076 lines, 47 declarations), `psl211_rows.v`,
`psl211_nogo_fidelity.v`, `STATUS.md`. Compared against
`notes/20260919-psl211-spectral-nogo-landing-design.md`, the source probe
`notes/probes/2026-09-19-psl211-sc-const/`, `reconstruct/s5_nogo.v`,
`instances/psl211/psl211_models.v`, `instances/psl211/psl211_rows.v`,
`instances/psl211/psl211_alldecks.v`, `instances/pgl27/pgl27_mixing.v`,
`instances/pgl27/pgl27_rows.v`, `instances/kim2025/five_card_rows.v`,
`manifest/pgg_tableau.v`, and the Kim landing's own naming audit
`notes/probes/2026-09-19-kim-spectral-landing/naming-audit.md`.

Read-only. No compiler was run, no git command was run, no file outside this
one was touched. Scans were done in Python, never with `grep -E '[[:<:]]'`,
which matches nothing on this machine.

---

## Findings

| ID | Weight | Quoted content | Rule or precedent | Proposed fix |
|---|---|---|---|---|
| B1 | BLOCKING | File name `psl211_spectral_nogo.v`, against the file's own header `(* Not claimed. The spectral arm is not shown unavailable at this instance. *)` | Design note soundness invariant 2, "Nothing says the spectral arm cannot be closed at PSL(2,11)". The precedent `reconstruct/s5_nogo.v` earns its suffix: "This file proves there is none." | Rename to `psl211_spectral_constancy.v`, or to `psl211_constancy_nogo.v` if the suffix is kept. Both are collision-free. |
| S1 | SHOULD | `psl211_alldecks_no_spectral_cert`, `psl211_alldecks_no_spectral_cert0` | The names drop the condition that makes them true. Tree idiom for a certificate's number is `_eps_`: `kim_centi_cert_eps_lt`, `kim_biased_cert_eps_lt2`. The trailing `0` also fights this file's own convention, where a trailing digit is a value: `psl211_perdeck_fiber_true0` | `psl211_alldecks_no_small_eps_cert`, `psl211_alldecks_no_zero_eps_cert`. Both collision-free. |
| S2 | SHOULD | The header index lists all 47 declarations and nothing else, in 106 of the header's 174 lines | Every declaration already carries a `(** ... *)` docstring. At this size the tree switches to a selective index: `psl211_models.v` indexes 49 of 73. Exhaustive indexes in the tree top out at `pgl27_rows.v`, 31 of 31 | Cut to the names cited from outside the file: `coalition_reading_constancy`, `spectral_cert_reading_constancy`, the three refutations, `_supp`, `_close`, `_cert_ideal_close`, the two certificate results, `_word584`, `psl211_alldecks_constancy_set0`. About twelve entries. |
| S3 | SHOULD | The occupancy argument appears twice: header, "the uniform law on the whole of `{perm 'I_12}` reads the same at every deck description, its variation distance from `` `U psl211_G_pos `` is `2 * (1 - 660/12!)`", and again above `psl211_alldecks_no_spectral_cert`, "The uniform law on the whole of `{perm 'I_12}` satisfies the constancy field, its variation distance from `` `U psl211_G_pos `` is `2 * (1 - 660/12!)`" | CLAUDE.md, "Long exposition goes at the file header, anchored to nothing. A tutorial pinned to one declaration restates results it does not track and drifts against them" | Keep the header copy. Replace the declaration copy with one line: "The excluded range of epsilon is bounded above. The header records why the larger range is occupied and that the occupancy is argued and not compiled." |
| S4 | SHOULD | Header, "`psl211_alldecks_uniq` at `instances/psl211/psl211_alldecks.v:421-429`" | CLAUDE.md bars line numbers in statement comments. The range is accurate today, `Lemma` at 421 and `Qed` at 429, and will not stay accurate | Drop the range. The name is unique in the tree and greppable: "`psl211_alldecks_uniq` of `instances/psl211/psl211_alldecks.v`". |
| S5 | SHOULD | `psl211_dealt_raw_countE` docstring, "This is the count comparison of the Plan B probe read at one numeral instead of over the whole multiplicity vector." | A rendered statement comment carries the fact and its position, not provenance. "Plan B" is a project-internal plan label a reader of the permanent file cannot expand | "One numeral of the reading multiplicity vector already separates the two chiralities, where the probe compared the whole vector." Better, drop the second sentence: the first already states the fact. |
| S6 | SHOULD | Proof-local hypotheses. `psl211_blockline1_law_neq` has `Cb0 : #\|...\| = 1` and `Cb1 : #\|...\| = 0`, while `psl211_alldecks_constancy_false_close` and `psl211_dealt_constancy_false` have `H0 : #\|...\| = 0` and `H1 : #\|...\| = 1`, and `psl211_alldecks_constancy_false_supp` has `Hcard1` | One word per concept, file-wide. A trailing digit is the value in three proofs and the block line in the fourth. STATUS.md records the swap, "with the numeral now naming the block line rather than the value, which is why the pairs are also swapped in reading order", which is the confusion stated rather than removed. Three schemes for one fiber cardinality | One rule: the letter is what it is, the suffix is the coordinate value. `C` cardinality, `L` mass, `U` mass at the uniform law, `H` hypothesis. Suffix `t` and `f` for the chirality, `j0` and `j1` for the block line, `j` being the tree's own letter for the block index in `case: x => b [[j ph] pc]`. So `H0`, `H1` become `Ct`, `Cf`, `Hcard1` becomes `Cf`, and `Cb0`, `Cb1` become `Cj0`, `Cj1`, and likewise `Lb0`, `Lb1` become `Lj0`, `Lj1`, `Eb0`, `Eb1` become `Ej0`, `Ej1`, `Hb0`, `Hb1` become `Hj0`, `Hj1`. Proof-local names cannot collide. |
| S7 | SHOULD | `psl211_blockline1_row_size` docstring, "block line one of the chirality's table has six positions", over a statement that fixes chirality true | The counterpart `psl211_perdeck_row_size (b : bool)` of `psl211_models.v` quantifies over the chirality, so "the chirality's" reads as "either", which this statement does not say. `_corow_size` inherits it through "its complement" | "block line one of the chirality-true table has six positions", and "the complement of that row has the other six". |
| S8 | SHOULD | `STATUS.md` writes the barred two-character distance token four times, at the rename record and twice more | The token is barred everywhere the project writes, source and prose alike. The record can be made without spelling it | Rewrite the rename record as: "SRC's `psl211_samechir_law_neq` named its eight proof-local hypotheses with bare capitals L, C, E and H suffixed by the digits 0 and 1, and the L form with digit one spells a term this project bars for a distance, L being a word length here." The later mention at the incidental-findings entry can read "`manifest/pgg_analysis_manifest.v:684` writes, of the S_5 word path, a distance named with the barred two-character token." |
| N1 | NOTE | The fourteen `psl211_blockline1_*` names, of which seven are not tied to block line one: `_view` is a fixed reading, `_test` and `_testE` take `(sq t : seq nat)`, `_raw_count` takes `sq`, `_fiber`, `_fiberE` and `_massE` take an arbitrary deck description `x` | The prefix names the comparison, not the argument, exactly as `psl211_perdeck_*` does in `psl211_models.v`, where `psl211_perdeck_fiber` takes a chirality and `psl211_perdeck_raw_count` a whole deck. The numeral is a parameter value, which has precedent in `psl211_alldecks_constancy_false_word584`, and it sits mid-name, where the file's value-digits sit last | Keep the names. Add one sentence to the header's Definitions block, above the block-line entries: "The `psl211_blockline1_` prefix names the comparison between block line zero and block line one at one chirality, as `psl211_perdeck_` names the comparison between the two chiralities at one deck description." Details below. |
| N2 | NOTE | `coalition_reading_constancy` and `spectral_cert_reading_constancy` are quantified over `(A : PGGAlgebraic) (E : ExecutionParams A)` and carry no instance prefix, in a file destined for `instances/psl211/` | They are framework-level and belong beside `SpectralCert` in `manifest/pgg_tableau.v`. The design note puts the manifest out of scope, so the location is forced and not chosen. Unprefixed helpers in an instance file have precedent: `fdistmap_head1` and `rho_from_words_weighted1` in `instances/kim2025/five_card_exec.v` | Names are right, keep them. One header sentence: "The first two declarations are framework-level and name no instance. They belong beside `SpectralCert` and sit here because this landing does not edit the manifest." |
| N3 | NOTE | `fdistmap_point_condE` | No library duplicate exists. infotheo's `fdistmapE` is `fdistmap b = \sum_(a in A \| a \in g @^-1 b) p a`, the preimage as a set membership, and this file needs `\sum_(x \| f x == v) p x`, the form a support hypothesis is spent in. Verified across `user-contrib/infotheo` and `user-contrib/mathcomp` | Keeping it local is the right judgement. No change. |
| N4 | NOTE | The file declares no `Section`. Four boxed banner comments divide it | `s5_nogo.v` has `Section Kernel` and `psl211_models.v` has `Section psl211_dealer`, both because they share `Variable`s. This file shares none, so a section would only add a name | No change. |
| N5 | NOTE | `seatT`, `cardT`, `cutT`, `viewT` | The only whole-word hits of any name in this file against the production tree. All four are `Local Notation` here and `Local Notation` at every hit, so neither declaration is visible outside its own file | No change. |
| N6 | NOTE | The planned move into `instances/psl211/tableau/` | `notes/2026-09-19-124500-instance-tableau-directory-proposal.md` names the files there after the Tableau phases, plus `*_certificates.v` and `*_checks.v`, and says "`psl211_spectral_nogo.v` names `SpectralCert`, so it belongs in `instances/psl211/tableau/` and moves there in this batch". A refuted field is closest to the `*_checks.v` role, "recorded failures, mutations, `realises_expected`" | Nothing to change now. The name under B1 is correct for `instances/psl211/`, and the move batch should decide whether it becomes the instance's checks file or the proposal gains a row for it. |
| N7 | NOTE | `leq_var_dist` in place of SRC's `var_dist_point_le` | Verified at `user-contrib/infotheo/probability/variation_dist.v:51`, `Lemma leq_var_dist (p q : R.-fdist A) x : \| p x - q x \| <= d( p , q ).` Same statement, same arity | Correct as done. |
| N8 | NOTE | Lines over 80 bytes | None, in any of the three `.v` files, measured on byte length in Python | Confirmed. |
| N9 | NOTE | `STATUS.md` uses "headline" nine times | The word is meta, and CLAUDE.md bars it from rendered statement bodies. `STATUS.md` is a probe record and not a rendered statement body, and no `.v` file in PROBE contains it | Acceptable where it is. Do not carry it into the permanent file. |
| N10 | NOTE | The rows-file header cites eight names of the new file | All eight exist with exactly that spelling: `coalition_reading_constancy`, `psl211_dealt_constancy_false`, `psl211_alldecks_constancy_false`, `psl211_alldecks_constancy_false_supp`, `psl211_alldecks_constancy_false_close`, `psl211_alldecks_no_spectral_cert`, `psl211_alldecks_no_spectral_cert0`, `psl211_alldecks_constancy_false_blockline` | Confirmed. |

---

## B1, the blocking finding, in full

The file's header says, under its own heading:

```
(* Not claimed. The spectral arm is not shown unavailable at this instance.   *)
(* What is excluded is a range of epsilon, and the range of larger epsilon    *)
(* is occupied                                                               *)
```

and a source comment above the certificate theorem says:

```
(* So the spectral arm is not unavailable at this instance, and
   what this theorem excludes is a range of epsilon and not the arm. *)
```

and the design note's second soundness invariant says:

```
2. Nothing says the spectral arm cannot be closed at PSL(2,11).
```

A file named `psl211_spectral_nogo.v` says it. The name is what travels: it
goes into `_CoqProject`, into the header of `psl211_rows.v`, into the manifest's
path list when the tableau move happens, and into the paper. The header's
qualification does not follow it into any of those places.

The precedent does not extend. `reconstruct/s5_nogo.v` opens

```
(* This file proves there is none.  The entire no-go reduces to ONE kernel    *)
(* fact about the natural permutation module P = GF(5)^5 of S_5:              *)
```

so its suffix names a proved impossibility of the thing the file is named after.
Here the proved impossibility is narrower than the file's name: no certificate
over the all-decks model carries a shuffle bound epsilon under `1/1320`. The
arm itself is not excluded, and the file says so three times.

Two honest names, both collision-free as whole words over the production tree,
`legacy/`, the installed infotheo and the installed mathcomp, and both free as
file names anywhere in the repository.

- `psl211_spectral_constancy.v`. Names the subject and leaves the verdict to
  the header, which is what every other file in `instances/psl211/` does:
  `psl211_models.v`, `psl211_mixing.v`, `psl211_alldecks.v`, `psl211_blocks.v`,
  `psl211_closure.v`, `psl211_rows.v` are all subject nouns. First choice.
- `psl211_constancy_nogo.v`. Keeps the `s5_nogo.v` suffix and moves it onto the
  thing actually refuted, which is the constancy field and not the arm. Second
  choice, for whoever wants the suffix kept.

Either way the probe directory name and `STATUS.md` keep `nogo`, because they
record the work and not the result. The logical path `psl211_nogo_landing` in
`_CoqProject` is probe-local and does not land.

---

## N1, the block-line family, in full

The question was whether `blockline1` tells a reader the truth, and whether the
numeral reads as an index of a lemma. Both answers are yes and no respectively,
and the rename from `psl211_samechir_*` was an improvement, because `samechir`
carries a project-local abbreviation nobody can expand from the name.

What the family is. `psl211_models.v` holds `psl211_perdeck_*`, sixteen names
for the comparison of the two chiralities at one fixed deck description, with
`psl211_perdeck_deal := (ord0, 1%g, 1%g)`, block index zero. The new file holds
the mirror comparison, two deck descriptions at one fixed chirality, with
`psl211_blockline1_deal := (@Ordinal 132 1 isT, 1%g, 1%g)`, block index one. The
fourteen new names mirror the sixteen old ones one for one: `_deal`, `_view`,
`_test`, `_testE`, `_seq`, `_row_size`, `_corow_size`, `_seqE`, `_raw_count`,
`_raw_countE`, `_fiber`, `_fiberE`, `_massE`, `_law_neq`. The parallel is exact
and is the strongest argument for the names.

Why the numeral is safe. This file's value-digits are trailing:
`psl211_perdeck_fiber_true0` says the fiber at chirality true is empty, and
`psl211_alldecks_no_spectral_cert0` says the epsilon is zero. The block-line
digit is not trailing. It is bound to the noun in front of it, and reads the way
mathcomp's `expr1` or `perm1` reads, as "at one". The tree already names a
parameter value this way in `psl211_alldecks_constancy_false_word584`, the
584-letter word.

Where it misleads. Seven of the fourteen are not about block line one.
`psl211_blockline1_view` is the reading giving cards 3, 2 and 4, and its own
docstring says "The deck laid at `(true, psl211_perdeck_deal)` reaches it under
exactly one cut and the deck laid at `(true, psl211_blockline1_deal)` under
none". So the reading the name attaches to block line one is the one block line
one never produces. `_test`, `_testE`, `_raw_count`, `_fiber`, `_fiberE` and
`_massE` are parametric and belong to neither block line.

Why that is still not a rename. `psl211_models.v` has the identical shape:
`psl211_perdeck_view` is reached under no cut at chirality true, and
`psl211_perdeck_fiber` and `psl211_perdeck_raw_count` take the coordinate as an
argument. A reader of this tree already reads `psl211_X_view` as the reading of
comparison X. Renaming the family to `psl211_blockline_*` without the numeral
would lose which block line the deal fixes and would gain nothing the header
cannot state in one sentence.

Recommendation: keep the fourteen names, add the header sentence given in the
table above. If the user prefers the numeral gone, the collision-free set is
`psl211_blockline_deal`, `_view`, `_test`, `_testE`, `_seq`, `_row_size`,
`_corow_size`, `_seqE`, `_raw_count`, `_raw_countE`, `_fiber`, `_fiberE`,
`_massE`, `_law_neq`, and `psl211_blockline_deal` would then need its docstring
to say the index is one.

---

## The two constancy names

`coalition_reading_constancy` is the right name, and "constancy" is the tree's
one word for this field. Four production rows files write the same phrase:

- `instances/s5/s5_rows.v:66`, "is the constancy of a coalition's reading of the
  ideal cut in"
- `instances/pgl27/pgl27_rows.v:244`, "the constancy of a coalition's reading of
  the ideal cut in the dealt secret,"
- `instances/kim2025/five_card_rows.v:41`, "together with the constancy of a
  coalition's reading of that ideal, and"
- `instances/psl211/psl211_rows.v:41`, "constancy field asks that a coalition's
  reading of the ideal cut not vary"

and `manifest/pgg_tableau.v` writes "the constancy of a" and "its ideal
constancy" three times. The identifier is that phrase compressed, in the tree's
own word order. The record field is `sc_const`, which is the same word
abbreviated, not a second word.

The name drops the restriction to coalitions below `profile_k`. That follows the
settled Kim precedent: `five_card_static_obs_const` drops it too, and the Kim
audit's B5 fix put the restriction in the prose rather than the name. This
file's docstring carries it, "a coalition of fewer than `profile_k` seats reads
the law `ideal` on cuts the same way whatever the run argument", so the pair is
consistent with what was settled last week.

`spectral_cert_reading_constancy` states that the field of a given certificate
is that proposition, and `Proof. exact: sc_const cert. Qed.` makes a change to
the record surface here. The name is a bare noun phrase where mathcomp would
expect a suffix on a lemma, and the shared stem with the definition could be
read as a second proposition rather than a fact about the first. It is readable
as it stands and the shared stem is what makes the link visible, so this is not
a finding. If the user wants the mathcomp shape, `spectral_cert_constancyP` is
free.

---

## Family consistency of the seven names asked about

Mode, then property, then qualifier, is held everywhere:

| name | mode | property | qualifier |
|---|---|---|---|
| `psl211_alldecks_constancy_false` | alldecks | constancy false | none |
| `psl211_alldecks_constancy_false_blockline` | alldecks | constancy false | the pair spent |
| `psl211_alldecks_constancy_false_supp` | alldecks | constancy false | the class of ideals |
| `psl211_alldecks_constancy_false_close` | alldecks | constancy false | the class of ideals |
| `psl211_alldecks_constancy_false_word` | alldecks | constancy false | the cut law |
| `psl211_alldecks_constancy_false_word584` | alldecks | constancy false | the cut law, at its parameter |
| `psl211_dealt_constancy_false` | dealt | constancy false | none |
| `psl211_alldecks_no_spectral_cert` | alldecks | no certificate | none, see S1 |
| `psl211_alldecks_cert_ideal_close` | alldecks | a certificate's ideal is close | none |

One irregularity. The qualifier slot carries three different kinds of thing: the
pair of run arguments spent (`_blockline`), the class of ideals quantified over
(`_supp`, `_close`), and the cut law the ideal is measured from (`_word`,
`_word584`). A reader cannot tell from the suffix which kind it is. The header
index says which in every case, so this is readable, and no rename improves it
without lengthening all five. No finding.

`word584` is readable. 584 is the letter count of the word shuffle, and the
statement makes it visible, `@rho_from_words_weighted R 10 2 584 psl211_moves`.
The docstring says "the cut law of the 584-letter word shuffle". The precedent
for a numeral naming a parameter in a name is `pgl27_reprice39` and
`five_card_reprice_inv25`.

`_close` is the right suffix for the quantitative form. It names the hypothesis
`var_dist ... <= eps`, which is the certificate's own `sc_close` field, and the
tree's word for that field is "close". `psl211_alldecks_cert_ideal_close` uses
it for the same hypothesis, so the two `_close` names mean one thing.

---

## Collisions

Whole-word scan in Python over the 47 declaration names.

- Production tree, every `*.v` outside `notes/`, 207 files: zero hits. The four
  `Local Notation` names `seatT`, `cardT`, `cutT` and `viewT` hit
  `instances/psl211/psl211_alldecks.v`, `instances/psl211/psl211_models.v`,
  `instances/psl211/psl211_rows.v`, `instances/pgl27/pgl27_profile_privacy.v`,
  `security/pgg_leakage_witness.v`, `security/pgg_trace_secrecy.v`,
  `reconstruct/dealer_privacy.v`, `reconstruct/transitivity_privacy.v` and
  `protocol/pgg_functionality.v`, and every hit is itself a `Local Notation`.
  No declaration is visible outside the file that makes it.
- Kim landing probe `notes/probes/2026-09-19-kim-spectral-landing/`: zero hits.
- Extensions probe `notes/probes/2026-09-19-tableau-extensions/`: zero hits.

This reproduces STATUS.md's own claim of zero collisions over 583 files, by an
independent scan.

Every name proposed in this audit was scanned the same way over the production
tree, `legacy/`, `user-contrib/infotheo` and `user-contrib/mathcomp`, and over
the repository's file names: `psl211_spectral_constancy`, `psl211_constancy_nogo`,
`psl211_alldecks_no_small_eps_cert`, `psl211_alldecks_no_zero_eps_cert`, and the
fourteen `psl211_blockline_*` alternatives. All clean.

---

## Vocabulary

The three `.v` files are clean of every barred term. All four bans were scanned
with case-insensitive whole-word patterns, the metaphor for the file that
centralizes headline results, the metaphor for a logical relation in each of its
four inflections, the verb for an unproved assumption in each of its four
inflections, and the two-character distance token. Zero hits. No narrative or metaphor word for a mathematical
result appears in any identifier or any comment. "Close", "reaches", "spends",
"carries", "pays" and "price" are used for distances and for bounds, which is
the tree's existing register and not metaphor for a result.

`STATUS.md` spells the barred distance token four times, which is S8.

One pre-existing production occurrence is outside this landing and is already
recorded in `STATUS.md` as incidental: `manifest/pgg_analysis_manifest.v:688`
writes the token, followed by "distance one from group uniform", about
the S_5 word path. It belongs to whoever owns the manifest this week, and the
Kim landing owns it. Not this landing's finding, and the wording of the record
is S8's second half.

---

## Statement comments

Read against CLAUDE.md, "Statement comments in prover code and math documents",
including "The second sentence: domain position".

What the file does right, and it is most of it:

- Every one of the 47 declarations has a rendered `(** ... *)` docstring that
  states the fact and its position. `psl211_blockline1_deal` gives both in two
  clauses, "block line one, both labellings the identity. It differs from
  `psl211_perdeck_deal` in the block line alone, a public coordinate of the run
  argument that carries no secret."
- Every currency is labelled. `psl211_alldecks_constancy_false_word584` says
  which distance is which: "the 2^-40 is the whole information-theoretic price
  of that replacement, while the eps is a certificate's own distance field."
- Proof strategy is in non-rendered `(* ... *)` comments and never in a
  docstring. The `congr1` argument above `psl211_alldecks_constancy_false`, the
  `in_set` and not `inE` note above `psl211_alldecks_raw_viewE`, the `@` form
  note above `psl211_alldecks_no_spectral_cert0`, and every `Local Opaque`
  justification are all placed correctly.
- What a thing omits is given with its reason. The dealt statement's docstring
  says "The statement rules out one named ideal and no certificate, this tree
  carrying no dealt-mode sample adapter through which a certificate's ideal
  could be pinned to it."
- `psl211_alldecks_constancy_set0` states the vacuity boundary declaratively:
  "the field is not false for the trivial reason that its quantifier over
  coalitions admits a reading no law can make constant."
- No status marker, no effort estimate, no author attribution, no "key lemma",
  no "used by", anywhere.
- Type-honest throughout at the one place it is easy to slip. The header
  distinguishes the shuffle bound epsilon from the published number, "no
  certificate carries a shuffle bound epsilon strictly below 1/1320, and a row
  publishing its certificate's own bound publishes at least 1/660". That is
  correct, because `cert_eps cert = sw_bound_eps (sc_b cert) + sw_bound_eps
  (sc_b cert)` in `manifest/pgg_tableau.v`, so the published number is twice the
  shuffle bound and the two numbers differ by a factor of two, as written.

The header. 174 lines, of which 4 to 66 are exposition and 68 to 173 are the
index. The exposition is exposition a reader needs: it names the domain frame
per run mode, says what the run argument is in each, prices the two distances,
and carries the "Not claimed" paragraph that keeps the result inside its scope.
Keep it, less the line number of S4. The index is an inventory, S2, and the
occupancy paragraph is duplicated at a declaration, S3.

---

## The rows-file header

The landing's copy replaces thirteen lines of production with twenty-nine. The
replacement is true sentence by sentence and cites eight names that all exist
with exactly that spelling, checked by extracting the declaration set from the
new file and matching. One word per concept holds between the two files:
"constancy field", "run argument", "run modes", "deck description",
"group-uniform ideal", "shuffle bound epsilon" and "marginal bound" are the
same words in both. The rows header says "a coalition below the privacy
threshold" where the new file says "a coalition of fewer than `profile_k`
seats", which is the same restriction in two registers, and the new file itself
uses both, so this is not drift.

The arithmetic in the rows header is right. "at every ideal closer than 1/1320
to the group-uniform law, `psl211_alldecks_constancy_false_close`" matches the
lemma's two hypotheses, `var_dist ... <= eps` and `eps + eps < 1/660`. "so a row
over this model that publishes its certificate's own bound publishes at least
1/660" matches `cert_eps`, which is the shuffle bound twice.

---

## Rename table

Nothing here is required except B1. S1 is a should-fix and the rest of the table
is optional.

| old | new | weight | reason |
|---|---|---|---|
| `psl211_spectral_nogo.v` | `psl211_spectral_constancy.v` | BLOCKING | the old name asserts the design note's invariant 2 denies; the new one names the subject as every other file in the directory does |
| `psl211_alldecks_no_spectral_cert` | `psl211_alldecks_no_small_eps_cert` | SHOULD | the old name drops the condition; `_eps_` is the tree's word for a certificate's number, per `kim_biased_cert_eps_lt2` |
| `psl211_alldecks_no_spectral_cert0` | `psl211_alldecks_no_zero_eps_cert` | SHOULD | same, and the trailing `0` currently reads as a value on this file's own convention, `psl211_perdeck_fiber_true0` |
| `H0`, `H1` in `psl211_alldecks_constancy_false_close` | `Ct`, `Cf` | SHOULD | S6, the letter is what it is and the suffix is the coordinate |
| `H0`, `H1` in `psl211_dealt_constancy_false` | `Ct`, `Cf` | SHOULD | same |
| `Hcard1` in `psl211_alldecks_constancy_false_supp` | `Cf` | SHOULD | same |
| `Cb0`, `Cb1`, `Lb0`, `Lb1`, `Eb0`, `Eb1`, `Hb0`, `Hb1` in `psl211_blockline1_law_neq` | `Cj0`, `Cj1`, `Lj0`, `Lj1`, `Ej0`, `Ej1`, `Hj0`, `Hj1` | SHOULD | same, `j` being the tree's letter for the block index |
| the fourteen `psl211_blockline1_*` | the fourteen `psl211_blockline_*` | optional | only if the user wants the numeral gone; N1 recommends keeping it and adding a header sentence instead |
| `spectral_cert_reading_constancy` | `spectral_cert_constancyP` | optional | only if the user wants the mathcomp lemma shape; the current name is readable |

Every name in the "new" column was scanned for collisions and is clean.

---

## What I did not check

- Nothing was compiled. Every claim about what a statement says is read off the
  source, not off a goal. `STATUS.md` reports 23.6 s and exit 0 and I did not
  reproduce it.
- I did not verify the proofs. Where I traced a proof it was to judge a comment
  against the statement, not to check the mathematics.
- I did not verify `STATUS.md`'s N6 timing table, its N7 comment-stripped
  character count of 4485, or its N9 count of 50 `Print Assumptions` results.
  Those belong to the soundness audit.
- I did not verify the numeric content of the tables `psl211_dealt_decktbl`
  holds, nor the two `vm_compute` counts, nor `psl211_blockline1_seq`.
- I did not read the paper, so I cannot say which of the 47 names it will cite.
  S2's proposed index cut is drawn from what the rows header cites, which may be
  narrower than what the paper needs.
- I did not read the Kim landing's or the extensions probe's `.v` files beyond
  scanning them for collisions with these 47 names, and I read the Kim naming
  audit only for the conventions it settled.
- I did not check whether renaming the file breaks a path cited in a note, a
  plan or the paper. `STATUS.md`'s N11 table covers the reverse closure of the
  `.v` files and not of the prose.
