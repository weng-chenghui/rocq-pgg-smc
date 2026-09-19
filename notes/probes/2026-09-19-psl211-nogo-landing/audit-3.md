# Audit 3: soundness of the prose and naming, PSL(2,11) landing probe after fix pass 2

**Verdict: GO.** `psl211_spectral_constancy.v` and the header-only copy of
`psl211_rows.v` may be copied into the permanent tree. No blocking finding.
Four SHOULD findings and eight NOTEs follow. Everything fix pass 2 wrote is
true of the statements under it, with one wording slip (F2) and one sentence
that fix pass 2 chose not to make robust although it made its neighbour robust
(F1).

Auditor: third round, independent of the fix passes and of the three earlier
reports. Commit ed4105f. Files read in full:
`notes/probes/2026-09-19-psl211-nogo-landing/psl211_spectral_constancy.v`,
`psl211_rows.v`, `STATUS.md`, `audit-2.md`, the `history/*before-fix2*` copies,
and the spec `notes/20260919-psl211-spectral-nogo-landing-design.md`. Production
files read: `instances/psl211/psl211_rows.v`, `psl211_models.v`,
`psl211_alldecks.v`, `psl211_profile.v`, `psl211_closure.v`,
`manifest/pgg_tableau.v`, `manifest/pgg_analysis_manifest.v`, `_CoqProject`,
`Makefile`, and `notes/probes/2026-09-19-tableau-extensions/pgg_tableau.v` and
`psl211_rows.v`, `notes/probes/2026-09-19-kim-spectral-landing/psl211_rows.v`
and `STATUS.md`. Nothing was compiled.

## Findings

| ID | Severity | Quoted content | Evidence | Exact replacement |
|---|---|---|---|---|
| F1 | SHOULD | `psl211_spectral_constancy.v` header, lines 35 and 36: "The obligation of conclude is cert_eps cert = odflt (cert_eps cert) (c R), and cert_eps is that epsilon twice, so every" | True of `manifest/pgg_tableau.v`, whose `RepricePayload` is `cert_eps cert = odflt (cert_eps cert) (c R)`. False of `notes/probes/2026-09-19-tableau-extensions/pgg_tableau.v`, whose `ConcludePayload` is `cert_eps cert <= odflt (cert_eps cert) (c R)`. Fix pass 2 rewrote the docstring of `psl211_alldecks_no_small_eps_cert` to "The obligation of conclude bounds the published number below by cert_eps cert" precisely so that it survives that change, and left the header pinned to the equality. One file now describes one obligation two ways, and the weaker description is the true one. | Two lines, each exactly 80 bytes, replacing lines 35 and 36. Line 34 above and line 37 below stay as they are. See "F1, the replacement text". |
| F2 | SHOULD | `psl211_alldecks_raw_viewE` docstring: "This is psl211_perdeck_raw_viewE of psl211_models.v with the deck description left free instead of fixed at the deal psl211_perdeck_deal." | Fix pass 2 changed "fixed to psl211_perdeck_deal" to "fixed at the deal psl211_perdeck_deal" in the same pass that glossed a deck description as a whole run argument. Under that gloss a deck description cannot be fixed at a deal: the two have different types. What production's `psl211_perdeck_raw_viewE` fixes is the deal coordinate, its `(b : bool)` staying free, and what the landing lemma frees is exactly that coordinate, its `(x : psl211_inputT)` being whole. | Replace the third and fourth lines of the docstring. See "F2, the replacement text". |
| F3 | SHOULD | `psl211_spectral_constancy.v` header, line 76: "argument and a deal is its three public coordinates." | The type checks out. `ex_inputT psl211_alldecks_params` reduces to `psl211_inputT = bool * psl211_deal` and `psl211_deal = ('I_132 * {perm 'I_6} * {perm 'I_6})`, so the run argument is a pair whose second component has three coordinates, and `psl211_perdeck_deal : dealT := (ord0, 1%g, 1%g)` and `psl211_blockline1_deal : psl211_deal := (@Ordinal 132 1 isT, 1%g, 1%g)` are both of that type. "Public" does not check out as a domain word. In the all-decks model the deal is drawn uniformly and is not revealed, and production proves that the instance's privacy fails once it is fixed: `psl211_fixed_deal_view_dep` of `instances/psl211/psl211_models.v` refutes independence of the three seats' reading from the chirality under the dealer that lays `psl211_perdeck_deal` at both chiralities, and its own docstring says "for PSL(2,11) privacy depends on which deal law the dealer uses". A reader who takes "public" in its usual sense, known to the adversary, draws the conclusion that theorem refutes. What the file means everywhere is "not the secret", and its other uses say so locally: `psl211_blockline1_deal`'s docstring writes "a public coordinate of the run argument that carries no secret". | One line, exactly 80 bytes, replacing line 76. See "F3, the replacement text". The remaining uses of "public" each carry their own qualifier and need no change. |
| F4 | SHOULD | `STATUS.md`, N11: "A landing therefore compiles exactly two files and one line is added to `_CoqProject`." | The record never says what that line is or where it goes, so this step of the procedure cannot be executed from the record alone. The anchor exists: production `_CoqProject` lists `manifest/pgg_tableau.v`, then `manifest/pgg_tableau_syntax.v`, `instances/pgl27/pgl27_rows.v`, `instances/kim2025/five_card_rows.v`, `instances/s5/s5_rows.v`, `instances/psl211/psl211_rows.v`, `manifest/pgg_analysis_client.v`. The new file imports `pgg_tableau`, so its line has to follow `manifest/pgg_tableau.v`. `Makefile` delegates to `rocq makefile -f _CoqProject`, which computes the dependency order itself, so the position is for a reader and not for the build. | Add two sentences to N11. See "F4, the replacement text". |
| F5 | NOTE | header line 78: "as psl211_perdeck_ of instances/psl211/psl211_models.v names the comparison between the two chiralities at one deal" | This clause carries the defect that audit-2's A8 removed from the `psl211_blockline1_` clause beside it. Of the `psl211_perdeck_` family in `psl211_models.v`, `_deal`, `_coalition`, `_view`, `_seq`, `_row_size`, `_corow_size`, `_raw_view`, `_raw_count`, `_ptbl`, `_fiber` name objects and not a comparison; `_raw_countE`, `_fiber_card_neq` and `_law_neq` carry the comparison. | None proposed. A tightening costs a header line and the clause is an analogy, not a claim about the file. |
| F6 | NOTE | `g0`, and `let H` / `let K` inside `Definition psl211_blockline1_seq` | Neither falsifies the header's naming sentence. The sentence is scoped "In a proof script", and its letter list classifies named facts: "H every other named fact". `g0` is a cut introduced by `have /cards1P[g0 Hset]`, not a named fact, and its digit is a tag on the single element of a singleton fiber, not the value of `g0`, which is a permutation. The `let H` and `let K` sit in a `Definition` body, not a proof script, and they name two `seq nat` values, not facts. They are also character for character production's, `psl211_perdeck_seq` of `psl211_models.v` binding the same two names for the same two lists, so changing them here would split one construction across two files. | None. |
| F7 | NOTE | `psl211_alldecks_constancy_false_word584` | The one declaration name in the landing whose trailing digits are a value: 584 is the word length in `rho_from_words_weighted R 10 2 584`. The header's scheme sentence is scoped to proof scripts, so it is not falsified, and `STATUS.md`'s rename table applies the value reading to declaration names when it renames `psl211_alldecks_no_spectral_cert0`. Production writes "the 584-letter word law" in `instances/psl211/psl211_mixing.v` and carries the number in no declaration name. Accepted by three prior passes. | None. |
| F8 | NOTE | The constancy file cites `psl211_alldecks_static_indep`, the rows file cites `psl211_alldecks_view_secrecy`, for one domain claim | Both are right and the pairing is type-honest. The constancy field quantifies `static_coalition_obs`, so the static form is the matching citation; the row publishes the executed reading, so `psl211_alldecks_view_secrecy` is the matching citation there. The bridge is already cited in the rows header, "psl211_alldecks_exact_viewE, which identifies the framework's seat reader with the instance's". | None. |
| F9 | NOTE | `STATUS.md`, N10: "the fiber cardinalities of `psl211_alldecks_constancy_false_close`, `_supp` and `psl211_dealt_constancy_false` are `Ct` and `Cf`" | `_supp` carries `Cf` alone. The file's third `Ct` is in `psl211_perdeck_fiber_true0`, which the sentence does not name. | In `STATUS.md`, write "are `Ct` and `Cf`, and `Cf` alone in `_supp`, with a third `Ct` in `psl211_perdeck_fiber_true0`". |
| F10 | NOTE | Two other probes hold a `psl211_rows.v` | `notes/probes/2026-09-19-kim-spectral-landing/psl211_rows.v` differs from production in one hunk, its `Require` lines, and that landing's L5 row records it as a recompile and not an edit. `notes/probes/2026-09-19-tableau-extensions/psl211_rows.v` differs in three hunks: a `Require` line, a new "Key results" index entry `psl211_row_alldecks_armE`, and the lemma itself. Both were taken from production and both still carry the stale "Not claimed" paragraph. Nothing in this landing's rows header becomes false when either lands. The hazard is order: whichever lands second must rebase onto the other's text and not copy its own file over it. | None, this is for whoever sequences the three landings. |
| F11 | NOTE | `c` names two things around `psl211_alldecks_no_small_eps_cert`: "at its own reprice coordinate c" in the docstring, and "SpectralPropAt cert c, a variation distance bounded above by c" in the comment under it | `manifest/pgg_tableau.v` overloads the letter the same way, `RepricePayload (c : Reprice)` against `SpectralPropAt ... (c : R)`, so the landing inherits the overload rather than inventing it. | None. |
| F12 | NOTE | the comment under `psl211_alldecks_no_small_eps_cert`: "could only let a row publish a number larger than cert_eps, never a smaller one" | The weakened obligation is `cert_eps cert <= odflt (cert_eps cert) (c R)`, so equality is permitted and "larger" is loose. "Never a smaller one" is the operative half and is exact. | Optional: "could only let a row publish a number no smaller than cert_eps". |

## F1, the replacement text

Two lines, each exactly 80 bytes, replacing `psl211_spectral_constancy.v` lines
35 and 36.

```
(* strictly below 1/1320. The obligation of conclude bounds the published     *)
(* number below by cert_eps cert, which is that epsilon twice, so every       *)
```

Line 37 below is unchanged and the paragraph then reads "... so no certificate
carries a shuffle bound epsilon strictly below 1/1320. The obligation of
conclude bounds the published number below by cert_eps cert, which is that
epsilon twice, so every row over this model that publishes its certificate's
own number publishes at least 1/660." True of the equality of `RepricePayload`,
of the inequality of stage A's `ConcludePayload`, and of a row carrying
`no_reprice`, where `c R = None` and `odflt (cert_eps cert) None = cert_eps
cert`. It is also the wording the docstring five hundred lines below already
uses, which closes the file's one remaining split name for this obligation.

## F2, the replacement text

Replacing the third and fourth lines of the `psl211_alldecks_raw_viewE`
docstring. No line exceeds 80 bytes.

```
(** psl211_alldecks_raw_viewE — the raw reading is the instance's reading, at
    every deck description. This is psl211_perdeck_raw_viewE of
    psl211_models.v with the deal left free instead of fixed at
    psl211_perdeck_deal. *)
```

Checked against both statements. Production's
`psl211_perdeck_raw_viewE (b : bool) (g : cutT)` is at
`psl211_alldecks_seq (b, psl211_perdeck_deal)`, so its deal is pinned and its
chirality is free. The landing's
`psl211_alldecks_raw_viewE (x : psl211_inputT) (g : cutT)` is at
`psl211_alldecks_seq x`, so the difference between the two is the deal
coordinate alone, which is what the replacement says.

## F3, the replacement text

One line, exactly 80 bytes, replacing `psl211_spectral_constancy.v` line 76.

```
(* argument and a deal is its three coordinates other than the secret. The    *)
```

Line 75 above is unchanged, so the gloss reads "A deck description is a whole
run argument and a deal is its three coordinates other than the secret." That
is what the file uses the word for everywhere, and it claims nothing the
all-decks model does not support. The four other uses of "public" in the two
landing copies each bound themselves in place and need no edit: "Only the
chirality is secret, so the field asks for constancy of the reading in three
public coordinates as well", "whose first coordinate is the chirality and whose
other three are public" twice, and "a public coordinate of the run argument
that carries no secret".

## Question 1a: the header's Names paragraph

**The two glosses.** `ex_inputT psl211_alldecks_params` reduces through
`supplied_input_params psl211_algebra psl211_inputT ...` to `psl211_inputT`,
which `instances/psl211/psl211_alldecks.v` notates as `bool * psl211_deal`,
with `psl211_deal := ('I_132 * {perm 'I_6} * {perm 'I_6})`. So the run argument
is a pair whose first component is the chirality and whose second has three
coordinates, and "A deck description is a whole run argument" is true of the
type. "A deal is its three public coordinates" is true in the count and in the
type, `psl211_perdeck_deal` and `psl211_blockline1_deal` both being of
`psl211_deal` and differing in the first coordinate alone. "Public" is F3.

**The `psl211_blockline1_` sentence.** "The psl211_blockline1_ prefix names
block line one and the comparison with block line zero at one chirality" is
true of the family: `_deal`, `_seq`, `_row_size` and `_corow_size` name block
line one; `_view`, `_test`, `_testE`, `_raw_count`, `_raw_countE`, `_fiber`,
`_fiberE`, `_massE`, `_seqE` and `_law_neq` carry the comparison with block
line zero, all at chirality true. The `psl211_perdeck_` half of the sentence is
F5.

**The proof-local scheme, checked against every proof.** I stripped nested
comments in Python, cut the file at `Proof.` and `Qed.` into 26 proof bodies,
and collected every name bound by `have`, `set`, `pose`, `case`, a `cards1P`
pattern, and every intro pattern after `=>`. The capital-initial names are:

- `C`: `Ct` in `psl211_perdeck_fiber_true0`, `_close` and
  `psl211_dealt_constancy_false`, `Cf` in `_supp`, `_close` and
  `psl211_dealt_constancy_false`, `Cj0` and `Cj1` in
  `psl211_blockline1_law_neq`. All eight are `#|..._fiber ...| = n`, fiber
  cardinalities.
- `U`: `Ut` and `Uf` in `_close` and in `psl211_dealt_constancy_false`, `Uj0`
  and `Uj1` in `psl211_blockline1_law_neq`. All six are
  `(fdistmap ... ((`U psl211_G_pos) : R.-fdist cutT)) <view> = ...`, masses at
  the group-uniform law.
- `L`: `Lt` in `_supp` alone, and it is
  `(fdistmap ... ideal) psl211_perdeck_view = 0`, a mass at the ideal.
- `E`: `Et`, `Ef`, `Ej0`, `Ej1`. All four are
  `static_coalition_obs ... = (fun g => psl211_alldecks_view ...)`, reader
  identifications.
- `T`: `T1`, `T2`, `T3` in `_close`, a chain of `<=` ending at `eps + eps`.
- `H`: every remaining named fact, 38 of them, `H` bare included.

No capital-initial local name is off the scheme. The lowercase locals are `b`,
`f`, `g`, `g0`, `i`, `k`, `p`, `q`, `x`, `ideal`, none of which begins with a
scheme letter. The digits surviving in a proof script are `j0` and `j1` for the
two block lines, `1`, `2`, `3` for the chain steps, `0` in `g0`, `Hg0`, `Hg0G`
and `Hg0v` for the witness cut, and `0`, `1`, `2` in the `and3P` splits, which
index the seat. None names a value, so the last clause holds. `STATUS.md`'s
claim that this was checked mechanically with no name off the scheme is
reproduced.

The statement binders `C`, `E`, `R`, `A` and the `T` of `fdistmap_point_condE`
reuse scheme letters for a coalition, execution parameters, a real field, an
algebra and a finite type. The sentence's scope, "In a proof script", excludes
them, and all five are the tree's own binder conventions.

`g0` and the `let H` / `let K` are F6.

## Question 1b: the rows header's new four lines

"so the field asks for more than the secret-independence this row claims, and
its failure is no proof of leakage: under the all-decks law a coalition of at
most five of the twelve seats reads nothing about the chirality,
psl211_alldecks_view_secrecy."

Clause by clause against `Theorem psl211_alldecks_view_secrecy` of
`instances/psl211/psl211_rows.v`:

- "the field asks for more than the secret-independence this row claims":
  `coalition_reading_constancy` quantifies `forall x x' : ex_inputT E`, the row
  claims independence from `psl211_alldecks_secret` alone. Correct.
- "its failure is no proof of leakage": the refutations are of a universally
  quantified equation; no statement in either landing file asserts a positive
  dependence at the all-decks law. Correct, and weaker than the "is not
  leakage" that audit-2's A2 rejected.
- "under the all-decks law": the theorem's four conjuncts are all under
  `psl211_alldecksP R`, which `psl211_models.v` names "the law of the
  all-decks model". Correct.
- "a coalition of at most five of the twelve seats": the theorem's premise is
  `(HC : (#|C| < 6)%N)` and `seatT` is the twelve-seat interface index.
  Correct.
- "reads nothing about the chirality": the conjunction is independence of
  `sa_coalition_view` from `psl211_alldecks_secret`, then
  `` `I( secret ; view ) = 0 ``, then
  `` `H( secret | view ) = `H `p_ secret ``, then independence under every
  `h : {ffun seatT -> cardT} -> W`. The second conjunct is "reads nothing"
  exactly; the fourth extends it to every deterministic post-processing. The
  summary is true and understates rather than overstates.
- "psl211_alldecks_view_secrecy": the name is in this same file and in its own
  "Key results" index. Correct.

The refutations are about `static_coalition_obs` and the theorem is about
`sa_coalition_view`. The rows header already carries the identification between
the two, `psl211_alldecks_exact_viewE`, four paragraphs above, so the pairing is
not a gap. See F8.

## Question 1c: the certificate theorem's docstring and the trimmed comment

`cert_eps cert` is `sw_bound_eps (sc_b cert) + sw_bound_eps (sc_b cert)`, so
"cert_eps cert is the shuffle bound epsilon twice" is exact.
`PortProp c (SpectralDecay cert)` is
`SpectralPropAt cert (odflt (cert_eps cert) (c R))` in both versions of
`manifest/pgg_tableau.v`, so "A row publishes odflt (cert_eps cert) (c R) at
its own reprice coordinate c" is exact in both.

"The obligation of conclude bounds the published number below by cert_eps
cert, so no row over this model publishes less" is true under the equality
`cert_eps cert = odflt (cert_eps cert) (c R)` of production's
`RepricePayload`, and true under the inequality
`cert_eps cert <= odflt (cert_eps cert) (c R)` of the extensions probe's
`ConcludePayload`. The theorem gives `sw_bound_eps (sc_b cert) >= 1/1320` at
`#|pgg_G psl211_M| = 660`, which `psl211_card` of
`instances/psl211/psl211_closure.v` compiles, so `cert_eps cert >= 1/660` and
the chain closes.

The file names neither `RepricePayload` nor `ConcludePayload`. It writes "the
obligation of conclude" and "its own reprice coordinate c". `Reprice`, the type
of `c`, is not renamed by the extensions probe, so both phrases survive the
rename. This is what fix pass 2 was for and it works.

The trimmed comment is character for character audit-2's proposed text. Its
claim that a weakened obligation "could only let a row publish a number larger
than cert_eps" rests on `SpectralPropAt cert c` being
`var_dist ... <= c`, so a larger `c` is a weaker proposition. Correct, with the
looseness of F12.

The one sentence the pass did not make robust is the header's, which is F1.

## Question 1d: "deck description" against "deal"

**In the two landing copies, every use fits the gloss.** Twenty occurrences in
`psl211_spectral_constancy.v` and five in `psl211_rows.v`, each read against
the statement under it.

Whole run argument: constancy lines 17, 57, 63, 75, 101, 250, 286, 331, 368,
409, 441, 523; rows lines 7, 35, 47, 58, 165. Checked against
`psl211_alldecks_uniq (x : psl211_inputT)`, `psl211_blockline1_fiber (x :
psl211_inputT)`, `psl211_blockline1_massE (x : psl211_inputT)`,
`psl211_blockline1_seqE` at `(true, psl211_blockline1_deal)`, and
`psl211_blockline1_law_neq`, whose two sides are `(true, psl211_perdeck_deal)`
and `(true, psl211_blockline1_deal)`.

Three public coordinates: constancy lines 22, 80, 249, 333, 558; rows line 164.
Checked against `psl211_perdeck_deal : dealT` and the per-cut deal count of
`psl211_alldecks.v`, which is over `{y : psl211_deal | ...}`.

Line 332 is the one slip and it is F2.

**Production sentences that use "deck description" in the deal sense.** This
landing does not edit `instances/psl211/psl211_models.v`, whose reverse closure
is nine files. The list, for the landing plan to carry:

| file and line | text |
|---|---|
| `psl211_models.v:51` | "under a dealer laying one fixed deck description the reading of three seats is not independent of the chirality" |
| `psl211_models.v:73` | "`psl211_perdeck_deal` == the deck description fixing the counterexample" |
| `psl211_models.v:78` | "`psl211_fixed_deal_delta` == the dealer laying one deck description at both chiralities" |
| `psl211_models.v:117` | "`psl211_perdeck_raw_countE` == at one deck description the two chiralities have 0 and 1 cuts producing one reading" |
| `psl211_models.v:564` | "dealT — a deck description: a chirality-free block index together with two labellings." |
| `psl211_models.v:585` | "psl211_deal_pos — the type of deck descriptions is inhabited, so it carries a uniform law." |
| `psl211_models.v:594` | "psl211_dealer_delta — the all-decks dealer: whatever the chirality, the deck description is drawn uniformly and independently of it." |
| `psl211_models.v:690` | "psl211_dealer_sectionE — at one cut, the two chiralities send the uniform law on deck descriptions to the same law on what a coalition of at most five seats reads." |
| `psl211_models.v:786` | "psl211_perdeck_deal — the deck description that fixes the counterexample: block index zero of the chirality's table, with both labellings the identity." |
| `psl211_models.v:887` | "at a fixed deck description the two chiralities do not have equally many cuts producing a given reading" |
| `psl211_models.v:888` | "even though summing over deck descriptions they do" |
| `psl211_models.v:994` | "psl211_perdeck_fiber_card_neq — at one deck description the two chiralities have different numbers of cuts producing one reading." |
| `psl211_models.v:997` | "which fixes a cut and counts deck descriptions" |
| `psl211_models.v:998` | "The statement with the roles exchanged, fixing a deck description and counting cuts, is false" |
| `psl211_models.v:1115` | "and the uniform law on deck descriptions meets it" |
| `psl211_models.v:1132` | "psl211_fixed_deal_delta — the degenerate dealer that lays one and the same deck description whatever the chirality." |
| `psl211_models.v:1136` | "one deck description names two different decks" |
| `psl211_models.v:1142` | "psl211_fixed_dealP — the dealer law at that kernel: a uniform chirality, a fixed deck description, a uniform cut." |

Eighteen sentences, all in `instances/psl211/psl211_models.v` and none
elsewhere. The same file uses the word in the run-argument sense at lines 9,
46, 192, 205, 219, 235, 311 and 356, so the split is internal to that one file.

Production uses the word in the run-argument sense only, and so agrees with the
landing's gloss, in `instances/psl211/psl211_alldecks.v` at 153, 164, 171, 569,
1366 and 1391, in `instances/psl211/psl211_analysis.v` at 28, 101, 147, 161,
261 and 271, in `instances/psl211/psl211_rows.v` at 7, 35 and 145, and in
`manifest/pgg_analysis_manifest.v` at 569, 630, 819 and 1617. The manifest's
1617 spells it out: "The deck description this instance runs on is a class bit
paired with a block line of that class and a labelling of each of the two
six-code colour groups."

## Question 1e: "single-card marginal bound"

`instances/psl211/psl211_profile.v` is where the phrase comes from. It writes
"a separate marginal bound at epsilon = 0: the single-card pushforward of ...",
"psl211_marginal_bound — the marginal bound at epsilon = 0: single-card ...",
"Two-transitivity buys the single-card marginal above and nothing", and
"profile_eps_psl211 — the PSL(2,11) marginal bound's epsilon is zero. The
epsilon field of psl211_marginal_bound is 0: the single-card ...". The lemma is
`profile_eps_psl211 (R : realType) : sw_bound_eps (psl211_marginal_bound R) =
0%R`.

So "which is the epsilon profile_eps_psl211 of
instances/psl211/psl211_profile.v gives this instance's single-card marginal
bound" is true of the lemma and uses the file's own term. The change closes
audit-2's A10, and fix pass 2 applied it in three places rather than the one
A10 asked for, which is the right call.

## Question 2: soundness invariants 2 to 5, over both files in full

**Invariant 2, nothing says the arm cannot be closed here. Carried.** The file
name is `psl211_spectral_constancy`, not a no-go name. The header's "Not
claimed" paragraph opens "The spectral arm is not shown unavailable at this
instance. What is excluded is a range of epsilon". The certificate theorem's
docstring ends "It says neither that the arm is unavailable here nor anything
about what a coalition of at most five seats reads". The rows header says "What
is excluded is a range of epsilon and not the arm" and, of the spectral row,
only "Not claimed". `psl211_dealt_constancy_false`'s docstring says "no
spectral certificate over these parameters can take that law as its ideal cut,
while a certificate at some other ideal stays open". The word model sentence
says "Nothing here says the word row is excluded outright". Audit-2's A5 gap,
the unqualified "The field fails", is closed: the sentence now opens "At the
group-uniform ideal the field fails".

I re-derived the one arithmetic claim in that paragraph.
`psl211_alldecks_constancy_false_word584`'s premise
`(2%:R^-40 + eps) + (2%:R^-40 + eps) < (#|pgg_G psl211_M|%:R)^-1` is
`eps < 1/1320 - 2^-40` at `#|pgg_G psl211_M| = 660`, which is what the header
says it reaches. The occupancy sentence's variation distance,
`2 * (1 - 660/12!)`, is the sum of absolute differences between the uniform law
on `{perm 'I_12}` and `` `U psl211_G_pos ``, and infotheo's `var_dist` is that
sum, so "never exceeds 2" is right and "near 4" for its double is right.

**Invariant 3, nothing says or implies leakage. Carried.** The strongest
leakage-adjacent sentence is `psl211_perdeck_fiber_true0`'s, "one reading
already tells the two chiralities apart at this fixed deal, which is not the
law the row is about". It is true and it is exactly what production's
`psl211_fixed_deal_view_dep` proves, and the qualifier is present. Every other
statement of the kind is under the dealt parameters or under a fixed deal.
`psl211_alldecks_constancy_false`'s docstring closes with "this refutation
states no leakage", and the rows header with "its failure is no proof of
leakage" and the theorem name.

**Invariant 4, nothing says the all-decks failure is unrelated to the secret.
Carried.** `psl211_alldecks_constancy_false`'s docstring keeps "A change of
secret is always also a change of the laid deck here, the chirality selecting
the table the block line indexes." The header attributes the secret-free
failure to the second refutation only, "The second failure moves no secret",
and the conclusion drawn from it is about the field and not about the secret,
"so the field asks for constancy in public data and not for secrecy alone".
`psl211_blockline1_law_neq`'s docstring says the failure "does not need the
chirality to move", which is a claim about what suffices and not about what is
irrelevant, and the refutation that does move the secret is stated separately
and first.

**Invariant 5, the numbers. Carried.** A regular expression over both files
finds no `360`, no `600` and no `10/11`. The only occurrence anywhere in the
probe is `STATUS.md`'s own sentence recording their absence. `660`, `1320`,
`132`, `584` and `2^-40` are all compiled quantities with a named source.

## Question 3: round-2 items A1 to A13

| ID | State | Judgement |
|---|---|---|
| A1 | Closed, differently | The three renames were applied exactly as specified, `Ht0` to `Lt`, `Lt` and `Lf` to `Ut` and `Uf`, `Lj0` and `Lj1` to `Uj0` and `Uj1`, and I verified each at its `have` and at every use. The sentence deviates, see deviations 1 to 3 below. |
| A2 | Closed | The four lines are character for character audit-2's block. Checked against `psl211_alldecks_view_secrecy` in question 1b. |
| A3 | Closed | The docstring is character for character audit-2's block. Checked against both obligations in question 1c. |
| A4 | Closed | The non-sequitur "so no reading of these refutations gives leakage" is gone. What follows "The second failure moves no secret" is now a claim about the field, not about leakage. |
| A5 | Closed | "At the group-uniform ideal the field fails" names the ideal in the first clause. |
| A6 | Closed | The `psl211_blockline1_law_neq` docstring is audit-2's replacement text, and it names the two run arguments rather than two deck descriptions. |
| A7 | Closed | `STATUS.md`'s N3 cell reads "Deviation from decision 3, recorded below" and a sixth item was added under "What in the spec or in SRC turned out wrong", worded as A7 asked. |
| A8 | Closed, differently | Audit-2's sentence was applied with its last word changed, see deviation 5. The `psl211_perdeck_` half was carried over unchanged and is F5. |
| A9 | Closed | The five lines of the `coalition_reading_constancy` docstring are re-wrapped to the file's width with no wording change. I diffed them and only whitespace moved. |
| A10 | Closed, more widely | See deviation 6. |
| A11 | Declined, soundly | No action was asked for. The header's pointer to `notes/probes/2026-09-19-psl211-sc-const/` stands, in a `(* ... *)` block that coqdoc does not render, as the provenance of an explicitly uncompiled measurement. |
| A12 | Declined, soundly | No action was asked for. |
| A13 | Closed | The comment is character for character audit-2's trim, and the second comment is untouched, as A13 asked. |

**The deviations from audit-2's text, each judged.**

1. A1's block wrote "the comparison between the two chiralities at one deck
   description"; the file says "at one deal". **Sound.** Under the gloss the
   object compared at is a `dealT`, so the deviation makes the sentence
   type-honest where audit-2's was not.
2. A1's block wrote "the suffix names the coordinate the quantity is taken at";
   the file says "a C, U, L or E suffix names the coordinate". **Sound and
   necessary.** Audit-2's unrestricted clause is false of `T1`, `T2` and `T3`,
   whose suffixes index a chain step. The restricted clause is true as stated.
   It leaves the coordinate suffixes of `Ht`, `Hf`, `Hj0` and `Hj1` undeclared,
   which costs nothing: the sentence declares `H` as "every other named fact"
   and puts no constraint on its suffixes.
3. A1's block was extended by a sentence audit-2 did not ask for, "A deck
   description is a whole run argument and a deal is its three public
   coordinates." **Sound in intent.** It closes A6 file-wide rather than at one
   docstring, which is the cheaper fix, and it is where a reader looks. The
   word "public" is F3.
4. A4 and A5's block wrote "the two chiralities of one deck description"; the
   file says "one deal". **Sound**, same reason as 1.
5. A8's sentence was applied with "at one deal" for "at one deck description".
   **Sound**, same reason as 1.
6. A10 asked for "single-card marginal bound" in `psl211_rows.v`; the pass also
   wrote it in the constancy file's header index and in
   `psl211_alldecks_no_zero_eps_cert`'s docstring. **Sound.** One object,
   `psl211_marginal_bound`, now has one name in both landing copies, which is
   what A10 was for.
7. `psl211_perdeck_fiber_true0`'s "at this fixed deck description" became "at
   this fixed deal", which audit-2 did not ask for. **Sound**, and required by
   the new gloss: `psl211_perdeck_fiber` is at `(b, psl211_perdeck_deal)` with
   `b` free, so what is fixed is the deal.
8. `psl211_alldecks_raw_viewE`'s "fixed to psl211_perdeck_deal" became "fixed at
   the deal psl211_perdeck_deal", which audit-2 did not ask for. **Not sound as
   worded.** This is F2.

## Question 4: `STATUS.md`

**True of the final files.** The claims I checked mechanically:

- "46 declarations": 12 `Definition`, 32 `Lemma`, 1 `Theorem`, 1 `Corollary`,
  plus 4 `Local Notation` that the count excludes. 46.
- "every one ending in `Qed` or being a `Definition`": 34 provable
  declarations, 34 `Qed.`, no `Defined`, no `Admitted`, no `Abort`.
- "Every proof-local name introduced with a capital initial was listed
  mechanically and checked against the scheme, with no name off it":
  reproduced, question 1a.
- "The digits surviving in a proof script are the block-line indices `j0` and
  `j1`, the chain indices of `T1`, `T2` and `T3` ..., the witness `g0` ... and
  the three conjunct names of an `and3P` split": complete, nothing else.
- The N10 rename table: every landing name in it exists in the landing file,
  and the file's 46 names are covered by the table plus the "Names kept
  unchanged" paragraph plus the `psl211_dealt_*` block that paragraph names.
- N8's quoted production passage matches `instances/psl211/psl211_rows.v`
  lines 40 to 44 word for word, and the landing copy rewrites exactly that
  passage.
- The header index: all 13 names it lists are declared in the file.

One inaccuracy, F9.

**Identifiers quoted that no longer exist.** I collected the 154 back-quoted
identifier-shaped tokens in `STATUS.md` and searched them as whole words
against the probe's `.v` files, `history/`, and every `.v` file of the
production tree. Thirty-three are not found. Every one is an SRC name inside
the N10 rename table, the N5 disposition table, the N6 per-sentence table where
it is tagged "(SRC ...)", or the N10 prose that states the rename. `Abort` is a
keyword in the "no custom axiom" sentence, `LR` and `RL` are the N5 table's
legend, `_CoqProject` is a file, and `_supp`, `_constancy_`, `_sc_const_` and
`_eps_` are name fragments in rename prose. No live identifier is quoted for a
declaration that does not exist.

**Its own lines by number.** No. The record cites production and library lines,
`instances/psl211/psl211_rows.v:40-44`,
`probability/variation_dist.v:51`, `probability/fdist.v:377`, the manifest's
`:564-605` and `:660-690`, `instances/psl211/psl211_analysis.v:1-53`,
`instances/psl211/psl211_profile.v:80` and `:103`. All are in a probe record,
not in a permanent comment, and the record says why the one line range that was
in a permanent comment was removed.

**The landing procedure.**

- Which files are copied where: the Files table gives it. The constancy copy
  becomes `instances/psl211/psl211_spectral_constancy.v`, the rows copy becomes
  `instances/psl211/psl211_rows.v`, header comment only. Executable.
- The `_CoqProject` line and its anchor: **not given.** This is F4. The anchor
  exists in production.
- The import rewrite: none is needed, and the record says so twice. Both
  landing copies import only `From HB`, `From mathcomp`, `From infotheo`,
  `From pgg_smc` and `From pgg_reconstruct`, which are production's logical
  paths; neither names `psl211_nogo_landing`. N1 says "production import
  paths" and N10 says "The logical path `psl211_nogo_landing` in `_CoqProject`
  is probe-local and does not land". Executable.
- The single-file compiles in order: "Fix pass 2, what changed and what was
  compiled" gives the three files in order, through the machine-wide `rocq1`
  lock, with `rocq compile -time` and a real return code, and says `make` was
  never invoked. N11 says a landing compiles two production files, the new one
  and `psl211_rows.v`. Executable.
- `psl211_endpoints` only loaded: stated in N11, "loaded by the new file and
  never compiled: it was not touched, not compiled and not opened in this
  probe", and again in both fix-pass sections. I confirmed the constancy file
  has `From pgg_smc Require Import psl211_endpoints psl211_alldecks
  psl211_models.` and that neither landing copy is
  `instances/psl211/psl211_endpoints.v`. Executable.

## Question 5: the statement-comment rule, over the whole landing file

**Fact then position.** I read all 68 `(** ... *)` blocks. Every one opens with
the declaration's name and a declarative statement of what it is, and every
block that carries conceptual novelty carries its position. Examples that earn
their length and get it: `coalition_reading_constancy` ends with the domain
frame, "where the run argument carries public data as well ... the field asks
for constancy in that public data too and is stronger than the privacy the
instance claims"; `spectral_cert_reading_constancy` ends "so refuting the
proposition at a law refutes every certificate whose ideal cut is that law";
`psl211_perdeck_coalition_below_k` ends "it is the only nontrivial premise the
counterexample owes"; `psl211_alldecks_constancy_set0` ends "the field is not
false for the trivial reason that its quantifier over coalitions admits a
reading no law can make constant". Blocks that re-tuple existing data get one
sentence, which is right: `psl211_dealt_raw_viewE`,
`psl211_blockline1_corow_size`, `psl211_dealt_fiberE`.

**The attack model is named where it belongs.** Coalitions below the threshold
are given as "fewer than profile_k seats" in the field's own docstring and as
"at most five of the twelve seats" wherever a theorem with `#|C| <= 5` or
`#|C| < 6` is cited; the refutations exhibit three seats and say so. The run
argument is described per mode, "a whole deck description, whose first
coordinate is the chirality and whose other three are public" under the
all-decks parameters and "the chirality and nothing else" under the dealt ones,
and the consequence for the field is drawn in both places.

**No meta, status, proof strategy, line numbers, probe or plan names in a
rendered docstring.** Machine-checked over all 68 blocks for `notes/`, `probe`,
`SRC`, `TODO`, `deferred`, `reused`, `machine-checked`, `used by`, `key lemma`,
`important`, `headline`, `risk`, and for tactic words. The only hits are the
substring "block line" inside three docstrings. The strategy that has to be
kept is kept where the rule puts it, in `(* ... *)` comments: the `congr1`
reason above `psl211_alldecks_constancy_false`, the `in_set` reason twice, the
"no `/=` and no `//`" reason in `_supp`, the `Local Opaque` reasons, and the
`@`-form reason in `psl211_alldecks_no_zero_eps_cert`.

**Header exposition against inventory.** The header is 128 lines and the index
names 2 definitions and 11 results out of 46 declarations, so it cannot drift
into an inventory. The prose a reader needs is there, the occupancy argument is
written once, and the uncompiled parts are labelled "argued and not compiled"
and "How wide each failure is stays measured and not proved".

**One word per concept.** Checked for deck description against deal (question
1d, one slip at F2), for the marginal bound (question 1e, now one name), and
for the obligation of conclude, where the header and the docstring still
describe it two ways (F1). "Reading" is the prose word for a view throughout
both files, "mass", "law", "ideal", "cut", "run argument", "chirality" and
"block line" are each used for one thing. `c` is F11.

**Line width.** Every line of both `.v` files is at most 80 bytes, measured on
bytes. The 128 header-box lines are exactly 80.

**Barred vocabulary.** No `apex`, no `gate`, `gates`, `gated` or `gating` as a
word, no `posit`, `posits`, `posited` or `positing`, and no capital L followed
by digit one, in either `.v` file or in `STATUS.md`. The proof-local mass names
are `Lt`, `Ut`, `Uf`, `Uj0`, `Uj1`, `Ct`, `Cf`, `Cj0`, `Cj1`; none is the
barred token, and the rename that produced `Uj0` and `Uj1` is what removed it.
No metaphor word for a mathematical result: the file writes "refutes", "is
false at", "bounded", "exceeds", "excluded", "no proof of".

## Question 6: interaction with the other landings

Nothing in this landing's rows header becomes false when stage A of
`notes/probes/2026-09-19-tableau-extensions/` lands. Stage A's copy of
`psl211_rows.v` differs from production in three hunks: the `Require` line for
the tableau, a new index entry `psl211_row_alldecks_armE == the row carries the
exact arm`, and the lemma
`psl211_row_alldecks_armE ... : security_arm_of psl211_row_alldecks_tableau R
idx = ExactIndependenceArm`. None of them touches the "Not claimed" paragraph
or any fact it cites, and the new lemma agrees with what the paragraph already
says, that this row carries the exact arm and not a spectral one.

Two things to record. Both are F10 and neither blocks.

1. Stage A's copy and the Kim landing's copy were both taken from production
   and both still carry the stale paragraph. If either is landed by copying its
   file over production after this landing, this landing's header reverts
   silently, since nothing in either probe's ledger checks that paragraph. The
   Kim landing's L5 row does say its `psl211_rows.v` hunk is a `Require` line
   and that "their permanent text is production's", which is the right
   discipline; the sequencing still has to be a rebase.
2. The extensions probe also renames `RepricePayload` to `ConcludePayload` and
   weakens its obligation to `<=`. That does not reach the rows header, whose
   sentence is conditional, "a row over this model that publishes its
   certificate's own bound publishes at least 1/660". It does reach the
   constancy file's header, which is F1.

## What I did not check

- I compiled nothing. The main session's recompile after fix pass 2, three
  files at return code 0, 20 assumption blocks within the three `boolp` axioms
  and 28 closed, is taken as given, as is the comment-stripped identity of the
  rows copy with production.
- I did not re-derive the mathematics of any proof. I read every statement and
  every docstring against each other, and I re-derived only the arithmetic the
  prose asserts: `eps < 1/1320 - 2^-40` from the `word584` premise,
  `2 * (1 - 660/12!)` for the occupancy distance, and `cert_eps >= 1/660` from
  the theorem.
- I did not audit `psl211_nogo_fidelity.v`, `opaque_vm_test.v`, `_CoqProject`
  or the `history/` copies beyond using them as the diff base, since the brief
  scopes this round to the two files that land.
- I did not re-run the collision scan of N10 or the reverse-closure computation
  of N11.
- I did not verify `notes/probes/2026-09-19-psl211-sc-const/`, the verbatim
  source, which three earlier passes audited.
- I did not read the extensions probe's stage A beyond its `pgg_tableau.v`
  obligation and its `psl211_rows.v` diff, nor the Kim landing beyond its
  `psl211_rows.v` diff and its L5 ledger row.
