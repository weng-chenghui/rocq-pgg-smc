# Landing the PSL(2,11) result on the spectral arm

Date: 2026-09-19

Status: LANDED on 2026-09-19. Production commits `50ea761` (the new file
`instances/psl211/psl211_spectral_constancy.v` and its `_CoqProject` line) and
`b93aa16` (the header of `instances/psl211/psl211_rows.v`). Three audit rounds
on the landing probe, the third GO; what the audits changed is the section
"Changes after the audits" below. Plan:
`docs/superpowers/plans/2026-09-19-psl211-spectral-constancy-landing.md`.
As-built record: the last section of
`notes/probes/2026-09-19-psl211-nogo-landing/STATUS.md`. The verbatim source was
the closed probe `notes/probes/2026-09-19-psl211-sc-const/` (SRC below).
Summary: [[2026-09-19-112500-spectral-arm-at-kim-and-psl211-summary]]. Runs
beside [[20260919-kim-spectral-landing-design]] and touches none of its files.

## Problem

The header of `instances/psl211/psl211_rows.v` explains why this instance has
no spectral row, and half of the explanation is out of date. It says the
certificate's constancy field fails at three seats under the dealt mode, which
until 2026-09-19 rested on a count over raw tables and not on a statement at
the field's type, and it says that under the all-decks dealer the field "is a
different statement nobody has measured". It has now been measured, and it is
false. A reader of the paper who asks why PGL(2,7) and the five-card instance
have a row for their actual model through the spectral arm and PSL(2,11) does
not has no compiled fact to be pointed to. The answer matters beyond this
instance, because it says what the arm's fifth field really asks for: constancy
of the ideal's reading at every two run arguments, which is more than a privacy
argument over a mixed law needs.

The result also has to be stated with care. At the all-decks parameters the
run argument is the public deck description, and the field fails between two
deck descriptions of one chirality as well as between the two chiralities. So
its failure is no proof of leakage: under the all-decks law three seats read
nothing about the chirality, which is the exact arm's theorem.

## Decisions, each with its reason

1. **A new file `instances/psl211/psl211_spectral_constancy.v`.** Reason: the
   refutation and its support are some forty declarations, the rows file is
   where programs are written, and the tree has the precedent
   `reconstruct/s5_nogo.v`. The file imports the Tableau for `SpectralCert`,
   sits above it, and has no importer, so a landing compiles it and nothing
   else. One line in `_CoqProject`. Renamed from `psl211_spectral_nogo.v`
   after the naming audit: the file refutes the constancy field and a range
   of epsilon, and does not show the arm unavailable.
2. **`instances/psl211/psl211_models.v` is not edited.** The two lemmas SRC
   restated with the deck description free stay restated in the new file.
   Reason: that file has nine reverse-dependants, the manifest and every rows
   file among them, and editing it would collide with the Kim landing.
3. **Only what the paper can cite lands.** `fdist_uniform_close_supp` is proved
   in SRC and used by no headline, so it stays in the probe. SRC's
   `var_dist_point_le` is infotheo's `leq_var_dist` and is replaced by it. The
   corollary the third audit asked for lands: the constancy field refuted from
   the pair of deck descriptions of one chirality, so that "the failure does
   not need the secret to move" is a statement at the field's type. The
   diagnostic file `psl211_deck_diag.v` stays in the probe.
4. **Generic lemmas that survive decision 3 go to a new file under `lib/`**
   with an empty reverse closure, and not into
   `security/pgg_collusion_bound.v`, which has `psl211_endpoints` among its
   reverse-dependants, nor into the Kim landing's `lib/var_dist_supp.v`, whose
   closure will hold the five-card chain. The landing probe says which lemmas
   these are and proposes the file's name; if none survives, no file is made.
5. **The header of `psl211_rows.v` is rewritten to cite the compiled facts.**
   It is a comment-only change to a file with no importer.
6. **The proof-local hypothesis named after the barred two-character term is
   renamed**, as SRC's closure note records.

## Flow

The running value is the distance from the group-uniform cut.

```
flow psl211_no_spectral_cert                                  // distance
start  `U psl211_G_pos                                        // 0
hop    to the word law W by psl211_word_mixing                // 2^-40, word form only
hop    to a certificate's ideal by its closeness field        // 2^-40 + eps
eval   by psl211_alldecks_sc_const_false_close                // False if twice that < 1/660
object the pair of deck descriptions of opposite chirality    // psl211_perdeck_law_neq
object the pair of deck descriptions of one chirality         // psl211_samechir_law_neq
object the dealt mode                                         // psl211_dealt_sc_const_false
outside the occupancy of the unexcluded range: argued, not compiled
outside the numbers 360, 600 and 10/11: computed diagnostics, not theorems
```

Roles. Objects: the three refutations of the constancy field. Step
justifications: `psl211_word_mixing` and the certificate's closeness field,
joined by the tree's `var_dist_triangle`. Terminal: the closeness form of the
refutation. Packaging: `psl211_alldecks_cert_ideal_close`, which reads the
identification field of a certificate over the all-decks sample. Structure: a
composition of distances that is an inequality at every step, so no monad is
claimed.

## Claim ledger

| ID | Checkable claim | Passing evidence |
|---|---|---|
| N1 | The new file compiles in place of SRC's three probe files. | One landing copy, imports as the permanent file will have them, every declaration ending in `Qed`, in an order a reader can follow: the field as a proposition, the all-decks refutations, the quantitative form and the certificate theorem, the word form, the dealt mode. |
| N2 | The field as stated is the record's field. | `sc_const_prop_field` by `exact: sc_const cert`, so a change of the record surfaces here. |
| N3 | The three refutations at the field's type. | `psl211_alldecks_sc_const_false`, the corollary from `psl211_samechir_law_neq`, and `psl211_dealt_sc_const_false`. |
| N4 | The certificate theorem and the word form. | `psl211_alldecks_no_spectral_cert`, `psl211_alldecks_sc_const_false_word584`, with `leq_var_dist` in place of the local copy. |
| N5 | What does not land, and why. | A table of every SRC declaration: lands, lands renamed, replaced by a library lemma, or stays in the probe, with the reason. |
| N6 | No reduction hazard moves into a permanent file unmarked. | Every `vm_compute` in the file runs over plain `nat` tables, every `Local Opaque` sits where SRC has it, and no sentence costs more than its SRC counterpart by more than a tenth. The compile time of the file is reported; the expectation from SRC is under a minute. |
| N7 | The header of `psl211_rows.v`. | A landing copy with the "Not claimed" paragraph rewritten, true sentence by sentence, citing the new file's theorems by name, and identical to production once comments are stripped. |
| N8 | Sentences elsewhere that the result makes false or stale. | A search of the production tree for the propositions, not the names: that the all-decks constancy is unmeasured, that the dealt-mode failure is a raw count, that PSL(2,11) has no spectral arm for an unstated reason. The manifest's PSL(2,11) row table is read in full. A hit in the manifest is reported and not edited here, because the Kim landing owns that file this week. |
| N9 | Assumptions. | `Print Assumptions` in a fidelity file that imports the landing copy: the three `boolp` axioms, or closed. |
| N10 | Names. | No naming audit was run on SRC. Names are reviewed against the tree's conventions and `reconstruct/s5_nogo.v`, the file name included. Collision scan against the production tree. |
| N11 | Cost. | The production files a landing compiles: the new file, `psl211_rows.v` for its comment, and the new `lib/` file if there is one. `psl211_endpoints` is only loaded. |

## Soundness invariants

1. No new axiom, `Admitted` or `Abort`.
2. Nothing says the spectral arm cannot be closed at PSL(2,11). What is proved
   is that no certificate over the all-decks model carries an epsilon below
   `1/1320`, so a row publishing its certificate's own bound publishes at least
   `1/660`.
3. Nothing says or implies leakage at the all-decks parameters. The exact
   arm's independence is cited as a separate theorem about the all-decks law.
4. Nothing says the all-decks failure is unrelated to the secret. It occurs
   between the two chiralities and also at one chirality, and a change of
   secret is always a change of the laid deck.
5. The numbers 360, 600 and `10/11` appear only as computed diagnostics with
   their source, or not at all.
6. `instances/psl211/psl211_endpoints.v` is never compiled. No file with it
   among its reverse-dependants is edited.

## Changes after the audits

Recorded on 2026-09-19, after two rounds of audits of the landing probe. The
ledger and the decisions above stand as written, so that what was planned can
be compared with what was found.

1. **Decision 3, reversed in one point.** The corollary that refutes the
   constancy field from the pair of deck descriptions of one chirality does not
   land. The field is a universally quantified proposition, so its refutation
   from that pair has the same statement as the refutation from the pair of
   opposite chirality, and a reader cannot cite the two separately. What carries
   soundness invariant 4 is `psl211_blockline1_law_neq`: three seats read the
   group-uniform cut under two different laws at two run arguments of one
   chirality. Ledger row N3 therefore holds two refutations at the field's
   type, all-decks and dealt, and one law inequality.
2. **Decision 1, the file name.** The file is
   `instances/psl211/psl211_spectral_constancy.v`. The first name said the arm
   has no row here, which invariant 2 forbids saying.
3. **Names.** `sc_const_prop` is `coalition_reading_constancy`,
   `psl211_samechir_*` is `psl211_blockline1_*`,
   `psl211_alldecks_no_spectral_cert` is `psl211_alldecks_no_small_eps_cert`.
4. **Decision 4.** No generic lemma survived decision 3, so no `lib/` file is
   made.
5. **The sentence about leakage** reads "its failure is no proof of leakage"
   and names the separate theorem, `psl211_alldecks_view_secrecy`. "Is not
   leakage" claims an absence that the constancy file does not prove.
6. **The warning** `notation-incompatible-prefix` is already emitted by
   `instances/psl211/psl211_rows.v` in production and is accepted.

## Probe artifacts

Directory `notes/probes/2026-09-19-psl211-nogo-landing/`, logical path
`psl211_nogo_landing`: the landing copy of the new file, of the `lib/` file if
any, and of `psl211_rows.v`; a fidelity file; `_CoqProject`; `STATUS.md`; two
audit reports. Then a plan, an implementation by `cp`, and an as-built fidelity
file.

## Out of scope

A spectral or proximity row for PSL(2,11), which is stage D of
[[20260919-tableau-three-extensions-probe-design]]. A row that publishes a
refutation. Any edit to `psl211_models.v` or to the manifest. The paper.
