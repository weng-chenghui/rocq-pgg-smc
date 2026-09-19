# Landing probe: the PSL(2,11) spectral no-go file

Probe, 2026-09-19, branch `feat/tableau-extensions-probe`. Logical path
`psl211_nogo_landing`, directory `notes/probes/2026-09-19-psl211-nogo-landing/`.
No permanent file edited, no commit, no `make`. The verbatim source is the
closed probe `notes/probes/2026-09-19-psl211-sc-const/` (SRC), audited for
soundness three times; the spec is
`notes/20260919-psl211-spectral-nogo-landing-design.md`.

**Verdict: GO on every ledger row.** The three SRC probe files merge into one
landing copy of `instances/psl211/psl211_spectral_nogo.v` that compiles in
23.6 s with exit 0, carrying 47 declarations, every one ending in `Qed` or
being a `Definition`. The new corollary the third audit asked for is in.
No `lib/` file is proposed. The comment-only landing copy of
`instances/psl211/psl211_rows.v` is identical to production once comments are
stripped. One stale sentence exists in the production tree, and it is the one
the rows copy rewrites.

## Files

| file | what it is |
|---|---|
| `psl211_spectral_nogo.v` | landing copy of the new `instances/psl211/psl211_spectral_nogo.v` |
| `psl211_rows.v` | landing copy of `instances/psl211/psl211_rows.v`, header comment only |
| `psl211_nogo_fidelity.v` | `Print Assumptions` on all 47 landing declarations, plus the three refutations restated and closed by `exact:` |
| `opaque_vm_test.v` | the four-line measurement behind the N6 finding that `vm_compute` ignores `Local Opaque`; not in `_CoqProject` |
| `_CoqProject` | production `-R` lines with `../../../` prefixes, then `-Q . psl211_nogo_landing` |

## Ledger

| ID | Verdict | Evidence |
|---|---|---|
| N1 | GO | one file, production import paths, 47 declarations in the briefed order, exit 0 |
| N2 | GO | `spectral_cert_reading_constancy` by `exact: sc_const cert` |
| N3 | GO | `psl211_alldecks_constancy_false`, `psl211_alldecks_constancy_false_blockline`, `psl211_dealt_constancy_false`, all three restated in the fidelity file |
| N4 | GO | `psl211_alldecks_no_spectral_cert`, `psl211_alldecks_constancy_false_word584`, with infotheo's `leq_var_dist` in place of SRC's local copy |
| N5 | GO | table below, all 48 SRC declarations dispositioned |
| N6 | GO with two recorded deviations | table below; two sentences are 0.35 s and 0.41 s slower than SRC's rounded figures, both `perm_filter` steps |
| N7 | GO | comment-stripped copy identical to production, 4485 characters, verified with a nesting- and string-aware stripper |
| N8 | GO | exactly one stale passage in the production tree, `instances/psl211/psl211_rows.v:40-44`, which the rows copy rewrites; the manifest and the facade carry nothing this result touches |
| N9 | GO | 50 `Print Assumptions`: 28 `Closed under the global context`, 21 the three `boolp` axioms, 1 two of them. No custom axiom |
| N10 | GO | rename table below, zero whole-word collisions over 583 files |
| N11 | GO | a landing compiles two production files, both with an empty reverse closure |

## Compile table

Driven from Python through the machine-wide `rocq1` lock, `rocq compile -time`,
real `subprocess.returncode`, nothing piped in between. Fresh directory, `.vo`
files removed first.

| file | wall | slowest sentence | exit |
|---|---|---|---|
| `psl211_spectral_nogo.v` | 23.6 s | 6.53 s | 0 |
| `psl211_rows.v` | 6.3 s | 1.53 s (an import) | 0 |
| `psl211_nogo_fidelity.v` | 8.2 s | 1.54 s (an import) | 0 |

SRC compiled the same mathematics as three files in 16.4 + 5.8 + 15.7 = 37.9 s,
each paying its own 4 s of imports. No sentence is over 20 s. One warning is
emitted, on the `From infotheo Require Import ... variation_dist.` line:
`notation-incompatible-prefix` on `_ <| _` against `_ <| _ |> _`. It is not in
the project's suppressed list and it appears in the fidelity file too, so it
follows the import of `variation_dist` and not anything this file writes. A
landing brings it into `instances/psl211/`, where no file imports
`variation_dist` today.

### N6, per-sentence against SRC

| sentence | SRC | here | delta |
|---|---|---|---|
| `perm_filter` step of `psl211_blockline1_fiberE` (SRC `psl211_samechir_fiberE`) | 6.1 s | 6.53 s | +0.43 s |
| `perm_filter` step of `psl211_dealt_fiberE` | 6.1 s | 6.47 s | +0.37 s |
| `vm_compute` of `psl211_blockline1_raw_countE` | 5.1 s | 5.42 s | +0.32 s |
| `vm_compute` of `psl211_dealt_raw_countE` | not reported | under 0.2 s | — |

Both `perm_filter` steps and the one `vm_compute` exceed the tenth-of-a-second
threshold. SRC's figures are the rounded ones of its own STATUS table and were
not re-measured here, because re-running SRC would rewrite the `.vo` files of a
closed probe. The three deltas are 5 to 7 percent on sentences of 5 to 6.5 s and
the merged file loads a strictly larger environment than any single SRC file
(`variation_dist`, `pgg_collusion_bound`, `psl211_mixing`, `pgg_weighted_words`
and `algebraic_rigidity` are now present while the `psl211_samechir` block
elaborates). Nothing was reordered that could account for them.

### N6, reduction hazards

Every `vm_compute` in the landing file runs over plain `nat` tables:
`psl211_blockline1_row_size`, `psl211_blockline1_corow_size`,
`psl211_blockline1_raw_countE` and `psl211_dealt_raw_countE`. None touches
`inord`, `{ffun 'I_n}`, `{set 'I_n}`, `{perm 'I_n}` or `psl211_alldecks_seq`
as an ordinal object.

Merging three files into one changes what is opaque where. Measured, not
inferred: `vm_compute` ignores `Local Opaque`. `opaque_vm_test.v` in this
directory declares a four-element `seq nat`, seals it with `Local Opaque` and
closes `count (fun n => n == 3) tbl = 1` by `vm_compute`, exit 0. That is what
lets `psl211_dealt_raw_countE` keep its place at the end of the file while
`psl211_elem_table` has been opaque since the block-line section.

Two deviations from SRC's placement, both deliberate:

1. SRC file 2 sealed `psl211_perdeck_raw_count` at the top of its own file.
   In the merged order that point falls after the whole block-line section, so
   the seal is folded into the section's existing
   `Local Opaque psl211_alldecks_view psl211_elem_table` line. It is therefore
   earlier than SRC's, never later. Nothing between the two positions names
   `psl211_perdeck_raw_count`, and the values it takes come from
   `psl211_perdeck_raw_countE` of `psl211_models.v`, which is already proved.
2. SRC file 3's `Local Opaque psl211_elem_table` is dropped as redundant: the
   table is already opaque at that point in the merged file.

The two remaining seals sit exactly where SRC has them:
`Local Opaque psl211_blockline1_raw_count` after `psl211_blockline1_fiberE`,
and `Local Opaque psl211_dealt_raw_count` after `psl211_dealt_fiberE`. Each
proof after a seal was checked to need only the sealed constant's two values,
and the file compiles.

One block moved: `psl211_alldecks_static_obs_set0` and
`psl211_alldecks_constancy_set0` sit at the end of the landing file rather than
in the middle, per the briefed order. They now elaborate with five constants
opaque that were transparent for them in SRC. Neither proof reaches any of
them: the first rewrites with `psl211_alldecks_static_obsE`, `in_set0` and
`ffunE`, the second with the first.

## N10, names

No naming audit was ever run on SRC. Every landing name was reviewed against
`instances/psl211/psl211_models.v`, `reconstruct/s5_nogo.v` and the MathComp
conventions: state the proposition, carrier qualifiers last, no abbreviation a
reader cannot expand.

Two families were renamed.

- `sc_const` is a record-field abbreviation. A sibling audit rejected the same
  construction at the five-card instance in favour of the domain word
  *constancy*, so `sc_const_prop` becomes `coalition_reading_constancy` and
  every `_sc_const_` in a lemma name becomes `_constancy_`. The new name says
  who reads, what is read and what is claimed of it, and it needs no knowledge
  of the record's field spelling.
- `samechir` abbreviates *same chirality* and cannot be expanded by a reader
  who has not been told. The block is renamed after what actually distinguishes
  its deck description from `psl211_perdeck_deal`, which is the block line, and
  *block line* is the term the tree already uses for that coordinate. The block
  is then named the way `psl211_models.v` names its own, after the deck
  description it is built on.

| SRC name | landing name | reason |
|---|---|---|
| `sc_const_prop` | `coalition_reading_constancy` | field abbreviation to domain word |
| `sc_const_prop_field` | `spectral_cert_reading_constancy` | states what holds of a certificate, not where it came from |
| `psl211_alldecks_sc_const_false` | `psl211_alldecks_constancy_false` | follows the proposition |
| `psl211_alldecks_sc_const_false_supp` | `psl211_alldecks_constancy_false_supp` | same |
| `psl211_alldecks_sc_const_false_close` | `psl211_alldecks_constancy_false_close` | same |
| `psl211_alldecks_sc_const_false_word` | `psl211_alldecks_constancy_false_word` | same |
| `psl211_alldecks_sc_const_false_word584` | `psl211_alldecks_constancy_false_word584` | same |
| `psl211_alldecks_sc_const_set0` | `psl211_alldecks_constancy_set0` | same |
| `psl211_dealt_sc_const_false` | `psl211_dealt_constancy_false` | same |
| `psl211_samechir_deal` | `psl211_blockline1_deal` | expandable, and names the coordinate that differs |
| `psl211_samechir_view` | `psl211_blockline1_view` | same |
| `psl211_samechir_test` | `psl211_blockline1_test` | same |
| `psl211_samechir_testE` | `psl211_blockline1_testE` | same |
| `psl211_samechir_seq` | `psl211_blockline1_seq` | same |
| `psl211_samechir_row_size` | `psl211_blockline1_row_size` | same |
| `psl211_samechir_corow_size` | `psl211_blockline1_corow_size` | same |
| `psl211_samechir_seqE` | `psl211_blockline1_seqE` | same |
| `psl211_samechir_raw_count` | `psl211_blockline1_raw_count` | same |
| `psl211_samechir_raw_countE` | `psl211_blockline1_raw_countE` | same |
| `psl211_samechir_fiber` | `psl211_blockline1_fiber` | same |
| `psl211_samechir_fiberE` | `psl211_blockline1_fiberE` | same |
| `psl211_samechir_massE` | `psl211_blockline1_massE` | same |
| `psl211_samechir_law_neq` | `psl211_blockline1_law_neq` | same |
| `var_dist_point_le` | infotheo's `leq_var_dist` | same statement, same arity, already in the library |

Proof-local hypothesis names. SRC's `psl211_samechir_law_neq` used `L1` and
`L0` for the two masses, and `L1` spells a term this project bars for a
distance. The landed `psl211_perdeck_law_neq` of `psl211_models.v` uses `Lt`
and `Lf` for the two chiralities' masses; the same scheme suffixed by the block
line gives `Lb0` and `Lb1`, with `Cb0`, `Cb1` for the two fiber cardinalities,
`Eb0`, `Eb1` for the two reader identifications and `Hb0`, `Hb1` for the two
raw counts. No other occurrence of that term exists in any proof script here.

Names kept unchanged, with the reason: `psl211_perdeck_coalition_le3`,
`psl211_perdeck_coalition_below_k` (the `k` is `profile_k`),
`psl211_perdeck_ideal_lawE`, `psl211_perdeck_fiber_true0`,
`psl211_alldecks_raw_viewE`, `psl211_alldecks_static_obs_set0`,
`psl211_alldecks_cert_ideal_close`, `psl211_alldecks_no_spectral_cert`,
`psl211_alldecks_no_spectral_cert0`, `fdistmap_point_condE` and the whole
`psl211_dealt_*` block other than its headline. Each is built from words the
tree already uses, and each states its proposition.

New name: `psl211_alldecks_constancy_false_blockline`, the corollary. The
qualifier last says which pair of run arguments the proof spends.

File name: `psl211_spectral_nogo`, on the precedent of `reconstruct/s5_nogo.v`
and with the instance prefix the `instances/psl211/` directory uses throughout.

Collision scan: the 47 landing names plus the file name, as whole words with
Python `re` and `\b`, over 583 `.v` files, the production tree plus the
installed infotheo and mathcomp trees, excluding this directory. **Zero hits.**
`grep -E '[[:<:]]'` was not used: on this Mac it matches nothing and would have
reported a silent false negative.

## N5, every SRC declaration

`L` lands, `LR` lands renamed, `RL` replaced by a library lemma, `P` stays in
the probe.

| SRC declaration | source file | | landing name / reason |
|---|---|---|---|
| `sc_const_prop` | 1 | LR | `coalition_reading_constancy` |
| `sc_const_prop_field` | 1 | LR | `spectral_cert_reading_constancy` |
| `psl211_perdeck_coalition_le3` | 1 | L | discharges the threshold premise |
| `psl211_perdeck_coalition_below_k` | 1 | L | same |
| `psl211_alldecks_sc_const_false` | 1 | LR | `psl211_alldecks_constancy_false` |
| `psl211_alldecks_static_obs_set0` | 1 | L | needed by the empty-coalition lemma |
| `psl211_alldecks_sc_const_set0` | 1 | LR | `psl211_alldecks_constancy_set0` |
| `psl211_samechir_deal` | 1 | LR | `psl211_blockline1_deal` |
| `psl211_samechir_view` | 1 | LR | `psl211_blockline1_view` |
| `psl211_samechir_test` | 1 | LR | `psl211_blockline1_test` |
| `psl211_samechir_testE` | 1 | LR | `psl211_blockline1_testE` |
| `psl211_alldecks_raw_viewE` | 1 | L | the deck description left free |
| `psl211_samechir_seq` | 1 | LR | `psl211_blockline1_seq` |
| `psl211_samechir_row_size` | 1 | LR | `psl211_blockline1_row_size` |
| `psl211_samechir_corow_size` | 1 | LR | `psl211_blockline1_corow_size` |
| `psl211_samechir_seqE` | 1 | LR | `psl211_blockline1_seqE` |
| `psl211_samechir_raw_count` | 1 | LR | `psl211_blockline1_raw_count` |
| `psl211_samechir_raw_countE` | 1 | LR | `psl211_blockline1_raw_countE` |
| `psl211_samechir_fiber` | 1 | LR | `psl211_blockline1_fiber` |
| `psl211_samechir_fiberE` | 1 | LR | `psl211_blockline1_fiberE` |
| `psl211_samechir_massE` | 1 | LR | `psl211_blockline1_massE` |
| `psl211_samechir_law_neq` | 1 | LR | `psl211_blockline1_law_neq` |
| `var_dist_point_le` | 2 | RL | infotheo's `leq_var_dist`, `probability/variation_dist.v:51` |
| `fdist_uniform_close_supp` | 2 | P | proved in SRC, cited by no headline and by neither header |
| `fdistmap_point_condE` | 2 | L | kept local, two lines from `fdistmapE` |
| `psl211_perdeck_ideal_lawE` | 2 | L | the one consequence both quantitative refutations spend |
| `psl211_perdeck_fiber_true0` | 2 | L | needed by the support refutation |
| `psl211_alldecks_sc_const_false_supp` | 2 | LR | `psl211_alldecks_constancy_false_supp` |
| `psl211_alldecks_sc_const_false_close` | 2 | LR | `psl211_alldecks_constancy_false_close` |
| `psl211_alldecks_cert_ideal_close` | 2 | L | reads the certificate's identification field |
| `psl211_alldecks_no_spectral_cert` | 2 | L | the certificate theorem |
| `psl211_alldecks_no_spectral_cert0` | 2 | L | cited by a header sentence |
| `psl211_alldecks_sc_const_false_word` | 2 | LR | `psl211_alldecks_constancy_false_word` |
| `psl211_alldecks_sc_const_false_word584` | 2 | LR | `psl211_alldecks_constancy_false_word584` |
| `psl211_dealt_decktbl` | 3 | L | |
| `psl211_dealt_decktblE` | 3 | L | |
| `psl211_dealt_decktbl_mod` | 3 | L | |
| `psl211_dealt_view` | 3 | L | |
| `psl211_dealt_test` | 3 | L | |
| `psl211_dealt_testE` | 3 | L | |
| `psl211_dealt_raw_count` | 3 | L | |
| `psl211_dealt_raw_countE` | 3 | L | |
| `psl211_dealt_static_obsE` | 3 | L | |
| `psl211_dealt_raw_viewE` | 3 | L | |
| `psl211_dealt_fiber` | 3 | L | |
| `psl211_dealt_fiberE` | 3 | L | |
| `psl211_dealt_massE` | 3 | L | |
| `psl211_dealt_sc_const_false` | 3 | LR | `psl211_dealt_constancy_false` |
| six `Eval vm_compute in` | 4 | P | `psl211_deck_diag.v` is a diagnostic and declares nothing |

New in the landing, in no SRC file:
`psl211_alldecks_constancy_false_blockline`, the corollary of round 2's SF12.

### Why `psl211_alldecks_constancy_false_supp` lands

The rewritten "Not claimed" paragraph of `psl211_rows.v` says the field fails
"at every ideal whose support is exactly the shuffle group". That sentence is
this lemma and nothing else, so it lands, and with it its two supports,
`psl211_perdeck_fiber_true0` and `fdistmap_point_condE`.

`fdist_uniform_close_supp` is cited by neither header and by no headline. It
stays in SRC.

### Why `psl211_alldecks_constancy_set0` lands

A reader of a no-go file asks whether the refuted field is false for a trivial
reason, namely that its quantifier over coalitions admits a reading that no law
can make constant. This lemma answers that in the file, at the cost of two
short proofs with no reduction hazard: at the empty coalition the statement
holds for every law, so a refutation has to spend a nonempty coalition. Without
it the answer lives only in a probe.

### The `lib/` decision: no new file

Two lemmas were candidates.

- `var_dist_point_le` is infotheo's `leq_var_dist`
  (`probability/variation_dist.v:51`, `` `| p x - q x | <= d(p, q) ``), with the
  same arity: `A` implicit, `p`, `q`, `x` explicit, so SRC's
  `var_dist_point_le _ _ _` becomes `leq_var_dist _ _ _`. It is dropped. One
  call site lands, in `psl211_alldecks_constancy_false_close`; the other was
  inside `fdist_uniform_close_supp`, which does not land.
- `fdistmap_point_condE` is two lines from infotheo's `fdistmapE`
  (`probability/fdist.v:377`), which states the same sum with the preimage as a
  set membership instead of a bigop condition. `reconstruct/design_privacy.v`'s
  `uniform_fdistmap_pointE` and `uniform_fdistmap_fiberTE` are about a uniform
  law on a set and do not cover a general `p`. So it is genuinely a change of
  shape and not a new fact, and by the brief's own test a two-line consequence
  of a library lemma stays local. It is kept in the no-go file with a source
  comment saying so.

Nothing else survives, so no `lib/` file is proposed and no name is put forward.

## N8, the production tree

Searched for the propositions and not the names, over every directory in
`_CoqProject` including `legacy/`: that the all-decks constancy is unmeasured,
that the dealt-mode failure is a raw count or a `vm_compute`, and that
PSL(2,11) has no spectral arm, no word row, or mixing theorems carried by no
row. Patterns used, case-insensitively: `nobody has measured`, `unmeasured`,
`no spectral`, `spectral arm`, `no word row`, `constancy field`, `sc_const`,
`Absent capab`, `no row`, `carried by no`, `raw count`, `three seats`,
`2-transitive`, `not 3-transitive`.

**One hit.**

`instances/psl211/psl211_rows.v:40-44`, current text:

> Not claimed. There is no spectral arm for this dealer: a certificate's
> constancy field asks that a coalition's reading of the ideal cut not vary
> with the run argument, which fails at three seats under the dealt mode at
> the group-uniform ideal, and under the all-decks dealer it is a different
> statement nobody has measured.

The last clause is false after this result, and the opening sentence overstates:
what is excluded is a range of epsilon and not the arm. The landing copy in this
directory rewrites the passage.

**Read in full and clean.**

- `manifest/pgg_analysis_manifest.v`, Row 9, the twelve-card chirality
  instance's all-decks dealer, `:564-605`. Its bound-or-certificate field names
  `PSL211Analysis.marginal_bound` and `PSL211Analysis.certificate_bundle`, its
  model transfer is "none claimed", and its missing premise is "none: the cut
  this model draws is the uniform distribution on the group already, so the
  path compares no idealized model". Every one of those stays true. The row
  claims no spectral arm and gives no reason for its absence, so nothing there
  is made stale.
- The manifest's "Absent capabilities" paragraph, `:660-690`. It discusses the
  five-card development and the S_5 finite-word path and never mentions
  PSL(2,11). Clean.
- `instances/psl211/psl211_analysis.v` header, `:1-53`. A facade contract and a
  check table of aliases. No claim about the spectral arm, the constancy field
  or the word model. Clean.
- `instances/psl211/psl211_mixing.v` header. States the 2^-40 certificate and
  what is not in the file. It does not say its theorems are carried by no row.
  Clean.
- `instances/psl211/psl211_profile.v:80` and `:103` mention
  `psl211_word_mixing` as the payer of the 2^-40. Both stay true.

Nothing in the manifest or the facade is edited here, per the brief.

**Incidental, outside this result's scope.**
`manifest/pgg_analysis_manifest.v:684` writes "full-L1 distance one from group
uniform" about the S_5 word path. That spells, for a distance, the term this
project bars. It is not made false by anything here and belongs to whoever owns
that file this week.

## Header of the landing copy

Boxed, 80 bytes a line, checked in Python on the byte length. It states what the
file proves and its position: what the arm's fifth field asks for, and per mode
what the run argument is. All-decks, the run argument is the public deck
description and the field fails between two deck descriptions of one chirality
as well as between the two chiralities, so no refutation here is a proof of
leakage and the exact arm's independence, `psl211_alldecks_static_indep`, is a
separate theorem about the all-decks law. Dealt, the run argument is the secret
and the field fails because the group is 2-transitive and not 3-transitive,
where `pgl27_word_view_const` proves the same field at PGL(2,7).

What is not claimed: the arm is not shown unavailable, a certificate exists near
infotheo's ceiling of 2 on the sum of absolute differences, and that occupancy
is argued and not compiled. Its premise is compiled and cited,
`psl211_alldecks_uniq` at `instances/psl211/psl211_alldecks.v:421-429`.

The computed diagnostics 360, 600 and 10/11 do not appear. One sentence sends a
reader to `notes/probes/2026-09-19-psl211-sc-const/` for the reading
multiplicity measurements.

The index names every one of the 47 declarations and no other name.

## N9, assumptions

50 `Print Assumptions` in `psl211_nogo_fidelity.v`, 47 landing declarations plus
the three restatements.

- 28 `Closed under the global context`: the two coalition-cardinal lemmas and
  every combinatorial declaration of the block-line and dealt blocks, including
  both `vm_compute` count lemmas and `psl211_perdeck_fiber_true0`.
- 21 carry exactly `propositional_extensionality`,
  `functional_extensionality_dep` and `constructive_indefinite_description`.
- 1, `psl211_alldecks_static_obs_set0`, carries
  `propositional_extensionality` and `functional_extensionality_dep` only.

No custom axiom, no `Admitted`, `Abort`, `Axiom`, `Parameter` or `admit`
anywhere in this directory, checked with a whole-word scan.

## N11, cost

From `.Makefile.rocq.d`, reverse closures over `.vo` nodes.

| production file | change | reverse-dependants | `psl211_endpoints.vo` in closure |
|---|---|---|---|
| `instances/psl211/psl211_spectral_nogo.v` | new | 0 (nothing imports it) | no |
| `instances/psl211/psl211_rows.v` | header comment | 0 | no |

A landing therefore compiles exactly two files and one line is added to
`_CoqProject`. `instances/psl211/psl211_endpoints.v` is loaded by the new file
and never compiled: it was not touched, not compiled and not opened in this
probe. No file whose reverse closure contains it is edited;
`security/pgg_collusion_bound.v` (105 reverse-dependants, `psl211_endpoints` in
closure) is imported and not edited.

## Proofs: what needed a fix

Nothing broke in the move. Every proof body is SRC's, with three mechanical
substitutions and no tactic reordering.

1. `var_dist_point_le _ _ _` becomes `leq_var_dist _ _ _`, once, in
   `psl211_alldecks_constancy_false_close`. Same statement, same arity.
2. Every renamed constant is renamed at its uses.
3. The proof-local `L1`, `L0`, `C1`, `C0`, `E1`, `E0`, `H1`, `H0` of
   `psl211_samechir_law_neq` become `Lb0`, `Lb1`, `Cb0`, `Cb1`, `Eb0`, `Eb1`,
   `Hb0`, `Hb1`, with the numeral now naming the block line rather than the
   value, which is why the pairs are also swapped in reading order.

One proof is new, the four-line corollary:

    Corollary psl211_alldecks_constancy_false_blockline (R : realType) :
      ~ coalition_reading_constancy psl211_alldecks_params
          ((`U psl211_G_pos) : R.-fdist cutT).
    Proof.
    move=> Hconst.
    move/negP: (psl211_blockline1_law_neq R); apply; apply/eqP.
    exact: (Hconst psl211_perdeck_coalition psl211_perdeck_coalition_below_k
      (true, psl211_perdeck_deal) (true, psl211_blockline1_deal)).
    Qed.

Its statement is the same as `psl211_alldecks_constancy_false`'s. The two differ
in the pair of run arguments their proofs spend, which is the whole content of
the claim that the failure does not need the secret to move, and the statement
comment says so in those words.

## What in the spec or in SRC turned out wrong

1. **SRC's Q6 home table is superseded on two rows.** It proposed
   `fdistmap_point_condE` for `reconstruct/design_privacy.v` and
   `fdist_uniform_close_supp` for a new `lib/var_dist_supp.v`. The first is a
   two-line consequence of a library lemma and stays local by the brief's own
   test; the second does not land at all. So the sibling Kim landing's
   `lib/var_dist_supp.v` gets nothing from this probe.
2. **SRC's Q6 table also proposed splitting the landing across
   `psl211_models.v` and `psl211_rows.v`.** The spec overrides that with a new
   file, and the override is right: `psl211_models.v` has nine
   reverse-dependants and deliberately imports nothing from the manifest, while
   the constancy statements name `SpectralCert`.
3. **SRC's `Local Opaque` placement does not survive the merge unchanged.**
   Two of the four seals move or disappear, as recorded under N6. SRC's own
   note, that placing a seal before the `fiberE` lemma that unfolds it gives
   "is opaque", is about `psl211_dealt_raw_count` and still holds: that seal is
   after `psl211_dealt_fiberE` here as it is there.
4. **`vm_compute` ignores `Local Opaque`.** This was not recorded anywhere and
   it is what makes the briefed file order possible at all: the dealt block's
   count is evaluated at the end of the file, long after `psl211_elem_table` was
   sealed for the block-line block. Measured in `opaque_vm_test.v`.
5. **A warning follows the import of `variation_dist`**, not anything written
   here. Reported under the compile table so that a landing is not surprised by
   it.

## Reproduction

    cd notes/probes/2026-09-19-psl211-nogo-landing
    python3 <scratchpad>/nogo_compile.py

The driver reads `_CoqProject`, builds one `rocq compile -time` command per
file, and runs each through
`<scratchpad>/rocq1 900 16000`, the machine-wide single-Rocq lock, with
`subprocess.run` and no pipe, so the exit code printed is the real one. Two
other provers held the lock during this probe and the driver waited for it.
Nothing was run under `timeout` or `/usr/bin/time`, and `make` was never
invoked.

## Final state verified

Two comment sentences were corrected after the clean rebuild, one in each
landing copy. Both files were recompiled from source afterwards and both exit
0. The wall times of those two runs, 523.5 s and 312.9 s, are almost entirely
time spent waiting for the machine-wide Rocq lock while a sibling prover held
it; the compute figures in the compile table are the clean-rebuild ones.

The fidelity file's 50 `Print Assumptions` cover all 47 declarations of the
landing copy, in the file's own order, plus the three restatements. Checked
mechanically, not by eye.
