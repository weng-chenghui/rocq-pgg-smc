# Landing probe: the PSL(2,11) spectral constancy file

**Fix pass 1, 2026-09-19.** Two independent audits were run on the state this
record originally described, `soundness-audit.md` (GO, SA1 to SA8 should-fix)
and `naming-audit.md` (NO-GO, B1 blocking). The main session ruled on them as
D1 to D12 and this pass applied those rulings. Every file touched has its
pre-fix copy under `history/`, suffixed `.2026-09-19-before-fix1`. The changes
are names, comments, the header index and this record; no proof body changed
except where a renamed identifier or a renamed proof-local hypothesis occurs
in it, and the mathematics is unchanged but for one withdrawn corollary,
recorded under N3.

Probe, 2026-09-19, branch `feat/tableau-extensions-probe`. Logical path
`psl211_nogo_landing`, directory `notes/probes/2026-09-19-psl211-nogo-landing/`.
No permanent file edited, no commit, no `make`. The verbatim source is the
closed probe `notes/probes/2026-09-19-psl211-sc-const/` (SRC), audited for
soundness three times; the spec is
`notes/20260919-psl211-spectral-nogo-landing-design.md`.

**Verdict: GO on every ledger row.** The three SRC probe files merge into one
landing copy of `instances/psl211/psl211_spectral_constancy.v` carrying 46
declarations, every one ending in `Qed` or being a `Definition`.
No `lib/` file is proposed. The comment-only landing copy of
`instances/psl211/psl211_rows.v` is identical to production once comments are
stripped. One stale sentence exists in the production tree, and it is the one
the rows copy rewrites.

## Files

| file | what it is |
|---|---|
| `psl211_spectral_constancy.v` | landing copy of the new `instances/psl211/psl211_spectral_constancy.v` |
| `psl211_rows.v` | landing copy of `instances/psl211/psl211_rows.v`, header comment only |
| `psl211_nogo_fidelity.v` | `Print Assumptions` on all 46 landing declarations, plus the two refutations restated and closed by `exact:` |
| `opaque_vm_test.v` | three `Eval` sentences behind the N6 finding that `vm_compute` ignores `Local Opaque`; not in `_CoqProject` |
| `history/` | the pre-fix-pass copy of every file this pass touched |
| `_CoqProject` | production `-R` lines with `../../../` prefixes, then `-Q . psl211_nogo_landing` |

## Ledger

| ID | Verdict | Evidence |
|---|---|---|
| N1 | GO | one file, production import paths, 46 declarations in the briefed order, exit 0 |
| N2 | GO | `spectral_cert_reading_constancy` by `exact: sc_const cert` |
| N3 | Deviation from decision 3, recorded below | `psl211_alldecks_constancy_false` and `psl211_dealt_constancy_false`, both restated in the fidelity file; the third refutation is withdrawn, see the note below |
| N4 | GO | `psl211_alldecks_no_small_eps_cert`, `psl211_alldecks_constancy_false_word584`, with infotheo's `leq_var_dist` in place of SRC's local copy |
| N5 | GO | table below, all 48 SRC declarations dispositioned |
| N6 | GO with two recorded deviations | table below; two sentences are 0.35 s and 0.41 s slower than SRC's rounded figures, both `perm_filter` steps |
| N7 | GO | comment-stripped copy identical to production, 4485 characters, verified with a nesting- and string-aware stripper |
| N8 | GO | exactly one stale passage in the production tree, `instances/psl211/psl211_rows.v:40-44`, which the rows copy rewrites; the manifest and the facade carry nothing this result touches |
| N9 | GO | 48 `Print Assumptions`: 28 `Closed under the global context`, 19 the three `boolp` axioms, 1 two of them. No custom axiom |
| N10 | GO | rename table below, zero whole-word collisions over 583 files |
| N11 | GO | a landing compiles two production files, both with an empty reverse closure |

### N3, the third refutation withdrawn

`psl211_alldecks_constancy_false_blockline` had a statement character for
character that of `psl211_alldecks_constancy_false`, so it stated no fact a
reader could cite separately: the two differed only in the pair of run
arguments their proofs spent, which is not visible in a statement. It is
removed from the landing copy, with its `Print Assumptions` and its fidelity
restatement, and its text is kept in `history/`. The proposition it was
carried for, that the constancy field fails without the secret moving, is
carried by `psl211_blockline1_law_neq`, whose statement does name the two run
arguments `(true, psl211_perdeck_deal)` and `(true, psl211_blockline1_deal)`.
The spec's soundness invariant 4 is therefore carried by
`psl211_blockline1_law_neq`, and the rows header and the file header now cite
that lemma where they cited the corollary.

## Compile table

Driven from Python through the machine-wide `rocq1` lock, `rocq compile -time`,
real `subprocess.returncode`, nothing piped in between. Fresh directory, `.vo`
files removed first.

| file | wall | slowest sentence | exit |
|---|---|---|---|
| `psl211_spectral_constancy.v` | 24.3 s | 6.83 s | 0 |
| `psl211_rows.v` | 6.2 s | 1.57 s (an import) | 0 |
| `psl211_nogo_fidelity.v` | 8.5 s | 1.54 s (an import) | 0 |
| `opaque_vm_test.v` | 0.2 s | 0.11 s (an import) | 0 |

These are the fix-pass figures, in the order compiled. The main file has 363
sentences and 24.04 s of sentence time.

SRC compiled the same mathematics as three files in 16.4 + 5.8 + 15.7 = 37.9 s,
each paying its own 4 s of imports. No sentence is over 20 s.

One warning is emitted, on the `From infotheo Require Import ...` line:
`notation-incompatible-prefix` on `_ <| _` against `_ <| _ |> _`. It is not in
the project's suppressed list. It is not new. It follows the first infotheo
`Require` beside mathcomp's `fingroup`, with or without `variation_dist`, and
`instances/psl211/psl211_rows.v`, `instances/psl211/psl211_profile.v` and
`instances/psl211/psl211_mixing.v` already emit it. Nothing is added to
`_CoqProject`. The soundness audit established both halves with
`audit-soundness/warn_with.v` and `audit-soundness/warn_without.v`; the
sentence this record carried before the fix pass, that the warning follows the
import of `variation_dist` and that no file of `instances/psl211/` imports it
today, was false in both halves.

### N6, per-sentence against SRC

| sentence | SRC | here | delta |
|---|---|---|---|
| `perm_filter` step of `psl211_blockline1_fiberE` (SRC `psl211_samechir_fiberE`) | 6.1 s | 6.83 s | +0.73 s |
| `perm_filter` step of `psl211_dealt_fiberE` | 6.1 s | 6.63 s | +0.53 s |
| `vm_compute` of `psl211_blockline1_raw_countE` | 5.1 s | 5.21 s | +0.11 s |
| `vm_compute` of `psl211_dealt_raw_countE` | not reported | under 0.2 s | — |

Provenance of the "here" column, which the fix pass corrected. The figures are
read from the stdout of `rocq compile -time` on the fix-pass compile of
`psl211_spectral_constancy.v`, matched to source lines through the character
offsets the `-time` output carries. They are not read from a `.v.timelog`. The
directory holds four `.v.timelog` files, for `psl211_rows.v`,
`psl211_nogo_fidelity.v`, `opaque_vm_test.v` and the old file name
`psl211_spectral_nogo.v`. All four were written before this fix pass and so
describe pre-fix content; none is regenerated here, because `rocq compile
-time` writes its per-sentence figures to stdout and not to that file, and none
is deleted, because nothing under `notes/probes/` is deleted. SRC holds no
`.v.timelog` at all, so the per-sentence
comparison this row asks for cannot be reproduced from SRC's artifacts either
way, and SRC's figures below are the rounded ones of its own STATUS table,
not re-measured, because re-running SRC would rewrite the `.vo` files of a
closed probe.

Both `perm_filter` steps and the one `vm_compute` exceed the tenth-of-a-second
threshold. The deltas are 2 to 12 percent on sentences of 5 to 7 s and the
merged file loads a strictly larger environment than any single SRC file
(`variation_dist`, `pgg_collusion_bound`, `psl211_mixing`, `pgg_weighted_words`
and `algebraic_rigidity` are now present while the block-line block
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
evaluates `count (fun n => n == 3) tbl` three ways: `simpl` leaves the count
unevaluated with `tbl` folded, `cbv` unfolds `count` and leaves `tbl` folded,
and `vm_compute` prints `1`. That is what lets `psl211_dealt_raw_countE` keep
its place at the end of the file while `psl211_elem_table` has been opaque
since the block-line section.

The earlier version of that file closed `count (fun n => n == 3) tbl = 1` by
`vm_compute` and was replaced in the fix pass, its text kept in `history/`. A
lemma does not isolate `vm_compute`: the soundness audit's
`audit-soundness/opaque_mut.v` closes the same goal by `by []` under the same
seal, because ssreflect's `done` reaches it through kernel conversion, which
ignores the oracle as well. The three `Eval` sentences show what the sentence
above claims; the lemma did not.

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
| `psl211_alldecks_no_spectral_cert` | `psl211_alldecks_no_small_eps_cert` | the old name dropped the condition that makes it true, and `_eps_` is the tree's word for a certificate's number |
| `psl211_alldecks_no_spectral_cert0` | `psl211_alldecks_no_zero_eps_cert` | same, and the trailing `0` read as a value on this file's own convention |
| `var_dist_point_le` | infotheo's `leq_var_dist` | same statement, same arity, already in the library |

Proof-local hypothesis names. SRC's `psl211_samechir_law_neq` named its eight
proof-local hypotheses with bare capitals L, C, E and H suffixed by the digits
0 and 1, and the L form with digit one spells a term this project bars for a
distance, L being a word length here. The fix pass settled one scheme for the
whole file, stated in the header: a leading C is a fiber cardinality, U a mass
at the group-uniform law, L a mass at the ideal, E a reader identification, T a
step of an inequality chain and H every other named fact; a C, U, L or E suffix
names the coordinate the quantity is taken at, `t` and `f` the chirality and
`j0` and `j1` the block line; and a trailing digit is an index and never a
value. So `psl211_blockline1_law_neq` carries `Cj0`,
`Cj1`, `Uj0`, `Uj1`, `Ej0`, `Ej1`, `Hj0` and `Hj1`; the fiber cardinalities are
`Ct` and `Cf` in `psl211_alldecks_constancy_false_close` and
`psl211_dealt_constancy_false`, where they were `H0` and `H1`, `Cf` alone in
`_supp`, where it was `Hcard1`, and a third `Ct` in
`psl211_perdeck_fiber_true0`, where it was `Hcard0`; and
`psl211_alldecks_no_zero_eps_cert`'s hypothesis is `Heps` where it was `H0`,
that digit having named a value. Fix pass 2 brought the file to
that scheme: `Ht0` of `psl211_alldecks_constancy_false_supp` became `Lt`, the
masses `Lt` and `Lf` of `psl211_dealt_constancy_false` became `Ut` and `Uf`,
and `Lj0` and `Lj1` of `psl211_blockline1_law_neq` became `Uj0` and `Uj1`. The
digits surviving in a proof script are the block-line indices `j0` and `j1`,
the chain indices of `T1`, `T2` and `T3` in
`psl211_alldecks_constancy_false_close`, the witness `g0` of
`psl211_alldecks_constancy_false_supp` and the names built on it, and the three
conjunct names of an `and3P` split, where they index the seat.

Names kept unchanged, with the reason: `psl211_perdeck_coalition_le3`,
`psl211_perdeck_coalition_below_k` (the `k` is `profile_k`),
`psl211_perdeck_ideal_lawE`, `psl211_perdeck_fiber_true0`,
`psl211_alldecks_raw_viewE`, `psl211_alldecks_static_obs_set0`,
`psl211_alldecks_cert_ideal_close`, `fdistmap_point_condE` and the whole
`psl211_dealt_*` block other than its main statement. Each is built from words
the tree already uses, and each states its proposition.

File name: `psl211_spectral_constancy`, with the instance prefix the
`instances/psl211/` directory uses throughout and a subject noun, as every
other file in that directory has. The pre-fix name was `psl211_spectral_nogo`,
on the precedent of `reconstruct/s5_nogo.v`; the naming audit's B1 rejected it,
because `s5_nogo.v` proves there is no scheme of the kind it is named after,
while what is proved here is narrower than "no spectral arm" and the file's own
header says so three times. The probe directory and this record keep `nogo`,
and so does `psl211_nogo_fidelity.v`, because they record the work and not the
result. The logical path `psl211_nogo_landing` in `_CoqProject` is probe-local
and does not land.

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
| `psl211_alldecks_no_spectral_cert` | 2 | LR | `psl211_alldecks_no_small_eps_cert`, the certificate theorem |
| `psl211_alldecks_no_spectral_cert0` | 2 | LR | `psl211_alldecks_no_zero_eps_cert`, cited by a header sentence |
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

New in the landing, in no SRC file: nothing. The corollary
`psl211_alldecks_constancy_false_blockline`, which round 2's SF12 asked for and
which this landing added, was withdrawn in the fix pass; see the note under the
ledger.

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
`manifest/pgg_analysis_manifest.v` writes, of the S_5 word path, a distance
named with the barred two-character token, followed by "distance one from group
uniform". It is not made false by anything here and belongs to whoever owns
that file this week.

## Header of the landing copy

Boxed, 80 bytes a line, checked in Python on the byte length. It states what the
file proves and its position: what the arm's fifth field asks for, and per mode
what the run argument is. All-decks, the run argument is a whole deck
description, whose chirality is the secret and whose other three coordinates
are public, and the field fails between two deck descriptions of one chirality
as well as between the two chiralities, so the field asks for constancy in
public data and not for secrecy alone. What a coalition of at most five of the
twelve seats reads about the chirality under the all-decks law is the separate
theorem `psl211_alldecks_static_indep`. Dealt, the run argument is the secret
and the field fails because the group is 2-transitive and not 3-transitive,
where `pgl27_word_view_const` proves the same field at PGL(2,7).

What is not claimed: the arm is not shown unavailable, a certificate exists at
an epsilon near 2, and that occupancy is argued and not compiled. The fix pass
added what that certificate would be worth: its `cert_eps` is that epsilon
twice, near 4, while infotheo's `var_dist` sums the absolute differences of two
laws and so never exceeds 2, so the row such a certificate gives publishes a
number no pair of laws can exceed and bounds nothing. The occupancy's premise
is compiled and cited by name, `psl211_alldecks_uniq` of
`instances/psl211/psl211_alldecks.v`; the line range the header carried before
the fix pass is gone, absolute line numbers being barred from a permanent
comment and that range belonging to a file this one does not control.

The computed diagnostics 360, 600 and 10/11 do not appear. One sentence sends a
reader to `notes/probes/2026-09-19-psl211-sc-const/` for the reading
multiplicity measurements. The one uncompiled measurement left in a statement
comment, that `psl211_dealt_view` is the first numeral at which the two
chiralities' reading multiplicities differ, is removed: what stays is the
compiled part, that the two encoder decks reach that reading under different
numbers of cuts. That matches what was already done at
`psl211_blockline1_view`, whose SRC comment carried an uncompiled count of 660
distinct readings and lost it in the merge.

The index is selective, as `instances/psl211/psl211_models.v` is. It names the
two definitions a reader needs to parse the results and the eleven results the
rows header or a paper would cite, and the occupancy argument is written once,
in the header, rather than again above the certificate theorem. Before the fix
pass it named all 47 declarations over 106 of the header's 174 lines.

## N9, assumptions

48 `Print Assumptions` in `psl211_nogo_fidelity.v`, 46 landing declarations plus
the two restatements. Counted mechanically from the compiler's output.

- 28 `Closed under the global context`: the two coalition-cardinal lemmas and
  every combinatorial declaration of the block-line and dealt blocks, including
  both `vm_compute` count lemmas and `psl211_perdeck_fiber_true0`.
- 19 carry exactly `propositional_extensionality`,
  `functional_extensionality_dep` and `constructive_indefinite_description`.
- 1, `psl211_alldecks_static_obs_set0`, carries
  `propositional_extensionality` and `functional_extensionality_dep` only.

No custom axiom, no `Admitted`, `Abort`, `Axiom`, `Parameter` or `admit`
anywhere in this directory, checked with a whole-word scan.

## N11, cost

From `.Makefile.rocq.d`, reverse closures over `.vo` nodes.

| production file | change | reverse-dependants | `psl211_endpoints.vo` in closure |
|---|---|---|---|
| `instances/psl211/psl211_spectral_constancy.v` | new | 0 (nothing imports it) | no |
| `instances/psl211/psl211_rows.v` | header comment | 0 | no |

A landing therefore compiles exactly two files and one line is added to
`_CoqProject`. That line is `instances/psl211/psl211_spectral_constancy.v`, and
it goes directly before `instances/psl211/psl211_rows.v`, that is between
`instances/s5/s5_rows.v` and `instances/psl211/psl211_rows.v`. The reason is
that production's `_CoqProject` lists a file after the files it imports,
`manifest/pgg_analysis_manifest.v` before `manifest/pgg_tableau.v` and
`instances/psl211/psl211_models.v` before `instances/psl211/psl211_analysis.v`,
so the new file has to follow `manifest/pgg_tableau.v`, which it imports, and
putting it before the rows block keeps the four rows files together as the last
instance-level block they are today. `Makefile` delegates to
`rocq makefile -f _CoqProject`, which computes the dependency order itself, so
the position is for a reader and not for the build.
`instances/psl211/psl211_endpoints.v` is loaded by the new file
and never compiled: it was not touched, not compiled and not opened in this
probe. No file whose reverse closure contains it is edited;
`security/pgg_collusion_bound.v`, which has `psl211_endpoints` among its
reverse-dependants, is imported and not edited. The parenthesis this record
carried before the fix pass named the forward closure instead, and
`security/pgg_collusion_bound.vo`'s forward closure is two nodes and does not
contain `psl211_endpoints.vo`.

## Proofs: what needed a fix

Nothing broke in the move. Every proof body is SRC's, with three mechanical
substitutions and no tactic reordering.

1. `var_dist_point_le _ _ _` becomes `leq_var_dist _ _ _`, once, in
   `psl211_alldecks_constancy_false_close`. Same statement, same arity.
2. Every renamed constant is renamed at its uses.
3. Every proof-local hypothesis is renamed to the one file-wide scheme recorded
   under N10. The numeral now names the block line rather than the value, which
   is why the pairs of `psl211_blockline1_law_neq` are also swapped in reading
   order.

One proof was new in this landing, the four-line corollary
`psl211_alldecks_constancy_false_blockline`. The fix pass withdrew it, because
its statement was that of `psl211_alldecks_constancy_false` character for
character and so stated no fact a reader could cite separately. Its text is in
`history/psl211_spectral_nogo.2026-09-19-before-fix1.v`.

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
   sealed for the block-line block. Measured in `opaque_vm_test.v`, by three
   `Eval` sentences and not by a lemma, for the reason under N6.
5. **A warning follows the first infotheo `Require` beside `fingroup`**, not
   the import of `variation_dist` and not anything written here, and three
   files of `instances/psl211/` already emit it. Reported under the compile
   table so that a landing is not surprised by it. This record's pre-fix
   version of that sentence was wrong in both halves.
6. **The spec's decision 3 is reversed.** The corollary it asked for had the
   statement of `psl211_alldecks_constancy_false` character for character, so
   the refutation at one chirality is carried at the law's type by
   `psl211_blockline1_law_neq` and not at the field's type.

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

The fidelity file's 48 `Print Assumptions` cover all 46 declarations of the
landing copy, in the file's own order, plus the two restatements. Checked
mechanically, not by eye.

## Fix pass 1, what was compiled

Four files, in this order, each through the machine-wide `rocq1` lock with
`rocq compile -time`, real `subprocess.returncode`, nothing piped in between:
`psl211_spectral_constancy.v`, `psl211_rows.v`, `psl211_nogo_fidelity.v`,
`opaque_vm_test.v`. All four exit 0. The stale `.vo`, `.vos`, `.vok`, `.glob`
and `.aux` of the old file name were removed after the new name compiled; they
are ignored build products, not records. `make` was never invoked and
`instances/psl211/psl211_endpoints.v` was never compiled.

## Fix pass 2, what changed and what was compiled

Comments and proof-local names only. No statement and no proof body changed
beyond the rebound names. The pre-fix-2 copy of every file touched is in
`history/` under the `2026-09-19-before-fix2` suffix; nothing was deleted.

The two blocking findings of the second audit. The header's naming sentence
is now true of the file: the three renames above were applied, the chain-step
letter `T` is declared, and the suffix clause is restricted to the letters
that carry a coordinate, since `T1`, `T2` and `T3` are indexed by the step.
Every proof-local name introduced with a capital initial was listed
mechanically and checked against the scheme, with no name off it. The rows
header no longer says the field's failure "is not leakage": it says the
failure is no proof of leakage and names the theorem that settles what a
coalition reads, `psl211_alldecks_view_secrecy` of the same file, whose
premise is `(#|C| < 6)%N` and whose first conjunct is independence of the
chirality under the all-decks law.

The certificate theorem's docstring no longer says the obligation of
`conclude` pins the published number to `cert_eps cert`. It says the
obligation bounds that number below, which is true of the equality in
`manifest/pgg_tableau.v` and of the inequality in stage A of
`notes/probes/2026-09-19-tableau-extensions/pgg_tableau.v`. `PortProp` and
`publish` are the same in both, so the number a row publishes is
`odflt (cert_eps cert) (c R)` in both.

One word per object. *Deck description* is the whole run argument and *deal*
is its three public coordinates, said once in the header's naming paragraph
and applied in both landing copies. *Single-card marginal bound* replaces
*own marginal bound* wherever it named `psl211_marginal_bound`.

Three files, in this order, each through the machine-wide `rocq1` lock with
`rocq compile -time`, real `subprocess.returncode`, nothing piped in between:
`psl211_spectral_constancy.v`, `psl211_rows.v`, `psl211_nogo_fidelity.v`. All
three exit 0, at 24.0 s, 6.1 s and 8.1 s of wall time with the lock free. The
slowest sentence of the constancy file is a `size_filter` rewrite at 6.4 s.
`make` was never invoked and `instances/psl211/psl211_endpoints.v` was never
compiled. The rows copy is still character-identical to
`instances/psl211/psl211_rows.v` once comments and whitespace are stripped.

## Fix pass 3, what changed and what was compiled

Comments in `psl211_spectral_constancy.v` and this record only. No statement
and no proof body changed. The pre-fix-3 copy of every file touched is in
`history/` under the `2026-09-19-before-fix3` suffix; nothing was deleted.
`psl211_rows.v` needed no edit in this pass and is byte-identical to its
pre-fix-3 copy.

The four SHOULD findings of the third audit.

1. **F1, the header's obligation sentence.** The header said the obligation of
   `conclude` is `cert_eps cert = odflt (cert_eps cert) (c R)`. That is
   `RepricePayload` of `manifest/pgg_tableau.v` and not `ConcludePayload` of
   `notes/probes/2026-09-19-tableau-extensions/pgg_tableau.v`, whose obligation
   is `cert_eps cert <= odflt (cert_eps cert) (c R)`; both definitions were
   read before the edit. The header now says the obligation bounds the
   published number below by `cert_eps cert`, which is true of the equality, of
   the inequality, and of a row carrying `no_reprice`, where `c R` is `None`
   and `odflt (cert_eps cert) None` is `cert_eps cert`. That is the wording
   `psl211_alldecks_no_small_eps_cert`'s docstring already used, so the file
   now names this obligation one way.
2. **F2, `psl211_alldecks_raw_viewE`'s docstring.** It said the landing lemma
   is production's `psl211_perdeck_raw_viewE` with the deck description "fixed
   at the deal `psl211_perdeck_deal`", which under the file's own gloss is
   ill-typed: a deck description is a whole run argument and cannot be fixed at
   a deal. Both statements were opened. Production's
   `psl211_perdeck_raw_viewE (b : bool) (g : cutT)` is at
   `psl211_alldecks_seq (b, psl211_perdeck_deal)`, so its deal is pinned and
   its chirality is free; the landing's
   `psl211_alldecks_raw_viewE (x : psl211_inputT) (g : cutT)` is at
   `psl211_alldecks_seq x`, so the whole run argument is free and the
   difference between the two is the deal coordinate alone. The docstring now
   says the deal is left free instead of fixed at `psl211_perdeck_deal`, and
   its first sentence already carries that the reading is identified at every
   deck description.
3. **F3, the word *public* for the deal.** The gloss said a deal is the run
   argument's "three public coordinates". `psl211_fixed_deal_view_dep` of
   `instances/psl211/psl211_models.v` refutes independence of three seats'
   reading from the chirality under a dealer that lays one fixed deal, so a
   reader who takes *public* in its usual sense, known to the adversary, draws
   the conclusion that theorem refutes. The gloss now reads "a deal is its
   three coordinates other than the secret". Both landing copies were then
   grepped for the word: `psl211_rows.v` has none, and the eight other uses in
   the constancy file, every one of which labels a deal, a deck coordinate or
   the data outside the secret, were reworded to the same term. The header's
   "constancy of the reading in three public coordinates" becomes "in the
   other three coordinates" and its
   "constancy in public data" becomes "constancy in data outside the secret";
   `coalition_reading_constancy`'s docstring carries the same two changes at
   the framework level; `psl211_perdeck_ideal_lawE`'s and
   `psl211_alldecks_constancy_false`'s "whose other three are public" become
   "whose first coordinate is the secret chirality and whose other three are
   not"; `psl211_blockline1_deal`'s "a public coordinate of the run argument
   that carries no secret" drops the adjective its own relative clause already
   defined; and `psl211_blockline1_law_neq`'s "constancy in the public block
   line" becomes "constancy in the block line", the sentence above it already
   saying the pair carries the same secret. The word is now absent from both
   landing copies. This is wider than F3 asked, which named only the gloss line.
4. **F4, the `_CoqProject` line.** Recorded in N11 above, with the line, the
   anchor, and why the anchor is where it is.

Of the eight NOTEs, one was a comment edit and is applied. **F12**: the
`(* Argued and not compiled *)` comment under
`psl211_alldecks_no_small_eps_cert` said a weakened obligation "could only let
a row publish a number larger than `cert_eps`, never a smaller one". The
weakened obligation is `cert_eps cert <= odflt (cert_eps cert) (c R)`, which
permits equality, so *larger* was loose. It now says "no smaller than
`cert_eps`", and the trailing clause it duplicated is gone.

**F9** and **F10** are record edits and are applied, F9 in N10 above and F10
below. F9's own text was incomplete: the audit named `Hcard1` and the `H0`,
`H1` pairs, and the third `Ct`, in `psl211_perdeck_fiber_true0`, was `Hcard0`,
which no earlier pass recorded. N10 now names all four sites and all four old
names.

Five NOTEs proposed no action and none was taken.

- **F5**, the header's clause "as `psl211_perdeck_` of
  `instances/psl211/psl211_models.v` names the comparison between the two
  chiralities at one deal". Most of that family names an object and not a
  comparison. The audit proposed no replacement, the clause is an analogy
  rather than a claim about the file, and tightening it costs a header line.
- **F6**, `g0` and the `let H` / `let K` of `psl211_blockline1_seq`. The scheme
  sentence is scoped to proof scripts and to named facts, and the two `let`
  names are character for character production's own in `psl211_perdeck_seq`,
  so changing them here would split one construction across two files.
- **F7**, `psl211_alldecks_constancy_false_word584`, whose trailing digits name
  the word length. The scheme sentence is scoped to proof scripts, and three
  prior passes accepted the name.
- **F8**, the constancy file citing `psl211_alldecks_static_indep` where the
  rows file cites `psl211_alldecks_view_secrecy`. Each is the citation matching
  its own reader, and the rows header already carries the bridge between them.
- **F11**, `c` naming both a `Reprice` and a real number around
  `psl211_alldecks_no_small_eps_cert`. `manifest/pgg_tableau.v` overloads the
  letter the same way, so the landing inherits the overload rather than
  inventing it.

### Recorded, not changed: production uses "deck description" for the deal

`instances/psl211/psl211_models.v` uses *deck description* in the deal sense in
eighteen sentences. This landing does not edit that file, and it should not:
its reverse closure holds `instances/psl211/psl211_analysis.v`,
`manifest/pgg_analysis_manifest.v`, and through the manifest every rows file
and `manifest/pgg_analysis_client.v`, so a comment pass over it would put the
whole tableau layer in the compile set of a landing that is meant to compile
two files. The same file also uses the word in the run-argument sense at lines
9, 46, 192, 205, 219, 235, 311 and 356, so the split is internal to it, and
every other production file that uses the word agrees with the landing's gloss.
The list, for whoever reconciles the two senses later:

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

### Recorded, not changed: two other probes hold a copy of psl211_rows.v

`notes/probes/2026-09-19-kim-spectral-landing/psl211_rows.v` and
`notes/probes/2026-09-19-tableau-extensions/psl211_rows.v` were each taken from
production before this landing, so both carry production's header and neither
carries the rewritten "Not claimed" paragraph this landing lands. The Kim copy
differs from production in its `Require` lines alone and that landing's ledger
records it as a recompile; the extensions copy differs in a `Require` line, a
new "Key results" entry `psl211_row_alldecks_armE`, and that lemma. Nothing in
either becomes false when this landing lands, and nothing in this landing's
rows header becomes false when either of them lands.

The hazard is order, not content. Whichever of the three lands after this one
must take this landing's `instances/psl211/psl211_rows.v` header as its base
and apply its own hunk onto it. Copying its own probe copy over production
would revert this landing's header silently, because neither probe's ledger
checks that paragraph.

### Compiled after fix pass 3

Three files, in this order, each through the machine-wide `rocq1` lock with
`rocq compile -time`, real `subprocess.returncode`, nothing piped in between:
`psl211_spectral_constancy.v`, `psl211_rows.v`, `psl211_nogo_fidelity.v`. All
three exit 0, at 39.0 s, 5.6 s and 8.0 s of wall time, the first with another
probe's compile holding the lock for part of it. The slowest sentences are
unchanged from fix pass 2, two `size_filter` rewrites at 6.1 s each. The only
message is the pre-existing notation-level warning the whole tree carries.
`make` was never invoked and `instances/psl211/psl211_endpoints.v` was never
compiled. Recompiling all three is the guard against an unclosed comment, which
is the one way a comment-only pass can break a file. The rows copy is still
character-identical to `instances/psl211/psl211_rows.v` once comments and
whitespace are stripped, and in this pass it was not edited at all.

## As built, 2026-09-19

Two commits carry the landing into production. `50ea761` adds
`instances/psl211/psl211_spectral_constancy.v` and its `_CoqProject` line.
`b93aa16` rewrites the header of `instances/psl211/psl211_rows.v`. The plan
they land is
`docs/superpowers/plans/2026-09-19-psl211-spectral-constancy-landing.md`.

The main session compiled the two production files in place, each alone through
the machine-wide `rocq1` lock. The new file exits 0 at 23.3 s of wall time, its
two slowest sentences at 6.6 s and 6.3 s. The rows file exits 0 at 5.7 s.
`instances/psl211/psl211_endpoints.vo` was loaded from disk and not rebuilt: its
date is still 17 September, so the landing read that file's results and never
recompiled the file itself.

`psl211_asbuilt_fidelity.v` in this directory reports the permanent module the
way `psl211_nogo_fidelity.v` reports the landing copy. It Requires
`psl211_spectral_constancy` through the `pgg_smc` root and nothing through
`psl211_nogo_landing`, which matters because the module name now exists under
both roots. Three `Locate` sentences record which root answered: each prints
`pgg_smc.psl211_spectral_constancy` as the constant's full name, for
`psl211_alldecks_no_small_eps_cert`, `psl211_blockline1_law_neq` and
`coalition_reading_constancy`. Two `Check` sentences hold
`psl211_alldecks_no_small_eps_cert` and `psl211_blockline1_law_neq` against the
types production gives them, and the two refutations are restated and closed by
`exact:` as in the landing-copy file.

The file exits 0 at 7.5 s of wall time, again through the `rocq1` lock, with the
production `_CoqProject` flags and a `-Q` on this directory added. Its 48
`Print Assumptions` results split 28 to "Closed under the global context" and 20
to an axiom block. Every name in those blocks is one of
`propositional_extensionality`, `functional_extensionality_dep` and
`constructive_indefinite_description`, and no other constant appears. The first
two occur in all 20, the third in 19, `psl211_alldecks_static_obs_set0` resting
on the first two alone. These are the three the landing copy reports, so the
move into production changed nothing a reader would check.
