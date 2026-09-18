# Landing the general dealer law in the permanent tree

Date: 2026-09-18

Status: landing probe verified by the main session's own compile. Soundness
audit GO on 2026-09-19. Naming audit GO in round 3 on 2026-09-19, after two
rounds that each stopped on a comment sentence in the PSL block. Both audits
state that the landing copies, with the three import substitutions recorded
below, are fit to be written into the permanent files verbatim. Plan:
`docs/superpowers/plans/2026-09-19-general-dealer-law-landing.md`.

Sources: [[20260917-general-dealer-law-feasibility-design]] (C1 to C10, all
GO), [[20260918-general-dealer-law-probe-result]], and the compiled probe
`notes/probes/2026-09-17-general-dealer-law/` (commit 433af26).

## Problem

The feasibility probe showed that one dealer model recovers the three existing
privacy theorems and that privacy is a condition on the dealer law, not a
consequence of the protocol. Its files are probe files. They live outside the
library, they were compiled against one snapshot of the library, and their
declarations sit in files named after the verification work. The permanent
tree still has no dealer model, so the paper cannot cite one.

Landing is not a copy. Four things change when a declaration moves into a
permanent file, and the feasibility probe tested none of them: the file's own
section context and local notations, its opacity settings, the import graph
around it, and the set of compiled files that the edit invalidates. The last
one is expensive here. `instances/psl211/psl211_endpoints.v` costs about 900 s
and 17 GB to rebuild, and any edit below it in the import graph owes that
rebuild.

## Decisions of 2026-09-18 (user)

1. The paper's Section 2 presents only the mixed-law condition: every secret of
   positive mass has the same law of the coalition view under `delta s` times
   `nu`. It covers all three instances, because the per-deck condition implies
   it.
2. PGL(2,7) all decks goes through the per-deck condition inside Rocq, so that
   `dealer_shuffle_view_indep_of_deck` is used by an instance and is not an
   unused declaration. The paper says only that PGL(2,7) meets the general
   condition.
3. PSL(2,11) goes through the mixed-law condition. The fixed-deal refutation
   stays in the formalization and out of Section 2. The PSL instance section
   may say in one sentence that the dealer law affects privacy.
4. The feasibility design note was revised to the compiled probe (commit
   28f5fee).
5. Probe files keep their names. Permanent declarations go into semantic files.
6. No proof that `uniq` is necessary for the per-deck law to be true. The text
   says the per-deck theorem assumes valid decks.
7. No `Arguments` directives for now.
8. No study of whether the uniform PSL dealer law is necessary. The text says
   the uniform law meets the condition and one point mass does not.
9. The generic dealer block goes into a new file, `reconstruct/dealer_privacy.v`.

Defaults taken by the main session, to be overturned by the user if wrong:

- The refutation lemmas become permanent declarations. Decision 3 keeps them in
  the formalization, and `uniform_fdistmap_pointE` has no other use.
- The three `_via_dealer` theorems coexist with the theorems they restate,
  under the repository's `_via_` convention
  (`pgl27_view_indep_via_profile`, `instances/pgl27/pgl27_profile_privacy.v`).
  No existing proof is replaced.
- No Tableau row, manifest entry or facade is added. The dealer law is a
  library result, not a new instance.

## Flow

The running value is the number of existing compiled files an edit invalidates,
and whether `psl211_endpoints` is among them.

```
flow land_general_dealer_law                                   // invalidated: 0, endpoints: no
new    reconstruct/dealer_privacy.v      imports transitivity_privacy      // 0, no
         dealer_shuffleP, dealer_shuffle_secret, dealer_shuffle_view,
         dealer_shufflePE
         dealer_shuffle_view_indep           by inde_prod_kernel_fst   [interface]
         dealer_shuffle_view_indep_of_deck   by fdistmap_prod_const    [interface]
         inde_RV_fdistmap, fdistmap_prod_sectionE
edit   reconstruct/design_privacy.v      + uniform_fdistmap_pointE,
         uniform_fdistmap_fiberTE; uniform_fdistmap_fiberE through pointE  // 11, no
edit   instances/pgl27/pgl27_profile_privacy.v   imports dealer_privacy     // 11, no
         pgl27 dealer data; per-deck law     by ktuple_encode_uniform  [interface]
         pgl27_view_indep_via_dealer             mixed-law, then transport
         pgl27_view_indep_alldecks_via_dealer    per-deck
edit   instances/psl211/psl211_models.v  imports dealer_privacy             // 11 and 9, no
         psl211 dealer data; mixed law by psl211_alldecks_per_cut_count [interface]
         psl211_alldecks_view_indep_via_dealer   mixed-law, then transport
         boundary: psl211_perdeck_*, psl211_dealer_view_indep_of_deck_unsat,
                   psl211_fixed_deal_view_dep
edit   _CoqProject                       + reconstruct/dealer_privacy.v
terminal  three _via_dealer theorems typed as the theorems they restate;
          Print Assumptions = the three boolp axioms                        // endpoints untouched
outside   Section 2 prose, Arguments directives, necessity of uniq,
          necessity of the uniform law, Tableau and manifest rows
```

Roles. Object: `dealer_shuffleP`. Step justifications: the two independence
lemmas, the per-deck law, the mixed-law equality. Observation change:
`inde_RV_fdistmap` with the law equation and the two reader equations of each
instance. Invocation of an assumption: none, every step is exact and
information-theoretic. Boundary results outside the flow: the three PSL
refutation statements.

Structure. The bridge flow is a parameterised monad indexed by sample carrier
and reader pair. Its bind is `inde_RV_fdistmap` with the two reader equations,
and its laws hold propositionally through `fdistmap_comp`. The landing flow
itself accumulates a set of invalidated files under union.

## Pinned carrier

```coq
Variables (R : realType) (secretT deckT shuffleT viewT : finType).
Variable secretP : R.-fdist secretT.
Variable delta : secretT -> R.-fdist deckT.
Variable nu : R.-fdist shuffleT.
```

Instances: `secretT := bool`. PGL(2,7): `deckT := 8.-tuple 'I_8`,
`shuffleT := pgg_gT pgl27_M`, view `{ffun 'I_8 -> 'I_8}`. PSL(2,11):
`deckT := psl211_deal`, `shuffleT := pgg_gT psl211_M`, view
`{ffun 'I_12 -> 'I_12}`. The real field stays abstract. `Rdefinitions.R` was
exercised by the feasibility probe and is not landed.

## File plan, with the reason for each choice

| Declarations | Home | Reason |
|---|---|---|
| `dealer_shuffleP`, `dealer_shuffle_secret`, `dealer_shuffle_view`, `dealer_shufflePE`, `dealer_shuffle_view_indep`, `dealer_shuffle_view_indep_of_deck`, `inde_RV_fdistmap` | new `reconstruct/dealer_privacy.v`, importing `transitivity_privacy` only | Decision 9. A new file invalidates nothing. It needs `inde_prod_kernel_fst` and `fdistmap_prod_const` and nothing from `design_privacy`. |
| `fdistmap_prod_sectionE` | `reconstruct/dealer_privacy.v` | It is the lemma that turns a section-wise equality into the mixed-law premise, so it belongs with the condition it discharges. Its siblings `fdistmap_prod_const` and `fdistmap_prod_snd_const` sit in `transitivity_privacy.v`, and editing that file invalidates 41 files including `psl211_endpoints`. |
| `uniform_fdistmap_pointE`, `uniform_fdistmap_fiberTE`, and `uniform_fdistmap_fiberE` re-proved through the point lemma | `reconstruct/design_privacy.v`, Section `fibers` and a new section after it | They are statements about fibers of a uniform law, which is that file's first section. The edit invalidates 11 files and not `psl211_endpoints`. The statement of `uniform_fdistmap_fiberE` must not change. |
| PGL(2,7) dealer data, reader equations, per-deck law, `pgl27_view_indep_via_dealer`, `pgl27_view_indep_alldecks_via_dealer`, their mutations | `instances/pgl27/pgl27_profile_privacy.v` | That file already holds the other alternative route to `pgl27_view_indep` and the refutations showing its premises cannot be relaxed. Nothing imports it. The declarations and their order are the landing copy verbatim, the three sections after `End pgl27_profile_privacy.` in `pgl27_profile_privacy_landing.v`. |
| PSL(2,11) dealer data, reader equations, mixed law, `psl211_alldecks_view_indep_via_dealer`, the per-deck count, the two refutations | `instances/psl211/psl211_models.v` | It is the home of the all-decks law and of `psl211_alldecks_view_indep`. Nine files import it, all rows, manifest and Tableau files, none of them heavy. The declarations and their order are the landing copy verbatim: everything the copy adds after the last line of the production file, which is the banner comment, three `Local Notation`s, Section `psl211_dealer`, the raw-count chain and the two refutations, together with the `Local Opaque` and `Local Transparent` commands that bracket them and are landed in place. The file also gains imports of `psl211_blocks` and `psl211_closure`, an `Import Num.Theory`, and a `%N` annotation on the two rewrite patterns of `psl211_perdeck_seqE`. |

Dependency facts, computed from `.Makefile.rocq.d` on 2026-09-18:
`design_privacy` imports `transitivity_privacy` and no instance file;
`psl211_scheme`, `psl211_profile`, `psl211_exec` and `psl211_endpoints` do not
import `design_privacy`; `psl211_models` imports `psl211_endpoints`,
`psl211_closure`, `psl211_alldecks` and `design_privacy`;
`pgl27_profile_privacy` imports `pgl27_secrecy`, `pgl27_orbit` and
`transitivity_privacy`, and has no importer.

State of the tree on 2026-09-18: 85 of 193 files are already out of date in the
main checkout, because commit 1654fde edited `protocol/card_exchange_pismc.v`
and `protocol/pgg_run.v`. `transitivity_privacy`, `psl211_profile`,
`psl211_exec` and `psl211_endpoints` are among them. A full rebuild is owed
whatever this spec does. The feasibility probe was compiled against the `.vo`
files from before that commit.

## Claim ledger

| ID | Checkable claim | Passing evidence |
|---|---|---|
| L1 | `reconstruct/dealer_privacy.v` compiles as written, importing `transitivity_privacy` and nothing from `design_privacy` or any instance. | The candidate file compiles single-file with the repository header regime. `Print Assumptions` on all eight declarations reports the three `boolp` axioms. Its four mutations and their two positive controls live in the probe's `landing_fidelity.v` and behave as recorded there. |
| L2 | The two fiber lemmas fit inside `design_privacy.v`, and `uniform_fdistmap_fiberE` can be re-proved through `uniform_fdistmap_pointE` with its statement unchanged. | A full copy of `design_privacy.v` with the additions compiles. A `Check (uniform_fdistmap_fiberE : T)` with `T` the old statement copied verbatim succeeds. Every other lemma of the file reports the same assumptions as before. No identifier of the file is shadowed. |
| L3 | The PGL(2,7) block fits inside `pgl27_profile_privacy.v` after adding an import of `dealer_privacy`, with no cycle. | A full copy of that file with the additions compiles against the landing copy of `dealer_privacy`. Both `_via_dealer` theorems pass a two-way type ascription against `pgl27_view_indep` and `pgl27_view_indep_alldecks`. The validity mutation and its positive control behave as recorded. |
| L4 | The PSL(2,11) block fits inside `psl211_models.v`. That file has no sections, binds `R` per lemma, and defines `seatT` and `cardT` as local notations with definitions different from the probe's. | A full copy of that file with the additions compiles. The additions use no local notation that the file already defines with another meaning, which is shown by compiling and by printing the elaborated statement of `psl211_alldecks_view_indep_via_dealer`. The two-way type ascription against `psl211_alldecks_view_indep` succeeds. |
| L5 | Sealing `psl211_alldecks_view`, `psl211_elem_table` and `psl211_perdeck_raw_count` around the new block does not break any existing lemma of `psl211_models.v`, and each seal is released before the block ends. | The full copy compiles with the block placed at the end of the file, each `Local Opaque` paired with a `Local Transparent`. No sentence of the new block costs more under `rocq compile -time` than the same sentence costs in the feasibility probe, up to measurement noise of a tenth of a second, and the file's total time is reported next to its time without the block. |
| L6 | None of the four recorded hang shapes reappears in the permanent context. | `rocq compile -time` on each landing copy. Any sentence of the new material that costs more than its feasibility-probe counterpart, beyond measurement noise of a tenth of a second, is a finding. |
| L7 | The edit set does not invalidate `psl211_endpoints`. | The reverse-dependency computation above, repeated by the prover from `.Makefile.rocq.d` after adding `reconstruct/dealer_privacy.v` to a copy of `_CoqProject` and regenerating the dependency file in the probe directory. No `make` in the production tree. |
| L8 | The new names collide with nothing, inside each target file and across the tree. | A whole-word search of the tree and of installed infotheo and mathcomp for every landed name, plus the compile of each full copy. |
| L9 | The landed statements are the probe's statements. | After applying the identity renaming, each landed declaration is character-identical to its probe counterpart apart from binders that the target file's context supplies. Differences are listed one by one. |
| L10 | The landing holds against the compiled files that exist at landing time. | The landed files and the importers listed under L7 compile one at a time against whatever `.vo` files exist then. No full rebuild is run or waited for (user rule of 2026-09-18). The row is closed by the implementation, not by the probe. |
| L11 | Header tables and statement comments meet the project rule in each target file. | The naming audit: the named interface of each block appears in its file's header table, every new declaration has a statement comment giving the fact and its place in the privacy argument, each block uses its target file's vocabulary and comment form, and no comment claims more than a named lemma proves. |
| L12 | The position of `reconstruct/dealer_privacy.v` in `_CoqProject` is after `reconstruct/transitivity_privacy.v` and before the first file that imports it. | The regenerated dependency file orders it correctly and reports no cycle. |

## Cited objects

| Object | File | Required statement shape |
|---|---|---|
| `inde_prod_kernel_fst` | `reconstruct/transitivity_privacy.v:167` | A constant conditional pushforward under a kernel product implies independence from the first coordinate. |
| `fdistmap_prod_const` | `reconstruct/transitivity_privacy.v:216` | Constant section pushforwards on the support imply a constant pushforward of a kernel product. |
| `ktuple_encode_uniform` | `reconstruct/transitivity_privacy.v:591` | A t-transitive group pushes the uniform shuffle to the uniform law on the k-tuples a coalition reads, at one repetition-free deck. |
| `alldecksP`, `alldecks_secret`, `alldecks_view` | `reconstruct/transitivity_privacy.v:771` | The all-decks law and its two readers, to which the PGL(2,7) all-decks dealer law is definitionally equal. |
| `uniform_fdistmap_fiberE` | `reconstruct/design_privacy.v:51` | Equal fiber cardinalities on a set give equal pushforwards of the uniform law on it. |
| `pgl27_view_indep`, `pgl27_view_indep_alldecks` | `instances/pgl27/pgl27_secrecy.v:82`, `:215` | The two PGL(2,7) theorems restated. |
| `orbit_encode_deck` | `instances/pgl27/pgl27_orbit.v` | The deterministic deck has no repeated card. |
| `psl211_alldecksP`, `psl211_alldecks_secret`, `psl211_alldecks_view_indep` | `instances/psl211/psl211_models.v:138`, `:145`, `:427` | The PSL(2,11) all-decks law, its secret reader, and the theorem restated. |
| `psl211_alldecks_view`, `psl211_alldecks_per_cut_count`, `psl211_alldecks_seq` | `instances/psl211/psl211_alldecks.v:678`, `:1334` | The reading, the per-cut count, and the laid deck. |
| `psl211_ptbl_entry`, `psl211_mem_entry_perm`, `psl211_entry_perm_mem`, `psl211_entry_perm_inj`, `psl211_size_keys`, `psl211_elem_table` | `instances/psl211/psl211_closure.v` | The tabulated enumeration of the 660 shuffles that carries the raw count to the group. |

Line numbers are those of the stale snapshot and are rechecked by the probe.

## Soundness invariants

1. No landed file gains an axiom, an assumed constant, `Admitted` or `Abort`.
   Every new declaration ends in `Qed` or is a definition. No permanent file of
   the repository contains a `Print Assumptions` command, so the landed files
   contain none and every assumption check lives in the probe's
   `landing_fidelity.v`.
2. Every equality of laws is information-theoretic and exact. No computational
   premise appears.
3. The model is average-case over `secretP`, then conditional over `delta s`,
   then over the independent law `nu`. The quantifier order is fixed in
   `dealer_shuffleP`.
4. No landed statement or comment claims privacy for an arbitrary dealer law,
   claims that the uniform PSL(2,11) dealer law is necessary, or claims that a
   hidden uniform deal leaks. The refutation is at one deal with a point-mass
   dealer, a coalition of three seats and the production shuffle law and view.
5. The per-deck condition is stated as a sufficient condition that assumes
   valid decks. Nothing says `uniq` is necessary.
6. No existing statement changes. `uniform_fdistmap_fiberE` keeps its statement
   when its proof changes. The three restated theorems keep their proofs.
7. Carrier transport proves a law equation and both reader equations, by named
   lemmas, for each of the three instances.
8. Each of the mixed-law condition, the per-deck condition and the transport
   equivalence is used by at least one landed instance theorem.
9. No permanent file imports a probe file.
10. The guard `secretP s != 0` is never exercised non-trivially, since every
    instance has the uniform prior on a bit, and only the PGL(2,7) dealer laws
    depend on the secret. The landed comments do not suggest otherwise.

## Probe artifacts

New directory `notes/probes/2026-09-18-general-dealer-law-landing/`, logical
path `general_dealer_law_landing`, compiled one file at a time:

1. `dealer_privacy.v`, the candidate permanent file, verbatim.
2. `design_privacy_landing.v`, a full copy of `reconstruct/design_privacy.v`
   with the additions.
3. `pgl27_profile_privacy_landing.v`, a full copy with the additions.
4. `psl211_models_landing.v`, a full copy with the additions.
5. `landing_fidelity.v`, the two-way type ascriptions of L2 to L4 and the
   mutations that are not already inside the copies.
6. `_CoqProject`, `STATUS.md`, and the two audit reports.

There is no decomposition probe with admitted statements. Every supporting
lemma already ends in `Qed` in the feasibility probe, and the full copies are
stronger evidence than a composition of admitted statements.

## Landing probe results, 2026-09-18

All five landing files compile one at a time. The main session recompiled them
in order into a scratch directory: `dealer_privacy.v` 3.7 s,
`design_privacy_landing.v` 3.9 s, `pgl27_profile_privacy_landing.v` 4.3 s,
`psl211_models_landing.v` 28.6 s, `landing_fidelity.v` 49.2 s, each under
1.9 GB. `landing_fidelity.v` reports the three `boolp` axioms in 67 blocks and
`Closed under the global context` in 30.

Findings that the feasibility probe could not see, all caused by the context
of `psl211_models.v`:

- It must gain imports of `psl211_blocks` and `psl211_closure`, because
  `psl211_elem_table` is not in scope there.
- It must gain `Import Num.Theory`, because `pnatr_eq0` is not in scope.
- One rewrite pattern needs `%N`, because the file opens `ring_scope` at file
  level and the probe file opened no scope.
- L4 is settled in the good direction. The block uses the file's own `seatT`
  and `cardT`, redefines neither, and the elaborated statement of
  `psl211_alldecks_view_indep_via_dealer` is character-identical to that of
  `psl211_alldecks_view_indep`.

Corrections to this note made after the probe:

- L5 and L6 expected one sentence over 2 s. Four sentences of the PSL block
  exceed it, and each costs what it costs in the feasibility probe, so landing
  adds no cost. The rows now compare against the feasibility probe.
- Invariant 1 no longer asks for `Print Assumptions` inside permanent files.
- The feasibility probe's `STATUS.md` had proposed `design_privacy.v` for
  `fdistmap_prod_sectionE`. This note's file plan supersedes it:
  `reconstruct/dealer_privacy.v`.
- L9: 74 of the 75 landed statements are character-identical to the probe's
  after whitespace normalisation. `uniform_fdistmap_pointE` differs only in
  that Section `fibers` supplies its five binders.
- L8: none of the 75 landed names occurs in the tree, in installed infotheo or
  mathcomp, or among the identifiers already in a target file.

Decision on mutations, taken by the main session: no file under `reconstruct/`,
`lib/`, `protocol/`, `security/`, `smc/` or `groups/` contains a `Fail`
command, while six files under `instances/` and two under `manifest/` do.
`reconstruct/dealer_privacy.v` therefore carries no mutation, and its four
mutations with their positive controls move to the probe's
`landing_fidelity.v`. The mutations in the two instance files stay.

What a landing recompiles (L7), and nothing else: the 11 importers of
`design_privacy.v`, the 9 importers of `psl211_models.v`, none for
`pgl27_profile_privacy.v`. Their union with the edited files is 13 files,
listed in dependency order in the landing probe's `STATUS.md`.
`psl211_endpoints`, `psl211_profile` and `psl211_exec` are in none of them.

## Audit results, 2026-09-19

Soundness audit (`soundness-audit.md` in the landing probe): GO, no blocking
finding. It compared the elaborated types of all 31 existing declarations of
`psl211_models.v` between the production module and the landing copy and found
them identical, so the new imports change nothing already in the file. It
showed that the fidelity test discriminates: a coalition bound of 4 and
exchanged readers are rejected. It measured that `Local Opaque` does not
survive a file boundary, so the closing releases are hygiene and the release
before the raw count is the one the file needs. It recomputed the closures of
L7 member for member.

Naming audit (`naming-audit.md`): NO-GO on two comment sentences, with
thirteen further findings, all about comments, vocabulary, one name and this
note. Both blocking sentences were in the PSL block: one wrote that the
uniform deal law is the law that meets the mixed-law condition, which asserts
the necessity that decision 8 excludes, and one called the symmetry of the
counting argument per-deal where it is per-cut.

Folded into this note:

- The plan does not quote three lines of the landing copies verbatim. The two
  `From general_dealer_law_landing Require Import dealer_privacy.` lines become
  `From pgg_reconstruct Require Import dealer_privacy.`, and the line importing
  `design_privacy_landing` is deleted, because after the landing the two fiber
  lemmas come from `design_privacy` itself. Without this a permanent file would
  import a probe file, against invariant 9.
- The mutation move takes the two positive-control definitions and the three
  mutation sections with the four `Fail` commands. The resulting
  `dealer_privacy.v` and `landing_fidelity.v` are compiled before the plan
  quotes them.
- Vocabulary follows the target file, not the probe: in `psl211_models.v` the
  bit is the chirality, a group element is a cut, and an element of
  `psl211_deal` is a deck description. In `dealer_privacy.v` a group element is
  a shuffle. In `pgl27_profile_privacy.v` statement comments are written
  `name == ...`.
- `psl211_entry_perm_enum` lands as `psl211_perdeck_entry_perm_enum`, so that
  the `psl211_entry_perm_*` family stays in `psl211_closure.v`.
- Header tables list the reader equations of each instance and
  `psl211_dealer_valid_forced`, and the header of `psl211_models.v` gains a
  paragraph on the dealer route. Tables list a selection, as the repository's
  own tables do, so L11 asks for the named interface and not for every lemma.
- L5 and L6 compare with a tolerance of a tenth of a second.

Residual risk, stated by the soundness audit and accepted: nothing has been
compiled against the `.vo` files that commit 1654fde will produce. The landed
blocks name nothing that commit changed (`exchange_verifier`,
`endpoints_of_trace`, `evens`), and neither do the 13 files a landing
recompiles. `psl211_models.v` sits above the two edited protocol files, so its
existing execution lemmas are rechecked at some later recompile whether or not
this landing happens.

## Acceptance condition

L1 to L9, L11 and L12 are GO. L10 is closed by the implementation. An
independent soundness audit and an independent naming audit, both able to
compile, end in `VERDICT: GO`. Findings are folded into this note before a plan
is written. The plan then quotes the landing copies verbatim, one commit per
target file, in the order of the flow above.

## Out of scope

The text of the paper's Section 2. `Arguments` directives. Necessity of `uniq`.
Necessity of the uniform PSL(2,11) dealer law. Renaming probe files. Tableau
rows, manifest entries and facades. The rebuild of the production tree, which
is owed for an unrelated reason and is scheduled by the user.
