# General dealer law landing probe status

Date: 2026-09-18, revised 2026-09-19 after the soundness and naming audits

Source: the seven compiled files of
`notes/probes/2026-09-17-general-dealer-law/` (commit 433af26) and the spec
`notes/20260918-general-dealer-law-landing-design.md`.

This directory holds the four candidate permanent texts and the checks on
them. No production file was edited and no production file was rebuilt. Every
compile is single-file, against the `.vo` files as they stand.

The state below is after the fix pass of 2026-09-19, which answered the two
blocking findings of `naming-audit.md` and the four SHOULD-FIX findings of
`soundness-audit.md`. Each file as it stood before that pass is kept in
`history/<name>.2026-09-19-before-fix.v`. `history/` is not in `_CoqProject`.

## Machine-checked

Logical path `-Q . general_dealer_law_landing`. One Rocq process at a time,
each run under a 300 s / 8000 MB self-kill wrapper. No limit was ever reached
and no checksum or inconsistent-assumption error against a production library
appeared.

| File | rc | Wall | Peak RSS |
|---|---|---|---|
| `dealer_privacy.v` | 0 | 4 s | 1.50 GB |
| `design_privacy_landing.v` | 0 | 4 s | 1.51 GB |
| `pgl27_profile_privacy_landing.v` | 0 | 4 s | 1.52 GB |
| `psl211_models_landing.v` | 0 | 28 s | 1.74 GB |
| `landing_fidelity.v` | 0 | 51 s | 1.72 GB |

### With and without the additions

The production source of each edited file was compiled once into the session
scratchpad with `-o`, which reads production `.vo` files and writes nothing
into the tree.

| File | without additions | with additions | sentences | sentence-time sum |
|---|---|---|---|---|
| `design_privacy.v` | 4 s | 4 s | 169 -> 181 | 3.701 s -> 3.730 s |
| `pgl27_profile_privacy.v` | 4 s | 4 s | 118 -> 268 | 3.746 s -> 4.076 s |
| `psl211_models.v` | 4 s | 28 s | 139 -> 419 | 4.023 s -> 27.996 s |

The whole 24 s that `psl211_models.v` gains is the raw-count chain, and it is
the cost that chain already had: compiled on its own, the feasibility probe's
`psl211_per_deck_counter.v` takes 28 s with the same four slow sentences at
the same times.

### Sentences over 2 s

| Sentence | landing copy | feasibility probe |
|---|---|---|
| `rewrite -!size_filter; apply: perm_size.` (`psl211_perdeck_fiberE`) | 6.077 s | 6.099 s |
| `rewrite (nth_map 0) ?size_iota // nth_iota //.` (`psl211_perdeck_ptbl_enum`) | 6.062 s | 6.090 s |
| `apply: (@eq_from_nth _ [::]) ...` (`psl211_perdeck_ptbl_enum`) | 6.029 s | 6.084 s |
| `by split; vm_compute.` (`psl211_perdeck_raw_countE`) | 4.948 s | 4.965 s |

No other sentence of any landing file exceeds 2 s. The four differ from the
probe's by up to 55 ms in both directions, which is run-to-run noise and not a
cost the landing introduces. Outside the raw-count chain the slowest sentences
of every file are `Require Import` lines at 1.2 s to 1.4 s; the slowest
sentence inside a proof of new material is `by apply/inde_RV_fdistmap.` in
`psl211_alldecks_view_indep_via_dealer`, at 0.118 s.

## Claim ledger

| ID | Verdict | Evidence |
|---|---|---|
| L1 | GO | `dealer_privacy.v` compiles in 4 s importing `transitivity_privacy` and nothing from `design_privacy` or any instance. It holds exactly three sections and the eight declarations its header table names, and no `Fail`. `Print Assumptions` on all eight reports the three `boolp` axioms. Its four mutations and their two positive controls live in `landing_fidelity.v` and behave as recorded there. |
| L2 | GO | The full copy compiles. `uniform_fdistmap_fiberE` keeps its statement: the landing constant and the production constant each typecheck at the other's kernel type. All eight existing lemmas report, in the landing copy, exactly what they report in the production copy: `card_fiber_sum` and `pair_fibers_class_sizes` closed under the global context, the other six the three `boolp` axioms. No identifier is shadowed. |
| L3 | GO | The full copy compiles against the landing `dealer_privacy`. Both `_via_dealer` theorems pass the two-way ascription against `pgl27_view_indep` and `pgl27_view_indep_alldecks`, in the `ltac:(type of ...)` form and in the verbatim-transcription form. The validity mutation fails and its positive control compiles. |
| L4 | GO | The full copy compiles. The block uses the file's own `seatT` and `cardT` and redefines neither. The elaborated statement of `psl211_alldecks_view_indep_via_dealer` carries the index `{set 'I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1}`, character-identical to the index of the production `psl211_alldecks_view_indep`; no `'I_12` is needed anywhere. The two-way ascription against `psl211_models.psl211_alldecks_view_indep` succeeds in both forms: the `ltac:` form at `landing_fidelity.v` section 1, and the verbatim-transcription form, added on 2026-09-19 as section 1c, transcribed from `instances/psl211/psl211_models.v:427-430` with the file's `Local Notation seatT` written out. The three import and scope findings are below. |
| L5 | GO, and the row's expectation is wrong | The block sits at the end of the file, so no existing lemma is inside a seal. Each of the three `Local Opaque` commands is paired with a `Local Transparent`: 3 and 3, verified by count. Every existing lemma of the file still compiles and reports the same assumptions. But the row claims "no sentence of the new block over 2 s except the one `vm_compute` of the raw count", and that is false: four sentences exceed 2 s, not one. See the correction below. |
| L6 | GO | None of the four recorded hang shapes reappears. The two seals that prevent them are in force in the landing copy, and the transport step that the fourth shape threatened closes in 0.118 s. |
| L7 | GO | Computed in Python from `.Makefile.rocq.d`, read-only, no `make`. Closures listed below. `psl211_endpoints`, `psl211_profile` and `psl211_exec` are in none of them. |
| L8 | GO | Whole-word Python `\b` scan of `lib protocol groups security smc reconstruct instances manifest` and of the installed `infotheo` and `mathcomp` under `_opam/lib/coq/user-contrib`. What it counts is stated below. |
| L9 | GO, one difference | 74 of the 75 declarations landed before the fix pass were character-identical to their feasibility-probe counterparts after whitespace normalisation. The one difference is listed below. The fix pass changed comments, two identifiers and one file placement, never a statement. |
| L10 | OPEN, restated | Restated per the standing rule: not "after the production tree is rebuilt", but "the landed files and their listed importers compile single-file against whatever `.vo` files exist at landing time". Nothing here can close it, because the importers are not edited by this spec and were not compiled by this probe. |
| L11 | naming audit's row | Every landed declaration carries a statement comment. Header-table coverage is stated below. |
| L12 | GO | `reconstruct/transitivity_privacy.v` is at `_CoqProject` line 171; the first importer, `instances/pgl27/pgl27_profile_privacy.v`, is at line 180 and `instances/psl211/psl211_models.v` at line 212. `reconstruct/dealer_privacy.v` goes at line 172, after `transitivity_privacy.v` and before both importers, with eight files in between that neither import it nor are imported by it. |

## L7: what a real landing would have to recompile

Reverse-dependency closures from `.Makefile.rocq.d`, in dependency order. The
implementation plan compiles exactly these lists, single-file, and nothing
else.

`reconstruct/design_privacy.v`, 11 files:

```
instances/psl211/psl211_secrecy.vo
instances/psl211/psl211_models.vo
instances/psl211/psl211_analysis.vo
manifest/pgg_analysis_manifest.vo
manifest/pgg_tableau.vo
manifest/pgg_tableau_syntax.vo
instances/pgl27/pgl27_rows.vo
instances/kim2025/five_card_rows.vo
instances/s5/s5_rows.vo
instances/psl211/psl211_rows.vo
manifest/pgg_analysis_client.vo
```

`instances/pgl27/pgl27_profile_privacy.v`, 0 files. Nothing imports it.

`instances/psl211/psl211_models.v`, 9 files:

```
instances/psl211/psl211_analysis.vo
manifest/pgg_analysis_manifest.vo
manifest/pgg_tableau.vo
manifest/pgg_tableau_syntax.vo
instances/pgl27/pgl27_rows.vo
instances/kim2025/five_card_rows.vo
instances/s5/s5_rows.vo
instances/psl211/psl211_rows.vo
manifest/pgg_analysis_client.vo
```

The union of the three closures together with the three edited files is 13
files, in this order:

```
reconstruct/design_privacy.v
instances/pgl27/pgl27_profile_privacy.v
instances/psl211/psl211_secrecy.v
instances/psl211/psl211_models.v
instances/psl211/psl211_analysis.v
manifest/pgg_analysis_manifest.v
manifest/pgg_tableau.v
manifest/pgg_tableau_syntax.v
instances/pgl27/pgl27_rows.v
instances/kim2025/five_card_rows.v
instances/s5/s5_rows.v
instances/psl211/psl211_rows.v
manifest/pgg_analysis_client.v
```

Plus the new `reconstruct/dealer_privacy.v` itself, which invalidates nothing.
`instances/psl211/psl211_endpoints.v`, `psl211_profile.v` and `psl211_exec.v`
are in none of the three closures, so the 900 s rebuild is not owed.

## L8: what the scan counted

81 landed identifiers of the four candidate permanent texts: every
`Definition`, `Lemma`, `Theorem` and `Corollary` the landing adds, together
with the `Local Notation`s it adds and the names of its three `Fail`
commands. The count excludes the identifiers each target file already had.

One name occurs in the tree: `viewT`, at `protocol/pgg_functionality.v`,
`security/pgg_leakage_witness.v`, `security/pgg_trace_secrecy.v` and
`reconstruct/transitivity_privacy.v`. Every occurrence is a bound variable or
a `Local Notation`, and a `Local Notation` is not exported, so nothing
collides and the reuse is consistent across the development. No other name
occurs anywhere, in the tree or in the installed `infotheo` and `mathcomp`.

Against the identifiers already in each target file: no clash in any of the
three.

## L9: the one statement difference

`uniform_fdistmap_pointE`. The probe states it with all its binders written
out; the landing copy is inside `Section fibers` of `design_privacy.v`, whose
variables supply five of them.

```coq
(* psl211_per_deck_law_counter.v *)
Lemma uniform_fdistmap_pointE (R : realType) (X T : finType)
    (A : {set X}) (HA : (0 < #|A|)%N) (f : X -> T) (v : T) : ...

(* design_privacy_landing.v, inside Section fibers *)
Lemma uniform_fdistmap_pointE (f : X -> T) (v : T) : ...
```

The body is character-identical. The discharged type differs from the probe's
in the order of the explicit binders alone, because the section declares
`R X A HA` before `T` while the probe writes `R X T A HA`:

```
forall (R : realType) (X : finType) (A : {set X}) (HA : 0 < #|A|)
       (T : finType) (f : X -> T) (v : T), ...
```

The same three binders `X`, `A` and `T` are implicit on both sides, by the
same rule of the shared `Unset Strict Implicit` regime. The only use site,
`psl211_perdeck_massE`, applies it by `rewrite` and supplies no argument, so
the reordering is not visible there.

The other 74 declarations match exactly. No binder was renamed and no notation
respelled in any of them. The fix pass of 2026-09-19 renamed one landed
identifier, `psl211_entry_perm_enum` to `psl211_perdeck_entry_perm_enum`, and
changed no statement.

## Three findings on `psl211_models.v` (ledger row L4)

Each is a real property of the target file that the feasibility probe could
not see, because the probe file had its own imports and its own scope
settings.

1. **The file must import `psl211_blocks` and `psl211_closure`.** The
   raw-count chain names `psl211_elem_table`, `psl211_entry_perm`,
   `psl211_ptbl`, `psl211_ptbl_entry`, `psl211_size_keys`,
   `psl211_mem_entry_perm`, `psl211_entry_perm_mem` and
   `psl211_entry_perm_inj`. `psl211_models.v` imports none of them; the first
   compile stopped at `The reference psl211_elem_table was not found in the
   current environment`. Neither import adds an edge to the dependency graph,
   because both are already loaded transitively: `psl211_blocks` through
   `psl211_alldecks`, and `psl211_closure` through `psl211_exec`, which is a
   direct prerequisite of `psl211_models.vo`. `psl211_closure` is not a
   prerequisite of `psl211_alldecks` or of `psl211_endpoints`, both measured
   from `.Makefile.rocq.d`. The L7 closures are unchanged either way.

2. **The file must `Import Num.Theory`.** It imports `GRing.Theory` alone.
   The second compile stopped at `The variable pnatr_eq0 was not found in the
   current environment`, inside `psl211_perdeck_law_neq`. Adding it changed
   nothing above the block: every existing lemma still compiles and reports
   the same assumptions.

3. **One rewrite pattern needs a `%N`.** `psl211_models.v` opens
   `ring_scope` at file level and the probe's counter file opened no scope at
   all, so `rewrite -[X in _ < X]Hrow` parses its pattern as the ring order
   and reports `partial term (_ < _) does not match any subterm of the goal`.
   The two occurrences in `psl211_perdeck_seqE` are now written
   `-[X in (_ < X)%N]Hrow` and `-[X in (_ < X)%N]Hcorow`. The statement is
   untouched; this is a proof-script spelling change and is the only one in
   the whole landing.

## The two `design_privacy` modules

`psl211_models_landing.v` has to require both the landing copy of
`design_privacy` and the production one, because
`uniform_fdistmap_fiberTE` exists only in the copy while everything else the
file takes from that layer must come from the production module. In the real
landing there is one file and the question does not arise, so the probe had to
choose an order.

They clash on all ten names of `design_privacy.v`. The clash is resolved by
import order and not by an error: the landing copy is required first and the
production module second, so the production constants win every short name
they share, and only `uniform_fdistmap_pointE` and `uniform_fdistmap_fiberTE`
are reached in the copy. The one consequence is that the copy's
`uniform_fdistmap_fiberTE` is proved through the copy's
`uniform_fdistmap_fiberE` rather than the production one. Those two constants
have the same statement and the same assumptions, both checked in
`landing_fidelity.v`, so nothing downstream can tell them apart.

`landing_fidelity.v` reaches the production constants by qualification
(`design_privacy.uniform_fdistmap_fiberE`,
`psl211_models.psl211_alldecks_view_indep`) and imports only the landing ones.

## Assumptions

`landing_fidelity.v` runs 97 `Print Assumptions` commands and the output was
paired with them positionally in Python.

- 67 declarations report exactly `propositional_extensionality`,
  `functional_extensionality_dep` and `constructive_indefinite_description`,
  and nothing else.
- 30 report `Closed under the global context`: `psl211_deal_pos`, the whole
  raw-count chain from `psl211_perdeck_deal` to
  `psl211_perdeck_fiber_card_neq`, and the two existing `design_privacy.v`
  lemmas `card_fiber_sum` and `pair_fibers_class_sizes`, in both the
  production and the landing copy.

No project-local constant, no `Admitted` and no axiom outside the trio appears
anywhere. The tally is 67 and 30 both before and after the fix pass, so no
edit of that pass moved an assumption.

The spec anticipated the raw-count chain "`psl211_perdeck_raw_countE` through
`psl211_perdeck_fiber_card_neq`" as closed. That holds, and four more are
closed that it did not name: `psl211_perdeck_row_size`,
`psl211_perdeck_corow_size`, `psl211_perdeck_ptbl_nth` and `psl211_deal_pos`.

## Mutations

The four generic mutations and their two positive controls live in
`landing_fidelity.v`. They were moved there on 2026-09-19, which executes the
decision the spec records and which the naming audit's S9 and the soundness
audit's S4 both asked for. `reconstruct/dealer_privacy.v` then holds exactly
the three sections and the eight declarations its header table names, and no
`Fail`.

The mutations of the two instance copies stay beside the declarations they
mutate. The precedent for `^Fail ` in a permanent file is six files under
`instances/` and two under `manifest/`:
`instances/kim2025/five_card_rows.v`, `instances/pgl27/pgl27_rows.v`,
`instances/psl211/psl211_group.v`, `instances/psl211/psl211_rows.v`,
`instances/s5/s5_models.v`, `instances/s5/s5_rows.v`,
`manifest/pgg_analysis_client.v`, `manifest/pgg_analysis_manifest.v`.

There is **no** precedent under `reconstruct/`: not one of its files contains
a `Fail`. That is now moot for `dealer_privacy.v`, which has none.

| Mutation | File | First line of the error |
|---|---|---|
| `dealer_shuffleP_missing_shuffle` | `landing_fidelity.v` | `The term "secretP `X delta" has type` |
| `dealer_shuffle_view_indep_without_common_law` | `landing_fidelity.v` | `The term "dealer_shuffle_view_indep (mu:=fdist1 x)" has type` |
| `inde_RV_fdistmap_bad_reader` | `landing_fidelity.v` | `The term "proj1 (inde_RV_fdistmap P f X Y)" has type` |
| `fdistmap_prod_sectionE_without_sections` | `landing_fidelity.v` | `The term "fdistmap_prod_sectionE (h:=h)" has type` |
| `pgl27_dealer_bad_viewE` | `pgl27_profile_privacy_landing.v` | `The term "erefl" has type` |
| `pgl27_alldecks_dealer_view_law_without_validity` | `pgl27_profile_privacy_landing.v` | `The term "pgl27_alldecks_dealer_view_law R s Hdt HC" has type` |
| `psl211_dealer_bad_secretE` | `psl211_models_landing.v` | `The term "erefl" has type` |

All seven still fail, each with the error the feasibility probe recorded.
`rocq compile` prints nothing for a `Fail`, so the texts were re-read on
2026-09-19 with `rocq repl -q <flags> < <file>.v`.

## Header tables

The repository's tables are selective, so the tables here are too. After the
fix pass they name:

| File | landed declarations named |
|---|---|
| `dealer_privacy.v` | 8 of 8 |
| `design_privacy_landing.v` | 2 of 2 |
| `pgl27_profile_privacy_landing.v` | 19 of 21 |
| `psl211_models_landing.v` | 25 of 42 |

The seventeen absent from `psl211_models.v` are the raw-count chain, which
`instances/psl211/psl211_alldecks.v` keeps 76 of its own 103 declarations out
of its table for the same reason. `psl211_models.v` itself already runs at 22
per cent absent before the landing.

## Corrections the spec needs

1. **L5's timing expectation is wrong.** Four sentences of the new PSL(2,11)
   material exceed 2 s, not one. All four are in the raw-count chain, all four
   cost what they cost in the feasibility probe, and the recorded remedies do
   not apply to them: they are the counting, over the 660-element closure, not
   a conversion fallback. Restate the row as "no sentence of the new block
   over 2 s outside the raw-count chain, and the chain's four sentences at the
   times the feasibility probe measured, to within run-to-run noise".
2. **The file plan omits two imports and a scope fix.** `psl211_models.v`
   gains `psl211_blocks`, `psl211_closure` and `Import Num.Theory`, and one
   rewrite pattern gains a `%N`.
3. **The artifact list should say where `Print Assumptions` goes.** No
   production `.v` file contains a `Print Assumptions` command; the six that
   mention the words mention them inside comments. The candidate
   `dealer_privacy.v` therefore carries none, and every assumption check lives
   in `landing_fidelity.v`.
4. **`fdistmap_prod_sectionE` moved.** The design note's table of new generic
   declarations puts it in `design_privacy.v`; the file plan and Decision 9
   put it in `dealer_privacy.v`. The probe followed the file plan. The two
   tables should be reconciled.
5. **L10 is restated** as the standing rule requires.
6. **L1's counts are the post-move counts and are now right.** Eight
   declarations, and the mutations in the probe's `landing_fidelity.v`.
7. **Three `Require` lines name the probe logical path.** The acceptance
   condition says the plan quotes the landing copies verbatim. Quoted
   verbatim, two permanent files would import a probe file. The three
   substitutions the plan must make are: in
   `pgl27_profile_privacy_landing.v`, `From general_dealer_law_landing Require
   Import dealer_privacy.` becomes `From pgg_reconstruct Require Import
   dealer_privacy.`; in `psl211_models_landing.v`, the same line becomes the
   same replacement, and `From general_dealer_law_landing Require Import
   design_privacy_landing.` is deleted, because in the real landing
   `uniform_fdistmap_pointE` and `uniform_fdistmap_fiberTE` are in the
   production `design_privacy` that the file already imports.

## Deviations from the spec's file plan

| Deviation | Reason |
|---|---|
| Section names in `dealer_privacy.v` are lowercase (`dealer_kernel`, `carrier_transport`, `product_sections`) where the probe used CamelCase. | Fourteen of the sixteen files in `reconstruct/` use lowercase section names; the two exceptions are both in `reconstruct/s5_nogo.v`. Sections are closed before the file ends, so nothing outside sees the name. |
| The PGL(2,7) block is three new sections after `End pgl27_profile_privacy.`, not inside it. | The existing section binds `ord8_1` and `ord8_2` and opens `proba_scope` and `ring_scope` inside itself. Appending leaves every existing line untouched. The new sections open the two scopes the same way. |
| The PSL(2,11) block keeps the probe's `Section PSLBridge`, renamed `psl211_dealer`, inside a file that has no other section. | Discharging `Variable R : realType` out of it produces exactly the leading `(R : realType)` binder that every lemma of `psl211_models.v` already writes by hand, so the landed signatures match the file's style with no statement rewritten. |
| `dealT`, `cutT` and `viewT` are file-level `Local Notation`s in `psl211_models_landing.v`; `seatT` and `cardT` are the file's own and are not redefined. | The block spans a section and two section-free blocks, so the three notations have to outlive the section. `viewT` is spelled `{ffun seatT -> cardT}`, which is the probe's own spelling with the file's `seatT` and `cardT`. |

## The fix pass of 2026-09-19

Comments, names and file placement only. No statement and no proof changed,
which the unchanged 67 and 30 assumption tally and the unchanged compile table
both witness. Every mechanical substitution was applied by a Python pass that
asserts its own occurrence count, so a silent miss was impossible; one
assertion did fire, on the comment-style conversion, and caught two comments
whose name is followed by an argument.

| Item | What changed |
|---|---|
| naming B1, soundness S1 | `psl211_dealer_view_indep_of_deck_unsat`: "the uniform deal law is the law that meets it" became "the uniform deal law meets it". The definite article asserted a uniqueness nothing proves. |
| naming B2, soundness N5 | `psl211_perdeck_fiber_card_neq`: "per-deal symmetry" became "per-cut symmetry", which is the direction `psl211_alldecks_per_cut_count` actually has, and "not available once a representative deck is fixed" became "at the deck description `psl211_perdeck_deal` it fails", which is what is proved. |
| naming S3, S4, S5 | The PSL(2,11) block now follows its target file's vocabulary: "class" to "chirality", "shuffle" to "cut" for a group element while "shuffle group" stays for the group, "deal description" to "deck description". Counts are below. |
| naming S1 | The 21 landed statement comments of `pgl27_profile_privacy_landing.v` use `==`, which is what all 16 of that file's own comments use. The other two target files use the em-dash form and are unchanged. |
| naming S2 | `fdistmap_prod_sectionE` no longer carries the PSL words "cut" and "deals" into the generic file. |
| naming S6 | The argument-order rationale left `pgl27_alldecks_dealer_view_law`'s statement comment and became a `(* *)` comment above the `Fail` it explains. |
| naming S9, soundness S4 | The four mutations and two positive controls moved to `landing_fidelity.v`. |
| naming S10 | `psl211_entry_perm_enum` became `psl211_perdeck_entry_perm_enum`, at its declaration, its use site, its comment and in `landing_fidelity.v`. The new name collides with nothing. |
| naming S7, S8 | Eight header entries added, five to `pgl27_profile_privacy` and three to `psl211_models`, and the "The dealer route." paragraph added to the `psl211_models` header prose. |
| naming N1 | `dealer_privacy.v` now opens `fdist_scope`, `proba_scope`, `ring_scope`, with `ring_scope` innermost as its three siblings do. The file compiles unchanged. |
| soundness S3 | The verbatim-transcription ascription for PSL(2,11) was missing; it is now `landing_fidelity.v` section 1c, in both directions. |

A second comment pass followed on 2026-09-19, answering naming audit round 2.
Each file it touched is kept in `history/<name>.2026-09-19-before-fix2.v`, and
both are code-identical to those copies after comments are stripped, checked
in Python with a nesting-aware stripper. It rewrote the
`psl211_perdeck_fiber_card_neq` comment once more, because the first rewrite
left "it" with "the per-cut symmetry" as its grammatical antecedent, which
would say that the symmetry the file's headline result rests on fails at
`psl211_perdeck_deal`; the comment now says that the symmetry holds only in
its per-cut form and that the statement with the roles exchanged is what
`psl211_perdeck_deal` refutes. It deleted the rationale comment moved in the
first pass, which duplicated the mutation comment directly beneath it word for
word. It padded the seven header lines of `psl211_models_landing.v` that
closed one column early, six of them introduced by the first pass, and
rewrapped the `psl211_perdeck_raw_countE` entry so that no line opens with a
bare numeral; every line of that header block is now exactly 80 bytes, and the
four short header lines of the pgl27 copy are left alone because they are
byte-identical to `instances/pgl27/pgl27_profile_privacy.v` and are that
file's own. It brought three statement comments into line with the header
glosses that had been normalised without them, at `psl211_perdeck_deal`,
`psl211_perdeck_raw_countE` and `psl211_dealer_view_indep_of_deck_unsat`.
And it replaced the "The dealer route." paragraph, which had called the route
a condition rather than a route through one and had attributed "restate an
existing result" to the two refutations, which restate nothing.

Vocabulary after the first pass, measured in Python over the landed block and
over its target file:

| | class | chirality | shuffle (element) | shuffle group | cut | deal description | deck description |
|---|---|---|---|---|---|---|---|
| PSL block | 0 | 41 | 0 | 5 | 21 | 0 | 9 |
| `psl211_models.v` | 1 | 14 | 0 | 1 | 20 | 0 | 7 |

The scan's one apparent "shuffle" in the block is "PSL(2,11) shuffle group"
wrapped across two lines. The two "class" uses left in the PGL(2,7) block are
a secret's class of decks, which is that instance's own concept and not a
chirality.

## Non-compiling checks

- No LAND `.v` line exceeds 80 bytes.
- No `Admitted`, `Abort`, `Axiom`, `Parameter`, `Conjecture`, `Time`,
  `Timeout`, `Show` or `Print Assumptions` occurs in any of the four candidate
  permanent texts. `landing_fidelity.v` carries the 97 `Print Assumptions`
  commands, which is where the spec puts them.
- The banned vocabulary scan reports no match in any LAND file or in this one.
- `Local Opaque` and `Local Transparent` are 3 and 3 in
  `psl211_models_landing.v` and 0 and 0 everywhere else.
- Every landed declaration carries a statement comment.
- `git status --short | grep -v '^??'` is empty; no tracked file changed.
- `ps -axo comm= | grep -E 'rocqworker$'` is empty before and after every
  compile.

## Tooling notes for the next session

- The single-file command is in `_CoqProject` here and in the wrapper
  `scratchpad/landing/c.sh`. It is the feasibility probe's command with
  `-Q . general_dealer_law_landing`.
- `rocq compile -time` is the only way the four slow sentences become
  visible; the wall clock alone attributes all 28 s to the file.
- `Definition x : ltac:(let t := type of (@y) in exact t) := @z.` is a
  two-way type ascription that no transcription error can defeat, and it
  works in a type position. Both forms are in `landing_fidelity.v`.
- A `Definition` inside a `Section` discharges only the section variables it
  uses. `psl211_dealer_view` does not mention `R`, so it takes no `R`
  argument after `End`, while `psl211_dealer_nu` does and takes one.
- Editing a LAND file that others require makes their `.vo` files report
  "makes inconsistent assumptions over library general_dealer_law_landing.…".
  That names only LAND libraries, never a production one, and a recompile in
  `_CoqProject` order clears it. A production library in that message would
  be the stop-and-report case instead.
