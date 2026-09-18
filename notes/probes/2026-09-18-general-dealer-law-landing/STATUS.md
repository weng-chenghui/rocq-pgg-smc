# General dealer law landing probe status

Date: 2026-09-18

Source: the seven compiled files of
`notes/probes/2026-09-17-general-dealer-law/` (commit 433af26) and the spec
`notes/20260918-general-dealer-law-landing-design.md`.

This directory holds the four candidate permanent texts and the checks on
them. No production file was edited and no production file was rebuilt. Every
compile is single-file, against the `.vo` files as they stand.

## Machine-checked

Logical path `-Q . general_dealer_law_landing`. One Rocq process at a time,
each run under a 300 s / 8000 MB self-kill wrapper. No cap was ever reached
and no checksum or inconsistent-assumption error appeared.

| File | rc | Wall | Peak RSS |
|---|---|---|---|
| `dealer_privacy.v` | 0 | 4 s | 1.50 GB |
| `design_privacy_landing.v` | 0 | 4 s | 1.51 GB |
| `pgl27_profile_privacy_landing.v` | 0 | 4 s | 1.52 GB |
| `psl211_models_landing.v` | 0 | 29 s | 1.74 GB |
| `landing_fidelity.v` | 0 | 50 s | 1.72 GB |

### With and without the additions

The production source of each edited file was compiled once into the session
scratchpad with `-o`, which reads production `.vo` files and writes nothing
into the tree.

| File | without additions | with additions | sentences | sentence-time sum |
|---|---|---|---|---|
| `design_privacy.v` | 4 s | 4 s | 169 -> 181 | 3.701 s -> 3.730 s |
| `pgl27_profile_privacy.v` | 4 s | 4 s | 118 -> 268 | 3.746 s -> 4.076 s |
| `psl211_models.v` | 4 s | 29 s | 139 -> 419 | 4.023 s -> 28.353 s |

The whole 25 s that `psl211_models.v` gains is the raw-count chain, and it is
the cost that chain already had: compiled on its own, the feasibility probe's
`psl211_per_deck_counter.v` takes 28 s with the same four slow sentences at
the same times.

### Sentences over 2 s

| Sentence | in the landing copy | in the feasibility probe |
|---|---|---|
| `rewrite -!size_filter; apply: perm_size.` (`psl211_perdeck_fiberE`) | 6.130 s | 6.099 s |
| `rewrite (nth_map 0) ?size_iota // nth_iota //.` (`psl211_perdeck_ptbl_enum`) | 6.092 s | 6.090 s |
| `apply: (@eq_from_nth _ [::]) ...` (`psl211_perdeck_ptbl_enum`) | 6.078 s | 6.084 s |
| `by split; vm_compute.` (`psl211_perdeck_raw_countE`) | 4.965 s | 4.965 s |

No other sentence of any landing file exceeds 2 s. Outside the raw-count
chain the slowest sentences of every file are `Require Import` lines at
1.2 s to 1.4 s; the slowest sentence inside a proof of new material is
`by apply/inde_RV_fdistmap.` in
`psl211_alldecks_view_indep_via_dealer`, at 0.118 s.

## Claim ledger

| ID | Verdict | Evidence |
|---|---|---|
| L1 | GO | `dealer_privacy.v` compiles in 4 s importing `transitivity_privacy` and nothing from `design_privacy` or any instance. All ten of its declarations report the three `boolp` axioms. Its four `Fail` commands still fail; the error texts were read with `rocq repl -q <flags> < dealer_privacy.v`, which echoes "The command has indeed failed with message:". |
| L2 | GO | The full copy compiles. `uniform_fdistmap_fiberE` keeps its statement: the landing constant and the production constant each typecheck at the other's kernel type (`fiberE_landing_at_production_type`, `fiberE_production_at_landing_type`). All eight existing lemmas of the file report, in the landing copy, exactly what they report in the production copy: `card_fiber_sum` and `pair_fibers_class_sizes` closed under the global context, the other six the three `boolp` axioms. No identifier is shadowed. |
| L3 | GO | The full copy compiles against the landing `dealer_privacy`. Both `_via_dealer` theorems pass the two-way ascription against `pgl27_view_indep` and `pgl27_view_indep_alldecks`, in the `ltac:(type of ...)` form and in the verbatim-transcription form. The validity mutation fails and its positive control compiles. |
| L4 | GO, with three findings | The full copy compiles. The block uses the file's own `seatT` and `cardT` and redefines neither. The elaborated statement of `psl211_alldecks_view_indep_via_dealer` carries the index `{set 'I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1}`, character-identical to the index of the production `psl211_alldecks_view_indep`; no `'I_12` is needed anywhere. The two-way ascription against `psl211_models.psl211_alldecks_view_indep` succeeds in both forms. The three findings are below. |
| L5 | GO, and the row's expectation is wrong | The block sits at the end of the file, so no existing lemma is inside a seal. Each of the three `Local Opaque` commands is paired with a `Local Transparent`: 3 and 3, verified by count. Every existing lemma of the file still compiles and reports the same assumptions. But the row claims "no sentence of the new block over 2 s except the one `vm_compute` of the raw count", and that is false: four sentences exceed 2 s, not one. See the correction below. |
| L6 | GO | None of the four recorded hang shapes reappears. The two seals that prevent them are in force in the landing copy, and the transport step that the fourth shape threatened closes in 0.118 s. |
| L7 | GO | Computed in Python from `.Makefile.rocq.d`, read-only, no `make`. Closures listed below. `psl211_endpoints`, `psl211_profile` and `psl211_exec` are in none of them. |
| L8 | GO | Whole-word Python `\b` scan of `lib protocol groups security smc reconstruct instances manifest` and of the installed `infotheo` and `mathcomp` under `_opam/lib/coq/user-contrib`: 0 of the 75 landed names occurs anywhere. Against the identifiers already in each target file: no clash in any of the three. |
| L9 | GO, one difference | 74 of the 75 landed declarations are character-identical to their feasibility-probe counterparts after whitespace normalisation. The one difference is listed below. |
| L10 | OPEN, restated | Restated per the standing rule: not "after the production tree is rebuilt", but "the landed files and their listed importers compile single-file against whatever `.vo` files exist at landing time". Nothing here can close it, because the importers are not edited by this spec and were not compiled by this probe. |
| L11 | not this probe's row | Every landed declaration carries its feasibility-probe statement comment unchanged, and each target file's header table was extended. The naming audit owns the verdict. |
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

The other 74 declarations match exactly. No binder was renamed, no notation
respelled, in any of them.

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
   current environment`. Both are already loaded transitively through
   `psl211_alldecks`, so this adds no edge to the dependency graph and does
   not change the closures of L7; it only makes the names reachable.

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
anywhere.

The spec anticipated the raw-count chain "`psl211_perdeck_raw_countE` through
`psl211_perdeck_fiber_card_neq`" as closed. That holds, and three more are
closed that it did not name: `psl211_perdeck_row_size`,
`psl211_perdeck_corow_size` and `psl211_perdeck_ptbl_nth`, plus
`psl211_deal_pos`.

## Mutations

There is a precedent for `^Fail ` in permanent files, so the mutations stay in
the candidate files beside the declarations they mutate. The precedent is in
seven files under `instances/` and two under `manifest/`:
`instances/s5/s5_models.v`, `instances/s5/s5_rows.v`,
`instances/pgl27/pgl27_rows.v`, `instances/kim2025/five_card_rows.v`,
`instances/psl211/psl211_rows.v`, `instances/psl211/psl211_group.v`,
`manifest/pgg_analysis_manifest.v`, `manifest/pgg_analysis_client.v`.

There is **no** precedent under `reconstruct/`: not one of its files contains
a `Fail`. `dealer_privacy.v` is a `reconstruct/` file, so keeping its four
mutations there makes it the first. This is a decision for the user, not for
the probe; moving them costs nothing, because `landing_fidelity.v` already
exists to hold them.

| Mutation | File | Still fails |
|---|---|---|
| `dealer_shuffleP_missing_shuffle` | `dealer_privacy.v` | yes |
| `dealer_shuffle_view_indep_without_common_law` | `dealer_privacy.v` | yes |
| `inde_RV_fdistmap_bad_reader` | `dealer_privacy.v` | yes |
| `fdistmap_prod_sectionE_without_sections` | `dealer_privacy.v` | yes |
| `pgl27_dealer_bad_viewE` | `pgl27_profile_privacy_landing.v` | yes |
| `pgl27_alldecks_dealer_view_law_without_validity` | `pgl27_profile_privacy_landing.v` | yes |
| `psl211_dealer_bad_secretE` | `psl211_models_landing.v` | yes |

The three positive controls compile beside their mutations and report the
three `boolp` axioms.

## Corrections the spec needs

1. **L5's timing expectation is wrong.** Four sentences of the new PSL(2,11)
   material exceed 2 s, not one. All four are in the raw-count chain, all four
   cost what they cost in the feasibility probe, and the recorded remedies do
   not apply to them: they are the counting, over the 660-element closure, not
   a conversion fallback. Restate the row as "no sentence of the new block
   over 2 s outside the raw-count chain, and the chain's four sentences at the
   times the feasibility probe measured".
2. **The file plan omits two imports and a scope fix.** `psl211_models.v`
   gains `psl211_blocks`, `psl211_closure` and `Import Num.Theory`, and one
   rewrite pattern gains a `%N`. See the three findings above.
3. **The artifact list should say where `Print Assumptions` goes.** No
   production `.v` file contains a `Print Assumptions` command; the six that
   mention the words mention them inside comments. The candidate
   `dealer_privacy.v` therefore carries none, and every assumption check lives
   in `landing_fidelity.v`.
4. **`fdistmap_prod_sectionE` moved.** The design note's table of new generic
   declarations puts it in `design_privacy.v`; the file plan and Decision 9
   put it in `dealer_privacy.v`. The probe followed the file plan. The two
   tables should be reconciled.
5. **L10 is restated** as the standing rule requires, from "after the
   production tree is rebuilt" to "the landed files and their listed importers
   compile single-file against whatever `.vo` files exist at landing time".

## Deviations from the spec's file plan

| Deviation | Reason |
|---|---|
| Section names in `dealer_privacy.v` are lowercase (`dealer_kernel`, `carrier_transport`, `product_sections`) where the probe used CamelCase. | Every section in `reconstruct/` is lowercase. Sections are closed before the file ends, so nothing outside sees the name. |
| The PGL(2,7) block is three new sections after `End pgl27_profile_privacy.`, not inside it. | The existing section binds `ord8_1` and `ord8_2` and opens `proba_scope` and `ring_scope` inside itself. Appending leaves every existing line untouched, which is what "everything else in the file untouched" asks for. The new sections open the two scopes the same way. |
| The PSL(2,11) block keeps the probe's `Section PSLBridge`, renamed `psl211_dealer`, inside a file that has no other section. | Discharging `Variable R : realType` out of it produces exactly the leading `(R : realType)` binder that every lemma of `psl211_models.v` already writes by hand, so the landed signatures match the file's style with no statement rewritten. |
| `dealT`, `cutT` and `viewT` are file-level `Local Notation`s in `psl211_models_landing.v`; `seatT` and `cardT` are the file's own and are not redefined. | The block spans a section and two section-free blocks, so the three notations have to outlive the section. `viewT` is spelled `{ffun seatT -> cardT}`, which is the probe's own spelling with the file's `seatT` and `cardT`. |

## Non-compiling checks

- No LAND `.v` line exceeds 80 bytes.
- No `Admitted`, `Abort`, `Axiom`, `Parameter`, `Conjecture`, `Time`,
  `Timeout` or `Show` occurs in any LAND `.v` file.
- The banned vocabulary scan reports no match.
- `Local Opaque` and `Local Transparent` are 3 and 3 in
  `psl211_models_landing.v` and 0 and 0 everywhere else.
- Every landed declaration carries its feasibility-probe statement comment.
- Each target file's header table lists the declarations added to it.
- `git status --short | grep -v '^??'` is empty; no tracked file changed.
- `ps -axo comm= | grep -E 'rocqworker$'` is empty before and after every
  compile.

## Tooling notes for the next session

- The single-file command is in `_CoqProject` here and in the wrapper
  `scratchpad/landing/c.sh`. It is the feasibility probe's command with
  `-Q . general_dealer_law_landing`.
- `rocq compile -time` is the only way the four slow sentences become
  visible; the wall clock alone attributes all 29 s to the file.
- `Definition x : ltac:(let t := type of (@y) in exact t) := @z.` is a
  two-way type ascription that no transcription error can defeat, and it
  works in a type position. Both forms are in `landing_fidelity.v`.
- A `Definition` inside a `Section` discharges only the section variables it
  uses. `psl211_dealer_view` does not mention `R`, so it takes no `R`
  argument after `End`, while `psl211_dealer_nu` does and takes one. The
  feasibility probe's use sites already assume exactly this and needed no
  change.
