# Naming and style audit of stage A, second round

**NO-GO.**

Two blocking findings, both mechanical. One is a suffix that means two
different statements in the two T0 files, so a stage-B author or a paper
citing `<row>_rowE` gets a different kind of fact depending on which file it
was copied from. The other is the only recorded failure in the tree whose name
ends in `E`, sitting twenty-five lines above a proved `_armE` in the same
file, which spends the suffix stage A's ten new equations depend on.

Everything else is sound. The `SecurityArm` rename, the `<row>_armE` scheme,
the four general lemmas, `_raw` to `_bind`, `_bare` to `_unindexed`, the index
edits and the removal of the `ab_arm` index line are all correct against the
tree's own precedents, and I say below which precedent decides each. Zero
collisions across 249 files. Zero banned vocabulary. Zero new lines over 80
bytes.

Read-only. Nothing was compiled, nothing outside this file was written, no git
command was run that changes state.

Scope: the ten files of `notes/probes/2026-09-19-tableau-extensions/` at
commit `83045c5`, diffed against `history/*.0-baseline`,
`history/*.3-before-fix1` and `history/*.4-before-split`; `STATUS.md`;
`naming-audit-stageA.md`; the production tree; the Kim landing probe at
`notes/probes/2026-09-19-kim-spectral-landing/`; the PSL landing probe at
`notes/probes/2026-09-19-psl211-nogo-landing/`.

---

## Findings table

| ID | Class | Quoted content | Rule or precedent | Fix |
|---|---|---|---|---|
| N1 | **BLOCKING** | `t0_sampled_branch.v`: `Lemma t0_row_uniform_rowE : published_row t0_row_uniform = published_row five_card_row_uniform_tableau.` and `Lemma t0_row_uniform_manifestE : published_row t0_row_uniform = five_card_row_uniform.` against `t0_sampled_branch_pgl27.v`: `Lemma pgl27_row_exact_branch_rowE : published_row pgl27_row_exact_branch = pgl27_row_exact.` | Production `_rowE` is always `published_row <program> = <manifest constant>`: `pgl27_row_exact_rowE`, `pgl27_row_word_rowE`, `five_card_row_uniform_rowE`, `s5_row_rand_rowE`, `psl211_row_alldecks_rowE`. The PGL(2,7) T0 file follows it. `t0_sampled_branch.v` gives that statement the name `_manifestE` and gives `_rowE` to a program-to-program equation. | Rename table below. `t0_row_uniform_manifestE` becomes the `_rowE`; the program-to-program lemma is renamed or dropped as derivable. |
| N2 | **BLOCKING** | `pgl27_rows.v`: `Fail Definition pgl27_row_word_arm_exactE (R : realType) (idx : ...) := (erefl : security_arm_of pgl27_row_word_tableau R idx = ExactIndependenceArm).` | No `Fail` in the tree ends in `E`. The twelve recorded failures of the four rows files are `pgl27_row_exact_leak7`, `pgl27_inline_neq`, `pgl27_inline_reuse`, `pgl27_row_word39_unindexed`, `pgl27_row_word39_unindexed_bind`, `pgl27_row_word41`, `pgl27_word_arm_is_not_exact`, `five_card_row_s5_family`, `five_card_row_biased_at_manifest_level`, `five_card_F_or`, `s5_dealt_rand`, `s5_F_k5`, `psl211_alldecks_prefix_vm_neq`, `psl211_row_vm_reuse`. `E` in this tree marks a proved rewrite equation. | `pgl27_row_word_arm_exactE` becomes `pgl27_row_word_arm_neq`, after `pgl27_inline_neq`, which is the same shape: `Fail Definition <name> : <equation> := erefl`. Zero collisions. |
| N3 | SHOULD | `Lemma pgl27_row_word39E : pgl27_row_word39 = pgl27_row_word39_bind.` with `Proof. by []. Qed.` and no statement comment | The file's own precedent for a surface-against-bind equation is `pgl27_row_word_certE`, whose name carries the coordinate word and whose bind spelling is written inline rather than named. Every other `Lemma` of `pgl27_rows.v` carries a `(** *)`. | Name it `pgl27_row_word39_bindE`, zero collisions, and give it the comment below, moved off the `_bind` definition. |
| N4 | SHOULD | `Lemma pgl27_row_exact_branch_ideal_atE : published_at pgl27_row_exact_branch = published_at pgl27_row_exact_branch_ideal.` and `Lemma pgl27_row_word_branch39_atE : published_at pgl27_row_word_branch = published_at pgl27_row_word_branch39.` | Every `E` name in the tree names the subject on the **left**: `pgl27_row_exact_rowE`, `s5_F_thresholdE`, `five_card_row_biased_levelE`, and the sibling `pgl27_row_exact_branch_atE` in the same file. These two name the right-hand argument. | Swap the two sides so the named subject is on the left. `exact: erefl` closes a convertible equation in either orientation, but the author must compile it; I compiled nothing. |
| N5 | SHOULD | `pgg_tableau.v`: "Together with the previous lemma this is what makes the arm a property of the program's text" and "This is the step that carries the two lemmas above out to a published row" | The first round's S5 ruled that a comment names the declaration it means, and the fix pass applied it to the three pointers it was given. These two were written in the same pass. | Replacement text below, checked against the code and wrapped under 80. |
| N6 | SHOULD | `security_arm_of`: "The manifest row of a published row records the path and not the arm, so two rows over one model and one pair of statuses are one manifest row" against `SecurityArm`: "A published row's manifest row records the path the row ran and no theorem, so two rows over one model and one pair of statuses are one manifest row" | "A tutorial pinned to one declaration restates results it does not track and drifts against them." `STATUS.md` D5 records this as the goal: "The two comments now agree." Agreeing by restatement is the hazard. | Keep the reason on `SecurityArm`. Replacement for `security_arm_of` below. |
| N7 | SHOULD | Kim landing probe, `five_card_rows.v`: `Fail Definition five_card_row_repeated39_bare`, with "five_card_pow2_39_split is quantified over every real field but not over the family index, so it does not have the shape conclude asks for" | Identical defect to the one stage A renamed `pgl27_row_word39_bare` to `pgl27_row_word39_unindexed` for. All three probes land. | The Kim probe's `_bare` becomes `_unindexed`, or the two owners agree one word before either lands. |
| N8 | SHOULD | `t0_sampled_branch_pgl27.v` index: `pgl27_row_exact_branch  == the exact branch point published` and `pgl27_row_word_branch   == the word branch point published` | The bodies say "The first continuation, published at the status the unbranched exact program publishes" and "The first continuation of the word branch point". What is published is a continuation, not the branch point. | Two replacement lines below, each measured to exactly 80. |
| N9 | SHOULD | `t0_sampled_branch_pgl27.v:122`: `(*     The word model as a branch point, under a spectral payload            *)` at 79 columns | Every other section divider in the ten files is exactly 80. | One space before `*)`. |
| N10 | SHOULD | `g2_keyword_measure.v`: `(*   conclude_stays_bindable == a binder named conclude, in a file that       *)` then `(*                             requires the surface                           *)` | Production `pgg_tableau.v` puts the continuation at the gloss column, which is the `==` column plus three. Here `==` is at 30, the gloss at 33, the continuation at 32. | One space. |
| N11 | SHOULD | `t0_sampled_branch.v` header: Definitions align `==` at column 32, Key results at column 28 | Production `pgg_tableau.v` uses column 29 for both blocks; `t0_sampled_branch_pgl27.v` uses 30 for both. | One column for both blocks. |
| N12 | SHOULD | `t0_sampled_branch_pgl27.v`: "on the concluded row below that search does not return" | `STATUS.md` measures "did not return in 130 s" and "did not return in 200 s". Non-termination is not what was observed. | Replacement below. |
| N13 | SHOULD | `assumptions_report.v`: "declared as an Axiom at instances/s5/rigidity_s5_instance.v:179" | The statement-comment rule bars line numbers. The number is correct today, verified: `Axiom s5_group_order_eq` is at line 179. It will drift. | Cite the file and the name, drop `:179`. |
| N14 | SHOULD | `t0_sampled_branch.v`: `(** The manifest row is also the one the manifest writes for this path. *)` | The production sibling carries a position: "Conversion decides it, so the descriptive row and the theorem proved about it cannot drift apart." This one states the fact and stops. | Add the position sentence, or reuse production's. |
| N15 | SHOULD | `psl211_rows.v`: eleven docstrings open `(** <identifier> — <text>`, the new `psl211_row_alldecks_armE` does not | The file-local convention restates the identifier, which the statement-comment rule bars, and the other three rows files do not use it. | The new comment is the correct form. Record the file-local convention for the owner rather than propagate it. |
| N16 | SHOULD | `RepricePayload`, `port_reprice` | The first round's S7 ruled `reprice` is kept "only for the chosen number itself, never for the operation". These two name the operation `conclude` now owns. `Reprice`, `no_reprice` and `pgl27_reprice39` name the number and are correct. | Cost measured below. One production file, seven occurrences. |
| N17 | NOTE | `SecurityArm := ExactIndependenceArm \| SpectralDecayArm` | Correct, and better than the first round's `ExactArm` / `SpectralArm`. Reasoning below. | None. |
| N18 | NOTE | `<row>_armE`, `certify_exact_armE`, `certify_spectral_armE`, `conclude_armE`, `publish_armE` | Correct against the tree's actual `E` rule, which is not MathComp's head-first order. Derivation below. | None. |
| N19 | NOTE | 48 new identifiers, whole-word `\b` scan over 249 `.v` files | Zero hits outside the probe. | None. |
| N20 | NOTE | Banned vocabulary and line width | Zero hits for all four banned items and for narrative or metaphor words. Three lines over 80, all three byte-identical to production. | None. |
| N21 | NOTE | Kim landing probe, `five_card_row_repeated39` supplies `(fun R _ => five_card_pow2_39_split R)`, an equality, where stage A's `RepricePayload` now asks `<=` | Outside my remit, and `STATUS.md` D10 already records it for `kim_spectral_rows_probe.v`. It applies to the Kim **landing** probe too, which the D10 entry does not name. | Relayed to the owner. |

---

## 1. Every identifier new or renamed since the baseline

Forty-eight identifiers were added. None was removed except
`pgl27_row_word39_bare`, replaced by `pgl27_row_word39_unindexed`.

### The tree's actual `E` rule, derived from production

The specific question is whether `<row>_armE` is right when the left side's
head is `security_arm_of` and not the row. It is, and here is why.

MathComp's published rule builds a name from the head symbol of the left side
outward, as in `size_cat : size (cat s1 s2) = size s1 + size s2`. The four
rows files do not follow it and have not followed it since before stage A.
Their rule is **subject first, coordinate last, coordinate spelled in the
domain's word rather than in the reader's identifier**:

| lemma | left side | reader | coordinate word |
|---|---|---|---|
| `pgl27_row_exact_rowE` | `published_row pgl27_row_exact_tableau` | `published_row` | `row` |
| `five_card_row_biased_levelE` | `apr_completion five_card_row_biased` | `apr_completion` | `level` |
| `five_card_row_repeated_modelE` | `sp_f (tableau_at five_card_row_repeated_tableau)` | `sp_f` | `model` |
| `s5_F_thresholdE` | `fn_threshold s5_F` | `fn_threshold` | `threshold` |
| `pgl27_inline_paramsE` | `projT1 (projT2 (tableau_at pgl27_inline_dealt))` | `projT1` | `params` |
| `s5_dealt_row_observedE` | `ob_obs (tableau_at s5_dealt)` | `ob_obs` | `observed` |

In every one the subject is the named row or program with `_tableau` dropped,
and the reader's identifier never appears in the name. `security_arm_of`
reads the arm, the domain word is `arm`, so `pgl27_row_exact_armE`,
`pgl27_row_word_armE`, `pgl27_row_word39_armE`, `five_card_row_uniform_armE`,
`s5_row_rand_armE` and `psl211_row_alldecks_armE` are exactly right, and
`_armE` reads beside `_rowE` as the second coordinate read off one finished
row. This is N18.

The same rule decides the four general lemmas. `certify_exact_armE`,
`certify_spectral_armE` and `conclude_armE` read `ab_arm` off a statement's
result; `publish_armE` reads `security_arm_of` off a published row. Both
readers return `SecurityArm` and `security_arm_of` is literally
`ab_arm (published_at r) R idx`, so one coordinate word covers both, and the
subject is the statement in all four. `ab_arm_conclude` and
`security_arm_of_publish` would be MathComp's order, and they would be the
only two names in the file family built that way; they would also drop the
`E`, which is what tells a reader the statement is a rewrite equation. **Keep
the present scheme.** It is consistent with ten existing names and needs no
rename table.

### Where the scheme is broken

Two places. Both are N1 and N2 above, plus the orientation nit N4.

**N4 in full.** Five `_atE` lemmas were added. Three name the left side, two
name the right:

| lemma | statement | subject named |
|---|---|---|
| `t0_row_uniform_atE` | a three-way conjunction with `t0_row_uniform` on the left of two conjuncts | left |
| `pgl27_row_exact_branch_atE` | `published_at pgl27_row_exact_branch = published_at pgl27_row_exact_tableau` | left |
| `pgl27_row_word_branch_atE` | `published_at pgl27_row_word_branch = published_at pgl27_row_word_tableau` | left |
| `pgl27_row_exact_branch_ideal_atE` | `published_at pgl27_row_exact_branch = published_at pgl27_row_exact_branch_ideal` | **right** |
| `pgl27_row_word_branch39_atE` | `published_at pgl27_row_word_branch = published_at pgl27_row_word_branch39` | **right** |

The fix is to swap the two sides of the last two, not to rename them, because
the name is the one a reader will look for. Both sides are convertible, so
`exact: erefl` should still close each, but I compiled nothing and the author
must check.

### The rename table

| old | new | rule or precedent | collision |
|---|---|---|---|
| `pgl27_row_word_arm_exactE` | `pgl27_row_word_arm_neq` | `pgl27_inline_neq` and `psl211_alldecks_prefix_vm_neq` are the tree's two `Fail Definition ... := erefl` at a stated equation, both named `_neq`, neither named `E`. | 0 |
| `pgl27_row_word39E` | `pgl27_row_word39_bindE` | `pgl27_row_word_certE` is the file's precedent for a surface-against-bind equation and carries the coordinate word. `_bind` is already this file's word for the alternative spelling. | 0 |
| `t0_row_uniform_manifestE` | `five_card_row_uniform_branch_rowE` | The statement is `published_row X = <manifest constant>`, which is what `_rowE` means in production and in `t0_sampled_branch_pgl27.v`. | 0 |
| `t0_row_uniform_rowE` | drop, or `five_card_row_uniform_branch_unbranched_rowE` | Derivable from the line above and the production `five_card_row_uniform_rowE` by transitivity. `t0_sampled_branch_pgl27.v` does without it. | 0 |
| `t0_row_uniform` | `five_card_row_uniform_branch` | Matches `pgl27_row_exact_branch`, `pgl27_row_word_branch`. | 0 |
| `t0_row_uniform_transfer` | `five_card_row_uniform_branch_ideal` | Matches `pgl27_row_exact_branch_ideal`, and the status it publishes is `IdealFinite`. | 0 |
| `t0_row_uniform_atE` | `five_card_row_uniform_branch_atE` | Same. | 0 |
| `t0_row_uniform_row_neq` | `five_card_row_uniform_branch_transfer_neq` | `_neq` is the tree's suffix for a recorded difference, and the difference is the transfer, which the name should say. | 0 |
| `t0_s5_sampled` | `s5_rand_sampled` | The family is `s5_rand_family`; `five_card_uniform_sampled` and `pgl27_exact_sampled` both name instance, model, level. `t0_s5_sampled` names no model. | 0 |
| `t0_cross_instance` | `s5_cross_instance` | Matches `pgl27_cross_model`, whose prefix is the branch point's. | 0 |
| `t0_cross_instance_back` | `five_card_cross_instance_back` | Matches `pgl27_cross_model_back`. | 0 |
| `five_card_uniform_sampled` | keep | Already instance, model, level. | n/a |

Every proposed name was scanned with Python `re` and `\b` over 249 `.v` files:
production, the Kim landing probe, the PSL landing probe. All zero.

**On the `t0_` prefix.** The first round ruled that probe-only files keep
their ledger prefixes, and `STATUS.md` D12 declines the landing table on that
ground. The reason is sound in the abstract and is contradicted by the file
the same fix pass wrote: `t0_sampled_branch_pgl27.v` carries no `t0_` on any
of its twelve declarations. One of the two files has to move. Moving
`t0_sampled_branch.v` is the cheaper end state, because the PGL(2,7) file is
already in the landing shape and the rename then happens once instead of
twice. If the owner prefers the prefix, the twelve PGL(2,7) names take it
instead; either way the two files must agree before stage B writes a third.

### The remaining new names

`pgl27_reprice41` beside `pgl27_reprice39`, `pgl27_row_word41` beside
`pgl27_row_word39`, `pgl27_word_reprice41_false`, `pgl27_row_word39_bind`,
`pgl27_row_word39_unindexed`, `pgl27_row_word39_unindexed_bind`,
`conclude_stays_bindable`, `pgl27_exact_sampled`, `pgl27_word_sampled`,
`pgl27_row_word_branch39`: all correct.

`_bind` is right and I confirmed the word is the tree's own, not a new one:
`pgg_tableau_syntax.v:6` says "A program of pgg_tableau.v is a sequence of
binds over anonymous tuples", `pgg_tableau.v:403` heads a section "The carrier
and its dependent bind", and the operator is `tableau_bind`.

`_unindexed` is right and better than the first round's proposed
`_bare_bind`. The payload `(fun R => ssr_ext.eqW (pow2_split R))` now carries
the relation the obligation asks for and lacks only the index binder, so
"bare" would name a defect the term no longer has.

**N17, the constructor scheme.** `ExactIndependenceArm` and `SpectralDecayArm`
are the surface literal plus `Arm`, and that is better than the first round's
`ExactArm` and `SpectralArm`. The surface writes
`certify ExactIndependence w` and `certify SpectralDecay c`, so the arm tag
and the token a reader types are one word, and no third word is introduced.
The carrier qualifier `Arm` is last and spelled out. The planned
`IdealProximityArm`, `LeakageCeilingArm` and `DependenceArm` follow
mechanically, provided each is also the surface literal of its own certify
rule. Endorsed.

---

## 2. Collisions

Method: Python `re` with `\b`, over every `.v` file reachable from the repo
root with `.git`, `_build` and `.claude` pruned, minus the extensions probe
itself, minus `notes/` except the two landing probes. **249 files scanned**,
of which 29 are the Kim landing probe and 13 the PSL landing probe. The
scanner was control-tested first: `view_indist_of` returns 3 files,
`SecurityPort` 2, `pgl27_reprice39` 2, `publish` 21, which are the right
answers.

**Result: zero hits for all 48 new identifiers.** Not one of `SecurityArm`,
`ExactIndependenceArm`, `SpectralDecayArm`, `port_arm`, `ab_arm`,
`security_arm_of`, the four general `_armE`, the six per-row `_armE`,
`pgl27_reprice41`, `pgl27_row_word39E`, `pgl27_row_word39_bind`,
`pgl27_word_reprice41_false`, `pgl27_row_word_arm_exactE`,
`pgl27_row_word39_unindexed`, `pgl27_row_word39_unindexed_bind`,
`pgl27_row_word41`, the eight `t0_*`, `five_card_uniform_sampled`, the twelve
PGL(2,7) branch names, or `conclude_stays_bindable` appears anywhere outside
the probe. The twelve proposed replacement names above are likewise all zero.

**Two things the scan turned up that are not collisions.**

The baselines are the production files with the import stanza rewritten to
`From tableau_ext_probe Require Import`, and nothing else.
`history/pgg_tableau.v.0-baseline` is byte-identical to
`manifest/pgg_tableau.v`; the other five differ only in that stanza. So the
baseline is a faithful landing source.

The Kim landing probe carries its own copies of `pgg_tableau.v`,
`pgg_tableau_syntax.v`, `five_card_rows.v`, `pgl27_rows.v` and `s5_rows.v`.
Its `pgg_tableau.v` adds no declaration, only the import stanza. Its
`five_card_rows.v` adds twenty-five, none of which collides. But two of them
matter to stage A:

- `five_card_row_repeated39_bare`, the same recorded failure stage A renamed
  to `_unindexed`. This is N7.
- `five_card_row_repeated39` supplies `(fun R _ => five_card_pow2_39_split R)`,
  an equality, to a `RepricePayload` stage A has weakened to `<=`. It needs
  `ssr_ext.eqW` or the `ltW` route `STATUS.md` D10 already describes for
  `kim_spectral_rows_probe.v`. D10 names that probe and not the Kim **landing**
  probe. This is N21, outside naming, relayed.

---

## 3. One word per concept

**`arm` against `claim`.** Closed. `SecurityClaim`, `ExactViewIndependence`,
`SpectralViewDecay`, `port_claim`, `stack_claim` and `security_claim_of` are
gone. `pgl27_rows.v`'s "The two arms are different claims" is now "The two
arms are different statements", and `pgg_tableau.v`'s "different claims about
a coalition" is "different statements about a coalition". The word `claim`
survives only in the security-claim sense: "a claim about interpreter
messages", "the manifest's claim", "one security claim". `t0_sampled_branch.v`
uses it four times and `t0_sampled_branch_pgl27.v` none, which is drift but
not a violation, since the PGL(2,7) file says "the two finished rows" where
the five-card file says "one security claim".

**`conclude` and `publish`.** Closed. `republish` and its inflections appear
zero times in all ten `.v` files. In `STATUS.md` the five hits all name the
retired word as retired, which is the correct use. "reprice terminal" appears
nowhere; `assumptions_report.v` says "the conclude terminal". The section
heading, the index line and the body of `pgl27_rows.v` all say "concluded at".

**`Reprice` and `RepricePayload`, N16.** The first round's S7 ruled `reprice`
may name the chosen number and never the operation. Under that ruling:

| carrier | names | verdict |
|---|---|---|
| `Reprice` | the type of the chosen number | correct |
| `no_reprice` | the absence of one | correct |
| `pgl27_reprice39`, `pgl27_reprice41` | chosen numbers | correct |
| `RepricePayload` | the obligation `conclude` takes | names the operation |
| `port_reprice` | the lemma that performs the move | names the operation |

So yes, this is an inconsistency the landing must face, and it is confined.
**The cost, measured:** `RepricePayload` occurs 3 times in production, all in
`manifest/pgg_tableau.v`. `port_reprice` occurs 4 times, all in the same file.
No instance file, no manifest file, no `security/`, `smc/`, `protocol/`,
`lib/`, `groups/` or `reconstruct/` file mentions either. The Kim landing
probe's copy of `pgg_tableau.v` holds the same 7. So renaming to
`ConcludePayload` and `port_conclude` is seven occurrences in one production
file, seven in one Kim probe file, and the extensions probe's own copy. It
does not have to happen now, and it is cheapest to do while these three
probes are open rather than after they land.

**`branch point`, `continuation`, `coordinate`.** Consistent across both T0
files. `branch point` 8 times in the five-card file and 19 in the PGL(2,7)
file, always for a named `Tableau Sampled` value. `continuation` always for
what runs from one. `coordinate` always for `published_at`, which is what
makes the `done` note's phrase "Every coordinate equation of this file" true:
it covers exactly the four `_atE` lemmas, and the file's `_rowE` and `_armE`
close by `by []`, which the note does not claim otherwise.

**`index binder` and `unindexed`.** Consistent. `pgl27_rows.v:444` says "A
payload with the right relation but no index binder is rejected" and the two
recorded failures are `_unindexed` and `_unindexed_bind`. No third word.

---

## 4. Statement comments the fix pass wrote

Thirty-seven comments were written or rewritten. Thirty-three carry a fact and
a position and are clean of meta, status, effort, dates, line numbers and
proof strategy. The four exceptions are N5, N6, N13 and N14.

**Clean, named so the owner can see the pass worked.** `SecurityArm`
states what it omits and why: "with the witness and the certificate
forgotten". `ab_arm` states the true reason B4 asked for, that the two certify
statements each write one constructor, with the honest qualifier "for a row
written in the surface". `RepricePayload` and `port_reprice` both price the
step and name the condition a future arm owes, that its proposition be
monotone in its number, which is exactly the "price every step of a hybrid
argument" requirement. `certify_exact_armE` says what a reader may conclude:
"a reader needs no argument about the instance's probability model to know
which statement the row proved". `pgl27_word_reprice41_false` separates
"publishing an upper bound of the distance a row proved from publishing a
number the certificate does not prove".

**N5, the two positional pointers.** `pgg_tableau.v:805` and `:828`.
Replacements, checked against the code and wrapped under 80:

```
(* The same for the spectral statement. With certify_exact_armE this is what
   makes the arm a property of the program's text: the two statements are the
   only ones that build a port, and each writes one constructor at every
   field and index. *)
```

```
(* Publishing attaches the manifest row and leaves the arm alone, so the arm
   a finished row reports is the arm its data carried before the last line.
   This is the step that carries certify_exact_armE and certify_spectral_armE
   out to a published row, where a paper's table reads them. *)
```

**N6, the restated paragraph.** `security_arm_of` repeats the manifest-row
reason from `SecurityArm` almost word for word. Replacement, which keeps the
reason where the concept is introduced and gives this declaration the position
that is its own:

```
(* Which of the two arms a published row carries, at one real field and one
   index of its family. It reads ab_arm past the publish statement, so it is
   the reader a paper's arm column is taken from, and publish_armE is why the
   publish statement does not change the answer. *)
```

Checked: the body is `ab_arm (published_at r) R idx`, so "reads ab_arm past
the publish statement" is accurate. The forward reference to `publish_armE` is
the file's own habit, as at `pgg_tableau.v:123`.

**N3, the missing comment.** `pgl27_row_word39E` has none, and the sentence
that belongs to it currently sits on the `_bind` definition. Move it:

on `pgl27_row_word39_bind`:

```
(** The same row written through the bind and its payloads, with no surface
    notation between the statements. *)
```

on the lemma, renamed per N3:

```
(** The two spellings are one term, so the conclude and publish surface adds
    no step and hides no payload, as the five spectral clauses do not for the
    certify statement. *)
```

**N14.** `t0_row_uniform_manifestE`'s comment is
`(** The manifest row is also the one the manifest writes for this path. *)`.
Its production sibling `five_card_row_uniform_rowE` carries the position the
new one drops: "Conversion decides it, so the descriptive row and the theorem
proved about it cannot drift apart." Use it.

**N12, the `done` note. Acceptable form, with one correction.** It is a
non-rendered `(* *)` note in a file whose declaration comments are `(** *)`,
placed at the head of a section and anchored to no declaration, carrying proof
strategy where the rule says proof strategy belongs. It carries a measurement
and says where the numbers are, which is the one form the rule allows for a
measurement. The date matches the file family's own convention, as at
`pgg_tableau_syntax.v:36`. I checked the pointer: `STATUS.md` does hold the
table, under "A hang shape, found by recompiling from source and removed", and
the note's "a tenth of a second" matches the 0.133 s row.

The correction is that "that search does not return" asserts non-termination,
while `STATUS.md` records "did not return in 130 s" and "did not return in
200 s". Replacement:

```
(* Every coordinate equation of this file closes by exact: erefl and not by
   [], because ssreflect's done does not reach reflexivity on a goal whose
   two sides are published_at of a branch point and of a continuation: it
   spends its search first, and on the concluded row below that search did
   not return inside the time bound. The conversion itself is a tenth of a
   second. Measured on 2026-09-19; the bound and the numbers are in
   STATUS.md, under the T0 step. *)
```

**N13.** `assumptions_report.v` cites the axiom as
`instances/s5/rigidity_s5_instance.v:179`. I verified the number: `Axiom
s5_group_order_eq` is at line 179 today. The name and the file are enough and
will not drift.

---

## 5. The index and header of `pgg_tableau.v`

**The ground for removing the `ab_arm` index line is verified.** The baseline
index lists 20 Definitions and 4 Key results. Against them, the file declares
fifteen level accessors: `ob_Ht`, `ob_He`, `ob_Hr`, `ob_obs`, `sp_Ht`,
`sp_He`, `sp_Hr`, `sp_obs`, `sp_f`, `ab_Ht`, `ab_He`, `ab_Hr`, `ab_obs`,
`ab_f`, `ab_port`. **Not one of the fifteen is indexed.** `ab_arm` is declared
immediately after `ab_port`, inside that block, and is one of them. Removing
its line is correct and is the cleaner of the two fixes the first round
offered.

Sixteen further declarations are likewise unindexed: `cert_eps`, `PortProp`,
`BridgedProp`, `ExactProp`, `SpectralPropAt`, `ObsPayload`, `FamPayload`,
`ExactPayload`, `SpectralPayload`, `RepricePayload`, `RestatePayload`,
`RestatedTableau`, `oe_correct_prop`, `observed_correct`,
`sampled_viewE_prop`, `tableau_start`. So the index is selective by design:
the two arms' records, the carriers, the bind, the five statements, the three
terminals, the published row and its readers.

**Order.** Source order after the fix pass is `SecurityPort`, `SecurityArm`,
`port_arm`, then the accessors, and at the end of the file `view_indist_of`,
`security_arm_of`, then the four `_armE`. Index order is `SecurityPort`,
`SecurityArm`, `port_arm` in Definitions; `security_arm_of` last among the
readers; `certify_exact_armE`, `certify_spectral_armE`, `conclude_armE`,
`publish_armE` after `port_reprice` in Key results. **Every one matches source
order**, and the 13-line inversion the first round found is pre-existing and
untouched. All 86 header lines are exactly 80 bytes and the `==` column is 29
throughout, unchanged.

The glosses are accurate. `conclude == the terminal publishing an upper bound
of the accumulated bound` and `port_reprice == a port's proposition at a
number above its own bound` both match the weakened obligation.

---

## 6. First round, item by item

| item | status |
|---|---|
| B1, `claim` a second word for `arm` | **Closed.** Seven renames, the two prose sentences rewritten, and the constructor scheme improved on what B1 proposed. See N17. |
| B2, the `at` keyword sentence | **Closed.** I checked the rewritten paragraph against the copy's notation rules myself: `at` follows the literal `leaks` in one rule and the literal `SpectralDecay` in the other, and `by` follows slot `L` of the encoded rule, slot `k` of the leaks rule and slot `c` of the conclude rule. The "twentieth" arithmetic is consistent with the nineteen the paragraph above names, and `conclude` following the literal `\|>` is right. |
| B3, `SecurityArm`'s false sentence | **Closed.** "two rows over one model and one pair of statuses are one manifest row" is what `t0_row_uniform_row_neq` supports. |
| B4, `ab_arm`'s false reason | **Closed.** The comment now attributes the uniformity to the two certify statements, with the honest scope "for a row written in the surface". |
| B5, two `republish` comments | **Closed.** Both rewritten, and zero `republish` remains in any `.v` file. |
| B6, T0 claiming a configuration it lacks | **Closed.** The header, the second continuation's comment and the `_row_neq` comment all say two continuations at one arm under two statuses. |
| B7, `_raw` beside `_bare` | **Closed differently, and better.** `_bind` as proposed; `_bare_bind` became `_unindexed_bind` because the payload changed under D8 and no longer has the defect "bare" would name. |
| The pins section | **Closed.** Six anonymous `Check`s became six named `_armE` lemmas beside their `_rowE`, plus four general ones, all `Proof. by []. Qed.`, all reachable by `Print Assumptions`, and all ten listed in `assumptions_report.v`. The one residue is N2: the accompanying recorded failure took an `E` it should not have. |
| S1, `port_arm` comment | Closed. |
| S2, `RepricePayload` comment | Closed. |
| S3, `conclude` comment | Closed. |
| S4, `port_reprice` comment | Closed, with the audit's own wording. |
| S5, positional pointers | **Closed for the three named, reopened by two new ones.** N5. |
| S6, "The reader discriminates." | Closed. |
| S7, `reprice` / `republish` / `publish` / `conclude` | Closed for the operation. Two carriers still name it. N16. |
| S8, `arm` against `claim` in the four rows copies | Closed. The three instance readings are unchanged and correct. |
| S9, `_false` | Closed, not applied, correctly. Precedents verified: `kim_cdiv1_false` at `instances/kim2025/kim_input_privacy.v:625`, `indep_adj_swap_false` in `groups/pgg_raag.v`. |
| S10, `pgl27_row_word41` and `pgl27_reprice41` | Closed, not applied, correctly. |

**The three SHOULD items `STATUS.md` D12 declines.**

1. *The landing names for the `t0_` declarations.* Reason given: "a landing
   decision, not a probe one, and the probe files keep their ledger prefixes,
   which the naming audit itself calls correct there." **The reason is sound
   and the pass then broke it.** `t0_sampled_branch_pgl27.v`, written in the
   same pass, carries no ledger prefix on any of its twelve declarations. One
   scheme or the other, but not both. This is N1.

2. *`pgl27_word_reprice41_false`, `pgl27_row_word41` and `pgl27_row_word39E`
   keep their names, "all three are the audit's own verdict."* **Accurate for
   all three.** I checked: S9 rules on `_false` with two tree precedents, S10
   rules on `pgl27_row_word41`, and B7 rules on `pgl27_row_word39E`, naming
   `dealt_params_stepE` as the precedent for an `E` between two spellings of
   one term. I part company with B7 on the third only because the file has a
   nearer precedent, `pgl27_row_word_certE`, for exactly this statement shape.
   That is N3, a SHOULD, not a reversal of the first round's reasoning.

3. *The three inherited notation lines stay over 80 bytes.* **Sound.** I
   verified all three are byte-identical to `manifest/pgg_tableau_syntax.v`
   lines 323, 361 and 384, and they are notation strings that cannot be
   wrapped.

---

## 7. Lines over 80 bytes

Three, in `pgg_tableau_syntax.v`, all inherited:

| line | bytes | over 80 in production today? |
|---|---|---|
| `Notation "t 'encoded' 'inputs' T 'layout' L 'by' enc 'decoded_by' d 'committed_by' procs 'fuel' n" :=` | 101 | yes, `manifest/pgg_tableau_syntax.v:323` |
| `Notation "s 'execute' 'terminates' 'by' 'vm_compute' 'endpoints' 'by' e 'recon' 'by' r" :=` | 90 | yes, `:361` |
| `Notation "s 'certify' 'SpectralDecay' 'at' R idx b 'tied' 'by' Hd 'ideal' u 'mixing' 'by' Hc 'invariant' 'by' Hk" :=` | 116 | yes, `:384` |

The other nine files have none. **Every line the fix pass wrote is within 80
bytes**, including the new `conclude` notation, the four general lemmas, the
six `_armE`, the whole of both T0 files and all header boxes.

Alignment defects, which the byte count does not catch, are N9, N10 and N11.

`STATUS.md` has 48 lines over 80, all of them Markdown table rows or long
quoted sentences. Markdown tables cannot wrap, and the probe's other status
notes do the same, so this is not raised.

---

## 8. Banned vocabulary

Case-insensitive whole-word scan of all ten `.v` files and `STATUS.md`:

| item | hits |
|---|---|
| the word for a highest point | 0 |
| the metaphor for a logical restriction, and its four inflections | 0 |
| the verb for assuming without proof, and its three inflections | 0 |
| the two-character token, capital L then digit one, for a distance | 0 |
| narrative or metaphor words for a result: escape, beats, smash, dodge, cap as a noun | 0 |
| status markers: TODO, FIXME, deferred, "fully machine-checked", "reused as-is" | 0 |
| meta: headline, "key lemma", crucially, importantly | 0 |

The words that do occur and might look like hits are all mathematical or are
the tree's own: `reprice` as the name of a chosen number, `bare` in
`pgg_tableau_syntax.v` for an unqualified identifier, which is production
text, and `raw` only in `STATUS.md` where it records the retired name.

One thing I will not flag as stage A's: `psl211_rows.v` uses an em-dash in
eleven production docstrings, as in `(** cardT — a card of the twelve-card
deck, the value a seat reads. *)`. It is baseline, it is that file alone, and
the one comment stage A added there does not use it.

---

## What I did not check

- **Nothing was compiled.** Every claim about what elaborates, what is
  rejected and what `exact: erefl` closes is taken from `STATUS.md` and from
  reading the source. The side swap in N4 in particular needs a compile.
- **Mathematical soundness.** Whether the `<=` obligation is the right one,
  whether the monotonicity condition is stated correctly, whether
  `pgl27_word_reprice41_false` proves what it says: the soundness audit's
  remit, and a second soundness audit appears to be under way in
  `audit-soundness-2/`, which I did not read.
- **The production names `SpectralDecay` and `view_indist_of`.** Out of scope
  by instruction. I note only that if "Decay" moves, `SpectralDecayArm` and
  the surface literal of the conclude and certify rules move with it, so the
  three `_armE` families and the `Fail pgl27_row_word_arm_neq` above all
  change together. That is an argument for settling it before stage B adds
  three more arm constructors, not after.
- **`STATUS.md` beyond the sections bearing on questions 3, 6 and 8.** I read
  the verdict table, the T0 step, the fix-pass section D1 to D12, and the G3
  and D2 tables. I did not audit the compile table or the `Print Assumptions`
  transcript.
- **Library collisions.** The scan covers the repository and the two landing
  probes as instructed. It does not cover MathComp, mathcomp-analysis,
  infotheo or Stdlib. The first round reports it checked
  `~/Projects/coq/_opam/lib/coq/user-contrib` and found only `eqW`, which the
  probe writes qualified as `ssr_ext.eqW`.
- **The PSL landing probe's content.** Included in the collision scan, 13
  files, not read for style.
