# Landing commit 1 of the reading-index spec: the surface (2026-09-21)

Notation only. Every production file below has code tokens identical to its
counterpart in `../surface2/staged/`; the comments are the landing's own work.
Nothing is committed by this pass. Rocq 9.0.0, repository HEAD b27f9ab, base
for the staged copies 2fc0108 (`git diff 2fc0108 HEAD -- '*.v'` empty over
production, as the task said).

## 1. What changed

Nine production files.

| file | code change | comment change |
|---|---|---|
| `manifest/pgg_tableau_syntax.v` | eight rules restated, one builder added | header keyword paragraphs rewritten, index entry added, eight notation comments |
| `instances/s5/tableau/s5_tableau_observed.v` | `publish Observed assuming a` | none |
| `instances/s5/tableau/s5_tableau_analysis_bridged.v` | `certify ... by`, `publish ... assuming` | none |
| `instances/s5/tableau/s5_tableau_checks.v` | the recorded `publish Observed` term | header, two boundaries added |
| `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` | `certify ... by`, five-clause `by b`, `conclude at`, `publish ... assuming` | none |
| `instances/pgl27/tableau/pgl27_tableau_checks.v` | the three recorded terms | header, one boundary added |
| `instances/psl211/tableau/psl211_tableau_analysis_bridged.v` | `certify ... by`, `publish ... assuming`, the obstruction terminal inline, `psl211_alldecks_number` added | the new definition's own comment (from the staged tree) |
| `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v` | `certify ... by`, `conclude at`, `publish ... assuming` | none |
| `instances/kim2025/tableau/five_card_tableau_checks.v` | the two recorded terms | none |

`psl211_alldecks_obstruction` is kept: `psl211_alldecks_obstruction_pf`'s type
is `ObstructionPayloadProp psl211_alldecks_obstruction`, so a statement still
needs the name. No declaration is removed anywhere.

## 2. The rules as landed

```coq
s certify ExactIndependence by w
s certify ExactIndependence by w leaks at k by H
s certify InputIndistinguishability by c
s certify IdealProximity by c
s certify InputIndistinguishability at R idx by b tied by Hd ideal u
          mixing by Hc invariant by Hk
s |> conclude at c by p
s |> publish t assuming a
s |> publish Observed assuming a
s |> publish Sampled t assuming a
s |> publish Obstruction InputDistinguishability at c by pf assuming a
```

The obstruction terminal expands through a typed builder added beside
`obs_payload` and `mk_indistinguishability`:

```coq
Definition input_distinguishability_obstruction (q : StackAt Sampled)
    (c : forall R : realType, R) : ObstructionPayload q :=
  fun R idx => @InputDistinguishabilityObstruction R _ _
                 (amf_sample (sp_f q) R idx) (c R).
```

No reading clause is landed; that is commit 2.

## 3. Three measurements the landing had to make

Each has its own file and `.msg` in this directory.

**`Fail` does not catch a parse error.** `f0_fail_catches_parse.v`, a
miniature with one rule of the shape `x stepping by y` and then
`Fail Definition f0_no_by := 1 stepping 2.`:

```
exit status 1
Error: Syntax error: '.' expected after [gallina] (in [vernac_aux]).
```

All four spellings the landing removes are refused by the parser, so none of
them can be recorded as a compiled `Fail` sentence in a production file. See
section 5.

**A notation string cannot be broken across source lines.**
`f1a_notation_break_space.v` (break after a space) and
`f1b_notation_break_nospace.v` (break before it) both give

```
exit status 1
Error: y is unbound in the notation.
```

so the two rules whose string passes eighty bytes stand on one line each. See
section 6.

**`of` reserves nothing.** `f2_of_baseline.v`,
`Definition f2_of_binder (of : nat) : nat := of.` in a file whose only
`Require` is ssreflect:

```
exit status 1
Error: Syntax error: [name] expected after '(' (in [closed_binder]).
```

This is what lets the header say `of` is a keyword of Rocq independently of
this file, measured the way `at` and `by` were.

## 4. The header's keyword paragraphs, checked

Every sentence of probe A round 2's draft (`../surface2/LEDGER.md`, section 4)
was checked against the file. The count of twenty holds. Four corrections were
needed.

1. The draft said "at follows a literal in some rules and a slot in others".
   `at` follows a literal in **all four** rules that use it: `leaks`,
   `InputIndistinguishability`, `conclude`, `InputDistinguishability`. No rule
   of the file puts `at` after a slot. Corrected.
2. The draft described `by` as following "the slot r of a reading clause".
   There is no reading clause in this commit. Replaced by the slot `idx` of
   the five-clause rule and the slot `c` of the obstruction terminal, both of
   which the draft omitted.
3. The draft's `of` sentence described a reading clause as well. `of` is
   described only as the word of the bind, following its slot `f`.
4. The draft's `assuming` sentence, "It is written in no code of the tree.
   Five .v files contain the word and each contains it inside a comment", is
   false once the landing writes the keyword. Replaced by a sentence that is
   true after the landing and measured after it: no declaration of the tree is
   named `assuming`, and the word occurs in the code of the syntax file and of
   the eight instance files that write programs in its surface and nowhere
   else.

Two sentences were added beyond the draft, as the task asked: one saying a
`leaks` annotation attaches to the evidence it follows, one saying the two
terms after `at` in the five-clause rule are binders.

The index of the header gained `input_distinguishability_obstruction`.

## 5. The four boundaries, and the mechanism that could not be used

The task asked for one `Fail` each. `Fail` cannot hold any of them: all four
are parse errors, and `f0_fail_catches_parse.v` measures that a `Fail` around
a parse error never runs, so the file holding it does not compile. Each
boundary is therefore recorded as an entry that writes the term inside its
comment and quotes the message, in the checks file of the instance whose
program it perturbs. The term itself is compiled once, unguarded, here.

| boundary | perturbs | recorded in | file here | message |
|---|---|---|---|---|
| certify evidence written bare | `s5_rand_published` | `s5_tableau_checks.v` | `r1_bare_certify.v` | `Error: Syntax error: '.' expected after [gallina] (in [vernac_aux]).` |
| publish terminal with no `assuming` | `s5_rand_published` | `s5_tableau_checks.v` | `r2_bare_publish.v` | `Error: Syntax error: 'assuming' expected after [term level 0] (in [term]).` |
| conclude terminal with no `at` | `pgl27_word_published39` | `pgl27_tableau_checks.v` | `r3_bare_conclude.v` | `Error: Syntax error: '.' expected after [gallina] (in [vernac_aux]).` |
| obstruction terminal with a named payload | `psl211_alldecks_obstruction_published` | `psl211_tableau_checks.v` | `r4_named_payload.v` | `Error: Syntax error: 'assuming' expected after [term level 0] (in [term]).` |

All four were compiled against the landed production surface, not against the
staged tree, each exit status 1.

The three checks-file headers were widened to say that a term the kernel
refuses stands under a `Fail` and is compiled there, and that a term the
parser refuses cannot. Their counts went from three to five (s5), from seven
groups to eight (pgl27), and from four to five (psl211). The s5 and psl211
titles drop the word "kernel", which no longer covers every entry of those
files.

This is the one place where the landing departs from the task as written. The
owner may prefer these four boundaries in the syntax file's header instead,
beside the other measured parser facts about the surface; moving them is a
comment-only edit.

## 6. Lines over eighty bytes

Four, all in `manifest/pgg_tableau_syntax.v`, all notation strings:

| line | bytes | status |
|---|---|---|
| 399 `encoded` rule | 101 | pre-existing, untouched |
| 437 `vm_compute` rule | 90 | pre-existing, untouched |
| 476 five-clause rule | 133 | pre-existing at 128, touched by this landing (`'by' ` inserted) |
| 539 obstruction terminal | 96 | written by this landing |

A notation string cannot be broken across source lines (section 3), and the
declarations are broken as the file's others are: the string and `:=` on one
line, the body and the level annotation on the lines under it. No other line
of any changed file passes eighty bytes.

## 7. Verification

**Diff against staged.** Code tokens identical for all nine files. Comment
words identical for six of them; the four that differ are the syntax file
(header and notation comments) and the three checks files (header and the new
boundary entries).

**No term changed.** The `_bindE`, `_certE`, `_pathE`, `_sampledE` and
`_propertyE` equations of the eight instance files are unedited and compile:
16 `exact: erefl` equations in the five-card file, 7 in each of the pgl27 and
psl211 analysis files, 1 in the s5 analysis file, 3 in the s5 observed file,
plus `pgl27_word_published39_bindE` and `pgl27_word_published_certE`, which
close by `by []` as they did.

**Closure.** `closure.py --changed HEAD` gives 22 files, no frozen file met.
`compile_closure.py` through the lock: every file ok, `ALL OK`, longest
7.7 s, about 100 s for the run. `instances/psl211/psl211_endpoints.v` was
never compiled and is not in the closure.

**Fidelity.** `landing_fidelity.v`, requiring production alone, compiles in
4.6 s, exit 0. Nine equations by `exact: erefl` put a program of each
instance against its bind form, taken unchanged from `../surface/k16_*.v` and
`../surface2/k_obstruction_inline.v`, and both `Check`s of the builder print:

```
input_distinguishability_obstruction
     : forall q : StackAt Sampled,
       (forall R : realType, R) -> ObstructionPayload q
```

It also puts the builder's payload at the all-decks family against
`psl211_alldecks_obstruction` by `exact: erefl`, which is why the instance's
proof, stated at the named payload, fits the terminal with no ascription.

## 8. Files in this directory

- `f0_fail_catches_parse.v`, `f1a_notation_break_space.v`,
  `f1b_notation_break_nospace.v`, `f2_of_baseline.v` and their `.msg`
- `r1_bare_certify.v`, `r2_bare_publish.v`, `r3_bare_conclude.v`,
  `r4_named_payload.v` and their `.msg`
- `landing_fidelity.v`
- this file
