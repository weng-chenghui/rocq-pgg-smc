# Probe A, the surface prepositions: ledger (2026-09-21)

Rows K1, K2, K3, K4 and K16 of the claim ledger of
`notes/20260921-reading-index-and-surface-prepositions-probe-design.md`.
Probe B holds the reading index; nothing here depends on it.

Production is untouched. Every file this probe wrote is under
`notes/probes/2026-09-21-reading-index/surface/`, every `.vo` of a staged
copy sits beside its `.v` under `staged/`, and `find . -name '*.vo' -not
-path './notes/*' -newermt '2026-09-21 08:45'` was empty after the staged
tree was built. Every compile went through the machine-wide `rocq1` lock,
which printed `waiting for the Rocq lock` twice while probe B held it.

Rocq 9.0.0, repository HEAD 2fc0108, branch `feat/tableau-extensions-probe`.

## Summary

| id | verdict | shown by |
|---|---|---|
| K1 | GO, with a cost | `assuming` becomes the **twentieth** global keyword; no code use in the tree. `msg/k1_assuming.{before,after}.msg`, `msg/k1_assuming_toplevel.{before,after}.msg` |
| K2 | GO | the three security-property names stay identifiers, before and after. `msg/k2_property_names.{before,after}.msg` |
| K3 | GO | all 25 staged files compile with the new rules and the old bare rules removed; 66 sites migrated. `compile-staged.log`, `msg/mutation_bare_certify.after.msg`, `msg/mutation_bare_publish.after.msg` |
| K4 | measured, **with a finding against the decided spelling** | a notation's LEADING literal IS reserved, so `InputDistinguishability of r at c` costs the kind's own name. Four alternatives priced. `mini/k4*.v`, `msg/k4*.msg` |
| K16 | GO | eight rules put against their bind form by `exact: erefl`, at all four instances. `k16_s5.v`, `k16_pgl27.v`, `k16_psl211.v`, `k16_kim.v`, plus two equations already in the tree |

Two findings the owner has to rule on are collected in **Owner questions**
at the end.

## What was staged and how

`staged/manifest/pgg_tableau_syntax.v` and the twenty-one files that
`Require` it, which are exactly the four `instances/*/tableau/` directories
(`grep -rln pgg_tableau_syntax --include='*.v'`, outside `notes/`). No other
file of the tree requires the surface, and no production file requires any
of the twenty-one, so the staged tree is closed: every other `Require` falls
through to production's `.vo`. `instances/psl211/psl211_endpoints.v` was
never compiled.

`_CoqProject` maps the staged roots to `pgg_smc` **after** production's, so a
`Require` resolves to the staged copy where one exists. `compile.py` reads
its flags from that file and runs one Rocq process at a time through the
lock. The load path is four levels up (`../../../../lib`), not three as in
the 2026-09-20 precedent, because this probe sits one directory deeper; with
three the first compile failed at `Cannot find a physical path bound to
logical path pgg_sharing_framework with prefix pgg_reconstruct`.

Provenance: the staged instance files write `certify ExactIndependence by w`
and `|> publish t assuming a`, which production's `pgg_tableau_syntax.vo`
cannot parse, and they compile. That is the witness that the staged surface
is the one in use, in the same style as the 2026-09-20 probe's
`certify_idealproximity`.

## K1 — `assuming`

**Claim.** `assuming` can be reserved: it follows the slot `t` in
`publish t assuming a`.

**Verdict: GO, and it is the twentieth global keyword.**

Measured with `mini/k1_assuming.v` and `mini/k1_assuming_toplevel.v`, whose
`Require` lines are ssreflect and the surface alone, which is how the
measurements quoted in the header of `pgg_tableau_syntax.v` were taken. One
text, compiled twice: `before` drops the staged roots from the flags so the
surface is production's, `after` keeps them. A reserved token fails at
parsing and `Fail` does not catch a parse error, so the outcome is the exit
status and the message.

| use | before | after |
|---|---|---|
| binder name, `Definition f (assuming : nat) := assuming.` | accepted, `nat -> nat` | **rejected**, `Syntax error: [name] expected after '(' (in [closed_binder]).` |
| top-level identifier, `Definition assuming : nat := 0.` | accepted, `assuming : nat` | **rejected**, `Syntax error: [ident_decl] expected after [def_token] (in [gallina]).` |

The two uses need two files: a parse error stops the file, so the top-level
test below the binder test is never reached.

`assuming` follows the slot `t` of `publish t assuming a` and the slot `pf`
of `publish Obstruction o by pf assuming a`. In the other two rules it
follows a literal. One slot is enough.

**Grep of the tracked tree outside `notes/`.** Ten files contain the word;
five of them are `.v` files and in every one it is inside a comment:
`instances/denboer1989/five_card_program.v:182`,
`legacy/security/pgg_free_words.v:119`,
`protocol/card_protocol_posterior.v:12`,
`security/pgg_collusion_bound.v:883`,
`security/pgg_schreier_weighted.v:380`. The other five are Markdown, TSV and
a build log. No declaration and no binder is named `assuming`
(`grep -nE "^(Definition|Lemma|...) +assuming\b"` and
`grep -nE "\(assuming *:"` both empty). No code use, as the spec states.

**New keyword count: twenty.**

### Draft replacement sentences for the keyword paragraph of the header

Not applied to production. Three edits to the paragraph at lines 64 to 94 of
`manifest/pgg_tableau_syntax.v`.

First sentence, `nineteen` becomes `twenty` and the list gains one name:

> The surface reserves twenty identifiers as global keywords in every file
> that requires this one: dealt, functionality, execute, endpoints, recon,
> sample, certify, leaks, tied, ideal, mixing, invariant, encoded, supplied,
> layout, decoded_by, committed_by, expecting, fuel and assuming.

Replacing the closing sentence `The count of nineteen is unchanged.`:

> assuming is the twentieth, measured on 2026-09-21: it follows the slot t
> of the three-payload publish rule and the slot pf of the obstruction rule,
> and in a file whose Require lines are ssreflect and this one it is refused
> both as a binder name and as a top-level identifier, where before the rule
> carried it both were accepted. It is written in no code of the tree, and
> the five files that use the word use it in a comment.

Added after the sentence about `by`, because the certify rules move it:

> by now also follows the literal naming the security property in each of
> the four certify rules, and the evidence of a certify statement is the
> term after it. That position reserves nothing further.

The sentence saying that `ExactIndependence`, `InputIndistinguishability`
and `IdealProximity` follow a literal and stay identifiers stands unchanged:
they still follow the literal `certify`, and K2 re-measured them today.

## K2 — the three security-property names

**Claim.** `of` and `by` after the evidence constructors' names reserve
nothing new.

**Verdict: GO.**

`mini/k2_property_names.v`, compiled twice from one text. Its `Require`
lines are ssreflect, `pgg_tableau` and the surface: the surface imports
`pgg_tableau` and does not export it, so the three names are in scope only
when the statement file requires it too, which is what every instance file
does.

| | before | after |
|---|---|---|
| `Check ExactIndependence.` | accepted | accepted |
| `Check InputIndistinguishability.` | accepted | accepted |
| `Check IdealProximity.` | accepted | accepted |
| each of the three as a binder name | accepted | accepted |

Exit status 0 in both directions, 5.4 s before and 3.4 s after. The printed
types are unchanged, for instance `InputIndistinguishability : forall (R :
reals.Real.type) (A : PGGAlgebraic) (E : ExecutionParams A) (sa :
SampleAdapter R (instance_exec E)), IndistinguishabilityCert sa ->
SecurityEvidence sa`.

## K3 — the new rules, and the old bare ones removed

**Claim.** `certify X by e` and the old bare rule cannot coexist
ambiguously; the bare rule is removed.

**Verdict: GO.**

The staged `pgg_tableau_syntax.v` carries eight changed rules:

```coq
s certify ExactIndependence by w
s certify ExactIndependence by w leaks at k by H
s certify InputIndistinguishability by c
s certify IdealProximity by c
s |> publish t assuming a
s |> publish Observed assuming a
s |> publish Sampled t assuming a
s |> publish Obstruction o by pf assuming a
```

The five-clause input-indistinguishability rule is untouched: it is
separated from `certify InputIndistinguishability by c` by the token after
the property's name, `at` against `by`, and no factoring was needed. Rocq
raised no ambiguity warning on any of the four prefix-sharing pairs.

### Site counts per file

66 sites in 9 of the 21 files. `migrate.py` prints every changed line; the
log is reproducible by re-running it on a fresh copy.

| file | sites |
|---|---|
| `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v` | 24 |
| `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` | 17 |
| `instances/psl211/tableau/psl211_tableau_analysis_bridged.v` | 9 |
| `instances/pgl27/tableau/pgl27_tableau_checks.v` | 7 |
| `instances/s5/tableau/s5_tableau_analysis_bridged.v` | 4 |
| `instances/kim2025/tableau/five_card_tableau_checks.v` | 3 |
| `instances/s5/tableau/s5_tableau_checks.v` | 1 |
| `instances/s5/tableau/s5_tableau_observed.v` | 1 |
| the other twelve staged files | 0 |

By rule, counted off the changed lines: 32 certify statements (11
`ExactIndependence`, 15 `InputIndistinguishability`, 6 `IdealProximity`) and
34 publish terminals (31 three-payload, 2 `Observed`, 1 `Obstruction`).
Of the `ExactIndependence` sites two carry the tightness annotation, at
`pgl27_tableau_analysis_bridged.v` and inside the `Fail` of
`pgl27_tableau_checks.v`. No program of the tree
writes the `Sampled` terminal, so that rule had nothing to migrate; it is
exercised in `k16_psl211.v` instead.

No program is quoted inside a comment. A comment scanner over the
twenty-one files looked for lines carrying two or more surface keywords or a
`|>`, inside `(* *)`, and every hit was prose about a statement, never a
statement.

One line went over 80 bytes after the insertion,
`s5_tableau_checks.v:99` at 87, and was wrapped by hand.

### Compile

All 25 files, in dependency order (per instance: algebraic, executable,
observed, sampled, analysis_bridged, checks; s5 before kim2025, because
`five_card_tableau_checks.v` requires `s5_tableau_analysis_bridged`). Every
file exit status 0. Not one sentence took over 5 s, so the traps of ledger
row K18 did not appear in this half of the work.

| file | s |
|---|---|
| `staged/manifest/pgg_tableau_syntax.v` | 4.3 |
| `s5_tableau_{algebraic,executable,observed,sampled,analysis_bridged,checks}` | 3.3, 3.3, 3.9, 3.5, 3.9, 3.4 |
| `pgl27_tableau_{algebraic,executable,observed,sampled,analysis_bridged,checks}` | 3.7, 3.7, 3.9, 3.8, 7.2, 4.6 |
| `psl211_tableau_{algebraic,executable,observed,sampled,analysis_bridged,checks}` | 3.8, 3.8, 4.8, 3.8, 4.8, 4.4 |
| `five_card_tableau_{algebraic,executable,observed,sampled,analysis_bridged,checks}` | 3.7, 3.8, 3.7, 4.0, 5.9, 4.7 |

About 100 s for the whole staged tree.

### Mutation checks

Both are parse errors, which `Fail` does not catch, so each file was
compiled once without a guard and the message kept.

`mutation_bare_certify.v` — `s5_rand_published` with `by` removed from its
certify statement, nothing else changed. Exit status 1,
`msg/mutation_bare_certify.after.msg`:

```
File "./mutation_bare_certify.v", line 30, characters 4-51:
Error: Syntax error: '.' expected after [gallina] (in [vernac_aux]).
```

The span 4 to 51 is the whole clause
`certify ExactIndependence s5_rand_exact_witness`. The message names the
line but not the missing word, which is the weaker of the two.

`mutation_bare_publish.v` — the same program with `assuming` removed from
its terminal. Exit status 1, `msg/mutation_bare_publish.after.msg`:

```
File "./mutation_bare_publish.v", line 33, characters 69-70:
Error: Syntax error: 'assuming' expected after [term level 0] (in [term]).
```

This one names the missing word and points at the character where it should
have been.

## K4 — the two notations probe B will need

Measured in a miniature under `mini/`, whose only `Require` is ssreflect
plus `k4_core.v`. `k4_core.v` has stand-ins for the objects a statement
connects, all natural numbers under other names, and copies the bind and its
`of` from `pgg_tableau.v` at the same level and associativity, so that a
clash between the `of` of a reading clause and the `of` of the bind would
show. Nothing in the miniature is a claim about security.

### (a) `certify ExactIndependence of r by w` beside `certify ExactIndependence by w`

**They factor.** `mini/k4a_factor.v` declares four rules at once and all
four parse and elaborate:

```coq
s certify ExactIndependence by w
s certify ExactIndependence of r by w
s certify ExactIndependence by w leaks at k by H
s certify ExactIndependence of r by w leaks at k by H
```

Levels: level 90, left associativity, every slot at level 0, exactly the
levels the four rules already in `pgg_tableau_syntax.v` use. The two
annotated rules are `only parsing`, as their originals are. No ambiguity
warning, exit status 0 in 0.2 s.

Each spelling is put against its bind form by `exact: erefl`, so a rule that
parsed but reached a different term would have been caught:
`k4a_defaultE`, `k4a_readingE`, `k4a_default_leaksE`,
`k4a_reading_leaksE`. `k4a_reading_not_default` proves the two reach
different terms, and `k4a_default_is_default_reading` proves the omitted
clause is the default reading written out, which is the convertibility
ledger row K5 will need at the framework.

**`of` does not clash with the bind's `of`.** `k4a_bind`, written
`stage0 ;;; cert_exact of 3`, parses in the same file as all four rules.
`of` is a keyword already, from ssreflect and from the bind, so the reading
clause reserves nothing through it.

**One trap.** The miniature's `annotate` needed
`Arguments annotate : clear implicits.`, because its `k` occurs in the type
of its `H` and `Unset Strict Implicit` inferred it, so the annotation's
number had no slot and the error read
`The term "1" has type "nat" while it is expected to have type
"(0 < ?k) = true"`. `pgg_tableau_syntax.v` already carries that directive
for `exact_leaks`. Any new reading-indexed builder needs the same.

### (b) to (e) the obstruction kind, four spellings priced

**The finding: a notation's LEADING literal IS reserved as a global
keyword.** This corrects what the header of `pgg_tableau_syntax.v` implies
by listing only the after-a-slot position, and it is the one measurement of
this probe that went against expectation.

| form | file | reserves | is the kind's own name still an identifier |
|---|---|---|---|
| (b) `InputDistinguishability of r at c` | `mini/k4b_kind.v` | `InputDistinguishability` | **no** |
| (c) `r distinguishable at c` | `mini/k4c_kind_slotfirst.v` | `distinguishable` | yes |
| (d) `InputDistinguishabilityObstruction r c`, no notation | `mini/k4d_plain.v` | nothing | yes |
| (e) `obstruction InputDistinguishability of r at c` | `mini/k4e_kind_prefixed.v` | `obstruction` | yes |

Each cost is a measurement, not a reading of the rule:

- (b) `msg/k4b_bare_binder.after.msg`, exit 1,
  `Syntax error: [name] expected after '(' (in [closed_binder]).`;
  `msg/k4b_bare_toplevel.after.msg`, exit 1,
  `Syntax error: [ident_decl] expected after [def_token] (in [gallina]).`
  The same two uses succeed in `mini/k4d_plain.v`, which differs only in
  not requiring the notation, so the notation is the cause.
- (c) `msg/k4c_slotfirst_binder.after.msg`, exit 1, the same closed-binder
  error for `distinguishable`. A first literal after a leading slot is
  reserved, which the header already records.
- (e) `msg/k4e_opener_binder.after.msg`, exit 1, the same error for
  `obstruction`; and `msg/k4e_names_free.after.msg`, exit 0, where
  `InputDistinguishability` is accepted as a top-level identifier, as a
  binder name and as a `Check`, beside a parse of the rule itself. So the
  cost moves from the kind's name to the opening word.

**Prefix sharing is safe in every form.** `msg/k4b_prefix_ok.after.msg`,
exit 0: with `InputDistinguishability` reserved,
`InputDistinguishabilityPropAt` and `InputDistinguishabilityObstruction`
both work as global references and as binder names, and the rule still
parses beside them. The lexer takes the maximal identifier, so what is
reserved is the exact token and not the prefix.

**A near token.** `msg/k4b_near_token.after.msg`, exit 0: with
`InputDistinguishability` reserved, `InputIndistinguishability` stays an
identifier. Under (b) the tree would carry two tokens two letters apart with
opposite grammatical status, one a keyword and one the name of a security
property. Under (c), (d) and (e) it would not.

**None of the three candidate words is used as an identifier today.**
`grep -nE "^(Definition|Lemma|Theorem|Notation|Variable|Hypothesis|Record|Inductive|Variant|Let|Corollary|Fixpoint) +(InputDistinguishability|distinguishable|obstruction)\b"`
and `grep -nE "\((InputDistinguishability|distinguishable|obstruction) *:"`
over the tracked `.v` files outside `notes/` are both empty. Every textual
hit for the three words is prose inside a comment. So any of the four forms
can be landed today; the question is what each forecloses.

**Recommendation: (e), `obstruction InputDistinguishability of r at c`.**
It costs one keyword, the same as the decided (b), but spends it on a
generic word instead of on the kind's own name. That keeps
`InputDistinguishability` available as a declaration, which matters because
the framework's `ObstructionKind` at `manifest/pgg_tableau.v:1423` is
`Variant ObstructionKind ... := | InputDistinguishabilityObstruction of R`
and probe B's reading index changes that constructor's arity: a reader or a
proposition named `InputDistinguishability` is a name the reading work is
likely to want. It also removes the near-token hazard. It reads in the
decided prepositions unchanged, `of` for what is read and `at` for the
number, and it puts the word that says what kind of thing this is first,
which is how the manifest's column reads.

(d) is the zero-cost fallback if the owner wants no twenty-first keyword. It
gives up the prepositions: which argument is the reading and which the
number is then read off the constructor's type and not off the text, which
is the problem section 1 of the spec is about. (c) is not recommended: it
costs the same keyword as (e), puts the reading before the word that says
what is claimed, and names the claim with an adjective where the surface
names claims with nouns everywhere else.

## K16 — the migration is notation only

**Claim.** For one program per instance, the old-surface term written in
bind form equals the new-surface term, by `erefl`.

**Verdict: GO.** Eight equations, covering all eight changed rules.

Two of them were already in the tree and compiled in the staged copies
**unchanged**, which is itself the evidence:

| equation | file and line | what it puts against the bind form |
|---|---|---|
| `pgl27_word_published_certE` | `staged/.../pgl27_tableau_analysis_bridged.v:434` | the five-clause `certify InputIndistinguishability at R idx …` program and `publish t assuming a`, against `;;; certify_indistinguishability of pgl27_word_cert ;;; publish BaselineClassicalOnly of IdealFinite` |
| `pgl27_word_published39_bindE` | `staged/.../pgl27_tableau_analysis_bridged.v:507` | `certify InputIndistinguishability by c`, `conclude c by p` and `publish t assuming a`, against `pgl27_word_published39_bind`, which is written entirely in binds |

Both close by `by []`, as they did before the migration, and neither was
edited.

Six more were written for this probe, one file per instance:

| lemma | file | rule covered |
|---|---|---|
| `k16_s5_observed_bindE` | `k16_s5.v` | `\|> publish Observed assuming a` |
| `k16_s5_exact_bindE` | `k16_s5.v` | `certify ExactIndependence by w`, `\|> publish t assuming a` |
| `k16_pgl27_exact_bindE` | `k16_pgl27.v` | `certify ExactIndependence by w leaks at k by H` |
| `k16_kim_indistinguishability_bindE` | `k16_kim.v` | `certify InputIndistinguishability by c` |
| `k16_psl211_proximity_bindE` | `k16_psl211.v` | `certify IdealProximity by c` |
| `k16_psl211_obstruction_bindE` | `k16_psl211.v` | `\|> publish Obstruction o by pf assuming a` |
| `k16_psl211_sampled_bindE` | `k16_psl211.v` | `\|> publish Sampled t assuming a`, with its program written here because the tree has none |

Every one closes by `exact: erefl`, never `by []`, because an equation
between programs across a terminal has hung under `by []` before. Timings
of the final run: `k16_s5.v` 3.8 s, `k16_pgl27.v` 4.3 s, `k16_psl211.v`
4.4 s, `k16_kim.v` 4.3 s.

## Reading two migrated programs aloud, term by term

### The PGL(2,7) word program with `conclude`

`staged/instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:492`,
with its prefix `pgl27_dealt` from
`staged/instances/pgl27/tableau/pgl27_tableau_observed.v` spliced in:

```coq
pgl27_algebra
  dealt   fuel pgl27_fuel
  execute terminates by pgl27_dealt_terminates
          endpoints by pgl27_dealt_endpoints
          recon by pgl27_dealt_recon
  sample  pgl27_word_family
  certify InputIndistinguishability by pgl27_word_cert
  |> conclude pgl27_bound39 by (fun R _ => ssr_ext.eqW (pow2_split R))
  |> publish IdealFinite assuming BaselineClassicalOnly.
```

Aloud: the algebra `pgl27_algebra`, dealt at fuel `pgl27_fuel`; executed,
terminating by `pgl27_dealt_terminates`, with endpoints by
`pgl27_dealt_endpoints` and reconstruction by `pgl27_dealt_recon`; sampled
at `pgl27_word_family`; certified for input indistinguishability by
`pgl27_word_cert`; concluded at `pgl27_bound39` by that function; published
at `IdealFinite` assuming `BaselineClassicalOnly`.

Every clause reads as a clause. Nothing reads as an application any more:
before the migration the last two lines were `certify
InputIndistinguishability pgl27_word_cert` and `|> publish IdealFinite
BaselineClassicalOnly`, and both read as a name applied to an argument.

Two clauses still read badly, and neither is fixed by this migration.

1. **`dealt fuel n` has no preposition and two readings.** `dealt` is the
   mode and `fuel` the budget, so the line reads as two clauses run
   together. `sample f` is the same shape: a bare term after a literal. Both
   are outside the decided table, and recorded here only.
2. **`fuel pgl27_fuel` and `at k`, `at R idx`, `at c` are four different
   things after a one-word marker.** The decided table fixes `at` to a
   number, a size or a real field, which is three of those four; the fourth,
   `at R idx` in the five-clause rule, binds two variables. That rule is
   `only parsing` and its `at` is an ssreflect keyword already, so nothing
   breaks, but the spec's sentence *`at` a number, a size or a real field*
   does not cover `at R idx` as written and should either name that case or
   the rule should use another word.

`by` now carries three jobs in this one program: the three run obligations
(`terminates by`, `endpoints by`, `recon by`), the evidence of the certify
statement, and the proof of the terminal's bound. The spec says `by`
introduces *a proof or a piece of evidence*, which is a single meaning only
if a certificate counts as a proof. It does: `pgl27_word_cert` is a record
whose fields are proofs. So this is one meaning, not two, and the clause is
sound. Worth saying in the header, because a reader meeting `certify … by`
for the first time may read `by` as *by means of*.

### The PSL(2,11) obstruction program

`staged/instances/psl211/tableau/psl211_tableau_analysis_bridged.v:537`,
with its prefixes spliced in:

```coq
psl211_algebra
  supplied inputs psl211_inputT
           layout psl211_alldecks_layout
           expecting psl211_alldecks_expected
           fuel psl211_fuel
  execute terminates by psl211_alldecks_terminates
          endpoints by psl211_alldecks_endpoints
          recon by psl211_alldecks_recon
  sample psl211_exact_family
  |> publish Obstruction psl211_alldecks_obstruction
     by psl211_alldecks_obstruction_pf assuming BaselineClassicalOnly.
```

Aloud: the algebra `psl211_algebra`, supplied with inputs of
`psl211_inputT`, at layout `psl211_alldecks_layout`, expecting
`psl211_alldecks_expected`, at fuel `psl211_fuel`; executed, terminating by
`psl211_alldecks_terminates`, with endpoints by `psl211_alldecks_endpoints`
and reconstruction by `psl211_alldecks_recon`; sampled at
`psl211_exact_family`; publishing the obstruction
`psl211_alldecks_obstruction`, proved by `psl211_alldecks_obstruction_pf`,
assuming `BaselineClassicalOnly`.

The clause the migration was for is fixed. Before it, the terminal ended
`by psl211_alldecks_obstruction_pf BaselineClassicalOnly`, which reads as
the proof applied to the status, and the type is what stopped it being read
that way. Now the status has a word of its own.

Two clauses still read as an application.

1. **`publish Obstruction o`** — the obstruction follows the literal
   `Obstruction` with no preposition, so it reads as `Obstruction` applied
   to `o`. It is the same defect the certify statements had.
   `publish Obstruction of o by pf assuming a` would fix it at no keyword
   cost, because `of` is reserved already. Not in the decided table;
   recorded.
2. **`supplied inputs T layout L expecting e fuel n`** — four bare terms
   after four one-word markers, none of them a preposition. Outside the
   decided table; recorded.

One more reading point, about the surface and not this program. The word
`publish` is followed by four different kinds of thing across the four
rules: a transfer status, the level `Observed`, the level `Sampled`, and
the literal `Obstruction`. Section 4 of the spec records this and says
`assuming` does not change it. It does not; after the migration the line
still reads *publish <something> assuming <status>* where the something has
four grammars.

## Anything that surprised me

1. **A notation's leading literal is reserved.** I expected it to be free,
   on the reasoning that only a token after a slot needs to be a keyword.
   It is not: `mini/k4b_kind.v` reserves `InputDistinguishability`, and the
   two identifiers sharing its prefix survive only because the lexer takes
   the maximal munch. This changes what the decided spelling of the
   obstruction kind costs, and it is the reason for the owner question
   below.

2. **The two mutation messages are very unequal.** The missing `assuming`
   is reported as `'assuming' expected after [term level 0]`, which names
   the fix. The missing `by` is reported as
   `'.' expected after [gallina]`, which does not. A reader who writes the
   old certify spelling by habit gets a message that does not say what is
   wrong. Worth a line in the header saying which word is missing when that
   error appears at a certify statement.

3. **Nothing was slow.** Not one sentence of the staged tree took over 5 s,
   and the whole tree is about 100 s. The `by []` equations across
   terminals that have hung in this repository before
   (`pgl27_word_published_certE`, `pgl27_word_published39_bindE`) were
   untouched by the migration and stayed fast. The new equations were
   written with `exact: erefl` anyway.

4. **The staged tree is smaller than it looks.** Only the four
   `instances/*/tableau/` directories require the surface, and no
   production file requires any of them, so the closure pass the landing
   needs is 22 files and not the tree.

5. **The load path depth caught me once.** The 2026-09-20 precedent sits
   three directories below the repository root and this probe four, so the
   copied `_CoqProject` failed at the first compile. Worth a line in the
   landing plan if another probe copies it.

## Owner questions

1. **The obstruction kind's spelling.** The decided table says
   `InputDistinguishability of r at c`. Measured, that reserves
   `InputDistinguishability` as a global keyword in every file requiring the
   surface, so no declaration and no binder may ever carry that exact name,
   and the tree would hold `InputDistinguishability` as a keyword two
   letters from `InputIndistinguishability` as an identifier. The
   alternative `obstruction InputDistinguishability of r at c` costs the
   same one keyword, spends it on `obstruction`, and keeps both names.
   Recommended, but it is a change to a decided row and not mine to make.

2. **`at R idx` in the five-clause rule.** The spec's sentence about one
   preposition per meaning covers `at` for a number, a size and a real
   field. The five-clause rule also uses `at` to bind two variables at once.
   Either the sentence names that case or the rule takes another word.

3. **`publish Obstruction o`, with no preposition.** Recorded above, at no
   keyword cost to fix. Not in the decided table.

## Files

Under `notes/probes/2026-09-21-reading-index/surface/`:

- `_CoqProject`, `compile.py`, `measure.py`, `migrate.py`
- `compile-staged.log` — the 25 staged compiles and the probe compiles, with timings
- `migrate.log` — every one of the 66 changed lines, before and after
- `staged/manifest/pgg_tableau_syntax.v` — the eight changed rules
- `staged/instances/{s5,pgl27,psl211,kim2025}/tableau/*.v` — the 21 migrated files
- `k16_s5.v`, `k16_pgl27.v`, `k16_psl211.v`, `k16_kim.v`
- `mutation_bare_certify.v`, `mutation_bare_publish.v`
- `mini/k1_assuming.v`, `mini/k1_assuming_toplevel.v`, `mini/k2_property_names.v`
- `mini/k4_core.v`, `mini/k4a_factor.v`
- `mini/k4b_kind.v`, `mini/k4b_prefix_ok.v`, `mini/k4b_bare_binder.v`,
  `mini/k4b_bare_toplevel.v`, `mini/k4b_near_token.v`
- `mini/k4c_kind_slotfirst.v`, `mini/k4c_slotfirst_binder.v`
- `mini/k4d_plain.v`
- `mini/k4e_kind_prefixed.v`, `mini/k4e_names_free.v`, `mini/k4e_opener_binder.v`
- `msg/` — 19 message files, one per measurement, each carrying the command,
  the exit status, the elapsed time and the compiler's output
