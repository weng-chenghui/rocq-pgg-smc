# Probe A round 2, three decided rules (2026-09-21)

The three surface rules the owner decided after the read-aloud audit, at
spec commit 3aa41ab: the obstruction published inline with its kind and its
number, `conclude at c by p`, and the marginal bound of the five-clause rule
after `by`. Round 1 stays where it is under `../surface/`; this directory is
a fresh copy of its staged tree with round 1's surface already in it.

Production is untouched, every compile went through the `rocq1` lock, which
reported waiting while another process held it, and
`instances/psl211/psl211_endpoints.v` was never compiled.

The relative load path needed no fixing: `surface2` sits at the same depth
as `surface`, four directories below the repository root, so
`../../../../lib` resolves. The one change to the copied `_CoqProject` is
`-Q mini surface2_mini`, so the two probes' miniature roots do not share a
logical name.

Rocq 9.0.0, repository HEAD 10c1975.

## Summary

| item | verdict | shown by |
|---|---|---|
| 1(a) inline obstruction in the miniature, with a reading | **GO** | `mini/k5_inline.v`, `mini/k5_names_free.v` |
| 1(b) inline obstruction in the staged surface, without a reading | **GO** | `compile-staged.log`, `k_obstruction_inline.v`, `mini/k5_staged_names.v`, `msg/mutation_named_payload.after.msg` |
| 2 `conclude at c by p` | **GO** | `compile-staged.log`, `msg/k6_at_baseline.before.msg`, `msg/mutation_bare_conclude.after.msg` |
| 3 five-clause rule, `at R idx by b` | **GO** | `compile-staged.log`, `pgl27_word_published_certE` unchanged |
| 4 header sentences | drafted below | |
| 5 read aloud | two clauses remain, both outside the decided table | |

**Keyword count after all three rules: twenty. Unchanged from round 1.**
None of the three reserves anything new.

## 1(a) The inline obstruction with a reading, in the miniature

`mini/k5_inline.v` declares the decided rule

```coq
s |> publish Obstruction InputDistinguishability of r at c by pf assuming a
```

beside the three other publish rules, so the factoring question is asked of
the four together. Exit status 0 in 2.1 s.

**The type the expansion needs for `c`.** `forall R : realType, R`. That is
`ConcludedBound` of `manifest/pgg_tableau.v:649` with the option dropped:
`Definition ConcludedBound := forall R : realType, option R`, and an
obstruction's number is not optional, its kind carrying exactly one number.
The miniature uses the real `realType`, not a stand-in, so the
measurement is about the type the framework will use. The reading and the
number travel as the kind's two arguments.

**Every rule reaches its own bind form**, by `exact: erefl`:
`k5_obstructionE`, `k5_three_payloadE`, `k5_observedE`, `k5_sampledE`. So
the four factor and none of them captures another's text.
`k5_obstruction_readingE` reads the reading back off the published kind.

**Nothing is reserved.** `mini/k5_names_free.v`, exit 0, in a file requiring
the rule: `InputDistinguishability` works as a top-level identifier and as a
binder name; `InputDistinguishabilityPropAt` and
`InputDistinguishabilityObstruction` work as both; `Observed`, `Sampled` and
`Obstruction` work as binder names; and the rule still parses beside all of
them. `InputDistinguishability` follows the literal `Obstruction`, which
follows the literal `publish`, which follows the slot `s`, and only
`publish`'s position is after a slot. `publish` is reserved already.

This is the measurement that separates the inline rule from the withdrawn
`obstruction` opener: round 1 measured the opener reserved
(`../surface/msg/k4e_opener_binder.after.msg`), and the inline rule has no
opener.

## 1(b) The inline obstruction in the staged surface, without the reading

Round 1's staged framework carries no reading, so the rule landed here is

```coq
s |> publish Obstruction InputDistinguishability at c by pf assuming a
```

replacing `s |> publish Obstruction o by pf assuming a`.

**The builder.** The terminal takes a number and not a payload, so
`staged/manifest/pgg_tableau_syntax.v` gains

```coq
Definition input_distinguishability_obstruction (q : StackAt Sampled)
    (c : forall R : realType, R) : ObstructionPayload q :=
  fun R idx => @InputDistinguishabilityObstruction R _ _
                 (amf_sample (sp_f q) R idx) (c R).
Arguments input_distinguishability_obstruction : clear implicits.
```

beside `obs_payload` and `mk_indistinguishability`, which is where the file
keeps its typed builders. The `Arguments` line is needed for the reason the
file already records for `tg_f` and `exact_leaks`.

**What the builder gives up, stated.** `ObstructionPayload q` is
`forall R idx, ObstructionKind (amf_sample (sp_f q) R idx)`, so the
framework admits a number that differs at each index of a family. The
builder's `c` is a term in the field alone, so the rule writes one number
for every index. An obstruction whose number differs at two indices of one
family is written through the bind and the constructor, as before. No
program of the tree has one: the all-decks family has the single index
`tt`. This is a restriction of the surface and not of the framework, and it
is what lets the number appear in the program's own line.

**The instance's migration.** One statement, at
`staged/instances/psl211/tableau/psl211_tableau_analysis_bridged.v`. The
number is named beside the payload it is the number of:

```coq
Definition psl211_alldecks_number : forall R : realType, R :=
  fun R => (#|pgg_G psl211_M|%:R)^-1.
```

and the program reads

```coq
Definition psl211_alldecks_obstruction_published : PublishedObstruction :=
  psl211_exact_sampled
    |> publish Obstruction InputDistinguishability
       at psl211_alldecks_number
       by psl211_alldecks_obstruction_pf assuming BaselineClassicalOnly.
```

**Answers to the measured questions.**

| question | answer | shown by |
|---|---|---|
| does `InputDistinguishability` stay an identifier | yes, as a top-level identifier and as a binder name | `msg/k5_staged_names.after.msg`, exit 0 |
| do `InputDistinguishabilityPropAt` and `InputDistinguishabilityObstruction` stay usable | yes, both as global references | the same file |
| do `Obstruction`, `Observed`, `Sampled` stay binder names | yes, all three | the same file |
| do `ExactIndependence`, `InputIndistinguishability`, `IdealProximity` stay usable | yes, re-measured | the same file |
| does the rule factor with `publish Observed`, `publish Sampled t`, `publish t` | yes, no ambiguity warning, and all four reach their own bind form | `compile-staged.log`, `mini/k5_inline.v` |
| does the standalone payload `psl211_alldecks_obstruction` still typecheck | yes, unchanged, by plain constructor application | the staged file compiles |
| does `psl211_alldecks_obstruction_pf`, whose type is `ObstructionPayloadProp psl211_alldecks_obstruction`, still fit the terminal | yes: the builder's payload and the named one are convertible, and unification finds it with no ascription and no `@` | the staged file compiles |
| does the instance still NEED a named payload | **no** | `k_obstruction_inline.v`: `k_obstruction_pf_inline` states the proof at the builder's payload with the same two conjuncts, and `k_obstruction_no_named_payloadE` puts the program it terminates against the instance's own, by `exact: erefl` |
| does the program equal the old one by `exact: erefl` | yes | `k_obstruction_inline.v`, `k_obstruction_old_formE`, against the round-1 bind form `;;; publish_obstruction BaselineClassicalOnly of (mk_obstruction … psl211_alldecks_obstruction psl211_alldecks_obstruction_pf)` |
| do the consequence lemmas still hold where they did | yes | `psl211_alldecks_obstruction_published_pathE` by `exact: erefl` and `psl211_alldecks_published_input_distinguishability` through `obstruction_of`, both unchanged in the staged file, which compiles |
| is the number readable off the published value | yes | `k_obstruction_numberE`, `published_obstruction_kind … R tt = @InputDistinguishabilityObstruction … ((#\|pgg_G psl211_M\|%:R)^-1)` by `exact: erefl` |

`k_obstruction_inline.v` compiles in 24.5 s, exit 0. The 24.5 s is the file's
own load of the PSL(2,11) chain, not any one sentence.

**Mutation.** `mutation_named_payload.v`, the old spelling with a named
payload, exit 1, `msg/mutation_named_payload.after.msg`:

```
File "./mutation_named_payload.v", line 34, characters 69-70:
Error: Syntax error: 'assuming' expected after [term level 0] (in [term]).
```

**Keyword effect of this rule: none.** `Obstruction` follows the literal
`publish` and was already free (round 1). `InputDistinguishability` follows
the literal `Obstruction`, measured free above at both the miniature and the
staged surface. `at`, `by` and `assuming` are reserved already.

## 2 `conclude at c by p`

**`at` reserves nothing new.** `mini/k6_at_baseline.v`, whose only `Require`
is ssreflect, tries `Definition k6_at_binder (at : nat) : nat := at.` and
fails at parsing, `msg/k6_at_baseline.before.msg`:

```
File "./mini/k6_at_baseline.v", line 9, characters 23-25:
Error: Syntax error: [name] expected after '(' (in [closed_binder]).
```

So `at` is a keyword of Rocq before any file of this development is
required, which is what the header of `pgg_tableau_syntax.v` already
records for the `leaks` clause.

**Ten sites migrated**, in four files:

| file | sites |
|---|---|
| `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v` | 4 |
| `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` | 3 |
| `instances/pgl27/tableau/pgl27_tableau_checks.v` | 2 |
| `instances/kim2025/tableau/five_card_tableau_checks.v` | 1 |

The two bind spellings `;;; conclude c of p`, at
`pgl27_tableau_analysis_bridged.v:503` and `pgl27_tableau_checks.v:174`,
were deliberately left alone: they are the payload form the K16-style
equations put the surface against, and migrating them would destroy the
evidence.

**The equation holds.** `pgl27_word_published39_bindE` in the staged file
puts the migrated `pgl27_word_published39`, which now reads
`|> conclude at pgl27_bound39 by …`, against `pgl27_word_published39_bind`,
written entirely in binds and unchanged, and it still closes by `by []`.
`pgl27_word_published39_propertyE` likewise.

**Mutation.** `mutation_bare_conclude.v`, the terminal without `at`, exit 1,
`msg/mutation_bare_conclude.after.msg`:

```
File "./mutation_bare_conclude.v", line 36, characters 4-71:
Error: Syntax error: '.' expected after [gallina] (in [vernac_aux]).
```

## 3 The five-clause rule, `at R idx by b`

The rule becomes

```coq
s certify InputIndistinguishability at R idx by b tied by Hd ideal u
  mixing by Hc invariant by Hk
```

**It still separates from `certify InputIndistinguishability by c`.** Both
rules now contain `by`, and what separates them is the token immediately
after the property's name: `at` in the five-clause rule, `by` in the other.
Rocq raised no ambiguity warning and both spellings parse in the same file,
`staged/instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` carrying
the five-clause program at line 411 and the one-record spelling at line 425
inside `pgl27_word_published_sampledE`.

**One site**, `pgl27_tableau_analysis_bridged.v:412`, the bound moving from a
bare term after `idx` to a term after `by`. It is the only five-clause
statement in the tree.

**`pgl27_word_published_certE` holds unchanged.** It puts the five-clause
program against
`pgl27_dealt ;;; sample_step of pgl27_word_family ;;; certify_indistinguishability of pgl27_word_cert ;;; publish BaselineClassicalOnly of IdealFinite`
and still closes by `by []`, with no edit to the lemma. That is the evidence
that inserting `by` before the bound changed no term.

**Keyword effect: none.** `by` is reserved by ssreflect.

## Compile

All 25 staged files, exit status 0, no sentence over 5 s, about 105 s for the
tree. `compile-staged.log` has every line.

| file | s |
|---|---|
| `staged/manifest/pgg_tableau_syntax.v` | 4.5 |
| s5, the six | 3.4, 3.3, 4.0, 3.6, 4.2, 3.4 |
| pgl27, the six | 3.8, 3.9, 4.0, 3.8, 7.3, 4.7 |
| psl211, the six | 3.9, 3.8, 4.8, 3.9, 4.9, 4.5 |
| five-card, the six | 3.7, 3.8, 3.8, 4.0, 5.9, 4.7 |

No line of any changed file is over 80 bytes.

## 4 The keyword paragraph of the header, drafted

Not applied to production. It replaces the paragraph at lines 64 to 94 of
`manifest/pgg_tableau_syntax.v` and carries findings N27 to N32, N34 and N35
of `../audit-naming/REPORT.md`.

> The surface reserves twenty identifiers as global keywords in every file
> that requires this one: dealt, functionality, execute, endpoints, recon,
> sample, certify, leaks, tied, ideal, mixing, invariant, encoded, supplied,
> layout, decoded_by, committed_by, expecting, fuel and assuming. A token is
> reserved in two positions, measured on 2026-09-14 and 2026-09-21: when it
> follows a slot in some rule, and when it opens one. Every one of the
> twenty follows a slot, and no rule of this file opens with a literal.
>
> fuel is among them, measured on 2026-09-14: it follows the literal dealt
> in the dealer-dealt rule and would stay an identifier for that rule alone,
> but it follows a slot in the two rules added beside it.
>
> The tokens inputs, terminates, publish, conclude, vm_compute,
> ExactIndependence, InputIndistinguishability, IdealProximity,
> InputDistinguishability, Observed, Sampled and Obstruction follow a
> literal and stay identifiers, which is what keeps the three evidence
> constructors, the conclude terminal, the obstruction kind and the two
> completion levels usable by name. Observed, Sampled and Obstruction each
> follow the literal publish, and InputDistinguishability follows the
> literal Obstruction; each stays a binder name and a top-level identifier
> in a file whose Require lines are ssreflect and this one, and Observed and
> Sampled each stay the CompletionLevel constructor they name, as Tableau
> Observed in s5_tableau_observed.v and Tableau Sampled in
> s5_tableau_sampled.v write it. Inside the publish position the three
> tokens are taken by their rules, so the transfer-status slot of the
> three-payload rule cannot be filled by a bare token spelled Observed,
> Sampled or Obstruction, though a parenthesised one reaches the slot.
>
> at follows a literal in some rules and a slot in others, and was a keyword
> of Rocq before this file: a binder named at is refused in a file whose
> only Require is ssreflect. by follows the slot L of the encoded rule, the
> slot k of the leaks clause, the slot r of a reading clause and the slot c
> of the conclude terminal, so it would be a twenty-first, and it is not one
> only because ssreflect already reserves it, measured on 2026-09-19 by
> binding it in a file that requires nothing but ssreflect. by also follows
> the literal naming the security property in four of the five certify
> rules, and the evidence of a certify statement is the term after it; in
> the fifth the token after the property's name is at and the bound follows
> by. of follows the literal naming the security property in a reading
> clause and the slot f of the bind, and it reserves nothing, being an
> ssreflect keyword.
>
> assuming, measured on 2026-09-21, follows the slot t of the three-payload
> publish rule, the slot t of the Sampled terminal and the slot pf of the
> obstruction terminal, and the literal Observed in the fourth rule. In a
> file whose Require lines are ssreflect and this one it is refused both as
> a binder name and as a top-level identifier, and in a file that does not
> require this one both uses are accepted. It is written in no code of the
> tree. Five .v files contain the word and each contains it inside a
> comment.
>
> The surface has two kinds of word. A preposition carries one meaning
> throughout: of introduces what is read, at a number, a size or a real
> field with its index, by a proof or a piece of evidence, assuming an
> assumption status. A slot name says what the term after it is: dealt,
> encoded and supplied name the mode a run is driven in, inputs the input
> carrier, layout the sharing the dealer deals, decoded_by the reader of the
> committed payload list, committed_by the commit processes, expecting the
> value a run recovers, fuel the interpreter's budget, execute the run
> statement, terminates, endpoints and recon its three obligations, sample
> the model family, certify the security property, leaks the coalition size
> of a tightness annotation, tied the equation between the bound's law and
> the model's cut law, ideal the ideal cut, mixing the distance from it,
> invariant the constancy of a coalition's view, functionality the ideal
> function, conclude the number a program publishes and publish the level or
> the status it hands over.
>
> One of the twenty shadows a framework definition: endpoints is also the
> verifier's endpoint tuple in pgg_interface.v. A file requiring this
> surface must write that one through its module path. No file in the tree
> writes it bare. No file requiring the surface writes any of the other
> nineteen bare either, and no declaration of this file binds any of the
> twenty: the two realisation lemmas bind L and n, dealt_params_stepE binds
> x, q and n, and input_distinguishability_obstruction binds q and c.

Two notes on what the draft does and does not carry.

- The second position, a token that opens a rule, is stated although no rule
  of this file opens with a literal. Round 1 measured the position reserved
  (`../surface/msg/k4b_bare_binder.after.msg`,
  `../surface/msg/k4e_opener_binder.after.msg`), and the account of why a
  token is reserved is what stops the next rule being written without a
  measurement. That is finding N28.
- N35 is applied: the claim that the spec's sentence fails to cover
  `at R idx` is withdrawn, the sentence reading "a number, a size or a real
  field with its index". What is left of the point is in the read-aloud
  below, and it is a different point.

## 5 Reading the two programs aloud, term by term

### The PSL(2,11) obstruction program

With its prefixes spliced in:

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
  |> publish Obstruction InputDistinguishability
     at psl211_alldecks_number
     by psl211_alldecks_obstruction_pf assuming BaselineClassicalOnly.
```

Aloud: the algebra `psl211_algebra`, supplied with inputs of
`psl211_inputT`, at layout `psl211_alldecks_layout`, expecting
`psl211_alldecks_expected`, at fuel `psl211_fuel`; executed, terminating by
`psl211_alldecks_terminates`, with endpoints by `psl211_alldecks_endpoints`
and reconstruction by `psl211_alldecks_recon`; sampled at
`psl211_exact_family`; publishing an obstruction of kind input
distinguishability, at the number `psl211_alldecks_number`, proved by
`psl211_alldecks_obstruction_pf`, assuming `BaselineClassicalOnly`.

The terminal no longer reads as an application. Round 1 left
`publish Obstruction psl211_alldecks_obstruction`, the payload straight
after the literal; the kind's name now sits there and the number has `at`.

One clause of the program still reads as an application, and it is outside
the decided table:

1. **`supplied inputs T layout L expecting e fuel n`, and `sample f`.** Five
   bare terms after five slot names. These are the slot-name kind of word
   the header paragraph above now describes, so the surface has an account
   of them, but a reader meeting `sample psl211_exact_family` for the first
   time reads a function applied to a family. `dealt fuel n` is the same
   shape.

### The PGL(2,7) word program with `conclude at`

With its prefix spliced in:

```coq
pgl27_algebra
  dealt   fuel pgl27_fuel
  execute terminates by pgl27_dealt_terminates
          endpoints by pgl27_dealt_endpoints
          recon by pgl27_dealt_recon
  sample  pgl27_word_family
  certify InputIndistinguishability by pgl27_word_cert
  |> conclude at pgl27_bound39 by (fun R _ => ssr_ext.eqW (pow2_split R))
  |> publish IdealFinite assuming BaselineClassicalOnly.
```

Aloud: the algebra `pgl27_algebra`, dealt at fuel `pgl27_fuel`; executed,
terminating by `pgl27_dealt_terminates`, with endpoints by
`pgl27_dealt_endpoints` and reconstruction by `pgl27_dealt_recon`; sampled
at `pgl27_word_family`; certified for input indistinguishability by
`pgl27_word_cert`; concluded at `pgl27_bound39` by that function; published
at `IdealFinite` assuming `BaselineClassicalOnly`.

The conclude terminal no longer reads as an application. The one clause left
is the same as above: the slot names `dealt`, `fuel` and `sample` take a
bare term.

### The five-clause program, since its rule changed

```coq
  certify InputIndistinguishability at R idx
          by pgl27_word_marginal_bound R
          tied by esym (pgl27_word_cut_distE idx)
          ideal (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M))
          mixing by pgl27_word_mixing R
          invariant by pgl27_word_view_const R
```

The bound now reads as a clause. `ideal u` is the one clause of this rule
that still takes a bare term, and it is a slot name, not a preposition.

The residual point N35 leaves standing: in `at R idx` the two terms are
binders and everywhere else `at` is followed by a value. The rule is
`only parsing` and `R ident, idx ident` is what the notation declares, so
nothing is ambiguous, but `at` in this one position introduces names rather
than naming a value.

## Files

Under `notes/probes/2026-09-21-reading-index/surface2/`:

- `_CoqProject`, `compile.py`, `measure.py`, `migrate2.py`
- `compile-staged.log`, `migrate2.log`
- `staged/manifest/pgg_tableau_syntax.v` — the three changed rules and the
  new builder
- `staged/instances/{s5,pgl27,psl211,kim2025}/tableau/*.v`
- `k_obstruction_inline.v` — the four obstruction equations
- `mutation_bare_conclude.v`, `mutation_named_payload.v`
- `mini/k5_inline.v`, `mini/k5_names_free.v`, `mini/k5_staged_names.v`,
  `mini/k6_at_baseline.v`, `mini/k4_core.v`
- `msg/` — one message file per measurement, each with the command, the exit
  status, the elapsed time and the compiler's output
