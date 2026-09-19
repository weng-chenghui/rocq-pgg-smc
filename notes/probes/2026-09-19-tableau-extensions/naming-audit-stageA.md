# Naming, style and statement-comment audit of stage A

NO-GO.

Six blocking findings. Four are sentences that are false or that state
something the declaration does not show, one is a two-word-for-one-concept
split across the framework file and every rows file, and one is a pair of
adjacent name shapes that mean two unrelated things.

Read-only audit. No Rocq was run, no existing file was edited. Scope: the six
copies under `notes/probes/2026-09-19-tableau-extensions/` diffed against
`history/*.0-baseline`, `*.1-after-C`, `*.2-after-K`, plus the three
probe-only files.

---

## Verdict table

| Item | Verdict |
|---|---|
| 1. Names | NO-GO. B1, B6. |
| 2. The pins | SHOULD-FIX. Six anonymous `Check`s where the rows files use named lemmas. |
| 3. Statement comments | NO-GO. B3, B4, B5, plus eight SHOULD-FIX. |
| 4. Header sentences and index | NO-GO. B2. Index: one entry out of file order, four declarations of `pgl27_rows.v` unindexed. |
| 5. Probe-only idiom in the copies | GO. None found. |
| 6. Collisions | GO. Every new identifier is new outside the probe; `eqW` is infotheo's and is written qualified. |
| 7. Banned vocabulary | GO. Zero hits in every file of PROBE outside `history/`. |

---

## Blocking findings

### B1. `claim` is a second word for what the file calls the `arm`

`manifest/pgg_tableau.v` uses the word *arm* 40 times as the designator of the
alternative a row commits to, including the index gloss
`SecurityPort == the arm an instance certifies`. Stage A adds a type
designating exactly that alternative and calls it `SecurityClaim`, nine lines
below `SecurityPort`. The index now reads, three lines running:

```
(*   SecurityPort           == the arm an instance certifies                  *)
(*   SecurityClaim          == the name of a claim, with no witness attached  *)
(*   port_claim             == the claim a port carries                       *)
```

A reader of those three lines cannot tell whether *arm* and *claim* are one
thing or two.

The constructors make it worse. `ExactViewIndependence` and
`SpectralViewDecay` are one-word variants of the port constructors
`ExactIndependence` and `SpectralDecay`, and the statement surface writes the
port constructors as literals, so in `pgl27_rows.v` a reader meets
`certify SpectralDecay pgl27_word_cert` on one line and `= SpectralViewDecay`
eight lines later. Nothing in the spelling says which is the constructor
carrying a certificate and which is the tag. The inserted word `View` adds no
distinction either: `ExactIndependence` already means independence of the
coalition's *view* from the secret, by the header at `:25-26`.

The extension test fails too. Later stages add a third arm and the paper's
column is planned with five values. The current scheme gives no rule for
forming the third name: the port would be `IdealProximity` and the tag would
be `IdealProximityViewSomething`, with `View` inserted by taste.

**Rename table.**

| old | new | reason |
|---|---|---|
| `SecurityClaim` | `SecurityArm` | The file's own word for the alternative, 40 uses. The type names that alternative with its payload forgotten. |
| `ExactViewIndependence` | `ExactArm` | The port constructor already carries the mathematical content; the tag names the arm. Removes the near-duplicate spelling that stands beside `ExactIndependence` in every rows file. |
| `SpectralViewDecay` | `SpectralArm` | Same. |
| `port_claim` | `port_arm` | Reads the arm off a port. |
| `stack_claim` | `ab_arm` | It is a reader of `StackAt AnalysisBridged` and sits in the block of `ab_Ht`, `ab_He`, `ab_Hr`, `ab_obs`, `ab_f`, `ab_port`. `stack_` is a prefix no declaration of the tree uses. |
| `security_claim_of` | `security_arm_of` | `_of` is the file's suffix for a reader of a published row: `run_correct_of`, `view_identification_of`, `view_secrecy_of`, `view_indist_of`. |
| `pgl27_word_claim_is_not_exact` | `pgl27_row_word_arm_exactE` | Named after what is attempted, an equation pinning the word row's arm as the exact one. Distinct from the existing `pgl27_word_arm_is_not_exact` at production `:576`, which attempts a projection, not a pin. |

Extension to five values, with the paper's column in the same order:

```
Variant SecurityArm :=
  ExactArm | SpectralArm | ProximityArm | LeakageArm | DependenceArm.
```

If the author prefers to keep the mathematical word inside the constructor,
the uniform alternative is `ExactIndependenceArm`, `SpectralDecayArm`,
`IdealProximityArm`, `LeakageCeilingArm`, `DependenceArm`. One suffix, applied
to every value, and no value spelled one word away from a port constructor.
Either scheme is acceptable; the present one is not.

Carriers of the rename: `PROBE/pgg_tableau.v:29`, `:52-53`, `:63-64`, `:75-76`,
`:163-181`, `:276-284`, `:769-779`; `PROBE/pgl27_rows.v:331-349`, `:419-423`;
`PROBE/five_card_rows.v:352-358`; `PROBE/s5_rows.v:289-295`;
`PROBE/psl211_rows.v:188-194`; `PROBE/assumptions_report.v:23-26`;
`STATUS.md` step 5.

While renaming, `PROBE/pgl27_rows.v:574` reads "The two arms are different
claims"; write "The two arms are different statements", which is the header's
own phrasing at `pgg_tableau.v:24-25`.

### B2. `PROBE/pgg_tableau_syntax.v:70` says `at` follows a slot. It does not.

Current rewritten text, `:67-72`:

```
(* added beside it. The tokens inputs, terminates, publish, conclude,         *)
(* vm_compute, ExactIndependence and SpectralDecay follow a literal and stay  *)
(* identifiers, which is what keeps the two port constructors and the         *)
(* reprice terminal usable by name; at and by follow a slot in some rule but  *)
(* were keywords of Rocq and of ssreflect before this file, measured on       *)
(* 2026-09-19 by binding each in a file that requires nothing but ssreflect.  *)
```

`at` occurs in two rules. In the leaks rule, production `:372`, it follows the
literal `leaks`. In the spectral rule, production `:384`, it follows the
literal `SpectralDecay`. It follows a slot nowhere. The baseline sentence said
so correctly: "at follows a literal too and was a keyword of Rocq before this
file." The rewrite replaces a true statement with a false one, inside the
paragraph whose only job is to record which tokens cost a keyword and why.

It also merges `at` and `by` under one reason and so erases the distinction
the paragraph exists to draw. `at` costs nothing for two independent reasons.
`by` would cost a keyword and does not, only because ssreflect already spends
it.

The supporting count in `STATUS.md` is wrong twice. Line 429 says `by` follows
a slot in **three** existing rules; it is two. Lines 431-433 identify them as
"the slot `t` in the execute rule and the slot `k` in the leaks rule"; in the
execute rule, production `:356`, `by` **precedes** slot `t` and follows the
literal `terminates`. The two rules where `by` follows a slot are the encoded
rule at `:323`, after slot `L`, and the leaks rule at `:372`, after slot `k`.

Replacement for `:67-72`, nine lines, each 80 bytes:

```
(* added beside it. The tokens inputs, terminates, publish, conclude,         *)
(* vm_compute, ExactIndependence and SpectralDecay follow a literal and stay  *)
(* identifiers, which is what keeps the two port constructors and the         *)
(* conclude terminal usable by name; at follows a literal too, in the leaks   *)
(* and the spectral rules, and was a keyword of Rocq before this file. by     *)
(* follows the slot L of the encoded rule and the slot k of the leaks rule,   *)
(* so it would be a twentieth, and it is not one only because ssreflect       *)
(* already spends it, measured on 2026-09-19 by binding it in a file that     *)
(* requires nothing but ssreflect.                                            *)
```

"the reprice terminal" becomes "the conclude terminal" there and at
`PROBE/assumptions_report.v:20`: `conclude` is the terminal's name, `Reprice`
the type of its first argument, and the file names rules by their keyword.

### B3. `PROBE/pgg_tableau.v:163-168` states something the probe refutes

```
(* The names of the claims a row can carry, with no witness and no
   certificate attached to either. A published row's manifest row describes
   the path it ran and stores no theorem, so two rows over one model publish
   the same manifest row; this is the vocabulary in which they differ, and a
   reader asking which of the two claims a finished row carries reads this
   and not the manifest. *)
```

"two rows over one model publish the same manifest row" is false, and the
probe's own `t0_row_uniform_row_neq` proves it false: two rows over
`five_card_uniform_sampled` publish manifest rows that differ in
`apr_transfer`. The sibling comment on `security_claim_of` at `:769-774` gets
it right, "two rows over one model and one pair of statuses are one manifest
row". Two statements of one fact, one of them wrong, in one file.

Replacement, with the rename applied:

```
(* Which of the two arms a row commits to, with the witness and the
   certificate forgotten. A published row's manifest row records the path the
   row ran and no theorem, so two rows over one model and one pair of
   statuses are one manifest row; the arm is where they differ, and a reader
   asking what a finished row proved about a coalition reads this and not the
   manifest. *)
Variant SecurityArm := ExactArm | SpectralArm.
```

### B4. `PROBE/pgg_tableau.v:276-280` gives a false reason

```
(* The claim the data at this level carries, at one real field and one index.
   The port is a function of both, so the claim is read at the same two
   arguments the port is written at rather than at one chosen field; a row
   whose two arguments give two different claims is not expressible, because
   one port function answers for all of them. *)
```

The last clause is false as stated and the reason it gives is the opposite of
the truth. `ab_port q : forall R idx, SecurityPort (amf_sample (ab_f q) R idx)`
is a dependent function whose result type does not mention the constructor, so
one port function can perfectly well return `ExactIndependence` at one index
and `SpectralDecay` at another; when `amf_index` is a two-element type this
needs no classical choice at all. What is actually true, and is the fact worth
stating, is that `certify_exact` and `certify_spectral` each build a port with
one fixed constructor, so a row written through the surface has one arm at
every field and index. The comment attributes to the type a uniformity that
comes from the two statements.

Replacement, with the rename applied:

```
(* The arm the data at this level carries, at one real field and one index.
   The port is a function of both, so the arm is read at the arguments the
   port is written at rather than at one chosen field. The two certify
   statements build a port whose constructor is the same at every field and
   index, so for a row written in the surface the answer does not depend on
   either argument. *)
Definition ab_arm (q : StackAt AnalysisBridged) (R : realType)
    (idx : amf_index (ab_f q) R) : SecurityArm :=
  port_arm (ab_port q R idx).
Arguments ab_arm : clear implicits.
```

### B5. Two comments left saying `conclude` republishes the bound

Change C made the terminal publish an upper bound. Stage A rewrote three
comments and left two, so the landing source now carries both readings.

`PROBE/pgg_tableau.v:447`, in the comment on `TableauAt`:

```
   because a terminal that republishes the bound hands back a record at the
   same level whose proposition is no longer StackProp. *)
```

After C the terminal does not republish the bound; it publishes a chosen
number at least as large. Replacement:

```
   because a terminal that concludes a row at a chosen number hands back a
   record at the same level whose proposition is no longer StackProp. *)
```

`PROBE/pgg_tableau.v:426`, in the comment on `StackProp`:

```
   below, and the family a terminal leaves when it republishes a row.
```

Replacement:

```
   below, and the family a terminal leaves when it concludes a row.
```

See also the vocabulary list in the SHOULD-FIX section: after these two, the
word *republish* has no remaining use and should be spent nowhere.

### B6. `t0_sampled_branch.v` claims a configuration it does not exhibit

Both continuations write `certify ExactIndependence five_card_exact_witness`.
They carry one arm, published at two transfer statuses. The file says
otherwise in two places, and these are the sentences that carry the T0
verdict.

`:74-76`:

```
(** The second continuation from the same name, published at the transfer
    status of a model comparison. Two published rows over one Sampled value
    are what one model carrying two claims looks like. *)
```

`:107-108`:

```
(** The two published rows differ, and differ only where the two claims about
    one model are meant to differ: in what the manifest records of the path. *)
```

A reader of the probe concludes that T0 demonstrated two claims over one
model. It demonstrated two continuations over one model, which is the shape
two claims will need, and two transfer statuses. Say that.

Replacements:

```
(** The second continuation from the same name, published at the transfer
    status of a model comparison. Both continuations certify the exact arm,
    so what this pair shows is that one named Sampled value carries two
    finished rows, which is the shape a second arm will need. *)
```

```
(** The two published rows differ, in the one coordinate their two publish
    statements differ in: what the manifest records of the transfer. *)
```

The file header at `:6-10` needs the same correction. "runs two certify
continuations from it" is true; nothing there should be read as two claims
until stage B supplies a second arm.

### B7. `_raw` beside `_bare`: two name shapes, two unrelated meanings

`PROBE/pgl27_rows.v` now holds, thirty lines apart:

- `pgl27_row_word39_raw` at `:409`, a definition that elaborates and is equal
  to `pgl27_row_word39` by conversion;
- `pgl27_row_word39_bare` at `:429`, a recorded `Fail`;
- `pgl27_row_word39_bare_raw` at `:438`, a second recorded `Fail`.

`_raw` and `_bare` are near-synonyms in English and here denote unrelated
things: one is a second spelling of an accepted program, the other an
ill-typed payload. A reader scanning the names reads them as a pair of
stripped-down variants and learns nothing about which compiles.

`_raw` is also a new word. The tree's word for the form these definitions are
written in is *the bind*: `pgg_tableau_syntax.v:6` says "a program of
pgg_tableau.v is a sequence of binds", and the file's own name for the
operator is `tableau_bind`.

| old | new | reason |
|---|---|---|
| `pgl27_row_word39_raw` | `pgl27_row_word39_bind` | The tree's word for the form; stops colliding in shape with `_bare`, which names a rejection. |
| `pgl27_row_word39_bare_raw` | `pgl27_row_word39_bare_bind` | Same, and now reads as the bare payload attempted through the bind. |

`pgl27_row_word39E` keeps its name. It is an equation whose left side has
`pgl27_row_word39` as head symbol, which is what `E` marks, and
`dealt_params_stepE` is the tree's precedent for an `E` between two spellings
of one term.

---

## 2. The pins

Six pins, all in the form

```coq
Check (fun R idx =>
  (erefl : security_claim_of pgl27_row_exact_tableau R idx
           = ExactViewIndependence)).
```

Against the manifest's idiom and the rows files' idiom:

- The manifest writes `Timeout 60 Check (erefl : ...)`
  (`manifest/pgg_analysis_manifest.v:1779` and 209 siblings), and where a pin
  needs binders it spells their types:
  `Timeout 60 Check (fun (R : realType) (p : R.-fdist bool) => ...)` at
  `:1837` and `:1840`. The probe's `fun R idx =>` leaves both types to
  inference, so a later change to the arity or the implicit status of the
  reader re-elaborates `R` silently instead of failing. The `Timeout 60` is
  dropped too.
- The four rows files contain no `erefl` pin at all. Their idiom for a
  conversion fact about a published row is a named lemma:
  `pgl27_row_exact_rowE`, `pgl27_row_word_rowE`, `five_card_row_uniform_rowE`,
  `s5_row_rand_rowE`, `psl211_row_alldecks_rowE`, `pgl27_inline_paramsE`, each
  `Proof. by []. Qed.` The six pins are placed immediately beside those
  lemmas, in the same section, in a different form.

Three consequences of leaving them as `Check`s. A `Check` puts nothing in the
environment, so the manifest, the facade and the paper cannot cite the fact
that a given row carries a given arm, which is the one thing the reader was
added for. `Print Assumptions` cannot reach a `Check`, which is why
`assumptions_report.v` lists the three readers and none of the six pins.
And a `Check` that stops holding is a failed compile with no name attached.

**One convention: a named lemma, `_armE`, beside the row's `_rowE`.**

| file | name | statement |
|---|---|---|
| `pgl27_rows.v` | `pgl27_row_exact_armE` | `security_arm_of pgl27_row_exact_tableau R idx = ExactArm` |
| `pgl27_rows.v` | `pgl27_row_word_armE` | `... pgl27_row_word_tableau ... = SpectralArm` |
| `pgl27_rows.v` | `pgl27_row_word39_armE` | `... pgl27_row_word39 ... = SpectralArm` |
| `five_card_rows.v` | `five_card_row_uniform_armE` | `... five_card_row_uniform_tableau ... = ExactArm` |
| `s5_rows.v` | `s5_row_rand_armE` | `... s5_row_rand_tableau ... = ExactArm` |
| `psl211_rows.v` | `psl211_row_alldecks_armE` | `... psl211_row_alldecks_tableau ... = ExactArm` |

Shape, matching the `Fail` in the same file which already spells the index
type:

```coq
Lemma pgl27_row_word_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_word_tableau)) R) :
  security_arm_of pgl27_row_word_tableau R idx = SpectralArm.
Proof. by []. Qed.
```

`E` is the tree's suffix for an equation and `_armE` reads beside `_rowE` as
the second thing read off the same finished row. If the author declines named
lemmas, the fallback is the manifest's exact form, `Timeout 60 Check` with
both binder types written out; the bare `Check (fun R idx => ...)` is neither
convention.

---

## 3. Statement comments: the remaining findings

Blocking ones are B3, B4, B5, B6 above. The rest:

**S1. `PROBE/pgg_tableau.v:171-173`, `port_claim`.** States the fact, states
no position: nothing about which phase, which row, or which observer. Also
"decided by conversion at every program that writes one" is about how a pin
closes rather than about the definition.

```
(* The arm a port commits to, with its witness or its certificate forgotten.
   The constructor alone decides the answer, so a row's arm is fixed by the
   certify statement that wrote the port and needs no proof about the model. *)
```

**S2. `PROBE/pgg_tableau.v:646-651`, `RepricePayload`.** "the number a
spectral port is republished at" carries the word C retired, and "a number the
row's own certificate does not reach" is vague where the statement is exact.

```
(* The obligation of conclude: at every real field and index, the number a
   spectral port is concluded at is at least that port's own, and nothing for
   an exact port. A row may therefore publish the constant a paper cites
   whenever that constant is an upper bound of the distance the row proved,
   and may not publish a number below the one its certificate proved. The
   exact arm carries no number, so a reprice leaves it untouched. *)
```

**S3. `PROBE/pgg_tableau.v:680-683`, `conclude`.** "The terminal publishing a
row's accumulated bound as an upper bound of it" does not parse to anything:
the terminal publishes a chosen number that is an upper bound of the
accumulated bound, not the accumulated bound as an upper bound of itself.

```
(* The terminal concluding a row at a chosen number, against a proof that the
   number is at least the row's accumulated bound. Post-processing of the
   published constant rather than a step: the data and the arms are
   unchanged, only the real the spectral arm's proposition mentions moves,
   and it moves only upward. *)
```

**S4. `PROBE/pgg_tableau.v:660-661`, `port_reprice`.** "A port's proposition
at the program's own bound, together with an upper bound of that bound, is the
port's proposition at the upper bound." The second hypothesis is a proof that
the number is an upper bound, not a number. Write: "A port's proposition at
the program's own bound, and a proof that a chosen number is at least that
bound, give the port's proposition at the chosen number."

**S5. Positional pointers in text stage A added.** The rule is that a comment
names the declaration it means.

- `PROBE/pgl27_rows.v:398`: "asserts about a coalition no more than the row
  above" -> "no more than `pgl27_row_word_tableau`".
- `PROBE/pgl27_rows.v:408`: "as the five spectral clauses do not for the line
  above them" -> "as the five spectral clauses do not for the certify
  statement".
- `PROBE/pgg_tableau_syntax.v:395`: "written in the same surface as the
  statements above it" -> "written in the same surface as the statements of a
  row".

Replacement for `PROBE/pgl27_rows.v:406-408`:

```
(** The same row written through the bind and its payloads. The two are one
    term, so the conclude and publish surface adds no step and hides no
    payload, as the five spectral clauses do not for the certify statement. *)
```

**S6. `PROBE/pgl27_rows.v:343`, "The reader discriminates."** A bare
meta-sentence with no mathematical content. Replacement:

```
(** Pinning the word row at the exact arm is rejected by conversion, so a pin
    records the arm the row's certify statement wrote and no other. *)
```

**S7. One word per concept: `reprice`, `republish`, `publish`, `conclude`.**
After change C the file holds four words for two operations. Inventory:

| word | where | keep? |
|---|---|---|
| `conclude` | the declaration; index `:65`; new comments | keep, as the name of the terminal and of its effect |
| `reprice` | `Reprice`, `no_reprice`, `RepricePayload`, `port_reprice`, `pgl27_reprice39`, `pgl27_reprice41`, and the prose "a reprice leaves it untouched" `:651`, "the reprice obligation" `pgl27_rows:425`, "computed by the framework from the reprice" `:713` | keep, and only for the chosen number itself, never for the operation |
| `republish` | `:426`, `:447`, `:647`; `pgl27_rows:54`, `:387` | spend nowhere. After B5 and S2 the three framework uses are gone; the two in `pgl27_rows.v` are below |
| "published at 2^-39" | `pgl27_rows:394` | `publish` is the name of the last statement, which attaches the manifest row. Where `conclude`'s argument is meant, write "concluded at" |
| `restate` | the other terminal | keep, a different operation |

Carriers in `PROBE/pgl27_rows.v`:

- `:387` section heading: `(*     The word row republished at 2^-39 ... *)` ->
  `(*     The word row concluded at 2^-39                                     *)`
- `:54` index: `pgl27_row_word39 == the word row republished at that name` ->
  `pgl27_row_word39 == the word row concluded at that number`
- `:39` header: "the reprice of the word row's bound from 2^-40 + 2^-40 to
  2^-39, which moves a number and proves nothing new about a coalition" stays
  true and stays as it is.
- `:394` body: "The word row published at the single constant 2^-39" -> "The
  word row concluded at the single constant 2^-39".

**S8. One word per concept: `arm` against `claim` in the four rows copies.**
Covered by the B1 rename. Every one of the four new pin comments opens "The
claim this row carries" and becomes "The arm this row carries". The three
instance readings in those comments are correct against their files' own
vocabulary and stay as they are: "the conjunction of the committed bits" for
five-card, which the file calls "the conjunction"; "the tape secret" for S5;
"the chirality" for PSL(2,11).

**S9. `PROBE/pgl27_rows.v:452-455`, `pgl27_word_reprice41_false`.** The fact
and its position are both there and the phrasing is type-honest. One word:
"publishing a smaller number beside it" -> "publishing a number the
certificate does not prove". The name keeps `_false`: the tree has
`kim_cdiv1_false` at `instances/kim2025/kim_input_privacy.v:625` and
`indep_adj_swap_false` at `groups/pgg_raag.v:1666`, and the sibling
refutations `psl211_perdeck_law_neq`, `psl211_dealer_view_indep_of_deck_unsat`
and `psl211_fixed_deal_view_dep` are the same idiom. `~~ P` for a boolean `P`
is exactly "`P` is false", so the suffix is honest.

**S10. `PROBE/pgl27_rows.v:465`, the recorded `Fail pgl27_row_word41`.**
Correct by the tree's convention: named after what is attempted, with no
marker saying it fails. `pgl27_reprice41` beside `pgl27_reprice39` is correct
too. No change.

---

## 4. Header sentences and the index

Eight sentences are listed in `STATUS.md`. Each was read against the file it
sits in.

| where | true? | reads as part of the header? |
|---|---|---|
| `pgg_tableau.v:28-30` | yes | yes. The header names `dealt_step`, `conclude`, `exact_tail` and library lemmas in prose, so naming the reader is in style. Rename to `security_arm_of`. |
| `pgg_tableau.v:45-46` | yes | yes |
| `pgg_tableau.v:52-53` index, two lines added | yes | yes, but see the gloss below |
| `pgg_tableau.v:63-64` index, `stack_claim` | yes | **out of file order**, see below |
| `pgg_tableau.v:65-66` index, `conclude` | yes | yes |
| `pgg_tableau.v:75-76` index, `security_claim_of` | yes | yes |
| `pgg_tableau.v:82-83` index, `port_reprice` | yes | yes. "at an upper bound of its own" is elliptical; "at an upper bound of its own bound" does not fit in 80 bytes, so "at a number above its own bound" is the fix if one is wanted. |
| `pgg_tableau_syntax.v:36-37` | yes | yes |
| `pgg_tableau_syntax.v:67-72` | **no** | B2 |

`:17` "There are five statements." stays true: stage A adds no statement.
`:40` "Two things stay outside the program." stays true. All 84 header lines
are exactly 80 bytes and the index format is intact.

**Index completeness, `pgg_tableau.v`.** Every one of the 28 entries resolves
to a declaration of the file; nothing is listed that is absent. Every new name
is present. The two constructors are unlisted, which matches
`ExactIndependence` and `SpectralDecay` being unlisted.

**Index order.** The index is in file order, with one 13-line pre-existing
inversion (`publish` at 737 listed before `PublishedRowAt` at 724). The new
`stack_claim` line breaks that: it is listed at header `:63`, between
`certify_spectral` (declared at 631) and `conclude` (declared at 684), while
`stack_claim` is declared at 281. A 350-line jump backwards.

The cleaner fix, once the name becomes `ab_arm`: **remove the index line**.
The index lists no level accessor at all, not `ab_port`, not `ab_f`, not
`sp_f`, and `ab_arm` is one of them. `SecurityArm`, `port_arm` and
`security_arm_of` remain indexed, which is what a reader needs. If the line is
kept instead, it belongs between `StackAt` and `StackProp`.

**Gloss of `SecurityClaim`.** "the name of a claim, with no witness attached"
is circular and drops the certificate, which the body comment mentions. With
the rename, and at 80 bytes:

```
(*   SecurityArm            == which arm, with no witness or certificate      *)
(*   port_arm               == the arm a port commits to                      *)
...
(*   security_arm_of        == which of the two arms a published row carries  *)
```

**Index completeness, `pgl27_rows.v`.** Four declarations stage A added to the
copy are absent from its Definitions and Key results index at `:44-70`:
`pgl27_row_word39_bind` (now `_raw`), `pgl27_row_word39E`, `pgl27_reprice41`,
`pgl27_word_reprice41_false`. `STATUS.md` D2 anticipates this for a landing;
the copy is the landing source, so it should carry them now. Suggested lines,
in file order, after `pgl27_row_word39`:

```
(*   pgl27_row_word39_bind   == the same row written through the bind        *)
(*   pgl27_reprice41         == the name 2^-41 for a bound                   *)
```

and, under Key results:

```
(*   pgl27_row_word39E       == the surface and the bind build one term      *)
(*   pgl27_word_reprice41_false                                              *)
(*                           == the terminal's obligation at 2^-41 is false  *)
```

**The `by` paragraph, verified against production.** `by` occurs in five
notation rules of `manifest/pgg_tableau_syntax.v`. It follows a **slot** in
two of them: `:323`, after slot `L` of the encoded rule, and `:372`, after
slot `k` of the leaks rule. In the other three it follows a literal:
`terminates`, `endpoints` and `recon` at `:356` and `:361`, and `tied`,
`mixing` and `invariant` at `:384`. So the gap the probe reports is real, `by`
was already a slot-following token and the header never said so, but the count
is two and the identification in `STATUS.md` is wrong. See B2.

---

## 5. Probe-only idiom inside the six copies

None. A scan of the six copies for `probe`, `mutation`, `stage A`, `ledger`,
the ledger IDs `T0`, `C1`, `C2`, `C3`, `K1`, `G1`, `G2`, `G3`, `D1`, `D2`, and
for dates, returns five lines, all of them permanent text:

- `pgg_tableau_syntax.v:36`, `:64`: "Measured on 2026-09-14", both baseline.
- `pgg_tableau_syntax.v:71-72`: "measured on 2026-09-19 by binding each in a
  file that requires nothing but ssreflect". A dated measurement in a
  paragraph whose two other sentences are dated measurements; this is the
  file's own convention and should stay, with the sentence corrected per B2.
- `psl211_rows.v:53`: a path under `notes/probes/2026-09-15-psl211-planb/`,
  baseline.

The three probe-only files keep their ledger prefixes, which is correct there.

**Landing names for the `t0_` declarations.** `t0_` is a ledger ID and does not
travel. `five_card_uniform_sampled` is already domain-worded and matches
`five_card_committed`, `five_card_uniform_family`,
`five_card_row_uniform_tableau`; keep it. The rest:

| probe | landing | reason |
|---|---|---|
| `t0_row_uniform` | `five_card_row_uniform_tableau` | It is that row, reached from the named branch point; a landing replaces the unbranched definition rather than adding a twin. |
| `t0_row_uniform_transfer` | `five_card_row_uniform_ideal_tableau` | Named for what it publishes, `IdealFinite`, until stage B gives it its own arm; then rename for the arm, not for the status. |
| `t0_row_uniform_rowE` | `five_card_row_uniform_branch_rowE` | Keeps `_rowE`, says which of the two programs it identifies. |
| `t0_row_uniform_manifestE` | `five_card_row_uniform_branch_manifestE` | Same. |
| `t0_row_uniform_atE` | `five_card_row_uniform_branch_atE` | Same. |
| `t0_row_uniform_row_neq` | `five_card_row_uniform_transfer_neq` | `_neq` is the tree's suffix for a proved difference, as in `psl211_perdeck_law_neq`; and the difference is the transfer, which the name should say. |
| `t0_s5_sampled` | `s5_rand_sampled` | Matches `s5_rand_family`, `s5_row_rand_tableau`. |
| `t0_cross_instance` | `s5_sampled_takes_no_five_card_witness` | A recorded `Fail` named after what is attempted. |
| `t0_cross_instance_back` | `five_card_sampled_takes_no_s5_witness` | Same. |

---

## 6. Collisions

Whole-word scan with Python `re` and `\b`, over every `.v` file under `lib`,
`protocol`, `groups`, `security`, `smc`, `reconstruct`, `manifest`,
`instances`, `legacy`, every other directory under `notes/probes`, and
`~/Projects/coq/_opam/lib/coq/user-contrib`. `grep -E '[[:<:]]'` was not used.

| identifier | hits outside the probe |
|---|---|
| `SecurityClaim` | 0 |
| `ExactViewIndependence` | 0 |
| `SpectralViewDecay` | 0 |
| `port_claim` | 0 |
| `stack_claim` | 0 |
| `security_claim_of` | 0 |
| `pgl27_row_word39_raw`, `pgl27_row_word39E`, `pgl27_reprice41`, `pgl27_word_reprice41_false`, `pgl27_row_word41`, `pgl27_row_word39_bare_raw`, `pgl27_word_claim_is_not_exact` | 0 each |
| every `t0_*` name, `five_card_uniform_sampled`, `conclude_stays_bindable` | 0 each |
| `eqW` | 16, all in infotheo: `lib/ssr_ext.v:1224` is the declaration, the rest are uses in `information_theory/`. The probe writes `ssr_ext.eqW` qualified, so nothing is shadowed and nothing is guessed. |

The renamed forms were checked too: `SecurityArm`, `ExactArm`, `SpectralArm`,
`port_arm`, `ab_arm`, `security_arm_of` have no hit outside the probe either,
so the rename table introduces no collision. `pgl27_row_word_arm_exactE` does
not collide with the existing `pgl27_word_arm_is_not_exact`.

---

## 7. Banned vocabulary

Zero hits, case-insensitive whole-word, over every `.v` and `.md` file of the
probe directory outside `history/`, for: the word for a highest point in a
tree, the metaphor for a logical restriction and its four inflections, the
verb for assuming without proof and its three inflections, and the banned
two-character token for the sum of absolute differences.

Line widths: three lines over 80 bytes, at `PROBE/pgg_tableau_syntax.v:325`,
`:363` and `:386`, all three inherited notation rules from production `:323`,
`:361` and `:384`. Stage A's own text adds none. The 84 header lines of
`PROBE/pgg_tableau.v` are all exactly 80.
