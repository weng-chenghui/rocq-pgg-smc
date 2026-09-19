# Third audit of stage A, soundness and naming together

**NO-GO.** Two records in `STATUS.md` would be executed wrongly by a landing:
the G3 table still prescribes `port_reprice` as the name to write into
production while the copy carries `port_conclude` and the D2 table for
`manifest/pgg_tableau.v` records no rename at all, and the D2 table for
`instances/pgl27/pgl27_rows.v` directs a landing to add an index line for
`pgl27_row_word39E`, a name fix pass 2 retired. Both are the shape this
campaign keeps producing: a fix pass corrected the `.v` file and left the
note's account of it behind.

Everything else clears. Every sentence fix pass 2 wrote into the ten `.v`
files is true, including the two cross-model comments, which I checked by
compiling the mutations without `Fail` rather than by reading the recorded
messages. The renames are consistent with the tree's precedents, the two T0
files are parallel where the instances allow, no `.v` line exceeds 80 bytes
outside the three inherited notation lines, and no barred word appears in any
identifier, comment or line of `STATUS.md`. Stage B may build on this copy of
the Tableau once the two records are corrected.

Third-round auditor, independent of stage A, of fix passes 1 and 2, and of the
two earlier audit rounds.

---

## Findings

| ID | Severity | Quoted content | Evidence | Replacement |
|---|---|---|---|---|
| **A1** | **BLOCKING** | `STATUS.md` G3 table, row `` `:74` ``: "`port_reprice == a port's proposition at a renamed bound` \| false: at an upper bound \| `port_reprice == a port's proposition at a number above its own bound`" | The copy's own index line, `pgg_tableau.v:81`, reads "(*   port_conclude          == a port's proposition at a number above its own *)". E2 decided the rename and measured its cost. The D2 table for `manifest/pgg_tableau.v` (`:556-567`) lists `:614`, `:628`, `:631` as relation and proof edits and `` `:50`, `:60`, `:63`, `:68`, `:74` `` as "four lines added, two rewritten", with no rename row anywhere. A landing built from those two tables lands `port_reprice` beside a declaration the same landing renames. | Below, A1 |
| **A2** | **BLOCKING** | `STATUS.md` D2, `instances/pgl27/pgl27_rows.v` row `` `:53-54` ``: "index lines added for `pgl27_row_word39_bind`, `pgl27_reprice41`, the three `_armE` lemmas, `pgl27_row_word39E` and `pgl27_word_reprice41_false` if C3 and K1 land here" | The lemma is `pgl27_row_word39_bindE` (`pgl27_rows.v:434`) and the copy's own index line, `pgl27_rows.v:84`, already reads "(*   pgl27_row_word39_bindE  == the surface and the bind build one term       *)". E6 lists `pgl27_row_word39E` among names that no longer exist, so E6's own claim survives, but this row is a forward instruction written in the dead name. A landing executing it writes an index line for a lemma that is not there, and nothing compiles an index line. | `pgl27_row_word39E` becomes `pgl27_row_word39_bindE` in that cell |
| **A3** | SHOULD | `STATUS.md` step 2: "and on a goal whose two sides are `published_at` of a row without `conclude` and of a row with it that search does not return" | The table three lines above, in the same section, records "did not return in 130 s" and "did not return in 200 s". Round 2's N12 ruled this wording out and fix pass 2 applied the correction to `t0_sampled_branch_pgl27.v:97-103` only. E4 states the correction and names only the `.v` file. The note that supplies the bounds now asserts more than the bounds. | Below, A3 |
| **A4** | SHOULD | `STATUS.md` D9: "now names `conclude`'s payload as the second entry and says what it carries: an inequality between the number the row's own certificate proved and the number the row publishes" | The header at `pgg_tableau.v:41-45` now reads "which for a spectral port is an inequality between the number the row's own certificate proved and the number the row publishes and for an exact port is nothing". D9 reproduces the unqualified formulation that round 2's S8 flagged, as its account of the fixed file. Graded SHOULD because round 2 graded the identical wording in the `.v` file SHOULD. | Below, A4 |
| **A5** | SHOULD | `pgg_tableau.v:656`: "The exact arm carries no number, so a reprice leaves it untouched." | E2 retires *reprice* as a word for the operation and keeps it only for the number: "`Reprice`, `no_reprice`, `pgl27_reprice39` and `pgl27_reprice41` keep their names, since each names the number a row is concluded at". This sentence is text the probe wrote, the baseline read "so renaming a bound leaves it untouched", and it uses the retired operation noun inside the comment of the declaration fix pass 2 renamed away from it. | Below, A5 |
| **A6** | SHOULD | `STATUS.md` D10/D11: "`notes/probes/2026-09-19-kim-spectral-landing/five_card_rows.v`, at `:745` and `:788`, with a recorded `Fail` at `:751-757`" | Measured in that file today: the two `conclude` equality payloads are at `:755` and `:798`, the two rows are declared at `:751` and `:793`, and `Fail Definition five_card_row_repeated39_bare` occupies `:761-767`. That file's mtime is 13:51, after this note's 13:42, so the numbers drifted under another agent. The two arm-probe citations `` `:288` `` and `` `:365` `` and the citation `pgl27_rows.v:382` are still exact. E5's own reason for dropping line numbers from the verdict table applies here and was not applied. | Below, A6 |
| **A7** | SHOULD | `STATUS.md` D1: "What a new arm costs, so that stage B can price it: a constructor in `SecurityPort`, a constructor in `SecurityArm`, a branch in `port_arm`, a branch in `PortProp`, a branch in `ConcludePayload` and a case in `port_conclude`." | Each of the six is real, and I confirmed the five code sites at `pgg_tableau.v:163`, `:181`, `:410`, `:663`, `:680` with the proof's `case: p => [w\|cert]` at `:685`. But the spec's stage B also needs a certificate record, a proposition, a payload type, a `certify` statement, a composition law ending in `Qed`, a fifth general `_armE` lemma and one `certify` rule in `pgg_tableau_syntax.v`, none of which the six cover. A stage B planner pricing from this paragraph under-scopes by the whole of P2. | Below, A7 |
| **A8** | SHOULD | `t0_sampled_branch.v:109-116`, one `and3` where the sibling file has two lemmas | `t0_sampled_branch_pgl27.v` states the same content as `pgl27_row_exact_branch_atE` and `pgl27_row_exact_branch_ideal_atE`. Stage B's second continuation goes through a different arm, so its `published_at` will not equal its sibling's and only the first conjunct survives. With the `and3` stage B cannot reuse the shape without a `case`. | Below, A8 |
| **A9** | SHOULD, landing item | `t0_sampled_branch_pgl27.v:115-117` and `:161-163`, the two `_atE` statements whose named subject is on the right | Zero `_atE` lemmas exist in production, so the governing rule is the tree's `E` rule. Every production `E` lemma puts its name's subject on the left: the five `_rowE` of shape A, `pgl27_row_word_certE`, the two `_prefixE`, and the whole `<subject>_<coordinate>E` family (`five_card_row_repeated_modelE`, `s5_dealt_row_observedE`, `pgl27_inline_paramsE` and the rest). Three of the probe's five `_atE` follow it and two do not. | Below, A9 |
| **A10** | SHOULD | `STATUS.md` G1 compile table | The table's columns are "baseline", "after C", "after K", which are historical by construction, but nothing in the G1 section points forward to E7 and nothing in E7 says it supersedes G1. G1 also lacks `t0_sampled_branch_pgl27.v`, which did not exist when it was measured. | Below, A10 |
| **A11** | SHOULD | The sentences stage B makes false, true today | Eleven sites, listed in full under question 5 below. Each is a correct statement about a two-arm Tableau. | Listed under question 5 |
| **A12** | SHOULD | `t0_sampled_branch_pgl27.v` has no counterpart to `five_card_row_uniform_branch_transfer_neq` | Its two exact continuations publish `StaticExecutedOnly` and `IdealFinite`, the same pair the five-card file separates, so the instance allows the lemma. Its absence is the one gap in the two files' parallelism that the instances do not explain. | A `pgl27_row_exact_branch_transfer_neq` of the same shape, or a sentence in this note saying the pair is recorded once and not twice |
| **N1** | NOTE | `STATUS.md` C2: "`conclude` occurs in exactly one production file." | `conclude` is declared in `manifest/pgg_tableau.v:638` and used in `instances/pgl27/pgl27_rows.v`, so it occurs in two, plus an English-word hit in `legacy/reconstruct/ag_code.v:163` and a second at `security/pgg_mixing.v:304` which D10 already records. The next sentence disambiguates. | "`conclude` is used in exactly one production file outside the framework." |
| **N2** | NOTE | `STATUS.md` E6: "Every back-quoted name in this note that is not one of these exists as a whole word in a `.v` file of the probe or of production, checked mechanically." | I re-ran the check in Python over 207 production and 38 probe `.v` files. Three back-quoted Rocq-looking names are neither in a `.v` file nor in the retired table: `SecurityClaim`, `ExactViewIndependence`, `SpectralViewDecay`, all in the D1 rename table where they are plainly labelled as the old names. Three more, `IdealProximityArm`, `LeakageCeilingArm` and `DependenceArm`, are names D1 proposes for later stages. The rest of the misses are suffix fragments (`_bare`, `_bind`, `_raw`, `_rowE`, `_false`, `Arm`), the Rocq command `Abort`, the Python constant `RUSAGE_CHILDREN`, the file name `_CoqProject` and the search fragments `word39` and `reprice39`. | Add a "before fix pass 1" row for the three tag names and a "proposed for later stages" row for the three arm names, or narrow E6's claim to names the note asserts exist |
| **N3** | NOTE | `STATUS.md` E2: "its prose mentions `RepricePayload` twice in `audit-2.md` and `RepricePayload` twice with `port_reprice` twice in `soundness-audit.md`" | Exact when written and stale now: `audit-2.md` holds 2, `soundness-audit.md` holds 2 and 2, and since fix pass 2 that probe gained `audit-3.md` with 6 and a `STATUS.md` with 1. E2's operative claim, that no `.v` file outside `manifest/pgg_tableau.v` holds either carrier, is exact: I counted `RepricePayload` 3 at `:610`, `:616`, `:639` and `port_reprice` 4 at `:74`, `:622`, `:632`, `:643`. | Drop the per-file prose counts and keep the `.v` sentence |
| **N4** | NOTE | `pgg_tableau.v:394-396`: "A bound named once per real field, with None meaning the program's own sum.\n   single real will not serve, because the security port quantifies over the" | The missing "A" is production's, byte-identical at `manifest/pgg_tableau.v:350-352` and in `history/pgg_tableau.v.0-baseline`. Not the probe's defect, and a landing item. | "A single real will not serve, because the security port quantifies over" |
| **N5** | NOTE | `pgg_tableau.v:722-724`, `restate`: "conclude's target is computed by the framework from the reprice"; `pgl27_rows.v:39-40`: "the reprice of the word row's bound from 2^-40 + 2^-40 to 2^-39" | Both are baseline text the probe did not rewrite. The second is already in D10's seed list as `instances/pgl27/pgl27_rows.v:39-41`. The first uses "the reprice" for the `Reprice` argument, which E2 allows. | None owed by this probe |
| **N6** | NOTE | `pgg_tableau.v:781-784`: "and publish_armE is why the publish statement does not change the answer" | The mathematical reason is that `published_at (publish a q pf t)` is `q` by conversion. Naming the lemma is what round 2's N5 and N6 asked for, and the statement-comment rule's survival test pulls the other way. Round 2's ruling stands. | None |
| **N7** | NOTE | `t0_sampled_branch.v:99-102`: "following t0_sampled_branch_pgl27.v" | That file compiles after this one in the probe's `_CoqProject` and this file does not Require it, so the pointer is forward. The content it points at is correct. | "following the measurements under the T0 step of STATUS.md" |
| **N8** | NOTE | Round-2 soundness N1, "`conclude` cannot be applied twice and nothing says so" | Zero hits for "twice", "iterated" or "cannot be applied" in `STATUS.md`, and `conclude`'s comment at `pgg_tableau.v:690-694` does not state it. The item carried no proposed replacement, so nothing was owed, but section 9 of that report leans on the property. | One clause in `conclude`'s comment, or a line in the fix-pass-2 section saying the item was seen and nothing was owed |

### A1, replacement

G3 table, the `` `:74` `` row:

```
| `:74` | `port_reprice == a port's proposition at a renamed bound` | false: at an upper bound, and the name is the operation `conclude` owns | `port_conclude == a port's proposition at a number above its own bound` |
```

and a new row in the D2 table for `manifest/pgg_tableau.v`, after the `:631`
row:

```
| `:74`, `:610`, `:616`, `:639`, `:622`, `:632`, `:643` | `RepricePayload` (3 occurrences) and `port_reprice` (4) | renamed `ConcludePayload` and `port_conclude`, by E2; no other production file holds either name |
```

Every line number in that row is measured in `manifest/pgg_tableau.v` today.

### A3, replacement

`STATUS.md` step 2, the sentence beginning "ssreflect's `done`":

```
ssreflect's `done`
spends its search before it reaches reflexivity, and on a goal whose two sides
are `published_at` of a row without `conclude` and of a row with it that
search did not return inside the bounds in the table above, 130 s for the
equation and 200 s for the conjunction. The conversion the goal actually
needs is a tenth of a second.
```

Both numbers are the table's own.

### A4, replacement

`STATUS.md` D9, first sentence:

```
The paragraph of `pgg_tableau.v` that said an instance's mathematics enters
only through a certify payload now names `conclude`'s payload as the second
entry and says what it carries at each arm: at a spectral port an inequality
between the number the row's own certificate proved and the number the row
publishes, and at an exact port nothing.
```

### A5, replacement

`pgg_tableau.v:656-659`, the last four lines of the `ConcludePayload` comment,
each measured at or below 80 bytes:

```
   exact arm carries no number, so concluding a row leaves it untouched. An
   upper bound is the right obligation because the spectral arm's proposition
   is monotone in its number; an arm whose proposition is not monotone in the
   number it carries owes a different obligation here. *)
```

75, 77, 77 and 56 bytes.

### A6, replacement

`STATUS.md` D10/D11, the paragraph beginning "The same two rows stand":

```
The same two rows stand in the probe that would carry them to production,
`notes/probes/2026-09-19-kim-spectral-landing/five_card_rows.v`. They are
`five_card_row_repeated39` and `five_card_row_biased_inv25`, each with an
equality payload under its `conclude` line, with the recorded `Fail`
`five_card_row_repeated39_bare` between them and a third equality payload in
that directory's `pgl27_rows.v`, under `pgl27_row_word39`. That `Fail` is the
same shape and the same defect stage A renamed `pgl27_row_word39_unindexed`
for, so the two probes owe one word between them. A Kim landing edits that
copy and not the arm probe, so the landing's own status note owes the four
sites. The four are named and not numbered because that file is another
probe's and its line numbers moved once already under this note.
```

All five names verified in that file today.

### A7, replacement

`STATUS.md` D1, the cost paragraph:

```
What a new arm costs in the arm plumbing, so that stage B can price that
part: a constructor in `SecurityPort`, a constructor in `SecurityArm`, a
branch in `port_arm`, a branch in `PortProp`, a branch in `ConcludePayload`
and a case in `port_conclude`, whose proof splits on the port. Beside the
plumbing the arm owes its own mathematics and its own surface: a certificate
record, the arm's proposition, a payload type, a `certify` statement, a
composition law ending in `Qed`, a fifth general `_armE` lemma, one `certify`
rule in `pgg_tableau_syntax.v` with the keyword measurement repeated for each
new word, one index line in the header of `pgg_tableau.v` per new name, and
the sentences of G3 that count the arms and the statements. `SecurityArm` is
a second variant and not a projection of the first because `SecurityPort` is
indexed by the real field, the algebra, the run parameters and the sample
adapter, and a tag the manifest's table prints must be closed in none of
them.
```

### A8, replacement

`t0_sampled_branch.v:109-116` becomes the sibling file's pair. The comment at
`:104-108` stays on the first and its last clause moves to the second:

```
Lemma five_card_row_uniform_branch_atE :
  published_at five_card_row_uniform_branch
  = published_at five_card_row_uniform_tableau.
Proof. exact: erefl. Qed.

(** The second continuation holds that same coordinate, so the two finished
    rows of this branch point differ in their manifest row alone, and naming
    the Sampled value costs the row nothing it would otherwise have. *)
Lemma five_card_row_uniform_branch_ideal_atE :
  published_at five_card_row_uniform_branch_ideal
  = published_at five_card_row_uniform_branch.
Proof. exact: erefl. Qed.
```

The header index gains one 80-byte pair and `assumptions_report.v` one
`Print Assumptions` line, which takes the report from thirty blocks to
thirty-one.

### A9, replacement

Two statements, at the landing or at the start of stage B:

```
Lemma pgl27_row_exact_branch_ideal_atE :
  published_at pgl27_row_exact_branch_ideal
  = published_at pgl27_row_exact_branch.
Proof. exact: erefl. Qed.
```

```
Lemma pgl27_row_word_branch39_atE :
  published_at pgl27_row_word_branch39
  = published_at pgl27_row_word_branch.
Proof. exact: erefl. Qed.
```

Both comments above them are direction-neutral and survive the swap
unchanged. Not blocking: the names identify their subject unambiguously and
stage B writes its own `_atE` lemmas at the five-card instance rather than
reusing these. The fix pass's reason for declining, that a comment and index
pass may not change a statement, is a sound scoping reason and I do not
overturn it.

### A10, replacement

One sentence at the head of the G1 section:

```
These are the measurements taken at the baseline, after C and after K. The
numbers for the ten files as they stand are in E7, below; this table is kept
for the three-point comparison and not as the current state.
```

---

## 1. Everything fix pass 2 wrote, sentence against statement

**The two cross-model comments: both true, checked by compiling.** I wrote
`audit-3/a3_m1.v` and `audit-3/a3_m3.v`, each the mutation with `Fail`
removed, and compiled them through the shared lock against the production
`_CoqProject` flags plus `-Q <probe dir> tableau_ext_probe`. `rocq compile` is
silent on a passing `Fail`, so reading the messages needs the un-`Fail`ed
form.

At the five-card and S5 instance, `rc=1`:

```
The term "five_card_exact_witness" has type
 "forall (R : realType) (idx : unit),
  ExactWitness (amf_sample five_card_uniform_family R idx)"
while it is expected to have type "ExactPayload (tableau_at s5_rand_sampled)"
(cannot unify "ExactWitness (amf_sample five_card_uniform_family R idx)" and
"ExactWitness (amf_sample (sp_f (tableau_at s5_rand_sampled)) R idx)").
```

The two compared types are the two sample adapters, so
`t0_sampled_branch.v:135-138`, "the two families carry the same index type, so
the sample adapter the witness is stated over and the one the branch point
reached are compared where the clause is written", is true. The index premise
is true at the definitions as well: `five_card_uniform_family`
(`instances/kim2025/five_card_models.v`) and `s5_rand_family`
(`instances/s5/s5_models.v`) are both `@MkAnalysisModelFamily _ (fun _ => unit)`.

At PGL(2,7), `rc=1`:

```
The term "pgl27_exact_witness" has type
 "forall (R : realType) (idx : unit),
  ExactWitness (amf_sample pgl27_exact_family R idx)"
while it is expected to have type
 "ExactPayload (tableau_at pgl27_word_sampled)"
(cannot unify "amf_index (sp_f (tableau_at pgl27_word_sampled)) R" and
"unit").
```

The comparison is between index types and no adapter is reached, so
`t0_sampled_branch_pgl27.v:177-184`, "the clause is checked first against the
index type that coordinate's family carries, unit against a distribution on
the booleans, and the two sample adapters are never reached", is true, and so
is the consequence it draws, "separated by their index types alone, so an
ideal family and an actual family that share one index will need a different
mutation". The definitions agree: `pgl27_exact_family` is
`(fun _ => unit)`-indexed and `pgl27_word_family` is
`(fun R => R.-fdist bool)`-indexed, both in `instances/pgl27/pgl27_models.v`.
E3's quoted messages match mine word for word.

**The rewritten header sentences on `conclude`'s payload: true.**
`pgg_tableau.v:41-45` now reads "the payload of conclude, which for a spectral
port is an inequality between the number the row's own certificate proved and
the number the row publishes and for an exact port is nothing". Read against
`ConcludePayload` at `:660-665`, the spectral branch is
`cert_eps cert <= odflt (cert_eps cert) (c R)` and the exact branch is `unit`.
`odflt (cert_eps cert) (c R)` is the number the row's proposition mentions
after the terminal, since `PortProp c` at a spectral port is
`SpectralPropAt cert (odflt (cert_eps cert) (c R))`, and it is the number
`PublishedRowAt c` is indexed by. "The number the row publishes" is therefore
exact. The companion sentence at `:45-48`, "it leaves the data and the arms
untouched and moves the real the spectral arm's proposition mentions to any
upper bound of it", matches `conclude` at `:695-701`, which rebuilds
`MkTableau` at the same `q`.

One word: "the arms" is plural where a row carries one arm. `conclude` is
quantified over every field and index, so the plural reads as the family of
arms the port function gives, and I do not call it a defect.

**`certify_exact_armE`'s comment, R9: true.** "With conclude_armE and
publish_armE below it settles the arm of a finished row by one line of the
row's text." `certify_exact_armE` fixes the arm at the certify line,
`conclude_armE` says the terminal between does not move it, and `publish_armE`
carries it to `security_arm_of`. The three together do settle a finished row's
arm, and none of the three alone does. The round-2 over-credit is gone.

**The index lines written for N8: true and exactly 80 bytes.**
"pgl27_row_exact_branch  == the first continuation of the exact branch /
point, published" and the same for the word branch. `pgl27_row_exact_branch`
is the first of two continuations of `pgl27_exact_sampled` and it publishes,
so the gloss is right where the old one, "the exact branch point published",
named the wrong object. I measured every line of both header blocks: all 80
bytes, `==` at column 30 in both files, which is N9, N10 and N11 closed.

**The non-rendered notes about `done`: both true in the `.v` files.**
`t0_sampled_branch_pgl27.v:97-103` says "did not return inside the time
bound", which is what the table records. `t0_sampled_branch.v:99-102` says the
same of the sibling file and states the practice for its own lemma. The claim
it attributes to the sibling, "on a goal of this shape whose right side is a
concluded row", is true of `pgl27_row_word_branch39_atE`, whose right side is
`published_at pgl27_row_word_branch39`. The note's forward pointer is N7. The
one carrier that still asserts non-termination is `STATUS.md` itself, which is
A3.

**`five_card_row_uniform_branch_rowE` closes `by []`**, and that is correct:
it is a `published_row` equation against a bare manifest constant, the shape
production's own `five_card_row_uniform_rowE` closes the same way, and the
measured hang is on `published_at` goals. No `published_at` equation anywhere
in the probe closes by `done`.

## 2. Names after the renames

**The two T0 files, pair by pair.** Parallel where the instances allow:

| `t0_sampled_branch.v` | `t0_sampled_branch_pgl27.v` |
|---|---|
| `five_card_uniform_sampled` | `pgl27_exact_sampled` |
| `five_card_row_uniform_branch` | `pgl27_row_exact_branch` |
| `five_card_row_uniform_branch_ideal` | `pgl27_row_exact_branch_ideal` |
| `five_card_row_uniform_branch_rowE` | `pgl27_row_exact_branch_rowE` |
| `five_card_row_uniform_branch_atE`, first conjunct | `pgl27_row_exact_branch_atE` |
| the same, third conjunct | `pgl27_row_exact_branch_ideal_atE` |
| `five_card_row_uniform_branch_transfer_neq` | no counterpart |
| `s5_rand_sampled` | `pgl27_word_sampled` |
| `Fail s5_cross_instance` | `Fail pgl27_cross_model` |
| `Fail five_card_cross_instance_back` | `Fail pgl27_cross_model_back` |
| no counterpart | `pgl27_row_word_branch`, `pgl27_row_word_branch39`, `pgl27_row_word_branch_atE`, `pgl27_row_word_branch39_atE`, `pgl27_row_word_branch_armE` |

The right-hand block with no counterpart is the spectral payload and the
concluded row, which the five-card instance cannot reach in this probe because
it holds no `SpectralCert`. That is the instances speaking. The two gaps the
instances do not explain are the `and3` against two lemmas, A8, and the
missing `_transfer_neq`, A12. The second continuation of the exact PGL(2,7)
branch point also publishes `IdealFinite` against the first's
`StaticExecutedOnly`, so the lemma is available there.

**`_rowE` means one thing in the probe, and it is production's.** Production
has five of shape `published_row <X>_tableau = <X>`, one per instance, and two
unrelated ones in `*_models.v` that name a row of a trace list. Both probe
`_rowE` follow the shape:
`published_row five_card_row_uniform_branch = five_card_row_uniform` and
`published_row pgl27_row_exact_branch = pgl27_row_exact`. The program-to-
program lemma that made the suffix ambiguous was withdrawn, so round 2's N1 is
closed and the suffix now means exactly what E1 claims.

**The six names, judged against the tree.**

- `five_card_row_uniform_branch_transfer_neq`. Production's `_neq` names one
  side and leaves the other implicit as the canonical counterpart, in
  `pgl27_inline_neq`, `psl211_alldecks_prefix_vm_neq`,
  `psl211_perdeck_law_neq`, `psl211_perdeck_fiber_card_neq` and
  `fpf_involution_partner_neq`. This name follows that and adds the coordinate
  the two differ in. The one slack is that the name says transfer while the
  statement is `published_row A <> published_row B`, with the transfer reached
  by `congr1 apr_transfer` inside the proof. The comment states it, so it
  reads. Acceptable.
- `s5_rand_sampled`. Production has no `_sampled` declaration at all, so the
  probe sets the convention and sets it uniformly: instance, model, level, in
  all four of `five_card_uniform_sampled`, `s5_rand_sampled`,
  `pgl27_exact_sampled`, `pgl27_word_sampled`. The model word matches the
  family in every case. Correct.
- `s5_cross_instance` and `five_card_cross_instance_back`. E1's stated rule is
  that the prefix is the branch point's instance, and both follow it, as
  `pgl27_cross_model` and `pgl27_cross_model_back` do. The pair does not share
  a prefix where the PGL(2,7) pair does, and that is the rule's consequence
  and not a break of it: a cross-instance mutation has two branch points at
  two instances. Correct.
- `pgl27_row_word_arm_neq`. No production `Fail` name ends in `E`. Two
  production `Fail Definition` names end in `_neq` and both state an equality
  that does not hold by conversion, which is exactly this one's shape. The
  rename is right. The file also carries production's
  `pgl27_word_arm_is_not_exact`, a different fact about `view_secrecy_of`, so
  two spellings for "the word row's arm is not the exact one" now sit in one
  file. That one is production's and outside this probe.
- `pgl27_row_word39_bindE`. `pgl27_row_word_certE` is the file's precedent for
  an equation between a surface spelling and a written-out one, with the
  surface on the left, and this follows it. Correct.

**`ConcludePayload` and `port_conclude` beside `Reprice`.** The vocabulary is
coherent under E2's rule: the operation is *conclude* and the number is a
*Reprice*. "A row is concluded at a Reprice coordinate" is the sentence the
names support, and the surface, the type `PublishedRowAt c` and
`pgl27_reprice39` all read that way. Two comment sites still use *reprice* as
the operation noun. One is the probe's own, A5. The other two are baseline
text the probe never rewrote and D10 already lists, N5. No "republish"
survives in any `.v` file of the probe: I checked all ten.

**N4, the two `_atE` orientations.** Wrong by the tree's `E` rule, as A9 sets
out, and a landing item rather than a blocker for stage B. The fix pass's
reason for declining is sound: swapping the sides changes a statement, and a
pass given comments, indexes and alignment should not. The finding stands for
whoever lands this.

**The `and3` kept while the sibling splits.** A8. The mathematical content is
identical and the proof is fast, so nothing is wrong today. The reason to
split is stage B, whose second continuation at the five-card instance goes
through a different arm and so breaks the third conjunct. With two lemmas
stage B keeps one and drops the other. With the `and3` it must restate the
whole thing.

## 3. STATUS.md

**The E6 mechanical check, re-run.** Python, whole-word match over 207
production and 38 probe `.v` files, module-qualified names split on the dot,
the E6 retired table as the exemption list. Result in N2: three tag names from
before fix pass 1 and three arm names proposed for later stages are
back-quoted, absent from every `.v` file and absent from the retired table.
All six sit in the D1 rename table or in the sentence beside it, where the
text says what they are, so no reader is misled. E6's universal is false as
written and the fix is two table rows.

**Do steps 2, 3, 4 and the D2 seed list tell one story?** Steps 2, 3 and 4 do.
Step 2 is written throughout in the fix-pass-2 names, step 3 records the
`Fail` replacement correctly after round 2's S2, and step 4 names
`pgl27_row_word39_bindE`. The D2 list does not join them: it prescribes
`port_reprice` where the copy carries `port_conclude`, A1, and directs an
index line for `pgl27_row_word39E`, A2. Those are the two blocking findings.
I scanned every retired carrier against the whole note: the only two forward
instructions written in a dead name are these two. Every other occurrence of a
retired name is a labelled historical mention or a record of what was searched
at the time.

**Does STATUS.md cite its own lines by number?** No. Every `:NNN` in it points
at a production file, at a probe `.v` file or at another probe's file. The
verdict table was moved to citation by content in fix pass 2 and is accurate:
I checked `ConcludePayload` at `pgg_tableau.v:660`, `port_conclude` at `:675`,
the `conclude` line at `pgl27_rows.v:419`, `pgl27_reprice41` at `:471` and the
`conclude` notation rule at `pgg_tableau_syntax.v:403`, immediately before the
`publish` rule at `:409`.

**The records for the other landings.** The Kim arm probe's two sites,
`kim_spectral_rows_probe.v:288` and `:365`, are exact, and so is the Kim
landing probe's `pgl27_rows.v:382`. The Kim landing probe's
`five_card_rows.v` citations are not, A6: the payloads are at `:755` and
`:798`, the rows at `:751` and `:793`, and the `Fail` at `:761-767`. The named
facts are all true: that file does hold two equality payloads to `conclude`
and does record `five_card_row_repeated39_bare`, which I read in place. The
PSL landing probe's prose does mention `RepricePayload`, and the two counts
E2 gives are exact for the two files it names, with a third and a fourth file
added since, N3.

**The G1 timing table.** Historical by its column headings and not marked as
such, A10. E7 carries the current numbers for all ten files and is internally
consistent with the main session's recompile: rc=0 throughout, no sentence
above 5 s outside `Print Assumptions`, thirty assumption blocks, and one
non-boolp constant, production's `rigidity_s5_instance.s5_group_order_eq`,
at the S5 row.

## 4. Round-2 items

Two scope corrections first. The round-2 soundness report has no B items: its
items are S1 to S9 and its own N1 to N4. The round-2 naming report has N1 to
N21, of which two are blocking, fourteen are SHOULD and five are NOTE, not
sixteen SHOULD.

Soundness, one line each:

- **S1** closed as proposed, byte for byte, and I verified the new sentence
  against a compile rather than against E3.
- **S2** closed as proposed at all three sites, step 3, step 4 and the D2
  cell.
- **S3** closed differently, by content instead of by line, and every content
  citation checks out.
- **S4** closed as proposed, with the line numbers that A6 now finds stale.
- **S5** closed as proposed, and the type-honest form is right: the two rows
  are at two `Reprice` indices and so are of two types.
- **S6** closed as proposed and incomplete as a price, A7.
- **S7** closed as proposed, `Proof. split; exact: erefl. Qed.`
- **S8** closed as proposed in the file, and the note's own account of it was
  not updated, A4.
- **S9** closed as proposed.
- Soundness **N1** not closed and nothing was owed, N8 above.
- Soundness **N2** closed with nothing owed, the boundary sentence stands at
  `ab_arm`.
- Soundness **N3** and **N4** declined, and the reason is stated: both are
  NOTE, not SHOULD. Sound.

Naming:

- **N1** closed as proposed, the whole rename table applied and one lemma
  withdrawn. I confirmed by whole-word scan that no `t0_` declaration name
  survives in any `.v` file.
- **N2** closed as proposed.
- **N3** closed as proposed, both comments.
- **N4** declined, reason sound, A9.
- **N5** closed as proposed, both pointers name their lemmas.
- **N6** closed as proposed, and the reason stays on `SecurityArm` where it
  belongs.
- **N7** declined, reason sound: that file belongs to another probe, and the
  item is recorded in the seed list.
- **N8** closed as proposed, both index pairs at 80 bytes.
- **N9**, **N10**, **N11** closed, and I remeasured all of them: every header
  line of both T0 files and of `g2_keyword_measure.v` is 80 bytes, `==` at
  column 30 in both T0 files.
- **N12** closed in the `.v` file and open in `STATUS.md`, A3.
- **N13** closed as proposed.
- **N14** closed as proposed.
- **N15** declined, reason sound: a file-local convention is its owner's to
  keep or drop.
- **N16** closed differently, renamed now rather than deferred, and that
  rename is the root of A1.
- **N17** to **N21**: four NOTE with nothing owed and one, N21, declined with
  a record, reason sound, same ground as N7.

The six declines: N4, N7, N15, N21, soundness N3 and soundness N4. Each reason
is sound. N7, N21 and N15 all rest on the same rule, that a probe does not
edit another probe's file or propagate its conventions, and each is recorded
rather than dropped. N4's reason is a scoping rule about what a comment pass
may touch and it keeps the finding alive for the landing. Soundness N3 and N4
are declined as NOTE rather than SHOULD, which matches how the round-2 report
graded them.

## 5. Readiness for stage B

Stage B adds `IdealProximity` with its certificate, a `certify` statement, the
`SecurityArm` constructor `IdealProximityArm`, and a row at the five-card
instance continuing a named `Tableau Sampled` value through a different arm
than its sibling. From this copy as it stands, that touches, measured:

**`pgg_tableau.v`, the code.**

- `Variant SecurityPort` at `:161-164`: a third constructor,
  `IdealProximity of IdealProximityCert sa`.
- `port_arm` at `:177-183`: a third branch. This is the only `match` on
  `SecurityPort` whose result type does not mention the port.
- `PortProp` at `:406-412`: a third branch, the new arm's proposition.
- `ConcludePayload` at `:660-665`: a third branch. `unit` if the new arm's
  proposition is not monotone in a number, the inequality if it is. Its own
  comment already states the condition, "an arm whose proposition is not
  monotone in the number it carries owes a different obligation here".
- `port_conclude` at `:675-687`: a third case in the statement's `match` and a
  third case in the proof, whose `case: p => [w|cert]` at `:685` becomes a
  three-way split.
- New declarations with no existing site to edit: the certificate record
  beside `ExactWitness` and `SpectralCert`, the proposition beside `ExactProp`
  and `SpectralPropAt`, the payload type beside `ExactPayload` and
  `SpectralPayload`, the composition law beside `exact_tail` and
  `spectral_tail`, the `certify` statement beside `certify_exact` and
  `certify_spectral`, and a fifth general lemma `certify_idealproximity_armE`
  beside the four `_armE`.
- `Variant SecurityArm` at `:172`: the third tag. D1 already fixes its
  spelling, `IdealProximityArm`.
- Nothing else. `StackAt`, `StackProp`, `BridgedProp`, `tableau_bind`,
  `conclude`, `restate`, `publish`, `PublishedRowAt` and the four projections
  are all parametric in the port and need no edit. `conclude_armE` and
  `publish_armE` are quantified over `q` and carry through unchanged.

**`pgg_tableau_syntax.v`.** One `certify` rule for the new statement, beside
the four at `:375`, `:378`, `:383` and `:390`, taking the rule count from
thirteen to fourteen. The keyword measurement of the header is repeated for
each word the rule writes, and the count of nineteen at `:60-64` changes only
if a new word follows a slot. The literal `IdealProximity` follows the literal
`certify` and so stays an identifier, by the same argument the header already
makes for `ExactIndependence` and `SpectralDecay`.

**The header index of `pgg_tableau.v`,** `:49-84`: one line per new name, and
the `SecurityArm` line at `:52` needs no change.

**The sentences stage B makes false. Every one is true today,** so these are
SHOULD and not defects of stage A. Wording them now is cheaper than finding
them later, and G3 already owns four of them.

| site | text | why stage B breaks it |
|---|---|---|
| `pgg_tableau.v:17` | "There are five statements." | six |
| `pgg_tableau.v:22-23` | "certify_exact and certify_spectral adjoin a security witness of one of the two arms" | three arms, three statements |
| `pgg_tableau.v:23-24` | "Both arms speak only of a coalition below the privacy threshold" | the new arm does too, but "both" is wrong |
| `pgg_tableau.v:28-30` | "A row commits to one of them and claims nothing about the other, and security_arm_of names which of the two a finished row committed to." | "the other", "which of the two" |
| `pgg_tableau.v:32` | "Each arm has one composition law, and the two laws are where the mathematics of the row sits." | three laws |
| `pgg_tableau.v:75` | "security_arm_of        == which of the two arms a published row carries" | index line |
| `pgg_tableau.v:156` | "Which of the two arms an instance certifies" | `SecurityPort`'s comment |
| `pgg_tableau.v:166` | "Which of the two arms a row commits to" | `SecurityArm`'s comment |
| `pgg_tableau.v:633` | "The two certify statements are the only lines through which an instance's own mathematics enters a row" | `certify_spectral`'s comment |
| `pgg_tableau.v:781` | "Which of the two arms a published row carries" | `security_arm_of`'s comment |
| `pgg_tableau.v:806-809` | "the two statements are the only ones that build a port, and each writes one constructor at every field and index" | `certify_spectral_armE`'s comment, and the fact it states stays true of three statements |
| `pgg_tableau.v:279-284` | `ab_arm`'s "The two certify statements build a port whose constructor is the same at every field and index" | same |
| `assumptions_report.v:39-40` | "the two certify statements write it and the two terminals carry it through" | three statements |
| `five_card_rows.v:46` | "A program reaches it only through one of the two arms of certify" | three, and the gap this sentence describes may close |
| `five_card_rows.v:410` | "neither arm of certify takes a bound of that kind" | the new arm still does not take a conditional mutual information, so the sentence stays true and "neither" becomes "no arm" |
| `pgl27_rows.v:673` | "The two arms are different statements" | three |

The uniform repair is to write "each arm" and "the arms" where the text now
writes "the two arms", and to replace "which of the two" by "which arm".
`pgg_tableau.v:17` and `:32` carry counts and need the number changed.

**The cost recorded in STATUS.md.** D1's six places are exactly the six code
sites above and are truthfully recorded, which answers round 2's request.
As a price for stage B the record is short by the whole of the spec's P2, A7.

**Nothing in the code stands in stage B's way.** The two shapes stage A leaves
untested are named honestly in step 2, "Open for stage B": one named `Sampled`
value continued through two different arms, and a mutation between two
adapters that share an index type within one instance. Both are stage B's
first ledger items and both are stated as untested rather than as shown. The
`five_card_uniform_sampled` branch point that stage B will continue through a
second arm is in place and its payload type reduces through the name, which
was T0's whole question.

## 6. The statement-comment rule, the 80-byte box, barred vocabulary

**The rule on the fix pass's text.** Every comment fix pass 2 wrote carries
the fact and its position. `five_card_row_uniform_branch_rowE` gained the
position sentence round 2's N14 asked for, "Conversion decides it, so the
descriptive row and the theorem proved about it cannot drift apart".
`security_arm_of`'s comment now gives its own position instead of restating
`SecurityArm`'s, which stays where it belongs. `pgl27_row_word39_bind` is left
with the fact alone, one sentence, which is right: it re-spells existing data
and the rule prices a re-tupling at one sentence. The two `_armE` comments
name the lemmas they depend on rather than pointing at "the lemma above",
which is what round 2 asked for and which the rule's survival test would
prefer written as mathematics. That tension is N6 and I leave round 2's
ruling in place. The two source notes about `done` are strategy, in
non-rendered `(* ... *)` comments, which is where the rule puts strategy. No
status marker, effort estimate, proof sketch in a rendered body, or author
attribution anywhere in the ten files.

**Line width.** Exactly three `.v` lines exceed 80 bytes, all in
`pgg_tableau_syntax.v` at `:329`, `:367` and `:390`, and I confirmed each is
byte-identical to the line at the same position in
`manifest/pgg_tableau_syntax.v`. Every other line of every probe `.v` file is
at or under 80.

**Barred vocabulary.** Zero hits across the ten `.v` files and `STATUS.md`,
scanned case-insensitively as whole words, for every term on the account's
barred list: the noun for a file that centralizes a development's headline
results, the metaphor for a logical restriction in any inflection, the verb
for assuming without proving in any inflection, the two-character token
capital L followed by digit one, and the narrative words the rule against
metaphor for mathematical results names. The repository's own phrase for the
class relation, "class-conditional bound", is not needed here because no
sentence of stage A states one.

---

## What I did not check

- The Rocq content of stage A: rounds 1 and 2 both found it sound and my brief
  told me not to redo it. I read the statements to check the sentences about
  them and I proved nothing.
- The keyword paragraph of `pgg_tableau_syntax.v` clause by clause. Round 2
  found it right in every clause. I confirmed only that the `conclude` rule
  sits immediately before the `publish` rule, that thirteen `Notation` rules
  are in the file, and that the paragraph names `conclude` among the tokens
  that follow a literal and `by` among those that follow a slot.
- The compile table of E7 and the thirty assumption blocks. The main session
  recompiled all ten files from source after fix pass 2 and I took that as
  given. I compiled three scratch files of my own, `audit-3/a3_cross_msgs.v`
  at rc=0 and `audit-3/a3_m1.v` and `audit-3/a3_m3.v` at rc=1 by design.
- `instances/psl211/psl211_endpoints.v`: never opened, never compiled. No
  `make`, no full rebuild, no state-changing git command.
- Whether the two `_atE` statements of A9 still compile after the swap. The
  goals are symmetric and `exact: erefl` closes either direction by the same
  conversion, but I did not compile the swapped forms.
- The audit reports of the Kim and PSL probes beyond the four sites my brief
  named and the two carrier counts I verified.
