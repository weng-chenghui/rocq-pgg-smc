# Landing 3 of the Tableau extensions — staged text

Date: 2026-09-20. Branch `feat/tableau-extensions-probe`, HEAD `c8b1923`.

This directory holds the STAGED TEXT of landing 3 of
`notes/2026-09-20-000000-tableau-extensions-landing-design.md`. Nothing under
`manifest/`, `instances/`, `lib/`, `security/` or `_CoqProject` of the
repository was touched, and nothing under
`notes/probes/2026-09-20-tableau-extensions-landing1/` or
`notes/probes/2026-09-20-tableau-extensions-landing2/` was touched. The main
session does every `cp`.

Every staged file compiles, the fidelity file compiles, and every landed
declaration's assumptions are the classical trio.

## Layout

Seven files are LANDED: their text is the permanent text landing 3 proposes.
The seventh, `staged/lib/var_dist_supp.v`, became landed in fix pass 1.

| Staged path | Source | What it is |
|---|---|---|
| `staged/instances/pgl27/pgl27_exec.v` | PRODUCTION plus `pgl27_prior_sample` | landed |
| `staged/instances/pgl27/pgl27_models.v` | PRODUCTION plus `pgl27_prior_exact_family` | landed |
| `staged/instances/pgl27/pgl27_analysis.v` | PRODUCTION plus two facade aliases | landed |
| `staged/manifest/pgg_analysis_manifest.v` | PRODUCTION plus Row 10, its typed row and its pins | landed |
| `staged/manifest/pgg_analysis_client.v` | PRODUCTION plus one `Check`, row count ten | landed |
| `staged/instances/pgl27/pgl27_proximity.v` | NEW; twenty-six declarations of probe `p5_pgl27_prior_ideal.v`, `p5_pgl27_word_proximity.v`, `p5_mutations.v` | landed |
| `staged/lib/var_dist_supp.v` | PRODUCTION plus `var_dist_fdist1_uniform` and the `lra` import its proof needs | landed, from fix pass 1 |

Twelve files are CHAIN-CONSISTENCY COPIES. They are not landed by this
landing. They exist so that everything downstream of landing 2's five files
and of `instances/pgl27/pgl27_exec.v` compiles against the staged text rather
than against production's, which is what the `cp` will force in production.

| Staged path | Whose text it is |
|---|---|
| `staged/security/var_dist_joint_law.v` | landing 2 |
| `staged/instances/kim2025/five_card_mixing.v` | landing 2 |
| `staged/manifest/pgg_tableau_arm_relations.v` | landing 2 |
| `staged/instances/kim2025/five_card_proximity.v` | landing 2 |
| `staged/instances/kim2025/five_card_analysis.v` | production |
| `staged/manifest/pgg_tableau.v` | landing 1 |
| `staged/manifest/pgg_tableau_syntax.v` | landing 1 |
| `staged/instances/pgl27/pgl27_rows.v` | landing 1 |
| `staged/instances/kim2025/five_card_rows.v` | landing 1 |
| `staged/instances/s5/s5_rows.v` | landing 1 |
| `staged/instances/psl211/psl211_reading_constancy.v` | landing 1 |
| `staged/instances/psl211/psl211_rows.v` | landing 1 |

All twelve are copied from **production**, which holds landings 1 and 2
(landing 2 landed at commit `0397f8e`; the branch HEAD as this file is written
is `c8b1923`). `cmp` reports each of the twelve byte-identical to landing 2's
staged text at commit `cb3adfc`, the text every compile before that copy had
loaded, so the change of source moved nothing.

**Any of the twelve may move again**, and a landing-3 compile is evidence
only against the text it loaded. `restage.py` is how to redo this:

```
python3 restage.py --check     # report which of the twelve differ, and
                               # whether the difference is code or comments
python3 restage.py             # copy them and recompile the whole chain
```

It reports each file as `unchanged`, `comments only` or `CODE CHANGED`, using
the same comment-stripped token comparison `verify.py` uses, then calls
`compile.py` with no arguments, which compiles the `_CoqProject` order: the
nineteen staged files and the fidelity file, one Rocq process at a time
through the `rocq1` lock.

Those twelve plus the seven landed are the union of two reverse closures. A
Python walk over the `Require` lines of every `.v` file outside `notes/`,
`_build` and `.git` gives `instances/pgl27/pgl27_exec.v` the eleven
reverse-dependants the design's section 3 computes, `pgl27_models`,
`pgl27_analysis`, `pgg_analysis_manifest`, `pgg_tableau`,
`pgg_tableau_syntax`, `pgl27_rows`, `five_card_rows`, `s5_rows`,
`psl211_rows`, `psl211_reading_constancy` and `pgg_analysis_client`, and gives
`lib/var_dist_supp.v` those eleven together with `five_card_mixing` and
`five_card_analysis`. None of the nineteen is in the forward closure of
`instances/psl211/psl211_endpoints.v`, which the same walk computes as 35
modules: the intersection is empty. `psl211_endpoints.v` was never compiled
here, and `psl211_reading_constancy.v`, `psl211_models.v` and
`psl211_analysis.v` load `psl211_endpoints.vo` by digest, which is R3's
recorded state.

`_CoqProject` records the flags and the compile order. `compile.py` reads the
flags out of `_CoqProject` so the two cannot drift, and drives every
`rocq compile` through the machine-wide `rocq1` lock, one process at a time.
`verify.py` prints the four checks below; `verify.out` is its captured output,
`compile.out` the chain run's and `landing_fidelity.out` the fidelity run's.

### The load-path order

Landing 1 measured it and landings 2 and 3 reuse it: Rocq 9.0.0 resolves a
`Require` to the LAST matching `-R`/`-Q` entry, so the staged roots are the
last entries bound to `pgg_smc`, after production's AND after
`-Q . tableau_ext_landing3`. The run prints one `overriding-logical-loadpath`
warning per staged root, which is that remapping and not an error.

---

## E1 — `pgl27_exec.v` gains one sample adapter

`pgl27_prior_sample`, the text of `p5_pgl27_prior_ideal.v:78-85`, is added
after `End pgl27_execution.` in its own banner block, and the header's
`Definitions:` block gains a two-line entry for it.

**Placement, and why it is not inside the section.** The design's section 3
says "beside the file's existing adapters, at the end of the adapter section".
Every adapter of this file is inside `Section pgl27_execution`, whose
`Variable R : realType` (`:114`) and `Variable secretP : R.-fdist bool`
(`:521`) the probe's declaration binds itself, explicitly and in that order.
Writing it inside the section would either shadow both section variables or
drop the two binders from the text, and either changes the token stream. The
declaration therefore goes after `End`, which is the shape `pgl27_models.v`
already uses for the two model families it declares after
`End pgl27_sample_models` (`:417`, `:424`). No import is added: the file
already `Require`s `pgg_sample_adapter` and `pgl27_word_privacy`, which is
where `pgl27P_gen` is (`instances/pgl27/pgl27_word_privacy.v:97`).

One comment change, the file's own leading-name convention, which every other
declaration comment in `pgl27_exec.v` uses:

- before: "The sample layer of the exact shuffle over the eight-card
  execution, with the law of the dealt secret left free."
- after: "pgl27_prior_sample — the sample layer of the exact shuffle over the
  eight-card execution, with the law of the dealt secret left free."

Whole-file token diff against production: **1 hunk, 45 tokens, the added
definition**. Nothing else in the file moved.

---

## E2 — `pgl27_models.v` gains one model family

`pgl27_prior_exact_family`, the text of `p5_pgl27_prior_ideal.v:87-89`, is
added immediately after `pgl27_word_family` (`:424-426`), in the same
post-section block. The header index of this file lists neither existing
family, so it gains no entry.

One comment change, the same leading-name convention:

- before: "The exact shuffle as an analysis model family indexed by the
  prior."
- after: "pgl27_prior_exact_family — the exact shuffle as an analysis model
  family indexed by the prior."

Whole-file token diff against production: **1 hunk, 32 tokens, the added
definition**.

**The other two declarations the design's section 2 assigns to this file do
not land here.** `pgl27_prior_viewE` (`p5_pgl27_prior_ideal.v:96`) is proved
by `pgl27_static_obsE`, which is `instances/pgl27/pgl27_rows.v:159`, and
`pgl27_prior_exact_witness` (`:112`) is typed at `ExactWitness`, which is
`manifest/pgg_tableau.v:171`. Both files are strictly below `pgl27_models.v`
in the import order (`pgl27_rows` requires `pgg_tableau` requires
`pgg_analysis_manifest` requires the four facades require `pgl27_models`), so
neither name is in scope there and no import can bring it without a cycle.
The two therefore land in `instances/pgl27/pgl27_proximity.v`, which is below
both. Ruling Q1: accepted; this supersedes the design's section-2 table.

---

## E3 — `pgl27_analysis.v` gains two aliases

Section 4 of the facade gains `prior_sample := @pgl27_prior_sample` after
`fixed_word_sample` and `prior_exact_family := pgl27_prior_exact_family` after
`word_family`. Both follow the file's contract: a `Definition` whose body is
the landed constant, no restated type, the `pgl27_` prefix dropped. The
header's check table lists no model family, so it gains no line.

R2 asks for the family alias only. The adapter alias is added with it so that
the manifest row of E4 names its sample in facade vocabulary, as the design's
section 7 leaves open and as every other row does; the alternative it allows,
naming `pgl27_prior_sample` by file, is what the row would otherwise carry.
Ruling Q3: accepted.

Whole-file token diff against production: **2 hunks, 11 tokens**, one per
alias.

---

## E4 — `pgg_analysis_manifest.v` gains Row 10

Three code additions and one comment block.

1. The Row 10 comment block, after Row 9's and before
   "Aliases carrying no capability yet", in the field order of Row 9's
   (`:631-669` of production) and with the same capabilities table and level
   justification.
2. `pgl27_row_prior_exact`, after `psl211_row_alldecks`, with its own
   docstring.
3. Five `Check` pins in the rows checker, in the shape the nine existing rows
   use, and one application of the new family at its index type in the block
   that exercises parameterized families.

The banner "The deterministic checker: the nine typed rows" becomes "the ten
typed rows". Landing 4 makes it eleven.

The typed row, verbatim:

```
Definition pgl27_row_prior_exact : AnalysisPathRow :=
  @MkAnalysisPathRow PGL27Analysis.observed AnalysisBridged
    PGL27Analysis.prior_exact_family StaticExecutedOnly BaselineClassicalOnly.
```

Its five fields are the row equation's and not retyped: `landing_fidelity.v`
proves `published_row pgl27_row_prior_exact_tableau = pgl27_row_prior_exact`
by `exact: erefl`, so the manifest row and the program agree by conversion.

Two fields of the table need their own justification, both read off
declarations.

**Bound or certificate: none.** The row is published through the exact arm,
whose witness `pgl27_prior_exact_witness` carries independence
(`pgl27_view_indep_gen`) and no number. `ExactWitness`
(`manifest/pgg_tableau.v:171`) has no epsilon field.

**Transfer status: StaticExecutedOnly.** `pgl27_prior_sample` draws the cut
from `pgl27P_gen secretP`, the product of the given prior with the uniform law
on the group, so the model compares no idealized shuffle with a real one. That
is the same reading Row 1 gives for `pgl27_row_exact`, and the row equation
`pgl27_row_prior_exact_rowE` carries the same constructor.

Whole-file token diff against production: **3 hunks, 98 tokens**, the typed
row, the five pins and the family application.

---

## E5 — `pgg_analysis_client.v` reaches ten rows

`Check PGL27Analysis.prior_exact_family.` is added after
`Check PGL27Analysis.word_family.`, with the same `(* 4 Models, typed family
*)` trailing comment, and the header sentence "the nine typed rows" becomes
"the ten typed rows". The file keeps its single `Require` and every `Check`
stays bare.

Whole-file token diff against production: **1 hunk, 2 tokens**, the `Check`.

---

## E6 — the new `instances/pgl27/pgl27_proximity.v`

Twenty-six declarations, twenty-three of them statements and three recorded
`Fail`s. Twenty-four are token-identical to the probe's; the two that are not
are the forced edits (b) and (c) below. Fix pass 1 moved the twenty-seventh,
`var_dist_fdist1_uniform`, to `staged/lib/var_dist_supp.v` and renamed two of
the twenty-six; see the Fix pass 1 section.

| Group | Declarations | Probe source |
|---|---|---|
| the ideal at every prior | `pgl27_prior_viewE`, `pgl27_prior_exact_witness`, `pgl27_row_prior_exact_tableau`, `pgl27_row_prior_exact_armE`, `pgl27_row_prior_exact_rowE` | `p5_prior:96,112,134,144,157` |
| the distance | `pgl27_word_secret`, `pgl27_word_proximity_close` | `p5_word:111,128` |
| the certificate | `pgl27_word_proximity_cert`, `pgl27_word_proximity_cert_idealE` | `p5_word:191,206` |
| the number | `pgl27_word_proximity_cert_epsE`, `pgl27_word_proximity_eps_halfE`, `pgl27_pow2_40_ge1`, `pgl27_pow2_40_gt0`, `pgl27_word_proximity_le39`, `pgl27_word_proximity_cert_eps_lt2` | `p5_word:220,234,241,245,251,263` |
| the two rows | `pgl27_row_word_proximity`, `pgl27_row_word_proximity_rowE`, `pgl27_row_word_proximity_armE`, `pgl27_row_word_families_sampledE` (renamed in fix pass 1), `pgl27_row_word_obs_sampledE`, `pgl27_row_word_arm_neq` | `p5_word:285,299,307,323,335,350` |
| what the row states | `pgl27_word_view_proximity` | `p5_word:382` |
| the ideals refused | `pgl27_word_uniform_ideal_close_false` (renamed in fix pass 1) | `p5_mut:120` |
| in `lib/var_dist_supp.v` | `var_dist_fdist1_uniform` (moved there in fix pass 1) | `p5_mut:88` |
| recorded `Fail`s | `pgl27_word_proximity_cert_unit_ideal`, `pgl27_word_proximity_cert_uniform_ideal`, `pgl27_cross_model_proximity` | `p5_mut:68,187,205` |

`pgl27_row_word_branch39_armE` (`p5_word:314`) does NOT land: landing 1 put it
in production at `instances/pgl27/pgl27_rows.v:502`, together with
`pgl27_word_sampled` (`:485`) and `pgl27_row_word_branch39` (`:493`), which is
R1's way (a) carried out. The two sibling equations that land,
`pgl27_row_word_arms_sampledE` and `pgl27_row_word_obs_sampledE`, are stated
at that named `Tableau Sampled` value and not against another row.

Imports: the union of the three probe files' blocks, with the three
probe-local edges rewritten. `From tableau_ext_probe Require Import
pgg_tableau pgg_tableau_syntax` and `... pgl27_rows` become `From pgg_smc`
ones; `t0_sampled_branch_pgl27` resolves to `pgl27_rows` under R1(a);
`p5_pgl27_prior_ideal` resolves to this file, `pgl27_exec` and `pgl27_models`.
`pgg_collusion_bound` comes from `p5_mutations.v`'s block and carries
`var_dist_fdistmap`, the one step of `pgl27_word_uniform_ideal_not_close`.

### The three forced code edits

**(a) `var_dist_fdist1_uniform`: the `first [...]` list replaced by the branch
that fires.** Since fix pass 1 this declaration lands in
`staged/lib/var_dist_supp.v`. The probe writes, at `p5_mutations.v:98-100`:

```
have Hf : (fdist1 true : R.-fdist bool) false = 0.
  by first [by rewrite fdist1E | by rewrite fdist1E /= mul0rn
           | by rewrite fdist1E mul0rn | by rewrite fdist1E /=].
```

`first` takes the first branch that succeeds, so the branch that fires is the
first. The staged text is:

```
have Hf : (fdist1 true : R.-fdist bool) false = 0.
  by rewrite fdist1E.
```

Determined by compiling: the file that carries it compiles rc 0 with it. The
statement is unchanged; `verify.py` prints the 27-token proof-body difference
in full, from `staged/lib/var_dist_supp.v` since fix pass 1.

**(b) `pgl27_cross_model_proximity`: its subject respelled.** The probe writes
`pgl27_exact_sampled certify IdealProximity pgl27_word_proximity_cert`, and
`pgl27_exact_sampled` is `t0_sampled_branch_pgl27.v:81`, which landing 1 did
NOT land: production's `pgl27_rows.v` holds `pgl27_word_sampled` and not the
exact one. Left as written, the `Fail` would succeed on an unknown reference
and guard nothing. The staged text names the same value inline:

```
Fail Definition pgl27_cross_model_proximity : Tableau AnalysisBridged :=
  pgl27_dealt sample pgl27_exact_family
    certify IdealProximity pgl27_word_proximity_cert.
```

`pgl27_rows.v` already spells a `Tableau Sampled` inline in a `Fail`
(`:408`) and inline inside a statement (`:223`). The un-`Fail`ed scratch
compile below shows the failure is now the one the comment states. Ruling Q2.

**(c) `pgl27_row_prior_exact_rowE` states the manifest row by name.** The probe
writes its right-hand side at the raw family names, because the manifest held
no row at this model when it was written. Landing 3 adds that row, so the
lemma states what every other `_rowE` in the tree states, that the program
publishes its manifest row:

- before (`p5_pgl27_prior_ideal.v:157-161`):

```
Lemma pgl27_row_prior_exact_rowE :
  published_row pgl27_row_prior_exact_tableau
  = @MkAnalysisPathRow pgl27_observed AnalysisBridged
      pgl27_prior_exact_family StaticExecutedOnly BaselineClassicalOnly.
Proof. exact: erefl. Qed.
```

- after:

```
Lemma pgl27_row_prior_exact_rowE :
  published_row pgl27_row_prior_exact_tableau = pgl27_row_prior_exact.
Proof. exact: erefl. Qed.
```

`exact: erefl` closes it in **0.003 s** and its `Qed.` in 0.001 s, read off the
`-time` line, so `reflexivity` is not needed and `by []` is not used. The
docstring is rewritten to say what the lemma is, and the probe's clause about
`pgl27_row_exact` is dropped rather than asserted: no declaration in the tree
states that the two rows differ, a whole-tree scan for `pgl27_row_prior_exact`
outside `notes/` returning only the manifest's own definition and its pins.

- before: "It agrees with pgl27_row_exact on the completion level, the
  transfer status and the assumption status, and differs from it in the fourth
  coordinate, the model family an AnalysisPathRow records: pgl27_row_exact
  carries the unit-indexed exact family and this row carries the prior-indexed
  one. The equation published_row pgl27_row_prior_exact_tableau =
  pgl27_row_exact typechecks and is not provable by conversion, so the
  manifest of the tree holds no row at this model."
- after: "The manifest row the ideal program publishes: the row of the
  eight-card orbit instance at the prior-indexed exact shuffle. Its five
  coordinates are the observed execution the program runs on, the completion
  level the publish terminal reaches, the model family the sample step named,
  and the two statuses the terminal was given, so the manifest's description of
  this path is read off the program and not written beside it."

The header's `Key results:` entry moves with it, from "the manifest row the
ideal program publishes, in full" to "the ideal program publishes
pgl27_row_prior_exact". `landing_fidelity.v` keeps both statements: the landed
one, closed by the landed lemma, and the probe's raw-family one, closed by
`exact: erefl`. Ruling Q4.

### The R7 rename

`pow2_40_ge1` and `pow2_40_gt0` of `p5_pgl27_word_proximity.v:241,245` land as
`pgl27_pow2_40_ge1` and `pgl27_pow2_40_gt0`, matching the PSL(2,11) pair's
prefix, which is the orchestrator's decision on R7. The rename reaches four
sites: the two declarations and one reference inside each of
`pgl27_word_proximity_le39` and `pgl27_word_proximity_cert_eps_lt2`.
`verify.py` undoes it before the token comparison and prints the substitution,
so both declarations are still reported token-identical to the probe's.

### Comment changes against the probe

Seven, each with its reason.

`pgl27_prior_sample` and `pgl27_prior_exact_family`: the leading-name
convention of their new home, quoted in E1 and E2.

`pgl27_row_prior_exact_rowE`, the whole docstring, because the statement
changed: quoted in full under the forced edit (c) above.

`pgl27_word_proximity_le39`, one clause added, read off the two numbers
(`ipc_eps = 2%:R^-40` by `pgl27_word_proximity_cert_epsE`, the published
constant `2%:R^-39` by `pgl27_reprice39`):

- after: "…It is the obligation of the terminal that concludes the proximity
  row at that constant, and it is met strictly, the certificate's number being
  half of the published one."

`pgl27_word_proximity_cert_eps_lt2`, twice, because "ceiling" is a metaphor
noun for a bound and landing 2 removed it from its own files:

- before: "is under two, the ceiling var_dist_le2 gives" / "At about 4.5e-13
  of the ceiling"
- after: "is below two, the bound var_dist_le2 gives" / "At about 4.5e-13 of
  that bound"

`pgl27_word_view_proximity`, one word, following landing 2's N10: "view" stays
inside identifiers and the prose says "reading":

- before: "the joint law of the executed coalition view and that secret"
- after: "the joint law of the executed coalition reading and that secret"

`pgl27_cross_model_proximity`, last sentence, because the two failures it
cited are `t0_sampled_branch_pgl27.v:190,195` and are not in the tree:

- before: "Two models of one instance are separated here as they are for the
  exact and the input-indistinguishability payloads at pgl27_exact_sampled."
- after: "A certificate of one model of an instance therefore does not reach
  another model of the same instance, whichever arm it belongs to."

Two plain `(* *)` comments inside proofs lose a date, because the staged text
is permanent text:

`pgl27_row_word_obs_sampledE`:

- before: "Each row against the named value was measured on 2026-09-19 at
  under 0.01 s by exact: erefl."
- after: "Each row stated against the named value closes by exact: erefl in
  under 0.01 s."

`pgl27_row_word_arm_neq`:

- before: "Three costs were measured on 2026-09-19 and each is why one line
  reads as it does."
- after: "Three costs are each why one line reads as it does."

### Header

What the file is about, in four paragraphs: which two models are compared and
why the comparison needs a prior-indexed exact family; that the ideal's own
privacy is `pgl27_view_indep_gen` and therefore a theorem; where both numbers
come from and which certificate carries which, with the advantage reading; and
what the row does not claim, at four seats, citing `pgl27_view_dep_k4` and
`pgl27_view_leak_k4` (`instances/pgl27/pgl27_secrecy.v:116,192`, both present
in production and both stated at the uniform prior and the fixed deck pair).
`Definitions:` indexes the five definitions and `Key results:` the nineteen
remaining statements, so the two blocks index all 24 non-`Fail` declarations
and no `Fail`.

---

## The recorded `Fail`s, and why each fails

Three `Fail` guards land. Each was re-compiled without its `Fail`, one file
per guard, in the scratchpad and never in the repository
(`/private/tmp/.../scratchpad/unfail_l3_f1.v` … `unfail_l3_f3.v`). All three
fail, and each fails for the reason its comment states.

| Guard | Error |
|---|---|
| `pgl27_word_proximity_cert_unit_ideal` | `The term "secretP" has type "{fdist bool}" while it is expected to have type "amf_index pgl27_exact_family R"` — the index type, exactly as the comment says |
| `pgl27_word_proximity_cert_uniform_ideal` | the distance field: `pgl27_word_proximity_close secretP HC` has the type stated between the word model at `secretP` and `pgl27_prior_sample secretP`, against the type wanted at `amf_sample pgl27_word_family R secretP` and the uniform-prior ideal |
| `pgl27_cross_model_proximity` | `The term "pgl27_word_proximity_cert" … while it is expected to have type "IdealProximityPayload (tableau_at (pgl27_dealt sample pgl27_exact_family))" (cannot unify "amf_index (sp_f (tableau_at …)) R" and "{fdist bool}")` |

`rocq compile` echoes nothing for a `Fail` guard, so the guards' own compile is
evidence only that they fail, not why. The three scratch files are the record
of why.

---

## Compiles

One Rocq process at a time, through the `rocq1` lock, `rocq compile` with
`-time`, never `make`. `instances/psl211/psl211_endpoints.v` was never
compiled. Nothing was written into a production directory: every `.vo` lands
beside its `.v` under `staged/`.

| File | rc | wall | sentences over 5 s |
|---|---|---|---|
| `staged/lib/var_dist_supp.v` | 0 | 4.0 s | none |
| `staged/security/var_dist_joint_law.v` | 0 | 3.9 s | none |
| `staged/instances/pgl27/pgl27_exec.v` | 0 | 17.0 s | one, 8.73 s, production's own `by vm_compute` |
| `staged/instances/pgl27/pgl27_models.v` | 0 | 4.1 s | none |
| `staged/instances/pgl27/pgl27_analysis.v` | 0 | 3.7 s | none |
| `staged/instances/kim2025/five_card_mixing.v` | 0 | 4.2 s | none |
| `staged/instances/kim2025/five_card_analysis.v` | 0 | 3.8 s | none |
| `staged/manifest/pgg_analysis_manifest.v` | 0 | 5.9 s | one, 5.23 s, the `Require Export` block |
| `staged/manifest/pgg_tableau.v` | 0 | 13.0 s | none |
| `staged/manifest/pgg_tableau_syntax.v` | 0 | 4.3 s | none |
| `staged/instances/pgl27/pgl27_rows.v` | 0 | 6.3 s | none |
| `staged/instances/kim2025/five_card_rows.v` | 0 | 4.6 s | none |
| `staged/instances/s5/s5_rows.v` | 0 | 4.0 s | none |
| `staged/instances/psl211/psl211_reading_constancy.v` | 0 | 22.3 s | three, 5.16 s, 6.05 s and 6.06 s |
| `staged/instances/psl211/psl211_rows.v` | 0 | 5.4 s | none |
| `staged/manifest/pgg_analysis_client.v` | 0 | 3.8 s | none |
| `staged/manifest/pgg_tableau_arm_relations.v` | 0 | 3.7 s | none |
| `staged/instances/kim2025/five_card_proximity.v` | 0 | 5.7 s | none |
| `staged/instances/pgl27/pgl27_proximity.v` | 0 | 5.2 s | none |
| `landing_fidelity.v` | 0 | 29.8 s | none |

The table is the fix-pass-1 run, `python3 compile.py` with no arguments,
captured in `compile.out`. Another session held the machine-wide `rocq1` lock
during part of the run, so the wall times above are the per-file figures
`compile.py` prints after the lock is taken; the `-time` lines, not the wall
times, are what the "sentences over 5 s" column reads. Every file is rc 0 and
no landed file has a sentence over 5 s: the three slow sentences are
`pgl27_exec.v`'s production `by vm_compute.` at 8.902 s, the manifest's
`Require Export` block at 5.222 s, and the three of
`psl211_reading_constancy.v` at 5.073 s, 6.059 s and 6.084 s, all measured by
landings 1 and 2 as well.

Nineteen staged files and the fidelity file, compiled in the `_CoqProject`
order by `python3 compile.py` with no arguments, captured in `compile.out`.
No sentence of a landed file is over 5 s: the one slow sentence of
`pgl27_exec.v` is production's `by vm_compute`, measured at 8.94 s here and
unchanged by this landing, and the slow sentences of
`pgg_analysis_manifest.v` and `psl211_reading_constancy.v` are the ones
landing 1 and landing 2 both measured. Every number above was measured with
no other Rocq process running; a wall time taken while another session holds
the machine-wide `rocq1` lock includes that session's run, which is how
`var_dist_supp.v` once measured 74.4 s here against 3.9 s alone.

The design's compile order for landing 3 is the `_CoqProject` order above.
No row-against-row data equation was added: every row equation this landing
states names either the `Tableau Sampled` value `pgl27_word_sampled` or a
manifest `AnalysisPathRow`, and each closes by `exact: erefl` inside a file
whose slowest sentence is under 5 s.

---

## `Print Assumptions`

29 declarations, from `landing_fidelity.out`. Every one reports exactly the
classical trio `constructive_indefinite_description`,
`functional_extensionality_dep` and `propositional_extensionality`, and no
declaration is closed under the global context.

| Group | Declarations |
|---|---|
| `pgl27_exec.v` | `pgl27_prior_sample` |
| `pgl27_models.v` | `pgl27_prior_exact_family` |
| `pgl27_analysis.v` | `PGL27Analysis.prior_sample`, `PGL27Analysis.prior_exact_family` |
| `pgg_analysis_manifest.v` | `pgl27_row_prior_exact` |
| `pgl27_proximity.v` | the 23 non-`Fail` declarations |
| `var_dist_supp.v` | `var_dist_fdist1_uniform` |

No axiom other than the trio appears anywhere in the run, and no `Axiom`,
`Parameter`, `Admitted` or `Abort` is introduced by any landed file. The trio
reaches even `pgl27_prior_sample`, because its distribution `pgl27P_gen` is
built through the infotheo probability layer, which carries boolp.

---

## `landing_fidelity.v`

Logical path `tableau_ext_landing3`. It `Require`s the staged copies through
`pgg_smc`, which the flags resolve to `staged/`. Every restatement is the
probe's statement verbatim and is closed by `exact: <staged name>`; no `by []`
and no `done` appears on a `published_at` or `published_row` equation.

| Section | Checks |
|---|---|
| provenance | `Check` on `pgl27_exec.pgl27_prior_sample`, `pgl27_models.pgl27_prior_exact_family`, `pgl27_analysis.PGL27Analysis.prior_sample`, `pgl27_analysis.PGL27Analysis.prior_exact_family`, `pgg_analysis_manifest.pgl27_row_prior_exact`, `var_dist_supp.var_dist_fdist1_uniform`, `pgl27_proximity.pgl27_word_proximity_cert` |
| the five additions | each ascribed at its type, including `PGL27Analysis.prior_exact_family : AnalysisModelFamily PGL27Analysis.observed` and, since fix pass 1, `PGL27Analysis.prior_sample` |
| the ideal | `pgl27_prior_viewE` restated, the witness and the program ascribed, `_armE` restated |
| the manifest row | the landed `published_row pgl27_row_prior_exact_tableau = pgl27_row_prior_exact`, closed by the landed lemma, and beside it the probe's raw-family form of the same equation, closed by `exact: erefl` |
| the distance | `pgl27_word_proximity_close` restated at its threshold premise |
| the certificate | its type ascribed, its ideal equation, all four number lemmas and the R7 pair at the probe's unprefixed statements |
| the numbers | `ipc_eps = 2^-40`, `<= 2^-39`, and a fresh `< 2^-39` showing the terminal's obligation is met strictly |
| the two rows | the program ascribed, `_rowE`, `_armE`, both `_sampledE` and the `arm_neq` |
| the theorems | `pgl27_word_view_proximity` at 2^-39, `var_dist_fdist1_uniform` at one, the refutation at the point mass |
| assumptions | the 29 `Print Assumptions` above |

The provenance test is one-sided in both directions. Each of the seven `Check`s
names a constant that exists only in this landing's text of the file that
declares it, so if production's `pgl27_exec.vo`, `pgl27_models.vo`,
`pgl27_analysis.vo`, `pgg_analysis_manifest.vo` or `var_dist_supp.vo` were
loaded, the corresponding `Check` would be an error; and no production load
path holds a `pgl27_proximity` at all.

The equation `published_row pgl27_row_prior_exact_tableau = pgl27_row_exact`
is a row-against-row conversion, measured at 48 to 96 s on this instance, and
is not stated, which one comment in the file records.

The three recorded `Fail` guards are not restated in the fidelity file: a
`Fail` declares nothing, so there is no statement to ascribe. Their fidelity
is the token check of `verify.py` and the three scratch compiles above.

---

## `verify.py`

Four checks, output in `verify.out`.

1. **Whole-file token diffs against production**, for the six files
   production already has. `pgl27_exec.v`: 1 hunk, 45 tokens.
   `pgl27_models.v`: 1 hunk, 32 tokens. `pgl27_analysis.v`: 2 hunks, 11
   tokens. `pgg_analysis_manifest.v`: 3 hunks, 98 tokens.
   `pgg_analysis_client.v`: 1 hunk, 2 tokens. `var_dist_supp.v`: 2 hunks, 251
   tokens, the moved lemma and the `lra` import, both from fix pass 1. Every
   hunk is an addition listed in E1 to E5 or in Fix pass 1; nothing in any of
   the six moved.
2. **Per-declaration token diffs against the probe.** `pgl27_prior_sample`
   1 of 1, `pgl27_prior_exact_family` 1 of 1,
   `instances/pgl27/pgl27_proximity.v` **24 of 26** and
   `lib/var_dist_supp.v` **0 of 1** token-identical. The three that are not
   are the three forced edits of E6. Each is named in the script's `EXPECTED`
   map, printed with its reason and then printed in full:
   `pgl27_row_prior_exact_rowE` (8 tokens, the right-hand side),
   `var_dist_fdist1_uniform` (27 tokens, the proof body, now reported from
   its new home) and `pgl27_cross_model_proximity` (4 tokens, the subject).
   The four renames of `RENAMED` are undone before every comparison, at the
   declaration names and at the two references inside other proofs, and each
   substitution is printed.
3. **Comment word diffs.** Against the probe, every declaration whose
   comment a landing edit or a fix-pass finding touched. The Fix pass 1
   section maps each changed passage to its finding; the largest,
   `pgl27_row_prior_exact_rowE` at 133 words, is the docstring rewritten with
   its statement and then again for L3-3 and N2.
4. **Scans.** `SpectralDecay` 0, `SpectralCert` 0, `_indist\b` 0,
   `RepricePayload` 0, `idealproximity_ceiling` 0, any abbreviation of
   "indistinguishability" 0, `apex` 0, `gate`/`gates`/`gated`/`gating` 0,
   `posit`/`posits`/`posited`/`positing` 0, `L1` 0. `ceiling`: 8 hits, all
   eight in the chain-consistency copy of `five_card_rows.v`, which is
   landing 1's text already in production and which landing 3 does not own.
   Lines over 80 bytes: four, all in chain-consistency copies
   (`five_card_analysis.v:336` at 81 bytes, from production;
   `pgg_tableau_syntax.v:334,372,403` at 101, 90 and 128 bytes, from landing
   1). None is in a landed file.

---

## `_CoqProject` placement

Production's `_CoqProject` is not edited here. One new line, and the existing
line it goes after:

| New line | Inserted after | Why |
|---|---|---|
| `instances/pgl27/pgl27_proximity.v` | `instances/s5/s5_rows.v` and `instances/kim2025/five_card_proximity.v` of landing 2, before `instances/psl211/psl211_reading_constancy.v` | it `Require`s `pgl27_rows`, `pgg_tableau`, `pgg_tableau_syntax` and `pgg_analysis_manifest`, so it goes after all four; it requires no five-card or S5 module, so its position relative to landing 2's new line is free and the design's anchor, after `instances/pgl27/pgl27_rows.v`, would also serve |

The design's section 1 anchors it after `instances/pgl27/pgl27_rows.v`
(`_CoqProject:221`). Either anchor compiles; the one above is the ruled
placement and keeps the proximity files contiguous, which is how landing 2
placed `five_card_proximity.v`.

The other five files of landing 3 are already in `_CoqProject`.

---

## The four questions, as ruled

| Q | Ruling | How the staged text carries it |
|---|---|---|
| Q1 | accepted; it supersedes the design's section-2 table | `pgl27_prior_viewE` and `pgl27_prior_exact_witness` are in `instances/pgl27/pgl27_proximity.v`, beside the program they build. `pgl27_static_obsE` is `pgl27_rows.v:159` and `ExactWitness` is `pgg_tableau.v:171`, both strictly below `pgl27_models.v`, so neither can be stated where the table put them |
| Q2 | accepted | `pgl27_cross_model_proximity`'s subject is spelled inline, `pgl27_dealt sample pgl27_exact_family`, and the un-`Fail`ed scratch compile gives the index-type failure the comment states |
| Q3 | accepted | `PGL27Analysis.prior_sample` lands, so Row 10's sample field is in facade vocabulary like every other row's |
| Q4 | changed | `pgl27_row_prior_exact_rowE` states `published_row pgl27_row_prior_exact_tableau = pgl27_row_prior_exact`, which is what every other `_rowE` in the tree states, closed by `exact: erefl` in 0.003 s. Its docstring is rewritten, and the probe's clause about `pgl27_row_exact` is dropped because no declaration in the tree states the two rows differ. `landing_fidelity.v` keeps both the landed statement and the probe's raw-family one |

The `_CoqProject` line for `instances/pgl27/pgl27_proximity.v` goes after
`instances/kim2025/five_card_proximity.v`, as ruled.

Nothing else is left open.

---

## Fix pass 1

Date: 2026-09-20. Input: `soundness-audit-landing3.md` (L3-1 to L3-11) and
`naming-audit-landing3.md` (N1 to N35), plus the orchestrator's rulings on
N3, N15 and N16. Every replacement was checked against the declaration it
describes before it was written; where the two reports proposed different
texts for one passage, one text was written that satisfies both.

The landed files are now **seven**: the six of the Layout table plus
`staged/lib/var_dist_supp.v`, which gains `var_dist_fdist1_uniform` under
ruling N16(b).

### Code changes, in full

Four, and nothing else. `verify.py` check (1) prints each as a hunk.

1. `pgl27_row_word_arms_sampledE` renamed `pgl27_row_word_families_sampledE`
   (N3). The statement is about `ab_f`, the `AnalysisModelFamily` accessor
   (`manifest/pgg_tableau.v:351-353`), and `sp_f` (`:334`); there is no
   `ab_arms` field. Sites: the declaration, the header entry, and
   `landing_fidelity.v` at the restatement, its `exact:` and its
   `Print Assumptions`.
2. `pgl27_word_uniform_ideal_not_close` renamed
   `pgl27_word_uniform_ideal_close_false` (N15). The tree spells a refutation
   with `_false`: `kim_biased_conclude_below_false`,
   `psl211_alldecks_constancy_false_word584`. Sites: the declaration, the
   header entry, the prose reference inside the second recorded `Fail`'s
   comment, and the same three lines of `landing_fidelity.v`.
3. `var_dist_fdist1_uniform` moved from `pgl27_proximity.v` to
   `staged/lib/var_dist_supp.v` (N16(b)), statement and proof body
   unchanged, with a docstring rewritten for its new home and a
   header-table entry.
4. The two `Require` lines the move forces:
   `From pgg_smc Require Import pgg_collusion_bound var_dist_supp.` in
   `pgl27_proximity.v` (the spelling `instances/kim2025/five_card_proximity.v`
   already uses) and in `landing_fidelity.v`; and
   `From mathcomp Require Import boolp reals lra.` in `var_dist_supp.v`.

**The `lra` import was measured, not assumed.** Compiling the moved lemma
into `var_dist_supp.v` with the file's existing imports gives rc 1,
`Error: The reference lra was not found in the current environment.`
(`staged/lib/var_dist_supp.v`, line 184). With `lra` added to the
`boolp reals` line the file compiles rc 0 in 4.1 s, no slow sentence.

**The recompile closure of the move is complete.** A `Require` walk over
every `.v` file outside `notes/`, `_build` and `.git` gives the reverse
closure of `lib/var_dist_supp.v` as exactly 14 modules:
`five_card_analysis`, `five_card_mixing`, `five_card_proximity`,
`five_card_rows`, `pgg_analysis_client`, `pgg_analysis_manifest`,
`pgg_tableau`, `pgg_tableau_arm_relations`, `pgg_tableau_syntax`,
`pgl27_rows`, `psl211_reading_constancy`, `psl211_rows`, `s5_rows`,
`var_dist_joint_law`. Every one of the 14 is already a staged file of this
chain, and `pgl27_proximity.v` joins them by the new `Require`, so the
chain compile recompiles the whole closure. Nothing outside it loads
`var_dist_supp`.

### Per finding

| id | final text, or the decision | declaration checked |
|---|---|---|
| L3-1 (MUST) | Guard 1's last sentence becomes "The term written here is therefore refused before any distance is considered. The same family at its own index tt is a well-typed ideal for this actual model, and what refuses it there is the distance field, which the guard below records." | `pgl27_word_proximity_cert_unit_ideal`, whose written ideal is `amf_sample pgl27_exact_family R secretP`, and guard 2, whose comment already says the distance field is what the kernel rejects at index `tt` |
| L3-1, second half | Guard 3's last sentence becomes "The Fail rejects the one term written here, on that mismatch of index types, and the mismatch is what separates the two models of this instance." Guard 2's comment already carries "The Fail rejects the one term written here, on that mismatch of types, and rules out no other term." and is unchanged. | `pgl27_cross_model_proximity`; the three guards now agree that a `Fail` refuses one written term |
| L3-2 | "The only inexact quantity is that number: the ideal and its witness are the terms the ideal row already publishes, and the secret is the word model's own first projection, typed at the carrier that witness names." | `pgl27_word_proximity_cert`, field `ipc_secret = pgl27_word_secret secretP = fun u => u.1` on `sa_sampleP (pgl27_word_sample secretP)` |
| L3-3 + N2 | One text: "The manifest's typed row for the eight-card orbit instance at the prior-indexed exact shuffle is the row this program publishes. Its five coordinates are the observed execution the program runs on, the completion level the publish terminal reaches, the model family the sample step named, and the two statuses the terminal was given. The manifest writes those coordinates in the facade's vocabulary and the program in this file's, and conversion decides the equation, so the manifest's row for this path is a claim this equation discharges rather than a table maintained beside the program." | `pgl27_row_prior_exact_rowE`, and the hand-written `Definition pgl27_row_prior_exact` of the manifest; the closing clause is `pgl27_rows.v:342-344`'s own wording, which L3-3 names |
| L3-4 | Header entry: "== below the four-seat threshold, the two models' joint laws of reading and secret are within 2^-40" | `pgl27_word_proximity_close`, premise `(#\|C\| < profile_k (instance_profile pgl27_algebra))%N` |
| L3-5 + N9 | One text. Docstring: "The certificate's number is at most 2^-39, the constant the word row publishes for the input-indistinguishability arm. It is the obligation of the terminal that concludes the proximity row at that constant, and the obligation is met strictly, the certificate's number being half of the published one." Header entry: "== the certificate's number is at most 2^-39" | `pgl27_word_proximity_le39`, conclusion `<= 2%:R^-39` |
| L3-6 + N17 | One text, in the Row 10 level justification: "Row 1 records the same instance and the same cut at the uniform secret alone, its family being indexed by the unit type. The two rows agree in their other four coordinates and differ in the model family, and the member of this row's family at the uniform prior is the member of Row 1's at tt." | `pgl27_row_exact` and `pgl27_row_prior_exact`; the last clause is the equation the soundness auditor closed `by []` |
| L3-7 | The sentence moves with the lemma to `var_dist_supp.v` and loses "beat": "Pushing two joint laws of a reading and a secret along the secret coordinate leaves the two laws of the secret and can only shorten the distance, so a proximity number between two models whose secrets are drawn from these two laws is at least one, whatever the rest of the two executions does." | `var_dist_fdist1_uniform`; the mechanism named is `var_dist_fdistmap`, the step `pgl27_word_uniform_ideal_close_false` takes |
| L3-8 | "The proximity row publishes the manifest's row for the word path, as pgl27_row_word_rowE of pgl27_rows.v says of the word program." | `pgl27_row_word_rowE : published_row pgl27_row_word_tableau = pgl27_row_word`, `pgl27_rows.v:345-347` |
| L3-9 | `landing_fidelity.v` banner becomes "The five additions to the edited instance and manifest files" and gains `Check (PGL27Analysis.prior_sample : forall (R : realType) (secretP : R.-fdist bool), SampleAdapter R pgl27_exec_plug).` | `PGL27Analysis.prior_sample := @pgl27_prior_sample`; the ascription is the one the soundness auditor compiled |
| L3-10 + N10 | One text: "== the certificate's ideal and witness are the model and the port the ideal row publishes" | `pgl27_word_proximity_cert_idealE`, a conjunction of an `ipc_ideal` equation and an `ExactIndependence (ipc_witness …) = ab_port …` equation |
| L3-11 + N12 | One text, twice. Header entry: "== the framework's reading of a coalition at the prior-indexed exact shuffle is the instance's own reading pgl27_view". Docstring: "The framework's static reading of a coalition at this model is the instance's own reading pgl27_view, with the secret left inside the sample point." | `pgl27_prior_viewE`, right-hand side `pgl27_view R C` |
| N1 (MUST) | Header paragraph three, rewritten: "Both certificates over the word model are built from one number, the walk's single-card marginal number 2^-40 of pgl27_word_marginal_bound, which rests on pgl27_word_mixing, the distance between the word walk and the uniform cut on the group. The proximity certificate carries that number and the input-indistinguishability certificate carries it added to itself, which pgl27_word_proximity_eps_halfE states. The proximity row concludes at 2^-39, the constant pgl27_row_word_branch39 publishes for the other arm, so the two rows over this model are published at one constant and the terminal's obligation is met strictly. Each of these numbers bounds a sum of absolute differences, twice the total variation distance, so a distinguisher's advantage against the published row is at most 2^-40." | all three lemmas read: `pgl27_word_marginal_bound` is `@MkShuffleMarginalBound R pgl27_M 200 (2%:R^-40) rho_word (@pgl27_endpoint_mixing R)`; `pgl27_endpoint_mixing` is proved `le_trans … pgl27_word_mixing`; `pgl27_word_mixing` bounds the distance from `rho_from_words_weighted` to `` `U pgl27_G_pos ``; `pgl27_view_mixing` is on the joint law and is no longer named here. `ic_b (pgl27_word_cert …) = pgl27_word_marginal_bound R` and `cert_eps = sw_bound_eps (ic_b …) + sw_bound_eps (ic_b …)`. Both rows are `PublishedRowAt pgl27_reprice39`, and `pgl27_reprice39 = fun R => Some (2%:R^-39 : R)` |
| N4 (MUST) | Both "This is the value a paper's table prints in the arm column …" sentences deleted. | `pgl27_row_prior_exact_armE` and `pgl27_row_word_proximity_armE`; what remains is the fixed wording production `five_card_proximity.v:394-396` carries |
| N5 | "The number is spent once, against the input-indistinguishability row's twice. Its transfer status is IdealFinite, the same the input-indistinguishability row carries, and the two certificates compare against the same ideal cut." | `pgl27_row_word_proximity`, whose `publish` clause writes `IdealFinite`; the replacement is production `five_card_proximity.v:356-359` word for word |
| N6 | Header paragraph two cut to: "The ideal's own privacy is a theorem and not an assumption. pgl27_row_prior_exact_tableau publishes the exact execution through the exact arm at every law of the dealt secret, and pgl27_word_proximity_cert_idealE says that the model the proximity certificate calls ideal is the model that row publishes, and the witness it carries for that model the row's own port." | `pgl27_row_prior_exact_tableau` and `pgl27_word_proximity_cert_idealE`. Deviation from the auditor's text: the last clause names both halves of the conjunction, so that the header and the L3-10 entry say the same thing |
| N7 | "At about 4.5e-13 of that bound it is a cryptographic separation, where the proximity certificate of Kim's one-cut model at one percent of the same bound is a weak one." | `pgl27_word_proximity_cert_eps_lt2`; production `five_card_proximity.v:311-314` says of Kim's "At one percent of that bound it is a weak separation and not a cryptographic one" |
| N8 | Docstring keeps only "The premise is the arm's threshold at this instance, four seats." The proof comment gains "The threshold is used twice, once for the ideal witness's independence and once for pgl27_view_mixing." | `pgl27_word_proximity_close`; `H3` is used at the `inde_dist_of_RV2 (pgl27_view_indep_gen secretP H3)` line and at the `pgl27_view_mixing secretP H3` line |
| N11 | "== the input-indistinguishability certificate's number is twice the proximity certificate's" | `pgl27_word_proximity_eps_halfE` |
| N13 | "== the proximity row's security statement, at 2^-39" | `pgl27_word_view_proximity`, conclusion `<= 2%:R^-39` |
| N14 | Header entry "== the certificate's number is 2^-40"; the docstring's "in closed form" also goes, to "The certificate's number is the two-hundred-letter walk's marginal number, 2^-40." | `pgl27_word_proximity_cert_epsE`, conclusion `= 2%:R^-40` |
| N18 | "It differs from pgl27_row_exact in its model family, whose index is the law of the dealt secret where the other's is the unit type, and that index is what lets a row over the word model and a row over this one be read at one law of the secret." | `pgl27_row_exact` and `pgl27_row_prior_exact`, whose families carry `amf_index pgl27_exact_family R = unit` against `amf_index pgl27_prior_exact_family R = R.-fdist bool`. Added to this table by `F10` of `audit-landing3-fix1.md`: the text landed in fix pass 1 at `staged/manifest/pgg_analysis_manifest.v:985-988`, the row did not |
| N19 | "It differs from pgl27_sample only in leaving the law of the dealt secret free, which is what a comparison with the word model at the same law requires." | `pgl27_prior_sample` against `pgl27_sample`; "coordinate" now has one sense in `pgl27_exec.v`, the coordinate law |
| N20 | "The payload type is IdealProximityPayload at the model family the Sampled value names, so the clause is checked first against that family's index type, unit against a distribution on the booleans." | `pgl27_cross_model_proximity`; the Sampled value's family is `pgl27_exact_family`, index type `unit`, against the certificate's `{fdist bool}` |
| N21 | Applied: the section banner becomes "What a certificate may name as its ideal, and what refutes one". The order of the section is unchanged, as the finding allows. | the section holds three `Fail` guards and one refutation lemma; "the proximity arm refuses" attributed to the arm what the kernel and one theorem do |
| N22 | Applied at the lemma's new home: the `var_dist_supp.v` header entry reads "== the point mass at true and the uniform law on the booleans are one apart". | `var_dist_fdist1_uniform`, stated at `fdist1 true` |
| N24 | Applied: the `(* exact: erefl and not by [] … *)` comment moves inside `Proof. … Qed.` of `pgl27_row_word_proximity_rowE`, the placement `pgl27_row_word_obs_sampledE` already uses. | `pgl27_row_word_proximity_rowE`; the code tokens are unchanged |
| N27 | Applied at the one header entry that differed: `pgl27_row_word_proximity` == "the proximity claim, concluded at 2^-39". | the row's terminal is `conclude pgl27_reprice39` |

### Declined, with reasons

| id | decision |
|---|---|
| N23 | **Declined.** The replacement `have Hpos := pgl27_pow2_40_gt0 R.` is a proof-body edit, which the fix pass's own constraint forbids and which would make `pgl27_word_uniform_ideal_close_false` a fourth expected token difference from the probe. The duplication is two one-line `have`s inside one proof and costs nothing. |
| N25 | **Kept.** Both in-proof timing comments say what was measured: which tactic on which goal shape, and against which alternative. Neither is a bare number. They sit inside `Proof`, which is where the rule puts proof engineering. |
| N26 | **Kept.** "4.5e-13" is checkable against `2^-41` in one step; the words-form the auditor offers is not, and the finding itself says nothing turns on it. |
| N28 | **No action, as the finding asks.** The proposed change is to Row 1's capability column, which landing 3 does not own. Row 10's own text already spells out "the law of prior_sample at the row's index" and does not use "prior" in the manifest's older sense. |
| N29, N30, N31, N32, N34, N35 | Clean in the audit; nothing to apply. The leading-name convention of `pgl27_exec.v`, `pgl27_models.v` and `pgl27_analysis.v`, with the em-dash, is unchanged by this pass; `pgl27_proximity.v` keeps the no-leading-name convention of `pgl27_rows.v` and `five_card_proximity.v`. |
| N33 | Applied as part of the move (D), not as a separate change: `var_dist_supp` is now imported, so the comment naming `var_dist_le2` points at an imported file. |

### Deviations from the auditors' proposed replacements

| where | deviation | reason |
|---|---|---|
| N1 | "carries it added to itself" in place of "carries it twice"; "published at one constant" in place of "read in one column". | `cert_eps` is *by definition* `sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert)`, so the addition is the exact statement; and both rows are literally `PublishedRowAt pgl27_reprice39`, where "read in one column" invokes a table outside the development, which is the class N4 deletes. |
| N6 | The closing clause names both halves of `pgl27_word_proximity_cert_idealE`. | The lemma is a conjunction; naming one half in the header and both in the index entry would be two descriptions of one lemma. |
| L3-7 | "can only shorten the distance" replaces the auditor's bare "is therefore at least one". | The lower bound needs the data-processing step; naming it makes the sentence checkable from the lemma it is attached to. |
| L3-9 | The banner reads "the edited instance and manifest files" rather than "the edited files". | After the move there are five edited production files, and `var_dist_supp.v` is a `lib/` file whose addition is restated in the theorems block and witnessed by the new provenance `Check`, not in this block. |

### Verification of fix pass 1

`python3 compile.py` with no arguments: the twenty files of the `_CoqProject`
order, every one rc 0, captured in `compile.out`. `staged/lib/var_dist_supp.v`
and `landing_fidelity.v` were recompiled once more after the last two comment
edits of `pgl27_proximity.v`'s header, both rc 0. Read the `-time` lines and
not the wall times: another session held the `rocq1` lock through part of
both runs, which is why `pgl27_proximity.v` reads 5.2 s in one run and 77.5 s
in the other while its `-time` output has no sentence over 5 s in either.

`python3 verify.py`, in `verify.out`. Check (1): six whole-file hunks, all
additions. Check (2): `pgl27_prior_sample` 1 of 1,
`pgl27_prior_exact_family` 1 of 1, `pgl27_proximity.v` **24 of 26**,
`var_dist_supp.v` **0 of 1**. The two differences inside `pgl27_proximity.v`
and the one inside `var_dist_supp.v` are the three `EXPECTED` entries, each
printed with its reason; the four `RENAMED` substitutions are printed.
Check (4): every barred pattern 0 hits; `ceiling` 8 hits and four lines over
80 bytes, all in chain copies this landing does not own, unchanged from the
run before the fix pass.

`Print Assumptions`: 29 blocks in `landing_fidelity.out`, the distinct axiom
names across all of them being `constructive_indefinite_description`,
`functional_extensionality_dep` and `propositional_extensionality`, no block
closed under the global context, no `Error` line.

Against commit `0c4a4ef`, the code-token diff of the seven landed files and
`landing_fidelity.v` is exactly: 0 tokens in `pgl27_exec.v`, `pgl27_models.v`,
`pgl27_analysis.v`, `pgg_analysis_manifest.v` and `pgg_analysis_client.v`;
255 in `pgl27_proximity.v` (the `var_dist_supp` `Require`, the two renames and
the removal of the moved lemma); 251 in `var_dist_supp.v` (the `lra` import
and the same lemma arriving); 41 in `landing_fidelity.v` (the `Require`, the
new provenance `Check`, the L3-9 ascription and the two renames at three sites
each). No other code token moved.

The header of `pgl27_proximity.v` indexes 23 entries against 23 non-`Fail`
declarations, total in both directions, and none of the three `Fail`s.


## Fix pass 2 (comments only), against `audit-landing3-fix1.md`

Applied: `F1` (MUST), `F2`, `F3`, `F4`, `F5`, `F6`, `F8`, `F9`, `F10`. `F7`
changes nothing, its own entry deferring both of its sites to a later pass.
Three files were edited, `staged/instances/pgl27/pgl27_proximity.v`,
`staged/lib/var_dist_supp.v` and `landing_fidelity.v`, in their comments
alone; the chain copies, the production tree, the extensions probe and the
other landing directories were not touched.

### Per finding

| id | final text | declaration checked | deviation from the auditor's proposal |
|---|---|---|---|
| F1 (MUST) | Guard 3's closing: "The Fail rejects the one term written here, on that mismatch of index types, and rules out no other term. The index types separate pgl27_exact_family from pgl27_word_family. The certificate this file builds, pgl27_word_proximity_cert, reads its two models at one index, the member of pgl27_prior_exact_family at secretP and the member of pgl27_word_family at that same secretP." | `amf_index` is the first field of `Record AnalysisModelFamily` (`manifest/pgg_analysis_status.v:99-105`), and the three families of `staged/instances/pgl27/pgl27_models.v:417-434` are built with `(fun _ => unit)` for `pgl27_exact_family` and with `(fun R => R.-fdist bool)` for both `pgl27_word_family` and `pgl27_prior_exact_family`. The certificate's two models are `amf_sample (ab_f (published_at pgl27_row_prior_exact_tableau)) R secretP` and `amf_sample pgl27_word_family R secretP`, read at one `secretP` | The false clause is gone and the comment ends as guard 2 does. The positive clause is added, in a form that names the two families: three families are in play in this file, so "the two families" would have no referent. It is verified by reading `amf_index`, not taken from the audit. **Corrected within the pass.** The clause was first written "The two models a proximity certificate over this instance compares are read at the one index R.-fdist bool, which pgl27_prior_exact_family carries", a false universal: guard 2 directly above writes a proximity certificate over this instance whose ideal is `amf_sample pgl27_exact_family R tt`, read at `tt`, against an actual model read at `secretP`, and guard 1 records that this ideal is well typed. The clause now speaks of `pgl27_word_proximity_cert` alone, whose ideal and actual fields are `amf_sample pgl27_prior_exact_family R secretP` and `amf_sample pgl27_word_family R secretP` (`staged/instances/pgl27/pgl27_proximity.v:292-297`) |
| F2, and the two numbers of the same docstring | `pgl27_row_word_proximity`'s docstring now reads: "The word model certified by the proximity arm and concluded at 2^-39, the constant the input-indistinguishability row of the same model publishes and the one the published reading statement pgl27_word_view_proximity carries. The certificate's own number is 2^-40, half of that. Below four seats its distance field, pgl27_word_proximity_close, puts the joint law of a coalition's reading with the dealt secret within that number of the same joint law under the prior-indexed exact execution, where the reading and the secret are independent outright, so the ideal side is the product of its two marginals. The number is spent once, against the input-indistinguishability certificate's twice. Its transfer status is IdealFinite, the same the input-indistinguishability row carries, and the two certificates compare against the same ideal cut." | `pgl27_word_proximity_cert_epsE : ipc_eps (pgl27_word_proximity_cert secretP) = 2%:R^-40`; `pgl27_word_proximity_eps_halfE`, which states `cert_eps (pgl27_word_cert secretP)` as `ipc_eps (…) + ipc_eps (…)`; `pgl27_word_proximity_le39 : ipc_eps (pgl27_word_proximity_cert secretP) <= 2%:R^-39`, the terminal's obligation; `pgl27_word_proximity_close`, the certificate's last field, concluding `<= 2%:R^-40` on the two joint laws of reading and secret under the premise `(#\|C\| < profile_k …)%N`; and `pgl27_word_view_proximity`, whose conclusion is `<= 2%:R^-39` against the product of the ideal's two marginals | The auditor's text for `F2` is "The certificate's number is spent once, against the input-indistinguishability certificate's twice." The whole docstring was reread instead of that one sentence, because "is within that number" two lines above still had 2^-39 as its antecedent, which is true but weaker than the 2^-40 the certificate's distance field proves. Each number is now named once: 2^-39 as the published constant, which `pgl27_word_view_proximity` is the statement of, and 2^-40 as the certificate's own, which `pgl27_word_proximity_close` bounds the two joint laws by. The verb `F7` raises is left as it stands |
| F3 | `landing_fidelity.v`'s header: "Every declaration landing 3 adds is restated here at the statement the probe proved, modulo four name substitutions and one proof edit: the R7 rename of pow2_40_ge1 and pow2_40_gt0 to pgl27_pow2_40_ge1 and pgl27_pow2_40_gt0, the renames of pgl27_row_word_arms_sampledE to pgl27_row_word_families_sampledE and of pgl27_word_uniform_ideal_not_close to pgl27_word_uniform_ideal_close_false, and the replacement of the four-branch first [...] of var_dist_fdist1_uniform by the one branch that fires." | `verify.py`'s `RENAMED`, four entries (`verify.py:79-84`), and `EXPECTED["var_dist_fdist1_uniform"]`, "the four-branch first [...] replaced by the branch that fires" | The auditor's "the four edits the landing forces" counts the R7 pair as one edit. The header now counts what `verify.py` prints, four name substitutions, and separates the one proof edit, so the two cannot be read against each other |
| F4 | `var_dist_supp.v`'s header: "Beside it sit the scale a published variation distance is read against, the invariance of a uniform law under an injective endomap, the fact that a pushforward charges only the image, and the distance between the point mass at true on the booleans and the uniform law there." | the file's four lemmas beside `var_dist_fdistmap_supp_inj`: `var_dist_le2`, `fdistmap_inj_uniform_id`, `fdistmap_neq0_codom`, `var_dist_fdist1_uniform` | The auditor's clause says "a point mass on the booleans". The lemma is stated at `fdist1 true`, so the enumeration says "the point mass at true", the form `N22` asked for at the index entry and `F9` applies to the banner |
| F5, site 1 | header paragraph three: "which rests on pgl27_word_mixing, the bound by that same number on the distance between the word walk and the uniform cut on the group" | ``pgl27_word_mixing : var_dist (@rho_from_words_weighted R 6 4 200 pgl27_moves Wuni) (`U pgl27_G_pos) <= 2%:R^-40`` (`instances/pgl27/pgl27_mixing.v:1049-1052`), an upper bound and not a quantity | The auditor's text is "which bounds by that same number the distance between …", a second relative clause after "which rests on". The noun phrase "the bound on the distance" is used instead, so that one wording serves all three sites |
| F5, site 2 | `pgl27_word_proximity_close`'s docstring: "pgl27_word_mixing, the bound on the cut group's own distance, carries no coalition premise, so the same bound is reachable at every coalition by a route this proof does not take." | the same statement | none beyond the shared wording |
| F5, site 3 | `pgl27_word_proximity_eps_halfE`'s docstring: "Both are read off pgl27_word_mixing, the one bound on the cut group's distance; the input-indistinguishability arm spends it once for each of the two dealt secrets it compares and the proximity arm compares one law with one law." | the same statement | none beyond the shared wording |
| F6 | header paragraph three: "so the two rows over this model conclude at one constant and the terminal's obligation is met strictly" | both rows are `PublishedRowAt pgl27_reprice39` and both reach it through `conclude pgl27_reprice39`, at `pgl27_proximity.v:390` and `instances/pgl27/pgl27_rows.v:496` | none |
| F8, header | "pgl27_word_proximity_cert_idealE says that the model the proximity certificate calls ideal is the model that row publishes, and that the port built from its witness is the row's own port." | the second conjunct is `ExactIndependence (ipc_witness (pgl27_word_proximity_cert secretP)) = ab_port (published_at pgl27_row_prior_exact_tableau) R secretP`, a port equation | none; this is production `instances/kim2025/five_card_proximity.v:78-80`'s wording for the sibling lemma |
| F8, index entry | "== the certificate's ideal is the ideal row's model, and the port built from its witness is that row's port" | the same conjunction | none |
| F8, docstring | "The model the certificate calls ideal is the model the published ideal row carries, and the port built from the certificate's witness is that row's port. Conversion decides both, so the ideal a word row is measured against is the model pgl27_row_prior_exact_tableau publishes and not a second description of it." | the same conjunction | the sentence is recast so the witness's owner is named, "the certificate's witness", the docstring being the one site where "its" would attach to the row. Production's own docstring at `five_card_proximity.v:271-274` carries the slip this finding removes and was not followed there |
| F9 | `var_dist_supp.v`'s section banner: "The point mass at true against the uniform law on the booleans" | `var_dist_fdist1_uniform`, stated at `fdist1 true`, the section's one lemma | none |
| F10 | the `N18` row above, in the fix pass 1 table | `pgl27_row_exact` against `pgl27_row_prior_exact` | the row quotes the text as it landed in fix pass 1 and adds the two `amf_index` values it rests on |
| F7 | no change | — | — |

### Verification

`python3` token check, comment-stripped and tokenized on both sides, against
commit `538862a`: `pgl27_proximity.v` 2277 tokens before and after and
identical, `var_dist_supp.v` 1321 and identical, `landing_fidelity.v` 1531 and
identical. **Zero code-token differences in all three files.** A word-level
diff of the comment text alone reports 19 changed passages in
`pgl27_proximity.v`, 4 in `var_dist_supp.v` and 2 in `landing_fidelity.v`, and
every one of them falls inside a passage this pass rewrote for `F1`, `F2`,
`F3`, `F4`, `F5`, `F6`, `F8` or `F9`. No line of the three files exceeds 80
bytes and every box line closes at column 80.

`python3 compile.py` with no argument, the whole `_CoqProject` order, because
a comment edit changes the `.vo` digest of `staged/lib/var_dist_supp.v` and
that file is first in the order. All 20 files rc 0. The `-time` sentences over
five seconds are the same four as before the pass and none of them is in an
edited file: `by vm_compute` 8.7 s in `pgl27_exec.v`, the `Require Export`
block 5.2 s in `pgg_analysis_manifest.v`, and three in
`psl211_reading_constancy.v` at 5.1 s, 6.0 s and 6.0 s. The edited files
themselves: `var_dist_supp.v` 3.9 s, `pgl27_proximity.v` 5.2 s,
`landing_fidelity.v` 29.8 s, all with no slow sentence.

Three paragraphs the rewrites lengthened were then re-wrapped to the width
their files already use, which moved no word and left the comment word-diff
above unchanged: header paragraph three and `pgl27_row_word_proximity`'s
docstring in `pgl27_proximity.v`, and header paragraph one of
`landing_fidelity.v`. Header paragraph three was wrapped twice, the first
wrap leaving three lines whose text ran into the closing `*)` with no space;
at width 74 every box line of both files closes at column 80 with at least
one space before the `*)`. The two files the re-wraps touched were compiled
again after each, last at `pgl27_proximity.v` rc 0 in 5.0 s and
`landing_fidelity.v` rc 0 in 29.5 s, both with no sentence over five
seconds. The token check above was re-run after the last re-wrap and is the
run reported.

Two sentences were then rewritten inside the pass, guard 3's last one and the
docstring of `pgl27_row_word_proximity`, for the reasons the `F1` and `F2`
rows record. The token check was re-run after them, `pgl27_proximity.v` 2277
tokens before and after and identical, `var_dist_supp.v` 1321 and identical,
`landing_fidelity.v` 1531 and identical, and the two files were compiled
again, `pgl27_proximity.v` rc 0 in 4.9 s and `landing_fidelity.v` rc 0 in
29.3 s, both with no sentence over five seconds. That is the state this
record describes.
