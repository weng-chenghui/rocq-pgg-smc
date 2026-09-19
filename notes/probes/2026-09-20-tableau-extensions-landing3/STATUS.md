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

Six files are LANDED: their text is the permanent text landing 3 proposes.

| Staged path | Source | What it is |
|---|---|---|
| `staged/instances/pgl27/pgl27_exec.v` | PRODUCTION plus `pgl27_prior_sample` | landed |
| `staged/instances/pgl27/pgl27_models.v` | PRODUCTION plus `pgl27_prior_exact_family` | landed |
| `staged/instances/pgl27/pgl27_analysis.v` | PRODUCTION plus two facade aliases | landed |
| `staged/manifest/pgg_analysis_manifest.v` | PRODUCTION plus Row 10, its typed row and its pins | landed |
| `staged/manifest/pgg_analysis_client.v` | PRODUCTION plus one `Check`, row count ten | landed |
| `staged/instances/pgl27/pgl27_proximity.v` | NEW; twenty-seven declarations of probe `p5_pgl27_prior_ideal.v`, `p5_pgl27_word_proximity.v`, `p5_mutations.v` | landed |

Thirteen files are CHAIN-CONSISTENCY COPIES. They are not landed by this
landing. They exist so that everything downstream of landing 2's five files
and of `instances/pgl27/pgl27_exec.v` compiles against the staged text rather
than against production's, which is what the `cp` will force in production.

| Staged path | Whose text it is |
|---|---|
| `staged/lib/var_dist_supp.v` | landing 2 |
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

All thirteen are copied from **production**, which holds landings 1 and 2
(landing 2 landed at commit `0397f8e`; the branch HEAD as this file is written
is `c8b1923`). `cmp` reports each of the thirteen byte-identical to landing 2's
staged text at commit `cb3adfc`, the text every compile before that copy had
loaded, so the change of source moved nothing.

**Any of the thirteen may move again**, and a landing-3 compile is evidence
only against the text it loaded. `restage.py` is how to redo this:

```
python3 restage.py --check     # report which of the thirteen differ, and
                               # whether the difference is code or comments
python3 restage.py             # copy them and recompile the whole chain
```

It reports each file as `unchanged`, `comments only` or `CODE CHANGED`, using
the same comment-stripped token comparison `verify.py` uses, then calls
`compile.py` with no arguments, which compiles the `_CoqProject` order: the
nineteen staged files and the fidelity file, one Rocq process at a time
through the `rocq1` lock.

Those thirteen plus the six landed are the union of two reverse closures. A
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

Twenty-seven declarations, twenty-four of them statements and three recorded
`Fail`s. Twenty-four are token-identical to the probe's; the three that are
not are the forced edits below.

| Group | Declarations | Probe source |
|---|---|---|
| the ideal at every prior | `pgl27_prior_viewE`, `pgl27_prior_exact_witness`, `pgl27_row_prior_exact_tableau`, `pgl27_row_prior_exact_armE`, `pgl27_row_prior_exact_rowE` | `p5_prior:96,112,134,144,157` |
| the distance | `pgl27_word_secret`, `pgl27_word_proximity_close` | `p5_word:111,128` |
| the certificate | `pgl27_word_proximity_cert`, `pgl27_word_proximity_cert_idealE` | `p5_word:191,206` |
| the number | `pgl27_word_proximity_cert_epsE`, `pgl27_word_proximity_eps_halfE`, `pgl27_pow2_40_ge1`, `pgl27_pow2_40_gt0`, `pgl27_word_proximity_le39`, `pgl27_word_proximity_cert_eps_lt2` | `p5_word:220,234,241,245,251,263` |
| the two rows | `pgl27_row_word_proximity`, `pgl27_row_word_proximity_rowE`, `pgl27_row_word_proximity_armE`, `pgl27_row_word_arms_sampledE`, `pgl27_row_word_obs_sampledE`, `pgl27_row_word_arm_neq` | `p5_word:285,299,307,323,335,350` |
| what the row states | `pgl27_word_view_proximity` | `p5_word:382` |
| the ideals refused | `var_dist_fdist1_uniform`, `pgl27_word_uniform_ideal_not_close` | `p5_mut:88,120` |
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
that fires.** The probe writes, at `p5_mutations.v:98-100`:

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

Determined by compiling: `staged/instances/pgl27/pgl27_proximity.v` compiles
rc 0 with it. The statement is unchanged; `verify.py` prints the 27-token
proof-body difference in full.

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
| `staged/lib/var_dist_supp.v` | 0 | 3.9 s | none |
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
| `staged/instances/pgl27/pgl27_proximity.v` | 0 | 5.3 s | none |
| `landing_fidelity.v` | 0 | 30.0 s | none |

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
| `pgl27_proximity.v` | the 24 non-`Fail` declarations |

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
| provenance | `Check` on `pgl27_exec.pgl27_prior_sample`, `pgl27_models.pgl27_prior_exact_family`, `pgl27_analysis.PGL27Analysis.prior_sample`, `pgl27_analysis.PGL27Analysis.prior_exact_family`, `pgg_analysis_manifest.pgl27_row_prior_exact`, `pgl27_proximity.pgl27_word_proximity_cert` |
| the four additions | each ascribed at its type, including `PGL27Analysis.prior_exact_family : AnalysisModelFamily PGL27Analysis.observed` |
| the ideal | `pgl27_prior_viewE` restated, the witness and the program ascribed, `_armE` restated |
| the manifest row | the landed `published_row pgl27_row_prior_exact_tableau = pgl27_row_prior_exact`, closed by the landed lemma, and beside it the probe's raw-family form of the same equation, closed by `exact: erefl` |
| the distance | `pgl27_word_proximity_close` restated at its threshold premise |
| the certificate | its type ascribed, its ideal equation, all four number lemmas and the R7 pair at the probe's unprefixed statements |
| the numbers | `ipc_eps = 2^-40`, `<= 2^-39`, and a fresh `< 2^-39` showing the terminal's obligation is met strictly |
| the two rows | the program ascribed, `_rowE`, `_armE`, both `_sampledE` and the `arm_neq` |
| the theorems | `pgl27_word_view_proximity` at 2^-39, `var_dist_fdist1_uniform` at one, the refutation at the point mass |
| assumptions | the 29 `Print Assumptions` above |

The provenance test is one-sided in both directions. Each of the six `Check`s
names a constant that exists only in this landing's text of the file that
declares it, so if production's `pgl27_exec.vo`, `pgl27_models.vo`,
`pgl27_analysis.vo` or `pgg_analysis_manifest.vo` were loaded, the
corresponding `Check` would be an error; and no production load path holds a
`pgl27_proximity` at all.

The equation `published_row pgl27_row_prior_exact_tableau = pgl27_row_exact`
is a row-against-row conversion, measured at 48 to 96 s on this instance, and
is not stated, which one comment in the file records.

The three recorded `Fail` guards are not restated in the fidelity file: a
`Fail` declares nothing, so there is no statement to ascribe. Their fidelity
is the token check of `verify.py` and the three scratch compiles above.

---

## `verify.py`

Four checks, output in `verify.out`.

1. **Whole-file token diffs against production**, for the five files
   production already has. `pgl27_exec.v`: 1 hunk, 45 tokens.
   `pgl27_models.v`: 1 hunk, 32 tokens. `pgl27_analysis.v`: 2 hunks, 11
   tokens. `pgg_analysis_manifest.v`: 3 hunks, 98 tokens.
   `pgg_analysis_client.v`: 1 hunk, 2 tokens. Every hunk is an addition listed
   in E1 to E5; nothing in any of the five moved.
2. **Per-declaration token diffs against the probe.** `pgl27_prior_sample`
   1 of 1, `pgl27_prior_exact_family` 1 of 1, and
   `instances/pgl27/pgl27_proximity.v` **24 of 27** token-identical. The three
   that are not are the three forced edits of E6. Each is named in the script's
   `EXPECTED` map, printed with its reason and then printed in full:
   `pgl27_row_prior_exact_rowE` (8 tokens, the right-hand side),
   `var_dist_fdist1_uniform` (27 tokens, the proof body) and
   `pgl27_cross_model_proximity` (4 tokens, the subject). The R7 rename is
   undone before every comparison, at the declaration names and at the two
   references inside other proofs, and the substitution is printed.
3. **Comment word diffs.** Seven differences, each listed with before and
   after in E1, E2 and E6 and each classified. The largest,
   `pgl27_row_prior_exact_rowE` at 106 words, is the docstring rewritten with
   its statement.
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
