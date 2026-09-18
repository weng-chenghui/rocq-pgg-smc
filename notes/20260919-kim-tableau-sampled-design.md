# Kim's two five-card rows as Tableau programs that stop at Sampled

Date: 2026-09-19

Status: probe run on 2026-09-19 and verified by the main session's own compile.
K1 to K11 are GO, and K8 ends in the compiled conclusion that neither arm can
be supplied for the biased row. The audits are next. No plan is written until
two audits end in `VERDICT: GO`.

## Problem

The manifest carries three rows for the five-card development:
`five_card_row_uniform`, `five_card_row_biased` and `five_card_row_repeated`.
Only the first is written as a Tableau program
(`five_card_row_uniform_tableau` in `instances/kim2025/five_card_rows.v`). The
header of that file says so: the manifest carries two further five-card rows,
the biased and the repeated ones, and neither is written as a program here.

This hides the one fact a reader of the paper most needs about den Boer's
protocol and Kim's analysis of it. The three rows run the same committed
execution. They differ in one line, the probability model that is sampled, and
in how far the security mathematics then reaches. A reader who sees only the
manifest table sees three unrelated rows. A reader who sees the programs sees
one prefix and three continuations.

The risk in fixing this is overclaiming. Kim's repeated-cut result bounds the
endpoint marginal of one starting position. It is not a statement about what a coalition of
seats learns. A program that carried it to the `AnalysisBridged` level would
make endpoint mixing look like coalition privacy.

## Decisions (user, 2026-09-18 and 2026-09-19)

1. Add a real definition, `five_card_row_repeated_tableau : Tableau Sampled`,
   equal to `five_card_committed sample kim_centi_family`. The row stops at
   `Sampled`.
2. Do not extend the Tableau with a `certify EndpointMarginal` arm. It would
   change the completion interface and would let an endpoint bound reach the
   level that means coalition privacy.
3. The $2^{-40}$ bound is a Proposition placed after the Tableau in the paper.
   No paper file is edited by this work.
4. Programs are changed, and the result is merged into `main`.
5. Add two link lemmas once a probe confirms them: the row's family and level
   are the manifest row's, and the endpoint bound is restated on the law the
   row samples.
6. The biased row is handled too.
7. Compile only related files, one at a time. `five_card_rows.v` has no
   importer, so it is the only file to compile.

Default taken by the main session for the biased row, to be overturned by the
user if wrong. The manifest places `five_card_row_biased` at `AnalysisBridged`
on the strength of `five_card_colour_view_leak_bound`, a bound on a conditional
mutual information stated on Kim's own sample space. The `certify` statement
has two arms. `ExactIndependence` asks for exact independence of the static
coalition observation from a secret, and `SpectralDecay` asks for a variation
distance certificate with an ideal law whose coalition pushforwards do not
depend on the input. A mutual information bound is neither. The biased row is
therefore also written as a program that stops at `Sampled`, and the file says
plainly that the manifest level of that row rests on a theorem that no
`certify` arm carries. This is the situation `instances/s5/s5_rows.v` already
records for `s5_row_word`. No arm is added.

## Flow

The running value is the completion level.

```
flow five_card_kim_rows                                          // level: none
prefix   five_card_committed            existing, Tableau Observed          // Observed
row uniform    prefix sample five_card_uniform_family                       // Sampled
                      certify ExactIndependence five_card_exact_witness     // AnalysisBridged
                      |> publish StaticExecutedOnly BaselineClassicalOnly   // published row
row biased     prefix sample kim_biased_family                              // Sampled, stops
row repeated   prefix sample kim_centi_family                               // Sampled, stops
link     the family each Sampled row samples is its manifest row's model
outside  repeated: one seat's endpoint marginal below 2^-40, on the row's cut law
           by kim_centi_cut_distE [interface] and kim_deal_centi_lt [interface]
outside  biased: five_card_colour_view_leak_bound, cited on Kim's sample space
outside  no new certify arm, no edit to manifest/, no paper text
```

Roles. Object: `five_card_committed`. Steps: the three `sample` lines, and for
the uniform row `certify` and `publish`. Observation change: none new.
Invocation of an assumption: none, all three models are exact laws.
Post-processing outside the flow: the two bounds.

Structure. The Tableau is a parameterised monad indexed by completion level
before and after a statement. `tableau_start` is the unit and `tableau_bind`,
written `;;;`, is the bind. The three rows apply `sample_step` to one prefix
value with three payloads. No new DSL is needed, the existing one is the
subject.

## Pinned carrier

`five_card_committed : Tableau Observed`
(`instances/kim2025/five_card_rows.v:123`). Both Kim families have the type
`AnalysisModelFamily five_card_observed`
(`instances/kim2025/five_card_models.v:435`, `:443`), the type of
`five_card_uniform_family` (`:426`), and are unit-indexed. The real field is
abstract in every statement.

## Proposed declarations, all in `instances/kim2025/five_card_rows.v`

```coq
Definition five_card_row_biased_tableau : Tableau Sampled :=
  five_card_committed
    sample kim_biased_family.

Definition five_card_row_repeated_tableau : Tableau Sampled :=
  five_card_committed
    sample kim_centi_family.
```

Link lemmas. Their exact statements are settled by the probe, because they
depend on how a family is projected out of a `Tableau Sampled` and on the
dependent type of `apr_model`.

- `five_card_row_biased_modelE` and `five_card_row_repeated_modelE`: the family
  the program samples is the model of the manifest row, and both rows name the
  same observed execution. By conversion if possible.
- `five_card_row_repeated_at_manifest_level`: the repeated program ascribed
  the type `Tableau (apr_completion five_card_row_repeated)`, which makes the
  manifest's level term and the program's level index one term. No separate
  `levelE` lemma is landed for this row, because the ascription forces it.
- `five_card_row_biased_levelE`: the manifest's completion level for the
  biased row is `AnalysisBridged`. It stands beside the rejected ascription
  `five_card_row_biased_at_manifest_level`, a `Fail`, and the two are the two
  halves of the level gap of that row.
- `five_card_row_s5_family`, a `Fail`: a program sampling a family typed over
  another instance's observed execution is rejected where it is written.
- `five_card_row_repeated_endpoint_lt`: for every starting position, the law
  of its image under the cut that the repeated row samples is within $2^{-40}$
  of the uniform law on the five card positions, in variation distance. It is `kim_deal_centi_lt` carried along
  `kim_centi_cut_distE`. Its comment says that it bounds one starting
  position's endpoint marginal and names no seat, no set of seats and no
  secret. The file does not prove the identification of seats with card
  positions, so the statement is about positions.

- `kim_centi_small` and `five_card_row_biased_leak_bound`: the smallness side
  condition at bias one hundredth, and the ceiling on the conditional mutual
  information between the inputs and the executed colour reading given the
  secret, under the law the biased row samples (K7).

## Claim ledger

| ID | Checkable claim | Passing evidence |
|---|---|---|
| K1 | `five_card_committed sample kim_centi_family` elaborates as a `Tableau Sampled`. | A `Definition` with that type and body compiles in a probe file that imports what `five_card_rows.v` imports. Compile time and memory reported. |
| K2 | The same with `kim_biased_family`. | As K1. |
| K3 | The two programs and the uniform program share their prefix as one value. | A lemma stating that the first components of the three stacks are equal, proved by `by []` or `erefl`. A mutation that samples a family typed over another observed execution is rejected, as `s5_rows.v:192` does. |
| K4 | The family each program samples is its manifest row's model. | The `modelE` lemmas compile, by conversion. If conversion is too slow or fails, the probe reports the term that blocks it and the smallest lemma that does go through. |
| K5 | The repeated row's manifest level is the level the program reaches, and the biased row's is not. | `five_card_row_repeated_at_manifest_level` compiles, the repeated program being accepted at the type `Tableau (apr_completion five_card_row_repeated)`. The same ascription for the biased program is rejected with a level mismatch, and `five_card_row_biased_levelE` states the manifest's level for that row. |
| K6 | The endpoint bound holds on the cut law the repeated row samples. | `five_card_row_repeated_endpoint_lt` ends in `Qed`, from `kim_centi_cut_distE` and `kim_deal_centi_lt`, with `Print Assumptions` reported. A mutation with the bound tightened to $2^{-41}$, or with the seat replaced by a pair of seats, must fail, so that the lemma is shown to say what its comment says. |
| K7 | Whether `five_card_colour_view_leak_bound` can be restated on the law the biased row samples in a few lines. | Either a compiled restatement, or a report of the exact obstruction: the theorem lives on `five_card_leakage.Omega` with Kim's input distribution, the row samples `kim_single_sample`. If it is not short, the row's comment cites the theorem and the manifest's three bridge lemmas and no lemma is added. |
| K8 | Neither `certify` arm can be supplied for the biased row from existing theorems. | The probe states which field of `ExactWitness` and which fields of `SpectralCert` have no existing theorem behind them, by grep and by attempting the record. It does not try to prove a new security theorem. |
| K9 | `five_card_rows.v` has no importer, so nothing else recompiles. | The reverse-dependency closure from `.Makefile.rocq.d`, in Python. |
| K10 | The new names collide with nothing and follow the file's conventions. | Whole-word search of the tree and of installed infotheo and mathcomp. The existing program is `five_card_row_uniform_tableau : PublishedRow`; the new ones share the suffix at a different type, and the naming audit judges whether that reads correctly. |
| K11 | The file header is true after the change. | The sentence saying that neither further row is written as a program is replaced, and the header states which rows stop where and why. |

## Cited objects

| Object | File | Required statement shape |
|---|---|---|
| `five_card_committed` | `instances/kim2025/five_card_rows.v:123` | `Tableau Observed`, the shared prefix. |
| `five_card_row_uniform_tableau`, `five_card_row_uniform_rowE` | same file, `:286`, `:295` | The existing program and its link to the manifest row by conversion. |
| `sample_step`, the `sample` notation | `manifest/pgg_tableau.v:502`, `manifest/pgg_tableau_syntax.v:366` | From an observed stack and a family over its observed execution to `Tableau Sampled`. |
| `kim_biased_family`, `kim_centi_family` | `instances/kim2025/five_card_models.v:435`, `:443` | Unit-indexed families over `five_card_observed`. |
| `kim_centi_cut_distE` | `instances/kim2025/five_card_models.v:402` | The repeated model's cut law is the certificate bundle's weighted word shuffle at length seven. |
| `kim_deal_centi_lt` | `instances/kim2025/five_card_kim.v:646` | One seat's endpoint marginal under that shuffle is within $2^{-40}$ of uniform. |
| `five_card_colour_view_leak_bound` | `instances/kim2025/five_card_models.v:360` | A conditional mutual information is at most `kim_leak_bound eps`, under three hypotheses on `eps`. |
| `five_card_row_biased`, `five_card_row_repeated` | `manifest/pgg_analysis_manifest.v:766`, `:776` | Manifest rows at `AnalysisBridged` and `Sampled`. |
| `ExactWitness`, `SpectralCert`, `SecurityPort` | `manifest/pgg_tableau.v:114`, `:131`, `:149` | The two arms of `certify`. |
| the completion levels | `manifest/pgg_analysis_status.v:55-59` | `AnalysisBridged` adds a theorem about the sampled distribution and the observer. Any security, leakage, mixing or limitation theorem meets it. The Tableau admits a row to the same level only through one of the two arms. |

## Soundness invariants

1. No new axiom, assumed constant, `Admitted` or `Abort`. `Print Assumptions`
   is run from the probe, not from the permanent file.
2. No statement or comment says or suggests that the repeated row, or the
   $2^{-40}$ bound, gives coalition privacy. The bound is about one starting
   position's endpoint marginal under the cut law. It does not mention a secret.
3. No statement or comment says that the biased row is certified by the
   Tableau. Its program stops at `Sampled`. The manifest's higher level for it
   is attributed to the theorem that carries it.
4. Nothing under `manifest/` changes. No `certify` arm is added and no
   completion level is redefined.
5. The uniform row, its witness and `five_card_row_uniform_rowE` are untouched.
6. The three programs share one prefix value, and this is a compiled fact, not
   a layout convention.
7. Probe files are kept and never imported by a permanent file.

## Probe artifacts

Directory `notes/probes/2026-09-19-kim-tableau-sampled/`, logical path
`kim_tableau_sampled_probe`: `kim_rows_probe.v` for K1 to K6 with mutations,
`kim_biased_arms_probe.v` for K7 and K8, `five_card_rows_landing.v`, a full
copy of the permanent file with the additions, `_CoqProject`, `STATUS.md`, and
the two audit reports.

## Probe results, 2026-09-19

Probe directory `notes/probes/2026-09-19-kim-tableau-sampled/`. All four files
compile one at a time in 4 to 7 s under 1.9 GB, recompiled by the main session.
`kim_fidelity.v` reports the three `boolp` axioms for ten of the eleven new
declarations and `Closed under the global context` for
`five_card_row_biased_levelE`.

- K1, K2. Both definitions elaborate in no measurable time.
- K3. `five_card_row_repeated_prefixE` and `five_card_row_biased_prefixE` state
  that the algebra, the run parameters and the observed execution of each
  program are those of `five_card_committed`, and close by `by split`. The
  observed execution carries the three run facts as fields, so three conjuncts
  pin five components. A program sampling `S5Analysis.rand_family` is rejected
  with a type error naming `FamPayload (tableau_at five_card_committed)`.
- K4. `sp_f (tableau_at t) = apr_model row` closes by conversion for both rows.
- K5, stronger than this note asked. The repeated program is accepted at the
  type `Tableau (apr_completion five_card_row_repeated)`, which makes the
  manifest's level term and the program's level index one term. The same
  ascription for the biased program is a recorded `Fail`, and
  `five_card_row_biased_levelE : apr_completion five_card_row_biased =
  AnalysisBridged` is the positive fact beside it. The level gap of the biased
  row is therefore a compiled fact, and the comment only explains it. A
  separate `five_card_row_repeated_levelE` is not landed, because the
  ascription already forces it and the manifest checks that equation itself.
- K6. `five_card_row_repeated_endpoint_lt` is
  `by rewrite kim_centi_cut_distE; exact: kim_deal_centi_lt`, stated through
  `sa_cut_dist (amf_sample kim_centi_family R tt)`. `kim_centi_witness_rhoE`
  is not needed. The bound tightened to $2^{-41}$ and the version over a pair
  of seats both fail at the `exact:` step. Those two mutations stay in the
  probe, because they are `ltac:` terms inside a `Fail`, which does not read
  as a permanent file's idiom.
- K7, GO in three lines. The law the biased row samples is Kim's input law by
  `erefl`, so `five_card_colour_view_leak_bound` already lives on it and no
  bridge lemma is used. The one cost is a side condition the tree did not
  have: `0 < 5%:R^-1 - `|1 / 100|`, the smallness condition of
  `kim_input_private`. It lands as `kim_centi_small`, one line of arithmetic
  of the shape of `kim_centi_lt`, `kim_centi_gt` and `kim_centi_spec`. The
  landed bound is `five_card_row_biased_leak_bound`: the conditional mutual
  information between the inputs and the executed colour reading given the
  secret is at most `kim_leak_bound (1 / 100)`. The tree has no lemma saying
  that this number is positive, so no comment says so.
- K8, the answer is no. For the exact arm the only missing field is
  `ew_indep`, and no independence statement in the tree is made under Kim's
  biased law. For the spectral arm `sc_b`, `sc_Hd` and `sc_ideal` can be built
  and were compiled one by one in the probe, while `sc_close`, a variation
  distance on the cut group, and `sc_const`, constancy of a coalition's reading
  of the ideal law in the run argument, have nothing behind them. The first is
  the gap `s5_rows.v` records for `s5_row_word`. The three buildable fields
  stay in the probe.
- K9. The reverse-dependency closure of `five_card_rows.v` is empty.
- K10. None of the eleven new names occurs in the tree or in installed
  infotheo or mathcomp.
- K11. The header sentence is replaced, the title line now speaks of three
  rows, and the diff against the production file removes four lines and adds
  197.

Decisions taken by the main session after the probe:

- `kim_centi_small` lands in `five_card_rows.v`, above its one use.
  `five_card_kim.v`, where the other three side conditions at this bias live,
  has 20 importers, and the user's rule is to compile only related files. Its
  natural home is recorded as a note for the next time that file is edited.
- The landing copy gains one import, `kim_input_privacy`, for `kim_inputs`,
  `kim_secret` and `kim_leak_bound`. `five_card_models`, already imported,
  imports it, so the build graph gains no edge.
- Landed mutations: the program sampling another instance's family, and the
  biased program at the manifest's level. This file already carries one `Fail`.

## Audit results, 2026-09-19

Soundness audit (`soundness-audit.md` in the probe): GO. A `Tableau Sampled`
proves run correctness and that the executed coalition reader is the static
one, and asserts nothing about security. `modelE` pins the law: the manifest
row's model evaluates by conversion to the adapter that the manifest's bound
theorems name. Neither bound is vacuous. By the auditor's computation from the
definition, not by a compiled lemma, `kim_leak_bound (1 / 100)` is about 0.0091
bits against a trivial ceiling of about 1.19 bits, and $2^{-40}$ stands against
a trivial ceiling of 2. No lemma proves the leak bound positive and no comment
says so. The statement that neither arm can be supplied is scoped to existing
theorems and is conservative, since exact independence under a biased cut is
expected to be false.

Naming audit (`naming-audit.md`): NO-GO on two items. The first paragraph of
the file header, which the landing left untouched, says that every statement
below is about a coalition of at most one seat and that input privacy is not
what the file states. Both sentences become false once
`five_card_row_biased_leak_bound` lands, which holds at any list of card
positions and is Kim's input privacy bound. The soundness audit raised the same
paragraph. The second item is the mutation's name, a figure of speech; it
lands as `five_card_row_s5_family`.

Folded in:

- The header paragraph is rewritten so that its restriction to one seat covers
  the coalition statements only, and it names the biased bound as a ceiling on
  input privacy at any list of card positions.
- The level gap of the biased row is explained by the two criteria for one
  constructor. The manifest admits a row to `AnalysisBridged` on any theorem
  about the sampled distribution and the observer. The Tableau admits it only
  through an arm of `certify`. Each arm produces a theorem of that same kind,
  so the Tableau's criterion is the stricter of the two, and the gap at this
  row is the manifest's criterion met by a theorem no arm takes. The exposition sits in the
  header, and the biased program's comment is shortened to point at it.
- The endpoint bound is worded for a starting position, not a seat.
- `five_card_row_biased_prefixE`, `five_card_row_biased_modelE` and
  `five_card_row_biased_levelE` get statement comments that say what they are
  for.
- `prefixE` states three conjuncts. That the observed execution carries the
  three run facts is a remark about the record, not part of the statement, and
  the comment says no more than the statement.

Two wordings elsewhere in this note keep the word seat on purpose. "One seat's
endpoint marginal" in the Cited objects row for `kim_deal_centi_lt` and "a pair
of seats" in ledger row K6 describe the upstream lemma and a probe mutation,
both outside the landed text, and are left as their sources write them.

Naming round 2 stopped on one sentence of the passage just described, which
called the two levels one constructor. `Sampled` and `AnalysisBridged` are two
constructors, and the point is that `AnalysisBridged` has two admission
criteria. The same round asked that the header speak of the uniform row where
it enumerates five statements, since the two Kim programs have two each, and
that the repeated program's comment stop saying seat.

Kept, by the naming audit's judgement: the `_tableau` suffix at the type
`Tableau Sampled`, the name `five_card_row_repeated_at_manifest_level`, the
asymmetry between an ascription for one row and a lemma for the other, the
suffixes `_endpoint_lt` and `_leak_bound` that echo their source lemmas, and
`kim_centi_small` with its name and its home.

## Acceptance condition

K1 to K11 are GO, K8 in the sense that its negative conclusion is compiled. An independent soundness audit and an independent naming
audit end in `VERDICT: GO`. Findings are folded into this note before the plan.

## Out of scope

A new `certify` arm. Any edit under `manifest/`. The paper. A coalition privacy
theorem for Kim's biased or repeated cuts. The `s5_row_word` program.
