# Kim's two five-card rows as Tableau programs that stop at Sampled

Date: 2026-09-19

Status: spec written. Probe and audits not yet run. No plan is written until
every ledger row is GO or NO-GO with an isolating counter-probe and two audits
end in `VERDICT: GO`.

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
endpoint marginal of one card. It is not a statement about what a coalition of
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
- `five_card_row_repeated_levelE`: the manifest row's completion level is
  `Sampled`, the level the program reaches. For the biased row the
  corresponding statement is false by design, the manifest says
  `AnalysisBridged`, and the file records the gap in a comment and not in a
  lemma.
- `five_card_row_repeated_endpoint_lt`: for every seat, the endpoint marginal
  of the cut law that the repeated row samples is within $2^{-40}$ of uniform
  in variation distance. It is `kim_deal_centi_lt` carried along
  `kim_centi_cut_distE`. Its comment says that it bounds one seat's endpoint
  marginal and says nothing about a coalition or about a second secret.

Whether the biased row gets a restated bound is a probe question (K7).

## Claim ledger

| ID | Checkable claim | Passing evidence |
|---|---|---|
| K1 | `five_card_committed sample kim_centi_family` elaborates as a `Tableau Sampled`. | A `Definition` with that type and body compiles in a probe file that imports what `five_card_rows.v` imports. Compile time and memory reported. |
| K2 | The same with `kim_biased_family`. | As K1. |
| K3 | The two programs and the uniform program share their prefix as one value. | A lemma stating that the first components of the three stacks are equal, proved by `by []` or `erefl`. A mutation that samples a family typed over another observed execution is rejected, as `s5_rows.v:192` does. |
| K4 | The family each program samples is its manifest row's model. | The `modelE` lemmas compile, by conversion. If conversion is too slow or fails, the probe reports the term that blocks it and the smallest lemma that does go through. |
| K5 | The repeated row's manifest level is the level the program reaches. | `five_card_row_repeated_levelE` compiles. The manifest already checks `apr_completion five_card_row_repeated = Sampled` by `erefl`. |
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
| `kim_centi_cut_distE`, `kim_centi_witness_rhoE` | `instances/kim2025/five_card_models.v:402`, `:391` | The repeated model's cut law is the certificate bundle's weighted word shuffle at length seven. |
| `kim_deal_centi_lt` | `instances/kim2025/five_card_kim.v:646` | One seat's endpoint marginal under that shuffle is within $2^{-40}$ of uniform. |
| `five_card_colour_view_leak_bound` | `instances/kim2025/five_card_models.v:360` | A conditional mutual information is at most `kim_leak_bound eps`, under three hypotheses on `eps`. |
| `five_card_row_biased`, `five_card_row_repeated` | `manifest/pgg_analysis_manifest.v`, `:776` for the second | Manifest rows at `AnalysisBridged` and `Sampled`. |
| `ExactWitness`, `SpectralCert`, `SecurityPort` | `manifest/pgg_tableau.v:150` and above | The two arms of `certify`. |

## Soundness invariants

1. No new axiom, assumed constant, `Admitted` or `Abort`. `Print Assumptions`
   is run from the probe, not from the permanent file.
2. No statement or comment says or suggests that the repeated row, or the
   $2^{-40}$ bound, gives coalition privacy. The bound is about one seat's
   endpoint marginal under the cut law. It does not mention a secret.
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

## Acceptance condition

K1 to K6 and K9 to K11 are GO. K7 and K8 each end in a compiled fact or in a
reported obstruction. An independent soundness audit and an independent naming
audit end in `VERDICT: GO`. Findings are folded into this note before the plan.

## Out of scope

A new `certify` arm. Any edit under `manifest/`. The paper. A coalition privacy
theorem for Kim's biased or repeated cuts. The `s5_row_word` program.
