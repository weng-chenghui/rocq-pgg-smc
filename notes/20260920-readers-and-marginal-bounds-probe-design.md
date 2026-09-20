# A second reader at Sampled, and one-seat marginal bounds: spec for a probe (2026-09-20)

Tracker steps 4.1 and 4.4, one spec because the second is an instance of the
first. Parent: `notes/20260919-tableau-three-extensions-probe-design.md`, section
"What this batch leaves, by phase", groups "Observers" and "One-position
marginal bounds". The owner is away; every design decision below is the main
session's, with its reason, and can be overturned.

## The problem

Every proposition the Tableau states is about ONE reader: a coalition's static
reading, `static_coalition_obs C x g`, which the link lemma of `Sampled`
(`sampled_viewE_prop`) identifies with the executed coalition view. The tree
proves theorems about other readers, and none of them has a place:

1. the content trace of a coalition: `pgl27_coalition_trace_secrecy`
   (`instances/pgl27/pgl27_trace.v`, an entropy equality at the exact model),
   `pgl27_word_trace_indistinguishability` (`pgl27_word_privacy.v`, at most
   2^-39 between two dealt secrets at the word model),
   `pgl27_exec_trace_indistinguishability` (`pgl27_models.v`, the same on the
   executed trace);
2. one seat's endpoint: `s5_exec_endpoint_bound` (`s5_models.v`, the executed
   seat law against an ideal reading) and `five_card_repeated_endpoint_lt`
   (`five_card_tableau_sampled.v`, one position of the cut law against
   uniform). The manifest puts `s5_word_path` at `AnalysisBridged` on the first,
   while its header says that no endpoint marginal bound is a privacy or
   security capability;
3. a list of positions with the output given (`five_card_biased_leak_bound`, a
   conditional mutual information), and coalitions at or above the threshold
   (`pgl27_view_leakage_le`).

Why it matters: a reader of the manifest cannot tell which reader a published
number is about. The word program's 2^-39 is about the coalition's reading; the
tree also proves 2^-39 about the trace, which is a different and in general
finer reader, and nothing says how the two relate.

## Decision: a proposition is stated AT a reader; the phase does not change

`Sampled` keeps its meaning (a model is named; the executed coalition view is
its static reading). A second reader does not enter the program's stack: that
would change `StackAt Sampled`, and with it every program. Instead:

- **A static reader** of an execution: a family of functions
  `C -> run argument -> cut -> T C` into finite types. The coalition's reading
  is the canonical one. The content trace is a second. One seat's content is a
  third (the coalition reading at a singleton, or `ex_content_obs` directly).
- **The propositions of the security properties are generalised over the
  reader**, as new definitions beside the existing ones, and the existing ones
  are their instances at the canonical reader BY CONVERSION (ledger R2): so
  nothing the framework states today changes, and a theorem about the trace
  becomes "the input-indistinguishability proposition at the trace reader".
- **Post-processing**: if reader `r'` is a function of reader `r`, the
  input-indistinguishability proposition at `r` gives it at `r'` with the same
  number (data processing, `var_dist_fdistmap`). This is the statement that
  relates the trace's 2^-39 to the reading's.
- **An executed reader's link** is a lemma of the same shape as the `Sampled`
  link lemma, stated for that reader; where the tree already proves it (the
  executed trace against the static trace at PGL(2,7)) it is cited, not
  reproved.
- **One-seat marginal bounds (4.4) are NOT security evidence** and get no
  constructor of `SecurityEvidence`. They are a proposition of their own,
  `SeatMarginalPropAt`: the law of one seat's reading is within `c` of a named
  ideal law. It mentions no coalition, no second run argument and no secret,
  and its statement comment says so. The two theorems of item 2 are its
  instances. The manifest's level for `s5_word_path` is the manifest's own
  notion of a transfer at the observer level; the Tableau states no security
  property there, and the spec's landing records that in the S_5 phase files
  rather than changing the manifest.
- **Out of scope, with the reason**: item 3. A conditional mutual information
  and a monotonicity in the coalition are about HOW MUCH is learned, a measure
  of leakage, not about WHO reads; they need a fourth kind of proposition, and
  the Tableau has no word for a leakage measure at any phase.

Rejected: a new statement `read r` at `Sampled` that adds a link lemma to the
accumulated proposition (changes `StackProp Sampled`, the type of every
program, for three theorems at one instance); a fourth security property for
marginal bounds (contradicts the manifest's own header).

## Pinned carrier

`R : realType`, `A : PGGAlgebraic`, `E : ExecutionParams A`,
`sa : SampleAdapter R (instance_exec E)`; a reader's value type is a `finType`
depending on the coalition. Instances: PGL(2,7) exact and word models, S_5 word
model, five-card seven-cut model.

## Claim ledger

| id | Claim | Passing means |
|---|---|---|
| R1 | `StaticReader E` (record: `sr_T : {set seats} -> finType`, `sr_read : forall C, ex_inputT E -> cut -> sr_T C`) typechecks; the canonical `coalition_reading_reader` with `sr_read := static_coalition_obs` | `Definition`s; the type of `static_coalition_obs C x g` is a `finType` at the pinned carrier (print it) |
| R2 | `ReaderIndistinguishabilityPropAt sa r c` (as `IndistinguishabilityPropAt` with `sr_read r C` in place of `static_coalition_obs C`); at the canonical reader it equals `IndistinguishabilityPropAt cert c` for every `cert` | equation closed by conversion (`erefl`/`reflexivity`); mutation: at another reader the equation is a type error or is refused, message read |
| R3 | Post-processing: `(forall C x g, sr_read r' C x g = f C (sr_read r C x g)) -> ReaderIndistinguishabilityPropAt sa r c -> ReaderIndistinguishabilityPropAt sa r' c` | `Qed` from `var_dist_fdistmap`, `fdistmap_comp`; mutation: without the factorisation hypothesis the proof must fail |
| R4 | The PGL(2,7) trace reader: `pgl27_trace_reader` with `sr_read := pgl27_coalition_trace`-shaped static function; `pgl27_word_trace_indistinguishability` restated as `ReaderIndistinguishabilityPropAt (word model) pgl27_trace_reader 2^-39` | `Qed` by the existing theorem, no new mathematics; record how the threshold `#|C| <= 3` meets `#|C| < profile_k` |
| R5 | Which way the factorisation goes at PGL(2,7): is the coalition's reading a function of the trace, the trace of the reading, or neither? | the true direction(s) compiled as R3's hypothesis; if neither, say so with the obstacle. If the reading is a function of the trace, R3 gives the word program's reading proposition at 2^-39 from the trace theorem: compile that corollary and compare with what `indistinguishability_tail` gives |
| R6 | Exact independence at a reader: `ReaderExactPropAt sa r secret` (the reader's law independent of the secret, below the threshold); canonical instance equals the framework's exact-independence proposition's independence conjunct; the trace instance from `pgl27_coalition_trace_secrecy` | the canonical equation by conversion or a one-line lemma; for the trace, the bridge from the entropy equality to independence: find it in the tree (`pgl27_view_secrecy`'s proof uses one) or stop at the statement and report what is missing |
| R7 | The executed trace's link at PGL(2,7): executed content trace = static trace along the word adapter | cite the existing lemma if it exists (search `pgl27_models.v`, `pgl27_exec.v`); else state it and report, do not prove a long new lemma in the probe |
| R8 | `SeatMarginalPropAt sa i ideal c := var_dist (sa_seat_dist sa 0 i) ideal <= c`; `s5_exec_endpoint_bound` is an instance; `five_card_repeated_endpoint_lt` is an instance of its cut-law form (one position of the cut law against uniform): state the form that fits each, and whether one definition covers both | two `Qed`'d restatements; if two definitions are needed, say why |
| R9 | Vacuity and honesty: `SeatMarginalPropAt` at `c := 2` holds for every model and ideal (`var_dist_le2`); it implies no proposition of a security property: exhibit why (it has no second run argument and no secret) as a recorded type-level fact, not as prose | the at-two lemma `Qed`; a `Fail` that uses a seat-marginal proof where security evidence is expected, message read |
| R10 | No axiom beyond each cited theorem's own | `Print Assumptions` of R4, R5's corollary, R8 |

## Soundness invariants

- Pure additions: no existing definition, statement or name changes;
  `IndistinguishabilityPropAt` and the exact-independence proposition stay as
  they are, and R2/R6 prove they are instances.
- `var_dist` is the sum of absolute differences, twice the literature's total
  variation: an advantage is at most half of any number here.
- A proposition at a finer reader is the stronger statement; the comments say
  which reader is finer only where R5 compiled it.
- `SeatMarginalPropAt` is about one seat and one run law; no coalition, privacy
  or security statement follows from it.

## Procedure

Probe directory `notes/probes/2026-09-20-readers-and-marginal-bounds/`:
`r_framework.v` (R1, R2, R3, R6 framework part, R8 definition, R9),
`r_pgl27.v` (R4, R5, R6 trace part, R7), `r_marginals.v` (R8 instances),
`LEDGER.md`. Two audits before a landing plan. Landing homes, if GO: a new
`manifest/pgg_tableau_readers.v` above `manifest/pgg_tableau.v` (so the
framework file does not grow), instance restatements in the instances'
`tableau/` analysis-bridged or sampled files.

## Results of the probe and of the soundness audit; scope cut; landing plan (2026-09-21)

Probe: `notes/probes/2026-09-20-readers-and-marginal-bounds/` (`LEDGER.md`), ten
rows compiled, recompiled from source by the main session. Audit:
`audit-soundness.md` (GO for a plan with the scope cut; P4, P5, P6, P12, P15,
P18, P20 are the findings that change this spec). The owner is away; the
decisions are the main session's.

### What the probe and the audit established

1. At PGL(2,7) the content trace and the coalition's reading are one reader
   under two names: `pgl27_coalition_trace C = pgl27_view R C` and
   `static_coalition_obs C s g = pgl27_view R C (s, g)`, and the tree proved
   the trace theorem FROM the reading theorem by that equality. The two
   published 2^-39 were one number before this probe. The spec's motivating
   instance for a second reader is not one (P4, P5).
2. A genuinely different reader with a proved theorem exists and the spec
   missed it: the PSL(2,11) colour view, `psl211_colour_view C`, strictly
   coarser than the card-identity reading, with `psl211_colour_view_indep`
   below the threshold of six and `psl211_colour_view_dep_k6` at it
   (`instances/psl211/psl211_secrecy.v`). Its model `psl211P` has no sample
   adapter (P20, P21).
3. `ReaderExactPropAt` at the canonical reader is the `ew_indep` FIELD of
   `ExactWitness`, not the independence conjunct of the exact-independence
   proposition, which speaks of the executed view; the two differ by the
   `Sampled` link lemma. This spec's row R6 was worded wrongly (P6, P7).
4. The two "refusals" of R9 show only that two definitions have different
   types. The statement that says "no security property follows from a marginal
   bound" is a negative with a countermodel; the S_5 phase file already argues
   one in prose (one seat's reading law moves with the secret while that seat
   has a small marginal bound) (P12, P23).
5. The manifest's level for `s5_word_path` is consistent with the manifest's
   own definition of the level, and the S_5 sampled phase file already records
   that the word model has no program. Nothing is owed there (P17, P18).

### Decisions

- **Landed now (tracker 4.4):** `SeatMarginalPropAt`, `CutMarginalPropAt`, their
  vacuity at two, the two instances (`s5_exec_endpoint_bound` with its S_5
  axiom; the five-card bound, with the statement comment saying that the cited
  theorem is strict and the proposition is at `<=`), and ONE lemma at PGL(2,7)
  identifying the content trace with the coalition's static reading, whose
  comment says that the instance's trace theorems and reading theorems are
  therefore one statement each. Statement comments carry the factor two (the
  sum of absolute differences is twice the literature's total variation) and
  say: one seat or one position, one run law, no coalition, no second run
  argument, no secret; not security evidence.
- **NOT landed (tracker 4.1 stays open):** `StaticReader`, the reader forms of
  the propositions, the post-processing law. They are correct and have no use
  until a genuinely different reader instantiates them.
- **Follow-up probe (tracker 4.1b):** the PSL(2,11) colour reader. Rows: a
  sample adapter over `psl211P` (sample type `bool * pgg_gT psl211_M`,
  argument `fst`, cut `snd`), with the seat-indexing reconciliation that
  `pgl27_static_obsE` did at eight cards; the colour reader as a function of
  the canonical reading (the factorisation of R3, in the direction that is
  true); `ReaderExactPropAt` at the colour reader from
  `psl211_colour_view_indep`; sharpness from `psl211_colour_view_dep_k6`; the
  record's comment rewritten (P15: the type does not enforce that a reader
  ignores the run's messages; say what it is, a function of the run argument
  and the cut). Only if these compile does the reader framework get a landing
  plan. `instances/psl211/psl211_exec.v` and the endpoints closure stay
  untouched; `psl211_secrecy.v` is not frozen.
- **Follow-up row (tracker 4.4b), optional:** the S_5 countermodel of finding 4
  as a theorem.

### Landing plan for 4.4 (after the landing of tracker 4.3 is committed)

1. New leaf file `manifest/pgg_tableau_marginal_bounds.v` (imports the
   framework and the sample adapter; nothing imports it but the instance files
   below): the two definitions, `seat_marginal_prop_at2`,
   `cut_marginal_prop_at2`, boxed header with index. `_CoqProject` line.
2. `instances/s5/tableau/s5_tableau_sampled.v`: the S_5 instance
   (`s5_word_seat_marginal`), one header sentence pointing at it from the
   paragraph that already explains the word model.
3. `instances/kim2025/tableau/five_card_tableau_sampled.v`: the five-card
   instance beside `five_card_repeated_endpoint_lt`.
4. The PGL(2,7) identification lemma in the lowest file that sees both
   `pgl27_coalition_trace_E` and `pgl27_static_obsE` (the prover finds it and
   reports; no new import into a mathematics file from the framework).
5. Fidelity file in the probe directory; names checked free; one naming and
   comment audit of the landing; closure recompiled by the main session.
