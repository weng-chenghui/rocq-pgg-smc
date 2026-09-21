# Landing commit 2: the reading as an index of the security claim (record)

Written by the landing agent. Not committed by it.

## Steps and their state

| step | file(s) | state |
|---|---|---|
| 1 | `manifest/pgg_tableau.v` | landed, compiles 13.8 s / 14.0 s |
| 2 | `manifest/pgg_tableau_syntax.v` | landed, 4.5 s |
| 3 | `manifest/pgg_tableau_reading.v`, `manifest/pgg_tableau_security_property_relations.v` | landed, 3.7 s / 4.3 s |
| 4 | the instance annotation sites | landed, 22 sites (count below) |
| 5 | `instances/psl211/psl211_models.v`, `instances/psl211/psl211_colour_reading.v`, `instances/psl211/tableau/psl211_tableau_dealt.v`, `instances/psl211/psl211_reading_constancy.v`, the narrowed statements' comments | landed |
| 6 | `_CoqProject`, closure pass | done, 38 files, ALL OK, "frozen files met: none" |
| 7 | fidelity file | done, rc 0, 48.6 s, three classical axioms only |
| 8 | PGL(2,7) timing | measured 9.5 s against a 7 s baseline |

## Step 6, the closure pass

`python3 scripts/comment_pass/closure.py --changed HEAD` prints "frozen files
met: none" and 38 files.
`compile_closure.py ... --log $SP/s2c.log --cap 3000` ends `ALL OK`, no FAIL
line. Its last five lines:

```
ok      5.2 instances/psl211/tableau/psl211_tableau_dealt.v
ok      3.8 instances/s5/tableau/s5_tableau_checks.v
ok      4.3 manifest/pgg_analysis_client.v
ok      4.2 manifest/pgg_tableau_security_property_relations.v
ALL OK
```

## Step 7, the fidelity file

`notes/probes/2026-09-21-reading-index/landing2/landing_fidelity.v`, compiled
with `-o $SP/s2fid/landing_fidelity.vo`, rc 0 in 48.6 s. It holds:

- 38 `Check (name : full statement)` for the framework's new and restated
  declarations, the three reading lemmas of `pgg_tableau_reading.v`, the two
  new records of the relations file and every declaration of
  `psl211_tableau_dealt.v`, including the obstruction program's `_kindE` and
  `_pathE`;
- verbatim copies of the three records and the four propositions of HEAD
  2fc0108 and the four K5 equations against them, each by `exact: erefl`;
- the reading of one program per instance that names none
  (`s5_rand_published`, `five_card_uniform_published`,
  `pgl27_exact_published`, `psl211_alldecks_published`), each
  `= coalition_endpoint_reading <algebra>` by `exact: erefl`, and the colour
  program's `= psl211_colour_reading`;
- `fidelity_number_bound_nondegenerate`: over the all-decks model no
  input-indistinguishability certificate at the coalition's own endpoint
  reading satisfies the proposition at zero, from
  `psl211_alldecks_indistinguishability_number_ge` at 1/660;
- seven `Print Assumptions` under `Timeout 300`: `exact_tail`,
  `indistinguishability_tail`, `idealproximity_tail`,
  `input_distinguishability_prop_finer`, `psl211_colour_exact_published`,
  `psl211_dealt_obstruction_published`,
  `psl211_dealt_input_distinguishable`.

All seven print the same three axioms and nothing else:
`propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description`. No `s5_group_order_eq`, no custom
axiom.

The dealt obstruction program's `_pathE` is proved inside
`psl211_tableau_dealt.v` (whole file 4.8 s to 5.2 s) and checked again in the
fidelity file; its `Print Assumptions` returned inside its timeout. Nothing
had to be left out.

## Decisions and departures from the brief

1. **`certify_reading_exact_readingE` is not landed.** The staged framework
   file carried it. RULINGS design ruling 5(a) asks for a framework lemma per
   statement that names NO reading, and 5(b) puts the equation of a program
   that names one on that program itself; the owner's list of what lands says
   "the three `_readingE` framework lemmas". The three landed are
   `certify_exact_readingE`, `certify_indistinguishability_readingE`,
   `certify_idealproximity_readingE`. Nothing in the tree called the fourth.

2. **The obstruction terminal keeps both forms.** The rule without `of r` and
   the rule with it were compiled together in `pgg_tableau_syntax.v` with no
   ambiguity warning, so the brief's condition is met. The all-decks program
   keeps the short form at the default reading; the new dealt program writes
   `of (coalition_endpoint_reading psl211_algebra)`, so both rules have a
   caller and the new program's own line shows its reading.

3. **`psl211_colour_reading.v`: the seat reconciliation moved, not merged into
   one proof.** `psl211_colour_of_reading_obsE` is now stated ABOVE
   `psl211_colour_readingE`, and `psl211_colour_readingE` is proved by
   `rewrite /cr_read /psl211_colour_reading psl211_colour_of_reading_obsE`
   and then the old script. The probe's staged copy left the lemma below and
   did not compile; the brief's "the two proofs merge, named once" is
   realised as one lemma used by the other rather than one script, because
   both statements are cited elsewhere in the file.

4. **`psl211_dealt_family` and the Sampled value live in the new Tableau
   file**, not in `psl211_models.v`: the family needs `psl211_dealt_sample`,
   which is in `psl211_colour_reading.v`, and that file requires
   `psl211_models.v`. Only the endpoints statement and the observed execution
   went into `psl211_models.v`, as probe item m6 measured.

5. **`coalition_reading_cst_unit` uses `(unit : finType)`,** not
   `[the finType of unit]`, which Rocq 9.0.0 rejects here (`s0 has type
   finType while it is expected to have type Set`).

## Counts

- Framework `_readingE` lemmas: 3.
- `manifest/pgg_tableau_security_property_relations.v`: 14 reading sites, plus
  `coalition_reading_cst_unit` and `exact_witness_cst_reading`.
- Instance annotation sites, recounted (the two-record probe counted 43 over
  both trees; this is the one-record count in production):
  - `instances/s5/tableau/s5_tableau_analysis_bridged.v`: 1
  - `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v`: 5
  - `instances/kim2025/tableau/five_card_tableau_checks.v`: 3 (all `Fail`)
  - `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v`: 5
  - `instances/pgl27/tableau/pgl27_tableau_checks.v`: 2 (both `Fail`)
  - `instances/psl211/tableau/psl211_tableau_analysis_bridged.v`: 4
  - `instances/psl211/tableau/psl211_tableau_checks.v`: 1 (`Fail`)
  - `instances/psl211/psl211_reading_constancy.v`: 5
  - `instances/psl211/psl211_colour_reading.v`: the whole file restated
  Total outside the two psl211 restated files: 21; with
  `psl211_reading_constancy.v`: 26.

## Timings

`manifest/pgg_tableau.v` 14.0 s, `pgg_tableau_syntax.v` 4.6 s,
`pgg_tableau_reading.v` 4.4 s, `pgg_tableau_security_property_relations.v`
4.3 s, `psl211_models.v` 30.0 s, `psl211_reading_constancy.v` 24.0 s,
`pgl27_tableau_analysis_bridged.v` 9.5 s (baseline about 7 s, limit 15 s),
`five_card_tableau_analysis_bridged.v` 8.6 s,
`psl211_colour_reading.v` 18.1 s, `psl211_tableau_dealt.v` 4.8 s,
`landing_fidelity.v` 48.6 s. The whole closure of 38 files runs in about
220 s of CPU time.

## Comments

Every comment paragraph written or rewritten is copied, with the declaration
it sits on, into `COMMENTS.md` beside this file.
