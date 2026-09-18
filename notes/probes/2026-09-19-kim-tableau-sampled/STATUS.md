# Probe status: Kim's two five-card rows as Tableau programs

Date: 2026-09-19.
Spec probed: `notes/20260919-kim-tableau-sampled-design.md`.
Probe directory: `notes/probes/2026-09-19-kim-tableau-sampled/`,
logical path `kim_tableau_sampled_probe`.
Nothing under `lib/ protocol/ groups/ security/ smc/ reconstruct/ instances/
manifest/` or the production `_CoqProject` was touched. No `make` was run.

## Ledger

| ID | Verdict | Evidence |
|---|---|---|
| K1 | GO | `Definition five_card_row_repeated_tableau : Tableau Sampled := five_card_committed sample kim_centi_family.` elaborates in 0.000 s (`-time`, `kim_rows_probe.v` chars 1619-1732). |
| K2 | GO | The same with `kim_biased_family`, 0.000 s (chars 1734-1846). |
| K3 | GO | `five_card_row_repeated_prefixE` and `five_card_row_biased_prefixE`, `by split` in 0.033 s each, `Qed` 0.007 s. Two `Fail` mutations sampling another instance's family fire, error texts below. |
| K4 | GO | `five_card_row_repeated_modelE` and `five_card_row_biased_modelE`, `by []` in 0.000 s. Conversion decides both; `AnalysisModelSlot` iota-reduces to `AnalysisModelFamily` at `Sampled` and at `AnalysisBridged` alike. |
| K5 | GO | Stronger than the spec asked: `Definition five_card_row_repeated_at_manifest_level : Tableau (apr_completion five_card_row_repeated) := five_card_row_repeated_tableau.` typechecks. The biased analogue is a recorded `Fail`; `five_card_row_biased_levelE : apr_completion five_card_row_biased = AnalysisBridged` is `by []`. |
| K6 | GO | `five_card_row_repeated_endpoint_lt`, `by rewrite kim_centi_cut_distE; exact: kim_deal_centi_lt`, 0.002 s tactic, 0.002 s `Qed`. Classical trio only. Both mutations fail at the `exact:` step. |
| K7 | GO, with one new side condition | `five_card_row_biased_leak_bound`, one `exact:`. Needs `kim_centi_small`, the fourth side condition at bias one hundredth, which the tree does not carry. |
| K8 | NO, reported | Neither arm can be supplied. Exact arm: `ew_indep` has no theorem. Spectral arm: `sc_b`, `sc_Hd`, `sc_ideal` build; `sc_close` and `sc_const` have no theorem. |
| K9 | GO | The forward closure of `instances/kim2025/five_card_rows.vo` in `.Makefile.rocq.d` contains no other module's `.vo`, and a whole-tree scan finds `five_card_rows` on one line only, this file's own header. |
| K10 | GO | Whole-word scan of eleven new names over 521 `.v` files: zero hits. |
| K11 | GO | Header sentence replaced, title line and both header tables updated; the landing copy compiles. |

## Compile table

Machine-wide `ps -axo comm= | grep -E 'rocqworker$'` was empty before and
after every compile. Every compile ran under the perl time and RSS wrapper
`tmo` at a 8000 MB cap, which never fired.

| file | wall | summed `-time` | peak RSS |
|---|---|---|---|
| `kim_rows_probe.v` | 4.52 s | 4.46 s | 1.79 GB |
| `kim_biased_arms_probe.v` | 4.40 s | 4.34 s | 1.84 GB |
| `five_card_rows_landing.v` | 3.91 s | 3.84 s | 1.70 GB |
| `kim_fidelity.v` | 6.66 s | 6.52 s | 1.88 GB |

About 3.1 s of every figure is the two library `Require` lines, `reals boolp`
at 1.71 s and `infotheo fdist proba entropy` at 1.24 s. Peak RSS is the
loaded `.vo` closure and does not move with the new declarations. `-time`
reports per sentence and not per sentence's memory, so the RSS column is the
whole process, not the individual `Definition`; every new sentence in this
probe costs at most 0.037 s, so no per-sentence memory figure is meaningful.

The slowest new sentence anywhere is `kim_centi_small` at 0.037 s. No
sentence approaches the 20 s bug threshold, and none of the four recorded
hang shapes appears: nothing unfolds the executed run inside
`five_card_committed`, and the one `rewrite` (`kim_centi_cut_distE`) fires on
the cut law alone.

## Mutation error first lines

K3, `five_card_row_s5_family`, in `kim_rows_probe.v` and in the landing copy:

    The term "S5Analysis.rand_family" has type
     "AnalysisModelFamily s5_exec.s5_rand_observed"
    while it is expected to have type
     "FamPayload (tableau_at five_card_committed)".

K3, `five_card_row_pgl27_family`, probe only:

    The term "PGL27Analysis.exact_family" has type
     "AnalysisModelFamily pgl27_exec.pgl27_observed"
    while it is expected to have type
     "FamPayload (tableau_at five_card_committed)".

K5, the biased row at the manifest's level, in both files:

    The term "five_card_row_biased_tableau" has type "Tableau Sampled"
    while it is expected to have type
     "Tableau (apr_completion five_card_row_biased)".

K6, the bound tightened to two to the minus forty-first, probe only. The
caret in the `rocq repl` output points at `exact: kim_deal_centi_lt`, so the
`rewrite` succeeded and the failure is the final step:

    Error: Cannot apply lemma kim_deal_centi_lt

K6, the same read on a pair of seats against the product of two uniform
laws, probe only, same step:

    Error: Cannot apply lemma kim_deal_centi_lt

K8, the exact arm's witness fed the tree's one independence theorem of that
shape, probe only:

    The term "five_card_static_obs_indep R tt" has type
     "... sa_sampleP (amf_sample five_card_uniform_family R tt) |= ..."
    while it is expected to have type
     "... sa_sampleP (amf_sample kim_biased_family R tt) |= ..."

K8, `sc_close` fed the bundle's own distance field, and then fed
`kim_one_cut_centiE`, probe only:

    Error: Cannot apply lemma (sw_bound (five_card_biased_sc_b R))
    Error: Cannot apply lemma (kim_one_cut_centiE R)

## K9, the reverse-dependency closure

Computed in Python from `/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/.Makefile.rocq.d`
(188546 bytes, written 2026-09-18 23:01), by joining line continuations,
reading every `target: prereq...` rule as edges from each prereq to each
target, and taking the transitive closure forward from
`instances/kim2025/five_card_rows.v` and its `.vo/.vos/.vok/.glob` siblings.

    closure .v files      : NONE
    closure non-.v targets: ['instances/kim2025/five_card_rows.required_vos']
    closure size          : 1

That output is restated here as the independent soundness audit verified it,
because "closure `.v` files: NONE" is vacuous on its own: a `.v` file is
never a Make target, so no traversal of this file could ever return one. The
two decisive facts are that the forward closure of
`instances/kim2025/five_card_rows.vo` contains no other module's `.vo`, only
that file's own auxiliary targets, and that a whole-tree scan for the string
`five_card_rows` finds one line, this file's own header. The auditor's
traversal reported three auxiliary targets where mine reported one, a
difference in which suffixes were seeded and not in the conclusion. Sanity
check on the same traversal: `manifest/pgg_tableau.vo` has 20 dependent
targets, so the closure is empty because nothing imports this file and not
because the traversal is broken. Editing `five_card_rows.v` therefore
recompiles that file alone, as the spec's decision 7 says.

## K10, the collision scan

Python, `\b` word boundaries (BSD `grep -E '[[:<:]]'` silently matches
nothing here), over every `.v` file under `lib protocol groups security smc
reconstruct instances manifest` and under
`/Users/cheng-huiweng/Projects/coq/_opam/lib/coq/user-contrib/infotheo` and
`.../mathcomp`. 521 files scanned. Zero hits for each of:

    five_card_row_repeated_tableau             0
    five_card_row_biased_tableau               0
    five_card_row_repeated_prefixE             0
    five_card_row_biased_prefixE               0
    five_card_row_repeated_modelE              0
    five_card_row_biased_modelE                0
    five_card_row_repeated_at_manifest_level   0
    five_card_row_biased_levelE                0
    five_card_row_repeated_endpoint_lt         0
    kim_centi_small                            0
    five_card_row_biased_leak_bound            0

Naming reading. The five new `five_card_row_<mode>_*` names extend the file's
own `five_card_row_uniform_tableau` and `five_card_row_uniform_rowE` pattern,
mode word in the same position. `kim_centi_small` extends the
`kim_centi_lt`, `kim_centi_gt`, `kim_centi_spec` family of
`instances/kim2025/five_card_kim.v` and names the condition rather than the
bias. `five_card_row_repeated_at_manifest_level` is the one long name: `at`
is load-bearing, because dropping it leaves
`five_card_row_repeated_manifest_level`, which reads as a level-valued
definition rather than as the program read at a level.

## Assumption closure, K1 to K7 as landed

`kim_fidelity.v` runs `Print Assumptions` on all eleven new declarations of
the landing copy. Ten print the repository's classical trio
`boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`,
`boolp.constructive_indefinite_description`, which every fdist-record
statement in this tree carries. One, `five_card_row_biased_levelE`, prints
`Closed under the global context`. No fourth name anywhere, no new axiom, no
`Admitted`, no `Abort`.

## Where the additions were placed in the landing copy, and why

After the block `The exact arm's four conjuncts at this instance` and before
`The ideal functionality`. The uniform row's material runs program then
content, the section `The uniform row` followed by the section that reads its
four conjuncts off it. Placing the two new programs between those two would
separate the uniform row from its own read-off. The new material has the same
program-then-content shape, so it becomes the next pair of sections, `Kim's
two rows` and `What the two rows carry beside their programs`. The
functionality block that follows is about the prefix and not about any row,
so it reads last either way and is untouched.

The comment style matched is the file's own: `(** ... *)` prose above each
declaration, `(*` banners of 78 characters for section headings, and the
80-column boxed header. No `(** name — ... *)` form appears in this file, so
none was introduced.

## What was landed and what was kept in the probe

Landed in `five_card_rows_landing.v`, eleven declarations: the two programs,
the two `prefixE`, the two `modelE`, `five_card_row_repeated_at_manifest_level`,
`five_card_row_biased_levelE`, `five_card_row_repeated_endpoint_lt`,
`kim_centi_small` and `five_card_row_biased_leak_bound`. Two `Fail`
mutations: `five_card_row_s5_family`, the program sampling a family typed
over another instance's observed execution, and
`five_card_row_biased_at_manifest_level`, the biased program ascribed the
manifest row's completion level.

`five_card_row_repeated_levelE : apr_completion five_card_row_repeated =
Sampled` was NOT landed, for one reason and one only. The ascription
`Tableau (apr_completion five_card_row_repeated)` already forces
`apr_completion five_card_row_repeated` to be convertible to `Sampled`,
because `TableauAt` takes the level as a parameter, so the equation adds
nothing the ascription does not already check. The biased row's level is
landed as a lemma because there is no ascription to carry it, the ascription
being the recorded `Fail` beside it. That the manifest checks the repeated
equation itself, at `manifest/pgg_analysis_manifest.v:1787`, is NOT a reason
to drop the lemma and was wrongly given as one in the first version of this
file: the manifest checks the biased equation too, at `:1778`, by the same
`Timeout 60 Check (erefl : ...)` idiom, and the biased lemma is landed.

Kept in the probe and not landed: `five_card_row_pgl27_family`, the two
K6 mutations, and the three buildable `SpectralCert` fields. The K6 mutations
are `Fail Definition ... := ltac:(rewrite ...; exact: ...)` terms, and the
one `Fail` this file already carries, `five_card_F_or`, is a clean `erefl`
term; an `ltac:` proof inside a `Fail` is probe idiom and would read as an
intrusion in a permanent file.

## K7 in detail

`sa_sampleP (amf_sample kim_biased_family R tt) = kim_input_dist
(kim_centi_lt R) (kim_centi_gt R)` holds by `erefl`, checked in
`kim_biased_arms_probe.v`. Kim's theorem therefore already lives on the law
the biased row samples, and the restatement consumes none of the manifest's
three bridge lemmas: `kim_single_cut_distE`, `five_card_colour_viewE` and
`five_card_colour_view_RV_E` are not used. The only cost is the side
condition. `five_card_colour_view_leak_bound` takes four hypotheses on the
bias, `eps < 1/5`, `-(4/5) < eps` and `0 < 1/5 - |eps|`; the tree carries
`kim_centi_lt`, `kim_centi_gt` and `kim_centi_spec` at bias one hundredth,
and `kim_centi_spec` is `|eps| < 4/5`, the spectral condition, not this one.

The comment on `five_card_row_biased_leak_bound` states the argument order
read off `instances/kim2025/kim_input_privacy.v:21`, where
`cond_mutual_info (`p_ [% kim_inputs, kim_view A, kim_secret])` is written
`I(Inputs ; View | Secret)`: the information is between the inputs and the
reading, given the secret.

The comment does NOT say the bound is positive. `kim_leak_bound (1/100) > 0`
is not a lemma anywhere in the tree (whole-tree grep for `kim_leak_bound`
returns the definition at `kim_input_privacy.v:78`, the two bound statements,
one rewriting step and three comments), and it is not a one-line proof: it
needs `0 < log (expR 1)` on top of the sign of the rest. The comment says
instead that the statement is a numeric ceiling and not the assertion that
the information vanishes, which is a claim about the statement and not about
the value.

## K8 in detail

Exact arm, the missing field is `ew_indep` and it is the only one. The probe
prints the residual obligation of `MkExactWitness` at the biased member and
it is exactly `sa_sampleP (amf_sample kim_biased_family R tt) |= (fun u =>
static_coalition_obs C (sa_arg u) (sa_cut u)) _|_ Secret R` at every
coalition below the threshold. What was searched: a whole-tree grep for any
occurrence of `kim_input_dist` or `kim_single_sample` on a line also carrying
`_|_`, `inde_RV` or `indep` returns empty. Every independence statement in
the five-card cone is at the uniform law: `kim_secrecy.v:36` at `Let kimP :=
P R` (`kim_secrecy.v:32`), `five_card_rows.v:219` and `:314` at `P R`,
`five_card_rows.v:247` at `sa_sampleP (amf_sample five_card_uniform_family R
idx)`, `denboer_secrecy.v:32` at `dbP`, `five_card_leakage.v:258` and `:1023`
at `P`.

Spectral arm, three of five fields build, each compiled on its own in
`kim_biased_arms_probe.v`:

- `sc_b`, as `scb_bound (fc_kim_security_bundle at bias 1/100, length 1)`.
- `sc_Hd`, by `rho_from_words_weighted1` (`instances/kim2025/five_card_exec.v:945`),
  then `kim_single_cut_distE`, then `fc_kim_gensE`. This is the route
  `den_boer_witness_rotationE` takes at bias zero.
- `sc_ideal`, as `sa_cut_dist (five_card_sample R)`. A free choice.

`sc_close` is missing: it asks for a variation distance between two laws on
the cut group, and everything the bundle carries is per position, `sw_bound`
being one endpoint marginal on `'I_5` at each starting position and
`kim_one_cut_centiE` the same shape as an exact value `1/50`. Both are fed to
the slot and rejected, error lines above. This is the gap
`instances/s5/s5_rows.v` already records for `s5_row_word`, where
`s5_word_base_premise` names it as a premise nothing in the tree proves.

`sc_const` is missing: it asks that a coalition below the threshold read the
ideal law the same way at two different run arguments. The only statement of
that shape in the tree is `pgl27_word_view_const`
(`instances/pgl27/pgl27_rows.v:224`), supplied there by three-transitivity of
PGL(2,7). The five-card development states nothing of that shape at any cut
law; `five_card_viewS_indep` and `five_card_static_obs_indep` are
independence from a secret under the uniform sample, a different proposition
from constancy in the run argument.

Conclusion: no. Neither arm of `certify` can be supplied for the biased row
from theorems that exist today.

## Findings against the spec

1. K5 is under-specified in the note and the answer is better than the note
   expected. The note says the corresponding statement for the biased row is
   false by design and the gap is recorded in a comment and not in a lemma.
   The gap is expressible as a compiled fact, the `Fail` on
   `Tableau (apr_completion five_card_row_biased)`, so the comment now
   explains a checked fact instead of asserting an unchecked one.
2. K6 needs no identification lemma. The note's `Cited objects` table lists
   `kim_centi_witness_rhoE` as a required object; it is not used. The group
   carrier `pgg_gT FiveCardKim_M` is convertible to `{perm 'I_5}`, and
   `kim_centi_cut_distE` unifies against `sa_cut_dist (amf_sample
   kim_centi_family R tt)` directly, so the route is two lemmas and not
   three.
3. K7 needs a fourth side condition at bias one hundredth that the tree does
   not have. The note's hypothesis-consumption table in
   `instances/kim2025/five_card_models.v:52-77` states the distinction
   between `spec` and `small` correctly, but the note's cited-objects table
   does not name a `small` witness at bias one hundredth, and none exists.
4. The note's `Proposed declarations` block writes the two programs with the
   payload on a second line. That is what landed, matching
   `five_card_row_uniform_tableau`.
5. The landing copy adds one `Require Import` line,
   `From pgg_smc Require Import kim_input_privacy.`, which K7 needs for
   `kim_inputs`, `kim_secret` and `kim_leak_bound`. It adds no edge to the
   build graph: `five_card_models`, already required by this file, requires
   `kim_input_privacy`.
6. Three line numbers in the note's `Cited objects` table are wrong. The row
   for `ExactWitness`, `SpectralCert` and `SecurityPort` gives
   `manifest/pgg_tableau.v:150 and above`; the three records are declared at
   `:114`, `:131` and `:149`. The same table gives no line for
   `five_card_row_biased`, which is at `manifest/pgg_analysis_manifest.v:766`.
7. The note names neither landed mutation. Its closing list says only "the
   program sampling another instance's family, and the biased program at the
   manifest's level"; the identifiers are `five_card_row_s5_family` and
   `five_card_row_biased_at_manifest_level`.

## Implementation-plan notes

- `kim_centi_small`'s natural home is `instances/kim2025/five_card_kim.v`,
  beside `kim_centi_lt`, `kim_centi_gt` and `kim_centi_spec` in the same
  concrete section. It is placed in `five_card_rows.v` directly above its one
  use instead, because `five_card_kim.v` has importers and
  `five_card_rows.v` has none, and the user's rule is to compile only related
  files. Move it when `five_card_kim.v` is next opened for another reason.
- The landing compiles `instances/kim2025/five_card_rows.v` only, by K9.
- The two `SpectralCert` fields that do not exist are the same two
  `s5_rows.v` records as missing for `s5_row_word`. If either is ever proved
  for the five-card cut, the biased row's comment and the file header both
  name the gap and would both need revising.

## Fix pass, 2026-09-19, after the two independent audits

One comment, header and rename pass over `five_card_rows_landing.v`, with the
before-fix copies of the three touched `.v` files kept in `history/`, which is
not in `_CoqProject`. No statement, proof or type changed: with comments
stripped and the one rename applied, the file is line-for-line identical to
`history/five_card_rows_landing.2026-09-19-before-fix.v`, 214 code lines on
both sides, and it removes no code line of the production original. Applied:
the header's opening paragraph, which promised that every statement below is
about a coalition of at most one seat and that input privacy is not stated
here, both false once `five_card_row_biased_leak_bound` lands, replaced by the
naming auditor's nine lines; the mutation `five_card_row_alien_tableau`
renamed `five_card_row_s5_family`, a metaphor replaced by the combination that
is rejected, and the probe's second mutation renamed
`five_card_row_pgl27_family` to match; statement comments added to
`five_card_row_biased_prefixE` and `five_card_row_biased_modelE`; the comment
of `five_card_row_biased_levelE` rewritten to say that it and the rejected
ascription are the two halves of the level gap; "seat" replaced by "starting
position" for the index of the endpoint bound in the statement comment, the
header sentence and the Key results gloss, since this file does not prove the
identification of seats with card positions; the biased program's comment
shortened to point at the header rather than repeat it; and the header given
the two-criteria sentence, that the manifest admits a row to AnalysisBridged
on any theorem about the sampled distribution and the observer
(`manifest/pgg_analysis_status.v:55-59`), which a leakage bound meets, while a
program reaches that level only through one of the two arms of `certify`, so
both assignments are correct and the manifest's level for this row is not an
error. The two `prefixE` comments were checked against the landed three
conjuncts and already state exactly those three, phrasing the run facts as
what the observed execution record carries rather than as a conjunct; the
header table gloss does the same. Not applied, because not requested and
cosmetic: the naming auditor's N3, N7 and N8.
