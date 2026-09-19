# The Tableau extensions, as built (2026-09-20)

What the four landings of 2026-09-20 put into production, how each was
checked, where the result departs from the spec and the landing design, and
what is left. Spec: `notes/20260919-tableau-three-extensions-probe-design.md`.
Landing design: `notes/2026-09-20-000000-tableau-extensions-landing-design.md`.
Tracker: `notes/2026-09-19-214329-tableau-campaign-tracker.md`.

## What production holds now

| Landing | Commit | Files | Content |
|---|---|---|---|
| 1 | b03b467 | `manifest/pgg_tableau.v`, `manifest/pgg_tableau_syntax.v`, the four rows files, `instances/psl211/psl211_reading_constancy.v` (comments) | `conclude` with the obligation `cert_eps cert <= c` (`ConcludePayload`, `port_conclude`), so a row may be stated at any number at or above its certificate's own. `SecurityArm` with `port_arm`, `ab_arm`, `security_arm_of`, and one `_armE` equation per program. The third arm `IdealProximity` (`IdealProximityCert` with `ipc_ideal`, `ipc_witness`, `ipc_secret`, `ipc_eps`, `ipc_close`; `IdealProximityPropAt`; `idealproximity_tail`; `certify_idealproximity`; `view_proximity_of`). Keyword notations `\|> conclude c by p` and `certify IdealProximity cert`. `five_card_row_repeated39` publishes 2^-39 from `kim_centi_cert` by a strict inequality; `kim_centi_cert40` and its `_epsE` withdrawn. `pgl27_word_sampled`, `pgl27_row_word_branch39`. |
| 2 | 0397f8e | new `instances/kim2025/five_card_proximity.v`, new `manifest/pgg_tableau_arm_relations.v`, new `security/var_dist_joint_law.v`, `lib/var_dist_supp.v`, `instances/kim2025/five_card_mixing.v` | The one-cut five-card row certified by the proximity arm at one fiftieth against den Boer's uniform model; the bound against the executed law's own two marginals at three fiftieths. `indistinguishability_prop_cert_free`, `idealproximity_prop_at2`, `idealproximity_reading_le`. Five lemmas on the sum of absolute differences between joint laws and product laws. `card_tnth_count` moved to its only user; `kim_centi_marginal_bound40` and `kim_centi_cut_mixing40` withdrawn. |
| 3 | 31468b6 | new `instances/pgl27/pgl27_proximity.v`, `pgl27_exec.v`, `pgl27_models.v`, `pgl27_analysis.v`, the manifest and its client, `lib/var_dist_supp.v` | `pgl27_prior_sample`, `pgl27_prior_exact_family`, manifest row 10 `pgl27_row_prior_exact` (independence at every prior is `pgl27_view_indep_gen`). The word model's proximity certificate at 2^-40, its row concluded at 2^-39 with the obligation met strictly. `pgl27_word_uniform_ideal_close_false`. `var_dist_fdist1_uniform` in `lib/`. |
| 4 | 2373576 | new `instances/psl211/psl211_word_model.v`, new `instances/psl211/psl211_word_proximity.v`, `psl211_analysis.v`, the manifest and its client, `psl211_reading_constancy.v` (comments) | The all-decks model with its cut law replaced by the 584-letter word law, `psl211_word_law_le40`. The proximity row published plainly at 2^-40 for coalitions of at most five of twelve seats. Manifest row 11 `psl211_row_word`. The constancy file's comments no longer deny a word adapter. |

The manifest has eleven typed rows. Three instances publish through the
proximity arm. Every published row and every landed lemma depends on the three
classical axioms only, the S5 rows besides on `s5_group_order_eq`, as before.

## How each landing was checked

One directory per landing under `notes/probes/2026-09-20-tableau-extensions-landingN/`:
a `staged/` tree holding the landed files and chain copies of their whole
reverse closure, compiled into the staged tree; `landing_fidelity.v` ascribing
every landed declaration at the probe's statement, with `Print Assumptions`
and module-qualified provenance checks; `verify.py` for token and comment word
diffs; `restage.py` to follow the landing below it. Then, for each landing: a
soundness audit (Opus, compiling in its own scratch directory) and a naming
audit (Opus, read-only) on a frozen export; a fix pass by an Opus
`rocq-prover`; an audit of that fix pass (Opus); a second, comments-only fix
pass audited by the main session by token diff and by reading every changed
passage; `cp` with `cmp`; a single-file recompile of the production closure
(7, 15, 19 and 15 files); and the unchanged fidelity file compiled against
production's load path alone (40, 33 and 2 closed, 29, 24 `Axioms:` blocks,
equal to the staged runs). `instances/psl211/psl211_endpoints.v` was never
compiled; `make` was never run.

## Departures from the spec and the design

1. The framework files landed once, with stages A and B together, because the
   probe's file is one audited text. "A before B" holds at the level of rows.
2. Spec change 5 was wrong about the input-indistinguishability arm. Its
   proposition does not mention its certificate; its ideal is a means of proof
   that `ic_Hd`, `ic_close` and `ic_const` constrain. The framework header says
   what each arm's proposition mentions. The spec carries the correction.
3. The joint-law lemmas went to a new `security/var_dist_joint_law.v`, not to
   `lib/var_dist_supp.v`: two of them apply lemmas of
   `security/pgg_collusion_bound.v`, and `lib/` keeps no dependency on
   `security/`.
4. The declarations that name no instance went to a new
   `manifest/pgg_tableau_arm_relations.v`, not to an instance file.
5. `pgl27_prior_viewE` and `pgl27_prior_exact_witness` are in
   `pgl27_proximity.v`, not in `pgl27_models.v`: what they need is downstream
   of that file.
6. The facades `pgl27_analysis.v` and `psl211_analysis.v` were edited, which
   the spec did not list: the manifest sees a family only through a facade.
7. `_rowE` lemmas of the new rows state `= <the manifest row's name>`; the
   probe's raw-family forms are kept in the fidelity files.
8. Names that changed at the landings: `idealproximity_ceiling` ->
   `idealproximity_prop_at2`; `pgl27_row_word_arms_sampledE` ->
   `pgl27_row_word_families_sampledE`; `pgl27_word_uniform_ideal_not_close` ->
   `pgl27_word_uniform_ideal_close_false`; `pow2_40_ge1`, `pow2_40_gt0` ->
   `pgl27_pow2_40_*`; `psl211_word_lawE` -> `psl211_word_law_le40`;
   `psl211_word_law_tauto` -> `psl211_word_law_by_var_dist_le2`.
9. Two sentences of the probe's audited text were false and were corrected at
   the landing: that the model family is the only coordinate separating
   `psl211_row_word` from `psl211_row_alldecks` (the transfer status differs
   too), and the probe's clause relating `pgl27_row_prior_exact_tableau` to
   `pgl27_row_exact`, which nothing in the tree states and which was dropped.
10. One recorded `Fail` of the probe named a subject that production does not
    hold (`pgl27_exact_sampled`); left as written it would have succeeded on an
    unknown reference. It was respelled inline and re-checked without `Fail`.

## What the audits kept finding

Eleven audits and eight fix passes. No finding was about a statement or a
proof; nearly all were comment sentences, and the same classes recurred in
text the provers wrote, in text the auditors proposed, and in the probe's
already audited text:

- a universal sentence where the declaration speaks of one certificate, term,
  model or adapter;
- a recorded `Fail` said to show an impossibility or a necessity;
- an upper bound called "the distance";
- "the number" with the wrong antecedent;
- a witness called a port, a model called a row, a row said to publish or to
  draw, an index type said to separate two models;
- a header entry that drops a hypothesis;
- proof strategy, history, a paper's table or a timing in a docstring;
- a metaphor noun for a bound.

The main session read every rewritten passage and found four such sentences
that an agent had just written. A later landing repeated six defects its sibling
file had already had corrected, because it was taken from the probe: the brief
for a sibling file must say to diff against the corrected sibling.

## Left open

Owner's decisions, none blocking: the type name `Reprice` and the constants
`*_reprice39`, now that `conclude` states an upper bound; the words "spend",
"price", "currency", "cost" for how often an arm uses a bound, in at least four
production files.

For a pass over production comments: the docstring of
`kim_biased_proximity_cert_idealE` (a witness is not a port); the header
sentence of `psl211_word_proximity.v` that speaks of reading a row "in one
column"; five sentences of `psl211_reading_constancy.v` with an economic word;
eight uses of "ceiling" in `five_card_rows.v`.

Not compiled, as the spec records for P8: a countermodel to the implication
from the input-indistinguishability proposition to the proximity proposition
below two, and a derivation of proximity from an input-indistinguishability
certificate's own fields.

`instances/psl211/psl211_endpoints.vo` is older than its source; commit c9634fd
added `Optimize Proof` and `Optimize Heap` inside one proof and changed no
statement. Single-file compiles load it by digest.

The rows files are no longer leaves: `five_card_proximity.v`,
`pgl27_proximity.v` and `psl211_word_proximity.v` import them. The per-instance
`tableau/` reorganization has to account for that.
