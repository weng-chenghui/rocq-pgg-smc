# Landing 2 of the Tableau extensions — staged text

Date: 2026-09-20. Branch `feat/tableau-extensions-probe`, HEAD `16066cd`.

This directory holds the STAGED TEXT of landing 2 of
`notes/2026-09-20-000000-tableau-extensions-landing-design.md`. Nothing under
`manifest/`, `instances/`, `lib/` or `_CoqProject` of the repository was
touched, and nothing under
`notes/probes/2026-09-20-tableau-extensions-landing1/` was touched. The main
session does every `cp`.

Every staged file compiles, the fidelity file compiles, and every landed
declaration's assumptions are the classical trio or none.

## Layout

Five files are LANDED: their text is the permanent text landing 2 proposes.

| Staged path | Source | What it is |
|---|---|---|
| `staged/lib/var_dist_supp.v` | PRODUCTION `lib/var_dist_supp.v` minus `card_tnth_count` and its header entry, and nothing else | landed |
| `staged/security/var_dist_joint_law.v` | NEW; five lemmas of probe `p1_joint_law_distance.v` and `p9_actual_marginals.v` | landed |
| `staged/instances/kim2025/five_card_mixing.v` | PRODUCTION `instances/kim2025/five_card_mixing.v` plus `card_tnth_count`, minus `kim_centi_marginal_bound40` and `kim_centi_cut_mixing40` | landed |
| `staged/manifest/pgg_tableau_arm_relations.v` | NEW; six declarations of probe `p7_mutations.v` and `p8_spectral_relation.v` | landed |
| `staged/instances/kim2025/five_card_proximity.v` | NEW; thirty-two declarations of probe `p4_kim_biased_proximity.v`, `p7_mutations.v`, `p8_spectral_relation.v`, `p9_actual_marginals.v` | landed |

Ten files are CHAIN-CONSISTENCY COPIES. They are unchanged text and are not
landed. They exist so that everything downstream of `lib/var_dist_supp.v`
compiles against the staged library rather than against production's, which
is what the `cp` will force in production.

| Staged path | Copied unchanged from |
|---|---|
| `staged/instances/kim2025/five_card_analysis.v` | PRODUCTION `instances/kim2025/five_card_analysis.v` |
| `staged/manifest/pgg_analysis_manifest.v` | PRODUCTION `manifest/pgg_analysis_manifest.v` |
| `staged/manifest/pgg_analysis_client.v` | PRODUCTION `manifest/pgg_analysis_client.v` |
| `staged/manifest/pgg_tableau.v` | landing 1's `staged/manifest/pgg_tableau.v` |
| `staged/manifest/pgg_tableau_syntax.v` | landing 1's `staged/manifest/pgg_tableau_syntax.v` |
| `staged/instances/pgl27/pgl27_rows.v` | landing 1's staged copy |
| `staged/instances/kim2025/five_card_rows.v` | landing 1's staged copy |
| `staged/instances/s5/s5_rows.v` | landing 1's staged copy |
| `staged/instances/psl211/psl211_reading_constancy.v` | landing 1's staged copy |
| `staged/instances/psl211/psl211_rows.v` | landing 1's staged copy |

The seven copies taken from landing 1 come from its **commit `d737a46`**, "probe(tableau-ext
landing 1): fix pass 1 after the two audits", which is the branch HEAD as this
file is written and which landing 1's working tree matches exactly. That fix
pass changed comments in `pgg_tableau.v`, `pgl27_rows.v` and
`psl211_reading_constancy.v`, and added four `_armE` lemmas to
`five_card_rows.v`: `five_card_row_repeated_indistinguishability_armE`,
`five_card_row_biased_indistinguishability_armE`,
`five_card_row_repeated39_armE` and `five_card_row_biased_inv25_armE`, each
`exact: erefl` at `InputIndistinguishabilityArm`. They are additions, so
nothing landing 2 states changed.

Seven, not six: `psl211_rows.v` is a landing-1 file as well, and `restage.py`
copies all seven.

**Landing 1 may move again**, and a landing-2 compile is evidence only against
the landing-1 text it loaded. `restage.py` is how to redo this:

```
python3 restage.py --check     # report which of the six differ, and whether
                               # the difference is code or comments only
python3 restage.py             # copy them and recompile the whole chain
```

It reports each file as `unchanged`, `comments only` or `CODE CHANGED`, using
the same comment-stripped token comparison `verify.py` uses, then calls
`compile.py` with no arguments, which compiles the `_CoqProject` order: the
fifteen staged files and the fidelity file, one Rocq process at a time through
the `rocq1` lock. Equivalently, by hand: copy the seven paths of
`restage.py`'s `CHAIN` from
`notes/probes/2026-09-20-tableau-extensions-landing1/staged/` and run
`python3 compile.py`.

One measurement worth carrying: a recompile of
`staged/instances/kim2025/five_card_rows.v` once reported 149.4 s wall with no
sentence over 5 s, and an immediate second run reported 4.5 s. The `rocq1`
lock is machine-wide, so a wall time measured while another session compiles
includes that session's run. Every number in the table below was measured with
no other Rocq process running.

Those ten plus `five_card_mixing.v` are exactly the eleven files of
`lib/var_dist_supp.v`'s reverse closure, which the design's section 3
computes. None of the eleven is in the forward closure of
`instances/psl211/psl211_endpoints.v`: that file was never compiled here, and
`psl211_reading_constancy.v`, `psl211_models.v` and `psl211_analysis.v` load
`psl211_endpoints.vo` by digest, which is R3's recorded state.

`_CoqProject` records the flags and the compile order. `compile.py` reads the
flags out of `_CoqProject` so the two cannot drift, and drives every
`rocq compile` through the machine-wide `rocq1` lock, one process at a time.
`verify.py` prints the four checks below; `verify.out` is its captured output
and `landing_fidelity.out` the fidelity run's.

### The load-path order

Landing 1 measured it and this directory reuses it: Rocq 9.0.0 resolves a
`Require` to the LAST matching `-R`/`-Q` entry, so the staged roots are the
last entries bound to `pgg_smc`, after production's AND after
`-Q . tableau_ext_landing2`. Landing 2 adds `-R staged/lib pgg_smc` to that
block. The run prints one `overriding-logical-loadpath` warning per staged
root, which is that remapping and not an error.

---

## E1 — `lib/var_dist_supp.v` loses one lemma and gains nothing

The first staging put the five joint-law lemmas here and had to add
`From mathcomp Require Import lra` and
`From pgg_smc Require Import pgg_collusion_bound` to carry them, which made a
`lib/` file depend on a `security/` one. That is not accepted (Q3). The five
lemmas are re-homed to `staged/security/var_dist_joint_law.v` (E1b), and this
file's only difference from production is D5's removal:

- `card_tnth_count` and its proof deleted, with the banner above them.
- Its two lines removed from the header's `Lemmas:` block.
- The header's description sentence, which named it, rewritten:
  - before: "…the invariance of a uniform law under an injective endomap, the
    fact that a pushforward charges only the image, and the count of the tuple
    positions at which a predicate holds."
  - after: "…the invariance of a uniform law under an injective endomap, and
    the fact that a pushforward charges only the image. The distance between
    two joint laws of a reading and a secret is
    security/var_dist_joint_law.v."

The import block is production's, unchanged. Whole-file token diff against
production: **1 hunk, 57 tokens, the deleted lemma**. Nothing else in the file
moved.

---

## E1b — the new `security/var_dist_joint_law.v`

Q3's re-homing. Five lemmas, all token-identical to the probe's; `verify.py`
reports `5 of 5 declarations token-identical to the probe's`, so the move
changed no statement and no proof.

| Lemma | Probe source | Why it lands |
|---|---|---|
| `var_dist_fdistmap_pair` | `p1_joint_law_distance.v:61` | the data-processing step down to the pair |
| `var_dist_prodR` | `p1_joint_law_distance.v:84` | the step up from the cut, D5 |
| `var_dist_prodL` | `p1_joint_law_distance.v:100` | premise of `var_dist_own_marginals`, Q1 accepted |
| `fdist_prod_snd` | `p1_joint_law_distance.v:115` | D5 |
| `var_dist_own_marginals` | `p9_actual_marginals.v:65` | removes the ideal from the comparison |

`security/` is the right layer, because both data-processing steps come from
there: `var_dist_fdistmap` is `security/pgg_collusion_bound.v:126` and
`var_dist_triangle` is `:43`, and neither is in infotheo's
`variation_dist.v`, which carries only `symmetric_var_dist`. The file
`Require`s `var_dist_supp` and `pgg_collusion_bound`, both already in
`pgg_smc`, plus `lra` for the one arithmetic step of
`var_dist_own_marginals`. No cycle: `pgg_collusion_bound` requires
`perm_uniform` and `pgg_interface` only.

Name checks before the file was written. No module named `var_dist_joint_law`
exists anywhere in the tree. Of the five lemma names, only `var_dist_prodR`
occurs in production, twice, and both are `Local`:
`instances/pgl27/pgl27_mixing.v:1077` and
`instances/psl211/psl211_mixing.v:577`, invisible outside their files. R5's
decision leaves both, and the new lemma's comment names them.

Two comment changes against the probe's text, both deliberate:

`var_dist_prodR`, R5's sentence appended:

> Two section-local proofs of this statement predate the one here, at
> instances/pgl27/pgl27_mixing.v and instances/psl211/psl211_mixing.v; each is
> used once, inside its own file's joint mixing lemma, and neither is visible
> outside it.

`var_dist_prodL`, one word, because the probe's comment pointed at a
"corollary" that is a theorem in this tree:

- before: "The **corollary** about the actual model alone needs both sides"
- after: "The **statement** about the actual model alone needs both sides"

The file header is quoted in full in the report; it states what the file is
about (the sum of absolute differences between joint laws, twice the total
variation distance of the literature, bounding twice an advantage), which
lemma carries a bound in which direction, and a `Lemmas:` table.

Reverse closure: `instances/kim2025/five_card_proximity.v` only.
`manifest/pgg_tableau_arm_relations.v` does not `Require` it, because
`idealproximity_prop_at2` needs `var_dist_le2` of `var_dist_supp` and no
joint-law lemma.

---

## E2 — the move and the withdrawal in `five_card_mixing.v`

`card_tnth_count` is added immediately before `Section
five_card_colour_census`, which is the section holding
`den_boer_layout_law_const`, its only call site anywhere in the tree
(`instances/kim2025/five_card_mixing.v:279` before the move). It cannot go
inside that section, because it is stated at no real field. Its code tokens
are identical to `lib/var_dist_supp.v`'s. Its comment gains the file's own
leading-name convention, which every other comment in `five_card_mixing.v`
uses:

- before: "The positions of a tuple at which a predicate holds are counted…"
- after: "card_tnth_count — the positions of a tuple at which a predicate
  holds are counted…"

`kim_centi_marginal_bound40` and `kim_centi_cut_mixing40` are removed (D3).
Landing 1 rerouted their only consumer, so nothing in the tree names them: a
whole-tree scan outside `notes/` returns only these two definitions and
`instances/kim2025/five_card_rows.v`, which landing 1 replaces.

Three further sentences of the file named them and are rewritten:

1. Header `Definitions:` block: the `kim_centi_marginal_bound40` entry removed.
2. Header `Key results:` block: the `kim_centi_cut_mixing40` entry removed,
   and `card_tnth_count` added at the top of that block.
3. Header prose, line 20 of production:
   - before: "Each law is given in the two forms the rows use, the bundle's
     own spectral number and the constant a text quotes."
   - after: "The seven-cut law is given at the bundle's own spectral number,
     the one-cut law at that number and at the exact one fiftieth its row
     publishes."
   The rewrite is forced: after the withdrawal the seven-cut law has only one
   form in this file.
4. The section banner at production `:497-499`:
   - before: "The same two distances at the constants the two rows republish"
   - after: "The one-cut distance at the constant the row publishes"
   What remains under that banner is `kim_one_cut_centi_le`,
   `kim_biased_marginal_bound_exact` and `kim_biased_cut_mixing_exact`, all
   about the one-cut law.

No other sentence of `five_card_mixing.v` speaks of the two withdrawn names;
`verify.py`'s scan reports zero hits for either name anywhere under `staged/`.

Whole-file token diff against production: 2 hunks, the addition and the
removal.

---

## E3 — the new `manifest/pgg_tableau_arm_relations.v`

R8's decision: the declarations that name no instance do not go to an instance
file. Six land here, exactly the tables' list under R8.

| Declaration | Probe source | Kind |
|---|---|---|
| `idealproximity_prop_at2` | `p7_mutations.v:87`, where the probe names it `idealproximity_ceiling` | Lemma |
| `indistinguishability_prop_cert_free` | `p8_spectral_relation.v:100` | Lemma |
| `idealproximity_prop_cert_free` | `p8_spectral_relation.v:111` | recorded `Fail` |
| `indistinguishability_cert_in_proximity_prop` | `p8_spectral_relation.v:120` | recorded `Fail` |
| `idealproximity_reading_le` | `p8_spectral_relation.v:133` | Lemma |
| `idealproximity_tail_without_independence` | `p7_mutations.v:164` | recorded `Fail` |

All six are token-identical to the probe's, and the `Section
proximity_against_indistinguishability` wrapper of `p8_spectral_relation.v`
is kept intact with its four `Variable`s.

The design's section 2 and R8 both say
`idealproximity_tail_without_independence` "is stated at a five-card
certificate". It is not: its binders are `(A : PGGAlgebraic)`,
`(E : ExecutionParams A)`, `(sa : SampleAdapter R (instance_exec E))`,
`(cert : IdealProximityCert sa)`, and it names no instance. Under R8's rule it
therefore belongs in this file, and that is where it is. Recorded as question
Q2.

Two comment changes, both removals of a pointer into another file:

`idealproximity_prop_at2`, last sentence removed:

- before: "…a published number says something about a coalition exactly in so
  far as it is below two. **Kim's one-cut row publishes one fiftieth, and
  kim_biased_proximity_cert_eps_lt2 of p4_kim_biased_proximity.v is the
  comparison.**"
- after: the sentence is gone. A framework-level statement does not cite where
  an instance exhibits it, which is landing 1's Q2 ruling applied again.

`indistinguishability_prop_cert_free`, last clause shortened:

- before: "…idealproximity_ceiling holds it at two whatever the premise, **and
  the two lemmas at the end of this file hold it at the five-card instance at
  one fiftieth.**"
- after: "…idealproximity_ceiling holds it at two whatever the premise."
  Fix pass 1 rewrote this clause again, at N15 below.
  The two lemmas it named are not in this file; they are in
  `five_card_proximity.v`, and the header of this file says where.

Imports: `p8_spectral_relation.v`'s block minus every five-card and S5 module,
plus `var_dist_supp` for `var_dist_le2`. `pgg_tableau_syntax` is not imported,
because no declaration here uses the statement surface.

Header: what the file states, the two arms' propositions and the carrier they
share, the scale a published number is read against, where the arm's
mathematics is spent, and a `Not claimed.` paragraph. The type-honest
reading of the partial verdict is in that
paragraph: no implication from the input-indistinguishability proposition to
the proximity proposition at a constant below two, uniform in the certificate,
is claimed; no countermodel is built; no derivation from an
input-indistinguishability certificate's own fields is claimed; and the
implication that does hold at the five-card instance holds because its
conclusion is a theorem there and its premise is discarded.

Reverse closure: empty. `five_card_proximity.v` uses none of the six, so it
does not `Require` this file.

---

## E4 — the new `instances/kim2025/five_card_proximity.v`

Thirty-two declarations, all token-identical to the probe's, plus six
recorded `Fail`s beside the rows they guard.

| Group | Declarations | Probe source |
|---|---|---|
| the distance | `five_card_uniform_pairE`, `five_card_reading_secretE`, `five_card_arg_cut_prodE`, `kim_biased_proximity_close` | `p4:86,95,116,136` |
| the certificate | `kim_biased_proximity_cert`, `kim_biased_proximity_cert_idealE` | `p4:176,190` |
| the number | `kim_biased_proximity_cert_epsE`, `kim_biased_proximity_eps_halfE`, `kim_biased_proximity_cert_eps_lt2` | `p4:207,220,230` |
| the two rows | `five_card_row_biased_branch_indistinguishability` and its `_atE`, `_rowE`, `_armE`; `five_card_row_biased_proximity` and its `_rowE`, `_publishedE`, `_armE`; `five_card_row_biased_arm_neq` | `p4:245,255,261,300,275,285,290,313,321` |
| what the row states | `five_card_biased_view_proximity` | `p4:337` |
| the actual model alone | `five_card_biased_view_own_marginals` | `p9:98` |
| the number cannot move down | `five_card_reprice_inv100`, `kim_biased_conclude_below_false` | `p7:99,107` |
| every hypothesis discharged | `five_card_singleton_below_threshold`, `five_card_biased_proximity_at_singleton` | `p7:118,127` |
| the arm's proposition here | `five_card_biased_proximity_prop_holds`, `five_card_biased_indistinguishability_implies_proximity` | `p8:173,184` |
| recorded `Fail`s | `five_card_biased_proximity_by_computation`, `five_card_biased_proximity_by_done`, `kim_biased_cert_s5_ideal`, `kim_centi_proximity_from_biased`, `five_card_row_repeated_proximity`, `kim_biased_indistinguishability_from_centi` | `p7:141,149,187,202,208,218` |

The bare `Check five_card_biased_proximity_at_singleton.` of `p7:131` does NOT
land (Q5): a `Check` states no proposition, so it stays in the probe. The
definition it checked lands, and `landing_fidelity.v` pins it by
`Print Assumptions` instead. The `Check` is also gone from the fidelity file.

It `Require`s `security/var_dist_joint_law.v`, landing 1's staged
`five_card_rows` and `s5_rows`, and the staged framework, through `From pgg_smc Require Import` in every case. The `s5_rows`
edge exists only for `kim_biased_cert_s5_ideal`, whose subject
`s5_rand_exact_witness` is declared at `instances/s5/s5_rows.v:255`; the
design's section 3 keeps that edge deliberately.

Four comment changes, all narration removals:

`five_card_row_biased_branch_indistinguishability_atE`, the source comment
above the proof:

- before: "exact: erefl and not by [], following the hang shape recorded in
  STATUS.md: done does not return on an equation between two rows'
  coordinates."
- after: "exact: erefl and not by [], because done does not return on an
  equation between two rows' coordinates."

`kim_biased_conclude_below_false`:

- before: "…is false, and not merely beyond what **the probe could prove**"
- after: "…is false, and not merely beyond what **could be proved**"

`five_card_biased_proximity_prop_holds`:

- before: "It is the conclusion **the spec's P8 row wants**, standing on its
  own at this instance."
- after: "It is the **arm's** conclusion standing on its own at this instance."

`five_card_biased_indistinguishability_implies_proximity`:

- before: "The implication holds and carries no information: **what the spec
  asks for is** a derivation that reads the input-indistinguishability
  certificate's fields, and **this is not one**."
- after: "The implication holds and carries no information: a derivation that
  reads the input-indistinguishability certificate's fields **is a different
  statement and is not this one**."

`five_card_biased_view_own_marginals` is restated in the permanent voice,
because the probe's comment opened by naming a ledger row's reading:

- before: "Kim's one-cut row, read as a statement about that model alone: at
  fewer than two colluding seats, the joint law of the coalition's executed
  view with the conjunction of the committed bits is within three fiftieths of
  the product of its own two marginals. The den Boer uniform model has left
  the statement, and what remains is a bound on how far the one-cut run is
  from making a coalition's reading and the secret independent."
- after: "The same statement with the den Boer uniform model removed: at fewer
  than two colluding seats, the joint law of the coalition's executed view
  with the conjunction of the committed bits is within three fiftieths of the
  product of its own two marginals. What remains is a bound on how far the
  one-cut run is from making a coalition's reading and the secret independent,
  and the advantage a distinguisher gets from it is at most three hundredths."

The added clause is read off the number: `var_dist` is the sum of absolute
differences, so three fiftieths bounds twice the advantage and the advantage
is at most three hundredths.

Header: the probe's P4 header without its "Probe P4" line, plus a paragraph
for the three readings of the published number, plus a `Not claimed.`
paragraph pointing at `manifest/pgg_tableau_arm_relations.v`, plus
`Definitions:` and `Key results:` blocks. The sentence "That number bounds a
sum of absolute differences, twice the total variation distance, so a
distinguisher's advantage against this row is at most one hundredth" is new
and is read off `kim_biased_proximity_cert_epsE`.

---

## The recorded `Fail`s, and why each fails

Nine `Fail` guards land across the two new files. Each was re-compiled without
its `Fail`, one file per guard, in the scratchpad and never in the repository
(`/private/tmp/.../scratchpad/unfail_f1.v` … `unfail_f9.v`). All nine fail,
and each fails for the reason its comment states.

| Guard | File | Error |
|---|---|---|
| `idealproximity_prop_cert_free` | arm relations | `No applicable tactic` — `by []` does not close the equality, which is what "not closed by conversion" says |
| `indistinguishability_cert_in_proximity_prop` | arm relations | `The term "cert" has type "IndistinguishabilityCert sa" while it is expected to have type "IdealProximityCert ?sa"` |
| `idealproximity_tail_without_independence` | arm relations | `Cannot apply lemma (ipc_close cert HC)` — the final application, exactly as the comment says |
| `five_card_biased_proximity_by_computation` | five-card | `Unable to unify "true" with "var_dist …"` — `reflexivity` does not close it |
| `five_card_biased_proximity_by_done` | five-card | `No applicable tactic` |
| `kim_biased_cert_s5_ideal` | five-card | `SampleAdapter R (OE.oe_execution s5_rand_observed)` against `SampleAdapter R (instance_exec five_card_params)`, at the ideal field and not inside the proposition |
| `kim_centi_proximity_from_biased` | five-card | `IdealProximityCert (amf_sample kim_biased_family R idx)` against `… kim_centi_family …` |
| `five_card_row_repeated_proximity` | five-card | the payload's adapter: `IdealProximityCert (amf_sample kim_biased_family R idx)` against `IdealProximityCert (amf_sample (sp_f (tableau_at five_card_row_repeated_tableau)) R idx)` |
| `kim_biased_indistinguishability_from_centi` | five-card | `IndistinguishabilityCert (amf_sample kim_centi_family R idx)` against `… kim_biased_family …`, the same coordinate as the two above |

`rocq compile` echoes nothing for a `Fail` guard, so the guards' own compile
is evidence only that they fail, not why. The nine scratch files are the
record of why.

---

## Compiles

One Rocq process at a time, through the `rocq1` lock, `rocq compile` with
`-time`, never `make`. `instances/psl211/psl211_endpoints.v` was never
compiled. Nothing was written into a production directory: every `.vo` lands
beside its `.v` under `staged/`.

| File | rc | wall | sentences over 5 s |
|---|---|---|---|
| `staged/lib/var_dist_supp.v` | 0 | 4.1 s | none |
| `staged/security/var_dist_joint_law.v` | 0 | 3.9 s | none |
| `staged/instances/kim2025/five_card_mixing.v` | 0 | 4.1 s | none |
| `staged/instances/kim2025/five_card_analysis.v` | 0 | 3.8 s | none |
| `staged/manifest/pgg_analysis_manifest.v` | 0 | 5.8 s | one, 5.15 s, the `Require Export` block |
| `staged/manifest/pgg_tableau.v` | 0 | 12.9 s | none |
| `staged/manifest/pgg_tableau_syntax.v` | 0 | 4.3 s | none |
| `staged/instances/pgl27/pgl27_rows.v` | 0 | 6.3 s | none |
| `staged/instances/kim2025/five_card_rows.v` | 0 | 4.6 s | none |
| `staged/instances/s5/s5_rows.v` | 0 | 4.0 s | none |
| `staged/instances/psl211/psl211_reading_constancy.v` | 0 | 22.2 s | three, 5.06 s, 6.05 s and 6.06 s |
| `staged/instances/psl211/psl211_rows.v` | 0 | 5.5 s | none |
| `staged/manifest/pgg_analysis_client.v` | 0 | 3.8 s | none |
| `staged/manifest/pgg_tableau_arm_relations.v` | 0 | 3.8 s | none |
| `staged/instances/kim2025/five_card_proximity.v` | 0 | 5.7 s | none |
| `landing_fidelity.v` | 0 | 28.2 s | none |

Fifteen staged files and the fidelity file, compiled in the `_CoqProject`
order by `python3 compile.py` with no arguments. The slow sentence of
`pgg_analysis_manifest.v` is its `Require Export` block,
which loads the four facades. The three of `psl211_reading_constancy.v` are
the `by split; vm_compute` and the two `rewrite -!size_filter` the Kim landing
and landing 1 both measured at the same cost. No sentence of the four landed
files is over 5 s.

---

## `Print Assumptions`

35 declarations, from `landing_fidelity.out`. The trio is
`constructive_indefinite_description`, `functional_extensionality_dep` and
`propositional_extensionality`.

| Group | Declarations | Assumptions |
|---|---|---|
| `security/var_dist_joint_law.v` | `var_dist_fdistmap_pair`, `var_dist_prodR`, `var_dist_prodL`, `fdist_prod_snd`, `var_dist_own_marginals` | trio |
| `five_card_mixing.v` | `card_tnth_count` | **closed under the global context** |
| `pgg_tableau_arm_relations.v` | `idealproximity_prop_at2`, `indistinguishability_prop_cert_free`, `idealproximity_reading_le` | trio |
| `five_card_proximity.v` | `five_card_uniform_pairE`, `five_card_reading_secretE`, `five_card_arg_cut_prodE`, `kim_biased_proximity_close`, `kim_biased_proximity_cert`, `kim_biased_proximity_cert_idealE`, `kim_biased_proximity_cert_epsE`, `kim_biased_proximity_eps_halfE`, `kim_biased_proximity_cert_eps_lt2`, `five_card_row_biased_branch_indistinguishability` and its `_atE`, `_rowE`, `_armE`, `five_card_row_biased_proximity` and its `_rowE`, `_publishedE`, `_armE`, `five_card_row_biased_arm_neq`, `five_card_biased_view_proximity`, `five_card_biased_view_own_marginals`, `five_card_reprice_inv100`, `kim_biased_conclude_below_false`, `five_card_biased_proximity_at_singleton`, `five_card_biased_proximity_prop_holds`, `five_card_biased_indistinguishability_implies_proximity` | trio |
| `five_card_proximity.v` | `five_card_singleton_below_threshold` | **closed under the global context** |

No axiom other than the trio appears anywhere in the run, and no `Axiom`,
`Parameter`, `Admitted` or `Abort` is introduced by any landed file.
`card_tnth_count` and `five_card_singleton_below_threshold` are closed because
neither passes through a real field: one counts a tuple's positions and the
other compares two natural numbers.

---

## `landing_fidelity.v`

Logical path `tableau_ext_landing2`. It `Require`s the staged copies through
`pgg_smc`, which the flags resolve to `staged/`. Every restatement is the
probe's statement verbatim and is closed by `exact: <staged name>`; no `by []`
and no `done` appears on a `published_at` or `published_row` equation.

What it checks:

| Section | Checks |
|---|---|
| provenance | `Check var_dist_own_marginals`, `Check var_dist_prodL`, `Check var_dist_fdistmap_pair`, `Check card_tnth_count`, and `Fail Check` on `kim_centi_marginal_bound40`, `kim_centi_cut_mixing40`, `kim_centi_cert40`, `kim_centi_cert40_epsE` |
| the promotion | all five lemmas restated and closed by the staged `var_dist_joint_law` |
| the move | `card_tnth_count` restated and closed by the staged `five_card_mixing` |
| the arm relations | the three lemmas restated with their four section variables |
| the five-card distance | the four lemmas of the distance section restated |
| the certificate | its type ascribed, its ideal equation, and all three number lemmas |
| the two rows | both `PublishedRow`s ascribed, the two `_rowE`, the `_atE`, the `_publishedE`, both `_armE` and the `arm_neq` |
| the published number | `five_card_reprice_inv100 R = Some (1 / 100)` and the refutation at that number |
| the theorems | `five_card_biased_view_proximity` at one fiftieth and `five_card_biased_view_own_marginals` at three fiftieths |
| assumptions | the 35 `Print Assumptions` above |

The provenance test is one-sided in both directions. No production load path
holds a `var_dist_joint_law` at all, so a `Require` of it that resolves
resolved to the staged tree, and the three `Check`s on its lemmas would error
otherwise. If
production's `five_card_mixing.vo` or `five_card_rows.vo` were loaded, the
four `Fail Check`s would error, because each of those names exists there.

The nine recorded `Fail` guards are not restated in the fidelity file: a
`Fail` declares nothing, so there is no statement to ascribe. Their fidelity
is the token check of `verify.py` and the nine scratch compiles above.

---

## `verify.py`

Four checks, output in `verify.out`.

1. **Whole-file token diffs against production.** `var_dist_supp.v`: 1 hunk,
   57 tokens, the deletion of `card_tnth_count`. `five_card_mixing.v`:
   2 hunks, the addition of `card_tnth_count` and the removal of the two
   withdrawn declarations. Nothing else in either file moved.
2. **Per-declaration token diffs against the probe.** Every landed declaration
   is looked up by name in the probe file that declares it. Result: all five
   of `security/var_dist_joint_law.v`, `card_tnth_count`, all six of
   `pgg_tableau_arm_relations.v` and all 32 of `five_card_proximity.v` are
   token-identical to their source. Zero hunks anywhere. This is the token
   proof that Q3's re-homing moved the five lemmas without touching them.
3. **Comment word diffs.** Every difference is listed with before and after in
   E1 to E4 above and classified: one R5 addition, one wrong-word fix, one
   naming-convention prefix, and six narration removals.
4. **Scans.** `SpectralDecay` 0, `SpectralCert` 0, `_indist\b` 0,
   `RepricePayload` 0, any abbreviation of "indistinguishability" 0, `apex` 0,
   `gate`/`gates`/`gated`/`gating` 0, `posit`/`posits`/`posited`/`positing` 0,
   `L1` 0. `kim_centi_marginal_bound40` and `kim_centi_cut_mixing40` have two
   hits each, both in `landing_fidelity.v`: its header sentence and its
   `Fail Check`. Lines over 80 bytes: four, all in chain-consistency copies
   (`five_card_analysis.v:336` at 81 bytes, from production;
   `pgg_tableau_syntax.v:333,371,403` at 101, 90 and 128 bytes, from landing
   1). None is in a landed file.

---

## `_CoqProject` placement

Production's `_CoqProject` is not edited here. The two new lines, and the
existing line each goes after:

| New line | Inserted after | Why |
|---|---|---|
| `security/var_dist_joint_law.v` | `security/pgg_collusion_bound.v` (`_CoqProject:87`), before `security/pgg_security_solver.v` | it `Require`s `pgg_collusion_bound` and `lib/var_dist_supp.v` (`:35`) and nothing else of the project |
| `manifest/pgg_tableau_arm_relations.v` | `manifest/pgg_tableau_syntax.v` (`_CoqProject:220`), before `instances/pgl27/pgl27_rows.v` | it `Require`s `pgg_tableau` and `var_dist_supp` and nothing below them |
| `instances/kim2025/five_card_proximity.v` | `instances/s5/s5_rows.v` (`_CoqProject:223`), before `instances/psl211/psl211_reading_constancy.v` | Q4: it `Require`s `five_card_rows` and `s5_rows`, so it goes after both |

---

## The five questions, as ruled

| Q | Ruling | How it is built |
|---|---|---|
| Q1 | accepted, `var_dist_prodL` lands | it is in `security/var_dist_joint_law.v` as a premise of `var_dist_own_marginals`; `fdist_uniform_prod` stays in the probe |
| Q2 | accepted | `idealproximity_tail_without_independence` is in `manifest/pgg_tableau_arm_relations.v` |
| Q3 | not accepted as first built | the five lemmas moved to the new `staged/security/var_dist_joint_law.v`; `staged/lib/var_dist_supp.v` differs from production by the one removal and nothing else, its import block reverted |
| Q4 | accepted | the `_CoqProject` line for `five_card_proximity.v` goes after `instances/s5/s5_rows.v` |
| Q5 | accepted | the bare `Check five_card_biased_proximity_at_singleton.` is gone from the staged file and from `landing_fidelity.v`; the definition still lands and is pinned by `Print Assumptions` |

Nothing is left open. The one thing the main session must redo if landing 1
moves again is the restage, and `restage.py` above is how.

---

# Fix pass 1

Date: 2026-09-20, after `soundness-audit-landing2.md` and
`naming-audit-landing2.md`. Edited: the five landed files,
`landing_fidelity.v`, `verify.py` and this file. The ten chain-consistency
copies were not touched and not re-copied.

**Code-token diff against `b5c4094`**, comments stripped: 2 tokens in
`staged/manifest/pgg_tableau_arm_relations.v`, which is the N12 rename, and
0 tokens in each of the other four landed files. `landing_fidelity.v` gains
33 code tokens: the three S6 provenance probes, the rename at three sites,
and the one `Check` of soundness N5. Every comment passage that changed maps
to a finding below.

**Compiles**, `python3 compile.py`, the `_CoqProject` order, through the
`rocq1` lock, `rocq compile` and never `make`,
`instances/psl211/psl211_endpoints.v` never compiled:

| File | rc | wall |
|---|---|---|
| `staged/lib/var_dist_supp.v` | 0 | 16.3 s |
| `staged/security/var_dist_joint_law.v` | 0 | 4.1 s |
| `staged/instances/kim2025/five_card_mixing.v` | 0 | 4.3 s |
| `staged/instances/kim2025/five_card_analysis.v` | 0 | 3.9 s |
| `staged/manifest/pgg_analysis_manifest.v` | 0 | 6.0 s |
| `staged/manifest/pgg_tableau.v` | 0 | 13.1 s |
| `staged/manifest/pgg_tableau_syntax.v` | 0 | 4.4 s |
| `staged/instances/pgl27/pgl27_rows.v` | 0 | 6.4 s |
| `staged/instances/kim2025/five_card_rows.v` | 0 | 4.6 s |
| `staged/instances/s5/s5_rows.v` | 0 | 4.0 s |
| `staged/instances/psl211/psl211_reading_constancy.v` | 0 | 22.0 s |
| `staged/instances/psl211/psl211_rows.v` | 0 | 5.4 s |
| `staged/manifest/pgg_analysis_client.v` | 0 | 3.9 s |
| `staged/manifest/pgg_tableau_arm_relations.v` | 0 | 3.7 s |
| `staged/instances/kim2025/five_card_proximity.v` | 0 | 5.6 s |
| `landing_fidelity.v` | 0 | 28.3 s |

No sentence of a landed file is over 5 s. `landing_fidelity.out` recaptured:
33 `Axioms:` blocks naming only the classical trio and 2 "Closed under the
global context", which is the 35 above unchanged. `verify.py` recaptured in
`verify.out`: 5 of 5, 6 of 6 and 32 of 32 declarations token-identical to the
probe's, the two whole-file hunks unchanged at 57 and 151 tokens, no
declaration with a code-token difference, and the scans clean, with the four
lines over 80 bytes all in chain-consistency copies as before.

## Soundness findings

**S1 (MUST).** `five_card_proximity.v` header. Final text:

> Both numbers come from one distance on the cut group, the one fiftieth of
> kim_biased_cut_mixing_exact. The input-indistinguishability arm doubles
> whatever marginal bound its certificate carries and the proximity arm
> spends the distance once, so the proximity row publishes one fiftieth where
> the row built on kim_biased_cert_exact, five_card_row_biased_inv25 of
> five_card_rows.v, publishes one twenty-fifth. The input-indistinguishability
> row continued below carries kim_biased_cert instead, whose marginal bound is
> the one-cut bundle's spectral number, and publishes sqrt 5 over forty.

Declarations read: `kim_biased_epsE` (`five_card_rows.v:555`,
`sw_bound_eps (kim_biased_marginal_bound R) = Num.sqrt 5%:R * (1 / 80)`);
`kim_biased_cert_epsE` (`:748`, `cert_eps (kim_biased_cert R idx) =
Num.sqrt 5%:R * (1 / 80) + Num.sqrt 5%:R * (1 / 80)`, so `cert_eps` doubles
the marginal bound); `five_card_row_biased_inv25 : PublishedRowAt
five_card_reprice_inv25` (`:860`) continuing `kim_biased_cert_exact` (`:833`)
with `five_card_reprice_inv25 = Some (1 / 25)` (`:850`);
`kim_biased_proximity_cert_epsE` (`ipc_eps … = 1 / 50`);
`kim_biased_proximity_eps_halfE` (`cert_eps (kim_biased_cert_exact R idx) =
ipc_eps … + ipc_eps …`). Deviation: "sqrt 5 over forty", not the audit's "the
square root of five over forty", because the file's own comment at
`kim_biased_proximity_eps_halfE` already spells it that way and one word per
concept applies.

**S2 + naming N8.** One text satisfying both, on `kim_biased_proximity_cert`:

> The ideal and the witness are the terms the published uniform row carries,
> which kim_biased_proximity_cert_idealE states, and the secret is the same
> conjunction that row's witness is stated at. The number is the bound
> kim_biased_cut_mixing_exact proves on the cut group's own distance, and the
> last field is kim_biased_proximity_close of this file, which says the
> distance between the two joint laws is at most that number.

The clause the naming audit was unsure of was checked and kept:
`five_card_exact_witness` is `@MkExactWitness R five_card_algebra
five_card_params (amf_sample five_card_uniform_family R idx) bool (Secret R)
(@five_card_static_obs_indep R idx)` (`five_card_rows.v:383`), and
`ew_secret` is the fifth argument, so the certificate's `ipc_secret`,
`five_card_leakage.Secret R`, is that same term.

**S3.** `five_card_biased_proximity_at_singleton`, final clause:

> The coalition is not empty, so the reading the bound is stated on is the
> seat's own content observation at that seat, where the empty coalition's
> reading is ord0 at every seat.

Checked against `static_coalition_obs` (`protocol/pgg_instance.v:481`),
`[ffun i => if i \in C then ex_content_obs E x … else ord0]`.

**S4 + naming N14.** One text on `idealproximity_reading_le`: the superlative
is gone and the checkable half of N14 is kept.

> This is the arm's number read on the carrier the input-indistinguishability
> arm states its own bound on, and it needs no model of one arm to be a model
> of the other.

**S5.** The `Not claimed.` paragraph of `pgg_tableau_arm_relations.v`:

> Refuting it needs a model whose reading law is the same at every run
> argument, which is what the input-indistinguishability proposition asks, and
> far from the ideal's, which is what the proximity conclusion forbids. No
> such model is built here, and no proof of the implication is given either.

**S6.** Three qualified provenance probes added to `landing_fidelity.v` beside
the existing block, in the spelling the audit reports and with no
`pgg_smc.` prefix needed:

```
Check var_dist_supp.var_dist_le2.
Fail Check var_dist_supp.card_tnth_count.
Check five_card_mixing.card_tnth_count.
```

The file compiles rc 0 with them, so the middle `Fail` is satisfied: the
staged `lib/var_dist_supp.v` no longer declares `card_tnth_count` and the
staged `five_card_mixing.v` does.

**Soundness N1.** `pgg_tableau_arm_relations.v` header, second paragraph:

> The proximity proposition does mention its certificate, through the ideal
> adapter, that ideal's witness and the actual model's secret, as its
> definition shows. The two recorded failures beside it record what a written
> term does with that: …

Checked against `IdealProximityPropAt` (`pgg_tableau.v:487`), which names
`ipc_secret cert`, `ipc_ideal cert` and `ew_secret (ipc_witness cert)`.

**Soundness N2, N3 with the naming report's table proposals.** The
`var_dist_joint_law.v` `Lemmas:` entries now read "two products with a common
left factor are exactly as far apart as their right factors" and "a joint law
within a number of a product law is within three times that number of the
product of its own marginals", so the shared factor and the factor three are
both in the table. Checked against `var_dist_prodR : var_dist (P `x Q1)
(P `x Q2) = var_dist Q1 Q2` and `var_dist_own_marginals : var_dist J
(Mr `x Ms) <= d -> var_dist J ((fdistmap fst J) `x (fdistmap snd J)) <=
3%:R * d`.

**Soundness N4.** No change, as proposed. The distinction recorded: the
header of `pgg_tableau_arm_relations.v` names
`instances/kim2025/five_card_proximity.v` as exposition of what is not
claimed, while the declaration comment of the renamed
`idealproximity_prop_at2` cites no instance. Header exposition may place the
file in the tree; a statement comment states the statement.

**Soundness N5.** Applied, one line, and it compiles:
`Check (five_card_biased_proximity_at_singleton : forall (R : realType)
(i : 'I_5), _).` in `landing_fidelity.v`.

**Soundness N6 with naming N17.** Proof strategy moved out of the two
docstrings into plain `(* *)` comments inside the proofs:
`var_dist_fdistmap_pair` gains `(* var_dist_fdistmap at (reading, secret),
then transitivity. *)` and `var_dist_own_marginals` gains the three sentences
about spending the number three times.

## Naming findings

**N1 (MUST).** The 14 missing entries added to the `Key results:` block of
`five_card_proximity.v`, each checked against its declaration, with the
block now indexing all 21 non-`Fail` declarations that are not in the
`Definitions:` block, so the file's coverage is 26 of 26. The two `_rowE`
share one entry because both conclude `= five_card_row_biased`. Deviation on
one entry: `kim_biased_proximity_cert_eps_lt2` reads "that number is below the
bound two var_dist_le2 gives", not the audit's "under the ceiling a variation
distance has", per the ruling on N12's prose half.

**N2 (MUST).** `var_dist_prodR`, history gone:

> Two files carry a section-local proof of the same statement,
> instances/pgl27/pgl27_mixing.v and instances/psl211/psl211_mixing.v. Each is
> used once, inside that file's joint mixing lemma, and neither is visible
> outside it.

**N3, N4 (MUST / SHOULD).** The header of `pgg_tableau_arm_relations.v` keeps
its own frame and the `Not claimed.` paragraph; the three sentences that copy
declaration comments are gone, and the paragraph that restated the proof of
`idealproximity_tail_without_independence` is cut to N3's one sentence:

> One recorded failure below says where the arm's mathematics is spent: the
> ideal witness's independence is what turns the ideal joint law into the
> product of its marginals, and the arm's proposition compares the actual
> joint law with exactly that product.

**N5, N6, N7, N9, N10, N11, N13, N15, N16, N18, N21, N25, N26, N27, N28.**
All applied. N9 and N10 together give
`five_card_biased_view_own_marginals`:

> The one-cut row's bound restated against the executed law's own two
> marginals: at fewer than two colluding seats, the joint law of the
> coalition's reading with the conjunction of the committed bits is within
> three fiftieths of the product of that same law's two marginals. The den
> Boer uniform model has left the statement. What remains is a bound on how
> far the one-cut run is from making a coalition's reading and the secret
> independent, and the advantage a distinguisher gets from it is at most three
> hundredths.

N10 also rewrites `five_card_biased_view_proximity`'s "executed coalition
view" to "the coalition's executed reading". After the pass, "view" appears in
the five landed files only inside identifiers.

Deviation on N13: the trailing clause names the certificate rather than
saying "the input-indistinguishability certificate of the same model", because
S1 establishes that the one-cut model carries two such certificates at two
different numbers:

> At one percent of that bound it is a weak separation and not a cryptographic
> one, as is kim_biased_cert_exact at one twenty-fifth.

`cert_eps (kim_biased_cert_exact R idx) = 1 / 25` by
`kim_biased_proximity_eps_halfE`, which is two percent of two.

**N12, as ruled.** `idealproximity_ceiling` is now
`idealproximity_prop_at2`. Updated at the declaration, the header entry, the
header prose, the docstring of `indistinguishability_prop_cert_free`,
`landing_fidelity.v` (the restatement's own name, its `exact:` and its
`Print Assumptions`), `verify.py` and this file. `verify.py` gains a
`RENAMED` map that rewrites the staged name to the probe's before the token
comparison and prints the substitution, so the declaration is still reported
token-identical to the probe's modulo that one name.

The prose half of the ruling removes "ceiling" from the five landed files:
`var_dist_supp.v` twice (the header sentence and the section banner, now "The
bound two on a variation distance"), `five_card_mixing.v` once, and
`five_card_proximity.v` three times. **Deviation to record:**
`lib/var_dist_supp.v` and `instances/kim2025/five_card_mixing.v` therefore
carry comment changes beyond the single documented change of E1 and E2. Both
are comment-only; the whole-file code-token diffs against production are
unchanged at 1 hunk / 57 tokens and 2 hunks / 151 tokens.

**N19, as ruled.** The file name stays `security/var_dist_joint_law.v` and the
header gains one sentence in the shape `five_card_mixing.v` uses for a
layering fact:

> The two variation-distance lemmas this file applies, var_dist_fdistmap and
> var_dist_triangle, are stated in security/pgg_collusion_bound.v, so the file
> sits above that one and not in lib/, which carries no dependency on
> security/.

Deviation: "variation-distance lemmas", not "data-processing lemmas".
`var_dist_fdistmap` (`security/pgg_collusion_bound.v:126`) is data processing;
`var_dist_triangle` (`:43`) is a triangle inequality, so the collective noun
the finding proposed would be false of one of the two.

**N22, as ruled.** The `Recorded failures:` block of
`pgg_tableau_arm_relations.v` is removed, following the tree's precedent that
a recorded `Fail` is not indexed. No such block was added to
`five_card_proximity.v`. The header prose that says what the file records is
kept, because it is not a copy of a declaration comment.

**N24.** Applied as one line: "The statements here separate the two that carry
a number."

**N31, declined.** Moving the `(* exact: erefl … *)` comment of
`five_card_row_biased_branch_indistinguishability_atE` inside `Proof. … Qed.`
is not a one-line change; it reflows a proof body that `verify.py` compares
token by token against the probe. The finding itself records the current
placement as reading fine and the convention as already satisfied: the comment
is a plain `(* *)` comment and not part of the docstring.

**N20, N23, N29, N30.** Recorded by the audit with no action, and none taken.

## Scans after the pass

No line over 80 bytes in any landed file and no box-comment row whose closing
`*)` is off column 80. Zero hits in the five landed files for `apex`,
`gate`/`gates`/`gated`/`gating`, `posit`/`posits`/`posited`/`positing`, `L1`,
any abbreviation of "indistinguishability", and the meta words `renamed`,
`formerly`, `no longer`, `predate`, `probe`, `stage`, `landing`, `audit`,
`spec`. "percent" is spelled one way in both files that use it.

---

# Fix pass 2

Date: 2026-09-20, after `audit-landing2-fix1.md` (verdict GO, two SHOULD and
nine NOTE). Comments only. Edited: `staged/instances/kim2025/
five_card_proximity.v`, `staged/manifest/pgg_tableau_arm_relations.v`,
`staged/security/var_dist_joint_law.v` and this file. The chain copies,
production, landing 1 and landing 3 were not touched.

**Code-token check against `da53033`**, comments stripped by a nesting- and
string-aware splitter, whitespace tokens compared: identical in all three
files, 466 tokens in `var_dist_joint_law.v`, 492 in
`pgg_tableau_arm_relations.v`, 1131 in `five_card_proximity.v`. A comment
word diff against `da53033` maps every changed passage to F1, F2, F3, F4, F5,
F7, F8, F9 or F10, and to nothing else.

**Compiles**, `python3 compile.py`, the `_CoqProject` order, through the
`rocq1` lock, `rocq compile` and never `make`,
`instances/psl211/psl211_endpoints.v` never compiled:

| File | rc | wall |
|---|---|---|
| `staged/security/var_dist_joint_law.v` | 0 | 32.1 s |
| `staged/manifest/pgg_tableau_arm_relations.v` | 0 | 3.6 s |
| `staged/instances/kim2025/five_card_proximity.v` | 0 | 5.6 s |
| `landing_fidelity.v` | 0 | 27.9 s |

No sentence over 5 s in any of the four.

## F1 (SHOULD), `five_card_proximity.v:22-27`

Final text:

> Both numbers come from one bound on the cut group's distance, the one
> fiftieth of kim_biased_cut_mixing_exact. The input-indistinguishability arm
> doubles whatever marginal bound its certificate carries and the proximity
> certificate carries that bound once, so the proximity row publishes one
> fiftieth where the row built on kim_biased_cert_exact,
> five_card_row_biased_inv25 of five_card_rows.v, publishes one twenty-fifth.

Declarations read: `kim_biased_cut_mixing_exact`
(`staged/instances/kim2025/five_card_mixing.v:529-535`) concludes `var_dist
(sw_rho_dist (kim_biased_marginal_bound_exact R)) (sa_cut_dist
(five_card_sample R)) <= sw_bound_eps (kim_biased_marginal_bound_exact R)`,
a `<=`, and `kim_biased_marginal_bound_exact` (`:521-527`) is
`@MkShuffleMarginalBound R FiveCardKim_M 1 (1 / 50) …`, so one fiftieth
bounds the cut-group distance and is not that distance. `cert_eps`
(`staged/manifest/pgg_tableau.v:470-474`) is `sw_bound_eps (ic_b cert) +
sw_bound_eps (ic_b cert)`, so the doubling half stands.

Deviation: the pass also changed the sentence the finding did not quote,
"one distance on the cut group" to "one bound on the cut group's distance",
because that apposition made one fiftieth the distance too, and a following
"that bound" needs an antecedent that is a bound. Both sentences are F1. The
rest of the paragraph is unchanged in words and rewrapped.

## F2 (SHOULD), `five_card_proximity.v:272-274`

Final text:

> The model the certificate calls ideal, and the witness it carries for it,
> are the model and the witness of the published uniform row. Conversion
> decides both, so the ideal a biased row is measured against is the model
> the published uniform row carries and not a second description of it.

Declarations read: `five_card_row_uniform : AnalysisPathRow`
(`staged/manifest/pgg_analysis_manifest.v:827`) publishes no model;
`five_card_row_uniform_tableau : PublishedRow`
(`staged/instances/kim2025/five_card_rows.v:400`) is what the lemma at
`:275-279` names, through `amf_sample (ab_f (published_at
five_card_row_uniform_tableau)) R idx`. The file's own phrase at `:255` is
"the terms the published uniform row carries", so one wording now serves both
places. Deviation: none.

## F3 (NOTE), `pgg_tableau_arm_relations.v:117-119`

Final text:

> An implication from this proposition to the proximity proposition does hold
> for all that, its premise discarded: idealproximity_prop_at2 gives the
> proximity proposition at two whatever the premise.

Declaration read: `idealproximity_prop_at2` (`:93-98`) is proved `by move=> C
_; exact: var_dist_le2`, so the premise is discarded and the implication
holds. "not empty" is gone. Deviation: none.

## F4 (NOTE), `pgg_tableau_arm_relations.v:33-36`

Final text:

> The arm's mathematics is spent on the ideal witness's independence: it
> turns the ideal joint law into the product of its marginals, and the arm's
> proposition compares the actual joint law with exactly that product. One
> recorded failure below is a written term that omits that independence.

Declarations read: `IdealProximityPropAt`
(`staged/manifest/pgg_tableau.v:491-506`) has `(fdistmap (sa_coalition_view …)
…) `x (fdistmap (ew_secret (ipc_witness cert)) …)` on its right, a product,
while `ipc_close` (`:220-232`) compares with the ideal's joint law; the
failure is `idealproximity_tail_without_independence` (`:194-…`), the
composition law with the independence deleted from its proof. The sentence no
longer makes the failure the source of the fact and claims no necessity.

Deviation: "omits that independence" where the audit proposed "omits it", so
the pronoun has a written antecedent across the line break.

## F5 (NOTE), `pgg_tableau_arm_relations.v:40-43`

Final text:

> Refuting it needs a model whose coalition readings at any two run arguments
> stay within the constant the input-indistinguishability proposition names,
> and whose distance to the ideal exceeds the constant the proximity
> conclusion is stated at.

Declaration read: `IndistinguishabilityPropAt cert c`
(`staged/manifest/pgg_tableau.v:456-465`) asks `var_dist (fdistmap
(static_coalition_obs C x) (sa_cut_dist sa)) (fdistmap (static_coalition_obs
C x') (sa_cut_dist sa)) <= c` for every coalition below the threshold, which
is sameness only at `c = 0`. The sentence now says "stay within the
constant", not "is the same".

Deviation: the sentence does not repeat the coalition-size premise. It
describes what a countermodel must satisfy and names the proposition for the
constant, so no scope condition is asserted away.

## F7 (NOTE), `five_card_proximity.v:561-563`

Final text:

> The proximity arm and the input-indistinguishability arm are rejected at the
> same argument, the sample adapter each certificate type is indexed by, so a
> certificate of either arm is rejected where the other model's is required.

Declarations read: the two `Fail`s, `kim_centi_proximity_from_biased`
(`:548-551`) and `kim_biased_indistinguishability_from_centi` (`:564-568`),
each a written term the elaborator rejects. The quantification over "ways" is
gone. Deviation: none.

## F8 (NOTE), `five_card_proximity.v:72-74`

Final text:

> five_card_arg_cut_prodE == at a product law on the sample space, that pair's
> joint law is the uniform pair tensored with the model's cut law

Declaration read: `five_card_arg_cut_prodE` (`:198-203`) is stated at
`(fdist_uniform five_card_card_bool2) `x W`, so the hypothesis the entry
dropped is now in it.

Deviation: "at a product law on the sample space" where the audit proposed
"at a sample law written as a product", because the declaration comment at
`:193-196` already says "a law on the sample space written as a product" and
one concept keeps one word. Same three lines.

## F9 (NOTE), `five_card_proximity.v:78-80`

Final text:

> kim_biased_proximity_cert_idealE == the certificate's ideal is the uniform
> row's model, and the port built from its witness is that row's port

Declarations read: the second conjunct of the lemma (`:278-279`) is
`ExactIndependence (ipc_witness (kim_biased_proximity_cert R idx)) = ab_port
(published_at five_card_row_uniform_tableau) R idx`, and `ExactIndependence`
is a `SecurityPort` constructor taking an `ExactWitness`
(`staged/manifest/pgg_tableau.v:239-243`), so a witness is not a port.
Deviation: none.

## F10 (NOTE), `var_dist_joint_law.v:26-29`

Final text:

> The two variation-distance lemmas this file takes from the tree,
> var_dist_fdistmap and var_dist_triangle, are stated in
> security/pgg_collusion_bound.v, so the file sits above that one and not in
> lib/, which carries no dependency on security/.

Declarations read: `var_dist_triangle` (`security/pgg_collusion_bound.v:43`)
and `var_dist_fdistmap` (`:126`); infotheo's `symmetric_var_dist` is applied
at `staged/security/var_dist_joint_law.v:157` and `:160`, which is why the
count is stated of the lemmas taken from this tree. Deviation: none.

## F6 and F11

No change, as instructed. F6 records a reading the naming pass made
deliberately. F11 would replace a `_` in an ascription in
`landing_fidelity.v`, which is a code change and out of scope for a
comment-only pass.

## Scans after the pass

All three files compile rc 0. No line over 80 bytes. Every box-comment row
closes at column 80; the four rows a width scan flags are the one-line
docstrings at `five_card_proximity.v:345`, `:374` and `:492` and the in-proof
comment at `var_dist_joint_law.v:77`, all four byte-identical to `da53033`.
Zero hits in the three files for `apex`, `gate`/`gates`/`gated`/`gating` and
`posit`/`posits`/`posited`/`positing`. No abbreviation of
"indistinguishability". The new prose says "reading", not "view", and carries
no meta narration.
## As built (2026-09-20)

Fix pass 2 was audited by the main session: comment-stripped code tokens of
the five landed files and of `landing_fidelity.v` are identical to da53033
(script), and the nine changed passages were read against the findings F1 to
F5 and F7 to F10 of `audit-landing2-fix1.md` (commit cb3adfc).

The five staged files were copied with `cp` to `lib/var_dist_supp.v`,
`security/var_dist_joint_law.v`, `instances/kim2025/five_card_mixing.v`,
`manifest/pgg_tableau_arm_relations.v` and
`instances/kim2025/five_card_proximity.v`; `cmp` reports each copy
byte-identical to its staged source. `_CoqProject` gained three lines:
`security/var_dist_joint_law.v` after `security/pgg_collusion_bound.v`,
`manifest/pgg_tableau_arm_relations.v` after `manifest/pgg_tableau_syntax.v`,
`instances/kim2025/five_card_proximity.v` after `instances/s5/s5_rows.v`.
Production was recompiled single-file in dependency order, fifteen files: the
eleven of `lib/var_dist_supp.v`'s reverse closure, that file, and the three new
ones, all rc=0.

As-built fidelity: `landing_fidelity.v`, unchanged, compiled from a scratch
directory against production's load path only: rc=0, 33 `Axioms:` blocks at
the three classical axioms and 2 closed under the global context, as in the
staged run. Its provenance probes (`Check var_dist_supp.var_dist_le2`,
`Fail Check var_dist_supp.card_tnth_count`,
`Check five_card_mixing.card_tnth_count`, the `Fail Check`s of the four
withdrawn `*40` names) now hold of production.
