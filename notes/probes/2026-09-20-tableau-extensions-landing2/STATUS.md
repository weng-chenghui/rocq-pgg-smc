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
`idealproximity_ceiling` needs `var_dist_le2` of `var_dist_supp` and no
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
| `idealproximity_ceiling` | `p7_mutations.v:87` | Lemma |
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

`idealproximity_ceiling`, last sentence removed:

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
  The two lemmas it named are not in this file; they are in
  `five_card_proximity.v`, and the header of this file says where.

Imports: `p8_spectral_relation.v`'s block minus every five-card and S5 module,
plus `var_dist_supp` for `var_dist_le2`. `pgg_tableau_syntax` is not imported,
because no declaration here uses the statement surface.

Header: what the file states, the two arms' propositions and the carrier they
share, the ceiling, where the arm's mathematics is spent, and a `Not claimed.`
paragraph. The type-honest reading of the partial verdict is in that
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
| `pgg_tableau_arm_relations.v` | `idealproximity_ceiling`, `indistinguishability_prop_cert_free`, `idealproximity_reading_le` | trio |
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