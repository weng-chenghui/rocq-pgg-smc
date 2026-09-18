# Two landings: the general dealer law, and Kim's rows as Tableau programs

Date: 2026-09-19. Both batches are merged into `main` (202d2a1, no remote).
Every `.v` edit was made by an Opus `rocq-prover` subagent, every result was
recompiled and scanned by the main session before it was committed, and each
batch passed an independent soundness audit and an independent naming audit.

Specs: [[20260918-general-dealer-law-landing-design]] and
[[20260919-kim-tableau-sampled-design]]. Earlier notes:
[[20260917-general-dealer-law-feasibility-design]] and
[[20260918-general-dealer-law-probe-result]]. Plans with as-built records:
`docs/superpowers/plans/2026-09-19-general-dealer-law-landing.md` and
`docs/superpowers/plans/2026-09-19-kim-tableau-sampled.md`.

## The common problem

Both batches guard against the same mistake: a sentence in the paper that says
more than a compiled theorem says. In the first batch the sentence would be
"any dealer law $\delta_s$ preserves privacy". In the second it would be "Kim's
$2^{-40}$ bound is coalition privacy". Each batch puts the honest statement in
the library, puts the refutation or the limit beside it, and makes the
difference a compiled fact and not a remark.

## Batch 1: the general dealer law

### What the paper needed

One dealer model that recovers the three existing privacy theorems, and a
precise condition on $\delta_s$. The feasibility probe had shown both. Its
declarations lived in probe files, so the paper had nothing to cite.

### What landed

| File | Content | Commit |
|---|---|---|
| new `reconstruct/dealer_privacy.v` | `dealer_shuffleP`, `dealer_shuffle_secret`, `dealer_shuffle_view`, `dealer_shufflePE`, `dealer_shuffle_view_indep`, `dealer_shuffle_view_indep_of_deck`, `inde_RV_fdistmap`, `fdistmap_prod_sectionE` | 6b1e418 |
| `reconstruct/design_privacy.v` | `uniform_fdistmap_pointE`, `uniform_fdistmap_fiberTE`; `uniform_fdistmap_fiberE` keeps its statement and is proved through the point lemma | 5f574d2 |
| `instances/pgl27/pgl27_profile_privacy.v` | `pgl27_view_indep_via_dealer`, `pgl27_view_indep_alldecks_via_dealer` and their dealer data | 1284f7f |
| `instances/psl211/psl211_models.v` | `psl211_alldecks_view_indep_via_dealer`, the per-deck count, `psl211_dealer_view_indep_of_deck_unsat`, `psl211_fixed_deal_view_dep` | 025cc99 |

The joint law is $P(s,d,g) = \mathrm{secretP}(s)\,\delta_s(d)\,\nu(g)$. Two
sufficient conditions are proved. The mixed-law condition asks that every
secret of positive mass has the same law of the coalition view under
$\delta_s \times \nu$. The per-deck condition asks that every deck of positive
mass is valid and every valid deck has the same view law under $\nu$ alone, and
it implies the first. Section 2 of the paper presents only the first.

| Instance | Route inside Rocq | Coalition bound |
|---|---|---|
| PGL(2,7) deterministic | mixed-law, then `inde_RV_fdistmap` | $\lvert C\rvert \le 3$ |
| PGL(2,7) all decks | per-deck, `valid s d := uniq d` | $\lvert C\rvert \le 3$ |
| PSL(2,11) all decks | mixed-law, then `inde_RV_fdistmap` | $\lvert C\rvert \le 5$ |

Each `_via_dealer` theorem has a type convertible in both directions with the
theorem it restates. No existing proof was replaced.

### What the paper may and may not say

- It may say that privacy is a condition on the dealer law. At PSL(2,11), with
  the production shuffle group, view and a coalition of three seats, the dealer
  that lays one fixed deck description gives a reading that is not independent
  of the chirality (`psl211_fixed_deal_view_dep`). That dealer does not even
  depend on the chirality.
- It may say that the per-deck condition has no solution at PSL(2,11) under its
  own uniform dealer (`psl211_dealer_view_indep_of_deck_unsat`). At the deck
  description `psl211_perdeck_deal` one chirality has 0 cuts producing a given
  reading and the other has 1.
- It may not say that the uniform deal law is necessary, that a hidden uniform
  deal leaks, or that `uniq` is necessary for the per-deck law to be true.
- "Private at PGL(2,7), not at PSL(2,11), for a deterministic dealer" is a fair
  report of two compiled facts and not an explanation. The explanatory variable
  in the repository is `pgl27_3transitive` against `psl211_2transitive`.

### What the landing taught that the feasibility probe could not

Landing was tested on full copies of the three target files, because a
declaration meets a new context when it moves.

- `psl211_models.v` needed two more imports, `Import Num.Theory`, and a `%N` on
  two rewrite patterns, since that file opens `ring_scope` at file level. The
  file's own `seatT` and `cardT` served without change.
- Where a declaration lands decides what recompiles. Editing
  `transitivity_privacy.v` invalidates 41 files, among them `psl211_endpoints`
  at about 900 s and 17 GB. A new file invalidates nothing, and
  `design_privacy.v` invalidates 11. The landing recompiled 13 files, each
  under 30 s, and never touched `psl211_endpoints`.
- A landing copy that imports another landing copy must have those imports
  substituted, or a permanent file would import a probe file. Three lines.
- No file under `reconstruct/` contains a `Fail`, so the mutations of the
  dealer kernel stay in the probe.

## Batch 2: Kim's rows as Tableau programs

### What the paper needed

The manifest has three five-card rows and only the uniform one was a program.
The reader could not see that all three run the same committed execution and
differ in one line.

### What landed, all in `instances/kim2025/five_card_rows.v` (8dc3ba0)

```coq
Definition five_card_row_repeated_tableau : Tableau Sampled :=
  five_card_committed
    sample kim_centi_family.

Definition five_card_row_biased_tableau : Tableau Sampled :=
  five_card_committed
    sample kim_biased_family.
```

- `five_card_row_repeated_prefixE`, `five_card_row_biased_prefixE`: the algebra,
  the run parameters and the observed execution of each program are those of
  `five_card_committed`. A program that samples another instance's family is
  rejected (`five_card_row_s5_family`, a `Fail`).
- `five_card_row_repeated_modelE`, `five_card_row_biased_modelE`: the family
  each program samples is its manifest row's model, by conversion.
- `five_card_row_repeated_at_manifest_level`: the repeated program is accepted
  at the type `Tableau (apr_completion five_card_row_repeated)`, so the
  manifest's level term and the program's level index are one term. The same
  ascription for the biased program is a recorded `Fail`, and
  `five_card_row_biased_levelE` states that the manifest's level for that row
  is `AnalysisBridged`.
- `five_card_row_repeated_endpoint_lt`: for every starting position, the law of
  its image under the cut that the repeated row samples is within $2^{-40}$ of
  the uniform law on the five card positions. It names no seat, no set of seats
  and no secret.
- `kim_centi_small` and `five_card_row_biased_leak_bound`: under the law the
  biased row samples, the conditional mutual information between the inputs and
  the executed colour reading given the secret is at most
  `kim_leak_bound (1 / 100)`.

No `certify` arm was added and nothing under `manifest/` changed.

### Why both Kim programs stop at Sampled

A `Tableau Sampled` proves run correctness and that the executed coalition
reader is the static one. It asserts nothing about security.

The repeated row stops there because the manifest does. What is proved of the
seven-cut model is one starting position's endpoint marginal. The file does not
identify seats with card positions, so the bound is worded for positions.

The biased row stops there although the manifest says `AnalysisBridged`.
`AnalysisBridged` is one constructor with two admission criteria. The manifest
admits a row on any theorem about the sampled distribution and the observer
(`manifest/pgg_analysis_status.v:55-59`), and a leakage bound meets that. A
program reaches the level only through an arm of `certify`. Each arm produces a
theorem of the manifest's kind, so the Tableau's criterion is the stricter one,
and the gap at this row is the manifest's criterion met by a theorem no arm
takes. The exact arm would need independence under the biased law, which the
tree states nowhere and which is expected to be false. The spectral arm has
three of its five fields available and lacks a variation distance on the cut
group and a coalition constancy fact. `s5_rows.v` records the same situation
for `s5_row_word`.

Neither bound is vacuous. By the soundness auditor's computation from the
definitions, not by a compiled lemma, `kim_leak_bound (1 / 100)` is about
0.0091 bits against a trivial ceiling of about 1.19 bits, and $2^{-40}$ stands
against a trivial ceiling of 2.

For the paper: put the $2^{-40}$ Proposition directly after the repeated
program and cite `five_card_row_repeated_endpoint_lt`. Its statement is written
on the law the program samples, so the Proposition and the Tableau are about
the same model by a compiled fact. No paper file was edited.

## How the two batches were run

Each followed the same sequence: spec with a claim ledger, a probe that
compiles full copies of the target files, two independent audits, findings
folded back into the spec, a plan that quotes the audited copies, an
implementation by `cp`, and an as-built fidelity file that imports the
permanent modules.

| | Batch 1 | Batch 2 |
|---|---|---|
| Soundness audit | GO | GO |
| Naming audit | NO-GO, NO-GO, GO | NO-GO, NO-GO, GO |
| What stopped the naming rounds | two comment sentences in the PSL block, then one | two header sentences and one name, then one header sentence |
| Production files edited | 4 and `_CoqProject` | 1 |
| Files compiled at landing | 14, single-file | 1 |
| `psl211_endpoints` compiled | no | no |

Every naming NO-GO was about prose. None touched a statement, a proof or a
type. Three of the blocking sentences were written or suggested during a fix
pass, which is why each fix pass was audited again. Two devices made the later
rounds cheap. After every comment pass the main session checked that the file
was identical to its previous version once comments were stripped. And the
auditor's replacement text was extracted from the report file by a script that
asserted each boxed line to be 80 bytes before writing, since a relayed block
gets reflowed.

One sentence became false without being edited. The header of
`five_card_rows.v` said that every statement below is about a coalition of at
most one seat. Adding the biased leak bound made it false. An audit of a
landing has to read the text that did not change.

## Left open

1. The main checkout has 85 of 193 files out of date by modification time,
   because commit 1654fde edited two files under `protocol/`. Nothing in either
   batch was compiled against the `.vo` files that commit will produce. The
   landed blocks and every recompiled file name none of the three definitions
   it changed. The rule in force is to compile only related files.
2. `kim_centi_small` sits in `five_card_rows.v`. Its natural home is
   `five_card_kim.v`, beside `kim_centi_lt`, `kim_centi_gt` and
   `kim_centi_spec`, a file with 20 importers.
3. Not done, by decision: `Arguments` directives for the 65 `@`-spelled
   applications of the dealer block, a proof that `uniq` is necessary for the
   per-deck law to be true, and any study of whether the uniform PSL(2,11)
   dealer law is necessary.
4. Branches merged into `main` and deletable: `feat/dealer-privacy`,
   `feat/kim-tableau-sampled`, `chore/verifier-single-record`,
   `feat/pgl27-encoding-parameter`, `feat/pgl27-view-entropy`,
   `worktree-agent-aa400558bc3410a7b`.
