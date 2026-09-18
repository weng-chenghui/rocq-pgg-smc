# Three Tableau extensions: what the present arms cannot state

Date: 2026-09-19

Status: spec drafted. The probe starts when the batch of
[[20260919-kim-spectral-arm-probe-design]] is closed. This is a probe batch. It
edits no permanent file and ends in a verdict per extension. A landing is a
separate batch and needs the user's decision.

Follows [[20260919-kim-spectral-arm-probe-design]] and
[[2026-09-19-062455-third-certify-arm-for-the-biased-row]].

## Problem

The paper tells one story about every instance. There is an ideal model with a
uniform cut, which is private, and an actual model with a biased cut, which is
close to the ideal one and so private up to a small number. A Tableau program
is where that story becomes one term, so a reader should find every instance's
actual model there, at the level `AnalysisBridged`, with its number.

Three things the repository has proved cannot be written there today.

1. **The PSL(2,11) word model.** `psl211_word_mixing` bounds the variation
   distance between the word shuffle and the uniform law on the group by
   $2^{-40}$. No row carries it. The spectral arm cannot take it, and the reason
   is the arm's proposition and not a missing lemma. `SpectralPropAt` compares
   the readings at every two run arguments and takes no account of the law of
   the run argument. In the all-decks mode the run argument is the public deck
   description, so that is a statement per deck. The probe of 2026-09-19
   proved the certificate's constancy field false at the field type
   (`notes/probes/2026-09-19-psl211-sc-const/`), and its soundness audit
   measured that the failure is not about the secret: under the uniform cut
   the 660 cuts give 660 distinct readings at seats 0, 1 and 2, and two deck
   descriptions of the same chirality already differ, by more than two of
   opposite chirality do. By that diagnostic, which is a computation and not a
   theorem, a spectral certificate at this model would have to publish a
   number of at least $10/11$. Three seats nevertheless learn nothing about
   the chirality under the all-decks law. What PSL(2,11) has is independence
   on average over deck descriptions, under the uniform cut. The statement the
   story needs is that the word model is close to that model, and the Tableau
   has no proposition of that kind. In the dealer-dealt mode the run argument
   is the secret alone and the same field fails for a different reason, the
   group being 2-transitive and not 3-transitive. That mode has no private
   ideal model to be close to, so extension A is about the all-decks mode
   only.
2. **Kim's leakage bound.** `five_card_row_biased_leak_bound` bounds a
   conditional mutual information, and it holds at the full reveal. Both arms
   are about a coalition below the threshold, one in exact independence and one
   in variation distance. Neither can state a bound in bits above the
   threshold.
3. **A published number that is an upper bound.** The obligation of `conclude`
   is an equality, `cert_eps cert = c R`. A row whose certificate proves
   $2\sqrt5\,(1/80)^7$ cannot publish $2^{-39}$ without choosing a weaker
   epsilon inside the certificate, which hides the number actually proved.
   `SpectralPropAt` is monotone in its bound, so an inequality would be sound.

Each extension is probed for two things: whether the change to
`manifest/pgg_tableau.v` compiles with every existing row unchanged or changed
only in a payload, and whether the instance theorem it is meant for can then be
written as a program.

## The check for work on the DSL layer itself

- `Operation:` add one constructor to the sum type `SecurityPort` and one
  branch to every `match` on it, twice, and weaken one payload from an equality
  to an inequality. The invariant is that a program reaching `AnalysisBridged`
  proves exactly the proposition of its own arm, at the number it publishes.
- `Monad:` unchanged. The Tableau stays a parameterised monad indexed by the
  completion level before and after a statement. Each new piece is one more
  `certify_*` step from `Sampled` to `AnalysisBridged`. The laws of
  `tableau_bind` are not touched.
- `DSL:` yes, in all three cases the Tableau is the DSL and the gap is one of
  expressiveness: a proposition about an average over run arguments, a
  proposition in bits, and a published number that bounds the proved one.

## Flow

The running value is the number of existing row programs that still compile,
out of the six importers' worth of programs, then the new programs gained.

```
flow tableau_extensions                                         // rows kept 0, gained 0
object   T0 := a full copy of manifest/pgg_tableau.v             // probe copy, never imported by a permanent file
step C   RepricePayload, port_reprice : equality -> inequality   // by monotonicity of SpectralPropAt
check    copies of the five importers compile                    // rows kept: all, payloads of conclude changed
step A   IdealCloseCert, ApproxIndepPropAt, certify_ideal_close  // new arm, tail from two generic var_dist lemmas
check    copies of the five importers compile                    // rows kept: all, no payload changed
step B   LeakCert, LeakPropAt, certify_leak                      // new arm, tail from the view identification
check    copies of the five importers compile                    // rows kept: all
program  psl211 word row through step A                          // gained 1, number from psl211_word_mixing
program  Kim repeated row, form 1, published at 2^-39 by step C  // gained 2
program  Kim biased row through step B                           // gained 3, needs the ViewS and ViewA lemma
outside  one port per row: a row certified by one arm cannot also carry another
outside  the manifest rows, the paper, every permanent file
```

Roles. Object: the copy of the Tableau. Steps: the three edits. Terminals: the
three programs. Interfaces of the external components: `psl211_word_mixing`
enters through the closeness field of the new certificate,
`psl211_alldecks_view_indep` (or the landed `_via_dealer` form) through its
independence field, `five_card_colour_view_leak_bound` through `lc_bound`, and
`kim_centi_cert_eps_lt` through the payload of `conclude`.

## Pinned carriers

- Extension A: `sa : SampleAdapter R (instance_exec psl211_alldecks_params)`
  over an abstract `R : realType`, with sample space
  `psl211_inputT * pgg_gT psl211_M`, law the uniform law on deck descriptions
  times `rho_from_words_weighted R 10 2 584 psl211_moves psl211_Wuni`. No such
  adapter exists in the tree. The probe builds it, with its analysis family.
- Extension B: `amf_sample kim_biased_family R tt`.
- Extension C: the certificate `kim_centi_cert` of
  `notes/probes/2026-09-19-kim-spectral-arm/kim_spectral_rows_probe.v`.

## Claim ledger

| ID | Checkable claim | Passing evidence |
|---|---|---|
| C1 | Weakening the obligation of `conclude` to `cert_eps cert <= c R` keeps `port_reprice` provable. | The lemma ends in `Qed` in the Tableau copy, by transitivity through `SpectralPropAt`. |
| C2 | Every existing program still compiles after C1. | Copies of `pgg_tableau_syntax.v`, `s5_rows.v`, `pgl27_rows.v`, `psl211_rows.v` and `five_card_rows.v` compile against the copy. The probe lists every payload that had to change, with the old and the new text. `pgl27_row_word39` is the known case. |
| C3 | The weakened obligation still rejects a wrong number. | A reprice of a spectral row to a number below its `cert_eps` is a recorded `Fail` or an unprovable obligation shown by a compiled negation. The existing recorded `Fail` `pgl27_row_word39_bare` still fails. |
| C4 | Kim's repeated row publishes $2^{-39}$ from the bundle's own number. | A program ending in `conclude` at $2^{-39}$ with payload from `kim_centi_cert_eps_lt` elaborates, with the certificate's epsilon left at the spectral number. |
| A1 | A generic lemma: if two laws on a sample space are within `eps`, the joint law of any two readers under one is within `eps` of their joint law under the other. | `Qed`, from `var_dist_fdistmap`. |
| A2 | A generic lemma: if two readers are independent under the ideal law and the actual law is within `eps` of it, the actual joint law of the readers is within a stated multiple of `eps` of the product of its own marginals. | `Qed`, with the constant found by the probe and reported. The constant is 2 or 3 depending on whether the secret's marginal is the same under both laws, and the probe states which and why. |
| A3 | The new certificate and its proposition. | A record with an ideal law on the adapter's sample space, a secret reader, a closeness field and an independence field below the threshold, and a proposition that speaks of the actual model only. The tail lemma from `Sampled` ends in `Qed`. |
| A4 | The arm's proposition is not vacuous and not trivially true. | At the PSL(2,11) word model the published number is compared with `var_dist_le2`. A mutation with the independence field dropped must fail to give the tail. |
| A5 | Every existing program still compiles after A3, with no payload changed. | As C2. |
| A6 | The PSL(2,11) word model as a sample adapter and an analysis family. | Definitions compile. The cut law of the adapter is the word law by a lemma. The joint law is within $2^{-40}$ of the all-decks law, from `psl211_word_mixing` and a product lemma, or directly from `psl211_joint_mixing` if its carrier fits. |
| A7 | The PSL(2,11) word row is a program. | `certify` with the new arm, then `publish IdealFinite BaselineClassicalOnly`, elaborates. The independence field is the landed all-decks theorem. |
| A8 | The new arm does not make the spectral arm redundant, and the two are not confused. | A short compiled comparison: `SpectralPropAt` fixes two run arguments and ignores the law of the run argument, the new proposition averages over it. The probe states in one sentence each which instances fit which arm, and whether PGL(2,7)'s word row fits both. |
| B1 | The leakage certificate, its proposition and `certify_leak`. | As section 1 of the note on a third arm, compiled in the Tableau copy. `lc_bound` has no threshold premise. |
| B2 | The lemma the note names as missing. | The reading indexed by a set of seats and the reading indexed by a list agree at the list that enumerates the set, and conditional mutual information does not grow through `five_card_colour_fill C`. Both end in `Qed`, or the smallest counter-probe isolates what fails. |
| B3 | Kim's biased row through the leakage arm is a program. | It elaborates. |
| B4 | One port per row. | The probe reports, from the types, whether a row certified by one arm can also carry a second certificate, and what a second `certify` step at `AnalysisBridged` would have to change. It does not build it. |
| B5 | Every existing program still compiles after B1. | As C2. |
| B6 | The keyword measurement of `pgg_tableau_syntax.v` repeated for every new arm name. | `Check` of each new constructor name still passes after the notation is declared. |
| D1 | Names and homes. | Each new declaration has a proposed name and file. The reverse-dependency closure of `manifest/pgg_tableau.v` is recomputed from `.Makefile.rocq.d`, and `psl211_endpoints` is confirmed absent from it. Generic lemmas go to a new file under `lib/`. |
| D2 | What each landing would make false. | For each extension, the header sentences and recorded `Fail`s in the six files that a landing falsifies, by file and line. The known ones are the header of `five_card_rows.v` on two admission criteria and the header of `psl211_rows.v` on the absent spectral arm. |
| D3 | What the manifest pins. | `manifest/pgg_analysis_manifest.v` pins each row's level and statuses with `Check (erefl : ...)` and names each row's theorems through the instance's analysis facade, which sits below the manifest. For each new program the probe lists the pins and header tables a landing changes, and says where the instance theorem has to live to be named by the facade. The previous batch missed both points twice (`notes/probes/2026-09-19-kim-spectral-arm/soundness-audit-round2.md`, G1 and G4). The manifest has seven reverse-dependants, `pgg_tableau.v` and `pgg_tableau_syntax.v` among them. |

## Cited objects

| Object | File | Required statement shape |
|---|---|---|
| `SecurityPort`, `PortProp`, `RepricePayload`, `port_reprice`, `conclude`, `certify_exact`, `certify_spectral`, `exact_tail`, `spectral_tail` | `manifest/pgg_tableau.v:149`, `:363`, `:610`, `:622`, `:638`, `:577`, `:592`, `:535`, `:561` | The sum type, its three matches, and the two existing tails the new ones are modelled on. |
| `ExactWitness`, `ExactProp`, `SpectralPropAt`, `cert_eps` | `manifest/pgg_tableau.v:114`, `:304`, `:331`, `:345` | The shapes the new propositions sit beside. |
| `psl211_word_mixing`, `psl211_joint_mixing` | `instances/psl211/psl211_mixing.v:545`, `:595` | Variation distance at most $2^{-40}$, on the group and on the product with a secret prior. |
| `psl211_alldecks_sample`, `psl211_alldecksP`, `psl211_alldecks_secret`, `psl211_exact_family` | `instances/psl211/psl211_models.v:222`, `:200`, `:207`, `:516` | The ideal model of extension A. |
| `psl211_exact_witness` | `instances/psl211/psl211_rows.v:151` | The independence the ideal model has, below the threshold 6. |
| `five_card_colour_view_leak_bound`, `five_card_row_biased_leak_bound`, `five_card_static_obsE`, `five_card_colour_viewE` | `instances/kim2025/`, `five_card_rows.v` | The bound in bits and the two view identifications of extension B. |
| `view_mutual_info_le` | `reconstruct/transitivity_privacy.v` | Data processing for mutual information, to be tested for B2. |
| `var_dist_fdistmap`, `var_dist_fdistmap_transfer` | `security/pgg_collusion_bound.v:126` | Data processing for variation distance. |
| `var_dist_le2`, `kim_centi_cert`, `kim_centi_cert_eps_lt` | `notes/probes/2026-09-19-kim-spectral-arm/` | Probe results of the previous batch, copied and not imported across probes unless the probe directory depends on it openly. |

## Soundness invariants

1. No new axiom, assumed constant, `Admitted` or `Abort`, apart from the one
   decomposition probe the method allows, which stays in the probe.
2. Every distance is a variation distance between exact laws and every leakage
   a Shannon quantity of an exact law. No computational assumption appears.
3. The proposition of extension A speaks of the actual model. It is approximate
   independence on average over run arguments. It is not a statement at a fixed
   deck, and no comment presents it as one. The refutations at a fixed deck
   stay true and are cited beside it.
4. Extension A does not weaken the spectral arm and does not replace it. Both
   stay, and the difference is stated.
5. Extension B has no threshold premise, so it says something at the full
   reveal and nothing stronger than its number below the threshold. A row that
   carries only a leakage bound is not presented as a coalition privacy result.
6. Extension C never lets a row publish a number below the one it proved.
7. A published number is compared with its trivial ceiling: 2 for a variation
   distance, the entropy of the secret for a leakage.
8. No permanent file is edited. Probe files are kept and never imported by a
   permanent file. `psl211_endpoints` is never compiled.

## Probe artifacts

Directory `notes/probes/2026-09-20-tableau-extensions/`, logical path
`tableau_ext_probe`. Full copies of `manifest/pgg_tableau.v`,
`manifest/pgg_tableau_syntax.v` and the four rows files, with their imports of
one another pointed at the copies. One file of generic lemmas. One file per new
program. `_CoqProject`, `STATUS.md`, and the two audit reports. The three
extensions are applied to the copy in the order C, A, B, and the copy is saved
under `history/` after each, so that each extension's cost is read from its own
diff.

## Acceptance condition

Every ledger row ends in GO or in NO-GO with an isolating counter-probe. An
independent soundness audit and an independent naming audit end in a verdict.
The batch then reports, per extension, the size of the change to the Tableau,
the programs gained, and what a landing would make false. It edits no
permanent file.

## Out of scope

Any edit under `manifest/` or `instances/`. The paper. A bound on mutual
information derived from a variation distance. A second `certify` step on one
row. The `s5_row_word` program, beyond one sentence in A8 on whether its model
has the shape extension A asks for.
