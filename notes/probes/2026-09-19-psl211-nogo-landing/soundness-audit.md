# Soundness audit of the PSL(2,11) spectral no-go landing probe

**Verdict: GO.** No blocking finding. Eight SHOULD items, all of them comment
or report text, none of them a false theorem. The four soundness invariants
about what may not be said (2 to 5) hold in both landing copies. The renamed
field proposition is the record's fifth field, checked in both directions and
against four mutations. The certificate theorem's numbers are exact and its
word form survives the planned change of the `conclude` obligation.

Independent adversarial audit, 2026-09-19, commit `4d0cc7e`, branch
`feat/tableau-extensions-probe`. Rocq 9.0.0. Every compile went through
`scratchpad/rocq1`. `instances/psl211/psl211_endpoints.v` was never compiled
and `make` was never invoked. Scratch files are in
`notes/probes/2026-09-19-psl211-nogo-landing/audit-soundness/`.

## Findings

| ID | Severity | File and content | Evidence | Proposed fix |
|---|---|---|---|---|
| SA1 | SHOULD | `STATUS.md`, compile table: "It is not in the project's suppressed list and it appears in the fidelity file too, so it follows the import of `variation_dist` and not anything this file writes. A landing brings it into `instances/psl211/`, where no file imports `variation_dist` today." | Both halves are false. `audit-soundness/warn_without.v` has the infotheo line `From infotheo Require Import realType_ext fdist proba.` with no `variation_dist` and emits the same warning, at that line. And `instances/psl211/psl211_profile.v` carries `From infotheo Require Import realType_ext fdist proba variation_dist.` verbatim, as does `instances/psl211/psl211_mixing.v`; `instances/psl211/psl211_rows.v` carries `From infotheo Require Import realType_ext fdist proba.` next to `fingroup`. So the warning is already emitted by three files of that directory, one of them the file whose header this probe rewrites. | Replace the passage with the text under question 6 below. Add nothing to `_CoqProject`. |
| SA2 | SHOULD | `psl211_rows.v` landing copy: "The field fails at two deck descriptions of one chirality as well, `psl211_alldecks_constancy_false_blockline`, so it asks for more than the secret-independence this row claims" | The statement of `psl211_alldecks_constancy_false_blockline` is `~ coalition_reading_constancy psl211_alldecks_params ((`U psl211_G_pos) : R.-fdist cutT)`, character for character the statement of `psl211_alldecks_constancy_false`. Nothing in it mentions a chirality, a deck description or a pair. The theorem whose statement carries the sentence is `psl211_blockline1_law_neq`. A reader who looks up the cited name finds no support for the sentence. | "The field fails at two deck descriptions of one chirality as well, `psl211_blockline1_law_neq`, and is refuted again from that pair at `psl211_alldecks_constancy_false_blockline`, so it asks for more than the secret-independence this row claims". Checked against both statements. |
| SA3 | SHOULD | `psl211_spectral_nogo.v` header: "That is against a shuffle whose single-card marginal error this instance proves to be exactly zero, which is the content of `psl211_alldecks_no_spectral_cert0`." | The content of `psl211_alldecks_no_spectral_cert0` is `sw_bound_eps (sc_b cert) = 0 -> False`. That the instance's single-card marginal error is zero is a different, separately compiled fact, `profile_eps_psl211 : sw_bound_eps (psl211_marginal_bound R) = 0%R` of `instances/psl211/psl211_profile.v`, which the file imports and never names. | "`psl211_alldecks_no_spectral_cert0` states the same at epsilon zero, which is the epsilon `profile_eps_psl211` of `instances/psl211/psl211_profile.v` gives this instance's single-card marginal bound." |
| SA4 | SHOULD | `psl211_spectral_nogo.v`, statement comment of `psl211_alldecks_no_spectral_cert`: "so what this excludes is every published number equal to `cert_eps`: at least 1/660" | Self-contradictory as written. What the theorem excludes is published numbers *below* 1/660; what it forces is that the published number, which today's obligation pins to `cert_eps cert`, is at least 1/660. A reader can take the sentence to exclude the numbers at least 1/660, the opposite. | "so every number a row over this model can publish is `cert_eps cert`, and that is at least 1/660." Checked: `cert_eps cert = sw_bound_eps (sc_b cert) + sw_bound_eps (sc_b cert)` and the theorem refutes that sum being below `(#|pgg_G psl211_M|%:R)^-1`. |
| SA5 | SHOULD | `psl211_spectral_nogo.v`, source comment on the same theorem: "a certificate at that ideal therefore exists, with an epsilon near infotheo's ceiling of 2 on the sum of absolute differences. So the spectral arm is not unavailable at this instance" | True but incomplete in a way that misleads. The certificate's own published bound is `cert_eps = eps + eps`, so near 4, while `var_dist P Q = \sum_a `\|P a - Q a`\| <= 2` for every pair of laws. `SpectralPropAt cert c` with `c` above 2 holds of any certificate. The exhibited occupancy is therefore of a row that publishes a vacuous number, and the passage does not say so. | Append: "Such a certificate's own bound `cert_eps` is twice that epsilon, so the row it gives publishes a number above 2, and `var_dist` is at most 2 at every pair of laws: the arm is open there and the row says nothing." |
| SA6 | SHOULD | `psl211_spectral_nogo.v`, statement comment of `psl211_dealt_view`: "The first numeral at which the two chiralities' reading multiplicities differ." | An uncompiled measured claim carried into a permanent file with no source. The parallel claim on `psl211_blockline1_view` was carried in SRC with its source ("a `vm_compute` diagnostic of `audit-soundness/audit_diag.v` ... and not a Rocq theorem") and that source sentence was stripped in the landing copy. The two are now treated differently. | Either drop the sentence or restore a source: "Measured and not proved: it is the first numeral at which the two chiralities' reading multiplicities differ, a `vm_compute` diagnostic recorded in `notes/probes/2026-09-19-psl211-sc-const/`." |
| SA7 | SHOULD | `opaque_vm_test.v`: "`Lemma tbl_size : count (fun n => n == 3) tbl = 1. Proof. by vm_compute. Qed.`", offered in `STATUS.md` as "the four-line measurement behind the N6 finding that `vm_compute` ignores `Local Opaque`" | The test does not isolate `vm_compute`. `audit-soundness/opaque_mut.v` closes the identical goal with `Proof. by []. Qed.` under the same `Local Opaque tbl`, exit 0: ssreflect's `done` reaches it by kernel conversion, which ignores the conversion oracle as well. The N6 finding is nevertheless **true**, by the same file's three `Eval` lines: `Eval simpl` prints `count (eq_op^~ 3) tbl`, `Eval cbv` prints the unfolded `count` with `tbl` still folded, `Eval vm_compute` prints `1`. | Replace the lemma with the two `Eval` lines (exact text under question 5) so the artifact shows what the sentence claims. |
| SA8 | SHOULD | `psl211_spectral_nogo.v` header: "`psl211_alldecks_uniq` at `instances/psl211/psl211_alldecks.v:421-429`", and the source comment "`notes/probes/2026-09-15-psl211-planb/AUDIT-SOUNDNESS-2.md`, row 18" | Both line and row references are correct today (`Lemma psl211_alldecks_uniq` is at 421 and its `Qed.` at 429), and both go stale on the first edit above them in a file this one does not control. The project's comment rule bars absolute line numbers in statement comments. | Cite the name alone: "`psl211_alldecks_uniq` of `instances/psl211/psl211_alldecks.v`". Keep the probe path, drop "row 18" or replace it with the row's heading. |
| SA9 | NOTE | `STATUS.md` compile table, "6.53 s", and the N6 table's "6.53 s", "6.47 s", "5.42 s" | The `.v.timelog` files in the directory give 6.66 s, 6.94 s and 5.10 s for the same three sentences, and 24.03 s total against the table's 23.6 s. The largest deviation from SRC's rounded 6.1 s is therefore +0.84 s, or 14 percent, not +0.43 s. SRC's directory holds no `.v.timelog` at all, so the per-sentence comparison the ledger row asks for cannot be reproduced from the artifacts either way. | Say which run each number comes from, or re-measure both directories once. |
| SA10 | NOTE | `psl211_spectral_nogo.v`, statement comment of `psl211_perdeck_fiber_true0`: "so one reading already separates the two chiralities at this deck description" | The strongest leakage-adjacent sentence in the file. It is true and correctly qualified by "at this deck description", which is not the all-decks law. A skimming reader can still read it as leakage. | Optional: "so one reading already tells the two chiralities apart at this fixed deck description, which is not the law the row is about." |
| SA11 | NOTE | `psl211_spectral_nogo.v`, statement comment of `coalition_reading_constancy`: "The run argument carries the secret, so the field is at least constancy in the secret" | The definition is generic in `A` and `E`; that the run argument carries the secret is a fact about the two run modes of this instance, not about the definition. | "Where the run argument carries the secret, as it does in both run modes of this instance, the field is at least constancy in the secret". |
| SA12 | NOTE | `psl211_spectral_nogo.v`, statement comment of `psl211_alldecks_constancy_false_word584`: "there is no `sc_Hd` pinning a certificate's ideal to this law" | `sc_Hd` pins `sw_rho_dist (sc_b cert)` to `sa_cut_dist sa`. What pins the ideal is `sc_close`, through that identification. | "there is no adapter whose cut is this law, so no `sc_Hd` through which a certificate's ideal could be held near it". |
| SA13 | NOTE | `psl211_spectral_nogo.v`, statement comment of `psl211_blockline1_row_size`: "block line one of the chirality's table has six positions" | The statement fixes the chirality to `true`; the comment says "the chirality" as though one were under discussion. | "block line one of the chirality-true table has six positions". |
| SA14 | NOTE | `STATUS.md`: "The index names every one of the 47 declarations and no other name." | The index entry for `psl211_perdeck_fiber_true0` also names `psl211_perdeck_view`, which is declared in `psl211_models.v`. Harmless inside an explanation, but the claim as written is false. | "names every one of the 47 declarations, and no name outside them except where an entry explains itself by one". |
| SA15 | NOTE | `STATUS.md`, N11: "`security/pgg_collusion_bound.v` (105 reverse-dependants, `psl211_endpoints` in closure)" | Computed from `.Makefile.rocq.d`, `security/pgg_collusion_bound.vo` has a forward closure of two nodes and `instances/psl211/psl211_endpoints.vo` is not in it. The intended relation is the reverse one. | "`psl211_endpoints` among its reverse-dependants". |

## 1. Every comment and header against the lemma it sits on

Method. I read the whole 1076-line landing copy, matched all 47 statement
comments and the 174-line header against the declarations, and checked every
external name a comment cites against the production tree. Declaration count
verified mechanically: 12 `Definition`, 35 proofs, 35 `Proof`/`Qed` pairs, plus
4 `Local Notation`. The header's index covers all 47 and nothing else but the
one external name of SA14.

Invariants 2 to 5, each checked by a grep for the propositions and then by
reading every hit:

- **Invariant 2** holds. `grep -niE "leak|learn|separat|distinguish|unavailab|cannot|impossib|no spectral|not shown"` over both landing copies returns thirteen lines, all read. The file says "The spectral arm is not shown unavailable at this instance", "what this theorem excludes is a range of epsilon and not the arm", "while a certificate at some other ideal stays open", and the rows copy says "What is excluded is a range of epsilon and not the arm." Nothing says the arm cannot be closed. SA5 is a completeness note on the same passage, not a violation.
- **Invariant 3** holds. The header says "no reading of these refutations gives leakage" and cites `psl211_alldecks_static_indep`, whose statement I read: `(#|C| <= 5)%N -> psl211_alldecksP R |= (fun u => static_coalition_obs psl211_alldecks_params C u.1 u.2) _|_ psl211_alldecks_secret R`, quantified over `R : realType`. The three-seat coalition is covered. The claim "that is the theorem the published row carries" is true of the proposition: `psl211_exact_witness` builds `ew_indep` from `psl211_alldecks_view_indep` and `psl211_alldecks_exact_viewE`, which is the proof body of `psl211_alldecks_static_indep`, and `#|C| < profile_k` converts to `#|C| <= 5`. It is not the term the row carries; the wording survives that.
- **Invariant 4** holds. "A change of secret is always also a change of the laid deck here, the chirality selecting the table the block line indexes" is in the file; "does not need the chirality to move" is the strongest phrasing anywhere and is not "unrelated".
- **Invariant 5** holds. `grep -nE "360|600|10/11"` over the three landing files returns nothing.

Facts a comment asserts, checked against the tree:

| comment claim | where it is compiled | verdict |
|---|---|---|
| SpectralCert has five fields and `sc_const` is the fifth | `manifest/pgg_tableau.v`, `MkSpectralCert` | true |
| `psl211_perdeck_deal` and `psl211_blockline1_deal` differ in the block line alone | `psl211_perdeck_deal := (ord0, 1%g, 1%g)` of `psl211_models.v` against `(@Ordinal 132 1 isT, 1%g, 1%g)` here | true |
| the run argument is a chirality, a block line of 132 and two labellings | `Notation psl211_deal := (('I_132 * {perm 'I_6} * {perm 'I_6})%type)` | true |
| 660 cuts; the reciprocal of the group order is 1/660 | `psl211_card : #\|pgg_G psl211_M\| = 660` of `psl211_closure.v`, `psl211_size_elem_table` | true, and `psl211_card` is never cited in the comments |
| PGL(2,7) proves the same field through `pgl27_word_view_const`, three-transitivity read as constancy below four seats | the lemma in `instances/pgl27/pgl27_rows.v` is literally the `sc_const` shape at `pgl27_dealt_params`; `profile_k_pgl27 : profile_k pgl27_profile = 4` | true |
| the derived profile declares six | `profile_k_psl211 : profile_k psl211_profile = 6` | true |
| this tree carries no dealt-mode and no weighted-word sample adapter | the only `MkSampleAdapter` under `instances/psl211/` is `psl211_alldecks_sample` | true |
| the instance's marginal epsilon is zero | `profile_eps_psl211` of `psl211_profile.v` | true, uncited, SA3 |
| `psl211_alldecks_uniq` is the compiled premise of the occupancy claim | `instances/psl211/psl211_alldecks.v`, lines 421 to 429 | true today, SA8 |
| PSL(2,11) is 2-transitive and not 3-transitive | `psl211_2transitive` is compiled in `psl211_group.v`; the negative half is not compiled anywhere | half compiled, and the file presents it as background rather than as a theorem, which is the honest reading |
| the variation distance of uniform-on-`{perm 'I_12}` from `U psl211_G_pos` is `2 * (1 - 660/12!)` | not compiled, flagged "argued and not compiled" | arithmetic checked by hand and correct: `660*(1/660 - 1/12!) + (12! - 660)/12!` |

## 2. The renamed field proposition

`audit-soundness/field_mut.v`, exit 0, 5.1 s, one warning (the pre-existing
notation one). It contains, with the definition copied verbatim from the
landing copy:

- `control`, the landing lemma in term form, `... : coalition_reading_constancy E (sc_ideal cert) := sc_const cert`. Compiles.
- `control_back`, the field's own type proved from the restatement. Compiles. So the two are the same proposition, not one implying the other; the quantifier order and the carrier `R.-fdist (pgg_gT (mp_M (instance_profile A)))` agree.
- `Fail Definition m1`, the coalition-size premise dropped. Fails as required.
- `Fail Definition m2`, the two run arguments' roles swapped, so the equation reads `fdistmap (obs C x') ideal = fdistmap (obs C x) ideal`. Fails as required, although the mutant is logically equivalent: `exact`-style term matching is up to conversion only.
- `Fail Definition m3`, the threshold relaxed from `<` to `<=`. Fails as required.
- `Fail Definition m4`, the restatement read at `sa_cut_dist sa` instead of `sc_ideal cert`. Fails as required.

A `Fail` that stopped failing would have aborted the file, so exit 0 is the
whole result. `Print Assumptions control` gives exactly the three `boolp`
axioms, consistent with N9.

Conclusion: N2 holds and is stronger than the ledger claims. Any change to the
record's fifth field breaks `spectral_cert_reading_constancy`.

## 3. The new corollary

`psl211_alldecks_constancy_false_blockline` is at the field's type, its
statement being `~ coalition_reading_constancy psl211_alldecks_params ((`U
psl211_G_pos) : R.-fdist cutT)`, and its proof spends
`(true, psl211_perdeck_deal)` and `(true, psl211_blockline1_deal)` through
`psl211_blockline1_law_neq`. Its comment states correctly what one chirality
and two block lines mean for the secret: "already at a pair of run arguments
carrying the same secret, the two deck descriptions differing in the block line
alone", and it is candid that "It states what `psl211_alldecks_constancy_false`
states and spends a different pair".

The consequence of that candour is SA2. The statement is byte-identical to
`psl211_alldecks_constancy_false`'s, so the corollary can be cited for the
refutation but not for the proposition "the failure does not need the secret to
move". That proposition lives only in `psl211_blockline1_law_neq`, which is
also in the file and also in the index. The fidelity file inherits the same
limitation: `fidelity_alldecks_constancy_false_blockline` restates a statement
that cannot distinguish itself from `fidelity_alldecks_constancy_false`.

## 4. The certificate theorem and the word form

Quantification. `psl211_alldecks_no_spectral_cert (R : realType) (cert :
SpectralCert (psl211_alldecks_sample R)) : sw_bound_eps (sc_b cert) +
sw_bound_eps (sc_b cert) < (#\|pgg_G psl211_M\|%:R)^-1 -> False`. So: for every
real field `R` and every certificate over the one adapter this instance has,
the sum of the marginal bound's epsilon with itself is **not** strictly below
the reciprocal of the group order. The inequality refuted is strict and the
field is the arbitrary `R : realType` of the statement, not a fixed one. Since
`psl211_card` gives 660, the conclusion is `eps + eps >= 1/660`, that is
`eps >= 1/1320`. "No certificate with epsilon below 1/1320" is exactly right,
and the strictness is on the right side: `eps = 1/1320` is not excluded.

The published number. `cert_eps cert = sw_bound_eps (sc_b cert) + sw_bound_eps
(sc_b cert)` by definition in `manifest/pgg_tableau.v`, confirmed by
`cert_epsE` in `field_mut.v` closing `by []`. So `cert_eps cert >= 1/660`.

The rows header sentence, "a row that publishes its certificate's own bound
publishes at least 1/660", is **true in all three regimes**:

- **`publish` with `no_reprice`.** `PublishedRow := PublishedRowAt no_reprice`, `PortProp no_reprice (SpectralDecay cert) = SpectralPropAt cert (odflt (cert_eps cert) None) = SpectralPropAt cert (cert_eps cert)`. Published number is `cert_eps cert`, at least 1/660.
- **Today's `conclude`.** `RepricePayload` demands `cert_eps cert = odflt (cert_eps cert) (c R)`. The published number is forced equal to `cert_eps cert`, so at least 1/660.
- **Stage A's `conclude`.** In `notes/probes/2026-09-19-tableau-extensions/pgg_tableau.v` the obligation is `cert_eps cert <= odflt (cert_eps cert) (c R)` and `port_reprice` closes by `le_trans`. The published number is then at least `cert_eps cert`, so at least 1/660, and a smaller one is unprovable.

So the sentence is not "true only for `publish`", and no correction is owed on
that axis. The file's own source comment on this point, "an obligation weakened
from that equality to `cert_eps cert <= odflt (cert_eps cert) (c R)` could only
let a row publish a number larger than `cert_eps`, never a smaller one", matches
the probe's stage A text exactly. SA4 is a wording defect in the neighbouring
sentence, not an arithmetic one.

The word form. `psl211_alldecks_constancy_false_word584` assumes `var_dist
(rho_from_words_weighted ... 584 ...) ideal <= eps` and `(2%:R^-40 + eps) +
(2%:R^-40 + eps) < (#\|pgg_G psl211_M\|%:R)^-1`, which is `2^-40 + eps <
1/1320`, that is `eps < 1/1320 - 2^-40`. The header's "reaches eps < 1/1320 -
2^-40" is exact. `2%:R^-40` is `(2%:R ^+ 40)^-1`, so `2^-40` and not `2 * (-40)`.

## 5. The `vm_compute` and `Local Opaque` finding

`audit-soundness/opaque_mut.v`, run through the lock. Results at Rocq 9.0.0,
with `Local Opaque tbl` in force:

- `Lemma tbl_count_by_done : count (fun n => n == 3) tbl = 1. Proof. by []. Qed.` compiles. Hence SA7: `opaque_vm_test.v` does not isolate `vm_compute`.
- `Eval simpl in (count (fun n => n == 3) tbl)` prints `count (eq_op^~ 3) tbl`, `tbl` folded.
- `Eval cbv in (count (fun n => n == 3) tbl)` prints the fully unfolded `count` fixpoint applied to `tbl`, still folded.
- `Eval vm_compute in (count (fun n => n == 3) tbl)` prints `1`.

So the claim in `STATUS.md` is correct and the artifact offered for it is not.
The replacement artifact, exact text:

    Definition tbl : seq nat := [:: 1; 2; 3; 4].

    Local Opaque tbl.

    (* simpl and cbv respect Local Opaque and leave tbl folded; vm_compute
       ignores it and prints 1. A lemma is no evidence here: ssreflect's done
       closes count (fun n => n == 3) tbl = 1 by kernel conversion, which
       ignores the oracle as well. *)
    Eval cbv in (count (fun n => n == 3) tbl).
    Eval vm_compute in (count (fun n => n == 3) tbl).

N6's reduction claim, checked independently. The landing file has four
`vm_compute` sentences and every one runs over plain `nat`:

| sentence | what is evaluated | carrier |
|---|---|---|
| `psl211_blockline1_row_size` | `size (psl211_alldecks_row (true, psl211_blockline1_deal))` | `psl211_alldecks_row : psl211_inputT -> seq nat`, body `nth [::] (psl211_class_tbl x.1) (val x.2.1.1)` |
| `psl211_blockline1_corow_size` | `psl211_alldecks_corow`, a `filter` over `iota 0 12` | `seq nat` |
| `psl211_blockline1_raw_countE` | `count (psl211_blockline1_test sq) (unzip1 psl211_elem_table)` | `seq (seq nat)`; `psl211_blockline1_seq` is written with `index p H` and never with `ph`, `pc`, so no `{perm 'I_6}` is reduced |
| `psl211_dealt_raw_countE` | the same count over the literal `psl211_dealt_decktbl b` | `seq nat` |

None touches `inord`, `{ffun 'I_n}`, `{set 'I_n}`, `{perm 'I_n}` or
`psl211_alldecks_seq` as an ordinal object. Confirmed.

Costs, from the `.v.timelog` in the directory, with line numbers recovered from
the character offsets: `by vm_compute` at 404 and 409 cost 0.01 s and 0.00 s,
`by split; vm_compute` at 441 costs 5.10 s, the same tactic at 926, after
`Local Opaque psl211_elem_table`, costs 0.00 s, and the two `perm_filter` steps
at 476 and 982 cost 6.66 s and 6.94 s. The 0.00 s at 926 is the bytecode cache:
`psl211_elem_table` was compiled to bytecode at 441 and the seal does not
invalidate it. Total 24.03 s over 369 sentences, no sentence over 7 s. See SA9
for the mismatch with the table in `STATUS.md`.

## 6. The `notation-incompatible-prefix` warning

What triggers it. The conflict is between mathcomp's `H <| G` at level 70,
brought in by `fingroup`, and infotheo's `_ <| _ \|> _` at level 49. Two probes:

- `audit-soundness/warn_with.v`, the import prefix of `instances/psl211/psl211_profile.v` including `variation_dist`: exit 0, warning at the infotheo line.
- `audit-soundness/warn_without.v`, the same with `variation_dist` dropped, so `From infotheo Require Import realType_ext fdist proba.`: exit 0, **the same warning at that line**.

So the trigger is the first infotheo `Require` next to `fingroup`, and
`variation_dist` has nothing to do with it.

Does production already have it. Yes, on two independent grounds. The
project's own build logs carry it: `build.log` 48 times, `build-pinned.log` 74
times, over `manifest/pgg_analysis_status.v`, `security/pgg_mixing.v`,
`instances/s5/s5_models.v` and thirty more. Those logs predate the PSL(2,11)
instance, so they name no `psl211` file, but the import shape settles it
directly: `instances/psl211/psl211_profile.v` and
`instances/psl211/psl211_mixing.v` carry `From infotheo Require Import
realType_ext fdist proba variation_dist.`, and `instances/psl211/psl211_rows.v`
itself carries `From infotheo Require Import realType_ext fdist proba.` beside
`fingroup`. All three are `warn_with.v` and `warn_without.v`.

Does `_CoqProject` suppress it. No. The production file suppresses
`-projection-no-head-constant`, `-redundant-canonical-projection`,
`-notation-overridden`, `-ambiguous-paths` and
`-notation-incompatible-format`. `-notation-incompatible-prefix` is a different
warning and is not listed.

**Recommendation: accept, change nothing.** Not `Set Warnings`, because the
landing introduces no warning that the directory does not already emit, and a
local suppression would be the only one of its kind in the tree. Not avoiding
the import, because `var_dist` is the carrier of four statements. If the user
later wants it silenced, the change belongs to `_CoqProject` for the whole
tree, as one more line beside the other five, and the exact text is

    -arg -w -arg -notation-incompatible-prefix

but I recommend against it: the warning reports a real parsing hazard and the
tree has lived with it since before this instance existed.

Exact replacement for the `STATUS.md` passage (SA1):

> One warning is emitted, on the `From infotheo Require Import ...` line:
> `notation-incompatible-prefix` on `_ <| _` against `_ <| _ |> _`. It is not
> in the project's suppressed list. It is not new. It follows the first
> infotheo `Require` beside mathcomp's `fingroup`, with or without
> `variation_dist`, and `instances/psl211/psl211_rows.v`,
> `instances/psl211/psl211_profile.v` and `instances/psl211/psl211_mixing.v`
> already emit it. Nothing is added to `_CoqProject`.

## 7. N5 and N8

**N5.** Verified mechanically and then by sample. The SRC probe declares 48
constants over its three `.v` files (22, 12, 14); the `psl211_deck_diag.v`
diagnostic declares none, only six `Eval vm_compute in`. The table in
`STATUS.md` has 48 rows, every SRC name appears in exactly one, no row names
anything that is not an SRC declaration, and every row's source-file number is
right.

Twelve sampled, statements compared after applying the rename map:

| SRC | disposition | verified |
|---|---|---|
| `sc_const_prop` | LR | statement identical after rename; only the doc comment was rewrapped |
| `psl211_samechir_law_neq` | LR | identical |
| `psl211_alldecks_raw_viewE` | L | identical |
| `var_dist_point_le` | RL | absent from the landing; infotheo's `leq_var_dist` at `probability/variation_dist.v:51` is `` `\|p x - q x\| <= d(p, q) `` with `A` a section variable and `p q x` explicit, so `var_dist_point_le _ _ _` and `leq_var_dist _ _ _` have the same arity. Correct replacement |
| `fdist_uniform_close_supp` | P | absent from the landing, as claimed |
| `psl211_alldecks_sc_const_false_close` | LR | identical |
| `psl211_dealt_static_obsE` | L | identical |
| `psl211_alldecks_no_spectral_cert` | L | identical |
| `psl211_alldecks_sc_const_set0` | LR | identical |
| `psl211_samechir_deal` | LR | identical; the neighbouring `psl211_samechir_view`'s diagnostic source comment was dropped, which is the inconsistency SA6 names |
| `psl211_samechir_raw_countE` | LR | statement compared by hand: `psl211_blockline1_raw_count (psl211_perdeck_seq true) = 1 /\ psl211_blockline1_raw_count psl211_blockline1_seq = 0`, identical to SRC after rename |
| `psl211_dealt_raw_countE` | L | identical |

**N8, my own search of the production tree.** I searched `lib protocol groups
security smc reconstruct instances manifest legacy` for the propositions, with
a nineteen-pattern case-insensitive scan covering `nobody has measured`,
`unmeasured`, `not been measured`, `never measured`, `no spectral`, `spectral`,
`no word row`, `constancy`, `sc_const`, `raw count`, `vm_compute diagnostic`,
`different statement`, `not a Rocq theorem`, `no certificate`, `no row`,
`carried by no`, `ideal cut`, `SpectralCert`, `SpectralDecay`, then read every
hit under `instances/psl211/`, `manifest/pgg_analysis_manifest.v` and
`manifest/pgg_analysis_status.v`.

**I found exactly one hit and it is the one the prover reports**,
`instances/psl211/psl211_rows.v`, "There is no spectral arm for this dealer ...
under the all-decks dealer it is a different statement nobody has measured."
Nothing was missed.

Row 9 of `manifest/pgg_analysis_manifest.v`, the twelve-card chirality
instance's all-decks dealer, read in full. Its bound-or-certificate field names
`PSL211Analysis.marginal_bound` and `PSL211Analysis.certificate_bundle`; its
model transfer is "none claimed"; its missing premise is "none: the cut this
model draws is the uniform distribution on the group already, so the path
compares no idealized model". That last field is about the exact arm's transfer
premise and stays true: nothing in this result gives the row an idealized model
to compare. The row's four capability lines name `exact_view_indep`,
`static_indep`, `observed_recovers` and `secret_expectedE`, and the level
justification. No sentence of the row claims or explains the absence of a
spectral arm, so nothing there is made stale.

The manifest's "Absent capabilities" paragraph discusses the five-card
development and the S_5 finite-word path and never reaches PSL(2,11). Clean.
`instances/psl211/psl211_analysis.v`'s header is a facade contract and an alias
check table with no claim about the arm. Clean. `psl211_profile.v:128` and
`psl211_scheme.v:13` and `psl211_secrecy.v:21` say PSL(2,11) is only
2-transitive, which this result does not touch.

One incidental hit outside the result's scope, which `STATUS.md` also reports:
`manifest/pgg_analysis_manifest.v` writes "the cut distribution has full-L1
distance one from group uniform" about the S_5 word path, spelling a distance
with the two-character term this project bars. Nothing here makes it false.

## 8. The rows header, sentence by sentence

Comment-stripped equality with production reverified independently, with a
nesting- and string-aware stripper: identical, 4986 characters each. The change
is the "Not claimed" paragraph and one reflowed line.

| sentence | named theorem | verdict |
|---|---|---|
| "A spectral row for this dealer." | — | true; no spectral row exists for this instance |
| "A certificate's constancy field asks that a coalition below the privacy threshold read the ideal cut the same way at every run argument, and `instances/psl211/psl211_spectral_nogo.v` restates that field as `coalition_reading_constancy` and refutes it in both run modes." | `sc_const`, `coalition_reading_constancy` | true, and the restatement is verified in question 2 |
| "Under the dealer-dealt parameters, where the run argument is the secret, it fails at three seats at the group-uniform ideal, `psl211_dealt_constancy_false`." | `psl211_dealt_constancy_false` | true; `ex_inputT psl211_dealt_params` is `bool`, the witness coalition is `psl211_perdeck_coalition` with `#\|C\| <= 3` |
| "it fails at the group-uniform ideal, `psl211_alldecks_constancy_false`" | that lemma | true |
| "at every ideal whose support is exactly the shuffle group, `psl211_alldecks_constancy_false_supp`" | that lemma | true; its two hypotheses are `g \notin G -> ideal g = 0` and `g \in G -> ideal g != 0`, which is support equal to `G` |
| "and at every ideal closer than 1/1320 to the group-uniform law, `psl211_alldecks_constancy_false_close`" | that lemma | true and tight: `var_dist < 1/1320` gives `eps := var_dist` with `eps + eps < 1/660` |
| "No certificate over this model therefore carries a shuffle bound epsilon strictly below 1/1320, `psl211_alldecks_no_spectral_cert`, so a row over this model that publishes its certificate's own bound publishes at least 1/660." | that theorem, `cert_eps` | true, under `publish`, under today's `conclude` and under stage A's `conclude`; see question 4 |
| "In particular no certificate carries the instance's own marginal bound, whose epsilon is zero, `psl211_alldecks_no_spectral_cert0`." | that corollary plus `profile_eps_psl211` | true, with one uncited step, the analogue of SA3 |
| "The field fails at two deck descriptions of one chirality as well, `psl211_alldecks_constancy_false_blockline`, so it asks for more than the secret-independence this row claims and its failure is not leakage." | `psl211_blockline1_law_neq` is the theorem that says this | proposition true, citation wrong: **SA2** |
| "What is excluded is a range of epsilon and not the arm." | — | true, invariant 2 |
| the remaining sentences, from "Trace secrecy is not a field of an `AnalysisPathRow`" onward | — | unchanged from production, byte for byte |

## 9. Reverse closure

From `.Makefile.rocq.d`, forward closures over `.vo` nodes:

- Nothing in the production tree `Require`s `psl211_rows`: its `.vo` has zero reverse-dependants, confirmed both by the dependency graph and by a `Require` grep over all nine source roots. The comment-only change recompiles one file.
- `instances/psl211/psl211_endpoints.vo` has exactly two direct importers, `psl211_models.vo` and `psl211_analysis.vo`.
- The new file imports `psl211_models`, whose own closure already contains `psl211_endpoints.vo` (39 nodes). So the explicit `From pgg_smc Require Import psl211_endpoints` adds nothing to the closure that `psl211_models` did not already add, and it could be dropped without changing what a landing loads.
- A landing therefore **loads** `psl211_endpoints.vo` and never recompiles it: `psl211_endpoints.v` is unchanged and is not downstream of either changed file. Invariant 6 and ledger row N11 hold.

For the record, the same computation contradicts the parenthesis in N11 quoted
under SA15: `security/pgg_collusion_bound.vo` has a forward closure of two
nodes and `psl211_endpoints.vo` is not among them.

## What I did not check

- I did not recompile `psl211_spectral_nogo.v`, `psl211_rows.v` or `psl211_nogo_fidelity.v`. The main session did that in a fresh directory and reported exit 0, and I took the assumption counts from its report and from the fidelity file's own text rather than re-running them.
- I did not verify the collision scan over 583 `.v` files, nor the naming review of N10 beyond confirming that `reconstruct/s5_nogo.v` exists as the file-name precedent.
- I did not re-derive the `vm_compute` counts. That block line zero gives one cut and block line one gives none, and that one chirality gives none and the other one, rest on the compile alone.
- I did not check the occupancy claim in Rocq. The arithmetic `2 * (1 - 660/12!)` and the claim that uniform-on-`{perm 'I_12}` reads the same at every deck description I checked on paper only; the second follows from twelve-transitivity of the full symmetric group and from every laid deck being a bijection, which is `psl211_alldecks_uniq`, but neither step is compiled.
- I did not look for a compiled statement that PSL(2,11) is not 3-transitive. There is none; the file presents it as background.
- I did not compile `instances/psl211/psl211_endpoints.v` and did not run `make`, per the brief.
- I did not read the proof scripts line by line for tactic hazards beyond the four `Local Opaque` seals and the four `vm_compute` sentences.
- I did not audit the sibling Kim landing, and I read `notes/probes/2026-09-19-tableau-extensions/pgg_tableau.v` only for the `RepricePayload`, `port_reprice` and `conclude` block.
- I did not check the paper, which is out of the spec's scope, for numbers this result makes stale.
- I did not re-measure SRC's per-sentence costs; SRC holds no `.v.timelog` and re-running it would rewrite a closed probe's `.vo` files.
