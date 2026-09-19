# Audit 3 of the Kim spectral landing probe

**VERDICT: NO-GO**, on one blocking finding (B1). Everything else is SHOULD or
NOTE. B1 is a four-line comment repair in `pgg_analysis_manifest.v`; nothing in
the mathematics, the names, the numbers or the procedure is wrong.

Third round, independent. Directory
`notes/probes/2026-09-19-kim-spectral-landing/` at commit `8d83952`, after fix
pass 2. Spec `notes/20260919-kim-spectral-landing-design.md`. I wrote none of
the copies and none of the earlier audits.

Method: diffed every copy against `history/*.2026-09-19-before-fix2*` and
against its production file; opened every statement named by a changed
sentence; ran `tools/import_rewrite_table.py` and `tools/regen_diffs.py`; ran
two timed compiles (`five_card_rows.v` and one scratch file under
`audit-3/`). Scratch: `audit-3/a3_erefl.v`, `audit-3/diff-fix2-*.txt`.

## Findings

| ID | Sev | Quoted content | Evidence | Exact replacement |
|---|---|---|---|---|
| **B1** | **BLOCKING** | `pgg_analysis_manifest.v`, Row 4, immediately under the capability table: `(* Hypotheses of that capability: eps_lt_inv5, eps_gt_neg4inv5 and the        *)` / `(* small-bias hypothesis eps_small : 0 < 5^-1 - `\|`eps`\|`. All three are         *)` / `(* explicit arguments of the aliased theorem; none is discharged silently.    *)` | Production Row 4's capability table held **one** line, `colour_view_leak_bound`, and "that capability" pointed at it. Fix pass 2 inserted a second line, `biased_static_obs_indist`, directly above this sentence. `kim_biased_static_obs_indist` (`five_card_mixing.v`) reads `(C : {set 'I_(pi_T' ...).+1}) : (#|C| < profile_k (instance_profile five_card_algebra))%N -> forall x x', var_dist ... <= ...`: it takes **no** `eps` argument at all (the bias is fixed at one hundredth inside, through `kim_centi_lt R` and `kim_centi_gt R`), so none of `eps_lt_inv5`, `eps_gt_neg4inv5`, `eps_small` is a hypothesis of it, and "the aliased theorem" is no longer singular. `Hypotheses of` occurs exactly once in the manifest (`manifest/pgg_analysis_manifest.v:318`), so this is a Row-4-only construct the landing broke. | See §B1 below. |
| S1 | SHOULD | Four paragraphs fix pass 2 rewrote without reflowing. `five_card_mixing.v`: `    be a bound` (14 bytes, mid-paragraph). `five_card_rows.v`, `kim_centi_cert40`: `    the reading` (15 bytes). `five_card_rows.v` header: `(* level and which a leakage bound meets. A program reaches it                *)`. `pgg_analysis_manifest.v` Row 5: `(* endpoint_bound and deal_centi_lt stay in the row                           *)` | Same defect class as round 2's A4, A8 and G9, which the pass closed elsewhere. STATUS's claim is narrower and true ("Every comment box line the pass wrote closes at the box width"): the box closes, the paragraph does not fill. Measured: no line of any copy exceeds 80 bytes outside lines byte-identical to production, and every inner comment-box line is exactly 80. | §S1 below, four blocks, each line measured. |
| S2 | SHOULD | `five_card_rows.v:795-798`: `Lemma five_card_row_biased_forms_publishedE : published_row five_card_row_biased_spectral_tableau = published_row five_card_row_biased_inv25.` / `Proof. by []. Qed.` | This is the 2026-09-19 hang shape: a row without `conclude` against a row with it. Measured here with `-time`: `by []` **3.21 s**, `exact: erefl` **0.452 s**, both rc 0 (`audit-3/a3_erefl.v`). It is the single most expensive sentence in the file (next is an import at 1.54 s) and the only landing sentence over one second. | `Proof. exact: erefl. Qed.` |
| S3 | SHOULD | `five_card_analysis.v:149` `(* endpoint cards, and bool for the evaluated secret.                         *)`; `:188` `(** static_obs — what a coalition reads of the endpoint cards at one run`; `:190` `coalition's own seats read their own card`; the same phrase in both manifest observers cells | The carrier is `'I_5`, a card **position**. The same section header two lines up writes `the card position 'I_5 for the participant and input-party content readers` and `a list of card positions for the verifier endpoints`; `five_card_rows.v` writes `a coalition's colours read back as card positions`. "endpoint cards" and "their own card" are a third word for a concept the tree already names twice. `static_coalition_obs`'s own comment (`protocol/pgg_instance.v`) says "the coalition's seats read their own observation". | §S3 below. |
| S4 | SHOULD | `pgg_analysis_manifest.v` Row 4: `(* | biased_static_obs_indist | the cut distribution of                       *)` / `(*   single_biased_sample, by biased_sample_cut_witnessE | static_obs         *)`, and the level justification `(* committed pairs. Its distribution is this row's cut law, by                *)` | `FiveCardAnalysis.single_biased_sample = @kim_single_sample` is indexed by `eps`; `kim_biased_sample_cut_witnessE` identifies `sw_rho_dist kim_biased_marginal_bound` with `sa_cut_dist (@kim_single_sample R (1 / 100) (kim_centi_lt R) (kim_centi_gt R))` only. Row 5's title names its bias ("at bias one hundredth"); Row 4's does not, and now carries a theorem that holds at one bias only. | §S4 below. |
| S5 | SHOULD | `five_card_rows.v` index lists `kim_centi_cert_epsE, kim_biased_cert_epsE`, `five_card_pow2_39_split, five_card_inv50_split`, `five_card_reprice_inv25_lt2`, `five_card_row_repeated_spectral_rowE` | Six landing declarations of exactly those kinds are absent: `kim_biased_epsE`, `kim_biased_exact_le_eps`, `kim_centi_cert40_epsE`, `five_card_row_repeated_spectral_publishedE`, `five_card_row_biased_spectral_publishedE`, `five_card_row_biased_forms_publishedE`. Round 2's A19 asked for the retention decision **or** the index; STATUS gives the decision and leaves the index. | §S5 below. |
| S6 | SHOULD | STATUS, "Fix pass 1", the identification-equation bullet: "It is stated at the adapter `kim_single_sample` at bias one hundredth, which is the shape `kim_centi_cut_distE` has, and not at `amf_sample kim_biased_family`, **which is the shape `kim_centi_cut_distE` has**, so the file states both identification equations in one form." | The clause is repeated for the two opposed alternatives, so the sentence contradicts itself. Fix pass 2 wrote it while replacing a reason its own item 7 had just shown false. `kim_centi_cut_distE : sa_cut_dist kim_centi_repeated_sample = sw_rho_dist (scb_bound ...)` is stated at the concrete adapter; `sc_Hd` is what needs the `amf_sample` form. | §S6 below. |
| S7 | SHOULD | STATUS, L2 verdict row: "`five_card_mixing.v` compiles in 4.3 s, **requires neither the manifest, nor `pgg_analysis_status`**, nor the Tableau files, nor the facade." | STATUS's own item 7 says the opposite and is right: `instances/kim2025/five_card_models.v:99` reads `From pgg_smc Require Import pgg_analysis_status.` and `five_card_mixing.v:82` imports `five_card_models`, so `pgg_analysis_status` **is** loaded there. Verified by reading both import blocks. | §S7 below. |
| S8 | SHOULD | STATUS, "Fix pass 2", fidelity bullet, bolded: "so **both directions are derived from the published rows and nothing was left underived**." | Only one direction per row is. `landing_centi_prop_of_indist` closes `exact (@kim_centi_static_obs_indist R C HC x x')` and `landing_biased_prop_of_indist` closes `exact (@kim_biased_static_obs_indist R C HC x x')`: those come from the corollary, not from a published row. The fidelity file's own header says so: "one derives the certificate's own SpectralPropAt **from the corollary**". | §S8 below. |
| S9 | SHOULD | STATUS verdict table: L2 "4.3 s", L3 "4.0 s", L4 "6.6 s", L6 "7.2 s" | The compile table below them carries the post-fix-2 run: 4.6, 4.5, 6.5, 7.7 s. L2/L3/L6 are the pre-fix-2 figures (`history/STATUS.2026-09-19-before-fix2.md`); L4's 6.6 matches neither run. | Copy the four figures from the compile table: L2 4.6 s, L3 4.5 s, L4 6.5 s, L6 7.7 s. |
| S10 | SHOULD | STATUS, "Outside the `.v` files": names only `notes/20260919-kim-tableau-sampled-design.md` and `docs/superpowers/plans/2026-09-19-kim-tableau-sampled.md` | `notes/20260919-dealer-law-and-kim-rows-summary.md:118` records the deleted declaration as built: "`five_card_row_repeated_at_manifest_level`: the repeated program is accepted at the type `Tableau (apr_completion five_card_row_repeated)`". That sentence becomes false on landing and the list does not carry it. (Two probe files also `Print Assumptions` it, `notes/probes/2026-09-19-kim-tableau-sampled/kim_fidelity.v:17` and `kim_production_fidelity.v:51`; they are probe records, outside the 195-file production search, and are named here for completeness.) | Add to the list: `notes/20260919-dealer-law-and-kim-rows-summary.md:118-123`, the first sentence of the `five_card_row_repeated_at_manifest_level` bullet; the rest of the bullet, about the biased program's recorded `Fail`, stays true. |
| S11 | SHOULD | STATUS, import block for `five_card_rows.v`: "Against production that is four additions, `Lia`, `zify`, `lra` on the reals line and `five_card_mixing`, besides **the three repointed lines**." | The script's output for that file is three production-only sentences and six copy-only ones: `reals boolp` is modified (not repointed), two lines are repointed, and `five_card_mixing` is new. `five_card_mixing` is counted once among the four additions and again among the three repointed. | "besides the two repointed lines" |
| N1 | NOTE | `five_card_rows.v`: `Fact five_card_pow2_39_split (R : realType) : (2%:R : R)^-40 + 2%:R^-40 = 2%:R^-39.` with `Proof. by rewrite [RHS]splitr exprSr invfM. Qed.` and a source comment about `mulr_natl`/`mulr_natr` | `instances/pgl27/pgl27_word_privacy.v:180` already states `Fact pow2_split : (2%:R : R)^-40 + 2%:R^-40 = 2%:R^-39.` with the same proof and the same source comment. Duplicating it is the right call (importing `pgl27_word_privacy` into `instances/kim2025` would make the Kim instance depend on the PGL(2,7) instance), but nothing records that the tree now holds the identity twice. | Add one clause to the `Fact`'s source comment: `(* The same identity as pgl27_word_privacy's pow2_split, restated here so the *)` / `(* five-card instance does not import the PGL(2,7) one.                       *)` (both 80 bytes). |
| N2 | NOTE | `five_card_rows.v:177` `Require Import Lia.` | Emits `deprecated-missing-stdlib` ("Loading Stdlib without prefix is deprecated"), which the production `_CoqProject` warning flags do not silence. `instances/kim2025/five_card_kim.v:74` already spells it this way, so the copy follows precedent. Cost: measured `-time`, `zify` 1.543 s and the `reals boolp lra` line 0.769 s against production's `reals boolp`, so the arithmetic imports add about 1.6 s to every build of `five_card_rows.v`. | none |
| N3 | NOTE | `five_card_mixing.v`, `five_card_analysis.v`: "the number bounds every advantage it has in telling the two pairs apart" | True and loose by two. `var_dist` here is the sum of the absolute differences, and `var_dist_supp.v`'s own docstring says "the total variation distance of the literature is half of this quantity", so the distinguishing advantage is at most **half** the published number. | Optional: "half the number bounds every advantage it has in telling the two pairs apart". |
| N4 | NOTE | Both observers cells: `one shuffle, with no execution` | Rows 2, 7 and 9 mark an observer "executed" and say nothing about the others, so the explicit negative is a new qualifier. Informative, not false. | none |
| N5 | NOTE | Both capability lines: "derived from var_dist_fdistmap_transfer and centi_cut_mixing" / "and biased_cut_mixing" | The transfer's second premise, `static_obs_const`, is not named. Defensible: it is exact and spends nothing, which both files say, and the row's **bound or certificate** and **model transfer** cells name it. Row 2's line has the same shape. | none |
| N6 | NOTE | `manifest/pgg_tableau_syntax.v` keeps the surface keyword `tied`, and `instances/pgl27/pgl27_rows.v:300` writes `tied by esym (pgl27_word_cut_distE idx)`, while the landing writes "identification equation" in five files | The word the landing chose is `manifest/pgg_tableau.v`'s own ("the identification of the bound's law with the adapter's cut"), which is the better authority; the keyword is fixed production syntax and no landing file uses it. Recorded because a reader meets both. | none |
| N7 | NOTE | STATUS: "Six copies differ from production in `Require` sentences only, and in every one of them the difference is the logical path." | For `pgg_tableau.v` the copy also **splits** one production sentence in two (`From pgg_smc Require Import pgg_instance pgg_analysis_manifest.` becomes two lines), as the script's output shows. STATUS names the split for `psl211_rows.v` and not for `pgg_tableau.v`. The instruction that follows, restore production's block byte for byte, is right for both. | Optional: "in five of them the difference is the logical path, and `pgg_tableau.v` and `psl211_rows.v` also split one production sentence in two." |

## §B1

Current (`pgg_analysis_manifest.v`, Row 4, under the capability table):

```
(* Hypotheses of that capability: eps_lt_inv5, eps_gt_neg4inv5 and the        *)
(* small-bias hypothesis eps_small : 0 < 5^-1 - `|eps|. All three are         *)
(* explicit arguments of the aliased theorem; none is discharged silently.    *)
```

Replacement, every line measured at 80 bytes:

```
(* Hypotheses of colour_view_leak_bound: eps_lt_inv5, eps_gt_neg4inv5 and     *)
(* the small-bias hypothesis eps_small : 0 < 5^-1 - `|eps|. All three are     *)
(* explicit arguments of the aliased theorem; none is discharged silently.    *)
(* biased_static_obs_indist has one hypothesis, that the coalition holds at   *)
(* most one of the five seats, and it is an explicit argument too.            *)
```

Checked against `kim_biased_static_obs_indist`, whose binders are `(R : realType)`,
`(C : {set 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1})` and
`(#|C| < profile_k (instance_profile five_card_algebra))%N ->`, and against
`five_card_static_obs_const`'s docstring, "the privacy threshold is two, so a
coalition below it is empty or holds one seat".

## §S1

**(a) `five_card_mixing.v`, `kim_biased_sample_cut_witnessE`.** Current:

```
(** kim_biased_sample_cut_witnessE — the cut law the one-cut adapter draws
    from is the law the length-one bundle bounds. It is the identification
    field of the spectral certificate: without it the bundle's number would
    be a bound
    on some other shuffle than the one the row executes, and the seven-cut
    row's counterpart kim_centi_cut_distE would have no analogue here. *)
```

Replacement (longest line 76 bytes):

```
(** kim_biased_sample_cut_witnessE — the cut law the one-cut adapter draws
    from is the law the length-one bundle bounds. It is the identification
    field of the spectral certificate: without it the bundle's number would
    be a bound on some other shuffle than the one the row executes, and the
    seven-cut row's counterpart kim_centi_cut_distE would have no analogue
    here. *)
```

**(b) `five_card_rows.v`, `kim_centi_cert40`.** Current:

```
(** The repeated row's certificate with the constant in the marginal-bound
    field. The ideal cut, the identification equation and the constancy of
    the reading
    at every coalition of at most one seat are the same terms as in
    kim_centi_cert; the marginal bound carries two to the minus fortieth in
    place of the spectral expression, and the mixing field is the same
    distance bounded by that constant. *)
```

Replacement (longest line 76 bytes):

```
(** The repeated row's certificate with the constant in the marginal-bound
    field. The ideal cut, the identification equation and the constancy of
    the reading at every coalition of at most one seat are the same terms as
    in kim_centi_cert; the marginal bound carries two to the minus fortieth
    in place of the spectral expression, and the mixing field is the same
    distance bounded by that constant. *)
```

**(c) `five_card_rows.v` header.** Current:

```
(* level and which a leakage bound meets. A program reaches it                *)
(* only through one of the two arms of certify. Both criteria are met at      *)
(* both Kim rows. instances/s5/s5_rows.v records for s5_row_word the gap      *)
(* this file no longer has: there the constancy a spectral certificate asks   *)
(* for is false.                                                              *)
```

Replacement, five lines to four, every line 80 bytes:

```
(* level and which a leakage bound meets. A program reaches it only through   *)
(* one of the two arms of certify. Both criteria are met at both Kim rows.    *)
(* instances/s5/s5_rows.v records for s5_row_word the gap this file no longer *)
(* has: there the constancy a spectral certificate asks for is false.         *)
```

**(d) `pgg_analysis_manifest.v`, Row 5 level justification, tail.** Current:

```
(* which the row declares, and that is what gives AnalysisBridged.            *)
(* endpoint_bound and deal_centi_lt stay in the row                           *)
(* for what they are: they bound the distance from uniform of ONE seat's      *)
(* endpoint distribution, neither quantifies over a coalition and neither     *)
(* mentions a second secret. A ShuffleCertificateBundle exists for both       *)
(* models, and centi_cut_mixing is proved from the marginal bound that        *)
(* bundle carries.                                                            *)
```

Replacement, seven lines to six, every line 80 bytes:

```
(* which the row declares, and that is what gives AnalysisBridged.            *)
(* endpoint_bound and deal_centi_lt stay in the row for what they are: they   *)
(* bound the distance from uniform of ONE seat's endpoint distribution,       *)
(* neither quantifies over a coalition and neither mentions a second secret.  *)
(* A ShuffleCertificateBundle exists for both models, and centi_cut_mixing is *)
(* proved from the marginal bound that bundle carries.                        *)
```

## §S3

`five_card_analysis.v` section 3 header, current last two lines:

```
(* sequence, {ffun 'I_5 -> 'I_5} for a coalition's static reading of the      *)
(* endpoint cards, and bool for the evaluated secret.                         *)
```

Replacement (both 80 bytes):

```
(* sequence, {ffun 'I_5 -> 'I_5} for a coalition's static reading of the      *)
(* endpoint card positions, and bool for the evaluated secret.                *)
```

`static_obs`'s docstring, current:

```
(** static_obs — what a coalition reads of the endpoint cards at one run
    argument and one shuffle, before any execution is observed: the
    coalition's own seats read their own card and every other seat reads
    ord0, carrier {ffun 'I_5 -> 'I_5}. It is the reader the two cut-carrier
    transfers of section 7 compare at two committed pairs, and the reader
    Kim's two certified rows state their bound at. *)
```

Replacement (longest line 75 bytes):

```
(** static_obs — what a coalition reads of the endpoint card positions at
    one run argument and one shuffle, before any execution is observed: the
    coalition's own seats read the card position at their own start and
    every other seat reads ord0, carrier {ffun 'I_5 -> 'I_5}. It is the
    reader the two cut-carrier transfers of section 7 compare at two
    committed pairs, and the reader Kim's two certified rows state their
    bound at. *)
```

Checked against
`static_coalition_obs C x g = [ffun i => if i \in C then ex_content_obs E x (g, tnth (pi_starts (mp_PI (instance_profile A))) i) else ord0]`:
the value at a seat in `C` is the content observed at **that seat's start
position**, carrier `'I_(pgg_N' ...).+1`, and `five_card_exec_seat_countE`
gives `(pi_T' (mp_PI mpF)).+1 = 5`, so `{ffun 'I_5 -> 'I_5}` is right.

Both manifest observers cells, current third and fourth lines:

```
(*                            the endpoint cards at one committed pair and    *)
(*                            one shuffle, with no execution |                *)
```

Replacement (Row 4, both 80 bytes):

```
(*                            the endpoint card positions at one committed    *)
(*                            pair and one shuffle, with no execution |       *)
```

Row 5 ends its entry with a semicolon rather than a bar:

```
(*                            the endpoint card positions at one committed    *)
(*                            pair and one shuffle, with no execution;        *)
```

## §S4

Row 4's capability line, current first two lines:

```
(* | biased_static_obs_indist | the cut distribution of                       *)
(*   single_biased_sample, by biased_sample_cut_witnessE | static_obs         *)
```

Replacement (both 80 bytes):

```
(* | biased_static_obs_indist | the cut distribution of single_biased_sample  *)
(*   at bias one hundredth, by biased_sample_cut_witnessE | static_obs        *)
```

Row 4's level justification, current:

```
(* committed pairs. Its distribution is this row's cut law, by                *)
(* biased_sample_cut_witnessE, and its observer is static_obs, the second     *)
(* observer this row declares, so it reaches AnalysisBridged beside           *)
(* colour_view_leak_bound, which reaches it at the executed reader            *)
(* colour_view.                                                              *)
```

Replacement (every line 80 bytes):

```
(* committed pairs. Its distribution is this row's cut law at bias one        *)
(* hundredth, by biased_sample_cut_witnessE, and its observer is static_obs,  *)
(* the second observer this row declares, so it reaches AnalysisBridged       *)
(* beside colour_view_leak_bound, which reaches it at the executed reader     *)
(* colour_view.                                                               *)
```

(The last line also gains the byte it was missing; the current one is 79.)

## §S5

Add to `five_card_rows.v`'s **Key results** list, in the file's own two-column
form, each line 80 bytes:

```
(*   kim_biased_epsE          == the one-cut bundle's marginal bound in       *)
(*                              closed form                                   *)
(*   kim_biased_exact_le_eps  == the exact one-cut distance is under that     *)
(*                              bound                                         *)
(*   kim_centi_cert40_epsE    == the repriced repeated certificate's number   *)
(*   five_card_row_repeated_spectral_publishedE                               *)
(*   five_card_row_biased_spectral_publishedE                                 *)
(*                           == the three coordinates each certified program  *)
(*                              publishes                                     *)
(*   five_card_row_biased_forms_publishedE                                    *)
(*                           == the two one-cut programs publish one row      *)
```

## §S6

STATUS, "Fix pass 1", the identification-equation bullet. Current:

> It is stated at the adapter `kim_single_sample` at bias one hundredth, which
> is the shape `kim_centi_cut_distE` has, and not at `amf_sample
> kim_biased_family`, which is the shape `kim_centi_cut_distE` has, so the file
> states both identification equations in one form.

Replacement:

> It is stated at the adapter `kim_single_sample` at bias one hundredth, which
> is the shape `kim_centi_cut_distE` has, and not at `amf_sample
> kim_biased_family`, which is the shape `sc_Hd` asks for, so the file states
> both identification equations at a concrete adapter.

"in one form" is also weaker than it sounds: the two equations run in **opposite
directions**. `kim_centi_cut_distE : sa_cut_dist kim_centi_repeated_sample =
sw_rho_dist (scb_bound (kim_security_bundle_centi R))`, while
`kim_biased_sample_cut_witnessE : sw_rho_dist kim_biased_marginal_bound =
sa_cut_dist (@kim_single_sample R (1 / 100) ...)`. That is why `kim_centi_cert`
supplies `(esym (kim_centi_cut_distE R))` to `sc_Hd` and `kim_biased_cert`
supplies `(kim_biased_sample_cut_witnessE R)` bare. "at a concrete adapter" is
the property that actually holds of both.

## §S7

STATUS L2 verdict row. Replace

> requires neither the manifest, nor `pgg_analysis_status`, nor the Tableau
> files, nor the facade

with

> requires neither the manifest, nor the Tableau files, nor the facade, and
> names nothing of `pgg_analysis_status`, which `five_card_models.v` already
> loads below it

## §S8

STATUS, "Fix pass 2", fidelity bullet, last sentence. Replace

> Both program-side lemmas compiled at the first attempt; the fallback through
> `spectral_tail` was not needed, so **both directions are derived from the
> published rows and nothing was left underived**.

with

> Both program-side lemmas compiled at the first attempt; the fallback through
> `spectral_tail` was not needed, so **each row's corollary statement is
> derived from its own published row, the converse from the corollary, and
> nothing was left underived**.

## Question 1. Rows 4 and 5 as they now stand

Opened every statement a cell names. Everything below is true except B1 and the
imprecision of S4.

**Observers cells.** Row 4 lists `colour_view : (size A).-tuple bool` then
`static_obs : {ffun 'I_5 -> 'I_5}`; Row 5 lists the seat distribution, then
`static_obs`, then `verifier_endpoints : seq 'I_5`. The carrier is right:
`static_coalition_obs`'s codomain is
`{ffun 'I_(pi_T' ...).+1 -> 'I_(pgg_N' ...).+1}`, and
`five_card_exec.five_card_exec_seat_countE : (pi_T' (mp_PI mpF)).+1 = 5`. The
manifest's own spelled-type pin writes the unreduced form, so the cell's `'I_5`
and the pin agree. The gloss is where S3 bites, not the type. The shape matches
Row 2's `PGL27Analysis.coalition_endpoints : {ffun 'I_8 -> 'I_8}, executed;`
and Row 7's `: {ffun 'I_5 -> 'I_5}, executed;`, except for the new explicit
"with no execution" (N4).

**Capability lines.** Both are in Row 2's grammar,
`| theorem | distribution | observer | notion |`, and both use "approximate
privacy", which is in convention (3)'s closed list at the manifest's `:62-65`.
Row 2 names the law first and then the equation (`rho_word, the cut
distribution of fixed_word_sample by fixed_word_cut_distE`); the two new lines
have no alias for their law to name, so they open with "the cut distribution
of". That is the same construction Row 5's existing `deal_centi_lt` line
already uses ("the cut distribution of centi_sample, by centi_cut_distE"), so
the new Row 5 line is verbatim consistent with its neighbour.

**Direction of each equation.** Both cells are direction-neutral and both are
true, but the two equations do not run the same way, and a reader who assumes
they do will misread `kim_centi_cert`. `centi_cut_distE` runs `sa_cut_dist
centi_sample = sw_rho_dist bundle`, so Row 5's cell reads it right to left;
`biased_sample_cut_witnessE` runs `sw_rho_dist bound = sa_cut_dist
kim_single_sample`, so Row 4's cell reads it left to right. Each names the law
the mixing premise is stated at, and in each case that law is the one
`var_dist_fdistmap_transfer` is applied to. Recorded under S6, because STATUS
says the file "states both identification equations in one form".

**"twice".** Right, and it is the statement's own shape rather than a
multiplication. `kim_centi_static_obs_indist`'s right-hand side is
`sw_bound_eps (scb_bound (kim_security_bundle_centi R)) + sw_bound_eps (scb_bound (kim_security_bundle_centi R))`
and `kim_biased_static_obs_indist`'s is
`sw_bound_eps kim_biased_marginal_bound + sw_bound_eps kim_biased_marginal_bound`.
Same sum in `cert_eps`, which `manifest/pgg_tableau.v` defines as
`sw_bound_eps (sc_b cert) + sw_bound_eps (sc_b cert)`.

**Final-bridge cells and model-transfer cells.** Row 4's model-transfer cell
says the transfer's first hypothesis is `biased_cut_mixing` and its second is
`static_obs_const`; the proof of `kim_biased_static_obs_indist` applies
`var_dist_fdistmap_transfer` and discharges the two goals in that order, with
`exact: kim_biased_cut_mixing` and `exact: (@five_card_static_obs_const R C HC x x')`.
Row 5's cell says the same of `centi_cut_mixing`, and the proof of
`kim_centi_static_obs_indist` matches. Row 5's new clause "whose law is the cut
distribution of centi_sample by centi_cut_distE" is true: `kim_centi_cut_mixing`
is stated at `sw_rho_dist (scb_bound (kim_security_bundle_centi R))`, which is
`sa_cut_dist kim_centi_repeated_sample` by that equation.

**Level justifications against `AnalysisBridged`.** `pgg_analysis_status.v`
defines the level as "adds a theorem about that distribution and that
observer", and the manifest repeats it. Both rows now name the distribution
(the row's own cut law, through the named equation) and the observer
(`static_obs`, declared in the observers cell). Round 2's G1 and G2 are closed
by construction and not by assertion. Row 4's sentence also says
`colour_view_leak_bound` "reaches it at the executed reader colour_view" and
claims no relation between the two readers, which is right: the only result
relating a static reading to an executed one here is `five_card_static_obsE`,
in `five_card_rows.v`, above the manifest.

**Row docstrings.** `five_card_row_biased` and `five_card_row_repeated` carry
`apr_completion = AnalysisBridged` and `apr_transfer = IdealFinite`, and the
`erefl` pins at the end of the file agree. The docstrings say what the rows
now hold and name no absent premise, which the missing-premise cells ("none")
match.

## Question 2. The facade alias `static_obs`

**Docstring against the definition.** `Definition static_obs := @pgg_instance.static_coalition_obs five_card_algebra five_card_params`.
The docstring claims nothing about execution that the definition does not give:
`static_coalition_obs` takes a run argument and a group element directly, with
no `ObservedExecution` anywhere, so "before any execution is observed" is
exact. It claims nothing about the secret, and nothing about `colour_view`.
"the coalition's own seats read their own card and every other seat reads ord0"
is the definition's `if i \in C then ... else ord0` branch, with "card" the
wrong noun (S3). "It is the reader the two cut-carrier transfers of section 7
compare at two committed pairs" is true of both `kim_centi_static_obs_indist`
and `kim_biased_static_obs_indist`, whose two `fdistmap` arguments are
`@static_coalition_obs five_card_algebra five_card_params C x` and `... C x'`.
"the reader Kim's two certified rows state their bound at" is true:
`SpectralPropAt` is stated at `static_coalition_obs C x`, and both certified
programs carry it.

**"Seven carriers".** The count is right and the carriers are distinct: a
message list, `'I_5`, `bool * bool`, `seq 'I_5`, `(size A).-tuple bool`,
`{ffun 'I_5 -> 'I_5}`, `bool`.

**Check table row.** `(*   static coalition observer                -> static_obs                   *)`
sits with the other observer entries, and
`(*   one-cut identification equation          -> biased_sample_cut_witnessE   *)`
was moved by fix pass 2 to sit with the model entries, where the alias lives
(round 2's N3, applied). Both lines are 80 bytes.

**Manifest pin.** The spelled-type `Check` writes the unreduced
`'I_(pi_T' (mp_PI (instance_profile five_card_exec.five_card_algebra))).+1`
form, in the style of the observer pins around it, and compiles.

**Name.** Consistent with this development: `five_card_static_obs_const` and
the facade's own `static_obs_const` already spell this reader "static obs", and
naming the alias `static_view` would leave `static_obs_const` naming a
constancy of something no alias declares. `PGL27Analysis.static_view` and
`PSL211Analysis.static_view` alias `pgl27_view` and `psl211_alldecks_view`,
which are different terms from `static_coalition_obs` (related to it by a
lemma, `pgl27_rows.v:144`), so the different word is earned rather than drift.

**Collisions.** Whole-word Python scan over every `.v` file of the twelve
project directories and `legacy/`: `static_obs` **0** hits, `uniform_transfer_status`
**0** hits, `exec_transfer_status` 5 hits, all in files the landing edits
(`five_card_analysis.v` x3, `pgg_analysis_manifest.v`, `pgg_analysis_client.v`).
Same scan over `notes/probes/2026-09-19-psl211-nogo-landing/` and
`notes/probes/2026-09-19-tableau-extensions/`, `.v` and `.md`: **0** hits for
both new names. STATUS's count and mine agree.

## Question 3. The fidelity file's four lemmas

**`landing_centi_indist_of_program` and `landing_biased_indist_of_program`
mention no corollary.** Confirmed by reading the proofs. Each is
`move=> HC x x'`, one `have Hd` closed by the identification equation
(`exact: (kim_centi_cut_distE R)` / `exact: (esym (kim_biased_sample_cut_witnessE R))`),
`rewrite -Hd`, and
`by apply: (view_indist_of five_card_row_*_spectral_tableau R tt)`. Neither
`kim_centi_static_obs_indist` nor `kim_biased_static_obs_indist` appears, and
neither is reachable through the term either: `view_indist_of` projects
`published_thm`, whose spectral conjunct comes from `spectral_tail` applied to
the certificate, and the certificate's fields are `kim_centi_cut_mixing` /
`kim_biased_cut_mixing` and `five_card_static_obs_const`. So the derivation is
genuinely independent of the corollary, which is what round 2's G10 asked for.

**They start from `view_indist_of` of the published certified row.** Yes, and
at that row's own real field and index (`R`, `tt`).

**`cert_eps` versus "epsilon twice".** They are equal by delta alone.
`cert_eps cert := sw_bound_eps (sc_b cert) + sw_bound_eps (sc_b cert)`, a plain
`Definition`, and `sc_b (kim_centi_cert R tt)` reduces to
`scb_bound (kim_security_bundle_centi R)` by projection, so the stated
`<= cert_eps (kim_centi_cert R tt)` and the corollary's `<= eps + eps` are
convertible with no lemma. The same file's `kim_centi_cert40_epsE` closes by
`by []`, which is the direct evidence. The only step that needs a `Qed` lemma
is the distribution, through the identification equation, which is exactly what
the fidelity file's header says.

**`landing_centi_prop_of_indist` and `landing_biased_prop_of_indist`.** Both
are `move=> C x x' HC`, matching `SpectralPropAt`'s binder order
(`forall C x x', (#|C| < profile_k ...)%N -> ...`), one `have Hd` by the same
equation, `rewrite Hd`, and `exact (@kim_*_static_obs_indist R C HC x x')`.
They go from the corollary, not from a program.

**Is STATUS's description exactly true?** Almost. The fix-pass-2 bullet
describes the four lemmas correctly sentence by sentence and then closes with a
bolded claim that is false (S8). The L10 paragraph's "checks each row's bridge
corollary against the proposition its published certified program delivers, in
both directions" is fair: the two directions together do make the corollary and
`SpectralPropAt cert (cert_eps cert)` the same claim, one direction sourced
from the program and one from the corollary.

## Question 4. The landing procedure

**The script.** `tools/import_rewrite_table.py` compares correctly for what it
claims. It strips nested `(* ... *)` by depth, matches
`(?:From\s+\S+\s+)?Require\s+(?:Import|Export)[^.]*\.` over the stripped body
so a sentence may span lines, and normalizes whitespace with
`" ".join(s.split())`. `Require Import Lia.`, with no `From`, matches. Two
limits, neither reached here: `[^.]*` would truncate a dotted module path such
as `Foo.Bar`, and the comparison is `s not in copy`, a multiset-blind,
order-blind test, so a pure reordering of the import block would print nothing.
That matters only for the phrase "byte for byte", which the script does not
establish; the instruction it supports ("restore production's block") is
unaffected. I ran it: its output reproduces STATUS's pasted table exactly,
including the two counts round 2's G3 and A3 corrected (`s5_rows.v` and
`pgl27_rows.v` two lines each, `psl211_rows.v` three where production has two).
I also ran `tools/regen_diffs.py`: `TOTAL hunks 43, code hunks 23, of them with
a Require 10, landing 13`, which is L9's row exactly.

**Five files recompiled and not copied.** Correct and verified: the copies of
`pgg_tableau.v`, `pgg_tableau_syntax.v`, `s5_rows.v`, `pgl27_rows.v` and
`psl211_rows.v` differ from production in `Require` sentences only, so the
production text is already the permanent text.

**The four spelled import blocks.** Each matches the copy's own sentences with
`kim_landing_probe` rewritten to `pgg_smc`, checked sentence by sentence
against the script output. `five_card_mixing.v`'s block also moves
`var_dist_supp` from a trailing line into the `pgg_smc` library block and
splits `perm_uniform pgg_interface pgg_collusion_bound` in two; both are
spelled out.

**`_CoqProject`.** Both anchors confirmed in the production file as it stands:
line 34 is `lib/mutual_info_recoding.v` and line 35 `smc/graded_resource.v`;
line 75 is `instances/kim2025/five_card_models.v` and line 76
`instances/kim2025/five_card_analysis.v`.

**Dependency order.** The compile table lists it, eleven landing files in
order, plus the diagnostic that is not in `_CoqProject`.

**Cost row.** The table's figures are from one clean post-fix-2 run. They do
not match the four in the verdict table (S9). The prose's attribution of the
four sentences over 3 s is confirmed for `five_card_rows.v` by my own `-time`
run: the slowest landing-written sentence is the `by []` at 3.26 s (S2).

**Could someone execute it mechanically? Judgement calls left:**

1. `instances/kim2025/five_card_analysis.v`: "production's block with its last
   imported-cone line followed by `From pgg_smc Require Import five_card_mixing.`"
   asks the executor to decide which line is the last of the imported cone.
   Unambiguous in fact, since it is the last line of the block, but it is the
   one import block not spelled in full.
2. `_CoqProject` is named twice, once by absolute line number and once by
   neighbour. If another landing goes first the numbers move; the neighbours do
   not. The executor must prefer the neighbours. (In the actual order this is
   moot: the PSL landing's line lands in the `instances/psl211` block, below
   both of these.)
3. `card_tnth_count`'s home against the file name `var_dist_supp.v`, explicitly
   "flagged for the user": the owner may reopen decision 3 of the spec instead.
4. The dated status line on `notes/20260919-kim-tableau-sampled-design.md` and
   the superpowers plan, explicitly deferred to the implementation plan.
5. **Not named at all:** `notes/20260919-dealer-law-and-kim-rows-summary.md:118`
   (S10), and the two probe files that `Print Assumptions` the deleted
   `five_card_row_repeated_at_manifest_level`.

Nothing else needs a decision. The four permanent import blocks, the six
production restorations, the two `_CoqProject` anchors, the file list and the
compile order are all spelled.

**`Lia`, `zify`, `lra` in an instance rows file.** All three are needed.
`lia` is used once, in `kim_biased_exact_le_eps`, on a goal that is `(_ <= _)%N`
in `ssrnat` after `ler_nat`, which is what needs `zify`; plain `Lia` cannot
close it. `lra` is used in `five_card_inv50_split`, `five_card_reprice_inv25_lt2`
and at the end of `kim_biased_cert_eps_lt2`. Precedent for the exact spelling
is one directory over: `instances/kim2025/five_card_kim.v:74-75` reads
`Require Import Lia.` then `From mathcomp Require Import zify.`, and `lra` is
imported by nine production files including `instances/denboer1989/five_card_leakage.v`
and `instances/kim2025/kim_input_privacy.v`. No **rows** file imports an
arithmetic tactic today, but no rows file had a numeric lemma today either;
`instances/pgl27/pgl27_rows.v` reaches its identity by importing `pow2_split`
from `pgl27_word_privacy.v`, which is the alternative this landing could not
take without making the Kim instance depend on the PGL(2,7) one (N1). The
convention allows it; the cost is about 1.6 s per build (N2).

## Question 5. Sentences fix pass 2 rewrote

- **G5, direction.** Closed in both places. `five_card_mixing.v` and
  `five_card_analysis.v` now read "the number bounds every advantage it has in
  telling the two pairs apart". True; loose by two (N3).
- **G6, "about three percent of the ceiling".** Arithmetic checked:
  `cert_eps (kim_biased_cert R idx) = Num.sqrt 5%:R * (1 / 80) + Num.sqrt 5%:R * (1 / 80)`,
  that is `sqrt 5 / 40 ~ 0.0559`, against `var_dist_le2`'s ceiling of 2, so
  2.8 percent. The same figure appears in `kim_biased_cert_eps_lt2`'s docstring.
  Consistent, and "and no more" is gone.
- **G7, why the corollary sits below the facade.** The new reason holds:
  `five_card_rows.v` imports `pgg_analysis_manifest`, so the manifest is below
  the file that certifies the rows; the manifest's own contract says "The
  record stores no theorem: theorems stay facade aliases"; and
  `five_card_analysis.v` imports `five_card_mixing`, so the facade is above it.
- **A5.** "the seven-cut cut" is gone; the file writes "the seven-cut law".
- **A6, one word.** "identification" in all five files. Whole-word scan of the
  probe directory for "tying"/"tie"/"tied": three hits, all production and all
  the Tableau surface keyword (`pgg_tableau_syntax.v:62` and `:384`,
  `pgl27_rows.v:300`). No landing file uses the keyword. N6 records the
  residual.
- **A7, the at-most-one-seat restriction.** Every statement of the constancy
  outside `five_card_mixing.v` now carries it: `five_card_analysis.v:18`,
  `five_card_rows.v:549` and `:564` (both added by this pass), `:710`, and the
  manifest's "Absent capabilities" paragraph. `five_card_rows.v:592` names the
  certificate field rather than the statement and needs none.
- **Comment boxes at column 80.** Measured over all seven `.v` files: **no
  line exceeds 80 bytes** outside lines byte-identical to production, and every
  inner comment-box line is exactly 80 bytes. Round 2's G9 and A4 are closed.
  What is not closed is the paragraph fill inside four of them (S1), and the
  barred two-character distance term is gone from the S_5 paragraph, replaced
  by "the sum of the absolute differences ... is at least one", which is what
  coset confinement gives.

## Question 6. Round-2 items, one line each

| ID | Disposition |
|---|---|
| G1 | Closed. Row 4's level justification no longer calls the corollary a theorem at `colour_view`'s observer; it names `static_obs` as the second declared observer. |
| G2 | Closed. Both observers cells declare `static_obs` with its carrier, and both rows have a capability line for their bridge corollary. |
| G3 | Closed differently, and better: the table is now generated by a script whose output I reproduced, the "exhaustive" sentence is gone, and the instruction for the six repointed copies is "restore production's block" rather than a per-line rewrite. N7 records one residual. |
| G4 | Closed. Two capability lines in Row 2's grammar, with "approximate privacy" from the closed list. |
| G5 | Closed. |
| G6 | Closed. |
| G7 | Closed, with a reason that holds. |
| G8 | Closed. STATUS item 1 now says the `lib/` files open with a descriptive phrase, agreeing with the fix-pass bullet. |
| G9 | Closed. |
| G10 | Closed. The two program-side lemmas contain neither corollary, syntactically or in the term. |
| N1 | Declined; **partly sound, and the decline created S3.** The observer declaration does remove the `colour_view` conflation, which was the warning's point. But the new declaration spells the reading "endpoint cards" while four older sentences spell it "colours" and the same section header spells the carrier "card position", so the file now has three words where it had two. |
| N2 | Closed. STATUS now says the `amf_sample` form follows by conversion and names the `by []` that shows it. |
| N3 | Closed. The line sits with the model entries. |
| N4 | Closed. The line-number citation is gone. |
| A1 | Closed (= G4). |
| A2 | Closed (= G2). |
| A3 | Closed (= G3), including the `l7_fail_messages.v` row, now covered by "Two files of this directory land nowhere". |
| A4 | Closed for the box; the paragraph is reflowed. |
| A5 | Closed. |
| A6 | Closed differently: "identification", not the audit's proposed "tying". Sound, and better: it is `manifest/pgg_tableau.v`'s own word for the field. |
| A7 | Closed. |
| A8 | Closed for `var_dist_supp.v`; the same defect recurs in two docstrings the pass wrote (S1a, S1b). |
| A9 | Applied, and the replacement text is broken (S6). |
| A10 | Closed. `uniform_transfer_status`, five sites plus the fidelity print, zero collisions. |
| A11 | Closed. The index line is type-honest: "the two readings ... are within twice that number of each other". |
| A12 | Closed. The docstring names `kim_centi_cut_distE`. |
| A13 | Closed. Row 5's model-transfer cell names `centi_cut_distE`. |
| A14 | Declined; **sound.** Both sites are untouched production text ("five_card_row_biased_leak_bound states a ceiling on it"), and the audit itself asked for a later pass over the production file, not a landing change. |
| A15 | Closed. The docstring now says "the attacker is that coalition", using the opening phrase once. |
| A16 | Declined; **sound.** The table is checked against the phase-H1 minimum list, and adding an entry the list does not ask for widens the minimum. The decline is slightly in tension with the six entries this landing does add to the same table, but those all correspond to newly public aliases, and `sample_cut_witnessE` was public before. |
| A17 | Declined; **sound.** The audit asked for no change and recorded the two sentences for one owner decision over all three; STATUS repeats that. |
| A18 | Declined; **sound.** "endpoint marginal bound" is production text at Row 4's and Row 5's existing cells, outside the landing. |
| A19 | Kept, with the decision recorded; **half sound.** The "claimed or premise" argument is right: `kim_biased_exact_le_eps` is the premise of `kim_biased_cert_exact`'s docstring sentence about the price of quoting the bundle's number. The audit's alternative, the index, is still not done, and five more declarations of indexed kinds are missing with it (S5). |

## Question 7. The other two landings

**(a) The PSL landing.** No conflict. The Kim landing's file set is
`lib/var_dist_supp.v` (new), `instances/kim2025/five_card_mixing.v` (new),
`instances/kim2025/five_card_analysis.v`, `instances/kim2025/five_card_rows.v`,
`manifest/pgg_analysis_manifest.v`, `manifest/pgg_analysis_client.v` and
`_CoqProject`. The PSL landing's is
`instances/psl211/psl211_spectral_constancy.v` (new),
`instances/psl211/psl211_rows.v` (header comment) and `_CoqProject`. The only
shared file is `_CoqProject`, and the PSL line goes in the
`instances/psl211` block, production lines 202-222, below both Kim insertion
points at 35 and 76, so neither landing moves the other's anchor. The Kim
landing recompiles `psl211_rows.v` as a reverse-dependant of the manifest but
does not copy or edit it, so a rewritten PSL header passes through untouched.
One record staleness, not a conflict: if PSL lands first, the Kim probe's
verification that its `psl211_rows.v` copy equals production outside the
`Require` lines no longer reproduces, because the header will have changed.

**(b) Stage A of the extensions probe.** Stage A weakens `RepricePayload` from
`cert_eps cert = odflt (cert_eps cert) (c R)` to `cert_eps cert <= odflt ...`,
and adds the surface `|> conclude c by p`, with the one existing payload
rewritten as `(fun R _ => ssr_ext.eqW (pow2_split R))`. Nothing here is
blocking, and nothing in this landing is wrong today. What becomes false or
stale when stage A lands, to be recorded:

1. `five_card_rows.v`, `five_card_row_repeated39_bare`'s docstring: "**The
   reprice obligation is one identity per real field and per index.**" becomes
   false; the obligation becomes one inequality per real field and per index.
   The recorded `Fail` still fails, and for the same reason (the payload is not
   quantified over the index), but its stated reason needs the noun changed.
2. STATUS, "The recorded failures of `five_card_rows.v`":
   "`five_card_row_repeated39_bare`, copied from SRC: **`conclude` asks for one
   identity per real field and per index**." Same sentence, same correction.
3. `five_card_pow2_39_split`'s docstring, "**this identity is what names that
   sum by a single constant**", and `five_card_inv50_split`'s, "**It is the
   identity that names the sum ... by the single constant that row
   publishes**". Under stage A a reprice publishes an upper bound, so "names"
   becomes "bounds"; the extensions probe already makes exactly this change to
   the Tableau syntax index ("`conclude == the terminal republishing the
   bound`" is false, becomes "publishing an upper bound").
4. `five_card_rows.v` index: "`five_card_reprice39, five_card_reprice_inv25 ==
   the names 2^-39 and 1/25 for a bound**"** takes the same correction the
   extensions probe's G3 already schedules for `pgl27_rows.v:53-54`
   ("republished at that name" becomes "concluded at that number").
5. **Three payload sites, not one.** The extensions probe's C2 verdict reads
   "GO, one payload changed in the whole tree | `pgl27_rows.v:382`", and its
   D2 list was built by searching the tree before this landing. After this
   landing there are three `conclude` payloads,
   `five_card_row_repeated39`'s `(fun R _ => five_card_pow2_39_split R)`,
   `five_card_row_biased_inv25`'s `(fun R _ => five_card_inv50_split R)` and
   the `pgl27_rows.v` one, plus the bare payload inside the recorded `Fail`.
   Whichever lands second must re-run the D2 search; if the Kim landing goes
   first, stage A's C2 row and its rewrite table both need the two new sites.

## Question 8. The hang shape in `five_card_rows.v`

Compiled the landing copy once with `-time` through the lock wrapper (rc 0, 218
sentences, 8.12 s of sentence time). Every equation about a published row or
its coordinates, with its measured time:

| lemma | closer | time |
|---|---|---|
| `five_card_row_uniform_rowE` (production) | `by []` | 0.000 s |
| `five_card_row_repeated_modelE` (production) | `by []` | 0.000 s |
| `five_card_row_biased_modelE` (production) | `by []` | 0.000 s |
| `five_card_row_biased_levelE` (production) | `by []` | 0.000 s |
| `five_card_row_repeated_spectral_rowE` (new) | `by []` | 0.000 s |
| `five_card_row_biased_spectral_rowE` (new) | `by []` | 0.000 s |
| `five_card_row_repeated_spectral_publishedE` (new) | `by []` | 0.000 s |
| `five_card_row_biased_spectral_publishedE` (new) | `by []` | 0.000 s |
| `kim_centi_cert40_epsE` (new, a number not a row) | `by []` | 0.000 s |
| **`five_card_row_biased_forms_publishedE` (new)** | **`by []`** | **3.263 s** |

Exactly one compares a **concluded** row with an **unconcluded** one:
`five_card_row_biased_forms_publishedE`, whose left side is
`published_row five_card_row_biased_spectral_tableau`
(a `PublishedRow`, that is `PublishedRowAt no_reprice`, built with
`certify ... |> publish ...` and no `conclude`) and whose right side is
`published_row five_card_row_biased_inv25` (a
`PublishedRowAt five_card_reprice_inv25`, built with
`;;; conclude five_card_reprice_inv25 of ...`). That is the 2026-09-19 shape,
and it is the most expensive sentence in the file by a factor of two over the
next one.

It costs 3.26 s rather than 683 s because the projection is `published_row`,
the descriptive `AnalysisPathRow`, and not `published_at`, the dependent
`StackAt AnalysisBridged`. The recorded fix still applies. Measured in
`audit-3/a3_erefl.v`, both closers on the same goal, rc 0:

```
by [ ]            3.21  secs
exact : erefl     0.452 secs
```

Recommendation S2: `Proof. exact: erefl. Qed.` There is no counterpart lemma
for the repeated pair (`five_card_row_repeated_spectral_tableau` against
`five_card_row_repeated39`), so this is the only site.

## Question 9. Statement comments, width, vocabulary

**Statement-comment rule on everything fix pass 2 wrote.** Every rewritten
docstring states the fact and its position in the argument, and none carries
meta, status, effort, proof strategy or attribution. Two are worth naming as
good: `static_obs`'s says what the reader **omits** ("before any execution is
observed") and why it matters (it is the reader the transfers compare and the
rows state their bound at), which is the rule's "write what a thing is,
including what it omits"; and `kim_centi_static_obs_indist`'s prices the step
and labels the currency ("The number is the bundle's spectral one spent once
for each pair, so the only inexact quantity is that mixing distance; the
constancy of the ideal reading is exact and costs nothing"). One residual:
`kim_biased_static_obs_indist`'s new closing sentence, "Its number is about
three percent of the ceiling `var_dist_le2` gives, so it is a weak separation
bound and not a cryptographic one", names a lemma in a statement body. That is
domain position, not meta, and the lemma is the scale the number is read
against, so it stays.

**Width.** No `.v` line of any copy exceeds 80 bytes outside lines
byte-identical to production. Every inner comment-box line is exactly 80 bytes.
The short lines that remain in `five_card_analysis.v`, `pgg_analysis_client.v`
and `pgg_analysis_manifest.v` are production section markers
(`(* ===== 3. Observers ===== *)`, `(* --- 7 Transfer --- *)`) and three
production lines at 78 and 79 bytes, all byte-identical to production.

**Barred vocabulary.** Whole-word Python scan over all seven `.v` copies,
`_CoqProject`, `STATUS.md` and both scripts: **apex** 0, **gate/gates/gated/gating**
0, **posit/posits/posited/positing** 0, the two-character capital-L-one distance
token 0 (the S_5 paragraph now writes "the sum of the absolute differences"),
metaphor words for results (escape, beats, smash, dodge, headline, cap as a
noun) 0. Identifiers: none of the twenty-six new declarations carries a barred
word; all are built from the tree's own fragments (`cert`, `eps`, `epsE`,
`reprice`, `split`, `spectral`, `obs`, `indist`, `lt`, `lt2`, `E`).

## What I did not check

- The twelve compiles the main session reported, the assumption blocks, the
  comment-stripped equality of the five recompiled-only copies, and the
  facade/manifest/client difference list. Taken as given, as instructed.
- The mathematics, the names and the numbers that rounds 1 and 2 settled. I
  re-derived only the two figures fix pass 2 wrote (2.8 percent, and "twice").
- I did not open `kim_centi_marginal_bound40`, `kim_centi_cut_mixing40`,
  `kim_biased_marginal_bound_exact`, `kim_biased_cut_mixing_exact`,
  `kim_one_cut_centi_le`, `kim_bound_centi` or `kim_lambda2_at_centi`. The
  repriced certificates rest on them and rounds 1 and 2 checked them.
- I did not compile `five_card_mixing.v`, `five_card_analysis.v`,
  `pgg_analysis_manifest.v` or `kim_landing_fidelity.v`. Two compiles only,
  `five_card_rows.v` with `-time` and the scratch file, as instructed.
- I did not compile `instances/psl211/psl211_endpoints.v` and did not run
  `make`.
- I did not verify the extensions probe's own stage-A claims beyond reading its
  `RepricePayload` and its C2 and D2 sections; question 7b is about this
  landing's sentences, and those I read in full.
- I did not check the `diffs/` files byte by byte; I re-ran the script that
  writes them and compared its printed table with STATUS's.
