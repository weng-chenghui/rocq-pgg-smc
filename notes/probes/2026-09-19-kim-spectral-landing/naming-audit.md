# Naming, style and statement-comment audit of the Kim spectral landing

**NO-GO** for "these five files may be copied into the permanent tree as they are".

Five blocking findings. None of them is a proof defect: the mathematics
checked out at every point I could trace it without a compiler. Four are
sentences that claim more than the declaration they describe, or name a bridge
that does not bridge; one is the probe's own logical path left in five import
lines. All five are comment-and-import edits except B3, which is a rename of
three names that exist nowhere outside this landing.

Scope: `notes/probes/2026-09-19-kim-spectral-landing/` (`PROBE` below), the two
new files in full, the three edited files through `diffs/` read in their
surroundings. Read-only: no compiler was run, no file outside this one was
touched. Line numbers are PROBE line numbers.

---

## BLOCKING

### B1. The probe's logical path is in five import lines

`cp` alone does not produce the permanent files: `From kim_landing_probe
Require ...` resolves to the probe directory and must become `pgg_smc`.

| file | line | now |
|---|---|---|
| `five_card_mixing.v` | 68 | `From kim_landing_probe Require Import var_dist_supp.` |
| `five_card_analysis.v` | 92 | `From kim_landing_probe Require Import five_card_mixing.` |
| `pgg_analysis_manifest.v` | 75-76 | `From pgg_smc Require Export pgl27_analysis s5_analysis psl211_analysis.` + `From kim_landing_probe Require Export five_card_analysis.` |
| `five_card_rows.v` | 183-185 | three `From kim_landing_probe Require Import ...` lines |

Replacements.

`five_card_mixing.v`: `var_dist_supp` is a `lib/` file and belongs in the
`pgg_smc` library block, not appended after `algebraic_rigidity`. Replace
line 58 with two lines and delete line 68:

```
From pgg_smc Require Import perm_uniform var_dist_supp.
From pgg_smc Require Import pgg_interface pgg_collusion_bound.
```

`five_card_analysis.v:92`:

```
From pgg_smc Require Import five_card_mixing.
```

`pgg_analysis_manifest.v:75-76`, restoring the production form:

```
From pgg_smc Require Export pgl27_analysis five_card_analysis s5_analysis
                            psl211_analysis.
```

`five_card_rows.v:183-185`:

```
From pgg_smc Require Import five_card_mixing.
From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
```

`_CoqProject` gains two lines, in dependency order: `lib/var_dist_supp.v`
after `lib/mutual_info_recoding.v`, and `instances/kim2025/five_card_mixing.v`
between `instances/kim2025/five_card_models.v` and
`instances/kim2025/five_card_analysis.v`.

### B2. Row 4's capability line names a bridge that does not bridge

`pgg_analysis_manifest.v:325-327`:

```
(* | biased_cut_mixing | the cut distribution of single_biased_sample, by     *)
(*   single_cut_distE | the cut carrier {perm 'I_5}                           *)
(*   | cut-carrier mixing |                                                   *)
```

`biased_cut_mixing` is stated at `sw_rho_dist (kim_biased_marginal_bound R)`,
which unfolds to `@rho_from_words_weighted R 3 4 1 fc_kim_gens (kim_weight_dist
...)`. `single_cut_distE` (`five_card_models.v:188`) says

```
sa_cut_dist kim_single_sample
  = fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g) (kim_weight_dist ...)
```

These are two different terms. Closing the gap needs two further lemmas,
`rho_from_words_weighted1` (`five_card_exec.v:947`) and `fc_kim_gensE`
(`five_card_kim.v`), which is exactly the chain this landing's own
`kim_biased_sample_cut_witnessE` (`five_card_rows.v:540`) runs. The cell as
written attributes to one named lemma an identification it does not make, and
Row 4's level and transfer status rest on that attribution.

Row 5's analogue is exact and needs no change: `centi_cut_distE`
(`five_card_models.v:403`) is literally `sa_cut_dist kim_centi_repeated_sample =
sw_rho_dist (scb_bound (kim_security_bundle_centi R))`, the very term
`centi_cut_mixing` speaks about.

**Minimum fix, comment only.** Replace `pgg_analysis_manifest.v:325-327` with:

```
(* | biased_cut_mixing | the length-one weighted word shuffle, which is       *)
(*   the cut distribution of single_biased_sample by single_cut_distE         *)
(*   composed with rho_from_words_weighted1 and fc_kim_gensE                  *)
(*   | the cut carrier {perm 'I_5} | cut-carrier mixing |                     *)
```

**Recommended fix, structural.** The tree already carries the one-name form of
this identity for the other two five-card models: `kim_centi_cut_distE` for the
seven-cut law and `den_boer_witness_rotationE` / `den_boer_sample_cut_witnessE`
(`five_card_exec.v:976,990`) for the uniform one. The one-cut law is the only
one whose tying equation lives above the manifest. Move
`kim_biased_sample_cut_witnessE` from `five_card_rows.v` down into
`five_card_mixing.v` (everything it needs, `five_card_models` and
`five_card_exec`, is already imported there), alias it in the facade beside
`sample_cut_witnessE` as `biased_cut_witnessE`, and let the Row 4 cell read
`by biased_cut_witnessE`. This needs a compile, which this audit did not run.

### B3. Two words for one concept: `_spectral_` and `_ideal_` name the same construction

`five_card_rows.v` builds the two certified programs identically, `certify
SpectralDecay ... |> publish IdealFinite ...`, and names one after the arm and
the other after the transfer status. Inside one file that reads as two
different constructions.

| old | new | reason |
|---|---|---|
| `five_card_row_biased_ideal_tableau` | `five_card_row_biased_spectral_tableau` | same arm, same status, same shape as `five_card_row_repeated_spectral_tableau`; one word per concept |
| `five_card_row_biased_ideal_rowE` | `five_card_row_biased_spectral_rowE` | follows its program |
| `five_card_row_biased_ideal_publishedE` | `five_card_row_biased_spectral_publishedE` | follows its program |

Cost is zero outside the landing. Occurrences in PROBE `five_card_rows.v`:
103, 133, 434, 502, 594, 611, 612, 636, 637, 639, 641, 796. In PROBE
`kim_landing_fidelity.v`: 32, 33, 99, 101, 103. Nothing in the production tree,
in `legacy/` or in the installed libraries mentions any of the three.

### B4. `var_dist_supp.v` header describes two of its own lemmas wrongly

`var_dist_supp.v:12-15`:

```
(* number becomes a number about the group. Beside it sit the ceiling a       *)
(* published variation distance is read against, two support facts about      *)
(* pushforwards, and the count that reads a law on tuple positions off the    *)
(* underlying sequence.                                                       *)
```

Two errors. `fdistmap_inj_uniform_id` is not a support fact: it says an
injective endomap leaves the uniform law fixed. And `card_tnth_count` contains
no law at all, only `#|[pred k | p (tnth t k)]| = count p t`; calling it "the
count that reads a law on tuple positions" is not type-honest. The index entry
for the same lemma at line 23-24 is correct, which makes the header the only
wrong description of it.

Replacement for lines 12-15:

```
(* number becomes a number about the group. Beside it sit the ceiling a       *)
(* published variation distance is read against, the invariance of a uniform  *)
(* law under an injective endomap, the fact that a pushforward charges only   *)
(* the image, and the count of the tuple positions at which a predicate       *)
(* holds.                                                                     *)
```

### B5. Two headline sentences drop the at-most-one-seat restriction

`five_card_static_obs_const` carries the hypothesis `#|C| < profile_k
(instance_profile five_card_algebra)`, and `profile_k` here is 2, so it holds at
coalitions of at most one seat and says nothing at two. Two sentences that are
read outside the file that proves it state the constancy unconditionally.

`five_card_analysis.v:18`, and `pgg_analysis_manifest.v:700`, both say "the
constancy of a coalition's reading of that law". Everywhere else the landing is
careful: the facade's own section-7 block at 362, the facade docstring at 379,
`five_card_mixing.v:271` and the rows-file header at 32-33 all carry the
restriction.

Replacement for `five_card_analysis.v:16-19`:

```
(* Section 7 carries the two base premises Kim's one-cut and seven-cut rows   *)
(* rest on, the distance of each cut law from the uniform rotation law and    *)
(* the constancy, at every coalition of at most one of the five seats, of     *)
(* that coalition's reading of the uniform rotation law, together with one    *)
(* typed transfer status per analysis path.                                   *)
```

Replacement for `pgg_analysis_manifest.v:698-703`:

```
(* Five-card development. Section 7 of its facade carries the distance        *)
(* of each of Kim's two cut laws from the uniform rotation law on the cut     *)
(* carrier and the constancy of the reading of that law at every coalition    *)
(* of at most one of the five seats, so rows 4 and 5 claim a cut-carrier      *)
(* transfer and name no absent premise. Row 3's own cut law is the uniform    *)
(* rotation, so that row has no finite model to compare with an ideal one     *)
(* and claims no transfer.                                                    *)
```

---

## SHOULD-FIX

### S1. `var_dist_supp.v` uses the `instances/` docstring shape, not `lib/`'s

Measured over every `(**` docstring in the two directories:

| file | `(**` docstrings | opening with `identifier —` |
|---|---|---|
| `lib/perm_uniform.v` | 11 | 0 |
| `lib/support_posterior.v` | 13 | 0 |
| `lib/mutual_info_recoding.v` | 3 | 0 |
| `lib/proba_entropy_ext.v` | 1 | 0 |
| `lib/perm_exchange.v` | 0 (uses `(* ... *)`) | — |
| `instances/pgl27/pgl27_mixing.v` | 12 | 12 |
| `instances/kim2025/five_card_analysis.v` | 52 | 52 |
| `instances/kim2025/five_card_kim.v` | 49 | 17 |
| `instances/kim2025/five_card_rows.v` | 31 | 0 |

`lib/` is uniformly descriptive-phrase, with no exception in 28 docstrings.
`var_dist_supp.v` opens all five with `identifier —`. Either convert its five
to descriptive openings (`The variation distance between two laws on a finite
carrier is at most two, ...`), or accept the deviation as a deliberate change
to the `lib/` convention and say so once in the file header.

`five_card_mixing.v` is correct as it stands: `identifier —` on all 16
docstrings, matching `pgl27_mixing.v` and `five_card_analysis.v`, and
internally consistent. `five_card_rows.v`'s new docstrings open with a
descriptive phrase, matching that file's own 31 existing ones. Both are right.

### S2. The rows index calls `2^-39` a ceiling

`five_card_rows.v:138-139`:

```
(*   kim_centi_cert_eps_lt, kim_biased_cert_eps_lt2                           *)
(*                           == each of those numbers against a ceiling       *)
```

`kim_biased_cert_eps_lt2` is against 2, the ceiling `var_dist_le2` gives. But
`kim_centi_cert_eps_lt` is against `2^-39`, which is the constant PGL(2,7)'s
word row publishes, not a ceiling; its own docstring at 641-642 says so. The
file uses "ceiling" for 2 in three other places, so this entry gives one word
two meanings. Replacement:

```
(*   kim_centi_cert_eps_lt   == the repeated row's number is under the        *)
(*                              constant PGL(2,7)'s word row publishes        *)
(*   kim_biased_cert_eps_lt2 == the one-cut row's number is under the         *)
(*                              ceiling a variation distance has              *)
```

### S3. Six declarations the tree's convention indexes are missing from the rows header

The index is selective by convention (production `five_card_rows.v` omits 3 of
31, `pgl27_rows.v` 5 of 36), so exhaustiveness is not the standard. But six of
the landing's seventeen unindexed declarations are of kinds the tree does
index, and `pgl27_rows.v` indexes its own counterpart of two of them:

| missing | line | precedent |
|---|---|---|
| `kim_biased_sample_cut_witnessE` | 540 | `five_card_exact_witness` is indexed |
| `five_card_reprice39` | 733 | `pgl27_reprice39` is indexed |
| `five_card_reprice_inv25` | 776 | same |
| `five_card_pow2_39_split` | 653 | the reprice obligations |
| `five_card_inv50_split` | 772 | same |
| `five_card_reprice_inv25_lt2` | 802 | the smallness comparison, like `kim_centi_small` |

Add to `Definitions:` after the `kim_centi_cert40, kim_biased_cert_exact`
entry:

```
(*   kim_biased_sample_cut_witnessE                                           *)
(*                           == the one-cut adapter draws from the law the    *)
(*                              length-one bundle bounds                      *)
(*   five_card_reprice39, five_card_reprice_inv25                             *)
(*                           == the names 2^-39 and 1/25 for a bound          *)
```

and to `Key results:` after the `kim_centi_cert_eps*` entries:

```
(*   five_card_pow2_39_split, five_card_inv50_split                           *)
(*                           == the identity each reprice discharges          *)
(*   five_card_reprice_inv25_lt2                                              *)
(*                           == the repriced one-cut number under the ceiling *)
```

### S4. `kim_biased_sample_cut_witnessE` is a transparent `Definition` of a Prop with no reason given

`five_card_rows.v:540-545`. Every other equation in the file is `Lemma ...
Proof. ... Qed.`; a transparent proof term is a conversion decision and the
reader cannot see which conversion needs it. Either make it a `Lemma` (if the
row equations still go through by `by []`), or keep the `Definition` and put
the reason in a non-rendered source comment above it, for instance:

```
(* Transparent: the row equations below decide by conversion and unfold this
   field of the certificate. *)
```

Note that if B2's structural fix is taken, this declaration moves to
`five_card_mixing.v` and the question moves with it.

### S5. `kim_biased_exact_le_eps` ends on a judgement about the artifact

`five_card_rows.v:518-521`, last clause: "and the row is honest rather than
tight". That is an assessment of the file, not of the mathematics, and it is
the one clause of the docstring that would not survive the proofs being redone.
Replacement for the whole docstring:

```
(** The exact one-cut distance of kim_one_cut_centiE, one fiftieth, is under
    the spectral bound the certificate publishes, sqrt 5 over eighty. The
    certificate therefore overstates the distance it certifies by about two
    fifths, and the gap is the price of quoting the bundle's number rather
    than the exact one. *)
```

### S6. `kim_centi_cert40`'s docstring narrates a diff

`five_card_rows.v:709-714`: "That field and the mixing statement proved against
it are the two that change." A reader of the declaration alone cannot tell what
"change" is relative to, and the sentence is about the edit rather than the
object. Replacement:

```
(** The repeated row's certificate with the constant in the marginal-bound
    field. The ideal cut, the tying equation and the constancy of the reading
    at every coalition of at most one seat are the same terms as in
    kim_centi_cert; the marginal bound carries two to the minus fortieth in
    place of the spectral expression, and the mixing field is the same
    distance bounded by that constant. *)
```

### S7. Name the existing declarations `var_dist_supp.v` weakens

`var_dist_supp.v:6` says "The equality case of the data processing inequality",
and line 72-73 repeats it. The tree already has both results under names:
`var_dist_fdistmap` is its name for the inequality and
`var_dist_fdistmap_inj` for the whole-domain equality case, both in
`security/pgg_collusion_bound.v`. Naming them is how a reader finds the lemma
this one weakens, and how a later reader knows the near-duplicate proof at
lines 82-111 is deliberate. Add to the docstring of
`var_dist_fdistmap_supp_inj` (lines 71-76), replacing "It is the equality case
of the data processing inequality with injectivity weakened":

```
    It is var_dist_fdistmap_inj, the equality case of the data processing
    inequality var_dist_fdistmap, with injectivity weakened
```

The name itself is well formed against that family and needs no change.

---

## NOTES

### N1. The file name `var_dist_supp.v`: keep, and keep `card_tnth_count` in it

Transitive reverse-dependant counts, computed from `.Makefile.rocq.d`:

| candidate home | reverse-dependants | `psl211_endpoints` among them |
|---|---|---|
| `lib/var_dist_supp.v` (new) | 0 | no |
| `instances/denboer1989/den_boer_encoding.v` | 16 | no |
| `lib/perm_exchange.v` | 17 | **yes** |
| `instances/kim2025/five_card_kim.v` | 20 | no |
| `security/pgg_weighted_words.v` | 39 | no |
| `security/pgg_collusion_bound.v` | 105 | **yes** |
| `lib/perm_uniform.v` | 107 | **yes** |

`lib/perm_exchange.v` is the only existing `lib/` file whose subject is
combinatorial, and it is barred: the spec's soundness invariant 6 forbids
editing any file with `psl211_endpoints` among its reverse-dependants.
`den_boer_encoding.v` would give a PGG-free lemma a PGG-specific home, which is
the reason `lib/var_dist_supp.v` exists at all. A third new `lib/` file for one
four-token lemma is worse than a disclosed passenger.

Renaming the file is not worth it either. Any name covering both subjects
(`fdist_supp_ext`, `var_dist_ext`) is vaguer than one naming the headline
lemma, and `lib/perm_uniform.v` is the tree's own precedent for a grab-bag
under a headline name. Keep `var_dist_supp.v`, and let the header disclose the
passenger accurately, which is what B4 fixes.

### N2. "cut-carrier mixing" is well formed and duplicates nothing

"cut carrier" is already the manifest's own phrase, at Row 2's missing-premise
cell ("on the cut carrier itself", line 184 of production) and at Row 8's
missing-premise and model-transfer cells. Row 2 has **no** capability line for
`word_mixing` at all: its four capability lines are "approximate privacy at
2^-39" and one at 2^-40, and `word_mixing` appears only in the bound-or-
certificate and missing-premise fields. So no existing term is being
duplicated. The nearest existing terms, Row 8's "cut-level endpoint marginal
mixing" and "executed endpoint marginal mixing", are about endpoint marginals
on `'I_5` and name a different kind of theorem.

Out of this landing's scope, but worth the owner's attention: for one concept
to have one word tree-wide, Row 2 should eventually carry a `word_mixing |
rho_word | the cut carrier {perm 'I_8} | cut-carrier mixing |` line too.

### N3. No collisions

64 new identifiers, extracted from the two new files and from the `+` lines of
the three diffs, scanned with Python `re` and `\b` over 195 production `.v`
files (every directory in `_CoqProject`, `legacy/` included) and 1153 `.v`
files under `~/Projects/coq/_opam/lib/coq/user-contrib`. Zero hits.
`repeated_transfer_status` is picked up by the extractor because the diff
re-declares it; it is an existing name whose value changes, not a new one.

Two near-neighbours are worth recording as deliberate, not accidental:
`fdistmap_inj_uniform_id` sits beside `fdistmap_inj_uniform`
(`security/pgg_collusion_bound.v:572`) and `var_dist_fdistmap_supp_inj` beside
`var_dist_fdistmap_inj` and `fdistmap_uniform_supp_inj` in the same file. All
three new names are distinct and the suffixes follow that family.

### N4. Line length

Every line of both new files is at most 80 bytes. The only line above 80 in the
five files is `five_card_analysis.v:313` at 81 bytes, which is 79 characters
with a three-byte em dash, is untouched production, and is not in any diff
hunk.

### N5. Banned vocabulary

Zero whole-word hits for `apex`, `gate`/`gates`/`gated`/`gating`,
`posit`/`posits`/`posited`/`positing` across all five files.

### N6. The barred term, and a malformed box beside it

One occurrence, `pgg_analysis_manifest.v:718`, production `:688`,
pre-existing. Replacement for lines 714-720, which also closes the comment box
at line 714 that production leaves ragged (`... on the*)`):

```
(* group-uniform ideal. For Q the uniform distribution on the generated       *)
(* group the premise is moreover UNSATISFIABLE at every delta below one:      *)
(* every generator of this instance is a transposition, so a word of length   *)
(* L evaluates into the coset of the alternating subgroup determined by the   *)
(* parity of L, and the sum of the absolute differences between the cut       *)
(* distribution and group uniform is one. That sign-coset confinement is      *)
(* not formalized at S_5, and no theorem of this repository asserts it        *)
(* there.                                                                     *)
```

The claim survives the rewrite: a law confined to one coset of an index-two
subgroup is at distance one from group uniform in that sum, which is what the
sentence asserts.

### N7. Probe residue: clean apart from B1

Greps over the five files for `probe`, `SRC`, `STATUS`, `audit`, `form 1`,
`form 2`, `round`, `S[0-9]`, `L[0-9]+[a-z]?` as ledger identifiers, `2026` and
`spec` return nothing except the `kim_landing_probe` import path of B1 and the
pre-existing `L1` of N6. No date, no ledger identifier and no audit-round
vocabulary travelled.

`proved` occurs four times in new text (`pgg_analysis_manifest.v:408`,
`five_card_rows.v:46, 418, 710`). Three of the four describe what a theorem
says rather than its status, and the manifest's is proof provenance in a level
justification, which the manifest already does for S_5 ("Both bounds descend
from the in-kernel Rayleigh certificate of `s5_mixing.v`"). The fourth is S6.
`landed` at `five_card_analysis.v:386` is the facade's own pre-existing
vocabulary in that docstring and in the facade contract at lines 23-24.

### N8. Section names

`var_dist_supp_inj`, `kim_cut_supports`, `five_card_colour_census`,
`five_card_cut_mixing`. All lowercase snake, MathComp style, none equal to a
lemma name, none colliding with anything in the tree.
`Section five_card_cut_mixing` is a strict prefix of
`five_card_cut_mixing_of_supp_pow` declared inside it, which is legal and
reads correctly. `Section five_card_colour_census` holds both
`den_boer_layout_law_const` and `five_card_static_obs_const`; the second is
about a coalition's reading rather than the census, but the census is the
mechanism of both and the section variable `R` is what they share, so the name
is acceptable.

### N9. Header indices against their files

`var_dist_supp.v`: `Lemmas:` lists exactly the five lemmas in the file, all
present, none missing. Matches `lib/perm_exchange.v`'s exhaustive `Lemmas:`
block.

`five_card_mixing.v`: three `Definitions:` entries and ten `Key results:`
entries, every one present in the file. Eight further lemmas are unindexed
(`fc_sigma_pow5_eq1`, `fc_sigma_pow_ord_inj`, `fc_kim_word_eval_powE`,
`five_card_ideal_supp_pow`, `kim_single_cut_supp_pow`,
`kim_centi_cut_supp_pow`, `fc_arrange_countE`, `kim_one_cut_centi_le`), which
matches the selective convention of `pgl27_mixing.v` and `five_card_kim.v`.
Every index gloss I could check against the statement is true, including the
"three hearts and two clubs" census (`fc_arrange_countE` gives three `true` and
two `false`, and `false` is the club colour per `five_card_decode_ord0`).

`five_card_rows.v`: the title line "three rows, as seven programs" is true
(uniform, repeated sampled, biased sampled, repeated spectral, biased
certified, repeated39, biased inv25). Every name in the index is present in the
file. Six worth adding are listed at S3.

`five_card_analysis.v`: the three new contract-table lines (60-62) name
`centi_cut_mixing`, `biased_cut_mixing` and `static_obs_const`, all three
present at 372, 377 and 383.

### N10. The facade alias convention holds

`kim_centi_cut_mixing -> centi_cut_mixing`, `kim_biased_cut_mixing ->
biased_cut_mixing`, `five_card_static_obs_const -> static_obs_const` all strip
the instance prefix exactly as the facade contract requires at lines 27-28, and
as `kim_centi_cut_distE -> centi_cut_distE`, `kim_biased_family ->
biased_family` and PGL(2,7)'s `pgl27_word_mixing -> word_mixing` do.

The status trio is readable given the docstrings. `exec_transfer_status` keeps
a name that says which execution stage rather than which cut law, because
`manifest/pgg_analysis_client.v:48` checks it; its docstring at 385 now says
"the uniform exact-cut path" and the section-7 block at 364-365 lists the three
paths in the same three words the three docstrings use. Nothing further is
needed.

### N11. Statement comments: what checked out

The domain frame is stated correctly wherever I could check it against the
type. `SpectralPropAt cert c` is, verbatim, a bound of `c` on the variation
distance between the two pushforwards of `static_coalition_obs C x` and
`static_coalition_obs C x'` along the row's own `sa_cut_dist`, quantified over
`#|C| < profile_k`; the rows-file header at 31-43 describes exactly that, names
the ideal, says explicitly that it is not independence from the secret, that it
is conditional on fewer than two seats, and that it says nothing about the full
reveal. `kim_centi_cert`'s "five fields" match `SpectralCert`'s `sc_b`,
`sc_Hd`, `sc_ideal`, `sc_close`, `sc_const` one for one. The prices are
labelled: the spectral number is the only inexact quantity and the constancy
field is stated as exact, in the mixing file, the rows file and the facade.
The arithmetic in the four number lemmas is right (`sqrt 5 / 40 ≈ 0.056`,
about three percent of 2; `1/50 < sqrt 5 / 80`; `2·sqrt 5·(1/80)^7 ≈ 2.1e-13 <
2^-39 ≈ 1.8e-12`).

### N12. Two things the owner may want to decide, which this audit does not block

`kim_biased_exact_le_eps` (`five_card_rows.v:522`) has no consumer in the five
files and is not in the index. Under the tree's "keep only claimed or premise"
rule it stays only if the paper claims it or later work needs it.

`kim_biased_marginal_bound_exact` and `kim_biased_cert_exact` name the property
of the number, while `kim_centi_marginal_bound40`, `kim_centi_cert40`,
`five_card_reprice39` and `five_card_reprice_inv25` name the value. The split
was settled in SRC's five audits and the new context does not break it, so it
is left alone here.

### N13. The recorded failures

`five_card_row_repeated_spectral_uniform_rowE` and
`five_card_row_repeated39_bare` are each named after what is attempted, neither
marks the attempt as wrong, and the second mirrors `pgl27_row_word39_bare`
exactly. Both follow the rule.
