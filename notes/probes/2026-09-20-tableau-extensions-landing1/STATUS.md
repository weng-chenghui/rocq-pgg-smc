# Landing 1 of the Tableau extensions — staged text

Date: 2026-09-20. Branch `feat/tableau-extensions-probe`. The staged text was
first committed at `16066cd`; everything below is the text after fix pass 1,
whose per-finding record is the last section of this file.

This directory holds the STAGED TEXT of landing 1 of
`notes/2026-09-20-000000-tableau-extensions-landing-design.md`. Nothing under
`manifest/`, `instances/`, `lib/` or `_CoqProject` of the repository was
touched. The main session does the `cp` into production after the audits.

Every staged file compiles, the fidelity file compiles, and every assumption
is the classical trio except the three S5 declarations, which carry the
production `Axiom rigidity_s5_instance.s5_group_order_eq` they carried before.

## Layout

| Staged path | Source |
|---|---|
| `staged/manifest/pgg_tableau.v` | probe `pgg_tableau.v` |
| `staged/manifest/pgg_tableau_syntax.v` | probe `pgg_tableau_syntax.v` |
| `staged/instances/pgl27/pgl27_rows.v` | probe `pgl27_rows.v`, plus two definitions of probe `t0_sampled_branch_pgl27.v` |
| `staged/instances/kim2025/five_card_rows.v` | probe `five_card_rows.v` |
| `staged/instances/s5/s5_rows.v` | probe `s5_rows.v` |
| `staged/instances/psl211/psl211_rows.v` | probe `psl211_rows.v` |
| `staged/instances/psl211/psl211_reading_constancy.v` | PRODUCTION `instances/psl211/psl211_reading_constancy.v`, comments only |

The probe is `notes/probes/2026-09-19-tableau-extensions/`.

`_CoqProject` records the flags and the compile order. `compile.py` reads the
flags out of `_CoqProject` so the two cannot drift, and drives every
`rocq compile` through the machine-wide `rocq1` lock, one process at a time.
`verify.py` prints the code-token and comment-word diffs of every staged file
against its source. `landing_fidelity.out` is the captured output of the
fidelity run.

### The load-path order, measured twice

Rocq 9.0.0 resolves a `Require` to the LAST matching `-R`/`-Q` entry. Two
orders were run and only one works.

| Order | Outcome |
|---|---|
| staged `-R` lines before production's | production `pgg_tableau.vo` loads |
| staged `-R` lines after production's but before `-Q . tableau_ext_landing1` | `-Q .` rebinds `staged/manifest` to `tableau_ext_landing1.staged.manifest`, so production `pgg_tableau.vo` loads again. Measured: `staged/manifest/pgg_tableau_syntax.v", line 396: Error: The reference certify_idealproximity was not found in the current environment` |
| staged `-R` lines last, after `-Q .` | the staged framework loads, every file compiles |

The successful load is itself the provenance witness, and no separate probe is
needed for it: `certify_idealproximity` exists in the staged `pgg_tableau.v`
and in no production file, so a run that resolves it resolved `pgg_tableau` to
the staged copy. This is the same trap the Kim landing recorded
(`notes/probes/2026-09-19-kim-spectral-landing/STATUS.md:946`), one step
further: there the competing entry was a scratch directory, here it is the
landing directory's own `-Q .`.

---

## E1 — the `Require` rewrite

`From tableau_ext_probe Require` becomes `From pgg_smc Require`. Nothing else
on any of those lines moved.

| Staged file | Rewrites | Residual `tableau_ext_probe` |
|---|---|---|
| `manifest/pgg_tableau.v` | 0 | 0 |
| `manifest/pgg_tableau_syntax.v` | 1 | 0 |
| `instances/pgl27/pgl27_rows.v` | 2 | 0 |
| `instances/kim2025/five_card_rows.v` | 2 | 0 |
| `instances/s5/s5_rows.v` | 2 | 0 |
| `instances/psl211/psl211_rows.v` | 1 | 0 |

Before, in `instances/pgl27/pgl27_rows.v`:

```
From tableau_ext_probe Require Import pgg_tableau.
From tableau_ext_probe Require Import pgg_tableau_syntax.
```

After:

```
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
```

---

## E2 — the D3 withdrawal, in `five_card_rows.v`

Two declarations and two index blocks removed. Nothing else in the staged
tree names them: a `grep -rn kim_centi_cert40` over `staged/` returns nothing,
and over production it returns only `instances/kim2025/five_card_rows.v`,
which this staged copy replaces. The two declarations of
`instances/kim2025/five_card_mixing.v` that fed it,
`kim_centi_marginal_bound40` and `kim_centi_cut_mixing40`, are landing 2's
removal and are untouched here.

**Removed declarations** (probe `five_card_rows.v:746-766`, with their
comments):

```
(** A certificate over the repeated row's model with the constant in the
    marginal-bound field. The ideal cut, the identification equation and the
    constancy of the reading at every coalition of at most one seat are the
    same terms as in kim_centi_cert; the marginal bound carries two to the
    minus fortieth in place of the spectral expression, and the mixing field
    is the same distance bounded by that constant. *)
Definition kim_centi_cert40 (R : realType) (idx : unit)
  : IndistinguishabilityCert (amf_sample kim_centi_family R idx) :=
  @MkIndistinguishabilityCert R five_card_algebra five_card_params
    (amf_sample kim_centi_family R idx)
    (kim_centi_marginal_bound40 R)
    (esym (kim_centi_cut_distE R))
    (sa_cut_dist (five_card_sample R))
    (@kim_centi_cut_mixing40 R)
    (@five_card_static_obs_const R).

(** The certificate's own bound is then two copies of two to the minus
    fortieth, by conversion and with no arithmetic. *)
Lemma kim_centi_cert40_epsE (R : realType) (idx : unit) :
  cert_eps (kim_centi_cert40 R idx) = 2%:R ^- 40 + 2%:R ^- 40 :> R.
Proof. by []. Qed.
```

**Index block, before** (probe `:98-100`):

```
(*   kim_centi_cert40, kim_biased_cert_exact                                  *)
(*                           == the same two with a constant in the           *)
(*                              marginal-bound field                          *)
```

**After.** `kim_biased_cert_exact` survives (staged `:832`), so the entry is
kept and reworded, because "the same two" had lost one of its two. Fix pass 1
reworded it again, to the words the declaration's own comment carries
(soundness S9):

```
(*   kim_biased_cert_exact   == the one-cut certificate at the exact number   *)
(*                              one fiftieth                                  *)
```

**Index block, before** (probe `:154-155`), removed whole:

```
(*   kim_centi_cert40_epsE   == the number the constant repeated certificate  *)
(*                              publishes                                     *)
```

That entry is the only sentence in the file speaking of "the constant repeated
certificate", so removing it leaves no sentence to adjust. The section banner
above the removed block, "The same two rows at the constants they publish",
stays true: the section still holds the repeated row at `2^-39` and the
one-cut row at one twenty-fifth.

**The published number is unchanged.** `five_card_row_repeated39` still
publishes `2%:R ^- 39`, on the route
`Order.POrderTheory.ltW (kim_centi_cert_eps_lt R idx)` that the probe had
already put there, and `landing_five_card_reprice39` in the fidelity file
restates it.

**The `Fail` guards.** No `Fail` in the staged tree has either withdrawn name
as its subject or in its body, so no guard changed its reason. The two guards
the fidelity file writes for the withdrawal were confirmed with an un-`Fail`ed
copy in the scratchpad, never in the repository:

| Guard | Message with the `Fail` removed |
|---|---|
| `Fail Check kim_centi_cert40.` | `Error: The reference kim_centi_cert40 was not found in the current environment.` |
| `Fail Check kim_centi_cert40_epsE.` | `Error: The reference kim_centi_cert40_epsE was not found in the current environment.` |
| `Fail Check RepricePayload.` | `Error: The reference RepricePayload was not found in the current environment.` |
| `Fail Check port_reprice.` | `Error: The reference port_reprice was not found in the current environment.` |

---

## E3 — R1, the word branch point into `pgl27_rows.v`

**What moves.** Exactly two definitions of probe
`t0_sampled_branch_pgl27.v`, byte-identical, checked by string containment:
`pgl27_word_sampled` (t0 `:135-136`) and `pgl27_row_word_branch39`
(t0 `:148-153`).

**What does not, and why.** The design's R1 decision adds "the lemmas of
`t0_sampled_branch_pgl27.v` that the landing rows are stated against". A
name-by-name count of every t0 declaration against the three landing-3
sources shows there is no such lemma:

| t0 declaration | uses in `p5_pgl27_word_proximity.v` | in `p5_mutations.v` | in `p5_pgl27_prior_ideal.v` |
|---|---|---|---|
| `pgl27_word_sampled` | 6 | 0 | 0 |
| `pgl27_row_word_branch39` | 7 | 0 | 0 |
| `pgl27_exact_sampled` | 0 | 2 | 0 |
| `pgl27_row_word_branch` | 0 | 0 | 0 |
| `pgl27_row_exact_branch`, `pgl27_row_exact_branch_ideal` | 0 | 0 | 0 |
| `pgl27_row_exact_branch_atE`, `_ideal_atE`, `_rowE` | 0 | 0 | 0 |
| `pgl27_row_word_branch_atE`, `pgl27_row_word_branch39_atE`, `pgl27_row_word_branch_armE` | 0 | 0 | 0 |

`pgl27_exact_sampled`'s two uses are in `p5_mutations.v`, which lands in
landing 3 and can carry its own copy or its own route; it is not a landing-1
question and was not moved.

**Placement.** A new section after "The word row concluded at 2^-39" and
before "A number below the proved one". It has to be after
`pgl27_reprice39` (staged `:415`), which types `pgl27_row_word_branch39`, and
after `pgl27_dealt` (`:135`) and `pgl27_word_cert` (`:261`).

**Cost.** The two moved sentences, from `-time` on the staged file:

```
Definition~pgl27_word_sampled~...     0.000 s  [chars 27966-28056]
Definition~pgl27_row_word_bran...     0.001 s  [chars 28287-28557]
```

No row-against-row data equation was added, which is the 48-to-96 s hazard the
brief names. The file's whole compile went from 6.3 s (the Kim landing's
measurement of production's text) to 6.5 s.

**Index entries added** (staged `:57-60`, after `pgl27_row_word39_bind`):

```
(*   pgl27_word_sampled      == the word model named at Sampled, before any   *)
(*                              arm is chosen                                 *)
(*   pgl27_row_word_branch39 == the continuation of that name concluded at    *)
(*                              2^-39                                         *)
```

### The two moved comments, after Q1's ruling

The coordinator ruled on Q1 that `pgl27_row_word_branch` and the lemmas of
`t0_sampled_branch_pgl27.v` stay in the probe, and that the comment of
`pgl27_row_word_branch39` is rewritten so that it names no referent outside
the staged file. The code is unchanged: the code-token diff of
`pgl27_rows.v` is the same 3 hunks and 47 changed lines it was before the
rewrite. Fix pass 2 adds the branch row's arm equation inside that same E3
hunk, carrying it to 79 changed lines.

**`pgl27_row_word_branch39`, before** (probe `t0_sampled_branch_pgl27.v:145-147`,
moved verbatim in the first pass):

```
(** The second continuation, concluded at 2^-39 before it is published. The
    terminal sits between the branch point and the manifest row, so this pair
    exercises the reduction through the name across a terminal as well. *)
```

**After** (the text of fix pass 1; the first pass's wording and the reason it
was replaced are under "Fix pass 1", naming M7):

```
(** The word row built from the named value pgl27_word_sampled rather than
    from the dealt prefix: the same certificate, the same terminal at 2^-39
    and the same two statuses as pgl27_row_word39. Naming the Sampled value
    is what lets a further row over this model be written without repeating
    the prefix. *)
```

Each clause read off the two declarations, at the staged file's own lines:

| Clause | Read from |
|---|---|
| built from the named value `pgl27_word_sampled` rather than from the dealt prefix | the definition's first line, staged `:492`, against `pgl27_row_word39`'s `pgl27_dealt sample pgl27_word_family` at `:425-426` |
| the same certificate | `certify InputIndistinguishability pgl27_word_cert` at `:493` and at `:427` |
| the same terminal at 2^-39 | `\|> conclude pgl27_reprice39 by (fun R _ => ssr_ext.eqW (pow2_split R))` at `:494` and at `:428`, with `pgl27_reprice39 : Reprice := fun R => Some (2%:R^-39 : R)` at `:415` |
| the same two statuses | `\|> publish IdealFinite BaselineClassicalOnly` at `:495` and at `:429` |
| naming the Sampled value lets a further row be written without repeating the prefix | a statement about the surface, not an equation; no equation with `pgl27_row_word39` is claimed here, because no lemma of the staged file states one |

The arithmetic the first pass put in this comment is stated once in the file,
in the plain comment above `pgl27_row_word39` (`:419-421`).

The words "second", "this pair" and "exercises" do not occur in the section:
a scan of the block between the two banners returns nothing.

**`pgl27_word_sampled`, checked and unchanged.** Its moved comment is

```
(** The word model of PGL(2,7), named at Sampled. Its family is indexed by a
    distribution on the booleans, so a continuation here unifies a payload
    whose type mentions both the real field and that index. *)
```

Every phrase is about the declaration itself or about any continuation of it.
"A continuation here" quantifies and does not refer, so there is no referent
outside the staged file and no edit is owed.

---

## E4 — R15, the header sentence on what a certificate says

The probe's `pgg_tableau.v` already carries every other header change of
landing 1: "There are six statements", the three-arm paragraph naming
`certify_idealproximity` and `security_arm_of`, "those laws" for the three
composition laws, the `conclude` paragraph with "moves the real an arm's
proposition mentions to any upper bound of it", and a `Definitions:` block
holding `IdealProximityCert`, `SecurityArm`, `port_arm`,
`certify_idealproximity` and `conclude`'s rewritten entry. A scan of both
staged framework files for the word "two" found no stale count: the only
surviving occurrences are "the two bottom levels", "the two marginals", "the
two run arguments" and "the propositions of the two arms that carry a number",
and that last one is true, because the exact arm carries no number. A word
scan cannot see a count carried by an enumeration or by "both", and the
naming audit found two of those, which fix pass 1 corrected: `publish_armE`
named two of the three `certify_*_armE` lemmas (naming M3), and
`psl211_reading_constancy.v:236` called a premise the premise of "both"
security arms (naming M4).

So E4 is one new paragraph, inserted between the arms paragraph and the
composition-laws paragraph:

```
(* The exact arm's and the proximity arm's propositions mention terms an      *)
(* instance chooses, so a row of either says as much as those terms say.      *)
(* ExactProp mentions the witness's ew_secret, and a constant ew_secret       *)
(* satisfies ew_indep at every coalition. IdealProximityPropAt mentions       *)
(* the certificate's ipc_secret and the two marginals of its ipc_ideal, and   *)
(* at an ipc_ideal that is the row's own adapter, with ipc_secret that        *)
(* adapter's witness's own secret, ipc_close compares one distribution with   *)
(* itself and holds at the number zero. The input-indistinguishability arm    *)
(* is different in kind: IndistinguishabilityPropAt mentions neither          *)
(* ic_ideal nor a secret, only the readings of the model's own cut law at     *)
(* two run arguments and the number bounding their distance, so ic_ideal      *)
(* is a means of proving it. ic_close holds ic_ideal within the marginal      *)
(* bound's epsilon of that bound's own law and ic_const asks a coalition      *)
(* below the threshold to read it the same at every two run arguments, and    *)
(* at some models no law satisfies both below a positive number.              *)
```

That is the text of fix pass 1. The first pass's paragraph, which read the
type of `ic_ideal` and not the record, is quoted under "Fix pass 1" with the
soundness finding that refuted it.

The paragraph's first draft closed with a sentence citing
`psl211_word_proximity_cert_secretE` and `psl211_word_proximity_cert_secretTE`,
which the design's R15 asks the header to name. The coordinator ruled on Q2
that a header states what the framework says and not where an instance
exhibits it, so that sentence was removed and the paragraph now stands on the
three records alone. The removed text was:

```
psl211_word_proximity_cert_secretE and psl211_word_proximity_cert_secretTE
are where one instance pins both fields against its own chirality bit.
```

Every other clause is unchanged and each stays true without it, because none
of them referred to that sentence. The clause-by-clause table below is the
whole paragraph as it now stands.

Each clause read off the three records and the three propositions of the
staged file, at that file's own lines:

| Clause | Read from |
|---|---|
| `ExactProp` mentions the witness's `ew_secret` | `ExactProp` (`:425-445`) states independence of the view from `ew_secret w`, zero mutual information with it, the conditional entropy equation and the closure under post-processing |
| a constant `ew_secret` satisfies `ew_indep` at every coalition | `ew_secret : {RV (sa_sampleP sa) -> ew_secretT}` (`:172`) and `ew_indep` (`:173-176`), an independence statement quantified over coalitions below the threshold. The soundness auditor compiled the general fact that a constant random variable is independent of any other |
| `IdealProximityPropAt` mentions the certificate's `ipc_secret` and the two marginals of its `ipc_ideal` | `IdealProximityPropAt` (`:487-500`): the left `fdistmap` pairs the view with `ipc_secret cert`, the right side is `` `x `` of the ideal's view marginal and `fdistmap (ew_secret (ipc_witness cert))` |
| at an `ipc_ideal` that is the row's own adapter, with `ipc_secret` that adapter's witness's own secret, `ipc_close` compares one distribution with itself and holds at the number zero | `ipc_close`, `:219-229`: with `ipc_ideal := sa` and `ipc_secret := ew_secret ipc_witness` the two `fdistmap` arguments and the two distributions are the same terms, so `var_dist d d = 0 <= 0`. `ipc_ideal : SampleAdapter R (instance_exec E)` is `:215`, `ipc_witness : ExactWitness ipc_ideal` `:216`, `ipc_secret` `:217` |
| `IndistinguishabilityPropAt` mentions neither `ic_ideal` nor a secret, only the readings of the model's own cut law at two run arguments and the number bounding their distance | `IndistinguishabilityPropAt` (`:453-461`): its body is `var_dist (fdistmap (static_coalition_obs C x) (sa_cut_dist sa)) (fdistmap (static_coalition_obs C x') (sa_cut_dist sa)) <= c`. The certificate is a parameter the body does not use |
| `ic_close` holds `ic_ideal` within the marginal bound's epsilon of that bound's own law | `ic_close : var_dist (sw_rho_dist ic_b) ic_ideal <= sw_bound_eps ic_b`, `:192` |
| `ic_const` asks a coalition below the threshold to read it the same at every two run arguments | `ic_const`, `:193-197` |
| at some models no law satisfies both below a positive number | `psl211_alldecks_no_small_eps_cert` (`psl211_reading_constancy.v:703`), whose hypothesis is `sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert) < (#\|pgg_G psl211_M\|%:R)^-1 -> False`: at that one model no certificate, and so no `ic_ideal` satisfying `ic_close` and `ic_const`, exists below `1/660`. The claim is existential in the model, because at other models a law satisfying both does exist. The header states the fact and names no instance, which is what production's own header does at every other paragraph |

The paragraph does not claim that the proximity arm is vacuous, and does not
claim that any certificate is. It says which terms each arm's proposition
mentions, and that the input-indistinguishability arm's mentions neither an
ideal nor a secret.

Q2's ruling removed the citation of two landing-4 names, and fix pass 1
replaced the freedom claim; each clause of the table above is read off a
record or a proposition of the staged `pgg_tableau.v`, except the last, which
cites the staged `psl211_reading_constancy.v`.

---

## E5 — the sentences the `<=` obligation makes false

### The four rows files

Nothing to do. The design's section 4 lists thirteen production lines that the
`<=` obligation makes false or stale. A scan of all four staged files for
`republish`, `reprice obligation`, `one identity per real field` and
`exactly what the row above` returns nothing, so the probe's copies carry none
of them. The staged `pgl27_rows.v` payload is
`(fun R _ => ssr_ext.eqW (pow2_split R))` (`:423`) and the staged
`five_card_rows.v` payload is
`(fun R idx => Order.POrderTheory.ltW (kim_centi_cert_eps_lt R idx))`
(`:758`), which are the two landing-order items for those files.

### `instances/psl211/psl211_reading_constancy.v`

Started from PRODUCTION's text, not from a probe copy. Its code tokens are
identical to production's: `verify.py` reports 0 code-token hunks. Two comment
edits from the section-4 table, both for landing 1, and a third at `:236` that
fix pass 1 adds (naming M4: "premise every security arm states" for "premise
of both security arms", a two-arm count in a three-arm framework). The two
sentences
that become false only at landing 4 (`:67-69` and `:768-771`, the
"no weighted-word SampleAdapter exists in this tree" clause) are left alone,
and `:31-38`, `:14-15`, `:202`, `:208`, `:560`, `:674`, `:706` and `:725` were
read and need no landing-1 change.

**Edit 1** (`:689`), the R13 rename reaching this file.

Before: `odflt (cert_eps cert) (c R) at its own reprice coordinate c, and cert_eps`

After, as fix pass 1 leaves it (naming S7): `odflt (cert_eps cert) (c R)
at its own coordinate c, and cert_eps`

**Edit 2** (`:697-699` after fix pass 1), the hypothetical that landing 1
performs.

Before:

```
(* Argued and not compiled: the proposition a row carries is
   IndistinguishabilityPropAt cert c, a variation distance bounded above by c,
   so an obligation weakened from an equality to cert_eps cert <= odflt
   (cert_eps cert) (c R) could only let a row publish a number no smaller than
   cert_eps. *)
```

After, as fix pass 1 leaves it (soundness S5, naming S8):

```
(* The obligation of conclude at an input-indistinguishability port is
   cert_eps cert <= odflt (cert_eps cert) (c R), and the proposition the row
   carries is IndistinguishabilityPropAt cert (odflt (cert_eps cert) (c R)). *)
```

The first pass wrote `IndistinguishabilityPropAt cert c`, which does not
typecheck, because `c` is the coordinate and the proposition takes a real;
and it closed with a sentence the docstring three lines above already says.

The inequality written there is the `InputIndistinguishability` branch of the
staged `ConcludePayload` (`pgg_tableau.v:842-843`), copied from it. The
following comment block, "The excluded range of epsilon is bounded above. The
header records why the larger range is occupied and that the occupancy is
argued and not compiled", is about a different argued step and is unchanged.

---

## Verification

### 1. Code tokens

`python3 verify.py`. Comments stripped, whitespace normalized, the rest
tokenized, unified diff against the source.

| Staged file | Source | Code-token hunks | Every hunk |
|---|---|---|---|
| `manifest/pgg_tableau.v` | probe | 0 | — |
| `manifest/pgg_tableau_syntax.v` | probe | 1 | E1 |
| `instances/pgl27/pgl27_rows.v` | probe | 3 | E1, E1, E3 insertion, with fix pass 2's `pgl27_row_word_branch39_armE` inside the E3 hunk |
| `instances/kim2025/five_card_rows.v` | probe | 6 | E1, E1, E2 removal, and the three insertions of the four arm equations of fix pass 1 |
| `instances/s5/s5_rows.v` | probe | 2 | E1, E1 |
| `instances/psl211/psl211_rows.v` | probe | 1 | E1 |
| `instances/psl211/psl211_reading_constancy.v` | PRODUCTION | 0 | — |

The E3 hunk is an insertion only, of the 43 tokens of the two moved
definitions, and the moved text is byte-identical to `t0_sampled_branch_pgl27.v`
(both blocks occur exactly once in each file). The E2 hunk is a deletion only,
of the 108 tokens of the two withdrawn declarations. The three further hunks
in `five_card_rows.v` are insertions only, of the four `_armE` lemmas fix
pass 1 adds, and they are the only code that pass writes.
`pgl27_row_word_branch39_armE` is the only code fix pass 2 writes.

### 2. Comment words

| Staged file | Comment-word hunks | Classification |
|---|---|---|
| `manifest/pgg_tableau.v` | 14 | E4's paragraph as fix pass 1 rewrote it, and the seven further comment edits of fix pass 1 (naming M3, M5 at four sites, naming S5 at three sites) |
| `manifest/pgg_tableau_syntax.v` | 1 | fix pass 1's naming S11 and fix pass 2's F3, which fall in one hunk |
| `instances/pgl27/pgl27_rows.v` | 9 | E3 index entries; E3 moved section banner and the moved `pgl27_word_sampled` comment; the `pgl27_row_word_branch39` and `pgl27_row_word39` comments as fix pass 1 rewrote them (naming M7); the header sentence of naming S4 as fix pass 2 rewrote it (F6); and fix pass 2's index entry and docstring for `pgl27_row_word_branch39_armE` (F10) |
| `instances/kim2025/five_card_rows.v` | 18 | E2: index entry removed, index entry reworded, index entry removed, two declaration comments removed; and fix pass 1's naming M1, M2, M6, S6, S12, S13, soundness S4 and S9, plus the docstrings and index entries of the four new arm equations |
| `instances/s5/s5_rows.v` | 0 | — |
| `instances/psl211/psl211_rows.v` | 0 | — |
| `instances/psl211/psl211_reading_constancy.v` | 4 | E5 edit 1, E5 edit 2, and fix pass 1's naming M4 and the type-honest rewriting of E5 edit 2 (soundness S5, naming S7 and S8) |

No hunk is a meta-narration removal, because the scan below found nothing to
remove. Every hunk is listed against its finding in "Fix pass 1" below.

### 3. Scans

| Scan | Result |
|---|---|
| `SpectralDecay`, `SpectralCert`, `sc_` fields, `_indist\b`, `RepricePayload`, `port_reprice`, `kim_centi_cert40`, `spectral_constancy` | no hit anywhere in `staged/` |
| lines over 80 bytes | three, all in `manifest/pgg_tableau_syntax.v` (`:334`, `:372`, `:402`), all notation string literals, which the brief exempts |
| `apex`, `gate`/`gates`/`gated`/`gating`, `posit`/`posits`/`posited`/`positing`, `L1` | no hit |
| `indistinguishability` abbreviated | no hit; the word is spelled out at every one of its 125 occurrences in the seven files |
| probe, stage, audit, "renamed", "formerly", "landed", "landing" | three hits, all citations of a probe directory, plus the three dated measurements of the notation namespace, discussed below |

The hits, and why each stays:

| Hit | Text | Verdict |
|---|---|---|
| `manifest/pgg_tableau_syntax.v:40,68` | "Measured on 2026-09-14, …" | production already carries the same two sentences at `:36` and `:64` |
| `manifest/pgg_tableau_syntax.v:79` | "measured on 2026-09-19 by binding it" | the G2 keyword measurement the design's section 5 says lands with the file |
| `instances/psl211/psl211_rows.v:74` | cites `notes/probes/2026-09-15-psl211-planb/audit-soundness/audit_alldecks.out` | byte-identical to production `:74` |
| `instances/psl211/psl211_reading_constancy.v:71` | cites `notes/probes/2026-09-19-psl211-sc-const/` | byte-identical to production `:71` |
| `instances/kim2025/five_card_rows.v:814-816` | cites `notes/probes/2026-09-19-tableau-extensions/STATUS.md, section F2` for a 147 s against 0.07 s measurement | kept; see question Q3 |

No sentence anywhere in `staged/` speaks of a stage, an audit, a rename or a
landing. Nothing was removed on those grounds.

---

## Compile

Order as `_CoqProject` lists it. Every `.vo` lands beside its `.v` under
`staged/`; nothing was written into the production tree. One Rocq process at
a time through the `rocq1` lock. No `make`.
`instances/psl211/psl211_endpoints.v` was never compiled: it is loaded as a
`.vo` by digest through `psl211_models` and `psl211_analysis`, which is R3's
recorded state.

Times are the fifth run, after fix pass 2. Every file was recompiled in this
order, because `manifest/pgg_tableau.v` is upstream of all six others.

| File | rc | wall | sentences over 5 s |
|---|---|---|---|
| `staged/manifest/pgg_tableau.v` | 0 | 12.9 s | none |
| `staged/manifest/pgg_tableau_syntax.v` | 0 | 4.3 s | none |
| `staged/instances/pgl27/pgl27_rows.v` | 0 | 6.3 s | none |
| `staged/instances/kim2025/five_card_rows.v` | 0 | 4.5 s | none |
| `staged/instances/s5/s5_rows.v` | 0 | 3.9 s | none |
| `staged/instances/psl211/psl211_reading_constancy.v` | 0 | 22.0 s | two, 6.04 s and 6.07 s, with a third, `by split; vm_compute`, at the 5 s boundary and over it on some runs |
| `staged/instances/psl211/psl211_rows.v` | 0 | 5.5 s | none |
| `landing_fidelity.v` | 0 | 92.1 s | three, 20.86 s, 20.20 s and 20.82 s |

The slow sentences of `psl211_reading_constancy.v` are two
`rewrite -!size_filter; apply …` and one `by split; vm_compute`, which the
Kim landing measured at 6.1, 6.2 and 5.2 s in the same file before this
landing existed. The three slow sentences of the fidelity file are the three
`Print Assumptions` on declarations whose type names
`psl211_alldecks_observed`, at the 20 s the design predicted. None of the
declarations fix pass 1 adds is over 5 s: `five_card_rows.v` and the four
new arm equations report no slow sentence at all, and the fidelity file's
nine added sentences are likewise all under the threshold, so every one of
them closes by `exact: erefl` and none needed `reflexivity`. The one
declaration fix pass 2 adds is under the threshold as well: `-time` reports
`Chars 29042 - 29243 [Lemma~pgl27_row_word_branch39_...] 0. secs`,
`[Proof.] 0. secs`, `[exact~:~erefl~.] 0. secs` and `[Qed.] 0. secs`, so
`exact: erefl` stands and no `reflexivity` fallback was taken.

`psl211_reading_constancy.v` compiled against the staged framework is the
check the brief requires either way: production's text, unchanged in code,
compiles under the `<=` obligation.

---

## Print Assumptions

40 declarations, from `landing_fidelity.out`. The trio is
`constructive_indefinite_description`, `functional_extensionality_dep` and
`propositional_extensionality`.

| Group | Declarations | Assumptions |
|---|---|---|
| framework | `port_conclude`, `idealproximity_tail`, `certify_exact_armE`, `certify_indistinguishability_armE`, `certify_idealproximity_armE`, `conclude_armE`, `publish_armE` | trio |
| PGL(2,7) | `pgl27_row_exact_tableau`, `pgl27_row_word_tableau`, `pgl27_row_word39`, `pgl27_row_word39_bind`, `pgl27_row_word_branch39`, `pgl27_row_exact_rowE`, `pgl27_row_word_rowE`, `pgl27_row_exact_armE`, `pgl27_row_word_armE`, `pgl27_row_word39_armE`, `pgl27_row_word_branch39_armE`, `pgl27_row_word39_bindE` | trio |
| five-card | `five_card_row_uniform_tableau`, `five_card_row_repeated_indistinguishability_tableau`, `five_card_row_biased_indistinguishability_tableau`, `five_card_row_repeated39`, `five_card_row_biased_inv25`, `five_card_row_uniform_rowE`, `five_card_row_uniform_armE`, `five_card_row_repeated_indistinguishability_rowE`, `five_card_row_biased_indistinguishability_rowE`, `five_card_row_biased_forms_publishedE`, `five_card_row_repeated39_atE`, `five_card_row_repeated_indistinguishability_armE`, `five_card_row_biased_indistinguishability_armE`, `five_card_row_repeated39_armE`, `five_card_row_biased_inv25_armE` | trio |
| S5 | `s5_row_rand_tableau`, `s5_row_rand_rowE`, `s5_row_rand_armE` | trio **and** `rigidity_s5_instance.s5_group_order_eq` |
| PSL(2,11) | `psl211_row_alldecks_tableau`, `psl211_row_alldecks_rowE`, `psl211_row_alldecks_armE` | trio |

`rigidity_s5_instance.s5_group_order_eq` is production's own axiom and is the
documented exception. No other axiom appears anywhere in the run, and no
declaration is closed under the global context, because every one of them
passes through `boolp`.

---

## `landing_fidelity.v`

Logical path `tableau_ext_landing1`. It `Require`s the staged copies through
`pgg_smc`, which the flags resolve to `staged/`. Nothing in it is a new
mathematical claim: every restatement is closed by the staged declaration it
restates, or by conversion where the staged declaration is a definition and
the restatement is its unfolding. Proof scripts are `exact: <name>` and
`exact: erefl`; no `by []` and no `done` appears on a `published_at` or
`published_row` equation.

What it checks:

| Section | Checks |
|---|---|
| the proximity certificate | all five fields of `IdealProximityCert`, including `ipc_close` restated in full, so a change to any field's type is a compile error; and `IdealProximityPropAt` restated by unfolding, whose right side is the product of the ideal's two marginals where `ipc_close`'s is a joint law |
| the arm reader | `port_arm` at all three constructors; `security_arm_of` as `ab_arm` of the published data; the five general `_armE` lemmas restated; `view_proximity_of` against `view_indistinguishability_of` |
| the terminal | `ConcludePayload` restated by unfolding, which is where the `<=` lives; `port_conclude`'s statement; `Fail Check` on the two retired names |
| the per-program arm pins | all ten that exist in the four staged rows files |
| the manifest rows | the seven `_rowE` equations and one of the three `_publishedE` equations, plus `five_card_row_repeated39_atE`. The two `_publishedE` equations left out are `five_card_row_repeated_indistinguishability_publishedE` and `five_card_row_biased_indistinguishability_publishedE`, which production already carries unchanged, so the landing adds nothing to pin there |
| the published numbers | `five_card_reprice39 R = Some (2%:R ^- 39)`, `pgl27_reprice39 R = Some (2%:R ^- 39)`, `five_card_reprice_inv25 R = Some (1 / 25)` |
| the withdrawal | the two `Fail Check`s, and `five_card_row_repeated39 : PublishedRowAt five_card_reprice39` |
| E3 | `pgl27_word_sampled = (pgl27_dealt sample pgl27_word_family)`, the two types, and the branch row against `pgl27_row_word39` at `published_row`, at `published_at` and at `security_arm_of` |
| assumptions | the 39 `Print Assumptions` above |

Two parse facts worth carrying forward. `{RV _ -> _}` needs
`Local Open Scope proba_scope`, not merely `From infotheo Require Import
proba`. And `x = y sample f` parses as `(x = y) sample f`, so an equation
whose right side is a `sample` statement needs parentheses around it.

---

## Questions and the coordinator's rulings

All seven were ruled on. Q1 and Q2 forced one comment edit each, applied
above and recompiled; Q3 to Q7 stand as recorded for the auditors.

**Q1. The moved comment of `pgl27_row_word_branch39` named a sibling that did
not move. RULED: rewrite the comment.** `pgl27_row_word_branch` and the
lemmas of `t0_sampled_branch_pgl27.v` stay in the probe. The rewritten
comment, its before text and the clause-by-clause reading are in the E3
record above. The comment of `pgl27_word_sampled` was checked for the same
fault and needs no edit: "a continuation here" quantifies and does not refer.
No equation with `pgl27_row_word39` is claimed, because no lemma of the
staged file states one; the fidelity file's
`landing_pgl27_branch39_rowE` states the equation of the two published rows
and is where that claim lives.

**Q2. The R15 header paragraph cited two names that land in landing 4.
RULED: remove the citation.** A header states what the framework says, not
where an instance exhibits it. The removed sentence and the paragraph as it
now stands are in the E4 record above. The paragraph rests on `ipc_ideal`,
`ipc_witness`, `ipc_secret`, `ic_ideal` and `ew_secret` alone, and every
surviving clause is read off one of the three records of the staged
`pgg_tableau.v`.

**Q3. `five_card_rows.v` cites the probe's `STATUS.md` in a source comment.
RULED: keep it.** Pre-existing practice in production; a later comment pass
owns it.
Staged `:814-816`, inside the comment explaining why a conversion closes by
`reflexivity` and not by `exact: erefl`:

> Measured on 2026-09-19; the numbers are in
> notes/probes/2026-09-19-tableau-extensions/STATUS.md, section F2.

It was kept, because the tree already does this twice in text that is
production today: `instances/psl211/psl211_rows.v:74` cites
`notes/probes/2026-09-15-psl211-planb/audit-soundness/audit_alldecks.out` and
`instances/psl211/psl211_reading_constancy.v:71` cites
`notes/probes/2026-09-19-psl211-sc-const/`. If the owner wants permanent files
free of probe citations, these three go together and not one of them alone.

**Q4. `Reprice` keeps its name beside `ConcludePayload` and `port_conclude`.
RULED: nothing to write; the rename is the owner's pending decision.**
R13's decision is that landing 1 lands the probe's text, which renames the
payload and the port law and not the type of the coordinate, and that whether
`Reprice` is renamed is the owner's naming decision. R13 also offered a second
option, "the framework header says in one sentence why the type keeps the
older name". The probe's header does not say it and I did not write it,
because the brief lists exactly one new header sentence. The tree after
landing 1 therefore holds `Reprice`, `pgl27_reprice39`, `pgl27_reprice41`,
`five_card_reprice39` and `five_card_reprice_inv25` beside `ConcludePayload`
and `port_conclude`.

**Q5. E2 forced one index rewording the brief does not list. RULED:
accepted.** The index entry
at probe `:98-100` named two certificates in one entry, and the withdrawal
removes one of them. Keeping the entry unchanged would leave "the same two"
naming one certificate. The reworded entry is under E2 above. Flagged because
the brief's E2 says "remove … the header-table lines naming them", and this
line named one withdrawn declaration and one surviving one.

**Q6. `five_card_rows.v` carried one arm pin where PGL(2,7) carries three.
CLOSED by fix pass 1.** The first pass pinned only
`five_card_row_uniform_armE`, leaving the file's two
input-indistinguishability programs and its two concluded rows with no
`_armE`, so the file that is about that arm stated nothing about it. Both
auditors raised it, and fix pass 1 adds the four lemmas, modelled on
`pgl27_rows.v`'s three: `five_card_row_repeated_indistinguishability_armE`,
`five_card_row_biased_indistinguishability_armE`,
`five_card_row_repeated39_armE` and `five_card_row_biased_inv25_armE`. The
two concluded rows get one each because `pgl27_rows.v` carries
`pgl27_row_word39_armE` for its concluded row; `pgl27_row_word39_bind` and
`pgl27_row_word_branch39` carry none in the rows file, and the branch row's
is stated in `landing_fidelity.v` instead.

**Q7. Landing 2's withdrawal is now the only consumer left. RULED: noted;
landing 2 removes the two declarations.** After this
staged text replaces production's `five_card_rows.v`,
`kim_centi_marginal_bound40` (`five_card_mixing.v:507`) and
`kim_centi_cut_mixing40` (`:517`) have no consumer anywhere in the tree. A
whole-tree `grep` for the four D3 names outside `notes/` returns only those
two definitions and the staged file's own `.glob`. So landing 2's removal is
unblocked, and between landing 1 and landing 2 the tree holds two declarations
nothing uses.

---

## Fix pass 1

Applied against `soundness-audit-landing1.md` and `naming-audit-landing1.md`.
Every replacement in those reports was checked against the declaration before
it was written, and the deviations are recorded per finding. Where the two
reports proposed different texts for one passage, one text was written that
satisfies both. The only code written is item E, the four `_armE` lemmas of
`five_card_rows.v`; every other edit is a comment.

### The header paragraph: soundness S1 with naming S1, S2, S3

The first pass's paragraph said "ic_ideal is any law on the group" and closed
"So the proximity arm adds no freedom the tree did not already carry". The
first clause reads the field's type and not the record, and the staged
`psl211_reading_constancy.v:703` refutes it as a claim about what an instance
may field.

Neither report's replacement was written. The soundness replacement keeps the
sentence in the currency of "latitude" and still parallels the three arms;
the naming replacement keeps "freedom". Both leave standing the reading the
sentence is wrong about, which is that the three arms differ by how much
their ideals are constrained. The text written says instead what each
proposition mentions, which is the falsifiable fact: `ExactProp` mentions
`ew_secret`, `IdealProximityPropAt` mentions `ipc_secret` and the two
marginals of `ipc_ideal`, and `IndistinguishabilityPropAt` mentions neither
an ideal nor a secret, only the readings of the model's own cut law at two
run arguments and the number bounding their distance. That last is read off
the definition (`:453-461`), whose body does not use its `cert` parameter at
all. The paragraph and its clause table are in the E4 record above.

`ic_close` and `ic_const` are named as the two fields that constrain the
means of proof, and no instance is cited, because production's `pgg_tableau.v`
header cites none. Naming S3's "the tree" is gone with the sentence that
carried it. One blank comment line above the paragraph and one below
(soundness S10).

The last clause of that paragraph was corrected once more after the pass, on
the coordinator's reading. It had said

> and at a small enough epsilon no law satisfies both.

which is universal in the model and false: at the five-card instance
`kim_centi_cert` fields an `ic_ideal` satisfying both at the epsilon
`Num.sqrt 5%:R * (1 / 80) ^+ 7`, and wherever the cut law's own reading is
constant in the run argument, `ic_ideal` taken as that law satisfies both at
zero. It now reads

> and at some models no law satisfies both below a positive number.

Checked against `psl211_alldecks_no_small_eps_cert`
(`psl211_reading_constancy.v:703`), whose hypothesis is
`sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert) < (#|pgg_G psl211_M|%:R)^-1
-> False`. What is compiled is one model at which no certificate exists below a
stated positive number, so "at some models" and "below a positive number" are
both read off that statement, and the soundness auditor's "may leave no such
law" carried the same existential reading. Every other sentence of the
paragraph is unchanged.

### `landing_fidelity.v`: soundness S2, S6, S11

| Lemma | Statement | Proof | Deviation |
|---|---|---|---|
| `landing_idealproximity_propE` | `IdealProximityPropAt cert c` unfolded, the right side of the distance being `` `x `` of the ideal's view marginal and its secret marginal | `exact: erefl` | none; the auditor's statement compiled as given |
| `landing_pgl27_branch39_atE` | `published_at pgl27_row_word_branch39 = published_at pgl27_row_word39` | `exact: erefl` | none |
| `landing_pgl27_branch39_armE` | `security_arm_of pgl27_row_word_branch39 R idx = InputIndistinguishabilityArm` | `exact: erefl` | none |
| `landing_view_proximity_of` | `view_proximity_of r = view_indistinguishability_of r` | `exact: erefl` | none |

The existing `landing_pgl27_branch39_rowE` was kept, as soundness S6 asks.
No sentence of the fidelity file is over 5 s, so `exact: erefl` stands
everywhere and `reflexivity` was not needed.

### Item E: the four arm equations of `five_card_rows.v`

| Lemma | Statement | `-time` |
|---|---|---|
| `five_card_row_repeated_indistinguishability_armE` | `security_arm_of five_card_row_repeated_indistinguishability_tableau R idx = InputIndistinguishabilityArm` | under 5 s |
| `five_card_row_biased_indistinguishability_armE` | the same for the one-cut certified program | under 5 s |
| `five_card_row_repeated39_armE` | the same for `five_card_row_repeated39` | under 5 s |
| `five_card_row_biased_inv25_armE` | the same for `five_card_row_biased_inv25` | under 5 s |

All four close by `exact: erefl`, none by `by []` or `done`. The file's whole
compile is 4.6 s against the first pass's 4.5 s and reports no sentence over
5 s, so no `reflexivity` fallback was taken and no per-sentence number is
above the threshold the file records elsewhere. Each is ascribed again in
`landing_fidelity.v` (`landing_five_card_repeated_armE`,
`landing_five_card_biased_armE`, `landing_five_card_repeated39_armE`,
`landing_five_card_biased_inv25_armE`) and each is under `Print Assumptions`,
at the classical trio. Header index entries were added for all four.

### The comment findings, per finding

| Finding | File and declaration | Final text, and the deviation from the proposal |
|---|---|---|
| naming M1, soundness S3 | `five_card_rows.v`, `five_card_pow2_39_split` | "A certificate's cert_eps is its marginal bound's epsilon twice, once for each of the two committed pairs, and this identity puts the constant the repeated row publishes into that same shape, so the certificate's two spectral terms can be compared with it one at a time." Neither proposal verbatim: the soundness text says the identity "splits the constant … into the two halves kim_bound_centi bounds each spectral term by", which names the bounding lemma inside a statement comment, and the naming text names PGL(2,7)'s word row, which is a different file's constant. The text written keeps both true clauses, that `cert_eps` is the marginal bound's epsilon twice and that the identity puts `2^-39` into that shape, and drops the withdrawn certificate the first pass's sentence referred to |
| naming M2 | `five_card_rows.v`, index | two entries in place of one, as R-M2 asks: `five_card_inv50_split == the identity the one-cut row's terminal discharges` and `five_card_pow2_39_split == 2^-39 as a sum of two per-pair bounds` |
| naming M3 | `pgg_tableau.v`, `publish_armE` | "This is the step that carries the three certify statements' arm equations out to a published row, where a paper's table reads them." R-M3 verbatim |
| naming M4 | `psl211_reading_constancy.v:236` | "premise every security arm states". R-M4's first sentence only: the rest of its replacement rewrites two sentences the finding does not fault |
| naming M5 | `pgg_tableau.v`, four sites | The word `restate` is gone from all four. `IndistinguishabilityPropAt`: "so conclude can state a finished row at any number at or above that sum, the constant a paper cites among them, without reproving the arm." `cert_eps`: "It is the number a row carries when its coordinate names none." `IdealProximityPropAt`: "so conclude can state a finished row at any number at or above it, the one a paper cites among them." `PublishedRow`: "what a row whose coordinate names no number publishes." R-M5 was not taken verbatim at three of the four: it writes "the conclude terminal can publish a finished row", and it is `publish` and not `conclude` that publishes; and its `PublishedRow` text says "whose terminal names no number", where the coordinate belongs to `PublishedRowAt` and not to a terminal, which is naming S7's own point |
| naming M6, soundness S4 | `five_card_rows.v`, `five_card_row_repeated39` | The docstring states the row and its position, and adds "kim_centi_cert_eps_lt is strict, so the number the row publishes is strictly above the number the certificate proved and the row asserts about a coalition of at most one seat no more than that certificate did, at the number a reader cites." The payload moves to a plain comment, "The terminal's payload is kim_centi_cert_eps_lt weakened by ltW." R-M6's docstring keeps "what a coalition of at most one seat is shown is what that certificate proved", which is the identity phrasing soundness S4 faults, so the two were merged rather than either taken |
| naming M7 | `pgl27_rows.v`, `pgl27_row_word_branch39` and `pgl27_row_word39` | R-M7 verbatim at the branch row except "a further row" for "a second row", which avoids a count the file does not state; and the arithmetic moved out of `pgl27_row_word39`'s docstring into a plain comment, keeping `pow2_split`, `eqW` and "the terminal's obligation" |
| naming S4 | `pgl27_rows.v:39` | "the word row's conclusion at 2^-39, which moves a number and proves nothing new about a coalition". R-S4 verbatim |
| naming S5 | `pgg_tableau.v`, three sites | "The coordinate that names nothing. Every row that publishes the bound it accumulated carries it."; "The proposition a port carries at a given coordinate"; "computed by the framework from that coordinate". R-S5's first sentence was reworded to avoid using "coordinate" twice in two clauses. The identifiers `Reprice`, `no_reprice` and the four `*_reprice*` constants are untouched, as the brief requires |
| naming S6 | `five_card_rows.v:59` | "instances/s5/s5_rows.v records the other answer for s5_row_word". R-S6 says "the same question answered the other way", which is longer and says the same thing |
| naming S7, S8, soundness S5 | `psl211_reading_constancy.v` | The docstring drops "conclude" from "its own coordinate c", and the plain comment below it becomes "The obligation of conclude at an input-indistinguishability port is cert_eps cert <= odflt (cert_eps cert) (c R), and the proposition the row carries is IndistinguishabilityPropAt cert (odflt (cert_eps cert) (c R))." That is R-S8 with soundness S5's type-honest reading of the second argument, which R-S8 leaves as the untypeable `cert c` |
| naming S12 | `five_card_rows.v:51` | "independence of the direct computation from a secret". R-S12 writes "the direct computation of a coalition's view", which is thirteen characters longer and forces a reflow of the whole paragraph; `pgg_tableau.v` settles on "the direct computation" alone and this file already uses it at its index entry for `five_card_static_obs_indep` |
| naming S10 | `pgg_tableau_syntax.v:391`, the proximity notation | "The proximity rule takes one certificate whole, as the input-indistinguishability rule does, and has no builder." R-S10 verbatim; the reason it has no builder stays at the file header (`:30-33`), which is where it already stood |
| naming S11 | `pgg_tableau_syntax.v:262` | The paragraph break the probe's reflow replaced with two spaces inside a line is restored, so the statement about one object and the statement about thresholds are two blocks again, as in production |
| naming S13 | `five_card_rows.v`, `five_card_inv50_split` | "the identity that equates the sum … with the single constant that row publishes". R-S13 verbatim |
| soundness S7, naming N6 | this file | The E3 and E4 clause tables are renumbered against the staged files and now quote the text as fix pass 1 leaves it; the `landing_fidelity.v` coverage sentence now says seven `_rowE` and one of the three `_publishedE`, and says why the other two are left out |
| soundness S9 | `five_card_rows.v`, index | "kim_biased_cert_exact == the one-cut certificate at the exact number one fiftieth". S9 verbatim |

### Declined

| Finding | Why |
|---|---|
| naming N1, N2, N3, N4, N5, N7, N8, N9, N10 | Recorded by the auditor as notes with no action asked |
| soundness S8 | Superseded: it offers "reprice coordinate" or "coordinate"; the brief's ruling on the pending `Reprice` decision selects the second, which is what naming S7 asks and what was written |
| naming S9 as written | It asks for the two arm equations to be deferred to landing 2. The brief's item E lands them here instead, and four rather than two, so the finding is closed rather than deferred |

---

## Fix pass 2

Applies `audit-landing1-fix1.md`: F1 as a MUST, F2 to F6 as SHOULDs, F9 as a
NOTE, all on comment text, and F10 as the pass's one code change. F7 and F8
ask for no action. Every sentence below was written after opening the
declaration it describes and reading its type. Where the auditor's
replacement is not exactly true or not clear English, the written text and
the deviation are both recorded.

### F1 — the last clause of the header paragraph of `manifest/pgg_tableau.v`

Declarations read: `IndistinguishabilityCert` (staged `pgg_tableau.v:186-197`),
`psl211_alldecks_no_small_eps_cert` (staged `psl211_reading_constancy.v:703`)
and `psl211_alldecks_cert_ideal_close` (`:673`).

The paragraph's tail as it now reads, refilled at 74 columns so that no line
runs into the closing marker and none is left short:

```
(* adapter's witness's own secret, the two sides of ipc_close are one term at *)
(* every coalition below the threshold and the field holds at an ipc_eps of   *)
(* zero. The input-indistinguishability arm is different in kind:             *)
(* IndistinguishabilityPropAt mentions neither ic_ideal nor a secret, only    *)
(* the readings of the model's own cut law at two run arguments and the       *)
(* number bounding their distance, so ic_ideal is a means of proving it.      *)
(* ic_close holds ic_ideal within the marginal bound's epsilon of that        *)
(* bound's own law, ic_Hd identifies that law with the model's own cut law,   *)
(* and ic_const asks a coalition below the threshold to read ic_ideal the     *)
(* same at every two run arguments. At some models these three fields leave   *)
(* no certificate whose marginal bound's epsilon, taken twice, is below a     *)
(* positive number.                                                           *)
```

Each clause against the declaration:

| Clause | Read from |
|---|---|
| `ic_close` holds `ic_ideal` within the marginal bound's epsilon of that bound's own law | `ic_close : var_dist (sw_rho_dist ic_b) ic_ideal <= sw_bound_eps ic_b` |
| `ic_Hd` identifies that law with the model's own cut law | `ic_Hd : sw_rho_dist ic_b = sa_cut_dist sa` |
| `ic_const` asks a coalition below the threshold to read `ic_ideal` the same at every two run arguments | `ic_const : forall C, (#|C| < profile_k (instance_profile A))%N -> forall x x', fdistmap (static_coalition_obs C x) ic_ideal = fdistmap (static_coalition_obs C x') ic_ideal` |
| at some models these three fields leave no certificate whose marginal bound's epsilon, taken twice, is below a positive number | `psl211_alldecks_no_small_eps_cert (R) (cert) : sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert) < (#\|pgg_G psl211_M\|%:R)^-1 -> False`, proved by `psl211_alldecks_constancy_false_close` applied to `psl211_alldecks_cert_ideal_close cert`, itself `etrans (ic_Hd cert) (psl211_alldecks_cut_distE R)` against `ic_close cert`, with `indistinguishability_cert_reading_constancy cert` |

**Deviation from R-F1.** The proposal is the one-word substitution "no
certificate meets both below a positive number". Not taken as written. "Meets
both" still names `ic_close` and `ic_const` only, and the exclusion goes
through `ic_Hd`, which is why the pass gives `ic_Hd` a clause of its own. And
"below a positive number" needs the quantity named, because what the theorem
excludes is `sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert)` under
`(#|pgg_G psl211_M|%:R)^-1`, which the written clause calls the marginal
bound's epsilon taken twice. "Leave no certificate" is the theorem's own
quantifier, over certificates and not over laws.

### F2 — the subject of the verdict on `ipc_close`

Declarations read: `IdealProximityCert` (`pgg_tableau.v:212-229`),
`IdealProximityPropAt` (`:487-506`).

Written: "at an ipc_ideal that is the row's own adapter, with ipc_secret that
adapter's witness's own secret, the two sides of ipc_close are one term at
every coalition below the threshold and the field holds at an ipc_eps of
zero."

Checked: with `ipc_ideal := sa` and `ipc_secret := ew_secret ipc_witness`, the
two `fdistmap` arguments of `ipc_close` are the same function and both are
taken against `sa_sampleP sa`, at every `C`, since `C` occurs identically on
the two sides. `var_dist X X <= 0` holds, so the field is inhabited at
`ipc_eps = 0`. Nothing is claimed here about `IdealProximityPropAt`, whose
right side is a product of two marginals and not a joint law, which is what
`landing_idealproximity_propE` records.

**Deviation from R-F2.** "holds at zero" is written "holds at an ipc_eps of
zero", because the number is the record's own field and the bare form reads
as a claim about the arm's proposition, which is the reading F2 faults.

### F3 — the two surfaces of `manifest/pgg_tableau_syntax.v`

Written above the proximity notation:

```
(* The proximity rule takes its certificate whole and has no builder. The
   input-indistinguishability rule has both that form, above, and the
   five-clause builder mk_indistinguishability below. *)
```

Checked against the three notations around it: the whole-certificate form of
the input-indistinguishability rule at `:388-390`, the proximity rule at
`:394-396`, and the five-clause builder at `:402-408`, whose body is
`certify_indistinguishability of (mk_indistinguishability ...)`.

**Deviation from R-F3.** The proposal's single sentence is split in two and
the builder is named `mk_indistinguishability`, the name the file's header
uses at `:22`, so that "the five-clause builder below" points at a
declaration and not at a position.

### F4 — the referent of "at or above it"

Written, in the docstring of `IdealProximityPropAt`: "The bound is a
parameter, as it is for the input-indistinguishability arm, so conclude can
state a finished row at any number at or above the certificate's ipc_eps, the
one a paper cites among them."

Checked: `ConcludePayload`'s branch, `IdealProximity cert => ipc_eps cert <=
odflt (ipc_eps cert) (c R)` (`:863`), and `port_conclude`'s matching branch
(`:863` and `:858-866`).

**Deviation from R-F4.** The proposal writes the bare field name `ipc_eps`.
The field is applied to the certificate everywhere it occurs, so the written
text says "the certificate's ipc_eps".

### F5 — the dangling "that coordinate" above `restate`

Written:

```
(* The terminal handing a row over as a proposition its caller writes out.
   conclude is not an instance of it: conclude's target is BridgedProp of the
   Reprice it is given, where this terminal's target Q is a parameter. *)
```

Declarations read: `Definition restate (Q : Prop) (q : StackAt
AnalysisBridged) (pf : StackProp AnalysisBridged q) (p : RestatePayload Q q) :
RestatedTableau Q` (`:912-916`), `RestatePayload Q q := StackProp
AnalysisBridged q -> Q` (`:894-895`), and `Definition conclude (c : Reprice)
(q : StackAt AnalysisBridged) (pf : StackProp AnalysisBridged q) (p :
ConcludePayload c q) : TableauAt AnalysisBridged (BridgedProp c)`
(`:880-886`).

**Deviation from R-F5.** The proposal keeps "this one's is supplied", which
has no stated subject and is the unclear half of the sentence F5 faults. Both
targets are named instead: `conclude`'s is `BridgedProp c` at the `Reprice` it
is given, `restate`'s is its parameter `Q`. The identifier `Reprice` is used
as an identifier, and no new term is coined.

### F6 — which programs publish the manifest's rows

Written, in the header of `staged/instances/pgl27/pgl27_rows.v`:

```
(* things stay outside the two programs that publish the manifest's rows: the *)
(* word row's conclusion at 2^-39, which moves a number and proves nothing    *)
(* new about a coalition, and the two bridge lemmas that carry a row's        *)
(* accumulated proposition to the statement a paper cites.                    *)
```

Checked: the two programs are `pgl27_row_exact_tableau` and
`pgl27_row_word_tableau`, which the same paragraph names at `:23-26` and which
`pgl27_row_exact_rowE` (`:336`) and `pgl27_row_word_rowE` (`:343`) equate with
the manifest's `pgl27_row_exact` and `pgl27_row_word`. The conclusion at
2^-39 is a line of `pgl27_row_word39` (`:424-429`), a program in the same
surface, so it stays outside those two and not outside the programs. R-F6 in
content, refilled to the box.

### F9 — the direction of the one-cut identity

```
(*   five_card_inv50_split   == the identity that discharges the one-cut      *)
(*                              row's terminal obligation                     *)
```

Checked: `Fact five_card_inv50_split (R : realType) : (1 / 50 : R) + 1 / 50 =
1 / 25`, and the row's terminal `|> conclude five_card_reprice_inv25 by
(fun R _ => ssr_ext.eqW (five_card_inv50_split R))` against the obligation
`cert_eps cert <= odflt (cert_eps cert) (c R)`. **Deviation from R-F9:** the
proposal ends at "the one-cut row's terminal"; the entry says "terminal
obligation", because what the identity discharges is the obligation and not
the terminal.

### F10 — the branch row's arm equation, the pass's only code

Added to `staged/instances/pgl27/pgl27_rows.v`, beside
`pgl27_row_word_branch39`:

```
(** The arm the branch row carries. Naming the Sampled value before the
    certify statement leaves the port where that statement put it, so the
    branch row's table column is the one pgl27_row_word39 has. *)
Lemma pgl27_row_word_branch39_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_word_branch39)) R) :
  security_arm_of pgl27_row_word_branch39 R idx = InputIndistinguishabilityArm.
Proof. exact: erefl. Qed.
```

The statement is the pattern of `pgl27_row_word39_armE` (`:447-451`) with the
row name in both positions, the `published_at` inside the index binder and the
`security_arm_of` subject, and nothing else changed. `-time` reports
`Chars 29042 - 29243 [Lemma~pgl27_row_word_branch39_...] 0. secs`,
`[Proof.] 0. secs`, `[exact~:~erefl~.] 0. secs`, `[Qed.] 0. secs`, all under
the 5 s threshold, so `exact: erefl` stands and `reflexivity` was not needed.
`by []` was not used, as the brief requires and as the project's own measured
hang on `published_at` equations across `conclude` warns.

A header index entry was added under "Key results", after
`pgl27_row_word39_armE`:

```
(*   pgl27_row_word_branch39_armE                                             *)
(*                           == the branch row carries that arm as well       *)
```

In `landing_fidelity.v`, `landing_pgl27_branch39_armE` now closes by
`exact: pgl27_row_word_branch39_armE` rather than proving the fact itself, and
`Print Assumptions pgl27_row_word_branch39_armE.` was added to the PGL(2,7)
block after `pgl27_row_word39_armE`. The recaptured `landing_fidelity.out`
carries the new block at the classical trio, so the branch row's arm now
reaches the assumption report through a staged declaration, which is what F10
asks for.

### What the pass changed, measured

`python3 compile.py` over the `_CoqProject` order, one process at a time
through the `rocq1` lock, no `make`, `psl211_endpoints.v` never compiled:

| File | rc | wall | sentences over 5 s |
|---|---|---|---|
| `staged/manifest/pgg_tableau.v` | 0 | 12.9 s | none |
| `staged/manifest/pgg_tableau_syntax.v` | 0 | 4.3 s | none |
| `staged/instances/pgl27/pgl27_rows.v` | 0 | 6.3 s | none |
| `staged/instances/kim2025/five_card_rows.v` | 0 | 4.5 s | none |
| `staged/instances/s5/s5_rows.v` | 0 | 3.9 s | none |
| `staged/instances/psl211/psl211_reading_constancy.v` | 0 | 22.0 s | two, 6.05 s and 6.08 s |
| `staged/instances/psl211/psl211_rows.v` | 0 | 5.5 s | none |
| `landing_fidelity.v` | 0 | 92.1 s | three, 20.28 s, 19.88 s and 20.53 s |

`python3 verify.py` exits 0. Against the sources it reports, after this pass:
`pgg_tableau.v` 0 code hunks and 14 comment hunks, `pgg_tableau_syntax.v` 1
code hunk and 1 comment hunk, `pgl27_rows.v` 3 code hunks and 9 comment hunks,
`five_card_rows.v` 6 and 18, `s5_rows.v` 2 and 0, `psl211_rows.v` 1 and 0,
`psl211_reading_constancy.v` 0 and 4.

Against commit d737a46, with every comment stripped and the remainder
tokenized, the only code changed in the staged tree is the seven lines of
`pgl27_row_word_branch39_armE`, and in `landing_fidelity.v` the one proof term
and the one `Print Assumptions` line. With the code stripped instead and the
comment text normalized to one word per line, the changed passages are exactly
F1 and F2 in `pgg_tableau.v`, F4 and F5 in the same file, F3 in
`pgg_tableau_syntax.v`, F6 and F10's entry and docstring in `pgl27_rows.v`,
and F9 in `five_card_rows.v`. `psl211_reading_constancy.v`, `psl211_rows.v`
and `s5_rows.v` are untouched in both, and `landing_fidelity.v`'s comments are
untouched.

Line lengths: every line of every staged file is at most 80 bytes except
`pgg_tableau_syntax.v:334`, `:372` and `:403`, the three notation string
literals the brief exempts. No banned word appears in any line the pass
writes, "indistinguishability" is never abbreviated, no meta narration
entered the staged text, and the one piece of proof strategy the pass could
have written, why `exact: erefl` rather than `by []`, is in this file and not
in a docstring.
