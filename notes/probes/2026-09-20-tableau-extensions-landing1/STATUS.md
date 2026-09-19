# Landing 1 of the Tableau extensions — staged text

Date: 2026-09-20. Branch `feat/tableau-extensions-probe`, HEAD `1437c1c`.

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

**After.** `kim_biased_cert_exact` survives (staged `:814`), so the entry is
kept and reworded, because "the same two" had lost one of its two:

```
(*   kim_biased_cert_exact   == the one-cut certificate with a constant in    *)
(*                              the marginal-bound field                      *)
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
`pgl27_reprice39` (staged `:411`), which types `pgl27_row_word_branch39`, and
after `pgl27_dealt` (`:135`) and `pgl27_word_cert` (`:261`).

**Cost.** The two moved sentences, from `-time` on the staged file:

```
Definition~pgl27_word_sampled~...     0.000 s  [chars 27966-28056]
Definition~pgl27_row_word_bran...     0.001 s  [chars 28287-28557]
```

No row-against-row data equation was added, which is the 48-to-96 s hazard the
brief names. The file's whole compile went from 6.3 s (the Kim landing's
measurement of production's text) to 6.5 s.

**Index entries added** (staged `:55-58`, after `pgl27_row_word39_bind`):

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
rewrite.

**`pgl27_row_word_branch39`, before** (probe `t0_sampled_branch_pgl27.v:145-147`,
moved verbatim in the first pass):

```
(** The second continuation, concluded at 2^-39 before it is published. The
    terminal sits between the branch point and the manifest row, so this pair
    exercises the reduction through the name across a terminal as well. *)
```

**After:**

```
(** The word program continued from the named value pgl27_word_sampled,
    certified by the input-indistinguishability arm and concluded at 2^-39
    before it is published. The accumulated bound is 2^-40 twice, pow2_split
    adds the two copies, and eqW reads that identity as the inequality the
    terminal's obligation asks for, so the row publishes the constant a
    reader cites and asserts about a coalition below the privacy threshold no
    more than the certificate proved. Continuing from a named Sampled value
    is what lets a further row over this model be written without repeating
    the dealt prefix. *)
```

Each clause read off the declaration and the terminal:

| Clause | Read from |
|---|---|
| continued from the named value `pgl27_word_sampled` | the definition's first line, staged `:479` |
| certified by the input-indistinguishability arm | `certify InputIndistinguishability pgl27_word_cert`, `:480` |
| concluded at 2^-39 before it is published | `\|> conclude pgl27_reprice39 …` then `\|> publish …`, `:481-482`, with `pgl27_reprice39 : Reprice := fun R => Some (2%:R^-39 : R)` at `:411` |
| the accumulated bound is 2^-40 twice, `pow2_split` adds the two copies, and `eqW` reads that identity as the inequality the terminal's obligation asks for | the payload `(fun R _ => ssr_ext.eqW (pow2_split R))`; the obligation's `InputIndistinguishability` branch is `cert_eps cert <= odflt (cert_eps cert) (c R)` (`pgg_tableau.v:826-827`), and `ssr_ext.eqW` is the `=` to `<=` reading |
| asserts about a coalition below the privacy threshold no more than the certificate proved | the obligation is `<=`, so the published number is at or above the certificate's own |
| continuing from a named Sampled value lets a further row be written without repeating the dealt prefix | a statement about the surface, not an equation; no equation with `pgl27_row_word39` is claimed, because no lemma of the staged file states one |

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
staged framework files for a stale count found none: the only surviving
occurrences of "two" are "the two bottom levels", "the two marginals", "the
two run arguments" and "the propositions of the two arms that carry a number",
and that last one is true, because the exact arm carries no number.

So E4 is one new paragraph, inserted between the arms paragraph and the
composition-laws paragraph, and it is the one piece of landing-1 prose no
audit has read:

```
(* A certificate says as much as its ideal and its secret say, and the record *)
(* determines neither. ipc_ideal is an adapter the instance chooses and       *)
(* ipc_secret a random variable on the actual model's sample space, valued in *)
(* the carrier the ideal's witness names. At a one-point carrier ipc_close    *)
(* compares the two models' readings and mentions no secret at all, and at an *)
(* ideal that is the actual adapter, which the record permits whenever that   *)
(* adapter carries an exact witness, the two joint laws are one term and      *)
(* ipc_close holds at zero. The other two arms are chosen with the same       *)
(* freedom: ic_ideal is any law on the group, and a constant ew_secret        *)
(* satisfies ew_indep at every coalition. So the proximity arm adds no        *)
(* freedom the tree did not already carry.                                    *)
```

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

Each clause read off the three records of the staged file:

| Clause | Read from |
|---|---|
| `ipc_ideal` is an adapter the instance chooses | `ipc_ideal : SampleAdapter R (instance_exec E)`, `pgg_tableau.v:213` |
| `ipc_secret` is a random variable on the actual model's sample space, valued in the carrier the ideal's witness names | `ipc_secret : {RV (sa_sampleP sa) -> ew_secretT ipc_witness}`, `:215` |
| at a one-point carrier `ipc_close` compares the two models' readings and mentions no secret at all | `ipc_close`, `:217-227`: both sides are `fdistmap` of a pair whose second component is the secret, so a one-point carrier makes the second component a point mass and the field a statement about the two reading laws alone. This is the content of `psl211_word_proximity_cert_secretTE`'s own comment (`p6_mutations.v:134-137`) |
| at an ideal that is the actual adapter the two joint laws are one term and `ipc_close` holds at zero | with `ipc_ideal := sa` and `ipc_secret := ew_secret ipc_witness`, the two `fdistmap` arguments and the two distributions are syntactically the same, so `var_dist` is zero |
| which the record permits whenever that adapter carries an exact witness | `ipc_witness : ExactWitness ipc_ideal`, `:214`, is the only constraint on `ipc_ideal` |
| `ic_ideal` is any law on the group | `ic_ideal : R.-fdist (pgg_gT (mp_M (instance_profile A)))`, `:175` |
| a constant `ew_secret` satisfies `ew_indep` at every coalition | `ew_secret : {RV (sa_sampleP sa) -> ew_secretT}` and `ew_indep` an independence statement about it, `:156-160` |

The sentence does not claim that the proximity arm is vacuous, and does not
claim that any certificate in the tree is. It says which two fields the
instance chooses and that the other two arms already had the same latitude.

Q2's ruling removed the citation; the paragraph above is as it now
stands, and each clause of the table is read off a record of the staged
file and nothing else.

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
edits, both from the section-4 table, both for landing 1. The two sentences
that become false only at landing 4 (`:67-69` and `:768-771`, the
"no weighted-word SampleAdapter exists in this tree" clause) are left alone,
and `:31-38`, `:14-15`, `:202`, `:208`, `:560`, `:674`, `:706` and `:725` were
read and need no landing-1 change.

**Edit 1** (`:689`), the R13 rename reaching this file.

Before: `odflt (cert_eps cert) (c R) at its own reprice coordinate c, and cert_eps`

After: `odflt (cert_eps cert) (c R) at its own conclude coordinate c, and cert_eps`

**Edit 2** (`:697-701`), the hypothetical that landing 1 performs.

Before:

```
(* Argued and not compiled: the proposition a row carries is
   IndistinguishabilityPropAt cert c, a variation distance bounded above by c,
   so an obligation weakened from an equality to cert_eps cert <= odflt
   (cert_eps cert) (c R) could only let a row publish a number no smaller than
   cert_eps. *)
```

After:

```
(* The obligation of conclude at an input-indistinguishability port is
   cert_eps cert <= odflt (cert_eps cert) (c R), and the proposition the row
   carries is IndistinguishabilityPropAt cert c, a variation distance bounded
   above by c. The bound below on what a row over this model publishes is
   therefore the obligation itself and not a further argument. *)
```

The inequality written there is the `InputIndistinguishability` branch of the
staged `ConcludePayload` (`pgg_tableau.v:826-827`), copied from it. The
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
| `instances/pgl27/pgl27_rows.v` | probe | 3 | E1, E1, E3 insertion |
| `instances/kim2025/five_card_rows.v` | probe | 3 | E1, E1, E2 removal |
| `instances/s5/s5_rows.v` | probe | 2 | E1, E1 |
| `instances/psl211/psl211_rows.v` | probe | 1 | E1 |
| `instances/psl211/psl211_reading_constancy.v` | PRODUCTION | 0 | — |

The E3 hunk is an insertion only, of the 43 tokens of the two moved
definitions, and the moved text is byte-identical to `t0_sampled_branch_pgl27.v`
(both blocks occur exactly once in each file). The E2 hunk is a deletion only,
of the 108 tokens of the two withdrawn declarations.

### 2. Comment words

| Staged file | Comment-word hunks | Classification |
|---|---|---|
| `manifest/pgg_tableau.v` | 1 | E4, one insertion of 130 words |
| `manifest/pgg_tableau_syntax.v` | 0 | — |
| `instances/pgl27/pgl27_rows.v` | 2 | E3 index entries; E3 moved section banner, the moved `pgl27_word_sampled` comment and the rewritten `pgl27_row_word_branch39` comment |
| `instances/kim2025/five_card_rows.v` | 4 | E2: index entry removed, index entry reworded, index entry removed, two declaration comments removed |
| `instances/s5/s5_rows.v` | 0 | — |
| `instances/psl211/psl211_rows.v` | 0 | — |
| `instances/psl211/psl211_reading_constancy.v` | 3 | E5 edit 1, E5 edit 2 (two adjacent hunks) |

No hunk is a meta-narration removal, because the scan below found nothing to
remove.

### 3. Scans

| Scan | Result |
|---|---|
| `SpectralDecay`, `SpectralCert`, `sc_` fields, `_indist\b`, `RepricePayload`, `port_reprice`, `kim_centi_cert40`, `spectral_constancy` | no hit anywhere in `staged/` |
| lines over 80 bytes | three, all in `manifest/pgg_tableau_syntax.v` (`:333`, `:371`, `:403`), all notation string literals, which the brief exempts |
| `apex`, `gate`/`gates`/`gated`/`gating`, `posit`/`posits`/`posited`/`positing`, `L1` | no hit |
| `indistinguishability` abbreviated | no hit; the word is spelled out at all 15 sites the 2026-09-19 rename established |
| probe, stage, audit, "renamed", "formerly", "landed", "landing" | four hits, all citations of a probe directory for a measurement, discussed below |

The four hits, and why each stays:

| Hit | Text | Verdict |
|---|---|---|
| `manifest/pgg_tableau_syntax.v:40,68` | "Measured on 2026-09-14, …" | production already carries the same two sentences at `:36` and `:64` |
| `manifest/pgg_tableau_syntax.v:79` | "measured on 2026-09-19 by binding it" | the G2 keyword measurement the design's section 5 says lands with the file |
| `instances/psl211/psl211_rows.v:74` | cites `notes/probes/2026-09-15-psl211-planb/audit-soundness/audit_alldecks.out` | byte-identical to production `:74` |
| `instances/psl211/psl211_reading_constancy.v:71` | cites `notes/probes/2026-09-19-psl211-sc-const/` | byte-identical to production `:71` |
| `instances/kim2025/five_card_rows.v:780-782` | cites `notes/probes/2026-09-19-tableau-extensions/STATUS.md, section F2` for a 147 s against 0.07 s measurement | kept; see question Q3 |

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

Times are the second run, after the two comment edits of the Q1 and Q2
rulings. Every file was recompiled in this order, because
`manifest/pgg_tableau.v` is upstream of all six others.

| File | rc | wall | sentences over 5 s |
|---|---|---|---|
| `staged/manifest/pgg_tableau.v` | 0 | 12.9 s | none |
| `staged/manifest/pgg_tableau_syntax.v` | 0 | 4.3 s | none |
| `staged/instances/pgl27/pgl27_rows.v` | 0 | 6.2 s | none |
| `staged/instances/kim2025/five_card_rows.v` | 0 | 4.5 s | none |
| `staged/instances/s5/s5_rows.v` | 0 | 4.0 s | none |
| `staged/instances/psl211/psl211_reading_constancy.v` | 0 | 22.1 s | two, 6.06 s and 6.11 s |
| `staged/instances/psl211/psl211_rows.v` | 0 | 5.7 s | none |
| `landing_fidelity.v` | 0 | 88.2 s | three, 20.5 s, 19.8 s and 20.6 s |

The two slow sentences of `psl211_reading_constancy.v` are
`rewrite -!size_filter; apply …`, which the Kim landing measured at 5.2, 6.1
and 6.2 s in the same file before this landing existed. The three slow
sentences of the fidelity file are the three `Print Assumptions` on
declarations whose type names `psl211_alldecks_observed`, at the 20 s the
design predicted.

`psl211_reading_constancy.v` compiled against the staged framework is the
check the brief requires either way: production's text, unchanged in code,
compiles under the `<=` obligation.

---

## Print Assumptions

35 declarations, from `landing_fidelity.out`. The trio is
`constructive_indefinite_description`, `functional_extensionality_dep` and
`propositional_extensionality`.

| Group | Declarations | Assumptions |
|---|---|---|
| framework | `port_conclude`, `idealproximity_tail`, `certify_exact_armE`, `certify_indistinguishability_armE`, `certify_idealproximity_armE`, `conclude_armE`, `publish_armE` | trio |
| PGL(2,7) | `pgl27_row_exact_tableau`, `pgl27_row_word_tableau`, `pgl27_row_word39`, `pgl27_row_word39_bind`, `pgl27_row_word_branch39`, `pgl27_row_exact_rowE`, `pgl27_row_word_rowE`, `pgl27_row_exact_armE`, `pgl27_row_word_armE`, `pgl27_row_word39_armE`, `pgl27_row_word39_bindE` | trio |
| five-card | `five_card_row_uniform_tableau`, `five_card_row_repeated_indistinguishability_tableau`, `five_card_row_biased_indistinguishability_tableau`, `five_card_row_repeated39`, `five_card_row_biased_inv25`, `five_card_row_uniform_rowE`, `five_card_row_uniform_armE`, `five_card_row_repeated_indistinguishability_rowE`, `five_card_row_biased_indistinguishability_rowE`, `five_card_row_biased_forms_publishedE`, `five_card_row_repeated39_atE` | trio |
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
| the proximity certificate | all five fields of `IdealProximityCert`, including `ipc_close` restated in full, so a change to any field's type is a compile error |
| the arm reader | `port_arm` at all three constructors; `security_arm_of` as `ab_arm` of the published data; the five general `_armE` lemmas restated |
| the terminal | `ConcludePayload` restated by unfolding, which is where the `<=` lives; `port_conclude`'s statement; `Fail Check` on the two retired names |
| the per-program arm pins | all six that exist in the four staged rows files |
| the manifest rows | all eight `_rowE` and `_publishedE` equations, plus `five_card_row_repeated39_atE` |
| the published numbers | `five_card_reprice39 R = Some (2%:R ^- 39)`, `pgl27_reprice39 R = Some (2%:R ^- 39)`, `five_card_reprice_inv25 R = Some (1 / 25)` |
| the withdrawal | the two `Fail Check`s, and `five_card_row_repeated39 : PublishedRowAt five_card_reprice39` |
| E3 | `pgl27_word_sampled = (pgl27_dealt sample pgl27_word_family)`, the two types, and `published_row pgl27_row_word_branch39 = published_row pgl27_row_word39` |
| assumptions | the 35 `Print Assumptions` above |

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
Staged `:780-782`, inside the comment explaining why a conversion closes by
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

**Q6. `five_card_rows.v` carries one arm pin where the other three rows files
carry one each and PGL(2,7) carries three. RULED: leave it as the probe's
audited text has it, and keep this entry so the auditors see it.** The staged five-card file pins
only `five_card_row_uniform_armE`; its two input-indistinguishability programs
and its two concluded rows have no `_armE`. This is the probe's audited text
and was not changed. Recording it because the design's section 1 says landing
1 lands "the per-program `_armE` pins in the four rows files", which a reader
could take to mean one per program.

**Q7. Landing 2's withdrawal is now the only consumer left. RULED: noted;
landing 2 removes the two declarations.** After this
staged text replaces production's `five_card_rows.v`,
`kim_centi_marginal_bound40` (`five_card_mixing.v:507`) and
`kim_centi_cut_mixing40` (`:517`) have no consumer anywhere in the tree. A
whole-tree `grep` for the four D3 names outside `notes/` returns only those
two definitions and the staged file's own `.glob`. So landing 2's removal is
unblocked, and between landing 1 and landing 2 the tree holds two declarations
nothing uses.
