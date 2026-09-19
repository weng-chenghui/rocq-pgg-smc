# Soundness audit of the Kim spectral landing probe

Date: 2026-09-19. Independent adversarial audit. The auditor wrote none of what
is audited, edited no existing file and ran no Rocq process: every question was
answered from the probe text, the production tree, `.Makefile.rocq.d` and two
scripts written for this audit.

PROBE = `notes/probes/2026-09-19-kim-spectral-landing/`.
SRC = `notes/probes/2026-09-19-kim-spectral-arm/`.
Spec = `notes/20260919-kim-spectral-landing-design.md`.

## Verdict

**NO-GO** for "these landing copies may be copied into the permanent tree as
they are".

Four blocking findings. Three of them are one defect seen from three sides: the
landing raises Kim's seven-cut row to `AnalysisBridged` and attributes that
level, in the manifest's prose, to `centi_cut_mixing`, a bound on the cut
carrier that the manifest's own admission criterion and its own Row 2 and Row 8
precedents do not admit, and that the same row's surviving justification refuses
for `endpoint_bound` and `deal_centi_lt`. The fourth is a production sentence
the landing leaves false in `manifest/pgg_analysis_client.v`, which the probe's
proposition search missed.

Nothing in the mathematics is wrong. Every statement moved from SRC is
byte-identical, every pin pins what its docstring describes, the numbers are
right, the recompile set is right and no import cycle exists. The blocking
findings are all in prose that becomes permanent.

## Question 1 — fidelity of the move

A script (`stmt.py`, `cmp.py` in the audit scratch directory) strips comments,
splits each file into declarations at depth-zero periods, normalizes whitespace,
maps SRC names through `SRC/rename_map.tsv`, and compares statement by
statement over the five SRC files and the four landing files that carry
declarations.

**Result: 48 of 48 statements identical.** No hypothesis added, none dropped, no
implicit made explicit, no carrier changed.

Two statements differ, and both are the ones the prover declares:

| name | SRC | landing |
|---|---|---|
| `kim_biased_epsE` | `sw_bound_eps kim_biased_marginal_bound = Num.sqrt 5%:R * (1 / 80).` | `(R : realType) : sw_bound_eps (kim_biased_marginal_bound R) = Num.sqrt 5%:R * (1 / 80).` |
| `kim_biased_exact_le_eps` | `1 / 50 <= sw_bound_eps kim_biased_marginal_bound :> R.` | `(R : realType) : 1 / 50 <= sw_bound_eps (kim_biased_marginal_bound R) :> R.` |

Confirmed: this is what discharging gives. Both sit in SRC's
`Section five_card_cut_mixing` (`kim_sc_close_probe.v:33-141`) under
`Variable R : realType`, beside the `Definition kim_biased_marginal_bound` they
mention. `End` generalizes the definition to `forall R`, so every use inside a
discharged statement gains the argument `R`, and `R` stays explicit because no
other argument determines it. The two lemmas land in `five_card_rows.v`, a
different file from the section, so they must carry the binder in the discharged
form. Nothing else changed.

Two further declarations change kind, and that change is the landing's content,
not a drift. SRC's `Fail Definition five_card_row_biased_ideal_rowE` and
`Fail Definition five_card_row_repeated_spectral_rowE`
(`kim_spectral_rows_probe.v:189`, `:196`) become proved `Lemma`s at
PROBE/`five_card_rows.v:605`, `:611` with byte-identical statements. SRC could
not prove them because the manifest rows had not moved; the landing moves them.

Inventory: `var_dist_supp.v` five lemmas, `five_card_mixing.v` twenty-one
declarations, `five_card_rows.v` twenty-six new declarations plus three recorded
`Fail`s, one deletion (`five_card_row_repeated_at_manifest_level`). The section
rename `five_card_static_obs_const` to `five_card_colour_census` is present and
the lemma keeps its name (`five_card_mixing.v:232`, `:316`).

NOTE N6: SRC's recorded `Fail five_card_row_biased_inv25_rowE`
(`kim_spectral_rows_probe.v:371`) does not land. Nothing depends on it and the
spec does not ask for it; recorded for the SRC-to-landing ledger only.

## Question 2 — the manifest copy

Read in full. Fifteen hunks with comments, six with comments stripped.

### (a) the two row definitions and their docstrings

Both name the ideal ("the uniform rotation law on the cut group"), the carrier
("on the cut carrier itself") and the base premise by its facade alias
(`FiveCardAnalysis.biased_cut_mixing`, `FiveCardAnalysis.centi_cut_mixing`, with
`FiveCardAnalysis.static_obs_const` for the reading equality). Neither claims
independence from the secret, neither speaks of two seats, neither mentions the
full reveal. Both are within the certified statement. **Pass**, with one gap
folded into F1 below: `five_card_row_repeated`'s docstring asserts
`AnalysisBridged` and names no theorem that reaches it, where
`five_card_row_biased`'s names `colour_view_leak_bound`.

### (b) "cut-carrier mixing" added to the closed vocabulary at :65

The vocabulary need not be widened. The manifest already holds the answer for
this exact theorem shape. Row 2 is the closest analogue in the file: an
`IdealFinite` row whose model transfer rests on a mixing bound of the row's own
shuffle against group uniform on the cut carrier. That bound,
`PGL27Analysis.word_mixing`, appears at production `:173-174` under **bound or
certificate**, and at `:182-184` under **missing premise** as what supplies the
base-distribution bound "on the cut carrier itself". It gets **no capability
line**: Row 2's capability table (`:190-206`) never lists it, and the one
mention of it there is a derivation note inside another theorem's notion cell.
Row 8 does the same with the cut-level `S5Analysis.word_endpoint_bound`, which
does get a capability line but under the existing label "cut-level endpoint
marginal mixing" because it is a bound on an endpoint pushforward.

`centi_cut_mixing` and `biased_cut_mixing` are bounds on the cut law itself, so
"endpoint marginal mixing" genuinely does not cover them, and that is the reason
Row 2 gives them no capability line rather than the reason to widen a list the
header declares closed. Severity SHOULD-FIX (S1): drop the two capability lines
and revert `:65`, keeping both theorems where the landing already puts them,
under **bound or certificate**.

### (c) Row 3's missing-premise cell

**True and consistent.** `static_obs_const` is exactly the second hypothesis of
`var_dist_fdistmap_transfer` at this development (`security/pgg_collusion_bound.v:987`,
hypothesis `ideal_eq : fdistmap fx Q = fdistmap fy Q`), and it is stated over
`sa_cut_dist (FiveCardAnalysis.uniform_sample R)`, which is Row 3's own cut law.
"What this row lacks is a second model" matches the three other
`StaticExecutedOnly` rows: Row 1 says "none: the path compares no idealized
model, its shuffle being the exact uniform distribution on the group already"
(`:117-119`), Row 7 says "none is needed" (`:461`), Row 9 says "none: the cut
this model draws is the uniform ..." (`:598`). Row 3 now reads like them.

### (d) the "Absent capabilities" paragraph

The five-card paragraph rewrite is true. "Section 7 of its facade carries the
distance of each of Kim's two cut laws from the uniform rotation law on the cut
carrier and the constancy of a coalition's reading of that law" — the facade
carries exactly those three aliases. "Rows 4 and 5 claim a cut-carrier transfer
and name no absent premise" — they do. "Row 3's own cut law is the uniform
rotation, so that row has no finite model to compare with an ideal one" — true.
"No endpoint marginal bound is recorded as a privacy or security capability"
survives: "cut-carrier mixing" is neither. See S7 for the one clause in the
paragraph's opening that was already loose and stays loose.

### (e) the three new spelled-type `Check` pins

All three pin what their docstrings describe.

- `centi_cut_mixing` (copy `:1425-1429`) pins
  `var_dist (sw_rho_dist (scb_bound (FiveCardAnalysis.centi_bundle R))) (sa_cut_dist (FiveCardAnalysis.uniform_sample R)) <= sw_bound_eps (scb_bound (FiveCardAnalysis.centi_bundle R))`.
  `FiveCardAnalysis.centi_bundle = @kim_security_bundle_centi` and
  `FiveCardAnalysis.uniform_sample = @five_card_sample`
  (`five_card_analysis.v:337`, `:200`), so this is the same statement the facade
  pins at `five_card_analysis.v:460` under the other spelling. Docstring says
  "within the seven-cut bundle's own spectral number of the uniform rotation
  law, in variation distance on the cut group". Matches.
- `biased_cut_mixing` (copy `:1431-1435`) pins the same shape at
  `five_card_mixing.kim_biased_marginal_bound R`. Matches its docstring.
- `static_obs_const` (copy `:1437-1448`) pins
  `#|C| < profile_k (instance_profile five_card_algebra)` implying the two
  pushforward equality under `sa_cut_dist (uniform_sample R)`.
  `profile_k den_boer_profile = 2` (`instances/denboer1989/den_boer_profile.v:90`),
  so the premise is "at most one seat", which is what the docstring says. It is
  also literally the `sc_const` field of `SpectralCert`
  (`manifest/pgg_tableau.v:138-142`).

NOTE N4: the `biased` pin reaches through `five_card_mixing.` while the `centi`
pin goes through a facade alias, because `kim_biased_marginal_bound` has no
facade alias and `centi_bundle` does. Reaching into a non-facade module from a
manifest pin is precedented (`PGL27Analysis.word_mixing`'s pin at production
`:1047-1053` names `pgl27_mixing.pgl27_moves` and `pgl27_profile.pgl27_G_pos`),
so this is an asymmetry, not a violation.

### (f) every `erefl` pin touched

Nine pins bear on the two rows and the facade statuses. All nine are correct and
none is missing.

| pin | before | after | verdict |
|---|---|---|---|
| `FiveCardAnalysis.exec_transfer_status` | `StaticExecutedOnly` | unchanged | correct, the name now means the uniform path |
| `FiveCardAnalysis.biased_transfer_status` | absent | `IdealFinite` | new, correct |
| `FiveCardAnalysis.repeated_transfer_status` | `NoModelComparison` | `IdealFinite` | correct |
| `apr_completion five_card_row_biased` | `AnalysisBridged` | unchanged | correct |
| `apr_transfer five_card_row_biased` | `StaticExecutedOnly` | `IdealFinite` | correct |
| `apr_assumptions five_card_row_biased` | `BaselineClassicalOnly` | unchanged | correct |
| `apr_completion five_card_row_repeated` | `Sampled` | `AnalysisBridged` | correct |
| `apr_transfer five_card_row_repeated` | `NoModelComparison` | `IdealFinite` | correct |
| `apr_assumptions five_card_row_repeated` | `BaselineClassicalOnly` | unchanged | correct |

`Check (apr_model five_card_row_repeated : AnalysisModelFamily FiveCardAnalysis.observed)`
keeps its text and stays well-typed: the model slot is mandatory at both
`Sampled` and `AnalysisBridged`, so moving between them does not retype it.

### (g) what is still false in the manifest copy

Searched the copy by proposition for each of the eight the task names.
Everything the prover lists is changed. Two things are not right; both are F1
and F2 below. No count of rows by level or status exists in the file (checked by
regular expression over counting phrases; the only numeric claims are "the two
constructors of PggAxiom" at `:52` and "the only named assumption of this row"
at `:590`, both unaffected). The client's "nine typed rows" is unaffected: the
landing adds no row.

## Question 3 — the facade copy

`exec_transfer_status` keeps its name and its value `StaticExecutedOnly`, forced
by the bare `Check FiveCardAnalysis.exec_transfer_status.` at
`manifest/pgg_analysis_client.v:48`. The new docstring says which path it means
("the transfer status of the uniform exact-cut path"), so the file is not
misleading about the value. The residual is the identifier: `exec_` no longer
distinguishes it from `biased_transfer_status` and `repeated_transfer_status`,
which are executed paths too. See S3.

The retention-check contract at `:372-382` asks for "one representative per
section and one for the bound sub-block". The prover added exactly one
spelled-type `Check` for section 7 (`centi_cut_mixing`). **That is what the
contract asks.** The manifest checks all three aliases because the manifest's
contract is different — "every identifier in the tables below" — and all three
appear in Row 3, 4 and 5 cells.

No other docstring, header sentence or check-table line of the facade copy is
false. The header's section-7 sentence, the three alias docstrings and the three
new phase-H1 check-table rows all match what the section holds.

NOTE N7: the facade header at `:16` says section 7 carries "the two base
premises" and then enumerates three aliases. It is counting kinds, not aliases.
Reword to "the base premises Kim's one-cut and seven-cut rows rest on" if the
count is to be dropped.

## Question 4 — the rows-file copy

Read `diffs/five_card_rows.v.diff` in full. Nine hunks, four code hunks.

**The header is true and it is the best statement of scope in the batch.**
`:32-39` gives the certified statement verbatim, then says in three sentences
what it is not: "That is not independence of the reading from the secret, which
the exact arm states and which the uniform row alone carries. It is conditional
on a coalition of fewer than two seats. And it says nothing about the full
reveal." No sentence anywhere in the file implies independence from the secret,
two seats, or the full reveal for the certified rows. The file title "three
rows, as seven programs" is right: seven programs are declared
(`five_card_row_uniform_tableau`, the two `Tableau Sampled`, the two certified,
the two repriced).

`five_card_row_biased_levelE` (`:487-495`) and the recorded
`Fail five_card_row_biased_at_manifest_level` (`:497-506`) keep their statements
with rewritten prose. The rewrite is true: both are now told as facts about one
named program, each closing with the fact that the path also carries a program
that does reach the manifest's level. Neither sentence asserts anything about
the biased path as a whole.

The new recorded `Fail five_card_row_repeated_spectral_uniform_rowE` (`:615-623`)
fails for the stated reason. `l7_fail_messages.v` states it unguarded and the
recorded message is a unification failure between
`published_row five_card_row_repeated_spectral_tableau` and
`five_card_row_uniform`. The docstring says the two rows "differ in two of their
five fields": the model family (`centi_family` against the uniform family) and
the transfer status (`IdealFinite` against `StaticExecutedOnly`). Checked
against the two row values: observed, completion level and assumption status
agree, the other two do not. Two of five, as stated.

Both row equations are proved by conversion (`Proof. by []. Qed.`) against the
moved manifest rows, and **neither carries security content, and no comment
suggests otherwise**. `:600-604` says so explicitly: "An AnalysisPathRow stores
descriptive metadata and no Prop, so this equation fixes which path the program
is written for and asserts nothing about the certificate the program carries."
`five_card_row_biased_forms_publishedE` (`:790-794`) repeats the disclaimer and
adds that such an equation "cannot say which transfer status is the honest one".
This meets soundness invariant 5 of the spec.

## Question 5 — the numbers

Recomputed in Python.

| quantity | exact | printed claim | verdict |
|---|---|---|---|
| `2 * sqrt 5 * (1/80)^7` | 2.1324805998800e-13 | about 2.13e-13 | correct |
| `2^-39` | 1.8189894035459e-12 | about 1.82e-12 | correct |
| ratio | 8.5299223995201 | about 8.53 | correct |
| `sqrt 5 / 40` | 0.0559016994375 | about 0.0559 | correct |
| `1/25` | 0.04 | — | correct |
| `2^-40 + 2^-40 = 2^-39` | exact | `five_card_pow2_39_split` | correct |
| `1/50 + 1/50 = 1/25` | exact | `five_card_inv50_split` | correct |

No decimal figure appears in any of the five files; the numbers live in the
prose only as closed forms and word forms ("two to the minus thirty-ninth",
"sqrt 5 over eighty", "one twenty-fifth"), all of which match.

Every place a comment calls a number small or compares it with the ceiling names
`var_dist_le2`: `five_card_rows.v:686` ("under two, the ceiling `var_dist_le2`
gives for a variation distance") and `:800` (the same for one twenty-fifth).
The claim at `:689-690`, "at about three percent of the ceiling", is honest:
0.0559 / 2 = 2.80 percent. The claim at `:687-689` that the row "rules out a
coalition of at most one seat telling the two committed pairs apart with
certainty" is correct, since a variation distance of two is exactly the
mutually-singular case.

NOTE N1: no proof in the landing uses `var_dist_le2`. It is cited in two
docstrings and printed in the fidelity file, and nothing else. The lemma is the
scale the prose is read against, so it earns its place under the repository's
"claimed or premise" standard, but the implementation plan should say so rather
than leave a reviewer to find a library lemma with no consumer.

## Question 6 — dependencies and cost

Recomputed from `.Makefile.rocq.d` with `dep.py` (audit scratch directory),
which joins continuations, builds the target-to-prerequisite map and takes
forward and reverse closures.

**Manifest reverse-dependants: seven, exactly as claimed.**
`five_card_rows`, `pgl27_rows`, `psl211_rows`, `s5_rows`, `pgg_analysis_client`,
`pgg_tableau`, `pgg_tableau_syntax`. The one-hop set and the full reverse
closure coincide.

**Landing recompile set: eleven, exactly as claimed.** Nine existing production
files (the seven above plus `five_card_analysis` and `pgg_analysis_manifest`)
plus the two new files.

**`instances/psl211/psl211_endpoints.vo` is never recompiled.** It is in the
reverse closure of nothing in the landing. See S5 for the way STATUS states
this.

**Imports.** `var_dist_supp.v` requires `HB`, four mathcomp modules
(`all_boot all_order all_algebra`, `boolp reals`) and four infotheo modules
(`realType_ext fdist proba variation_dist`). Nothing from the project.
Confirmed.

`five_card_mixing.v` requires no manifest file, no `pgg_analysis_status`, no
Tableau file and no facade. Confirmed by reading its eighteen `Require` lines.

**No import cycle.** Every one of `five_card_mixing.v`'s project prerequisites
was taken through its own forward closure; none reaches `five_card_analysis`,
`pgg_analysis_manifest` or `five_card_rows`. So the facade may import
`five_card_mixing` safely.

**S6 — the `_CoqProject` placement question rests on a false premise.** The spec
(decision 3) and STATUS both say the two new lines go "after their
dependencies". The production `_CoqProject` is **not** in dependency order: the
audit script finds **101 places** where a file is listed before one of its own
prerequisites. `instances/kim2025/five_card_analysis.v` (line 76) is itself one
of them, sitting before seven of its prerequisites, the furthest being
`instances/denboer1989/denboer_trace.v` (line 146).

For `five_card_mixing.v` the requirement is not merely unmet, it is
unsatisfiable: its prerequisites run up to `reconstruct/algebraic_rigidity.v`
(line 130), while the facade that must import it is at line 76. There is no line
number both after 130 and before 76.

This costs nothing at build time, because `coq_makefile` orders the build from
`coqdep` and not from the `_CoqProject` list. It costs something in the
implementation plan, which must not say "compile in `_CoqProject` order,
single file each": that order is not a valid compile order for the existing
tree.

**Exact insertion points, by the file's real convention, which is grouping:**

- `lib/var_dist_supp.v` — a new line **35**, immediately after
  `lib/mutual_info_recoding.v` (line 34) and before `smc/graded_resource.v`.
  It has no project prerequisite, so no earlier position is required and the
  `lib` block is where its three neighbours with the same shape already sit.
- `instances/kim2025/five_card_mixing.v` — a new line **76**, immediately after
  `instances/kim2025/five_card_models.v` (line 75) and immediately before
  `instances/kim2025/five_card_analysis.v`, which becomes line 77. This is the
  position `instances/pgl27/pgl27_mixing.v` (line 196) holds relative to
  `instances/pgl27/pgl27_analysis.v` (line 201), which is the precedent
  decision 2 of the spec invokes.

## Question 7 — what the landing leaves false elsewhere

Independent search, by proposition and not by name, over the twenty-three
directories of `_CoqProject` plus `legacy/`, `docs/` and `README.md`: fourteen
proposition families, each as several regular expressions, each hit filtered by
a five-line context window mentioning the five-card development, Kim or
den Boer. Dated notes and plans were excluded as records.

**One hit the prover's L8 table missed, and it is blocking (F3):**
`manifest/pgg_analysis_client.v:34-37`.

Everything else the search produced is either inside one of the three files the
landing changes, or a different path, or a dated record. In particular:

- `manifest/pgg_tableau.v` and `manifest/pgg_tableau_syntax.v` mention the
  five-card development nowhere.
- `instances/s5/s5_rows.v`, `instances/pgl27/pgl27_rows.v` and
  `instances/psl211/psl211_rows.v` mention it nowhere.
- `manifest/pgg_analysis_status.v:62-71` defines `IdealFinite` and stays: it is
  the criterion the landing claims to meet.
- `manifest/pgg_analysis_client.v:12-13` ("Section 7 of a facade may carry no
  theorem") stays true as a general remark, and `:67-68` is the PSL(2,11) block.
- `README.md` makes no claim about any row's level or status.
- `docs/style/scan-2026-08-26/*` and `docs/superpowers/plans/*` are dated
  records.

NOTE N2: `instances/kim2025/five_card_kim.v:54` carries the same barred
two-character term as question 8's sentence, inside a parenthesis glossing
infotheo's `var_dist`. The landing does not edit that file and the question does
not ask about it, so it is recorded here and not carried.

## Question 8 — the barred term at `manifest/pgg_analysis_manifest.v:688`

PROBE copy line `:718`. The sentence runs from `:714` to `:720` of the copy
(`:684` to `:690` of production) and reads:

> For Q the uniform distribution on the generated group the premise is moreover
> UNSATISFIABLE at every delta below one: every generator of this instance is a
> transposition, so a word of length L evaluates into the coset of the
> alternating subgroup determined by the parity of L, and the cut distribution
> has full-L1 distance one from group uniform.

Two defects. The barred term, and an overclaim: "distance one" is an equality
that does not hold in general. With the word cut distribution P supported in one
coset C of index two and U uniform on the group G,

    sum over G of |P(g) - U(g)|
      = sum over C of |P(g) - 1/|G||  +  1/2
      >= | sum over C of (P(g) - 1/|G|) |  +  1/2
      =  (1 - 1/2) + 1/2  =  1,

with equality exactly when P(g) >= 1/|G| for every g in C. A word distribution
at length L need not dominate the uniform density on its coset, and for a
concentrated one the quantity approaches two. So the true statement is "at
least one", which is also all the sentence needs: the premise asks for a bound
below one.

The line at `:714` is also malformed in production: the closing `*)` is jammed
against the text with no padding, breaking the 80-column box. The replacement
repairs it.

**Exact replacement for copy `:714-720` (production `:684-690`):**

```
(* group-uniform ideal. For Q the uniform distribution on the generated       *)
(* group the premise is moreover UNSATISFIABLE at every delta below one:      *)
(* every generator of this instance is a transposition, so a word of length   *)
(* L evaluates into the coset of the alternating subgroup determined by the   *)
(* parity of L, and the sum of the absolute differences between the cut       *)
(* distribution and group uniform is at least one. That sign-coset            *)
(* confinement is not formalized at S_5, and no theorem of this repository    *)
(* asserts it there.                                                          *)
```

Checked against what it describes: the sentence is about
`S5Analysis.word_missing_premise`, whose bound is
`var_dist (sa_cut_dist (word_sample secretP L)) Q <= delta` on the cut carrier
`{perm 'I_5}`. `var_dist` in this repository is the sum of absolute differences
(`instances/kim2025/five_card_kim.v:54`, and
PROBE/`var_dist_supp.v:47`), so the replacement names the same quantity in the
words the owner asks for. "At least one" is what the coset confinement gives and
is what makes the premise unsatisfiable below one.

## Question 9 — STATUS.md

No self-citation by line number. Every `file:line` in the document points at
another file, and the one place line numbers could be confused declares its
frame: "Line numbers are the copies'" (`:90`). The defect class of the previous
batch is absent.

Two internal contradictions, both SHOULD-FIX: S4 and S5 below.

One statement is not a contradiction but is worth confirming as read: the
verdict row for the generic library file claims none of the five lemmas
duplicates infotheo or the tree, and the "Where each declaration went" section
gives the comparison in full. Not re-audited here; SRC's five soundness audits
cover it.

The flagged judgement calls in "What the spec or SRC got wrong" items 5 and 6
are the right things to flag. Item 5's first half is answered above (the facade
contract does ask for one section-7 representative, and the prover supplied
exactly one); its second half is answered by S1 (the vocabulary need not be
widened, because Row 2 shows the file's own arrangement for this theorem shape).
Item 6 is confirmed: `manifest/pgg_analysis_client.v:48` does hold a bare
`Check FiveCardAnalysis.exec_transfer_status.`, and renaming it would edit a
file the fifth ledger row requires be left alone but for its import. That
constraint does not survive F3, which makes that file an edited file anyway; see
S3.

---

# Findings

## BLOCKING

### F1 — Row 5's "final bridge theorem" cell names a theorem that is not one

**Severity:** BLOCKING (a false sentence in text that becomes permanent).
**File:** PROBE/`pgg_analysis_manifest.v:373-375`
(production `manifest/pgg_analysis_manifest.v:355`).

**Current text:**

```
(* | final bridge theorem | FiveCardAnalysis.centi_cut_mixing, a mixing       *)
(*                          bound on the cut carrier, with                    *)
(*                          FiveCardAnalysis.static_obs_const |               *)
```

**Why it is false.** The manifest defines `AnalysisBridged` at `:34-36` of the
copy as "+ bridge alias to a named security, leakage, mixing or limitation
theorem about the same distribution **and the same observer**".
`centi_cut_mixing` compares two laws on the cut carrier and names no observer at
all; `static_obs_const` names an observer but is a statement about the ideal
law, not about this row's law. Neither, alone or as a pair of named objects, is
a theorem about the row's distribution and the row's observer.

Three independent confirmations that this is the file's own standard, not the
auditor's:

1. Row 2 is the same shape and does not do this. `PGL27Analysis.word_mixing` is
   a mixing bound of the row's own shuffle against group uniform on the cut
   carrier. Production `:173-174` records it under **bound or certificate**;
   Row 2's **final bridge theorem** cell (`:175-177`) names three
   observer-level theorems and not `word_mixing`.
2. Row 8 says it outright. Its level justification (`:552-555`) puts
   `AnalysisBridged` on `exec_endpoint_bound`, "a mixing theorem at the row's
   own executed observer", while the cut-level `word_endpoint_bound` stays a
   bound.
3. Row 5 refuses weaker-in-the-same-way theorems in the very paragraph the
   landing keeps. The surviving sentence at copy `:404-407` keeps
   `endpoint_bound` and `deal_centi_lt` out because "neither quantifies over a
   coalition and neither mentions a second secret". `centi_cut_mixing`
   quantifies over no coalition and mentions no secret either, so the row now
   admits on one ground what it refuses on the same ground two lines later.

What does carry the row is the conclusion of `spectral_tail`
(`manifest/pgg_tableau.v:562-571`), which is `var_dist_fdistmap_transfer`
applied to `sc_close` and `sc_const`, instantiated at this row by the certified
program in `instances/kim2025/five_card_rows.v`. That conclusion is
coalition-quantified and two-pair-quantified, so it meets the row's own test.
The manifest cannot alias it, because `five_card_rows.v` imports the manifest.
The honest cell says so.

**Exact replacement:**

```
(* | final bridge theorem | the spectral arm's coalition bound at this        *)
(*                          row: var_dist_fdistmap_transfer applied to        *)
(*                          FiveCardAnalysis.centi_cut_mixing and             *)
(*                          FiveCardAnalysis.static_obs_const. It is          *)
(*                          stated by the certified program of                *)
(*                          instances/kim2025/five_card_rows.v, which         *)
(*                          imports this file, so no alias of it can          *)
(*                          be checked here |                                 *)
```

### F2 — Row 5's level justification draws the same inference

**Severity:** BLOCKING (same defect, second carrier).
**File:** PROBE/`pgg_analysis_manifest.v:399-404`
(production `manifest/pgg_analysis_manifest.v:374-380`).

**Current text (the clause at issue):**

```
(* both cut distributions are named, giving Sampled. centi_cut_mixing         *)
(* bounds the distance of the seven-cut distribution from the uniform         *)
(* rotation law on the cut carrier itself, a mixing theorem about this        *)
(* row's own distribution, giving AnalysisBridged; with static_obs_const it   *)
(* discharges both hypotheses of var_dist_fdistmap_transfer, giving           *)
(* IdealFinite. endpoint_bound and deal_centi_lt stay in the row for          *)
```

"giving AnalysisBridged" is the false step. The `IdealFinite` half of the same
sentence is correct and is confirmed above under question 2(e).

**Exact replacement:**

```
(* both cut distributions are named, giving Sampled. centi_cut_mixing         *)
(* bounds the distance of the seven-cut distribution from the uniform         *)
(* rotation law on the cut carrier itself, and with static_obs_const it       *)
(* discharges both hypotheses of var_dist_fdistmap_transfer, giving           *)
(* IdealFinite. The conclusion of that transfer, a bound on the variation     *)
(* distance between the static readings of a coalition of at most one         *)
(* seat at two committed pairs, is what gives AnalysisBridged; it is          *)
(* stated by the certified program of five_card_rows.v, which imports         *)
(* this file. endpoint_bound and deal_centi_lt stay in the row for            *)
```

The corresponding clause of `five_card_row_repeated`'s docstring
(PROBE `:793-802`, production `:770-778`) has the same omission and should gain
the same sentence: after "with FiveCardAnalysis.static_obs_const for the reading
equality", add that the transfer's coalition conclusion, stated by the certified
program of `five_card_rows.v`, is what reaches `AnalysisBridged`. As it stands
that docstring asserts `AnalysisBridged` and names nothing that reaches it,
where the sibling docstring for `five_card_row_biased` names
`colour_view_leak_bound`.

### F3 — `manifest/pgg_analysis_client.v` is left false, and is not in the change list

**Severity:** BLOCKING (a false sentence in permanent text, missed by the
probe's proposition search).
**File:** production `manifest/pgg_analysis_client.v:34-37`, unchanged in
PROBE/`pgg_analysis_client.v:34-37`.

**Current text:**

```
(* Five-card development, sections 1 to 6, the bound sub-block and section 7.
   That section carries no theorem, so its representative is the typed
   transfer status; the bound alias below is deliberately NOT a security
   alias. *)
```

After the landing, section 7 of the five-card facade carries three theorem
aliases, so "That section carries no theorem" is false. The probe's proposition
table lists this proposition ("nothing to alias, section 7 empty") and records
only three hits, all inside `five_card_analysis.v`. The client's copy in the
probe has one hunk and that hunk is the import, so the landing as it stands
publishes the false sentence.

The file's own pattern for a facade whose section 7 does carry a theorem is the
PGL(2,7) block at `:31-32`, which checks a section-7 theorem and the typed
status. Following it also removes the anomaly that the five-card block now
checks two of three typed statuses and no theorem.

**Exact replacement for `:34-37`:**

```
(* Five-card development, sections 1 to 6, the bound sub-block and section 7.
   Section 7 carries the base premises of the two cut-carrier transfers, so
   it is represented here by one of them and by the typed transfer statuses;
   the bound alias below is deliberately NOT a security alias. *)
```

**And, after `:48`:**

```
Check FiveCardAnalysis.centi_cut_mixing.        (* 7 Transfer *)
Check FiveCardAnalysis.exec_transfer_status.    (* 7 Transfer, typed status *)
Check FiveCardAnalysis.biased_transfer_status.
Check FiveCardAnalysis.repeated_transfer_status.
```

This adds one code hunk to a file the fifth ledger row wanted untouched. The
ledger row's purpose, that the landing does not force a rewrite of the manifest's
reverse-dependants, is unaffected: the change is four lines and one comment, and
every other reverse-dependant stays import-only.

### F4 — the barred term at the manifest's S_5 missing-premise paragraph

**Severity:** BLOCKING (the owner has barred the term, the landing edits the
file, and the sentence also overclaims).
**File:** PROBE/`pgg_analysis_manifest.v:714-720`
(production `manifest/pgg_analysis_manifest.v:684-690`).

Current text, reasoning and exact replacement are given under question 8 above.

## SHOULD-FIX

### S1 — the capability vocabulary need not be widened

**File:** PROBE/`pgg_analysis_manifest.v:65`, `:325-327`, `:394-396`.

Revert `:65` to the production line:

```
(* information or endpoint marginal mixing.                                   *)
```

and delete the two capability lines at `:325-327` and `:394-396`. Both theorems
already appear where Row 2 puts its counterpart, under **bound or certificate**:
`biased_cut_mixing` at `:304-305` and `centi_cut_mixing` at `:367`. Reasoning
under question 2(b).

### S2 — the new capability lines put a carrier in the observer column

**File:** PROBE/`pgg_analysis_manifest.v:326`, `:395`.

The table header is `| theorem | distribution | observer | notion |`. Every
other line holds a reader in the third column (`colour_view A, executed`,
`one seat's endpoint distribution`, `content_trace R ord0, executed`,
`static_view`). The two new lines hold `the cut carrier {perm 'I_5}`, which is a
carrier and not an observer. Subsumed by S1 if the lines are dropped.

### S3 — `exec_transfer_status` no longer says which path

**File:** PROBE/`five_card_analysis.v:361-368` region.

The name is pinned by `manifest/pgg_analysis_client.v:48` and cannot be changed
without editing that file. F3 makes that file an edited file, so the constraint
is gone. Two options, in order of preference:

1. Add `Definition uniform_transfer_status : TransferStatus := StaticExecutedOnly.`
   beside it, pin it, use the honest name everywhere in the manifest prose, and
   leave `exec_transfer_status` in place with a docstring saying it is the
   earlier name of the same status. No file outside the facade changes.
2. Rename to `uniform_transfer_status` and update
   `manifest/pgg_analysis_client.v:48` in the same landing.

Either way the facade should carry three names that name their three paths.

### S4 — STATUS.md's code-hunk count contradicts its own table

**File:** PROBE/`STATUS.md:23` and `:249-259`.

The verdict row says "16 code hunks, of which 9 are import repoints and 7 are
the landing itself". The table in the same document sums to twenty:
1+1+1+1+1+1+4+6+4. Counted mechanically over `diffs/*.code.diff`: **twenty**
code hunks, and thirty-five with comments (which matches). Of the twenty, ten
are import hunks (six reverse-dependants with one each, the facade one, the
manifest one, the rows file two) and ten are the landing itself.

Replace "16 code hunks, of which 9 are import repoints and 7 are the landing
itself" with "20 code hunks, of which 10 are import repoints and 10 are the
landing itself", and the same numbers in the L9 section heading sentence at
`:246-247`.

### S5 — STATUS.md's statement about `psl211_endpoints` contradicts itself

**File:** PROBE/`STATUS.md:26` and `:73`, against `:19`.

`:19` says "`psl211_endpoints.v` is only loaded", which is right. `:26` says it
"is in none of their closures" and `:73` says it "is in no closure and was
never compiled". Recomputed: `instances/psl211/psl211_endpoints.vo` is in the
**forward** dependency closure of all nine existing production files of the
recompile set, through `instances/psl211/psl211_analysis.vo`, which the manifest
re-exports. It is in the **reverse** closure of none of them, which is the
invariant that matters and which holds.

Replace `:26` with: "Eleven production files recompile, as S10 predicted for
option 2, and `instances/psl211/psl211_endpoints.vo` is in the reverse closure
of none of them, so the landing never recompiles it." Replace the sentence at
`:73` with: "`instances/psl211/psl211_endpoints.v` is loaded through
`psl211_analysis` and recompiled by nothing the landing touches."

### S6 — the `_CoqProject` placement rule is unsatisfiable as written

Reasoning and the two exact insertion points are under question 6. The
implementation plan must also not prescribe compiling in `_CoqProject` order.

### S7 — the "Absent capabilities" opening clause

**File:** PROBE/`pgg_analysis_manifest.v:693-694`.

The landing weakens "names the premise it lacks" to "names what it lacks". Rows
1, 7 and 9 are `StaticExecutedOnly` and their missing-premise cells say "none",
"none is needed" and "none": they name nothing they lack. The clause was already
loose before the landing and stays loose after it. Since the landing rewrites
this exact line, carry the repair:

```
(* security capability, and every path whose transfer status is               *)
(* NoModelComparison or StaticExecutedOnly states in its missing-premise      *)
(* cell either the premise it lacks or why none is absent. The                *)
```

## NOTE

- **N1** `var_dist_le2` lands with no proof consuming it; it is cited in two
  docstrings of `five_card_rows.v` and printed in the fidelity file. Record the
  reason in the implementation plan so a later audit does not read it as dead.
- **N2** `instances/kim2025/five_card_kim.v:54` carries the same barred term,
  outside the landing's files.
- **N3** The comment box at PROBE/`pgg_analysis_manifest.v:714` is malformed in
  production (no padding before `*)`); the F4 replacement repairs it.
- **N4** The `biased_cut_mixing` pin reaches into `five_card_mixing.` while the
  `centi_cut_mixing` pin goes through a facade alias. Precedented, asymmetric.
- **N5** Rows 4 and 5 keep their observers cells unchanged, so the static
  coalition observation the transfer's conclusion is about appears in neither.
  If F1 and F2 are taken, consider adding it to Row 5's observers cell.
- **N6** SRC's recorded `Fail five_card_row_biased_inv25_rowE` does not land.
- **N7** The facade header counts "the two base premises" and enumerates three
  aliases.

---

## Scope of this audit

Not re-audited, by instruction: the mathematics of the lemmas copied from SRC,
which five SRC soundness audits cover. Not re-run: the compile, which the main
session reports at return code zero over twelve files with fifty-three
`Print Assumptions` blocks at the three `boolp` axioms and nine closed. No Rocq
process was started for this audit.
