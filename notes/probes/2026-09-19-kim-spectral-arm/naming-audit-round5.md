# Naming, style and statement-comment audit, round 5

NO-GO.

Scope: the one comment the fourth fix pass changed, the disposition of round
4's B4-1 to B4-4 and S4-1 to S4-4, every passage the fourth fix pass added to
or changed in `STATUS.md`, and the mechanical scans. Read-only with respect to
the compiler: no `rocq`, `coqc` or `make` was run, and no existing file was
edited. The five `.v` files, `STATUS.md` and `rename_map.tsv` were read at this
revision; `history/*.2026-09-19-before-fix4.*` were used only to isolate the
delta.

Two blocking findings, three should-fix, six notes. Neither blocking finding
disputes a proof, a statement or a number the kernel checks, and neither
disputes the substance of the fourth pass. Both are about the landing
material's own citations: one is a set of line numbers that the same pass made
stale by growing the file above them, the other is a reproducibility sentence
about a script that, as published, prints nothing.

I confirmed independently, with my own scripts, that the twenty-nine/sixteen/six
split is exact and that the dependency cone is 12, 13, 6 and union 17.

---

## 1. Blocking

### B5-1. Four self-citations added by this pass are two lines short, and the "correction" that produced two of them moved them the wrong way

`STATUS.md:974-975` and `STATUS.md:1972-1973`.

`:972-976` reads:

> Those eleven propositions are the ones found so far. The list of propositions
> is no more complete than the list of places, and it is open. The last four
> were added in round 4 from this document's own cells, `:589`, `:605`, `:606`
> and `:611`, each of which already records the proposition as falsified

None of the four cited lines is a cell that records one of the four
propositions. In this file as it stands, `:589` and `:605` are the header rows
`| line | text today | why a landing makes it false |` of the Row 4 and Row 5
tables, `:606` is the separator `|---|---|---|`, and `:611` is the cell
`| :361 | completion level | Sampled | becomes AnalysisBridged |`, which is a
fifth proposition and not one of the four.

The four cells that do record the four propositions are `:591` for
`:301-302`, `:607` for `:351-354`, `:608` for `:355` and `:613` for
`:374-380`. Every one of the cited numbers is exactly two short.

The cause is this pass itself. In
`history/STATUS.2026-09-19-before-fix4.md` those four cells sit at `:589`,
`:605`, `:606` and `:611`, so the citations were right when written. The same
pass then inserted one line at the front matter and one line at `:536-537`,
which pushed everything below by two.

The second locus is the consequence. `STATUS.md:1971-1973` reads:

> Line numbers the audits cite that the source does not bear, corrected while
> applying: I2's citations of this file's Row 5 cells are `:605` and `:606`,
> not `:606` and `:607`.

In the file this sentence sits in, the two Row 5 cells at issue are `:607` and
`:608`. I2's original `:606` and `:607` were themselves right for one of the
two against the pre-fix file. The recorded correction therefore replaced one
right number with a wrong one and left the other wrong, and it does so in the
paragraph whose stated purpose is fixing wrong line numbers.

Blocking because these are line citations in the landing material, and because
a citation into a file that the same pass is editing is the kind that goes
stale silently. Pinning the cells by content rather than by line removes the
failure mode instead of resetting it.

Fix, replacing `STATUS.md:973-976` from "The last four" to "as falsified":

> The last four were added in round 4 from this document's own Row 4 and Row 5
> cells for `manifest/pgg_analysis_manifest.v:301-302`, `:351-354`, `:355` and
> `:374-380`, each of which already records the proposition as falsified

Fix, replacing `STATUS.md:1972-1973` from "I2's citations" to "`:606` and
`:607`.":

> I2's citations of this file's Row 5 cells are to the rows for
> `manifest/pgg_analysis_manifest.v:351-354` and `:355`. Both this file's own
> line numbers for them and I2's have moved with the two lines this pass added
> above them, so the cells are named by their content and not by line.

### B5-2. "the script as published reproduces the output below" is false: the published script prints nothing

`STATUS.md:1360-1361`, inside the paragraph this pass added above the cone
script, and the code block at `STATUS.md:1368-1443`.

`:1357-1361` reads:

> The five `.glob` files beside this probe were regenerated from the current
> sources on 2026-09-19, in `_CoqProject` order, each compile returning 0, and
> the script as published reproduces the output below against them.

The published code block ends at `:1442` with `    return seen`. It defines
`decls`, `spans`, `refs`, `edges`, `above_hits` and `closure`, and contains no
statement that prints anything and no call to `closure`. Run as published,
with `G` pointed at this directory, it exits 0 and emits nothing. It cannot
reproduce the block at `:1447-1508`.

The computation underneath is right, and I verified it. Taking the published
block verbatim, substituting this directory for the `G` placeholder and
appending a driver that calls `closure` on the three theorems, I get
`declarations found: 56`, cones of 12, 13 and 6 in the same member order as
`:1450-1485`, a union of 17 with the same members as `:1487-1504`, and zero
references above the facade, matching `:1506-1507`. So the `.glob` files do
match the current sources and round 4's B4-1 is genuinely closed on the
mathematics. What is not closed is the reproducibility claim that B4-1 was
about, and S8's "How a landing batch must rebuild this list" is the section
that sends a landing engineer to run this.

Fix, the smaller of the two: append to the code block, immediately before the
closing fence at `:1443`:

```python

roots = ["kim_centi_cut_mixing", "kim_biased_cut_mixing",
         "five_card_static_obs_const"]
print("declarations found:", len(decls))
union = set()
for r in roots:
    c = closure(r)
    union |= c
    print("\n=== cone of %s: %d probe-local declarations ===" % (r, len(c)))
    for n in [n for f in FILES for (_a, _b, n) in spans[f] if n in c]:
        print("    %-34s %s" % (n, decls[n][0] + ".v"))
print("\n=== union of the three cones: %d ===" % len(union))
for n in [n for f in FILES for (_a, _b, n) in spans[f] if n in union]:
    print("    %-34s %s" % (n, decls[n][0] + ".v"))
hits = set()
for r in roots:
    for n in closure(r) | {r}:
        hits |= above_hits[n]
print("\n=== references above the facade, inside the three theorems and "
      "their cone ===")
print("    " + ("none" if not hits else "\n    ".join(sorted(hits))))
```

That driver produces the block at `:1447-1508` line for line against the
current `.glob` and `.v` files, so the sentence at `:1360-1361` then holds as
written and needs no change.

---

## 2. Should fix

### S5-1. The changed comment attributes the covering to both quantifiers and then concedes it happens at one bias, and its middle clause reads as a derivation the file does not make

`five_card_rotation_probe.v:90-95`, the statement comment of
`fc_kim_rho_supp_pow`.

Current text:

```
(* Every cut the weighted word shuffle gives mass to is a power of the
   five-cycle, at every word length and every letter weighting. The two
   quantifiers together are what let one statement cover all of Kim's cut
   laws, the length one reaching the seven-cut law from the one-cut law at
   one bias, so each of them and the uniform rotation law live on one group
   and a variation distance between them is a distance on that group. *)
```

Clause by clause against the lemma at `:96-99`. The first sentence is true:
the hypothesis is `@rho_from_words_weighted R 3 4 L fc_kim_gens W g != 0` with
`L` and `W` universally quantified and the conclusion is
`exists k : nat, g = (fc_sigma ^+ k)%g`. The closing clause is true and is the
position the spectral arm needs. Two defects sit between them.

First, "The two quantifiers together are what let one statement cover all of
Kim's cut laws" claims both quantifiers do the covering, and the appositive
that follows says the covering runs "at one bias", which is to say the
weighting quantifier is held fixed while it happens. Every Kim cut law this
development carries is at bias `1/100`: `kim_single_cut_supp_pow` (`:145-149`)
instantiates `@fc_kim_security_bundle R (1 / 100) (kim_centi_lt R)
(kim_centi_gt R) (kim_centi_spec R) 1`, `kim_centi_cut_supp_pow` (`:154-157`)
instantiates `kim_security_bundle_centi R`, which is the same bundle at `L = 7`
(`instances/kim2025/five_card_kim.v:640-641`), and the third law in the probe,
`kim_biased_marginal_bound_exact` (`kim_spectral_rows_probe.v:318-323`), names
`kim_weight_dist (kim_centi_lt R) (kim_centi_gt R)` outright. The sentence is
true only if "all of Kim's cut laws" means Kim's family at every bias, which
the comment nowhere says, and false under the reading a reader of this file
will take. This is round 4's B4-4 half-corrected: the covering quantifier was
named right in the appositive and the wrong attribution was left in the main
clause.

Second, "the length one reaching the seven-cut law from the one-cut law" reads
as the seven-cut law being obtained from the one-cut law. It is not. Both
corollaries are proved directly from the lemma by `exact:
fc_kim_rho_supp_pow` (`:149` and `:157`), and neither mentions the other.

Everything else the rule asks for is present. The fact comes first, the
position second, and there is no proof narration, no pointer to a sibling
declaration by name and no status word. All six lines are inside 80 bytes.

Fix, replacing `five_card_rotation_probe.v:90-95`:

```
(* Every cut the weighted word shuffle gives mass to is a power of the
   five-cycle, at every word length and every letter weighting. Both
   quantifiers are Kim's: the bias fixes the letter weighting and the number
   of cuts fixes the word length. The two Kim cut laws this development
   carries share the bias one hundredth and differ only at word lengths one
   and seven, so each of them and the uniform rotation law live on one group
   and a variation distance between them is a distance on that group. *)
```

Longest line is 77 bytes.

### S5-2. "One `.v` character changed in this pass"

`STATUS.md:1950`.

The sentence is

> One `.v` character changed in this pass, the statement comment of
> `fc_kim_rho_supp_pow`.

The appositive names a comment, and a comment is what changed: five lines of
comment text were rewritten and `five_card_rotation_probe.v` grew from 7601 to
7672 bytes. The noun is the wrong one and the sentence is false as written.
The next sentence, "Comments stripped, the five files are byte-identical to
their `before-fix4` copies", is the true one and I confirmed it: stripping
nested `(* ... *)` and comparing token streams, all five files are identical
to their `before-fix4` copies.

Fix, at `STATUS.md:1950`: "One `.v` comment changed in this pass, the
statement comment of `fc_kim_rho_supp_pow`."

### S5-3. The seven-category summary of the twenty-nine does not reach three of them

`STATUS.md:1191-1195`.

> Twenty-nine declarations stay above, enumerated under option 2 below. They
> are the certificates, the row programs, the lemmas that read off their
> published fields, the repricing definitions and identities, the two
> bundle-number lemmas, the one-cut per-card-position bound and the two form-2
> mixing statements.

Read narrowly, the seven categories cover 4 + 4 + 8 + 5 + 2 + 1 + 2 = 26 of the
twenty-nine. The three they miss are `kim_biased_sample_cut_witnessE`, which
is a tying field and not a certificate, and `kim_centi_marginal_bound40` and
`kim_biased_marginal_bound_exact`, which are `ShuffleMarginalBound` values and
not certificates either. The enumeration at `:1252-1274` names all three
explicitly, and the S10 table row at `:1160` groups them as "the remaining
bounds and the certificates", so "the certificates" here can be read as a
shortening of that row. Not blocking for that reason, but it is the shape S4-4
was raised about and a count-bearing sentence should carry its own arithmetic.

Fix, replacing `STATUS.md:1192-1195` from "They are" to "mixing statements.":

> They are the four certificates with the tying field and the two form-2
> marginal bounds, the four row programs, the eight lemmas that read off the
> certificates' numbers and the rows' published fields, the two repricing
> identities and the three repricing definitions and bounds, the two
> bundle-number lemmas, the one-cut per-card-position bound and the two
> form-2 mixing statements.

---

## 3. Notes

| ID | Location | Observation |
|---|---|---|
| a | `STATUS.md:613` and `:969` | The same manifest passage is quoted two ways in one document, "A ShuffleCertificateBundle exists for both models and does not raise the level." at `:613` and "A ShuffleCertificate-Bundle ..." at `:969`. The source hyphenates across `manifest/pgg_analysis_manifest.v:379-380`, so `:969` is the literal quote and `:613` is the reading. Round 4's note c accepted the reading. One spelling per quotation would read better. |
| b | `STATUS.md:753-756` against `:1965` | The body calls three of the nine "sampler `Check`s" as though they were not spelled-type, and the disposition row calls all nine spelled-type. All nine do spell the type: `:1177`, `:1182` and `:1187` are each `Timeout 60 Check (FiveCardAnalysis.<name> : forall ...)`. No count is affected. |
| c | `STATUS.md:1258` | "their eight number and published-field lemmas" attaches to the four row programs, but five of the eight, `kim_centi_cert_epsE`, `kim_centi_cert_eps_lt`, `kim_biased_cert_epsE`, `kim_biased_cert_eps_lt2` and `kim_centi_cert40_epsE`, read off certificates and not rows. The eight named are the right eight. |
| d | `STATUS.md:70-76` and `:1979-1981` | Two compile-time records, 4.5/4.2/5.4/4.2/10.9 for the third pass and 4.4/4.2/5.4/4.2/10.9 for this one. Both are disclosed as separate runs and neither can be checked in a round that runs no compiler. Recorded as unverified, not as wrong. |
| e | `five_card_sc_const_probe.v:46`, `:91` | `Section five_card_static_obs_const` still encloses `Lemma five_card_static_obs_const`. Open since round 2 and deliberately not applied by two passes that changed comments only. Still a one-line edit for the landing. |
| f | `STATUS.md:1952` | "all five recompile with return code 0" cannot be checked here. The indirect evidence is strong: the five `.glob` files are newer than every `.v` file, and the published script's byte offsets resolve against the current sources, giving 56 declarations and cones of 12, 13 and 6. A stale `.glob` collapses those to 0, 1 and 6, as round 4 measured. |

---

## 4. Checked and found correct

**The twenty-nine, the sixteen and the six, recomputed independently.** My own
script over the five `.v` files, stripping nested comments and matching
top-level `Definition`, `Lemma`, `Theorem`, `Fact`, `Corollary` and `Fail`
forms, finds 56 declared identifiers, 5 of them recorded `Fail`s, so 51 real
declarations. `var_dist_injective_probe.v` holds 7, one of them a `Fail`, so 6
generic. The sixteen listed at `:1242-1248` as moving are exactly the 9 of
`five_card_rotation_probe.v`, the 3 of `five_card_sc_const_probe.v` and 4 of
the 6 of `kim_sc_close_probe.v`. That leaves 29, and the 29 named at
`:1252-1274` are that set exactly, name for name, with no member missing and
none added. The four recorded `Fail`s of `kim_spectral_rows_probe.v` are
correctly excluded from the count, and the fifth `Fail`,
`var_dist_const_reader_mutation` (`var_dist_injective_probe.v:123`), is in the
generic file.

**The dependency cone.** Reproduced against the current `.glob` and `.v` files:
12 for `kim_centi_cut_mixing`, 13 for `kim_biased_cut_mixing`, 6 for
`five_card_static_obs_const`, union 17, same members and same order as
published, and zero references into `pgg_analysis_manifest`,
`pgg_analysis_status`, `pgg_tableau`, `pgg_tableau_syntax`,
`five_card_analysis` or `five_card_rows`. Thirteen instance-specific plus the
three theorems is sixteen, and the S10 table carries fourteen daggered rows,
twelve naming one declaration and two naming two.

**Option 2, described the same way everywhere.** The recompile figures agree at
every occurrence: 9 at `:1212`, `:1317` and `:1593`; 10 at `:1212`, `:1318` and
`:1643`; 11 at `:1310`, `:1319`, `:1609` and `:1644`; 18 and 19 at `:1123` and
`:1649-1650`. What moves is described identically at `:1131`, `:1189-1191` and
`:1241-1249`. What stays is the S5-3 wording above and the exact enumeration.

**B4-2.** Applied and true. `kim_centi_cert`'s mixing field is
`@kim_centi_cut_mixing R` (`kim_spectral_rows_probe.v:73`) and
`kim_biased_cert`'s is `@kim_biased_cut_mixing R` (`:87`); both take
`@five_card_static_obs_const R` as the constancy field (`:74`, `:88`), so
"the constancy field they share" is right. Three theorems now matches the
"three aliases" at `:662` and `:721-722`.

**B4-3.** Applied and true. `instances/kim2025/five_card_rows.v:338` is
`five_card_row_uniform_tableau` and its `publish` step at `:342` writes
`StaticExecutedOnly`; `publish` takes a `StackAt AnalysisBridged` and writes
`AnalysisBridged` into the row (`manifest/pgg_tableau.v:691-695`), so "fixes
`AnalysisBridged` through it" holds. `:347` is `five_card_row_uniform_rowE`,
`Proof. by []. Qed.` The narrower universal survives the two nearest
candidates: `five_card_row_repeated_modelE` (`:441`) and
`five_card_row_biased_modelE` (`:447`) name the manifest's two rows but only
their `apr_model` field, and the two `prefixE` lemmas mention `Sampled` only as
the programs' own index.

**B4-4.** Applied, with the residue at S5-1.

**S4-1.** Verified line by line in `manifest/pgg_analysis_manifest.v`. The five
spelled-type `Check`s open at `:1207` `single_cut_distE`, `:1214`
`repeated_cut_distE`, `:1221` `repeated_seat_distE`, `:1233` `centi_cut_distE`
and `:1245` `centi_repeated_seat_distE`; the seven name occurrences are at
`:1210`, `:1217`, `:1225`, `:1229`, `:1235`, `:1248` and `:1253`; the three
sampler `Check`s open at `:1177`, `:1182` and `:1187`. With
`instances/kim2025/five_card_analysis.v:402` that is nine `Check`s at eleven
lines, and eight of the nine are in the manifest, as the text now says.

**S4-2.** `manifest/pgg_analysis_manifest.v:753` ends with the word "reaching"
and the clause "the development supplies no ideal-distribution equality" lies
in `:754-755`. The H1 disposition row at `:1897` carries the same `:753-755`.

**S4-3.** The superseded paragraph is at
`history/STATUS.2026-09-19-before-fix3.md:680-685`. It names seven
declarations outright plus "its `rowE`", and covers four more by the suffixes
`prefixE` and `modelE`, which is twelve of the twenty-six.

**I1.** The replacement universal holds. The four certified programs sit at
`kim_spectral_rows_probe.v:100-104`, `:110-114`, `:284-289` and `:360-366`,
each a full chain from `five_card_committed`. Every `certify`,
`certify_spectral` and `certify_exact` chain in `instances/` starts from its
own instance's prefix: `pgl27_dealt` (`instances/pgl27/pgl27_rows.v:270`,
`:295`, and the further chains at `:312`, `:381`, `:392`, `:421`, `:438`,
`:479` and `:499`), `s5_supplied` (`instances/s5/s5_rows.v:275`),
`psl211_alldecks_prefix` (`instances/psl211/psl211_rows.v:175`) and
`five_card_committed` (`instances/kim2025/five_card_rows.v:338`). All four
prefixes are `Tableau Observed` (`pgl27_rows.v:124`, `s5_rows.v:166`,
`psl211_rows.v:126`, `five_card_rows.v:175`), and `Observed` precedes
`Sampled` in `CompletionLevel` (`manifest/pgg_analysis_status.v:60-61`).
T0 is at `notes/20260919-tableau-three-extensions-probe-design.md:169`.

**I2.** The four added propositions and their manifest citations all hold:
`:301-302` is `bound or certificate | none; kim_leak_bound is the numeric
constant of the bridge theorem, not a shuffle certificate`, `:351-354` is the
four-entry bound-or-certificate list, `:355` is `final bridge theorem | NONE`,
and `:379-380` is the sentence about the existing bundle. The bullet list holds
seven items before them and eleven after, as `:972` says. The wrong citations
are the pointers back into this document, which are B5-1.

**I6.** `instances/kim2025/five_card_rows.v:383-389` is the docstring of
`five_card_row_repeated_tableau`, and `:384` begins "The program stops at
Sampled, the level the manifest records for this row", quoted exactly.

**Vocabulary.** "card position" throughout for an `'I_5` index into the deck,
"seat" only for a coalition member, "reading" for a coalition's observation,
"pow" as the support suffix, "constancy" for the fifth field of `SpectralCert`.
The one comment this pass changed keeps all of them.

**Mechanical.** Zero lines over 80 bytes in the five `.v` files. Zero
whole-word hits for any of the nine forms on the owner's banned-vocabulary
list in the five `.v` files, `STATUS.md` and `rename_map.tsv`, scanned with
Python `re` and `\b`, case-insensitive. Zero whole-word hits, in the same
files, for the two-character spelling the owner bars for the sum of absolute
differences. Comments stripped, all five `.v` files are identical to their
`before-fix4` copies.
