# Naming, style and statement-comment audit, round 4

NO-GO.

Scope: the one comment the third fix pass changed, the disposition of round 3's
B-1 to B-4 and S-1 to S-6, every file:line and every count the third fix pass
added to `STATUS.md`, `STATUS.md`'s internal consistency as the seed of a
landing plan, and the mechanical scans. Read-only with respect to the compiler:
no `rocq`, `coqc` or `make` was run, and no existing file was edited. The five
`.v` files and `STATUS.md` were read at this revision; the pre-fix copies in
`history/*.2026-09-19-before-fix3.*` were used only to isolate what this pass
added.

Four blocking findings, four should-fix, six notes. None of them disputes a
proof, a statement or a number the kernel checks. The cone computation that
B-2 asked for is mathematically right, and I reproduced it independently; what
is broken is its reproducibility from the artifact as published.

---

## 1. Blocking

### B4-1. The dependency-cone script does not reproduce its own output against the files it points at

`STATUS.md:1257-1396`, the subsection "The dependency cone of the three
theorems".

The script is published with

```python
G = "<directory holding the five .v files and their .glob files>"
```

and is followed by `Output:` and the cones 12, 13, 6 and union 17. Pointed at
this directory as it now stands, the script prints cones of **0, 1 and 6 and a
union of 7**.

The cause: the `.glob` files were written at 08:59 from the pre-deletion
`kim_sc_close_probe.v`. This pass deleted line 21 at 09:21, shortening that
file by 64 bytes, so every glob byte offset into it is now misaligned with the
source. The script reads offsets from the glob and line boundaries from the
`.v`, so the two no longer agree. Copying the five
`history/*.2026-09-19-before-fix3.v` beside the same globs reproduces the
published 12, 13, 6 and 17 exactly, which is where the published output came
from.

The result itself is right. I recomputed the cone from the current sources by a
method that does not use the globs at all, by taking each declaration's source
span between its own line and its `Qed`/`Defined`/`Admitted` or the next
top-level command, stripping comments, and closing over whole-word references.
That gives 12, 13, 6 and union 17, the same thirteen instance-specific
declarations and the same four generic ones. The deleted line is a `Require`
that no declaration references, so the cone is unchanged by the deletion.

Blocking because S8's own "How a landing batch must rebuild this list" tells a
landing batch to redo the mechanical work. A landing engineer re-running this
script as published gets a seven-element union, concludes the option-2 cone is
seven declarations plus the three theorems, and lands a file that does not
compile.

Fix: insert one sentence immediately after "Without that cut `var_dist_le2` and
`var_dist_fdistmap_const_neq` appear in the constancy cone, and they are not in
it." (`STATUS.md:1255-1256`):

> The `.glob` files in this directory were written before this revision deleted
> the dead `Require` from `kim_sc_close_probe.v`, so their byte offsets match
> the `history/*.2026-09-19-before-fix3.v` copies and not the current sources.
> The output below was produced against those copies. Reproducing it needs
> them, or a recompile of the five files. The deleted line is a `Require` that
> no declaration references, so the cone is the same either way.

### B4-2. Two sentences of the facade list give section 7 two theorems and three aliases

`STATUS.md:694-695` and `STATUS.md:716-717`. Both were added by this pass.

`:692-695` reads:

> The section header at `:351-358` becomes false. The constancy field is the
> ideal distribution equality that discharges the second hypothesis, and the
> mixing field is the cut-carrier bound the first asks for, so the section
> has two theorems to alias.

`:715-718` reads:

> The file header at `:16-17` ... becomes false under option 2, where section 7
> gains three aliases.

These cannot both be true. `STATUS.md:1145-1146` states the count itself: "The
three theorems at issue are `kim_centi_cut_mixing`, `kim_biased_cut_mixing` and
`five_card_static_obs_const`." There are two mixing theorems and one constancy
theorem, so section 7 has three theorems to alias. Item 1 counts fields, of
which there are two, and reports them as theorems.

Fix, replacing `STATUS.md:692-695` down to "to alias.":

> The section header at `:351-358` becomes false. The constancy field is the
> ideal distribution equality that discharges the second hypothesis, and the
> mixing field is the cut-carrier bound the first asks for, so the section has
> three theorems to alias: `kim_centi_cut_mixing` and `kim_biased_cut_mixing`
> for the two models' mixing fields, and `five_card_static_obs_const` for the
> constancy field they share.

### B4-3. "None of them mentions a manifest row's level or transfer status" is false

`STATUS.md:889-890`, the closing sentence of B-4's rewritten enumeration.

Two of the twenty-six declarations it covers do mention one.

`five_card_row_uniform_tableau` (`instances/kim2025/five_card_rows.v:338-342`)
ends its body with `|> publish StaticExecutedOnly BaselineClassicalOnly.`
`StaticExecutedOnly` is a constructor of `TransferStatus`
(`manifest/pgg_analysis_status.v:72`), and `publish` takes a
`StackAt AnalysisBridged` (`manifest/pgg_tableau.v:691-696`), so the
declaration fixes a completion level as well. Its docstring at `:331-337` says
so in prose: "publishes a row whose transfer status is StaticExecutedOnly".

`five_card_row_uniform_rowE` (`:347-349`) equates
`published_row five_card_row_uniform_tableau` with the manifest row
`five_card_row_uniform` by conversion, which pins that row's level and status
without naming either.

The conclusion the sentence supports survives, because both are about the
uniform row and a spectral landing restatuses only the biased and the repeated
rows. The reason given for it does not. This is the failure mode the round
exists to catch, one level over from B-2: the list of what moves was rebuilt,
and the reason given for what stays was not checked against the source.

Fix, replacing `STATUS.md:889-890` "None of them mentions a manifest row's
level or transfer status.":

> None of them mentions the biased or the repeated row's level or transfer
> status. Two mention the uniform row's: `five_card_row_uniform_tableau`
> (`:338`) writes `StaticExecutedOnly` into its `publish` step and fixes
> `AnalysisBridged` through it, and `five_card_row_uniform_rowE` (`:347`) pins
> the manifest's `five_card_row_uniform` by conversion. A spectral landing
> leaves the uniform row alone, so both stay true.

### B4-4. The changed comment names the wrong quantifier as the one that covers Kim's cut laws

`five_card_rotation_probe.v:90-95`, the statement comment of
`fc_kim_rho_supp_pow`.

The text is round 3's S-2 replacement used verbatim, character for character,
so the fix pass applied the audit faithfully. The defect is in the audit's own
wording, which no one checked against the two corollaries that sit forty lines
below it.

The second sentence reads "The quantifier over the weighting is what lets one
statement cover all of Kim's cut laws". The two Kim cut laws this file derives
from the lemma instantiate the same weighting and differ only in word length.
`kim_single_cut_supp_pow` (`:145-149`) uses
`@fc_kim_security_bundle R (1 / 100) (kim_centi_lt R) (kim_centi_gt R)
(kim_centi_spec R) 1`, and `kim_centi_cut_supp_pow` (`:154-157`) uses
`kim_security_bundle_centi R`, which is
`@fc_kim_security_bundle R (1 / 100) kim_centi_lt kim_centi_gt kim_centi_spec 7`
(`instances/kim2025/five_card_kim.v:640-641`). The bundle's law is
`rho_from_words_weighted R 3 4 L fc_kim_gens W` with
`W := kim_weight_dist eps_lt eps_gt` (`five_card_kim.v:371`), so at one bias
the two share `W` and differ in `L` alone. The quantifier doing the covering in
this file is the one over the word length.

Everything else about the comment is right. It carries no proof narration, no
pointer to a sibling declaration and no status word, which is what S-2 asked
for, and the first sentence is true of the lemma at both quantifiers.

Fix, replacing `five_card_rotation_probe.v:90-95`:

```
(* Every cut the weighted word shuffle gives mass to is a power of the
   five-cycle, at every word length and every letter weighting. The two
   quantifiers together are what let one statement cover all of Kim's cut
   laws, the length one reaching the seven-cut law from the one-cut law at
   one bias, so each of them and the uniform rotation law live on one group
   and a variation distance between them is a distance on that group. *)
```

Every line is inside 80 bytes.

---

## 2. Should fix

### S4-1. Ten occurrence lines are reported as ten `Check`s

`STATUS.md:747-749` and `:753-754`.

The ten cited lines are ten occurrences of the searched names inside **eight**
`Check` commands. `:1177`, `:1182` and `:1187` each open their own;
`:1210`, `:1217`, `:1225`, `:1229`, `:1235`, `:1248` and `:1253` are
continuation lines of `Check`s opened at `:1207`, `:1214`, `:1221`, `:1221`,
`:1233`, `:1245` and `:1245`. Adding the facade's `:402` gives nine `Check`s at
eleven lines, not eleven `Check`s. Every cited line is a real occurrence inside
a spelled-type `Check`, and the paragraph's conclusion is unaffected, which is
why this is not blocking.

Fix, at `:747-749`: "...and seven more occurrences inside five spelled-type
`Check`s in `manifest/pgg_analysis_manifest.v`, opened at `:1207`, `:1214`,
`:1221`, `:1233` and `:1245`, with the names at `:1210`, `:1217`, `:1225`,
`:1229`, `:1235`, `:1248` and `:1253`, beside the three sampler `Check`s at
`:1177`, `:1182` and `:1187`."

And at `:753-754`: "The previous form of this sentence reported one spelled-type
`Check` where the search returns nine, at eleven lines,".

### S4-2. The `five_card_row_uniform` docstring quote starts one line before its citation

`STATUS.md:637`. The range cited is
`manifest/pgg_analysis_manifest.v:754-755`; the quoted text begins with
"reaching", which is the last word of `:753`. The clause a landing falsifies,
"the development supplies no ideal-distribution equality", is entirely inside
`:754-755`, so the citation finds the passage.

Fix: `manifest/pgg_analysis_manifest.v:753-755`.

### S4-3. "named nine declarations out of the twenty-six" is neither count

`STATUS.md:891-892`. The previous form of that paragraph named eight
declarations individually, `five_card_row_repeated_endpoint_lt`,
`kim_centi_small`, `five_card_row_biased_leak_bound`,
`five_card_row_uniform_tableau`, its `rowE`, `five_card_exact_view_secrecy`,
`five_card_committed_paramsE` and `Fail five_card_row_s5_family`, and covered
four more by suffix, the two `prefixE` and the two `modelE`. Twelve of the
twenty-six, eight by name.

Not blocking: the count describes a superseded revision of this document, not
the source, and a landing acts on neither.

Fix: "and covered twelve declarations out of the twenty-six, eight by name and
four by suffix."

### S4-4. Option 2's "keeps only" under-enumerates by ten declarations

`STATUS.md:1140-1141` ("Only the certificates, the row programs, the lemmas
that read off their published fields and the two repricing identities stay
above") and `STATUS.md:1195-1199` ("`instances/kim2025/five_card_rows.v` keeps
only the certificates, the four row programs, their `epsE`, `eps_lt`,
`publishedE` and `rowE` lemmas, and the two repricing identities
`five_card_pow2_39_split` and `five_card_inv50_split`").

Fifty-one real declarations, six generic and sixteen moving, leaves
twenty-nine above. Ten of them fall outside both enumerations:
`kim_biased_epsE`, `kim_biased_exact_le_eps`, `kim_centi_marginal_bound40`,
`kim_centi_cut_mixing40`, `five_card_reprice39`, `kim_one_cut_centi_le`,
`kim_biased_marginal_bound_exact`, `kim_biased_cut_mixing_exact`,
`five_card_reprice_inv25` and `five_card_reprice_inv25_lt2`. Two of those,
`kim_centi_cut_mixing40` and `kim_biased_cut_mixing_exact`, are mixing
statements, which a reader of the S10 table's "the two mixing fields †" row
would expect to travel with them.

I checked the direction that would have been fatal and it is clean: nothing in
the moving sixteen references anything that stays, so option 2 is not a cycle.

Fix, appended to `STATUS.md:1199` after "`five_card_inv50_split`.":

> It also keeps the alternative-pricing bounds and their mixing lemmas,
> `kim_centi_marginal_bound40`, `kim_centi_cut_mixing40`,
> `kim_biased_marginal_bound_exact` and `kim_biased_cut_mixing_exact`, the two
> number lemmas `kim_biased_epsE` and `kim_biased_exact_le_eps`,
> `kim_one_cut_centi_le`, and the three repricing definitions
> `five_card_reprice39`, `five_card_reprice_inv25` and
> `five_card_reprice_inv25_lt2`: twenty-nine declarations in all.

---

## 3. Notes

| ID | Location | Observation |
|---|---|---|
| a | `STATUS.md:720-721` | "a spelled-type `Check` in the manifest's five-card section beside `:1385-1389`". Those two lines are `erefl` status pins; the manifest's spelled-type five-card `Check`s are at `:1177-1253`. Putting a new spelled-type `Check` beside the section-7 pins is a defensible placement, so no change is required, but the sentence reads as if `:1385-1389` were spelled-type `Check`s. |
| b | `STATUS.md`, the B1 disposition row | Calls `reconstruct/s5_nogo.v:53` "the only other 'constancy' in the tree". Two further occurrences, capitalized, are at `instances/pgl27/pgl_leakage_targets.py:39` and `:233`; both are about a collision ratio across orbits and neither names this field. "In the tree" reads naturally as the `.v` sources, so no change is needed. |
| c | `STATUS.md:562`, the Row 5 cell | Quotes `A ShuffleCertificateBundle exists for both models and does not raise the level.` The source hyphenates the identifier across the line break, `ShuffleCertificate-` at `:379` and `Bundle` at `:380`. A reading of the source, not a literal quote. |
| d | `STATUS.md:68-76` | The five added compile times, 4.5 s, 4.2 s, 5.4 s, 4.2 s and 10.9 s, and the 6.16 s to 5.4 s move, cannot be checked in a round that is read-only with respect to the compiler. Recorded as unverified, not as wrong. |
| e | `five_card_sc_const_probe.v:46`, `:91` | `Section five_card_static_obs_const` still encloses `Lemma five_card_static_obs_const`. Open since round 2, deliberately not applied by a pass that fixed its code changes in advance. Still a one-line edit for the landing. |
| f | `kim_sc_close_probe.v:33`, `:141` | `five_card_cut_mixing`, rename_map's right-hand value for `five_card_sc_close`, is a `Section` name and not a lemma. Consistent with the map; no change. |

---

## 4. Checked and found correct

**The changed comment.** `five_card_rotation_probe.v:90-95` is round 3's S-2
replacement verbatim, character for character. It carries no proof narration,
no pointer to a sibling declaration and no status word, so S-2's stated defect
is fixed. Its first sentence is true of the lemma at both quantifiers. The
second sentence is B4-4 above.

**The deleted import falsifies no comment.** No comment in
`kim_sc_close_probe.v` mentions the manifest or the analysis status. The only
probe file whose comments discuss the manifest is `kim_spectral_rows_probe.v`,
whose `Require` at `:21` is live and untouched.

**Vocabulary.** "card position" throughout for an `'I_5` index into the deck,
with bare "position" only after it inside the same comment; "seat" only in
`five_card_sc_const_probe.v:38,53,85,86` and only for a coalition member, which
is a `pi_starts` index; "reading" consistently for a coalition's observation;
"pow" as the support suffix; "constancy" for the certificate's fifth field.
`sc_const` is confirmed as the fifth field of `SpectralCert`
(`manifest/pgg_tableau.v:131-142`, the field itself at `:138`), and the record's
own docstring at `:127` says "Five fields".

**B-1.** The replacement matches the fifteen-row table at `STATUS.md:1009-1025`
exactly: `psl211_endpoints` is in the closures of the first four rows and of
none of the other eleven, and the four are the four the table marks **YES**.

**B-2.** The cone is right. Recomputed from the current sources independently of
the globs: 12, 13 and 6, union 17, the same thirteen instance-specific
declarations and the same four generic ones, `var_dist_fdistmap_supp_inj`,
`fdistmap_inj_uniform_id`, `fdistmap_neq0_codom` and `card_tnth_count`.
Thirteen plus the three theorems is sixteen, and the S10 table carries fourteen
dagger rows, twelve naming one declaration and two naming two, which is
sixteen. The option-2 description of what MOVES is the same in all three places
it appears: the S10 table's dagger note, "Their proofs do not travel alone",
and "What the new file holds is the whole cone". The reproducibility of the
script is B4-1 and the description of what STAYS is S4-4.

**B-3.** 133 `.v` files across the twelve production directories, counted:
5 + 12 + 3 + 14 + 4 + 16 + 9 + 11 + 11 + 28 + 15 + 5. The row definitions at
`:768` and `:778` are the lines the searched names occur on, and those lines do
carry the status, so the citation is right for the grep result it reports. The
three bare `Check`s at `pgg_analysis_client.v:41,43,44` are right: `:42` is
`uniform_family`, which is not one of the five searched names. The `Check` count
is S4-1.

**B-4.** The enumeration is exact. `instances/kim2025/five_card_rows.v` holds
28 `Definition`, `Lemma` and `Theorem` commands, 10 + 17 + 1, and 3 recorded
`Fail`s at `:409`, `:473` and `:571`, with zero `Corollary`, `Fact` or
`Example` to adjust for. All twenty-four line citations in the "other
twenty-four" list hold the named declaration, as do `:390`, `:401`, `:456`,
`:465` and `:473`. The file has two `prefixE` lemmas, not three. The closing
sentence is B4-3.

**S-1 to S-6.** All six applied as round 3 asked. S-1's "nine sites in six
files" plus `s5_nogo.v:53` as a tenth occurrence is exactly what a whole-tree
grep of the `.v` sources returns. S-2 is verbatim. S-3's narrower claim is
true. S-4 now matches the G1 row. S-5 no longer says the kernel rejects an
`erefl` that `Qed`s. S-6's added closing quote is at `:379-380` as claimed.

**External documents.** All four citations verify:
`notes/20260919-kim-tableau-sampled-design.md:38` is decision 2 and `:35-37`
is decision 1 ending "The row stops at `Sampled`";
`docs/superpowers/plans/2026-09-19-kim-tableau-sampled.md:35` is construction
choice 4; row T0 is at
`notes/20260919-tableau-three-extensions-probe-design.md:169`;
`soundness-audit.md:336-337` is the ceiling caution.

**Names.** Every identifier `STATUS.md` attributes to the probe exists in the
five files or in `rename_map.tsv`'s right-hand column. The one apparent
exception, `five_card_row_biased_spectral_tableau` at `STATUS.md:1682`, is
pre-existing text whose own sentence says the name "appears nowhere".

**Completeness claims.** The landing list's new standing is carried
consistently. No sentence added by this pass claims the list is complete; the
three places that could have, the S8 row of the verdict table, the section
heading and the S10 preamble, each say the opposite.

**Mechanical.** Zero lines over 80 bytes in the five `.v` files. Zero hits for
the banned vocabulary in the five `.v` files, `STATUS.md` and
`rename_map.tsv`. Fifty-six declared identifiers, including the five recorded
`Fail` names, scanned whole-word with Python `re` over the twelve production
directories, `legacy/`, `~/Projects/coq/_opam/lib/coq/user-contrib` and the
other probe directories: no collision.
