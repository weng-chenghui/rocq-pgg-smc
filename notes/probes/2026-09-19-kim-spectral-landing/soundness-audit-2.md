# Second soundness audit of the Kim spectral landing probe, after fix pass 1

**NO-GO** for "these landing copies, with the import rewrite STATUS.md lists,
may be copied into the permanent tree".

Date: 2026-09-19. Independent adversarial audit, second round. The auditor
wrote none of what is audited and did not write `soundness-audit.md` or
`naming-audit.md`. One Rocq compile was run, a four-question conversion probe
in `audit-soundness-2/`; nothing else was compiled and no file outside
`soundness-audit-2.md` and `audit-soundness-2/` was written.

PROBE = `notes/probes/2026-09-19-kim-spectral-landing/` at commit `907d819`.
Line numbers are PROBE line numbers unless a path is given.

Three blocking findings. Two are one defect seen from two sides: the fix pass
gave rows 4 and 5 a bridge theorem stated at an observer neither row declares,
and wrote a sentence asserting the opposite. The third is that the "Import
rewrite at cp time" table, which the verdict is explicitly conditioned on, is
wrong for three of the nine copies and its exhaustiveness claim is false.

The mathematics of the two new corollaries is right, their statements say
nothing beyond what is proved, the four fidelity lemmas do what STATUS says
they do, and every first-round finding but one is closed.

---

## Findings

| ID | Severity | Quoted content | Evidence | Replacement |
|---|---|---|---|---|
| G1 | BLOCKING | Row 4 level justification: "it is a second theorem at this row's own distribution **and observer**" (`pgg_analysis_manifest.v:351-352`) | Row 4's observers cell names one observer, `FiveCardAnalysis.colour_view : (size A).-tuple bool` (`:297-300`). `biased_static_obs_indist` is stated at `static_coalition_obs five_card_algebra five_card_params C x`, carrier `{ffun 'I_5 -> 'I_5}`, as the manifest's own pin spells out (`:1505-1510`). Those are two different readers; the only result relating them is `five_card_static_obsE` (`five_card_rows.v:274-297`), which lands in a file *above* the manifest and relates `static_coalition_obs` to `five_card_colour_fill (ViewS ...)`, not to `colour_view`. | §G1 below |
| G2 | BLOCKING | Rows 4 and 5 observers cells, unchanged by the fix pass (`:297-300`, `:367-370`) | `manifest/pgg_analysis_status.v:55-59` defines the level as "AnalysisBridged adds a theorem about that distribution **and that observer**", and the manifest repeats it at `:34-36`. Rows 2, 7, 8 and 9 each name their bridge theorem's observer in the observers cell and give it a capability line: Row 2 lists `PGL27Analysis.static_view` (`:163`) and a line for `word_view_indist_via_transfer` (`:204-206`); Row 9 lists `static_view` and a line for `static_indep` (`:651-653`); Row 7 says "so the theorem's distribution and observer are the row's own" (`:522-524`); Row 9 says the same (`:664-666`). Row 5 has no other bridge theorem at all, so its whole `AnalysisBridged` now rests on a reader the row never declares and whose notion appears in no capability table. | §G2 below |
| G3 | BLOCKING | STATUS "Import rewrite at cp time": "\| `s5_rows.v`, `pgl27_rows.v`, `psl211_rows.v` \| one `From kim_landing_probe Require ...` line each \|" and "The list is exhaustive: no other line of any copy differs from the permanent file by a logical path." | Each of the three carries **two** such lines: `s5_rows.v:115-116`, `pgl27_rows.v:101-102`, `psl211_rows.v:94-95`. And `psl211_rows.v` differs from production by more than a logical path: production has `From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.` on one line and the copy **split** it into two (`diffs/psl211_rows.v.code.diff`), so restoring the permanent file needs a rejoin the table does not mention. | §G3 below |
| G4 | SHOULD | Rows 4 and 5 capability tables (`:327-331`, `:398-404`) carry no line for the new bridge theorems | Convention (3) at `:62-65` fixes the closed vocabulary, which contains **approximate privacy** — the label Row 2 gives `word_view_indist_via_transfer`, a theorem of the identical shape (`:204-206`). Row 5's capability table now lists only two endpoint marginal bounds, so a reader of that table concludes the row claims no privacy capability while its final-bridge cell names one. | §G4 below |
| G5 | SHOULD | "the number is how far it can be from telling the two pairs apart" (`five_card_analysis.v:400-401`); "the bound says how far it can be from telling the two pairs apart" (`five_card_mixing.v:394-395`) | The number is an upper bound on `var_dist` between the two readings, hence an upper bound on the distinguishing advantage. A *small* number means the coalition is *far* from telling the pairs apart, so the number does not measure how far it is; it measures how close it can come. The direction is inverted in both places. | §G5 below |
| G6 | SHOULD | "so it rules out a coalition separating the pairs with certainty **and no more**" (`five_card_mixing.v:468-469`) | The published number is `sqrt 5 / 40 = 0.0559`, and `var_dist_le2`'s ceiling is 2, so the bound rules out every advantage above about 2.8 percent, not only certainty. The rows file states this correctly two files up: "At about three percent of the ceiling it is not a strong statement" (`five_card_rows.v:687-688`). | §G5 below |
| G7 | SHOULD | "it is stated here rather than there because the manifest is imported by the file that certifies those rows" (`five_card_mixing.v:28-29`) | The reason given is the reason the *manifest* cannot name the certified program's proposition, not the reason this corollary lives in `five_card_mixing.v`. The manifest holds no theorem by its own contract (`pgg_analysis_manifest.v:22-23`, "The record stores no theorem: theorems stay facade aliases"), and `five_card_mixing.v` sits below the facade, so the manifest does in fact reach the corollary, through `FiveCardAnalysis.centi_static_obs_indist`. | §G7 below |
| G8 | SHOULD | STATUS "What the spec or SRC got wrong" item 1: "`five_card_analysis.v`, `pgl27_mixing.v` and the `lib/` files **do begin with the identifier**" | Measured over `lib/*.v`: 40 `(** … *)` openings, **0** identifier-first, 40 descriptive-phrase-first. The fix-pass bullet in the same document says the opposite and is the one that is right: "opens all five docstrings with a descriptive phrase, which is the convention of all 28 docstrings in `lib/`". Two sentences of one document contradict each other and the older one is false. | §G8 below |
| G9 | SHOULD | `five_card_analysis.v:19`: `(* coalition's reading of the uniform rotation law. Beside them it carries the*)` | New text written by the fix pass. The line is 80 columns but has no space before `*)`, which is the exact malformation the same pass repaired at the manifest's S_5 paragraph (first-round N3). | §G9 below |
| G10 | SHOULD | `kim_landing_fidelity.v:76-83`, `:106-113` | `landing_centi_indist_of_prop` closes with `apply: (landing_centi_prop_of_indist R tt)`, and that lemma is itself proved from `kim_centi_static_obs_indist`. So the "other direction" never uses an independently-established proposition: its proof term contains the corollary. Neither lemma is obtained from the certified program or from `spectral_tail`, so nothing in the file checks that the stated `SpectralPropAt` is the one `five_card_row_repeated_spectral_tableau` carries. | §G10 below |
| N1 | NOTE | "reading static endpoint **colours**" (`five_card_mixing.v:25`, `:394`; `five_card_analysis.v:396`) | `static_coalition_obs` has carrier `'I_(pga_n A).+2 = 'I_5` (`protocol/pgg_instance.v:297-298`), not `bool`. The values are in the image of `encode_bool` (`den_boer_layout = map_tuple encode_bool (fc_arrange_tup …)`, `instances/denboer1989/den_boer_encoding.v:24-25`), so "colour" is semantically right; but `colour_view`, Row 4's declared observer, is the decoded `(size A).-tuple bool` and a different term. The word invites the conflation G1 makes explicit. | — |
| N2 | NOTE | STATUS: "It is stated at the adapter `kim_single_sample` at bias one hundredth … and not at `amf_sample kim_biased_family`" | True, and the gap is closed by **conversion**, not by a further lemma: `sa_cut_dist (amf_sample kim_biased_family R tt) = sa_cut_dist (@kim_single_sample R (1/100) (kim_centi_lt R) (kim_centi_gt R))` closes by `by []` (compiled, `audit-soundness-2/conv_probe.v`). STATUS does not say so; one clause would. | — |
| N3 | NOTE | Facade mapping list, `five_card_analysis.v:67` | "one-cut tying equation -> biased_sample_cut_witnessE" is appended after the two section-7 entries, but the alias itself sits in section 4 Models (`:263-266`), beside `centi_cut_distE`. The list is unsectioned, so nothing is false; the placement reads as section 7. | — |
| N4 | NOTE | `five_card_rows.v:57` cites `manifest/pgg_analysis_status.v:55-59` by line number | The citation is accurate today (checked). It is pre-fix landing text, not written by the fix pass, and is the defect class the campaign has been removing elsewhere. | — |

---

## Question 1 — the two new corollaries, word by word

Statements, read against `five_card_mixing.v:399-419` and `:470-490`.

**Coalition premise.** Both carry
`(#|C| < profile_k (instance_profile five_card_algebra))%N`. Compiled:
`profile_k (instance_profile five_card_algebra) = 2` closes by `by []`
(`audit-soundness-2/conv_probe.v`, `audit_profile_k_is_2`, rc 0). So the
premise is "at most one seat", which is what both docstrings say ("at every
coalition of at most one seat", "a coalition of at most one seat"), what the
facade aliases say, and what the manifest's pin spells (`:1484-1485`).
**Correct.**

**Which reading.** Both push forward along
`@static_coalition_obs five_card_algebra five_card_params C x`, the static
endpoint reading of `protocol/pgg_instance.v:481-489`, not any executed
reader. Both docstrings say "static endpoints" / "static endpoint colours".
No sentence claims the executed observer. **Correct**, with N1 on the word
"colours".

**Which law.** Both are stated at the bundle's `sw_rho_dist`
(`scb_bound (kim_security_bundle_centi R)` and `kim_biased_marginal_bound R`),
not at `sa_cut_dist` of the row's adapter. The seven-cut docstring says "under
the seven-cut cut" and the one-cut one "under the single biased cut"; those
are the adapters' laws, and the identification is by `kim_centi_cut_distE` and
`kim_biased_sample_cut_witnessE`, neither of which is a conversion (compiled:
both `Fail by []` guards pass). The docstrings therefore describe the law
correctly only through an equation they do not name. At the file's own level
this is fine, because the file states both equations; at the manifest's level
it is what G1's replacement text fixes by naming the equation.

**Which number.** `sw_bound_eps b + sw_bound_eps b`, the epsilon twice, which
is `cert_eps` (`pgg_tableau.v:346-348`) and is what
`var_dist_fdistmap_transfer` concludes (`security/pgg_collusion_bound.v:987-988`,
`<= delta + delta`). Both docstrings say "twice the bundle's spectral number"
and "spent once for each pair". **Correct.**

**Words beyond what is proved.** A word scan over every line the fix pass
added to the five `.v` copies finds no occurrence of "independence", "secret",
"reveal" or "two seats". The only hits are "privacy threshold", which is the
repository's own name for `profile_k`, and the identifier
`colour_view_leak_bound`. Soundness invariant 2 of the spec holds at the word
level. The direction error G5 and the understatement G6 are the two sentences
that are wrong about what the number means, not about what is quantified.

**"indist" in the name, against the PGL(2,7) precedent.**
`pgl27_word_view_indist_via_transfer` (`instances/pgl27/pgl27_models.v:387-399`)
bounds `var_dist` between the two secrets' pushforwards along `pgl27_view`,
by the same `var_dist_fdistmap_transfer`, and is named `_view_indist_`. So
"indist" for a variation-distance bound between two secrets' reading laws is
the tree's established use, and `static_obs_indist` follows it exactly.

Whether it is honest **for a static reading** is a separate question, and the
answer is yes at the name and no at the manifest. At PGL(2,7) the static and
executed readers are identified by `pgl27_static_coalition_viewE`, the row
lists `static_view` among its observers, and the row's justification is
careful to say that `AnalysisBridged` is reached "at both executed observers
rather than at the static layer alone" (`pgg_analysis_manifest.v:212-215`).
At the five-card development there is no such identification below the
manifest, the rows list no static observer, and Row 5 now reaches
`AnalysisBridged` at the static layer alone. The name is honest; the row's
bookkeeping around it is not. That is G1 and G2.

## Question 2 — do they deserve the "final bridge theorem" cell?

The manifest's own criterion, twice stated: "AnalysisBridged + bridge alias to
a named security, leakage, mixing or limitation theorem about the same
distribution **and the same observer**" (`:34-36`), and
`manifest/pgg_analysis_status.v:55-59`, "AnalysisBridged adds a theorem about
that distribution and that observer".

**How Row 2 justifies its cell.** Observers cell names five readers including
`PGL27Analysis.static_view` (`:160-166`). Final bridge cell names three
theorems (`:175-177`). All three have capability lines naming their
distribution, their observer and their notion (`:192-206`), including
`word_view_indist_via_transfer | rho_word | static_view | approximate privacy
at 2^-39, derived from var_dist_transfer and word_mixing`. The level
justification then says which observers carry the level (`:208-215`).

**How Row 8 justifies its cell.** Final bridge theorem
`S5Analysis.exec_endpoint_bound` (`:562`), which has its own capability line
naming its distribution and its observer (`:587-589`), and the justification
reads "exec_endpoint_bound is a mixing theorem at the row's own executed
observer, giving AnalysisBridged" (`:592-594`). Row 8 also keeps the
cut-level `word_endpoint_bound` as a *bound*, with its own capability line, and
says explicitly that the executed one is what carries the level.

**Row 5 as the fix pass leaves it.** Final bridge cell:
`FiveCardAnalysis.centi_static_obs_indist, the coalition bound
var_dist_fdistmap_transfer concludes at this row from
FiveCardAnalysis.centi_cut_mixing and FiveCardAnalysis.static_obs_const`
(`:382-386`). Chain, in order: the two premises are named, the transfer is
named, the conclusion is named. That is complete and in the right order **for
the distribution side**, except that the equation tying the corollary's law to
the row's adapter, `centi_cut_distE`, is named only in the
distribution-to-observer bridges cell (`:372`) and not where the bridge is
claimed. **For the observer side the chain is not named at all**: the row's
observers cell (`:367-370`) lists "one seat's endpoint distribution … ;
FiveCardAnalysis.verifier_endpoints : seq 'I_5", and the corollary is about
`static_coalition_obs`, which appears nowhere in the row. The manifest's own
spelled-type pin for the alias (`:1488-1493`) writes `static_coalition_obs`
out in full, so the file contradicts itself: the pin says what the observer is
and the row does not list it.

**Row 4.** Same gap, plus the sentence G1 quotes, which asserts the criterion
outright. Row 4 at least keeps `colour_view_leak_bound`, a theorem genuinely at
its declared executed observer, so Row 4's `AnalysisBridged` does not fall if
the new cell is corrected; Row 5's does.

**Is anything claimed that only the rows file can state?** No. The fix pass
removed that problem: the first audit's F1 proposed prose saying "no alias of
it can be checked here", and the fix pass did better by proving the corollary
below the facade and aliasing it. Nothing in the manifest now refers to the
certified program. The residue is the observer, not the file boundary.

### G1 — exact replacement for `pgg_analysis_manifest.v:348-353`

Current, from "IdealFinite rather than" to the end of the paragraph:

```
(* IdealFinite rather than StaticExecutedOnly. The conclusion of that         *)
(* transfer is biased_static_obs_indist, a bound on the variation distance    *)
(* between the static readings of a coalition of at most one seat at two      *)
(* committed pairs; it is a second theorem at this row's own distribution     *)
(* and observer, and it reaches AnalysisBridged as colour_view_leak_bound     *)
(* does.                                                                      *)
```

Replacement:

```
(* IdealFinite rather than StaticExecutedOnly. The conclusion of that         *)
(* transfer is biased_static_obs_indist, a bound on the variation distance    *)
(* between the static readings of a coalition of at most one seat at two      *)
(* committed pairs. Its distribution is this row's cut law, by                *)
(* biased_sample_cut_witnessE, and its observer is the static coalition       *)
(* reading named above, so it reaches AnalysisBridged beside                  *)
(* colour_view_leak_bound, which reaches it at the executed reader            *)
(* colour_view.                                                               *)
```

Checked against the statement: `biased_static_obs_indist` is at
`sw_rho_dist (kim_biased_marginal_bound R)`, and
`biased_sample_cut_witnessE : sw_rho_dist (kim_biased_marginal_bound R) =
sa_cut_dist (@kim_single_sample R (1/100) …)` is Row 4's own adapter at the
row's bias, since `single_biased_sample := @kim_single_sample` and
`biased_family` is that adapter at `1/100` (`instances/kim2025/five_card_models.v:435-438`).
"named above" is true only once G2's observers-cell change is made.

### G2 — exact replacements for the two observers cells

`pgg_analysis_manifest.v:297-300`, Row 4:

```
(* | observers          | FiveCardAnalysis.colour_view                        *)
(*                          : (size A).-tuple bool, the decoded colour        *)
(*                            sequence at a list A of seat indices into the   *)
(*                            endpoint list;                                  *)
(*                        static_coalition_obs at five_card_params, the       *)
(*                          seats' reading of the dealt card at their own     *)
(*                          positions, carrier {ffun 'I_5 -> 'I_5} |          *)
```

`pgg_analysis_manifest.v:367-370`, Row 5:

```
(* | observers          | one seat's endpoint distribution, reached through   *)
(*                         FiveCardAnalysis.repeated_seat_distE and           *)
(*                         FiveCardAnalysis.centi_repeated_seat_distE;        *)
(*                       static_coalition_obs at five_card_params, the seats' *)
(*                         reading of the dealt card at their own positions,  *)
(*                         carrier {ffun 'I_5 -> 'I_5};                       *)
(*                       FiveCardAnalysis.verifier_endpoints : seq 'I_5 |     *)
```

`static_coalition_obs` is reachable from the manifest: it comes from
`protocol/pgg_instance.v` and the manifest already writes it out in three pins
(`:1473`, `:1488`, `:1505`). Row 8's observers cell already names an observer
descriptively rather than by facade alias (`:546-551`), so no new facade alias
is required.

And Row 5's level justification, `:411-414`:

```
(* IdealFinite. The conclusion of that transfer, centi_static_obs_indist,     *)
(* is a bound on the variation distance between the static readings of a      *)
(* coalition of at most one seat at two committed pairs. Its distribution     *)
(* is this row's cut law, by centi_cut_distE, and its observer is the         *)
(* static coalition reading named above, and that is what gives               *)
(* AnalysisBridged. endpoint_bound and deal_centi_lt stay in the row          *)
```

Checked: `centi_sample := @kim_centi_repeated_sample`
(`five_card_analysis.v:221`) and
`centi_cut_distE : sa_cut_dist kim_centi_repeated_sample = sw_rho_dist
(scb_bound (kim_security_bundle_centi R))`
(`instances/kim2025/five_card_models.v:402-408`), which is the corollary's law.

### G4 — the two capability lines

After `pgg_analysis_manifest.v:331`, Row 4:

```
(* | biased_static_obs_indist | the cut distribution of                       *)
(*   single_biased_sample, by biased_sample_cut_witnessE                      *)
(*   | static_coalition_obs, the seats' reading of the dealt card             *)
(*   | approximate privacy at twice the length-one bundle's number |          *)
```

After `pgg_analysis_manifest.v:404`, Row 5:

```
(* | centi_static_obs_indist | the cut distribution of centi_sample, by       *)
(*   centi_cut_distE | static_coalition_obs, the seats' reading of the        *)
(*   dealt card | approximate privacy at twice the seven-cut bundle's         *)
(*   number |                                                                 *)
```

"approximate privacy" is already in the closed vocabulary of convention (3)
(`:63`), so no vocabulary is widened and the first audit's S1 stays honoured.
The third column holds a reader in both lines, so the first audit's S2 stays
honoured too.

## Question 3 — the four fidelity lemmas

`kim_landing_fidelity.v:55-113`. Read in full.

**Do they use only the tying equation?** Yes, directly.
`landing_centi_prop_of_indist` introduces `Hd : sa_cut_dist (amf_sample
kim_centi_family R idx) = sw_rho_dist (scb_bound (kim_security_bundle_centi
R))` by `exact: (kim_centi_cut_distE R)`, rewrites, and closes
`exact (@kim_centi_static_obs_indist R C HC x x')`. `landing_biased_prop_of_indist`
does the same with `esym (kim_biased_sample_cut_witnessE R)`. Neither mentions
`kim_centi_cut_mixing`, `kim_biased_cut_mixing`, `five_card_static_obs_const`
or `var_dist_fdistmap_transfer`. So the mixing and constancy theorems are not
re-invoked, and the "same proposition" claim is not empty: it says that the
program's payload type and the corollary differ by the tying equation and by
the order of the three binders, and nothing else.

**Is the tying equation really not a conversion?** Compiled, both guards pass:

```
Goal forall R : realType,
  sa_cut_dist (amf_sample kim_centi_family R tt)
  = sw_rho_dist (scb_bound (kim_security_bundle_centi R)).
Proof. move=> R. Fail by []. Abort.
```

and the same shape for the one-cut equation (`audit-soundness-2/conv_probe.v`,
rc 0). STATUS's sentence "those two are equal by the certificate's tying
equation, a `Qed` lemma, so they are not convertible" is **true**, and its
"Neither direction is a bare `exact:`" is true of the route taken.

**Where the evidence is thinner than STATUS reads.** STATUS's L10 says the file
"derives each certified program's own proposition and the corollary the
manifest's bridge cell names from the other". The second direction closes with
`apply: (landing_centi_prop_of_indist R tt)`, a lemma whose own proof is the
corollary, so its proof term contains the corollary and it is not a derivation
from an independently held proposition. Nor is either lemma tied to the
program: the statement `SpectralPropAt (kim_centi_cert R idx) (cert_eps
(kim_centi_cert R idx))` does coincide with what `certify SpectralDecay
kim_centi_cert` carries (`spectral_tail`, `pgg_tableau.v:562-564`), but nothing
in the file checks that, and `landing_centi_prop_of_indist` would close by
`exact: (spectral_tail (kim_centi_cert R idx))`.

**G10, minimal fix.** Prove the two `_prop_of_indist` lemmas as they are, and
change the two `_indist_of_prop` proofs to go through the certificate rather
than through the sibling lemma:

```
Proof.
move=> HC x x'.
have Hd : sa_cut_dist (amf_sample kim_centi_family R tt)
        = sw_rho_dist (scb_bound (kim_security_bundle_centi R)).
  exact: (kim_centi_cut_distE R).
rewrite -Hd.
by apply: (spectral_tail (kim_centi_cert R tt)).
Qed.
```

That makes the pair a genuine two-way check: one direction from the corollary
to the program's proposition, the other from the certificate's own proof to
the corollary. STATUS's sentence then becomes exactly true and the file gains
the check that the two propositions are the program's.

## Question 4 — the restated one-cut tying equation

`five_card_mixing.v:440-448`:

```
Lemma kim_biased_sample_cut_witnessE :
  sw_rho_dist kim_biased_marginal_bound
  = sa_cut_dist (@kim_single_sample R (1 / 100)
                   (kim_centi_lt R) (kim_centi_gt R)).
```

**Is the certificate's identification field still of the type the record
demands?** `SpectralCert`'s `sc_Hd` field is
`sw_rho_dist sc_b = sa_cut_dist sa` with `sa = amf_sample kim_biased_family R
idx` (`pgg_tableau.v:132-136`, `five_card_rows.v:566-574`). The lemma's type
is at `kim_single_sample R (1/100) …`. **It typechecks by conversion, and the
conversion is real, not assumed**: compiled,

```
Lemma audit_biased_family_conv (R : realType) :
  sa_cut_dist (amf_sample kim_biased_family R tt)
  = sa_cut_dist (@kim_single_sample R (1 / 100)
                   (kim_centi_lt R) (kim_centi_gt R)).
Proof. by []. Qed.
```

closes (rc 0), because `kim_biased_family` is literally
`MkAnalysisModelFamily … (fun R _ => @kim_single_sample R (1/100)
(kim_centi_lt R) (kim_centi_gt R))`
(`instances/kim2025/five_card_models.v:435-438`) and `amf_sample` beta-reduces
at any index. So the rows file gets from the restated lemma to
`sa_cut_dist (amf_sample kim_biased_family R tt)` **by conversion, not by
another lemma**.

**Is that stated truthfully?** It is not stated at all. STATUS says where the
lemma is stated and why, and says "every row equation and certificate still
compiles", but nowhere says that the certificate closes the gap by conversion.
Recorded as N2; one clause in the STATUS bullet closes it.

**Nothing downstream claims an `erefl` that depends on it.** Every `erefl` in
the twelve copies was enumerated. They are: three profile and status pins in
the facade (`:440`, `:442`, `:495-499`); the manifest's typed-status and row
pins (`:1159` through `:1957`), all on `AnalysisPathRow` fields and
`TransferStatus` constructors; `five_card_rows.v:621` and `:892`, `:898`, which
are a recorded `Fail` on the uniform row equation and two functionality
equations; `pgg_tableau.v:457`; and recorded `Fail`s in `pgl27_rows.v` and
`s5_rows.v`. None mentions `biased_sample_cut_witnessE`,
`kim_biased_marginal_bound` or `kim_biased_cert`. The row equations that do
concern the biased certified program, `five_card_row_biased_spectral_rowE` and
`_publishedE`, are `Proof. by []. Qed.` on `AnalysisPathRow` metadata, which
carries no `Prop`, and they compile. **Confirmed.**

## Question 5 — the client file and the S_5 sentence

**F3's fix is true now.** `pgg_analysis_client.v:34-38` reads:

```
(* Five-card development, sections 1 to 6, the bound sub-block and section 7.
   Section 7 carries the base premises of the two cut-carrier transfers and
   the coalition bound each pair of them concludes, so it is represented here
   by one of those bounds and by the typed transfer statuses; the bound alias
   below is deliberately NOT a security alias. *)
```

Checked clause by clause against `five_card_analysis.v:378-424`: section 7
holds `centi_cut_mixing`, `biased_cut_mixing`, `static_obs_const` (the base
premises), `centi_static_obs_indist`, `biased_static_obs_indist` (the two
coalition bounds), and three typed statuses. The block below checks
`FiveCardAnalysis.centi_static_obs_indist` and all three statuses (`:49-52`),
so "one of those bounds and … the typed transfer statuses" is accurate. The
`deal_centi_lt` line still carries `(* bound, not security *)`. **True.**

**F4's sentence, as written.** `pgg_analysis_manifest.v:726-733`:

> For Q the uniform distribution on the generated group the premise is
> moreover UNSATISFIABLE at every delta below one: every generator of this
> instance is a transposition, so a word of length L evaluates into the coset
> of the alternating subgroup determined by the parity of L, and the sum of
> the absolute differences between the cut distribution and group uniform is
> at least one. That sign-coset confinement is not formalized at S_5, and no
> theorem of this repository asserts it there.

Conditions checked.

1. *Every generator is a transposition.* True: the alphabet is the four
   adjacent transpositions of `path_gen_tuple 3`, given as a table at
   `instances/s5/s5_mixing.v:136-140` and as a nat-level swap function at
   `instances/s5/pgg_raag_s5.v:33-39`, and `path_gen_tuple_3_invol`
   (`s5_mixing.v:119-126`) proves each squares to the identity via `tperm2`.
2. *A length-L word lands in the coset fixed by the parity of L.* Follows,
   since every letter is odd and the sign map is a homomorphism to a group of
   order two. The instance's `word_sample` draws words of exactly L letters.
3. *The sum of the absolute differences is at least one.* With P supported in
   one coset C of index two and U uniform on G,
   `sum_G |P - U| = sum_C |P(g) - 1/|G|| + 1/2 >= |sum_C (P(g) - 1/|G|)| + 1/2
   = (1 - 1/2) + 1/2 = 1`, with equality only when P dominates the uniform
   density everywhere on C. So "at least one" is right and "one" would have
   been wrong, which is the correction the fix pass made.
4. *Unsatisfiable at every delta below one.* The premise is
   `var_dist … Q <= delta`; a quantity bounded below by one admits no
   `delta < 1`. True.
5. *`var_dist` is the sum of the absolute differences.* Confirmed at
   `var_dist_supp.v:45-47` and `security/pgg_collusion_bound.v`.

The barred two-character term is gone from the manifest copy, and the comment
box that production left ragged is closed: all eight lines measure 80 columns.
**F4 is closed and the mathematics is right.**

## Question 6 — every other sentence the fix pass wrote or rewrote

Verified against `history/*.2026-09-19-before-fix1*`.

**Manifest.** Convention (3) reverted to the production vocabulary (`:65`); the
two "cut-carrier mixing" capability lines dropped; Row 4's bridges cell gains
`biased_sample_cut_witnessE` and its model-transfer cell names it as the
identification of `biased_cut_mixing`'s law — true, since that is exactly what
the lemma says; Row 4's and Row 5's final-bridge cells and level justifications
rewritten (G1, G2 above); both row docstrings gain the transfer's conclusion
(`:805-818`, `:823-837`) — both read "the bound a coalition of at most one seat
has on telling two committed pairs apart by what it reads", which is accurate
and does not repeat G5's inversion; the "names what it lacks" clause replaced
by "states in its missing-premise cell either the premise it lacks or why none
is absent" (`:703-705`), which is true of rows 1, 7 and 9 ("none", "none is
needed", "none: the cut this model draws is the uniform …"); the five-card
"Absent capabilities" paragraph gains the at-most-one-seat restriction
(`:711-712`); the S_5 paragraph as under question 5. One new spelled-type pin
for the tying equation (`:1295-1300`) and two for the bridge aliases
(`:1480-1512`), all three pinning what their docstrings describe, all reaching
`static_coalition_obs` and `profile_k` explicitly.

**Facade header and section 7.** Header now says section 7 carries the base
premises, "the constancy, at every coalition of at most one of the five seats",
and "the coalition bound each pair of premises gives" — all three true of
`:378-424`. Naming-audit B5 is closed. G9 is the only defect: line 19 has no
padding before `*)`. Replacement for `:18-21`:

```
(* constancy, at every coalition of at most one of the five seats, of that    *)
(* coalition's reading of the uniform rotation law. Beside them it carries    *)
(* the coalition bound each pair of premises gives, and one typed transfer    *)
(* status per analysis path.                                                  *)
```

The retention block keeps one spelled-type `Check` for section 7
(`centi_cut_mixing`) plus three status pins, which is what the file's own
contract at `:432-437` asks for.

**`var_dist_supp.v` docstrings.** All five now open with a descriptive phrase
and the header names `var_dist_fdistmap_inj` and `var_dist_fdistmap` as the
results weakened. Naming-audit B4 is closed; the header's four items now match
the five lemmas. G8 is the contradiction this created inside STATUS.

**Rows header index.** `2^-39` is no longer called a ceiling: the entry now
reads "the repeated row's number is under the constant PGL(2,7)'s word row
publishes", and only `kim_biased_cert_eps_lt2` keeps the word ceiling, where it
is right. The five missing entries are there:
`five_card_reprice39`, `five_card_reprice_inv25`, `five_card_pow2_39_split`,
`five_card_inv50_split`, `five_card_reprice_inv25_lt2`. **True.**

**STATUS.md, "Import rewrite at cp time".** Every line the table quotes exists
verbatim in the copy it names — ten of ten checked mechanically. Every module
the permanent forms name is real: `perm_uniform`, `var_dist_supp`,
`pgg_interface`, `pgg_collusion_bound`, `five_card_mixing`, `pgl27_analysis`,
`five_card_analysis`, `s5_analysis`, `psl211_analysis`, `pgg_instance`,
`pgg_analysis_manifest`. Both `_CoqProject` anchors exist as claimed:
line 34 is `lib/mutual_info_recoding.v` and line 35 `smc/graded_resource.v`;
line 75 is `instances/kim2025/five_card_models.v` and line 76
`instances/kim2025/five_card_analysis.v`. The hunk counts are right: over
`diffs/`, 38 hunks with comments, 23 code hunks, 10 of them containing a
`Require` line and 13 the landing. **But the table is wrong for three files —
G3.**

### G3 — exact replacement for two rows of the table

Replace

```
| `s5_rows.v`, `pgl27_rows.v`, `psl211_rows.v` | one `From kim_landing_probe Require ...` line each | the same line at `pgg_smc` |
```

with

```
| `s5_rows.v`, `pgl27_rows.v` | two `From kim_landing_probe Require ...` lines each, `s5_rows.v:115-116` and `pgl27_rows.v:101-102` | both lines at `pgg_smc`, unchanged otherwise |
| `psl211_rows.v` | `From pgg_smc Require Import pgg_analysis_status.`, `From kim_landing_probe Require Import pgg_analysis_manifest.` and `From kim_landing_probe Require Import pgg_tableau pgg_tableau_syntax.` (`:93-95`) | the production form restored: `From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.` followed by `From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.`, the three copy lines becoming two |
```

and replace the sentence "The list is exhaustive: no other line of any copy
differs from the permanent file by a logical path." with "The list is
exhaustive. Four copies also differ by where a `Require` line is split, and
each row below gives the production form to restore."

### G5, G6, G7 — the three sentences about what the number means

`five_card_mixing.v:394-395`, replacement for the two lines:

```
    the privacy threshold that sees only static endpoint colours, and the
    bound caps how close it can come to telling the two pairs apart. The number
```

`five_card_analysis.v:400-401`, replacement for the two lines:

```
    path: the attacker is that coalition, and the number caps how close it
    can come to telling the two pairs apart. *)
```

`five_card_mixing.v:467-469`, replacement:

```
    statement of Kim's one-cut analysis path. Its number is about three
    percent of the ceiling var_dist_le2 gives, so it is a weak separation
    bound and not a cryptographic one. *)
```

Checked against `kim_biased_cert_eps_lt2`'s own docstring
(`five_card_rows.v:684-688`), which already uses "about three percent of the
ceiling", so the vocabulary stays one word per concept.

`five_card_mixing.v:27-29`, replacement for the last clause of the new header
paragraph:

```
(* other. That is the conclusion the analysis manifest's two Kim rows are     *)
(* bridged by. It is stated here, below the facade, because the manifest      *)
(* holds no theorem of its own and reaches every one through a facade alias.  *)
```

### G8 — the STATUS contradiction

In "What the spec or SRC got wrong", item 1, replace
"`five_card_analysis.v`, `pgl27_mixing.v` and the `lib/` files do begin with
the identifier, and the new declarations in those two places do too." with
"`five_card_analysis.v` and `pgl27_mixing.v` do begin with the identifier, and
the new declarations there do too. The `lib/` files do not: all 40 docstrings
under `lib/` open with a descriptive phrase, which is why fix pass 1 rewrote
`var_dist_supp.v`'s five to match."

## Question 7 — S3 left undone

`five_card_analysis.v:410-414`:

```
(** exec_transfer_status — the transfer status of the uniform exact-cut path:
    it carries its landed static results to its executed observers, and its
    security statement is an exact independence rather than a comparison with
    an ideal law. *)
```

Checked: Row 3 is the uniform path, its transfer status is
`StaticExecutedOnly` (`pgg_analysis_manifest.v:253`), its final bridge theorem
is `exec_trace_secrecy`, an entropy equality at an executed reader
(`:241`, `:259-260`), and its model-transfer cell says "none claimed"
(`:243`). Every clause of the docstring is true, and the docstring does say
which path the alias means.

**Verdict on S3: a naming residue, not a soundness problem.** No sentence in
the landing is false because the name was kept. The residue is that `exec_`
no longer distinguishes this alias from `biased_transfer_status` and
`repeated_transfer_status`, which name executed paths too, and a reader who
reads only the identifier learns nothing. STATUS records it, gives both
options and says it is the owner's call, which is the right disposition. It
does not block the landing.

## Question 8 — the first-round findings

| ID | Status | One line |
|---|---|---|
| F1 | closed differently | Row 5's final-bridge cell no longer names a mixing bound; it names `centi_static_obs_indist`, a real transfer conclusion proved below the facade and aliased, which is better than the audit's proposed prose. The observer half of the same criterion is re-opened as G2. |
| F2 | closed | "giving AnalysisBridged" no longer hangs on `centi_cut_mixing`; the transfer's conclusion carries the level in both the level justification and the row docstring. |
| F3 | closed | `pgg_analysis_client.v:34-38` rewritten and two `Check`s added; every clause verified against section 7. |
| F4 | closed | Barred term gone, quantity named as the sum of the absolute differences, claim weakened to "at least one", comment box closed; all four conditions of the sentence checked and true. |
| S1 | closed | `:65` reverted to the production vocabulary and both "cut-carrier mixing" capability lines dropped. |
| S2 | closed by S1 | The two lines that put a carrier in the observer column are gone. |
| S3 | not closed, recorded | Naming residue only; the docstring names the path, so nothing is false. See question 7. |
| S4 | closed | STATUS now says 38 hunks, 23 code, 10 import, 13 landing; all four recounted over `diffs/` and correct. |
| S5 | closed | Both sentences rewritten to the reverse closure; `psl211_endpoints.v` is now described as loaded through `psl211_analysis` and recompiled by nothing. |
| S6 | closed | STATUS drops "after its dependencies", states the grouping rule, gives both insertion points and both anchors; both anchors verified in the production `_CoqProject`. |
| S7 | closed | "names what it lacks" replaced by "states in its missing-premise cell either the premise it lacks or why none is absent", which is true of rows 1, 7 and 9. |

Naming audit, for completeness: B1 partly closed (the table exists but is wrong
for three files, G3); B2 closed differently (the capability line is dropped and
the tying equation moved, aliased and named in Row 4's bridges and
model-transfer cells); B3 closed (the rename is applied at all seventeen
occurrences and nothing outside the probe mentions the old names); B4 closed;
B5 closed at both carriers.

---

## What I did not check

- The mathematics of the declarations copied from SRC. Five SRC soundness
  audits and the first round cover it, and question 1 of this round covers
  only the two new corollaries and their comments.
- The twelve-file compile, the 71 `Print Assumptions` blocks and the
  comment-stripped equality with production. The main session reports all
  twelve at rc 0, 62 assumption blocks within the three `boolp` axioms and 9
  closed, and I was told not to repeat it. The only Rocq I ran is
  `audit-soundness-2/conv_probe.v`.
- `instances/psl211/psl211_endpoints.v`, never compiled, never read for this
  audit.
- The dependency and recompile-set arithmetic (seven reverse-dependants,
  eleven recompiled files). Recomputed in round 1 and unchanged by the fix
  pass.
- The numeric claims recomputed in round 1 (`2*sqrt 5*(1/80)^7`, `2^-39`,
  `sqrt 5/40`, `1/25`). I re-derived only `sqrt 5/40 = 0.0559` and its ratio
  to the ceiling 2, for G6.
- The proposition search of the production tree (L8). Round 1 ran an
  independent one and found the single miss that became F3; I did not rerun
  it, so a proposition neither search names could still be false somewhere.
- `l7_fail_messages.v` was not re-run; STATUS's claim that it still returns 1
  with the same message is taken on the probe's word.
- Whether the owner wants the `exec_transfer_status` rename. That is a
  decision, not a fact.
