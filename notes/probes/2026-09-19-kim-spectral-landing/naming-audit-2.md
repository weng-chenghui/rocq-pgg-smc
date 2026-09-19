# Naming and style audit, round 2, of the Kim spectral landing after fix pass 1

**NO-GO** for "the names and comments of these landing copies may go into the
permanent tree".

Three blocking findings. None is a new identifier and none is a proof defect.
Two are in the manifest's Row 4 and Row 5 tables, where the fix pass applied
half of the PGL(2,7) precedent it cites: it moved the two Kim rows from naming
a pair of premises to naming a bridge theorem, but did not give that theorem a
capability line and did not add its observer to the row's observers field, so
each row's four-column table no longer accounts for the theorem the row's own
level justification says gives it AnalysisBridged. The third is the STATUS
section that replaced first-round B1: it undercounts the import lines to
rewrite and, at `psl211_rows.v`, its instruction produces a file that differs
from production by a line split the landing does not intend.

The new identifiers are sound. `indist` is the tree's word for exactly this
statement shape, the facade aliases follow the facade's own contract, and a
whole-word scan of all thirteen new names over 207 production `.v` files, the
two sibling probes and 1153 `user-contrib` files returns zero hits.

Scope: the six files that land plus `kim_landing_fidelity.v` and `STATUS.md`,
at commit 907d819, diffed against `history/*.2026-09-19-before-fix1*` to
separate fix-pass text from SRC landing text from untouched production text.
Read-only: nothing was compiled, and no file but this one was written.

---

## Findings

| ID | class | quoted content | rule or precedent | exact fix |
|---|---|---|---|---|
| **A1** | BLOCKING | Row 5 field cell `(* \| final bridge theorem \| FiveCardAnalysis.centi_static_obs_indist, the *)`, and Row 5's four-column table holds only `endpoint_bound` and `deal_centi_lt`. Row 4 likewise names `biased_static_obs_indist` in its final-bridge cell and gives it no line. | Row 2 gives its transfer conclusion a capability line: `(* \| word_view_indist_via_transfer \| rho_word \| static_view *)` / `(*   \| approximate privacy at 2^-39, derived from var_dist_transfer and *)` / `(*     word_mixing \| *)`. The manifest's own reading of AnalysisBridged is "bridge alias to a named security, leakage, mixing or limitation theorem about the same distribution and the same observer", and the four-column table is where the manifest records that. | Add to Row 4's table `(* \| biased_static_obs_indist \| sw_rho_dist of the length-one bundle's marginal bound, the cut distribution of single_biased_sample by biased_sample_cut_witnessE \| static_coalition_obs at a coalition of at most one seat \| approximate privacy at twice the bundle's spectral number, derived from var_dist_fdistmap_transfer, biased_cut_mixing and static_obs_const \| *)`, and the matching line to Row 5 with `centi_static_obs_indist`, `centi_cut_distE` and `centi_cut_mixing`. |
| **A2** | BLOCKING | Row 4's level justification: `(* transfer is biased_static_obs_indist, ...; it is a second theorem at this row's own distribution *)` / `(* and observer, and it reaches AnalysisBridged as colour_view_leak_bound *)` / `(* does. *)`. Row 4's observers field names one observer, `FiveCardAnalysis.colour_view`. Row 5's names "one seat's endpoint distribution ... FiveCardAnalysis.verifier_endpoints : seq 'I_5". Neither names the static coalition reader the new theorem is stated at. | Row 2 lists `PGL27Analysis.static_view` among its observers, which is what `word_view_indist_via_transfer` is stated at. Row 7 shows that an observer with no facade alias may still be named: `(* sa_coalition_view of rand_sample at offset zero *)` / `(*   : {ffun 'I_5 -> 'I_5}, executed; *)`. | Add to both observers fields an entry of Row 7's shape, for instance `(* static_coalition_obs C x at the five-card algebra *)` / `(*   : {ffun 'I_5 -> 'I_5}, the static endpoint reading of a *)` / `(*     coalition at a committed pair; *)`. Until it is there, the sentence "at this row's own distribution and observer" is false of the row as tabulated. |
| **A3** | BLOCKING | STATUS's "Import rewrite at cp time": "The list is exhaustive: no other line of any copy differs from the permanent file by a logical path", and the row `\| s5_rows.v, pgl27_rows.v, psl211_rows.v \| one From kim_landing_probe Require ... line each \| the same line at pgg_smc \|`. | Each of the three has two such lines, not one. `l7_fail_messages.v` has three and is absent from a table that lists `kim_landing_fidelity.v` precisely so as to say it does not land. At `psl211_rows.v` the copy reads `From pgg_smc Require Import pgg_analysis_status.` / `From kim_landing_probe Require Import pgg_analysis_manifest.` / `From kim_landing_probe Require Import pgg_tableau pgg_tableau_syntax.` where production reads two lines, `From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.` and `From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.`, so "the same line at pgg_smc" leaves that file three lines where production has two. | Correct the count to two lines each; give `psl211_rows.v` its own row with the production restoration form spelled out, as the table already does for `pgg_analysis_manifest.v` and `pgg_tableau.v`; add a row for `l7_fail_messages.v` saying it does not land. |
| **A4** | SHOULD | `five_card_analysis.v`, fix-pass text: `(* coalition's reading of the uniform rotation law. Beside them it carries the*)` | The comment box has no space before `*)`. This is the exact shape the fix pass closed one file away, recorded in STATUS as "the comment box that production leaves ragged is closed". | Reflow the paragraph so every line ends `... *)` with the box column intact; the sentence loses one word per line at most. |
| **A5** | SHOULD | `five_card_mixing.v`: `(** kim_centi_static_obs_indist — at every coalition of at most one seat and` ... `static endpoints under the seven-cut cut is within twice the bundle's` | "the seven-cut cut" repeats the noun. One word per concept: everywhere else the file writes "the seven-cut law". | Write "under the seven-cut law". |
| **A6** | SHOULD | Three surface forms for the certificate's second field. `five_card_rows.v`, `kim_centi_cert`: "the identification of that bound's law with the law the repeated adapter draws its cut from". `five_card_mixing.v`, fix-pass move: "It is the tying field of the spectral certificate". `five_card_rows.v`, fix-pass rewrite at `kim_centi_cert40`: "The ideal cut, the tying equation and the constancy". `five_card_analysis.v`, new: `(*   one-cut tying equation                   -> biased_sample_cut_witnessE   *)` | One word per concept, file-wide and across the five files. The fix pass carried "tying" into two more files while the declaration that constructs the field still says "identification". | Pick "tying equation" and use it in all four places, including `kim_centi_cert`'s docstring: "the tying equation identifying that bound's law with the law the repeated adapter draws its cut from". |
| **A7** | SHOULD | `five_card_rows.v`, `kim_centi_cert`: "and the constancy of a coalition's reading of the ideal cut in the committed pair", and `kim_biased_cert`: "The ideal cut and the constancy of a coalition's reading of it are the same two terms". `kim_centi_cert40`, rewritten by the fix pass: "the constancy of the reading at every coalition of at most one seat". | First-round B5: `five_card_static_obs_const` holds only at `#|C| < profile_k` with `profile_k` two, so "a coalition's reading" states it at every coalition. B5 named two sentences; these two are the same overstatement in the same file, and the fix pass made a third sentence restricted, so the file now says it both ways. | Restrict both: "the constancy, at every coalition of at most one seat, of the reading of the ideal cut". |
| **A8** | SHOULD | `var_dist_supp.v`, all five docstrings, for instance "It\n    is the endomap case of fdistmap_inj_uniform,\n    whose conclusion is uniform on the image" and "A pushforward gives mass only to points in the image of the map. It\n    is how the support of a cut law defined as a\n    word-shuffle pushforward is read off the word evaluation." | The S1 conversion deleted the leading `identifier — ` without reflowing, so five docstrings carry short lines where `lib/perm_uniform.v`, `lib/support_posterior.v` and `lib/mutual_info_recoding.v` fill to the margin. | Reflow the five docstrings. No wording change. |
| **A9** | SHOULD | STATUS, on first-round B2: "Its statement as SRC writes it also needs `amf_sample`, which comes from `manifest/pgg_analysis_status.v` and which `five_card_mixing.v` deliberately does not import." | `instances/kim2025/five_card_models.v:99` reads `From pgg_smc Require Import pgg_analysis_status.`, and `five_card_mixing.v:81` imports `five_card_models`, so the module is loaded and `kim_biased_family` (declared at `five_card_models.v:435`) is in scope. The decision to state the equation at `kim_single_sample` is right on its own merits, since that is the shape `kim_centi_cut_distE` has; the recorded reason is not a fact about the tree. | Replace the reason with the one that holds: "stated at the adapter `kim_single_sample`, which is the shape `kim_centi_cut_distE` has, so the file states both tying equations in one form; the `amf_sample` form follows by conversion, as `kim_landing_fidelity.v` shows". |
| **A10** | SHOULD | S3 left undone: `exec_transfer_status` now sits beside `biased_transfer_status` and `repeated_transfer_status` and names an execution stage rather than a model. | The other two are named after the path's model family, and the facade's own name for the uniform model is `uniform_sample`. | Rename `exec_transfer_status` to `uniform_transfer_status`. Cost and collision check in section 6. |
| **A11** | NOTE | `five_card_mixing.v` index: `(*   kim_centi_static_obs_indist == a coalition below the privacy threshold   *)` / `(*                                  reads the seven-cut law within twice      *)` / `(*                                  that number at both committed pairs       *)` | A coalition does not read within a number; two readings are within a distance of each other. Type-honest phrasing. | "== the two readings of the seven-cut law at two committed pairs are within twice that number". |
| **A12** | NOTE | `kim_centi_static_obs_indist` is stated at `sw_rho_dist (scb_bound (kim_security_bundle_centi R))` and its docstring calls that "the seven-cut law", with no identification named. | `kim_landing_fidelity.v` shows the two are not convertible: `landing_centi_prop_of_indist` must `rewrite Hd` with `kim_centi_cut_distE` first. Row 4's model-transfer cell, rewritten by the fix pass, does name its identification. | Add "by `kim_centi_cut_distE`" to the docstring's first sentence. |
| **A13** | NOTE | Row 5's capability table lost the line that named `centi_cut_distE`; Row 4's model-transfer cell gained a naming of `biased_sample_cut_witnessE`. | The two rows now treat the identification asymmetrically. `centi_cut_distE` is still in Row 5's distribution-to-observer bridges field, so nothing is lost, only the symmetry. | Optional: name `centi_cut_distE` in Row 5's model-transfer cell as Row 4 names its counterpart. |
| **A14** | NOTE | `five_card_rows.v`: "five_card_row_biased_leak_bound states a ceiling on it" and "The statement is a numeric ceiling on that information", both untouched production; against "the ceiling var_dist_le2 gives", four times, in landing text. | "ceiling" is reserved for two in every line the landing writes, and production already used it for a mutual-information bound. Not the landing's defect; it is what a reader meets. | Out of scope for the landing. Record it for a later pass over the production file. |
| **A15** | NOTE | `kim_centi_static_obs_indist`'s docstring opens "at every coalition of at most one seat" and continues "the attacker is a coalition below the privacy threshold". | Two phrases for one class inside one docstring. `five_card_static_obs_const` ties them once in the same file ("the privacy threshold is two, so a coalition below it is empty or holds one seat"), so a reader can follow. | Use one of the two in the docstring. |
| **A16** | NOTE | `five_card_analysis.v` check table gains `(*   one-cut tying equation                   -> biased_sample_cut_witnessE   *)` while the uniform path's `sample_cut_witnessE` has no line in that table. | The table is a minimum list rather than an index, so absence is allowed; the asymmetry is new. | Optional: add the uniform counterpart. |
| **A17** | NOTE | `five_card_rows.v`: "so the same status is the honest one for it" and "cannot say which transfer status is the honest one", both SRC landing text. | First-round S5 removed "the row is honest rather than tight" as a judgement about the artifact. These two survived, because S5 named only one clause. Both are closer to a claim about which status the mathematics supports than the one S5 removed. | No change required. Recorded so the owner can decide once for all three. |
| **A18** | NOTE | Rows 4 and 5 capability cells read `\| endpoint marginal bound \|`; the manifest's closed vocabulary lists "endpoint marginal mixing". | Untouched production text, at production lines 369 and 372. Row 8 shows that a qualified form is acceptable ("cut-level endpoint marginal mixing"), but "bound" is a different noun. | Out of scope. Record for a later pass. |
| **A19** | NOTE | `kim_biased_exact_le_eps` still has no consumer in the five files and is not in the rows index. | First-round N12, and the repository's "keep only claimed or premise" standard. STATUS records the retention decision for `var_dist_le2` and not for this one. | Record the decision in STATUS, or drop the lemma. |

---

## 1. The new identifiers

### Is `indist` the right word, and does the tree use it this way?

Yes, and the tree uses it for exactly this statement shape. Every production
name containing `indist` denotes a bound on the variation distance between two
observer laws taken at two secrets:

| name | file | statement |
|---|---|---|
| `pgl27_word_view_indist` | `instances/pgl27/pgl27_models.v` | `var_dist (fdistmap (fun g => pgl27_view R C (s, g)) (rho_word R)) (fdistmap ... (s', g) ...) <= 2%:R^-39` at `#\|C\| <= 3` |
| `pgl27_word_view_indist_via_transfer` | same file | the same statement, proved through `var_dist_fdistmap_transfer` |
| `pgl27_word_trace_indist` | same file | the same for the static content trace |
| `pgl27_exec_view_indist`, `pgl27_exec_trace_indist` | same file | the same at the executed sample layer |
| `word_view_indist`, `word_trace_indist`, `exec_view_indist`, `exec_trace_indist`, `word_view_indist_via_transfer` | `instances/pgl27/pgl27_analysis.v` | facade aliases of the five above |
| `view_indist_of` | `manifest/pgg_tableau.v` | the framework's own name for the proposition of that shape |

`kim_centi_static_obs_indist` and `kim_biased_static_obs_indist` state
`var_dist (fdistmap (static_coalition_obs C x) P) (fdistmap
(static_coalition_obs C x') P) <= eps + eps` under `#|C| < profile_k`. Same
quantifier, same relation, same kind of bound. `indist` is right.

The stem `static_obs` is the file's own, from `five_card_static_obs_const` and
`static_coalition_obs`, and the facade already carries `static_obs_const`.
PGL(2,7) writes `view` because its observer is `pgl27_view`. The two
instances therefore use different nouns for a coalition's static reading, but
each uses its own file's noun, which is the tree's existing split and not this
landing's.

### Would `_via_transfer` be needed?

No, and adding it would name a distinction that does not exist here.
`pgl27_word_view_indist_via_transfer` carries that suffix because
`pgl27_word_view_indist` already proves the identical statement by another
route; its own docstring says so: "The statement is that of
pgl27_word_view_indist verbatim; only the route differs". Kim has no direct
proof of the coalition bound, so `kim_centi_static_obs_indist` is the only
name for that proposition and the suffix would promise a sibling that is not
there.

### Facade aliases

`centi_static_obs_indist`, `biased_static_obs_indist` and
`biased_sample_cut_witnessE` each strip the `kim_` prefix, which is the
contract the file states: "the module supplies the namespace, so the aliases
drop the five_card_, den_boer_ and kim_ prefixes of their targets". They sit
beside `centi_cut_distE`, `biased_family` and `static_obs_const`, formed the
same way. `biased_sample_cut_witnessE` pairs with the existing
`sample_cut_witnessE := @den_boer_sample_cut_witnessE`, so the uniform and the
one-cut tying equations now carry parallel facade names.

### The rename

`five_card_row_biased_ideal_tableau` / `_rowE` / `_publishedE` to
`five_card_row_biased_spectral_tableau` / `_rowE` / `_publishedE`. Applied at
all twelve occurrences in `five_card_rows.v` and all five in
`kim_landing_fidelity.v`. The old names survive only in `history/`. The new
names match `five_card_row_repeated_spectral_tableau`, which is built by the
same `certify SpectralDecay ... |> publish IdealFinite` clause.

### Fidelity lemmas, judged lightly

`landing_centi_prop_of_indist`, `landing_centi_indist_of_prop`,
`landing_biased_prop_of_indist`, `landing_biased_indist_of_prop`. The `_of_`
connective has precedent in the tree: `kim_marginal_of_cert`, `rank4_of_diff`,
`fc_curried_of_facade`, `sa_seat_view_of_run`, `prescribed_of_set`, and this
landing's own `five_card_cut_mixing_of_supp_pow`. The direction reads
correctly, `X_of_Y` deriving X from Y. The `landing_` prefix marks a file that
does not land, which is honest for a probe evidence file.

### Collision scan

Thirteen new names, scanned with Python `re` and `\b` over 207 production `.v`
files outside `notes/`, the 12 files of
`notes/probes/2026-09-19-psl211-nogo-landing/`, the 10 files of
`notes/probes/2026-09-19-tableau-extensions/` and 1153 `.v` files under
`~/Projects/coq/_opam/lib/coq/user-contrib`. **Zero hits in all four
populations.** The only hits anywhere are inside this landing probe. The three
old `_ideal_` names hit nothing outside `history/`.

The proposed `uniform_transfer_status` of A10 was scanned the same way: zero
hits in the repository and zero in `user-contrib`. `exact_transfer_status` is
taken, by `instances/psl211/psl211_analysis.v`.

---

## 2. Statement comments of the fix pass's text

Against the two-part standard: the fact, then the object's position in the
attack model, which here is a coalition of at most one seat reading static
endpoint colours at two committed pairs.

**What holds.** Both new lemma docstrings name the attack model explicitly.
`kim_centi_static_obs_indist`: "the attacker is a coalition below the privacy
threshold that sees only static endpoint colours, and the bound says how far it
can be from telling the two pairs apart". Both price the step and label the
currency: "The number is the bundle's spectral one spent once for each pair, so
the only inexact quantity is that mixing distance; the constancy of the ideal
reading is exact and costs nothing", and for the one-cut path "Its number is of
hundredth scale rather than cryptographic, so it rules out a coalition
separating the pairs with certainty and no more". That second clause is the
sentence a domain reader needs, and it agrees with `kim_biased_cert_eps_lt2`,
which puts the same number at about three percent of two. The facade aliases
repeat the position rather than the type, as the contract asks. No status
marker, no effort estimate, no proof strategy, no line number, and no `Used
by:` slot appears anywhere in the new text.

**Narration of an earlier name.** None. The one place at risk, `kim_centi_cert40`,
was rewritten away from "That field and the mixing statement proved against it
are the two that change" to a comparison with `kim_centi_cert` by name, which
is a statement about two objects and not about an edit.

**One word per concept.** Three problems, A5, A6, A7 above, plus the milder
A15. The word counts across the five files:

- "reading" for what a coalition gets off the static endpoints: consistent in
  all new text, 48 uses across the five files. "view" survives only in
  untouched production text and only for `colour_view`, a different observer.
  "observation" survives only in untouched production text. No drift introduced.
- "constancy": one concept, and the fix pass restricted one of its three
  unrestricted phrasings (A7).
- "cut carrier" nominal and "cut-carrier" attributive, used consistently in
  three files; no competing term.
- "ceiling" for two: every landing line uses it that way, two untouched
  production lines do not (A14).
- the certificate's identification field: three surface forms (A6).

**Domain position, checked against the type.** The bound in both new lemmas is
`eps + eps`, written as a sum and not as `2 * eps`, matching what
`var_dist_fdistmap_transfer` concludes and matching the PGL(2,7) instance,
where `word_mixing` at `2^-40` yields `2^-39`. "twice the bundle's spectral
number" and "spent once for each pair" are both true of that sum.

**The header of `five_card_mixing.v`.** The new paragraph states the fact and
the position well: "the statement the attack model asks for: a coalition of at
most one seat, reading static endpoint colours at two committed pairs, sees
laws within twice the bundle's number of each other". Its last clause, "it is
stated here rather than there because the manifest is imported by the file that
certifies those rows", narrates a placement decision, but it states a durable
dependency fact and sits in a `(* ... *)` banner rather than a rendered
docstring, so it is within the rule's allowance for a file header.

---

## 3. The manifest's tables

**Closed vocabulary: yes.** Convention (3) is back to production's exact list,
"correctness, exact privacy, approximate privacy, trace secrecy, conditional
entropy, mutual information or endpoint marginal mixing", and the two
capability lines that used the widened term are gone. Row 4's remaining
capability line reads "mutual information, at most kim_leak_bound eps" and Row
5's two read "endpoint marginal bound"; all three are untouched production
cells. The one deviation from the closed list is "bound" for "mixing" in those
two Row 5 cells, which is production's (A18).

The reversion is right on the precedent the fix pass cites. Row 2 puts
`PGL27Analysis.word_mixing` under "bound or certificate" with no capability
line, and `centi_cut_mixing` and `biased_cut_mixing` are bounds of the same
shape.

**Grammatical shape against Rows 2 and 8: no, in two ways.** Row 2's shape is
that every theorem named in "final bridge theorem" appears in the four-column
table with a notion, and that the observer it is stated at appears in the
observers field. Row 8 holds to the same shape with two theorems and two
observers. Rows 4 and 5 now name a final bridge theorem that appears in neither
place. This is A1 and A2, and it is the half of the PGL(2,7) precedent the fix
pass did not apply.

The prose cells themselves are well formed and match Row 2's grammar. Row 4's
model-transfer cell now reads "its first hypothesis is
FiveCardAnalysis.biased_cut_mixing, whose law is the cut distribution of
single_biased_sample by FiveCardAnalysis.biased_sample_cut_witnessE", which
closes first-round B2's misattribution by naming the identification rather than
the wrong lemma. Row 5's counterpart names no identification (A13).

Both level justifications are now accurate about what gives what: the mixing
theorem with the constancy theorem gives IdealFinite, and the transfer's
conclusion is what reaches AnalysisBridged. The "Absent capabilities"
paragraph's weakening from "names what it lacks" to "states in its
missing-premise cell either the premise it lacks or why none is absent" is
correct against rows 1, 7 and 9.

---

## 4. `var_dist_supp.v`

**Docstring openings: converted, and the convention now matches `lib/`.** All
five open with a descriptive phrase. Compared with three existing `lib/` files:

- `lib/perm_uniform.v`: "Membership in prescribed s v is exactly agreement
  with v at each of the k coordinates named by s."
- `lib/support_posterior.v`: "The source is the independent product of a
  uniform Boolean secret with a uniform draw from [A]."
- `lib/mutual_info_recoding.v`: "Two maps that agree wherever a law charges
  push that law forward to the same law: fdistmap f d = fdistmap g d as soon
  as f and g agree on fdist_supp d."

The pattern in `lib/` is a declarative sentence that may name identifiers
inside it but never opens with one followed by a dash. `var_dist_supp.v` now
does the same: "The variation distance between two laws on a finite carrier is
at most two", "A reader that separates the points carrying mass transports the
variation distance exactly", "An injective endomap of a finite type leaves the
uniform law fixed", "A pushforward gives mass only to points in the image of
the map", "The positions of a tuple at which a predicate holds are counted by
the predicate on the underlying sequence". Each is followed by a sentence
placing the lemma in the five-card argument, which is what the `lib/` files do
too. The convention is met; only the line filling was not redone (A8).

**Header paragraph against the five lemmas: true.** The rewritten sentence
reads "Beside it sit the ceiling a published variation distance is read
against, the invariance of a uniform law under an injective endomap, the fact
that a pushforward charges only the image, and the count of the tuple positions
at which a predicate holds." Checked one by one:

| clause | lemma | statement | true |
|---|---|---|---|
| the ceiling | `var_dist_le2` | `var_dist P Q <= 2%:R` | yes |
| invariance under an injective endomap | `fdistmap_inj_uniform_id` | `injective f -> fdistmap f (fdist_uniform cA) = fdist_uniform cA` | yes |
| a pushforward charges only the image | `fdistmap_neq0_codom` | `fdistmap f P b != 0 -> exists a, f a = b` | yes |
| the count of the tuple positions at which a predicate holds | `card_tnth_count` | `#\|[pred k : 'I_n \| p (tnth t k)]\| = count p t` | yes |

The two errors first-round B4 named are gone: `fdistmap_inj_uniform_id` is no
longer called a support fact, and `card_tnth_count` is no longer said to read a
law. First-round S7 is closed in the same pass: the header and the docstring of
`var_dist_fdistmap_supp_inj` both name `var_dist_fdistmap_inj` and
`var_dist_fdistmap`, so a reader can find the results this file weakens.

---

## 5. First-round findings, one line each

| finding | status |
|---|---|
| **B1** import lines | **Not closed.** Answered by the STATUS section rather than by editing the copies, which is the right choice, but the section is not executable as written: see A3. |
| **B2** Row 4 bridge misattribution | **Closed differently, and correctly.** The structural fix was taken, the lemma moved to `five_card_mixing.v` as a `Lemma ... Qed.`, and Row 4's cell now names the identification. I agree with the restatement at `kim_single_sample`; I do not agree with the reason recorded for it (A9). |
| **B3** `_ideal_` to `_spectral_` | **Closed.** All seventeen occurrences renamed, zero collisions, old names only in `history/`. |
| **B4** `var_dist_supp.v` header | **Closed.** All five lemmas now described correctly. |
| **B5** at-most-one-seat restriction | **Closed for the two named sentences, open elsewhere.** `five_card_analysis.v` and the manifest's paragraph now carry it; `five_card_rows.v` states it both ways (A7). |
| **S1** `lib/` docstring convention | Closed on the convention, not on the line filling (A8). |
| **S2** `2^-39` called a ceiling | Closed; the index now says "the constant PGL(2,7)'s word row publishes" for one entry and "the ceiling a variation distance has" for the other. |
| **S3** six missing index entries | Closed; five added to `five_card_rows.v`, and `kim_biased_sample_cut_witnessE` indexed in `five_card_mixing.v`, where it now lives. |
| **S4** transparent `Definition` of a Prop | Closed differently; it is a `Lemma ... Qed.` in `five_card_mixing.v`, so the question is gone rather than answered. |
| **S5** judgement about the artifact | Closed at the named docstring. Two sentences of the same kind survive elsewhere in the file (A17). |
| **S6** `kim_centi_cert40` narrates a diff | Closed; the new text compares two named certificates. |
| **S7** name the results weakened | Closed. |
| **N1** keep the file name | Followed; `var_dist_supp.v` unchanged. |
| **N2** "cut-carrier mixing" | Closed differently; rather than adding the suggested Row 2 line, the term was removed from the vocabulary and both lines dropped, which makes the suggestion moot and matches Row 2's actual treatment of a bound of that shape. |
| **N3** no collisions | Reconfirmed independently over four populations. |
| **N4** line length | Reconfirmed; see section 7. |
| **N5** barred vocabulary | Reconfirmed; see section 8. |
| **N6** the barred token and the ragged box | Closed. The token is gone and the box is closed. On "distance one" against "at least one": **I agree with the fix pass.** A law confined to one coset of an index-two subgroup has sum of absolute differences from group uniform equal to one only when it is uniform on that coset; concentrated on a single element it reaches nearly two. The general bound is at least one, and at least one is what makes the premise unsatisfiable below delta one, which is the sentence's whole point. First-round N6's "is one" was an unjustified strengthening. |
| **N7** probe residue | Reconfirmed; the `kim_landing_probe` paths are still the only residue, and the barred token is gone. |
| **N8** section names | Unchanged by the fix pass. |
| **N9** header indices | Updated and still true of their files. |
| **N10** facade alias convention | Holds for the three new aliases. |
| **N11** statement comments that checked out | Unchanged. |
| **N12** two owner decisions | `kim_biased_exact_le_eps` still has no consumer and no recorded decision (A19); the exact-against-value naming split is unchanged. |
| **N13** the recorded failures | Unchanged. |

---

## 6. S3: `exec_transfer_status`

STATUS records two options and takes neither: "the soundness audit's preferred
option adds a second alias for one value, which the facade's own contract of
one alias per public value refuses and whose docstring would have to narrate
the earlier name, and the alternative renames a public facade alias, which is
the owner's call."

**Recommendation: take the rename, to `uniform_transfer_status`.**

The first option is barred by the facade's own contract, which the file states
as "one alias per public value", and the fix pass's own reason for refusing it
is sound. The second is the only one left, and the name it produces is the one
the other two statuses already use: `biased_transfer_status` and
`repeated_transfer_status` are named after the model family of their path, and
the facade's name for the uniform model is `uniform_sample`. `exec_` names an
execution stage that all three paths share, which is what makes it unreadable
now that there are three.

Collision check for `uniform_transfer_status`: zero whole-word hits over the
whole repository and over `user-contrib`. `exact_transfer_status` would collide
with `instances/psl211/psl211_analysis.v`.

Cost, from a whole-word search over all `.v` files outside `.claude/` and
`history/`. Five sites in three files, every one of which the landing already
edits:

| file | site |
|---|---|
| `instances/kim2025/five_card_analysis.v` | the docstring, the `Definition`, and the `erefl` pin in the retention block |
| `manifest/pgg_analysis_manifest.v` | one `erefl` pin |
| `manifest/pgg_analysis_client.v` | one bare `Check` |

Plus one `Print Assumptions` line in `kim_landing_fidelity.v`, which does not
land. Two `erefl` pins, one bare `Check`, one `Definition` and one docstring.
No file enters the landing's edit set that is not already in it, and no file
with `psl211_endpoints` among its reverse-dependants is touched. The
constraint that originally forced the name, the bare `Check` in
`pgg_analysis_client.v`, is already gone, because the fix pass makes that file
an edited file.

---

## 7. Lines over 80 bytes

Measured in bytes, not characters, over the six files.

| line | bytes | same line in production |
|---|---|---|
| `five_card_analysis.v`, `(** colour_view_RV_E — the same equality as an equality of random variables. *)` | 81 | **Yes**, byte for byte, at `instances/kim2025/five_card_analysis.v:307`. Untouched production, 79 characters with a three-byte dash, and in no diff hunk. |

That is the only one, in all six files. `var_dist_supp.v` and
`five_card_mixing.v` have no production counterpart and no line over 80.
`pgg_analysis_manifest.v`, `five_card_rows.v` and `pgg_analysis_client.v` have
none, and neither do their production counterparts.

Two comment-box lines reach exactly 80 bytes with no space before `*)`. One is
fix-pass text and is A4. The other,
`(* | correctness theorem  | S5Analysis.exec_correct, S5Analysis.exec_recovers,*)`,
is untouched production, at `manifest/pgg_analysis_manifest.v:402`.

---

## 8. Vocabulary

**Barred terms: clean.** Whole-word scan, case-insensitive, of `apex`,
`gate`/`gates`/`gated`/`gating`, `posit`/`posits`/`posited`/`positing` and the
two-character token for a distance, over the six landing files,
`kim_landing_fidelity.v` and `STATUS.md`: **zero hits in all eight.** The only
occurrences anywhere in the directory are inside `naming-audit.md` and
`soundness-audit.md`, where each is quoted as a finding.

The barred token that first-round N6 found at
`pgg_analysis_manifest.v` is gone, replaced by "the sum of the absolute
differences between the cut distribution and group uniform". STATUS records
that `instances/kim2025/five_card_kim.v` carries the same token in a
parenthesis glossing `var_dist` and that the landing does not edit that file,
which is the honest disclosure.

**Narrative and metaphor words for mathematical results.** Three, all SRC
landing text rather than fix-pass text, all recorded above: "the honest one"
twice (A17) and "not a strong statement" once, the last of which is a statement
about how much the bound says and therefore position rather than judgement. No
`escape`, `beats`, `smash`, `dodge`, or `cap` as a noun. "ceiling" as a noun for
two is a metaphor, but it is the tree's established word for that bound and it
is used consistently in every line the landing writes (A14).

---

## What I did not check

- **Nothing was compiled.** Every claim about what type-checks, including that
  the fix pass's restated `kim_biased_sample_cut_witnessE` still fits the
  `sc_Hd` field of `kim_biased_cert` by conversion, rests on STATUS's report of
  twelve files at `rc=0` and on reading the proof scripts. The interderivability
  lemmas of `kim_landing_fidelity.v` were read, not run.
- **No proof script was audited for correctness**, beyond confirming that each
  new lemma's proof applies `var_dist_fdistmap_transfer` to the two premises its
  docstring names.
- **The arithmetic** of the published numbers was taken from the first round's
  N11, not recomputed, except for the coset argument of N6, which I checked.
- **The three files that land unchanged apart from imports**, `pgg_tableau.v`,
  `pgg_tableau_syntax.v` and the three rows files, were diffed against
  production for import lines only; their bodies were not read.
- **`instances/kim2025/five_card_kim.v`, `five_card_models.v` and
  `five_card_exec.v`** were read only where a precedent or an import was in
  question.
- **The soundness audit's own findings** were not re-adjudicated; only the
  naming and comment consequences of the fix pass's response to them.
- **Whether `kim_biased_exact_le_eps` and `var_dist_le2` should be kept** is an
  owner decision under the "claimed or premise" standard, not a naming question.
