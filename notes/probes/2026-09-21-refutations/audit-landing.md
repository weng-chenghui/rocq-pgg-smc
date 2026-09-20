# Combined audit of the refutations landing (2026-09-21)

Working tree on top of `a29635b`, `git diff HEAD` over six production files,
plus `landing_fidelity.v` and the two message files of
`notes/probes/2026-09-21-refutations/`. Nothing was compiled and no Rocq
process was started for this audit; every verdict below is read off the source,
the diff and the recorded messages. Where a claim rests on conversion, it is
marked as resting on the prover's compile.

## Verdict

**GO**, with six comment corrections applied first. Every one of them is a
sentence in a docstring or a file header; none touches a statement, a proof, a
name or a notation, so none of them can change what compiles, and all six sit
in the two categories of prose the landing is already allowed to edit. Three
are MUST: G1 and G2 each state as a fact about the framework something the
framework does not do, and G11 is a count the landing's own added sentence
contradicts fourteen lines later in the same header. G3, G4 and G12 are
SHOULD. The rest are NOTE.

The mathematics is sound. Every new statement is the one the plan's last
section writes, the two corollaries stand in the stated relation to the core,
the PGL(2,7) non-vacuity lemma has the right strictness, and the path the
terminal builds is honest on all five coordinates against the manifest's own
definitions.

## What was checked and found clean

**Pure addition.** Seven lines are removed and all seven are header prose:
`instances/psl211/tableau/psl211_tableau_analysis_bridged.v:39` (one sentence
of the header, extended to seven), `instances/psl211/tableau/psl211_tableau_checks.v:13,26`
(the boundary count and the last sentence of the boundary list), and
`manifest/pgg_tableau_syntax.v:86-89` (the keyword paragraph). All four are in
the categories the task allows. No index entry is removed anywhere. No
existing statement, proof, name or notation changes. `indistinguishability_tail`
is untouched: it and its `Arguments` line appear only as diff context, and the
new lemma is inserted after them.

**The added `Require`.** `From pgg_smc Require Import psl211_reading_constancy.`
at `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:146` creates no
cycle. `instances/psl211/psl211_reading_constancy.v:170-190` requires no
`psl211_tableau_*` file, and the only other importers of it are
`instances/psl211/psl211_colour_reading.v:92` and
`instances/psl211/psl211_tableau_executable.v` (prose reference at :26). The
arrow runs from the mathematics up into the tableau, which
`notes/probes/2026-09-20-tableau-directories-s5/staged/TEMPLATE.md:199-200`
names as the allowed direction.

**`InputDistinguishabilityPropAt`** (`manifest/pgg_tableau.v:1343-1351`) is
exactly what the plan writes: an existential over a coalition below the
threshold and two run arguments, with `c <=` the sum of absolute differences of
the two static readings under `sa_cut_dist sa`, the model's own cut law, with
no law argument (D1's anchoring). Set against
`IndistinguishabilityPropAt` (`manifest/pgg_tableau.v:592-600`), which reads
`forall C x x', #|C| < k -> var_dist ... <= c`, it is the literal quantitative
negation: the same coalition constraint, the same two fdistmaps of
`static_coalition_obs` under the same law, the inequality reversed and the
quantifier dualised. `indistinguishability_number_ge_of_input_distinguishability`
is the one-line consequence of that duality and its proof is
`le_trans Hge (Hprop C x x' HC)`, which is the only proof the shapes admit.
Non-vacuous by construction: no certificate occurs, so the statement is about
the model and a coalition's static reading alone.

**`indistinguishability_prop_of_ideal_close`** (`manifest/pgg_tableau.v:896`,
comment at :885-895) is TRUE and does subsume
`indistinguishability_tail` (`manifest/pgg_tableau.v:871-874`). The tail lemma
concludes `IndistinguishabilityPropAt cert (cert_eps cert)`, and `cert_eps cert`
is `sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert)`
(`manifest/pgg_tableau.v:607-610`), which is the new lemma's `eps + eps` at
`eps := sw_bound_eps (ic_b cert)`. The route the new proof takes is the triangle
inequality with `ic_const` in the middle, and it needs only
`var_dist (sa_cut_dist sa) (ic_ideal cert) <= eps`, which is weaker than the
tail lemma's route through `ic_close` and `ic_Hd`. Landed beside the tail lemma
as a pure addition, as the plan says.

**`no_indistinguishability_cert_ideal_close_of_input_distinguishability`.** The
law is the model's own (`sa_cut_dist sa`, no free law argument). The strictness
is right: from `eps + eps < c` the composite gives `c <= eps + eps`, and
`le_lt_trans` then produces `c < c`. At `eps + eps = c` there is no
contradiction and the lemma correctly does not claim one.

**The PSL(2,11) facts.** The core is at `psl211_perdeck_coalition`, the three
seats 0, 1 and 2 (`instances/psl211/psl211_models.v:790-792`, exactly three, not
merely the `<= 3` of `psl211_perdeck_coalition_le3`), at the two run arguments
`(true, psl211_perdeck_deal)` and `(false, psl211_perdeck_deal)`, at the constant
`(#|pgg_G psl211_M|%:R)^-1`. That constant is right: the two masses at the point
`psl211_perdeck_view` are `0` and `(#|pgg_G psl211_M|%:R)^-1` (the two mass
lemmas), `leq_var_dist p q a` gives `|p a - q a| <= var_dist p q`, and
`Habs0` computes `|0 - 1/#|G|| = 1/#|G||`. The `eq_ind` at the end rewrites the
left-hand side of the `leq_var_dist` instance by `Hval`, giving the goal
verbatim. The group order is 660 (`instances/psl211/psl211_closure.v:63`,
`psl211_card`). `psl211_alldecks_input_distinguishability` supplies exactly the
existential's three witnesses and discharges the threshold conjunct with
`psl211_perdeck_coalition_below_k` (the threshold is six,
`instances/psl211/psl211_profile.v:134`, so three seats are below it).
Both mass lemmas are in term mode: `etrans` of two `congr1`s, no `rewrite` on
the reader, with the 228 s measurement recorded in a non-rendered source comment
at `instances/psl211/psl211_reading_constancy.v:862-865` rather than in a
docstring.

**D2 is answered.** `psl211_alldecks_indistinguishability_number_ge` still
quantifies over a certificate, but it is now a `Corollary` of the
certificate-free `psl211_alldecks_input_distinguishability`, and its own
docstring says "whatever the program's certificate" and points at the
certificate-free theorem as the source. The quantifier can no longer be read as
carrying the content, because the content is proved without it. That is D2's
replacement.

**The four points about the manifest** (audit's "What the landed comment must
say about the manifest", D24) are all present at
`instances/psl211/tableau/psl211_tableau_analysis_bridged.v:513-529`: the
manifest records paths and imposes duties on paths; no duty requires a
published program to have one; the single coordinate with no honest value is
the capability line, whose closed vocabulary is quoted; extending that
vocabulary is the owner's call. The closing sentence about a twelfth path is
correct: the manifest has eleven typed paths
(`manifest/pgg_analysis_manifest.v:2104`), and `psl211_alldecks_path`
(`manifest/pgg_analysis_manifest.v:1076-1078`) is
`MkAnalysisPath PSL211Analysis.observed AnalysisBridged PSL211Analysis.exact_family
StaticExecutedOnly BaselineClassicalOnly`, which agrees with the obstruction's
path on the observed execution, the level, the model family and the assumption
status and differs in the transfer status alone, exactly as the comment says.

**D10 quotations are verbatim.** `publish_obstruction_completionE`'s comment
quotes `manifest/pgg_analysis_manifest.v:40-42` word for word, "limitation
theorem about the same distribution and the same observer" included.
`publish_obstruction_transferE` and the published program's comment quote
`manifest/pgg_analysis_status.v:68-69`, "NegativeTransfer is a theorem
transporting an obstruction to the path's observer", word for word.

**D4, D5, D9, D25, D26 are all discharged.** The published program's comment
names `psl211_alldecks_no_small_eps_cert` and states the relation (the landed
statement constrains where the ideal sits, the existing one constrains the
certificate's own marginal bound, and the second follows by the same route at
the certificate's own number), and the existing theorem is not edited. The
non-conflict with the exact-independence program is explained by the quantifier
over the run argument, with the reindexing named as a second and separate fact,
in the order D5 asks for. `ObstructionPayload`'s comment says the kind may
differ at each field and index (D9). The number bound's comment carries the
over-reading guard (D25). Each mass lemma's comment names
`psl211_alldecks_constancy_false_close`
(`instances/psl211/psl211_reading_constancy.v:658`) as the lemma that computes
it inline (D26).

**The factor two.** `var_dist` is the sum of absolute differences, so it is
twice the total variation distance, and the advantage at the two named run
arguments is at least half of the number. The three places that say so
(`psl211_alldecks_perdeck_reading_ge`, the published program's comment, and the
`InputDistinguishabilityPropAt` comment) all divide and none multiplies: 1/660
in the sum of absolute differences gives advantage at least 1/1320. The
arithmetic is right in all three.

**Nothing over-claims.** No sentence anywhere in the diff says or implies that
input indistinguishability is refuted at this model at every number. Each
statement of the refutation is quantified: "every number ... is at least
1/660", "no certificate ... once eps added to itself stays below 1/660". A
program publishing a number of 1/660 or more is explicitly left standing by the
number bound's own comment.

**The record and the terminal against `PublishedSampled`/`publish_sampled`.**
Five fields (at, path, kind, thm, pf) against `PublishedSampled`'s three
(`manifest/pgg_tableau.v:1194-1197`); `: clear implicits` on the three fields
whose types unfold to quantified statements, matching
`Arguments published_observed_thm : clear implicits`
(`manifest/pgg_tableau.v:1187`) and the same reason given; six coordinate
equations covering all five path coordinates plus the kind, where
`publish_sampled` has three; three readers matching
`run_correct_of_sampled`/`view_identification_of_sampled` plus `obstruction_of`.
The terminal writes `AnalysisBridged` and `NegativeTransfer` itself and takes
the assumption status as the line's payload, on the same footing as the other
three terminals.

**The surface rule.** `s |> publish Obstruction o by pf a` puts the obstruction
in the column the transfer status occupies in the other two publish rules and
the assumption status last (D11, D27), and the use site at
`instances/psl211/tableau/psl211_tableau_analysis_bridged.v:530-533` writes it
in that order. The keyword paragraph carries the measurement date 2026-09-21,
the measured facts (follows the literal `publish`; stays a binder name and a
top-level identifier), the count of nineteen unchanged, and no history words.
The caveat sentence about the transfer-status slot is correctly updated from
two tokens to three.

**Layout.** No added line exceeds 80 bytes in any of the six files. Every added
boxed comment line is exactly 80 bytes with a space before the closing `*)`;
the only added lines that are 80 bytes without that space are the all-star rule
lines, which is the repository's form. All five new banners are one content
line and carry no probe, ledger, plan or audit token. Index entries are
complete and in file order: in
`instances/psl211/psl211_reading_constancy.v` the five new entries sit between
the `psl211_alldecks_no_zero_eps_cert` entry and
`psl211_alldecks_constancy_false_word584`, which is the declaration order
(:762, :786, :813, :847, :899, :921, :970).

**Names.** Every landed name is the plan's decision 8 name, and every one is
free across all tracked `.v` files outside `notes/`, legacy included. Forty-one
names checked, zero collisions.

**`landing_fidelity.v`.** Production only: its `Require` list
(:9-27) names `pgg_smc` modules alone, with no `From refuteprobe` line. Every
landed declaration is pinned at its full statement, counted against the diff:
twenty framework declarations plus the five record fields and the constructor,
the surface rule with its desugaring, five psl211 mathematics declarations,
seven psl211 phase declarations, and the PGL(2,7) lemma. The `Print Assumptions`
lines are present for the core, the number bound, the published program, the
program's reader and the PGL(2,7) lemma; their output is not verified here
because nothing was compiled.

## The removed lines, one by one

| removed line | file:line | class |
|---|---|---|
| `(* coalition_reading_constancy and refutes it in both run modes.              *)` | `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:39` | header prose of a file receiving a declaration; replaced by the same sentence plus six lines introducing the third program. Allowed. |
| `(* Three boundaries are recorded. The first is that an obligation built where *)` | `instances/psl211/tableau/psl211_tableau_checks.v:13` | header prose of a file receiving a declaration; the count three becomes four. Allowed, and the new count is right: the file records four boundaries in six `Fail` terms, the third and fourth each carrying two. |
| `(* that field being one term.                                                 *)` | `instances/psl211/tableau/psl211_tableau_checks.v:26` | header prose; the sentence continues into the fourth boundary. Allowed. |
| `(* s5_tableau_sampled.v write it. The count of nineteen is unchanged. Inside  *)` and the three lines after it | `manifest/pgg_tableau_syntax.v:86-89` | the keyword paragraph of the syntax header. Allowed. |

No other line is removed, in any file. Nothing in the `Definitions:` or
`Key results:` index of any file is removed, and no `Require` line is removed.

## Findings

Six of the twelve findings ask for a sentence to change inside an 80-byte
comment box or an 80-byte docstring. The replacements below are written as
prose, not as padded lines: a fix pass rewraps each to the file's columns.

| id | class | file:line | the name, sentence or finding | rule, problem and evidence | replacement |
|----|-------|-----------|-------------------------------|----------------------------|-------------|
| G1 | MUST | `manifest/pgg_tableau.v:1568`; `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:488`; `instances/psl211/tableau/psl211_tableau_checks.v:27` | "the five security readers of this file project a BridgedProp out of a PublishedAt" (and the two restatements of it) | A statement comment must be true of the code it sits on. Six definitions in `manifest/pgg_tableau.v` take a `PublishedAt c`: `run_correct_of` (:1123), `view_identification_of` (:1130), `view_secrecy_of` (:1136), `view_indistinguishability_of` (:1144), `view_proximity_of` (:1153), `security_property_of` (:1161). Exactly five of them project out of the third field `published_thm : BridgedProp c published_at`; the sixth, `security_property_of`, does not — it returns `ab_security_property (published_at r) R idx : SecurityProperty` and never touches the third field. That sixth reader is the one the checks file's second recorded rejection is about. So the sentence either counts five and leaves the reader it records outside the claim, or counts `security_property_of` among the five and is false of it. The file already has the right form for this claim in its own header at `manifest/pgg_tableau.v:85-88`, about `PublishedObserved` and `PublishedSampled`: "inductive types distinct from PublishedAt, which is what makes every security reader inapplicable to a value of either". No count, no projection claim. | At `manifest/pgg_tableau.v:1566-1570`: "It is the whole of what such a value says beyond the Sampled level: every reader of this file that names a security statement or a security property takes a PublishedAt, and PublishedObstruction is a different inductive type, so none of them applies to a value of it." At `psl211_tableau_analysis_bridged.v:486-490`: "It certifies no security property: its data carries no SecurityEvidence, and every reader of manifest/pgg_tableau.v that names one takes a PublishedAt, a different inductive type." At `psl211_tableau_checks.v:26-30`: "The fourth is which readers reach a published obstruction. The readers of manifest/pgg_tableau.v that name a security statement or a security property all take a PublishedAt, and PublishedObstruction is a different inductive type with no coercion into it, so none of them applies; the two terms below are the two spellings that were checked." |
| G2 | MUST | `manifest/pgg_tableau.v:1413-1415` | "a number at or below zero makes that member's proposition hold at every model, var_dist being non-negative" | The sentence is D1's second option, and it overstates what is true. `InputDistinguishabilityPropAt sa c` (:1343-1351) is an existential over a coalition `C` with `#\|C\| < profile_k (instance_profile A)` and over two run arguments `x x' : ex_inputT E`. At `c <= 0` the inequality conjunct is free, but the proposition still asserts that such a `C` and such an `x` exist. It therefore holds at every model whose threshold admits some coalition and whose run-argument type is inhabited, not at every model. Neither `ObstructionKind` nor `publish_obstruction` constrains `c` in sign, so a reader of a published obstruction must read the number, and the comment is the only place that says so. | "The one member carries the number the model is distinguishable at, and nothing in this enumeration or in the terminal below constrains it: at a number at or below zero the inequality conjunct is free, var_dist being non-negative, so the member's proposition then holds at every model with a coalition below the threshold and an inhabited run-argument type, and a reader of a published obstruction reads the number before the kind." |
| G11 | MUST | `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:25`, and `:422` | "Two programs are published here and they part at the model."; "the two programs of this instance are each written once above the model they branch at" | Both counts are stale after the landing and the first is contradicted fourteen lines later by the landing's own sentence at `:39-41`, "A third program over the all-decks model publishes that reason rather than describing it". The file now defines three published programs: `psl211_alldecks_published`, `psl211_word_proximity_published` and `psl211_alldecks_obstruction_published` (`:530`). Header prose of a file receiving a declaration is inside the allowed edit set, so this costs nothing to fix. | At `:25`: "Two programs with security evidence are published here and they part at the model." At `:420-423`: "psl211_word_proximity_published_sampledE — the proximity program too is its named Sampled value with the payload and the terminal adjoined, so the two programs with security evidence are each written once above the model they branch at." |
| G3 | SHOULD | `instances/psl211/tableau/psl211_tableau_checks.v:157-158` | "(* The message is the one above, at the second argument position of the reader. *)" | The clause is false and distinguishes nothing. `landing_draft_reader_secrecy.msg` reports the error at line 21, characters 23-24 of `Check (view_secrecy_of r).`, which is the token `r`; `landing_draft_reader_property.msg` reports it at line 21, characters 28-29 of `Check (security_property_of r).`, also the token `r`. Under `Arguments view_secrecy_of {c} r` (`pgg_tableau.v:1138`) and `Arguments security_property_of {c} r R idx` (`pgg_tableau.v:1165`), `r` is the first explicit argument in both. The two messages are identical apart from those coordinates. | "(* The message is the one above, word for word, at the same argument. *)" |
| G4 | SHOULD | `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:44-45` | "its path records NegativeTransfer where the two above record a security claim" | Type-honest phrasing: a transfer status is set against a claim, and a claim is not a value of `TransferStatus`. `psl211_alldecks_path` records `StaticExecutedOnly` (`manifest/pgg_analysis_manifest.v:1076-1078`), which per `manifest/pgg_analysis_status.v:69-71` carries no transfer theorem at all, so "a security claim" does not name what the contrast is between either. | "It certifies no security property, and the transfer coordinate of its path is NegativeTransfer where the all-decks path the first of the two above describes records StaticExecutedOnly." |
| G12 | SHOULD | `manifest/pgg_tableau.v:1493-1494` | "The assumption status is the line's payload, as it is at the two terminals below." | The two terminals meant are `publish_observed` (:1225) and `publish_sampled` (:1242), and both sit above this one in the file; the new section is inserted at :1328, after `view_identification_of_sampled`. Read positionally the sentence is false. The intended sense is almost certainly the section title "Handing a program over below AnalysisBridged", and one word settles it. The neighbouring `publish_obstruction_assumptionsE` comment at :1547-1548 already says "the other three terminals", which is unambiguous and correct. | "The assumption status is the line's payload, as it is at the two terminals below AnalysisBridged." |
| G5 | NOTE | `instances/psl211/tableau/psl211_tableau_checks.v:141-143` | "That reader projects the third field of a PublishedAt" | `view_secrecy_of r := proj2 (published_thm r)` (`pgg_tableau.v:1136-1137`): it takes the second conjunct of the third field, not the field. The rejection's reason is unaffected, so this is precision only. | "That reader is the second conjunct of the third field of a PublishedAt, and a published obstruction is a value of a different inductive type, so the rejection is a failure to unify the two record types:" |
| G6 | NOTE | `manifest/pgg_tableau.v:1355-1356` | "so a model's sharpest statement is the one at the largest number its own two readings reach" | D8 asked for downward closure and an open bound in place of a largest element. Downward closure is now stated, and for one fixed coalition and one fixed pair of run arguments the largest admissible `c` is attained, at their `var_dist`. Over all pairs it need not be, since `ex_inputT E` carries no finiteness. The sentence reads as the second. | "The family is downward closed in c, so the sharpest statement one coalition and one pair of run arguments support is the one at the distance between their two readings." |
| G7 | NOTE | `manifest/pgg_tableau.v:1357` (`input_distinguishability_prop_le`), `:1392` (`no_indistinguishability_cert_ideal_close_of_input_distinguishability`), `:1578` and `:1587` (`run_correct_of_obstruction`, `view_identification_of_obstruction`) | four landed declarations with no use site in the tree | "Keep only claimed or premise". `input_distinguishability_prop_le` has two occurrences tree-wide, its index entry and its statement. `no_indistinguishability_cert_ideal_close_of_input_distinguishability` is named in the published program's docstring but applied nowhere. The two readers mirror `run_correct_of_sampled` and `view_identification_of_sampled`, which are equally unapplied, so the terminal family's API is complete by the existing pattern rather than dead weight. Recorded, not objected to. | None. If the owner prunes, prune the pair at `publish_sampled` in the same pass, not this one alone. |
| G8 | NOTE | `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:522-525` | "correctness, exact privacy, approximate privacy, trace secrecy, conditional entropy, mutual information and endpoint marginal mixing" | Duty (3) at `manifest/pgg_analysis_manifest.v:68-71` reads "... mutual information **or** endpoint marginal mixing". The list is not inside quotation marks, so this is not a misquotation, but D10's standard is that the manifest's own words are used. | "... conditional entropy, mutual information or endpoint marginal mixing". |
| G9 | NOTE | `manifest/pgg_tableau_syntax.v:86` | "Obstruction is a third token of that kind" | `Observed` and `Sampled` are `CompletionLevel` constructors and the preceding sentence says so; `Obstruction` names no declaration in the tree. The clause that follows ("it stays a binder name and a top-level identifier") states the measured fact correctly, so "of that kind" is loose rather than wrong. | "Obstruction sits in the same position, measured on 2026-09-21 in the same way: it follows the literal publish in the terminal rule handing over an obstruction, and it stays a binder name and a top-level identifier in a file whose Require lines are ssreflect and this one." |
| G10 | NOTE | `notes/probes/2026-09-21-refutations/landing_fidelity.v:86-95` | `ObstructionKind` is the one landed declaration with no `Check` of its own | Every other landed declaration is pinned at its full statement. `ObstructionKind` appears only in the codomain of the constructor's ascription (:88) and inside `ObstructionPayload`'s (:95), which pins its arity and its result sort but not its own signature. | Add `Check (@ObstructionKind : forall (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A), SampleAdapter R (instance_exec E) -> Type).` before line 86. Fidelity file only; not a production change. |

## Things the audit could not settle without compiling

1. `psl211_alldecks_obstruction_pf` gives `psl211_alldecks_input_distinguishability R`,
   stated at `psl211_alldecks_sample R`, where the payload is at
   `amf_sample psl211_exact_family R idx`. That the two adapters are
   convertible is D4's "landing's first step" and is settled by the file
   compiling, which the prover reports and this audit did not repeat.
2. The six `exact: erefl` path equations and `by []` on the transfer
   disequality rest on conversion at the facade's vocabulary. Same standing.
3. The `Print Assumptions` output of `landing_fidelity.v` (the three classical
   axioms) is reported by the prover and not re-read here.
