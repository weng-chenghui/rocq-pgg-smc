# Audit round 4 of stage A, fix pass 3

Date 2026-09-19. Opus auditor, independent of the prover. I wrote none of the
probe, none of the production files it copies, and none of the three earlier
audit rounds. Everything below is checked against the frozen export at
`scratchpad/extA_fix3_frozen/notes/probes/2026-09-19-tableau-extensions/`,
against `history/*.6-before-fix3` in that directory, against the production
files at commit `d5f70cd`, and against my own compiles. Scratch files are in
`scratchpad/extA_audit4/`.

## What I compiled

A fresh copy of the ten frozen `.v` files in `scratchpad/extA_audit4/copy`, in
the probe `_CoqProject` order, with the production `_CoqProject` flags and
`-Q <copy> tableau_ext_probe` last, one process at a time through
`scratchpad/rocq1`. No `.vo` the prover produced was read. All ten returned
`rc=0`.

| file | my wall | F5 | my slowest sentence | F5 |
|---|---|---|---|---|
| `pgg_tableau.v` | 14.2 s | 14.1 s | 4.167 s, `Definition ab_port` | 4.22 s, same |
| `pgg_tableau_syntax.v` | 4.9 s | 5.3 s | 1.534 s, a `Require Import` | same kind |
| `pgl27_rows.v` | 6.9 s | 7.0 s | 2.105 s, a `Require Import` | same kind |
| `five_card_rows.v` | 5.0 s | 5.0 s | 1.515 s, a `Require Import` | same kind |
| `s5_rows.v` | 4.4 s | 4.5 s | 1.945 s, a `Require Import` | same kind |
| `psl211_rows.v` | 5.9 s | 5.9 s | 1.513 s, a `Require Import` | same kind |
| `t0_sampled_branch.v` | 4.2 s | 4.3 s | 1.898 s, a `Require Import` | same kind |
| `t0_sampled_branch_pgl27.v` | 4.7 s | 4.7 s | 2.269 s, a `Require Import` | same kind |
| `g2_keyword_measure.v` | 4.1 s | 4.1 s | 2.009 s, a `Require Import` | same kind |
| `assumptions_report.v` | 50.2 s | 53.2 s | 20.522 s, `Print Assumptions psl211_row_alldecks_armE` | 21.91 s, same |

The compile table of F5 is reproduced within noise. No sentence outside a
`Print Assumptions` command reaches 5 s, as F5 says. The report prints
**34** `Axioms:` blocks. The only constant names in those blocks are
`propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description` and
`rigidity_s5_instance.s5_group_order_eq`, the last at the S5 block alone.
F5's count and its constants are correct. The scan allowed dots in names.

Targeted experiments, each against the built `.vo` so that only the sentence
is timed:

| experiment | scratch file | result |
|---|---|---|
| `reflexivity` on the `five_card_row_repeated39_atE` goal | `copy/f4_refl.v` | **0.068 s**, `Qed.` 0.000 s |
| `exact: erefl` on the identical goal | `copy/f4_erefl.v` | **156.916 s**, `Qed.` 0.005 s |
| `exact: (erefl (published_at five_card_row_repeated39))` | `copy/f4_alt.v` | **162.045 s**, `Qed.` 0.006 s |
| `Print` of both proof terms | `copy/f4_refl.v` | both are `erefl` at the same type |
| `Print Assumptions` of both | `copy/f4_refl.v` | the three boolp constants, nothing else |
| the recorded failure without `Fail` | `copy/f4_unindexed.v` | one error, at the payload, quoted below |
| `1/25 < cert_eps (kim_biased_cert R tt)` | `copy/f4_arith.v` | `Qed` |
| `sw_bound_eps (kim_biased_marginal_bound R) < 1/25` | `copy/f4_arith.v` | `Qed` |
| the proposed swap in A5 below | `copy/f4_swap.v` | `rc=0`, `exact: erefl` at 0.001 s |

Every `.v` file of the probe was diffed against `history/*.6-before-fix3` and,
separately, against its production counterpart, both raw and with a
nesting-aware and string-aware Rocq comment stripper (`extA_audit4/strip.py`).

## Findings

| ID | sev | file:line | claim | evidence | proposed replacement, checked |
|---|---|---|---|---|---|
| A1 | SHOULD | `five_card_rows.v:826-829` and `STATUS.md:1176-1180` | the docstring of `five_card_row_biased_inv25` says it continues from the exact certificate "because a row publishes a number at least its certificate's and the bundle's number, sqrt 5 over forty, is above one twenty-fifth", and F2 says "the one-cut bundle's number is sqrt 5 over forty, about 0.0559" | the file fixes the meaning of "the bundle's number" three times and it is not sqrt 5 over forty. `five_card_rows.v:547`: "The one-cut bundle's marginal bound is sqrt 5 over eighty. A row built on it publishes twice that". `kim_biased_epsE` at `:550`: `sw_bound_eps (kim_biased_marginal_bound R) = Num.sqrt 5%:R * (1 / 80)`. `kim_biased_cert_epsE` at `:709`, under the docstring "twice the bundle's spectral number ..., sqrt 5 over forty". I compiled `sw_bound_eps (kim_biased_marginal_bound R) < 1/25` and `1/25 < cert_eps (kim_biased_cert R tt)`, both `Qed`, in `copy/f4_arith.v`. So the sentence as written is refuted by its own file, while the conclusion it draws is right at the object it should have named | replace `five_card_rows.v:828-829` by three lines, of 74, 68 and 20 bytes: `    at least its certificate's, and the bound kim_biased_cert publishes is` / `    twice the bundle's number, sqrt 5 over forty, which is above one` / `    twenty-fifth. *)`. `STATUS.md:1177-1178`: "a number at least the certificate's, and `kim_biased_cert` publishes twice the one-cut bundle's number, sqrt 5 over forty, about 0.0559, while the constant" |
| A2 | SHOULD | `STATUS.md:1088`, `:1090` | E6 is headed "Names that no longer exist" and its universal is that every back-quoted Rocq name in the note outside the table exists in a `.v` file of the probe or of production, "checked mechanically over 198 production and 10 probe files" | the refresh of F2 put four of the listed names back. `five_card_row_repeated39`, `kim_centi_cert`, `kim_centi_cert40` and `kim_centi_cert_eps_lt` are all in the frozen `five_card_rows.v` and in `instances/kim2025/five_card_rows.v`. `five_card_row_repeated39_bare` is at `instances/kim2025/five_card_rows.v:761`. `var_dist_le2` is in three production files, `lib/var_dist_supp.v`, `instances/kim2025/five_card_mixing.v` and `instances/kim2025/five_card_rows.v`, and in the probe copy. The mechanical check was not re-run after the refresh | delete the rows `five_card_row_repeated39, five_card_row_repeated39_bare, kim_centi_cert, kim_centi_cert40, kim_centi_cert_eps_lt` and `var_dist_le2` from the E6 table and re-run the check. A seventh name in the table, `eq_le`, is glossed "a lemma the brief named and MathComp does not have"; MathComp does have `eq_le`, with the statement `(x == y) = (x <= y <= x)%O`, which is why infotheo introduced `eqW` beside it, see the comment above `ssr_ext.v:1224`. Gloss it "a lemma with the statement the brief wanted, which MathComp's `eq_le` does not have" |
| A3 | SHOULD | `STATUS.md:88-116` and `:76-77` | Step 2's block is introduced by "As compiled:" and shows `five_card_row_uniform_branch_atE` as a three-way conjunction closed by `Proof. split; exact: erefl. Qed.`, and line 76 says that lemma "proves it is not [two claims], since the two continuations hold one `AnalysisBridged` coordinate" | fix pass 3 applied A8 and split that lemma. `t0_sampled_branch.v:111-122` now holds two lemmas, each a single equation closed by `exact: erefl`, and `five_card_row_uniform_branch_atE` alone relates the first continuation to the unbranched program and says nothing about the second. F3 records the split at `:1247-1251` but Step 2 was not updated, so the note's only "as compiled" transcript of that file is now false | replace `STATUS.md:109-116` with the two lemmas as they stand in `t0_sampled_branch.v:111-122`, and at `:76` write "and `five_card_row_uniform_branch_atE` with `five_card_row_uniform_branch_ideal_atE` prove it is not, since both continuations hold one `AnalysisBridged` coordinate" |
| A4 | SHOULD | `STATUS.md:1192-1197` | F2's withdrawal table is introduced as "Their uses, measured over the tree" | two production uses are absent. `kim_centi_marginal_bound40` is used at `instances/kim2025/five_card_rows.v:730`, inside `kim_centi_cert40`'s definition, and the table's production column for that row names `five_card_mixing.v` alone. `kim_centi_cut_mixing40` is used at `instances/kim2025/five_card_rows.v:733`, the same way, and its row says "the same file". The `kim_centi_cert40` row omits the occurrence at `instances/kim2025/five_card_rows.v:739`, inside `kim_centi_cert40_epsE`'s statement. The "elsewhere" column of the `kim_centi_cert40` row omits `notes/20260919-kim-spectral-landing-design.md:42,176` and `notes/2026-09-19-112500-spectral-arm-at-kim-and-psl211-summary.md:187`. Every other entry checks out: `kim_centi_cert40` at `:98`, `:726`, `:754`, `:765`; `kim_centi_cert40_epsE` at `:149`, `:738`; `kim_centi_marginal_bound40` at `five_card_mixing.v:35`, `:507`, `:518`, `:520`; `kim_centi_cut_mixing40` at `five_card_mixing.v:65`, `:517` | add to the `kim_centi_marginal_bound40` row "and `instances/kim2025/five_card_rows.v`, inside `kim_centi_cert40`'s definition", the same to the `kim_centi_cut_mixing40` row, add "`kim_centi_cert40_epsE`'s statement" to the first row's production column, and add the two note files to its "elsewhere" column. The four are still withdrawable together, because every unlisted use is inside `kim_centi_cert40`, which the same withdrawal removes |
| A5 | SHOULD | `t0_sampled_branch.v:119-122` | F3 says A8 was applied by splitting into "the two lemmas the PGL(2,7) file has" | the names mirror, the statements do not. `t0_sampled_branch_pgl27.v:115-118` reads `published_at pgl27_row_exact_branch = published_at pgl27_row_exact_branch_ideal`, subject on the right. `t0_sampled_branch.v:119-122` reads `published_at five_card_row_uniform_branch_ideal = published_at five_card_row_uniform_branch`, subject on the left. The probe now holds one convention per file, and the five-card one is the convention round-3 A9 proposed for the PGL(2,7) file and F3 declined at `:1256-1264` | swap the five-card one to match the sibling. I compiled it: `copy/f4_swap.v`, `rc=0`, `exact: erefl` at 0.001 s. Text: `Lemma five_card_row_uniform_branch_ideal_atE :` / `  published_at five_card_row_uniform_branch` / `  = published_at five_card_row_uniform_branch_ideal.` / `Proof. exact: erefl. Qed.` Swapping the PGL(2,7) pair instead is the other resolution and costs more, because it falsifies the source note named in A9's second reason |
| A6 | SHOULD | `STATUS.md:8`, `:18`, `:260`, `:633` | the verdict table and the step headings label the C rows against the spec | the labels are shifted by one. Spec C1 at `notes/20260919-tableau-three-extensions-probe-design.md:179` is "`conclude` with an inequality ... Every existing `conclude` compiles with its payload changed", which STATUS splits into its C1 and C2. Spec C2 at `:180` is "A number below the proved one cannot be published", which is STATUS's C3 heading at `:260`. Spec C3 at `:181` is "The repeated five-card row publishes 2^-39 from the number it proved ... with the certificate's epsilon left at the spectral number", and STATUS has no heading and no verdict row for it. `STATUS.md:633` compounds this: it says "The spec's ledger row C2 expects 'every existing `conclude` in the five importer copies' to need a payload change", which is the spec's C1. A reader of the verdict table would take spec C3 to be covered by `pgl27_reprice41`, which is the spec's C2 | relabel: STATUS's C1 and C2 both answer spec C1, STATUS's C3 answers spec C2, and add a verdict row `| C3 | GO | five_card_rows.v, five_card_row_repeated39 continuing from kim_centi_cert |`. The row is earned: see the confirmation C3 below |
| A7 | SHOULD | `pgg_tableau.v:117`, `pgg_tableau_syntax.v:69`, `:129` | F4 is headed "The sentences a third arm makes false" and closes with a Counts list of the two sentences whose count stage B edits | three more sentences count the arms by proxy and are in neither list. `pgg_tableau.v:117` is the banner `(*     The two security witnesses   ...   *)` over `ExactWitness` and `SpectralCert`; spec P2 at `:181` of the design note gives stage B a third certificate record. `pgg_tableau_syntax.v:69` says the tokens "keep the two port constructors and the `conclude` terminal usable by name", and stage B adds `IdealProximity` as a third constructor, which F4 itself names at `:1319-1321`. `pgg_tableau_syntax.v:129` is the banner `(*     The two typed builders   ...   *)` over `mk_exact` and `mk_spectral`. The literal phrases the round-3 list chased are all gone: I swept the ten `.v` files for "two arms", "both arms", "which of the two", "neither arm", "either arm" and "the other arm" and found none | add three rows to the Counts list rather than rewrite, since each count is the point of its sentence, exactly as F4 treats "There are five statements": `pgg_tableau.v`'s banner over the witness records, `pgg_tableau_syntax.v`'s "the two port constructors", and `pgg_tableau_syntax.v`'s banner over the typed builders. The banners are padded to exactly 80 bytes, so stage B's rewrite must re-pad |
| A8 | NOTE | `five_card_rows.v:794-797` | the source comment above `five_card_row_repeated39_atE` says "the refine path ssreflect's `erefl` takes spent 151 s here against `reflexivity`'s 0.07 s. Measured on 2026-09-19; the numbers are in STATUS.md, under the Kim refresh" | 151 s is the file wall, not the sentence. F2 at `:1169` gives the sentence as 147.07 s and the file as 151.6 s. My own reproduction of the sentence against the built `.vo` is 156.916 s. And "STATUS.md, under the Kim refresh" names no heading: the section is "Fix pass 3, after the third audit and two landings", subsection F2. Since `five_card_rows.v` is a production file, a landing carries this pointer into a tree where a bare `STATUS.md` locates nothing. The four production comments that cite a probe all give the full path, `psl211_alldecks.v:865`, `:1175`, `psl211_rows.v:74`, `psl211_spectral_constancy.v:71` | write "spent 147 s here against `reflexivity`'s 0.07 s" and "the numbers are in `notes/probes/2026-09-19-tableau-extensions/STATUS.md`, under F2" |
| A9 | NOTE | `five_card_rows.v:737` | `kim_centi_cert40`'s docstring opens "The repeated row's certificate with the constant in the marginal-bound field" | after the route change the repeated row carries `kim_centi_cert`, not `kim_centi_cert40`, and no program in the file carries `kim_centi_cert40`. The index line at `:98` is unaffected, because it says what the two certificates are and not what uses them, and the section banner at `:733` is unaffected too | "A certificate over the repeated row's model with the constant in the marginal-bound field", which stays true whichever certificate a row carries |
| A10 | NOTE | `pgg_tableau_syntax.v:329`, `:367`, `:390` | the three over-80-byte lines are recorded as byte-identical to production | they are, at production `manifest/pgg_tableau_syntax.v:323`, `:361`, `:384`. I compared the bytes, not the numbers. The six-line offset is the `conclude` notation rule stage A inserts above them | none needed; anyone re-checking should match by content, since the line numbers differ by six |

## Confirmations, with the evidence

**The diff.** `pgg_tableau_syntax.v`, `s5_rows.v`, `t0_sampled_branch_pgl27.v`,
`g2_keyword_measure.v` and `_CoqProject` are byte-identical to
`history/*.6-before-fix3`. With comments stripped, the pass changed **no code
at all** in `pgg_tableau.v`, `pgl27_rows.v` and `psl211_rows.v`: every one of
those 30, 2 and 35 changed lines is a comment. The code changes of the pass
are confined to three files. In `t0_sampled_branch.v`, the A8 split. In
`assumptions_report.v`, four added `Print Assumptions` commands. In
`five_card_rows.v`, the refresh.

**The two refreshed copies against production.** `psl211_rows.v` differs from
`instances/psl211/psl211_rows.v` in exactly three places, which is what F1
says: the framework import repointed to `tableau_ext_probe`, one index line,
and `psl211_row_alldecks_armE` after `psl211_row_alldecks_rowE`.
`five_card_rows.v` differs from `instances/kim2025/five_card_rows.v`, comments
stripped, in exactly six places: the two framework imports repointed,
`five_card_row_uniform_armE`, the two concluded programs rewritten in the
keyword surface with payloads of type `<=`, the recorded failure renamed and
rewritten the same way, and `five_card_row_repeated39_atE`. That is the
claimed list, with one compression worth naming: `five_card_row_repeated39`
also changes its certificate from `kim_centi_cert40` to `kim_centi_cert`,
which the one-line summary folds into "the keyword surface" and which F2
states in full.

**The unrefreshed copies.** `instances/pgl27/pgl27_rows.v` last moved at
`c17fe95`, 2026-09-14, and `instances/s5/s5_rows.v` at `e0ca7b9`, 2026-09-14,
both before the probe took its copies on 2026-09-19, so no refresh was owed.
I checked the stronger property too: with comments stripped, the copies of
`pgl27_rows.v`, `s5_rows.v`, `pgg_tableau.v` and `pgg_tableau_syntax.v` differ
from production only by stage-A additions. There is no stale production
content in any of them.

**C3 of the spec is met.** `five_card_row_repeated39` continues from
`kim_centi_cert`, whose `cert_eps` is
`Num.sqrt 5%:R * (1 / 80) ^+ 7 + Num.sqrt 5%:R * (1 / 80) ^+ 7` by
`kim_centi_cert_epsE`, the spectral expression and not a constant. It reaches
the published constant through `kim_centi_cert_eps_lt`, whose statement in
production and in the copy is `cert_eps (kim_centi_cert R idx) < 2%:R ^- 39`,
a strict inequality in the direction `conclude` needs, weakened by
`Order.POrderTheory.ltW` to the `<=` that `ConcludePayload` asks for. So the
row publishes 2^-39 with the certificate's epsilon left at the spectral
number, which is the spec's C3 word for word. Before this pass the row ran
through `kim_centi_cert40`, whose epsilon is `2%:R ^- 40 + 2%:R ^- 40`, a
constant, and C3 was not met. This is the substantive gain of the pass.

**`reflexivity` is sound here in every sense that matters.** The proof term is
`erefl` under both tactics, printed side by side at the same type in
`copy/f4_refl.v`. `Print Assumptions` gives the three boolp constants and
nothing else under both. The `Qed.` sentence costs 0.000 s after `reflexivity`
and 0.005 s after `exact: erefl`, so the kernel conversion the goal needs is
cheap under both and the entire cost is in ssreflect's elaboration. Supplying
the argument explicitly does not recover it: `exact: (erefl (published_at
five_card_row_repeated39))` cost 162.045 s, slightly worse than the bare form.
The campaign rule bars `by []` and `done` on a `published_at` equation because
`done` spends a search that does not return, and F2 is right that this is not
the cause here. I found no `published_at` equation in the probe closed by
`by []` or `done`. The `_armE` lemmas do use `by []`, but their goals are
`security_arm_of ... = ...Arm` and only their binders mention `published_at`,
so the rule does not reach them and they are fast. Every other `_atE` lemma
still uses `exact: erefl` and every one is fast: 0.002 s and 0.000 s in
`t0_sampled_branch.v`, and 0.002 s, 0.001 s, 0.008 s and 0.148 s in
`t0_sampled_branch_pgl27.v`. The only other `exact: erefl` in
`five_card_rows.v`, at `five_card_row_biased_forms_publishedE`, costs 0.457 s.

**The recorded failure fails for the intended reason and for no other.**
Compiled without `Fail` in `copy/f4_unindexed.v`, there is exactly one error,
at the payload:

```
The term "Order.POrderTheory.ltW (kim_centi_cert_eps_lt R tt)" has type
 "is_true (cert_eps (kim_centi_cert R tt) <= 2 ^- 39)"
while it is expected to have type
 "forall idx : amf_index (ab_f (tableau_at (...))) R, match ab_port (...) R idx with
  | ExactIndependence _ => unit
  | SpectralDecay cert => cert_eps cert <= odflt (cert_eps cert) (five_card_reprice39 R)
  end"
```

The relation is `<=`, which is right, and the index binder is what is missing.
F2's quotation at `:1207-1218` is this message with the `ab_port` argument
elided, marked as elided. The docstring at `:777-780` says the obligation is
one inequality per real field and per index and that a payload with the right
relation and no index binder is rejected, which is what the message shows and
all it says.

**The biased row.** `sqrt 5 / 40 <= 1/25` is false. I compiled the strict
form: `1/25 < cert_eps (kim_biased_cert R tt)` ends in `Qed` in
`copy/f4_arith.v`, so no `conclude` at one twenty-fifth can run from
`kim_biased_cert`, and `kim_biased_cert_exact` stays. Its epsilon is `1 / 50`,
the fourth field of `kim_biased_marginal_bound_exact` at
`instances/kim2025/five_card_mixing.v:540`, and `cert_eps` doubles it by
`manifest/pgg_tableau.v:345-347`, so the obligation is exactly
`1 / 50 + 1 / 50 <= 1 / 25`. `five_card_inv50_split` states
`(1 / 50 : R) + 1 / 50 = 1 / 25` and `ssr_ext.eqW`, at
`infotheo/lib/ssr_ext.v:1224`, is `x = y -> (x <= y)%O`, so the payload has
the type the terminal asks for with nothing to spare. Every comment about
this is truthful except the one named in A1.

**The withdrawal list.** Every listed use exists. Two are missing, see A4.

**F4's sixteen.** The table has sixteen rows and I checked each against the
file it names. Every "what it says" column matches the frozen text, and every
rewritten sentence is true of the code under it. The arithmetic of the
paragraph is consistent: fifteen from the round-3 list, one from the refreshed
header, with the round-3 sixteenth moved to Counts. F4's closing claim that
"no arm of certify takes a bound of that kind" survives a third arm is right,
because spec P2 gives the new arm a variation distance on the pair of reading
and secret and not a conditional mutual information. What the sweep missed is
in A7.

**The split lemma.** `five_card_row_uniform_branch_atE` and
`five_card_row_uniform_branch_ideal_atE` are both single equations closed by
`exact: erefl`, both have header index lines at `t0_sampled_branch.v:34-39`,
and `assumptions_report.v:67` now prints the second one. Its statement is
correct and its docstring is true. Only the orientation is off, see A5.

**A9 of round 3 stays declined, and its second reason is real.**
`t0_sampled_branch.v:102-105` says the coordinate equations close by
`exact: erefl` "following the measurements under the T0 step of STATUS.md,
where done did not return inside the time bound on a goal of this shape whose
right side is a concluded row". The measurement it points at is the table at
`STATUS.md:155-162`, whose slow row is
`published_at pgl27_row_word_branch = published_at pgl27_row_word_branch39`
under `by []`, which did not return in 130 s. The right side of that goal is
`pgl27_row_word_branch39`, the concluded row, and
`t0_sampled_branch_pgl27.v:161-164` states
`pgl27_row_word_branch39_atE` in exactly that orientation. Swapping the sides
would put the concluded row on the left and make the sentence false. The
reason is real and checkable.

**Hygiene.** No barred vocabulary in any `.v` file or in `STATUS.md`, checked
with a word-boundary search for the three banned words and their inflections.
No occurrence of the two-character token for the sum of absolute differences.
No `Admitted`, `Abort`, `Axiom`, `Parameter`, `Hypothesis` or `admit` in any
`.v` file. Exactly three lines exceed 80 bytes, the three known notation lines,
see A10. Every boxed comment line in every `.v` file is exactly 80 bytes; I
checked all of them and found no exception. The new statement comments say
what their object is and where it sits, with no status marker, no "key lemma",
no "used by", and no audit or fix-pass narration. The one place where proof
route is discussed, the `reflexivity` rationale, is in a non-rendered `(* *)`
comment and not in the rendered docstring, which is where the rule puts it.

**STATUS integrity, the rest.** Every back-quoted Rocq identifier in F1 to F5
exists in the frozen probe or in production, except `IdealProximity` and
`certify_idealproximity`, which F4 marks as stage B's. The D2 line list for
`manifest/pgg_tableau.v` is right: `RepricePayload` occurs at production lines
610, 616 and 639, three of them, and `port_reprice` at 74, 622, 632 and 643,
four, and STATUS lists exactly those seven. I spot-checked the other fourteen
D2 rows for that file and the three for `pgg_tableau_syntax.v` against
production by line and found no mismatch. F5's "four more than after fix pass
two" is right: E7 records thirty, the diff adds four `Print Assumptions`
commands, and I counted 34.

## Verdict

**GO** for "stage A is closed and stage B may build on these copies".

No blocking item. The ten files compile from source with no `.vo` the prover
produced, the assumption surface is the three boolp constants plus the one
production axiom the S5 instance already carried, the recorded failure fails
for the reason it is kept for, the deviation to `reflexivity` produces the
same term with the same kernel check and is forced by a measured factor of
2300, and the pass closes the spec's C3, which stage A did not previously
meet. The seven SHOULD items are all in prose and bookkeeping. A1 is the one
I would fix before a landing, because the sentence it names is refuted by a
lemma twenty lines above it in the same file and it would travel into
production unchanged.

## What I did not check

- `instances/psl211/psl211_endpoints.v`, never opened and never compiled.
- The production `.vo` files. I trusted that they are current, as instructed,
  and compiled only my own copies against them.
- The mathematical content of the production theorems the copies import:
  `kim_centi_cut_mixing`, `kim_biased_cut_mixing_exact`,
  `five_card_static_obs_const`, `psl211_alldecks_view_secrecy` and the
  `psl211_spectral_constancy.v` results cited in the refreshed PSL header. I
  checked how the copies use them, not that they are true.
- The refreshed PSL header's long "Not claimed" paragraph, beyond confirming
  that every Rocq name in it exists and that the paragraph is production's own
  text, unmodified by stage A.
- The Kim landing probe and the PSL landing probe as artifacts. I searched
  them for the four withdrawal names and read nothing else in them.
- Whether stage B's `IdealProximity` will in fact need a third witness record,
  a third port constructor and a third typed builder. A7 rests on spec P2 at
  `notes/20260919-tableau-three-extensions-probe-design.md:181` reading that
  way, not on compiled stage-B code.
- The three earlier audit rounds' own findings, except A5, A8, A9 and A12 of
  round 3 and N1 to N7, which F3 answers and which I checked.
