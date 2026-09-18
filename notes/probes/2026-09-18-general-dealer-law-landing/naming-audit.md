# Naming and style audit of the general dealer law landing

Date: 2026-09-18

Independent read-only audit. Nothing was compiled, no Rocq process was started,
no file was edited. The evidence below is file reads and Python `\b` word scans
over the working tree and over the installed `infotheo` and `mathcomp` under
`/Users/cheng-huiweng/Projects/coq/_opam/lib/coq/user-contrib`. `grep -E` word
boundaries were not used, per the standing note that they match nothing on this
machine.

Scope: ledger rows L8, L9, L11 and L12 of
`notes/20260918-general-dealer-law-landing-design.md`, the five `.v` files and
`STATUS.md` of `notes/probes/2026-09-18-general-dealer-law-landing/`, and the
production originals they land into.

Throughout, LAND abbreviates
`notes/probes/2026-09-18-general-dealer-law-landing/` and FEAS abbreviates
`notes/probes/2026-09-17-general-dealer-law/`.

The pending decision taken but not executed, that the four `Fail` commands of
`dealer_privacy.v` move to `landing_fidelity.v` while the instance mutations
stay, is assumed throughout and is audited once, at S9.

---

## Findings table

| id | severity | file:line | rule | evidence | pasteable alternative |
|---|---|---|---|---|---|
| B1 | BLOCKING | `LAND/psl211_models_landing.v:1094-1095` | no comment claims the uniform PSL(2,11) dealer law is necessary (spec Decision 8, Soundness invariant 4) | the comment ends "and the uniform deal law is **the law** that meets it". The definite article asserts uniqueness. Nothing in the file proves that any other kernel fails the mixed-law condition. The refutation that is proved, `psl211_fixed_deal_view_dep:1128`, is at one point mass, which shows one law fails, not that only one succeeds | `    dealer_shuffle_view_indep is available to this instance, and the uniform`<br>`    deal law meets it. *)` |
| B2 | BLOCKING | `LAND/psl211_models_landing.v:975-976` | a statement comment states which law is averaged over what | "The **per-deal** symmetry that the all-decks counting argument uses". The symmetry that argument uses is `psl211_alldecks_per_cut_count`, `instances/psl211/psl211_alldecks.v:1334`, which fixes a cut and counts deals, and whose own comment at `:1331` calls it "the per-cut form". Under this file's `per-` convention, `per_cut` at `psl211_alldecks.v:79` and "per-deck" at `LAND/dealer_privacy.v:131`, "per-X" means "at a fixed X", so "per-deal symmetry" names the symmetry the annotated lemma refutes. The same block writes the thought correctly at `:1013` | `    chiralities have different numbers of cuts producing one reading.  The`<br>`    per-cut symmetry that the all-decks counting argument uses is therefore` |
| S1 | SHOULD-FIX | `LAND/pgl27_profile_privacy_landing.v:329,337,340,346,352,376,385,394,404,415,464,479,511,527,554,582,589,595,604,614,624` | a landed comment matches the style of the file it lands in | the block writes all 21 statement comments as `(** name — ...`. `instances/pgl27/pgl27_profile_privacy.v` writes all 16 of its own as `(** name == ...`, and has zero em-dash comments. The other two target files use em-dash and match | replace the em-dash with ` == ` on those 21 lines, for example `(** pgl27_dealer_delta == the deterministic dealer of the exact PGL(2,7) row:` |
| S2 | SHOULD-FIX | `LAND/dealer_privacy.v:245,247,271,272` | one word per concept, file-wide | `fdistmap_prod_sectionE` moves from the PSL(2,11) probe file `FEAS/psl211_alldecks_bridge.v` into the generic `reconstruct/dealer_privacy.v` and brings the PSL word "cut" with it, 4 times, plus "deals" once. The new file's own words are "shuffle", 14 uses, and "deck", 19. Nothing generic is named "cut" anywhere in `reconstruct/` | `:245` `    section of positive mass.  It is the section form of fdistmap_prod_const,`<br>`:247` `    per-section count up to the law of the whole sample. *)`<br>`:271-272` `(* a section of zero mass contributes zero to both sums, so the premise is`<br>`   needed only where the second law is supported *)` |
| S3 | SHOULD-FIX | `LAND/psl211_models_landing.v:769,781,790,861,866,868,947,1116` | one word per concept, judged against the target file | the block says "class" or "classes" 8 times for the chirality bit. `instances/psl211/psl211_models.v` says "chirality" 12 times and "class" once, at `:142`. Round 2 C002 downgraded this to an implementation-plan item because the production file `psl211_alldecks.v` mixes the two. This is that implementation, and the file it lands in does not mix | `:769` `    zero of the chirality's table, with both labellings the identity. *)`<br>`:781` `(** psl211_perdeck_seq b — the deck psl211_perdeck_deal names at chirality b,`<br>`:790` `(** psl211_perdeck_row_size — block zero of either chirality's table has six`<br>`:861` `    of chirality b to psl211_perdeck_view. *)`<br>`:866` `(** psl211_perdeck_raw_countE — that count is zero at one chirality and one at`<br>`:868` `    deck description the two chiralities do not have equally many cuts`<br>`:947` `    chirality b at psl211_perdeck_deal to psl211_perdeck_view. *)`<br>`:1116` `    psl211_alldecks_seq reads the chirality table at the chirality: one deck` |
| S4 | SHOULD-FIX | `LAND/psl211_models_landing.v:827,860,868,892,946,975,998,1122,1175,1176` | one word per concept, judged against the target file | the block says "shuffle" or "shuffles" for a group **element** 10 times. `psl211_models.v` says "cut" or "cuts" 20 times and uses "shuffle" only for the group, `:58` and `:187`. Round 3 recorded this as unfixed in `FEAS/psl211_per_deck_law_counter.v` and it lands unchanged. The six uses at `:550,582,766,874,1003,1131` say "shuffle group" and are correct | `:827` `    deck sq under the cut whose table is t, written on raw data. *)`<br>`:860` `    (** psl211_perdeck_raw_count b — how many of the 660 cuts carry the deck`<br>`:892` `(** psl211_perdeck_ptbl_nth — a cut's table reads off its images. *)`<br>`:946` `(** psl211_perdeck_fiber b — the cuts of the group carrying the deck at`<br>`:998` `    count over the 660 tabulated cuts. *)`<br>`:1122` `    fixed deck description, a uniform cut. *)`<br>`:1175-1176` `   zero, off the group the cut factor is zero, and on both the sample`<br>`   would put its cut in the empty true fiber *)` |
| S5 | SHOULD-FIX | `LAND/psl211_models_landing.v:546,567,576,672,1074,1112,1116,1122` vs `:868,974` | one word per concept, judged against the target file | the same object, `psl211_deal`, is "deal description" 6 times and "deck description" twice inside the block. `psl211_models.v` says "deck description" 8 times and never "deal description". Round 3 recorded the split as a NOTE in the probe, where "deck description" was the odd one out. The move inverts it: in the target file "deck description" is the established word | use "deck description" at `:546,567,576,672,1074,1112,1116,1122`, for example `:546` `(** dealT — a deck description: a chirality-free block index together with` |
| S6 | SHOULD-FIX | `LAND/pgl27_profile_privacy_landing.v:421-422` | proof and apparatus rationale belongs in `(* *)`, not in a statement comment | "Validity is the last premise so that dropping it leaves an arrow rather than shifting an argument" states an argument-order choice made for the mutation at `:567`. Round 3 already asked for this move, `FEAS/naming-audit-round3.md:291-294`, and the landing did not apply it | delete `:421-422` from the statement comment, ending it at "dealer model.", and add above the `Fail` at `:562`: `(* the premises are declared coalition size first and validity last, so that`<br>`   dropping validity leaves an arrow rather than shifting an argument *)` |
| S7 | SHOULD-FIX | header tables of the three edited files | L11: every landed public declaration listed under Definitions or Key results | 30 of the 82 landed declarations are absent. The repository's tables are selective, 22 to 73 per cent absent, so the row as written is stricter than the tree. But the eight below are the named interface the spec's own Roles paragraph, `:96-101`, calls "the two reader equations of each instance", plus the lemma the unsat comment leans on | add to `pgl27_profile_privacy.v` Key results:<br>`(*   pgl27_dealer_viewE == the model's view along the embedding is the exact  *)`<br>`(*     row's view                                                             *)`<br>`(*   pgl27_dealer_secretE == and its secret is the row's orbit secret         *)`<br>`(*   pgl27_alldecks_dealerPE == the all-decks row's law is the model's law    *)`<br>`(*   pgl27_alldecks_dealer_viewE == and its view is the all-decks view        *)`<br>`(*   pgl27_alldecks_dealer_secretE == and its secret the all-decks secret     *)`<br>add to `psl211_models.v` Key results:<br>`(*   psl211_dealer_viewE == the model's reading along the reassociation is    *)`<br>`(*                              the instance's reading                        *)`<br>`(*   psl211_dealer_secretE == and its secret the instance's chirality         *)`<br>`(*   psl211_dealer_valid_forced == the all-decks dealer forces every validity *)`<br>`(*                              predicate to accept psl211_perdeck_deal       *)` |
| S8 | SHOULD-FIX | `LAND/psl211_models_landing.v:1-80` | the header prose accounts for the file's content | the psl211 header gains 35 lines, every one of them a table row, and no prose. The file grows by 663 lines, 55 per cent of its final length, and gains two refutations. `pgl27_profile_privacy_landing.v:30-36` shows the intended shape, a "The dealer route." paragraph | insert after `psl211_models.v:42`:<br>`(* The dealer route. The all-decks independence is obtained a second way,    *)`<br>`(* from the dealer model of reconstruct/dealer_privacy.v, by placing the     *)`<br>`(* chirality, the deck description and the cut in its sample space. The      *)`<br>`(* route is the mixed-law condition, whose premise the per-cut deal count of *)`<br>`(* psl211_alldecks.v discharges. Two refutations follow it: the per-deck     *)`<br>`(* condition has no solution under this dealer, and under a dealer laying    *)`<br>`(* one fixed deck description the reading of three seats is not independent  *)`<br>`(* of the chirality. Both restate or bound an existing result and replace    *)`<br>`(* no proof.                                                                 *)`<br>`(*                                                                            *)` |
| S9 | SHOULD-FIX | `LAND/dealer_privacy.v:176-184, 291-297` | the pending decision, and no meta in a statement comment | the decision moves the four `Fail` commands. The two positive-control `Definition`s are not `Fail` commands and would stay. Both then carry a statement comment reading "the positive control for **the mutation below**", with no mutation below, both are meta rather than mathematical content, and both are absent from the header table, which already counts only eight declarations | move `dealer_shuffle_view_indep_with_common_law` (`:176-184`), `fdistmap_prod_sectionE_with_sections` (`:291-297`) and the four sections `dealer_kernel_mutations`, `carrier_transport_mutation`, `product_section_mutation` to `landing_fidelity.v` together with the `Fail` commands. `reconstruct/dealer_privacy.v` then holds exactly the three sections and eight declarations its header already lists |
| S10 | SHOULD-FIX | `LAND/psl211_models_landing.v:876` | a name reads as a member of the family it joins | `psl211_entry_perm_enum` states a fact about the closure table and joins the `psl211_entry_perm_*` family, whose other members `psl211_entry_perm_mem:625`, `psl211_entry_perm_inj:673`, `psl211_ptbl_entry:632` and `psl211_size_keys:648` all live in `instances/psl211/psl211_closure.v`. Landing it in `psl211_models.v` splits the family across two files. Editing `psl211_closure.v` is outside the spec's file plan, so the rename is the cheap repair | `Lemma psl211_perdeck_entry_perm_enum :` and its two use sites at `:924` and `:876`'s comment, keeping the block's own `psl211_perdeck_*` family intact |
| S11 | SHOULD-FIX | spec `:152` (row L1) | the spec does not contradict the probe | L1 says "`Print Assumptions` on all **eight** declarations" and "the **two** kernel mutations and the transport mutation", three. `LAND/STATUS.md:63` says ten declarations and the mutation table at `:262-267` lists four. The spec's numbers are the post-move numbers, which is evidence the decision at S9 is the intended end state | after the move, restate L1 as: `The candidate file compiles single-file with the repository header regime. `Print Assumptions` on all eight declarations reports the three `boolp` axioms. Its four mutations and their positive controls live in the probe's `landing_fidelity.v` and behave as recorded there.` |
| S12 | SHOULD-FIX | spec `:130-131` | the file plan states the permanent name, statement source and home of each landed declaration | rows 1 and 3 name their declarations. Rows 4 and 5 do not: "PGL(2,7) dealer data, reader equations, per-deck law, ... their mutations" covers 23 declarations and "PSL(2,11) dealer data, reader equations, mixed law, ... the two refutations" covers 43. A plan cannot be written verbatim from either | replace the two prose groupings with the declaration lists this audit prints under "Landed names", or add one sentence to each row: `The declarations and their order are the landing copy verbatim, LAND/pgl27_profile_privacy_landing.v:321-670` and `LAND/psl211_models_landing.v:541-1204` |
| S13 | SHOULD-FIX | spec `:131` | the file plan is complete | the row for `psl211_models.v` does not mention the two imports, the `Import Num.Theory` and the `%N` pattern fix that the probe found necessary. They are recorded only in the findings prose at `:241-246` and in `STATUS.md:175-198` | append to the row: `The file also gains imports of psl211_blocks and psl211_closure, an Import Num.Theory, and a %N annotation on the two rewrite patterns of psl211_perdeck_seqE.` |
| N1 | NOTE | `LAND/dealer_privacy.v:66-68` | file-level scope order | the file opens `ring_scope`, `proba_scope`, `fdist_scope`, so `fdist_scope` is innermost. `reconstruct/design_privacy.v:41-43`, `instances/psl211/psl211_models.v:106-108` and `instances/pgl27/pgl27_profile_privacy.v:68,71-72` all put `ring_scope` innermost. Nothing breaks today, the file compiles, but the new file resolves ambiguous notations in an order no other file of the development uses | `Local Open Scope fdist_scope.`<br>`Local Open Scope proba_scope.`<br>`Local Open Scope ring_scope.` |
| N2 | NOTE | `LAND/dealer_privacy.v:64` | import line shape | `Import GRing.Theory Num.Theory.` on one line. The two named siblings use two lines, `design_privacy.v:39-40` and `transitivity_privacy.v:72-73`. Precedent for the combined form exists in `reconstruct/coalition_view_transport.v:31` and in `pgl27_profile_privacy.v:66` | `Import GRing.Theory.`<br>`Import Num.Theory.` |
| N3 | NOTE | `LAND/dealer_privacy.v:28-50` | header block shape | the header carries both a `Section N --` table and `Definitions:` and `Key results:` blocks, repeating all eight names. `design_privacy.v` and `transitivity_privacy.v` carry only the first, `reconstruct/pgl_bound.v` only the second. The combined form is a superset of both precedents and is what the two instance targets use. No action asked |
| N4 | NOTE | `LAND/psl211_models_landing.v`, 18 identifiers | compound spelling | `psl211_perdeck_*` runs the compound together. The one sibling compound in the tree is `psl211_alldecks_per_cut_count`, `instances/psl211/psl211_alldecks.v:1334`, with an underscore, and the probe's own file names are `psl211_per_deck_counter.v` and `psl211_per_deck_law_counter.v`. Round 2 B010 settled the identifier spelling and left this as a NOTE. The move puts the two spellings in one file, `:685` calls `psl211_alldecks_per_cut_count` and `:768` declares `psl211_perdeck_deal`, which is new, but the question was adjudicated and is not reopened here |
| N5 | NOTE | `LAND/STATUS.md:70` | the reported scope of the L8 scan | the 75 names scanned exclude the five `Local Notation`s and the seven `Fail` names, which is how 87 landed declarations become 75. Re-running the scan over all 87 finds one name in the tree, `viewT`, at `protocol/pgg_functionality.v:202`, `security/pgg_leakage_witness.v:42`, `security/pgg_trace_secrecy.v:29,41` and `reconstruct/transitivity_privacy.v` section `monotone_ramp`. Every one is a bound variable, not a global constant, and `Local Notation` is not exported, so there is no collision and the reuse is consistent. L8 stands. The row would be more useful stating what it counted |
| N6 | NOTE | `LAND/STATUS.md:304` | an accurate claim about the tree | "Every section in `reconstruct/` is lowercase" is not exact: `reconstruct/s5_nogo.v` declares `Section Kernel` and `Section SecretSixDim`. Fourteen of the sixteen files follow the lowercase rule, `dealer_privacy.v` follows it, and the conclusion is unaffected |
| N7 | NOTE | `LAND/STATUS.md:16` | the banned-vocabulary scan, metaphor sense | "No cap was ever reached", of the 300 s and 8000 MB wrapper limits. The ban is on that word as a noun for a mathematical bound, which this is not, and the file is a probe record | `No limit was ever reached` |
| N8 | NOTE | `LAND/pgl27_profile_privacy_landing.v:451` | lone `by [].` | 24 lone `by [].` lines exist in the production tree, four of them in `reconstruct/transitivity_privacy.v` at `:701,822,831,876`. Precedent, no action |
| N9 | NOTE | `LAND/pgl27_profile_privacy_landing.v:545` | section naming | `Section pgl27_dealer_view_law_mutation` is the first section in the tree named after a verification technique rather than a mathematical topic. The other two new sections, `pgl27_dealer` and `pgl27_alldecks_dealer`, match the `<instance>_<topic>` pattern of `pgl27_leakage_transport.v` and `psl211_alldecks.v`. Section names are discharged and invisible outside the file. The user's decision keeps the instance mutations and they need a home |
| N10 | NOTE | `LAND/landing_fidelity.v:133,138` | development words in identifiers | `fiberE_landing_at_production_type` and `fiberE_production_at_landing_type` contain a development word. This is a probe file, which the spec allows to be named after the verification work, and the two names state exactly which constant is ascribed which type |
| N11 | NOTE | `LAND/psl211_models_landing.v:760` | a dated measurement in a permanent file | "measured 2026-09-18, `Eval vm_compute in val (inord 0)` returns a stuck ..." sits in a non-rendered `(* *)` comment, which is the carrier the project rule prescribes for this content. The permanent tree does the same at `protocol/pgg_instance.v:32`, `instances/psl211/psl211_closure.v:14` and `instances/psl211/psl211_endpoints.v:6`, and `psl211_models.v:374-376` already carries one. Round 2 D002 does not survive the move. No action |

---

## N1. File conventions of the new `reconstruct/dealer_privacy.v`

Measured against `reconstruct/transitivity_privacy.v` and
`reconstruct/design_privacy.v`.

**Passes.** The two-line infotheo copyright and licence block is byte-identical
to both siblings, `:1-2`. The header opens with a `PGG:` title line and a prose
paragraph, then a `Section N --` table with `==` entries, which is
`design_privacy.v:4-24` exactly. `Set Implicit Arguments. Unset Strict Implicit.
Import Prenex Implicits.` appear in that order at `:61-63`, matching both
siblings. Section names are lowercase, `dealer_kernel`, `carrier_transport`,
`product_sections`, which fourteen of the sixteen `reconstruct/` files do. The
statement comments are `(** name — ...`, which `design_privacy.v` uses in 10 of
its 12 comment blocks. `transitivity_privacy.v` uses no name prefix at all in
any of its 32 blocks, so `design_privacy.v` is the governing precedent and the
new file follows it. One blank line separates declarations, as in both
siblings. Every declaration carries a statement comment.

**Divergences.** Three, all cosmetic or near-cosmetic, all in the findings
table: the scope order at N1, the combined import line at N2, the hybrid header
block at N3.

**The header already describes the post-move file.** The `Section N --` table
numbers three sections and the `Definitions:` and `Key results:` blocks name
eight declarations. The file as it stands has six sections and ten
declarations. The gap is exactly the mutation apparatus, which confirms that
the pending decision is the intended end state and gives S9 its shape: moving
only the four `Fail` commands leaves two orphaned positive controls whose
comments name a mutation that is no longer there.

---

## N2. The three edited files

### `reconstruct/design_privacy.v`

Clean. Two declarations added, `uniform_fdistmap_pointE` into the existing
`Section fibers` and `uniform_fdistmap_fiberTE` into a new `Section
full_set_fibers`. Both use the file's em-dash comment style. Both appear in the
header's `Section N --` table, which is renumbered 1 to 4 correctly. The header
prose at `:6-15` is untouched and remains true: nothing added concerns
t-transitivity or the counting premise it describes. The file's header table is
the one table in the repository that is already complete, 0 of 10 declarations
absent, and it stays complete, 0 of 12.

### `instances/pgl27/pgl27_profile_privacy.v`

**Three new sections after `End pgl27_profile_privacy.`** The existing section
binds `ord8_1` and `ord8_2` and opens two scopes inside itself, so appending
rather than extending leaves every existing line untouched. The names
`pgl27_dealer` and `pgl27_alldecks_dealer` follow the `<instance>_<topic>`
pattern of `instances/pgl27/pgl27_leakage_transport.v`, which has
`pgl27_leakage_positions` beside the file-named `pgl27_leakage_transport`.
Acceptable. `pgl27_dealer_view_law_mutation` is at N9.

**Comment style does not match the file.** S1. The file is uniform, 16 of 16
`==`, 0 em-dash. The block is uniform the other way, 21 of 21 em-dash. This is
the single most visible inconsistency the landing introduces, and it is
mechanical.

**Local Notations carry no comment**, `:325-327` and `:578-580`. The file's own
`ord8_1` and `ord8_2` at `:75-76` carry none either, so the block matches its
file. `psl211_models_landing.v` does comment its notations, and `psl211_models.v`
comments `seatT`, `cardT`, `mpP` and `eP`. Each block matches its own file,
which is the right answer.

**Header.** The added `The dealer route.` paragraph at `:30-36` is accurate: it
says the two theorems are obtained "a third way", names the two conditions, says
which row takes which, and ends "Both restate an existing theorem and replace no
proof." Nothing in the existing header prose is contradicted. Nine declarations
are absent from the table, five of which S7 asks for.

### `instances/psl211/psl211_models.v`

**One section in a file that has none.** `Section psl211_dealer` binds `Variable
R : realType`, and the discharge produces exactly the leading `(R : realType)`
binder that every lemma of the file already writes by hand. The eight
declarations after the section bind `R` per lemma in the file's own style. So
the discharged signatures are uniform across the file even though the source
shows two shapes. Acceptable, and preferable to the alternative, which would be
to rewrite every statement in the block. One consequence a reader should know:
`psl211_dealer_view` does not mention `R` and so takes no `R` argument after the
`End`, while `psl211_dealer_nu` does. The use sites at `:1102` and `:1126`
already assume this.

**Comment style matches**, em-dash on both sides, 35 in the production file and
45 in the block, zero `==` in either.

**Header prose is not updated at all.** S8. Every one of the 35 added header
lines is a table row. No existing header sentence is contradicted: the sentence
at `:14-17` about the fixed-dealer colour result of `psl211_secrecy.v` concerns
a different observer and is unaffected by `psl211_fixed_deal_view_dep`. But a
reader of the header learns nothing about 55 per cent of the file.

**Twenty-one declarations absent from the table.** S7 asks for three of them.
The raw-count chain may stay out: `instances/psl211/psl211_alldecks.v` keeps 76
of 103 declarations out of its own table, so selective tables are the
repository's practice. The number to watch is that `psl211_models.v` currently
runs at 22 per cent absent and would land at 38 per cent.

---

## N3. Statement comments

**Present everywhere.** All 82 landed `Definition`, `Lemma`, `Theorem` and
`Corollary` declarations carry a preceding `(** ... *)` block. The only
uncommented declarations in any LAND file are `Local Notation`s, and each block
follows its own target file's practice, as recorded above.

**No status, progress, effort or "key lemma" material.** A scan of every `(**`
block in the five files for status markers, effort estimates, measurements and
proof strategy returns two hits, both discussed: S6, apparatus rationale in a
pgl27 statement comment, and S9, "the positive control for the mutation below"
in two `dealer_privacy.v` comments that the pending decision should remove from
that file. Tactic rationale is otherwise correctly carried in `(* *)` blocks
inside proofs, at `:740-742`, `:806-809`, `:931-932`, `:936-937`, `:983-985`,
`:1024-1026`, `:1067`, `:1150-1153`, `:1165-1166`, `:1174-1180` of
`psl211_models_landing.v` and at `:271-272` of `dealer_privacy.v`. That is the
prescribed carrier.

**Claim scope.** Four prohibitions were checked against every comment in the
five files.

1. *Privacy for an arbitrary dealer law.* Not claimed. `dealer_privacy.v:8-10`
   says "gives two **sufficient** conditions on the dealer law", and both lemma
   comments at `:112-117` and `:131-137` state their premises. Clean.
2. *Necessity of the uniform PSL(2,11) dealer law.* Claimed once. B1. This
   sentence was not adjudicated by round 3: that report quotes, for the same
   lemma, the wording "the average over deal descriptions that
   `dealer_shuffle_view_indep` asks for is the only route that remains", and
   that string occurs in no `.v` file of the feasibility probe. The sentence
   actually in the file is the one B1 quotes.
3. *A hidden uniform deal leaks.* Not claimed, and explicitly disclaimed at
   `psl211_models_landing.v:1135-1137`: "What is NOT shown here is that a hidden
   uniform deal leaks: the deal is public in this refutation, being a point
   mass." Round 3 called this comment the standard for the development and this
   audit agrees. It stands unchanged.
4. *Necessity of `uniq`.* Not claimed. `pgl27_alldecks_dealer_view_law` at
   `:415-422` states validity as a premise and never as a requirement, and the
   mutation note at `:562-566` makes a statement about the term's type, not
   about the mathematics.

**Averaging direction.** B2 is the one comment that states it wrongly. Every
other comment in the block is right: `:673` "the per-cut deal count of
psl211_alldecks", `:689-690` "The per-cut equality is lifted to the pair of deal
and cut", `:1013-1015` "The averaged symmetry that psl211_alldecks establishes
is therefore genuinely a statement about the average over deals". The generic
side is right too: `dealer_privacy.v:14-21` distinguishes the mixed-law and
per-deck conditions and says which implies which, and `:112-117` says the
mixed-law premise "is the point at which an instance's counting argument enters
the general model", which is exactly where `psl211_dealer_sectionE` enters.

**Information-theoretic and exact.** Stated where it matters and nowhere
overstated: `dealer_privacy.v:114-115`, `psl211_models_landing.v:706-707` "it is
exact: no approximation and no computational premise". No comment mixes an
assumption-conditional term with an unconditional one, because no landed
statement carries an assumption.

**One word per concept.** Three drifts, all in the psl211 block and all judged
against the target file, not against the probe: S3 chirality against class, S4
cut against shuffle, S5 deck description against deal description. One drift in
the new generic file: S2. The pgl27 block is clean: "view" 13, "reading" 0,
"shuffle" 7, "cut" 0, which matches `pgl27_secrecy.v` and `pgl27_orbit.v`. The
generic file is clean on view against observation: `_view` identifiers with
"observation" prose, which `reconstruct/design_privacy.v:6-7` and `:85` do too.

---

## N4. Names in their permanent context

**Collisions: none.** The whole-word scan was re-run over all 87 landed
declarations, including the five `Local Notation`s and the seven `Fail` names
that `STATUS.md`'s 75 excluded, against 132 `.v` files in `lib protocol groups
security smc reconstruct instances manifest` and 388 installed `infotheo` and
`mathcomp` files. One name occurs: `viewT`, five times, always as a bound
variable. Detail at N5 in the table. Against the identifiers already in each
target file: none of the 87 occurs in `design_privacy.v`, in
`pgl27_profile_privacy.v` or in `psl211_models.v`. Against the nine importers of
`psl211_models.v` and the eleven of `design_privacy.v` listed in
`LAND/STATUS.md:82-112`: `Local Notation` is not exported, so the five notations
cannot reach them, and none of the 82 declarations occurs in any importer. L8
holds.

**Do the names read wrongly in their permanent homes?** Four questions, judged.

*`psl211_dealer_*` beside the file's `psl211_alldecks_*` family.* Reads
correctly. The two families name different things. `psl211_alldecks_*` is the
instance's own model, `psl211_dealer_*` is the same data placed in the general
model's sample space, and the bridge between them is named
`psl211_dealer_assoc`, `psl211_dealerPE`, `psl211_dealer_viewE`,
`psl211_dealer_secretE`. The theorem that joins the two families is
`psl211_alldecks_view_indep_via_dealer`, which carries both stems in the order
the statement reads, and the `_via_` component is the repository's convention,
`pgl27_view_indep_via_profile` at `instances/pgl27/pgl27_profile_privacy.v:82`.
No objection.

*`psl211_perdeck_*` against the repository's spelling of "per deck".* The
repository writes the compound with an underscore, `psl211_alldecks_per_cut_count`,
and hyphenates it in prose, `psl211_alldecks.v:1331`. The landing runs it
together in 18 identifiers. Round 2 B010 settled the identifier spelling and
left a NOTE, so this is not reopened. What the move adds is that both spellings
now sit in one file, three lines apart at `:685` and `:768`. Recorded at N4 in
the table, not raised as a finding.

*`pgl27_dealer_*` inside a file whose other names are `constant_deck_*` and
`profile_*`.* Reads correctly, and better than the alternatives. The file
already holds three name families, one per route: `profile_*` for the
record-level route, `constant_deck_*` for the counterexample, and now
`pgl27_dealer_*` for the dealer route. Each family stem names the object the
route runs on, which is what a reader needs to tell three proofs of the same
theorem apart. The two headline results carry the file's `_via_` convention.
No objection.

*`psl211_entry_perm_enum`.* This one does read wrongly. S10.

---

## N5. The banned-vocabulary scan and mechanical checks

All scans run in Python with `\b`, case-insensitive, over the five `.v` files
and `STATUS.md`.

| check | result |
|---|---|
| the banned-vocabulary scan, whole words, identifiers and comments | zero hits in all five `.v` files and in `STATUS.md` |
| metaphor words for mathematical results: escape, beats, smash, dodge | zero hits |
| that word for a bound, as a noun | one hit, `STATUS.md:16`, of a wrapper limit and not of a bound. N7 |
| development words in identifiers: generic, bridge, square, counter, probe, landing | two hits, both in `landing_fidelity.v`, which is a probe file. N10. Zero in the four candidate permanent texts |
| lines over 80 bytes | zero, in all five `.v` files |
| lone `by [].` | one, `pgl27_profile_privacy_landing.v:451`, with 24 in the production tree. N8 |
| `Print Assumptions`, `Time`, `Timeout`, `Show`, `Admitted`, `Abort`, `Axiom`, `Parameter`, `Conjecture` in a candidate permanent file | zero, in all four. `landing_fidelity.v` carries its 97 `Print Assumptions` commands, which is where the spec puts them |

---

## N6. L9 by independent reading

Fifteen landed declarations were compared against their feasibility-probe
counterparts, statement text and statement comment, after whitespace
normalisation. The ten the row asks for are included, with
`uniform_fdistmap_pointE` among them.

| declaration | landing | feasibility probe | statement | comment |
|---|---|---|---|---|
| `uniform_fdistmap_pointE` | `design_privacy_landing.v:57` | `psl211_per_deck_law_counter.v:35` | differs, binders only | identical |
| `uniform_fdistmap_fiberTE` | `design_privacy_landing.v:89` | `psl211_alldecks_bridge.v:73` | identical | identical |
| `dealer_shuffleP` | `dealer_privacy.v:84` | `dealer_kernel_probe.v:25` | identical | identical |
| `dealer_shuffle_view_indep` | `dealer_privacy.v:118` | `dealer_kernel_probe.v:60` | identical | identical |
| `dealer_shuffle_view_indep_of_deck` | `dealer_privacy.v:138` | `dealer_kernel_probe.v:79` | identical | identical |
| `inde_RV_fdistmap` | `dealer_privacy.v:214` | `carrier_transport_probe.v:25` | identical | identical |
| `fdistmap_prod_sectionE` | `dealer_privacy.v:248` | `psl211_alldecks_bridge.v:35` | identical | identical |
| `pgl27_alldecks_dealer_view_law` | `pgl27_..._landing.v:423` | `pgl27_deterministic_bridge.v:118` | identical | identical |
| `pgl27_view_indep_via_dealer` | `pgl27_..._landing.v:517` | `pgl27_deterministic_bridge.v:214` | identical | identical |
| `psl211_dealer_mixed_lawE` | `psl211_..._landing.v:691` | `psl211_alldecks_bridge.v:251` | identical | identical |
| `psl211_alldecks_view_indep_via_dealer` | `psl211_..._landing.v:732` | `psl211_alldecks_bridge.v:288` | identical | identical |
| `psl211_perdeck_raw_countE` | `psl211_..._landing.v:870` | `psl211_per_deck_counter.v:126` | identical | identical |
| `psl211_perdeck_fiber_card_neq` | `psl211_..._landing.v:980` | `psl211_per_deck_counter.v:234` | identical | identical |
| `psl211_dealer_view_indep_of_deck_unsat` | `psl211_..._landing.v:1096` | `psl211_per_deck_law_counter.v:148` | identical | identical |
| `psl211_fixed_deal_view_dep` | `psl211_..._landing.v:1138` | `psl211_per_deck_law_counter.v:180` | identical | identical |

The single difference is the one `STATUS.md:137-167` reports:

```coq
(* psl211_per_deck_law_counter.v:35 *)
Lemma uniform_fdistmap_pointE (R : realType) (X T : finType)
    (A : {set X}) (HA : (0 < #|A|)%N) (f : X -> T) (v : T) :

(* design_privacy_landing.v:57, inside Section fibers *)
Lemma uniform_fdistmap_pointE (f : X -> T) (v : T) :
```

Five binders are supplied by `Section fibers`, `design_privacy.v:46-50`. The
body of the statement, the conclusion and the proof script are
character-identical. No binder was renamed and no notation respelled in any of
the fifteen. L9 holds as reported.

One consequence of the comments being identical: B1, S4, S5 and S6 are
unfixed items the landing inherited rather than introduced, and two of them, S4
and S5, were recorded as minor in the probe by round 3 precisely because the
probe files were probe files. The move into `psl211_models.v` is what changes
their answer.

---

## N7. The spec

**The file plan.** Rows 1 and 3 state the permanent name, the statement source
and the home precisely enough to write a plan verbatim. Rows 4 and 5 do not.
S12. Row 5 is also incomplete on the imports and the scope fix. S13.

**`_CoqProject`, L12: stated correctly.** Verified against the file.
`reconstruct/transitivity_privacy.v` is at line 171.
`instances/pgl27/pgl27_profile_privacy.v` is at line 180 and
`instances/psl211/psl211_models.v` at line 212, so both importers follow.
Inserting `reconstruct/dealer_privacy.v` at line 172 places it after
`transitivity_privacy.v` and before both importers, with eight files in
between, `coalition_view_transport`, `design_privacy`, `pgl27_group`,
`pgl27_orbit`, `pgl27_scheme`, `pgl27_profile`, `pgl27_run` and `pgl27_secrecy`,
none of which imports it and none of which it imports. The count of eight in
`LAND/STATUS.md:74` is exact.

**Contradictions between the spec and the probe.** One, S11: L1 counts eight
declarations and three mutations against the probe's ten and four. The other
four items `LAND/STATUS.md:275-299` lists as corrections the spec needs are
already folded into the spec: the L5 timing expectation at spec `:156` and
`:253-255`, the `Print Assumptions` placement at `:186-188` and `:256`, the home
of `fdistmap_prod_sectionE` at `:128` and `:258-259`, and the restatement of L10
at `:161`. Row L11 at spec `:162` is stricter than the repository's own practice
and is the source of S7.

---

## What blocks the landing

1. **B1**, `LAND/psl211_models_landing.v:1094-1095`. A statement comment claims
   the uniform PSL(2,11) dealer law is the law meeting the mixed-law condition.
   The spec forbids it at Decision 8 and Soundness invariant 4, nothing proves
   it, and round 3 did not adjudicate this sentence.
2. **B2**, `LAND/psl211_models_landing.v:975-976`. A statement comment names the
   wrong averaging direction for the symmetry the all-decks argument uses. A
   charitable reading exists, but it contradicts the file's own `per-`
   convention, and the correct phrasing is already in the same block at
   `:1013`.

Both are one-sentence replacements and the replacement text is in the findings
table.

## What does not block the landing

S1 to S13 and N1 to N11. Of these, S1, S3, S4, S5 and S6 are the ones that
should be applied in the same commit as B1 and B2, because they are the same
kind of edit in the same two files and because S4, S5 and S6 are round-3 items
that the landing carried forward unchanged. S7, S8, S11, S12 and S13 are edits
to header blocks and to the spec and can be applied when the plan is written.
S9 is the execution of the decision already taken and should be done as part of
it rather than after. S10 is a rename of one identifier and its two use sites.
N1 to N11 need no action beyond the two one-line repairs offered at N1 and N2,
which are optional.

VERDICT: NO-GO
