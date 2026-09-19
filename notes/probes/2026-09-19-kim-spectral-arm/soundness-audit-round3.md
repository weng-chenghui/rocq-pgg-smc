# Soundness audit, round 3: is STATUS.md's landing account true and complete?

Independent audit, 2026-09-19. Round 1 is `soundness-audit.md` (F1-F9), round 2
is `soundness-audit-round2.md` (G1-G7). No code changed since round 2, so no
Rocq compiler was run in this round and no proof was re-audited. Every claim
below is checked against the source at this revision with Python and `grep`
over the repository. No repository file was edited. This file is the only one
written.

**VERDICT: NO-GO** for "the probe's claims are true as stated, STATUS.md's
landing account is true and complete enough to write a landing plan from, and
the result may be reported to the user".

The mathematics is unchanged and unchallenged. All six round-2 findings are
correctly disposed of and every line number the fix pass added checks out
against the source. What still fails is the completeness test, and in the same
way it failed in round 2: the fix pass searched for the two row names and for
the facade's two typed statuses, and found everything that carries those
names. It did not search for the sentence those names stand for. The manifest
states "the five-card development supplies no ideal distribution equality"
three further times, in three places that carry neither row name, and all
three become false at a landing (H1). One statement about which hypothesis the
mixing field discharges is mathematically wrong and appears twice (H2). The
header index of `five_card_rows.v` states both programs' level and is not in
the list (H3). And the account never says whether the landing keeps the two
`Tableau Sampled` programs or retypes them, which decides whether four lemmas
in that file still compile (H4).

The remedy is again narrow: add four rows to the change list, correct one
clause about the transfer inequality, and state one assumption explicitly. No
proof changes and no re-proving.

---

## 1. Disposition of G1-G6, against the source

| ID | Round-2 severity | Disposition | Evidence checked this round |
|---|---|---|---|
| G1 | BLOCKING | **Applied, and every cited line is right, but the search was too narrow. See H1.** | All three row pins verified verbatim: `manifest/pgg_analysis_manifest.v:1779-1780` `Timeout 60 Check (erefl : apr_transfer five_card_row_biased = StaticExecutedOnly).`, `:1787` `Timeout 60 Check (erefl : apr_completion five_card_row_repeated = Sampled).`, `:1788-1789` `(erefl : apr_transfer five_card_row_repeated = NoModelComparison).`. The three survivors are where STATUS says: `:1777-1778`, `:1781-1782`, `:1790-1791`. Manifest header `:67-72` quoted verbatim. Row 4 cells `:301-302`, `:305`, `:306`, `:308` and survivors `:303`, `:307`, `:310`, `:322-328` all match the file. Row 5 cells `:351-354`, `:355`, `:357`, `:358-360`, `:361`, `:362`, `:374-380` and survivor `:364` all match. Facade section header `:351-358`, docstrings `:361-363` and `:366-367`, definitions `:364` and `:368`, pins `:433-436`, manifest facade pins `:1385-1386` and `:1388-1389` under the comment `:1381-1383`, all verbatim. |
| G2 | BLOCKING | **Applied, correct.** | `_CoqProject` enumerates exactly **194** `.v` files by name with no duplicate. The five `lib/` lines are `:30-34`. `reconstruct/dealer_privacy.v` is `_CoqProject:172`. `Makefile:8` is `rocq makefile -f _CoqProject -o $(ROCQMAKEFILE)`. |
| G3 | SHOULD-FIX | **Applied, correct.** | I rebuilt the reverse closure from `.Makefile.rocq.d` with my own script (join continuations, split on `:`, keep `.vo`, invert, transitive forward closure, exclude self). The manifest's closure is **7** and its members are exactly the seven STATUS lists. All fifteen rows of the S10 table reproduce exactly: 105, 107, 102, 41, 39, 24, 20, 20, 10, 9, 0, 7, 8, 16, 20. The three extra rows in the script output (`pgl27_analysis` 8, `pgg_analysis_client` 0, `pgg_tableau` 5) reproduce too. |
| G4 | SHOULD-FIX | **Applied. The counts are right. Two gaps in the option-2 description: H5 and H10.** | See section 3. |
| G5 | NOTE | **Applied, correct.** | `2*math.sqrt(5)*(1/80)**7 = 2.132480599880019e-13`. STATUS's `2.1325e-13`, `about 2.13e-13` and the ratio `8.5299` all reproduce. See section 4. |
| G6 | NOTE | **Applied, correct.** | `kim_spectral_rows_probe.v:291-293` now reads "The reprice obligation is one identity per real field and per index. `five_card_pow2_39_split` is quantified over every real field but not over the family index, so it does not have the shape `conclude` asks for." That is the reason the round-2 audit gave. |
| G7 | NOTE | **Unchanged, as stated.** | F7 and F8 are still recorded as observations with no change. |

One positive confirmation the change list does not need but a landing plan
will want. The `Check` at `manifest/pgg_analysis_manifest.v:1785-1786`,
`Timeout 60 Check (apr_model five_card_row_repeated : AnalysisModelFamily
FiveCardAnalysis.observed).`, **survives** the completion-level move, because
`AnalysisModelSlot observed c` reduces to `AnalysisModelFamily observed` at
both `Sampled` and `AnalysisBridged` (`manifest/pgg_analysis_status.v:119-124`,
the `match c with | Sampled | AnalysisBridged => AnalysisModelFamily observed`
branch). So the manifest holds exactly the three compile breakages STATUS
names and no fourth.

---

## 2. Completeness of the landing change list (S8)

I built my own list first, from whole-tree Python searches over the 195 `.v`
files of the directories `_CoqProject` names, `legacy/` included, for
`five_card_row_repeated`, `five_card_row_biased`, `repeated_family`,
`biased_family`, `kim_centi_family`, `kim_biased_family`,
`exec_transfer_status`, `repeated_transfer_status`, `NoModelComparison`,
`StaticExecutedOnly`, `apr_completion`, `apr_transfer`, `Tableau Sampled`,
`tableau_at`, `Sampled` within four lines of a five-card or Kim mention, and
for the phrasings `nothing to alias`, `no ideal`, `ideal distribution
equality`, `absent premise`, `missing premise`, `none claimed`, `no transfer`,
`NOT AnalysisBridged`, `endpoint marginal only`, plus row-counting patterns.

### 2.1 Items in STATUS.md, confirmed

Every item in S8 is real and every line number is right. Confirmed against the
source, one by one:

- The two manifest row definitions and their docstrings, `:766-768` with
  `:760-765`, and `:776-778` with `:770-775`.
- The three `erefl` row pins and the three that stay.
- The manifest header passage `:67-72`.
- The Row 4 and Row 5 header tables, both the lines named false and the lines
  named true.
- The facade's section header, two docstrings, two definitions and two pins,
  and the two manifest pins on the facade's statuses with their comment.
- `manifest/pgg_analysis_client.v` is safe. Its only mentions of the two rows
  are the bare `Check five_card_row_biased.` and `Check five_card_row_repeated.`
  at `:149-150`, and of the two statuses the bare `Check`s at `:48-49`. Its one
  row-counting header, `:126` "The typed status vocabulary and the nine rows",
  counts rows and not levels, so it stays true.
- "No file anywhere counts or pattern-matches manifest rows by level or
  status": confirmed by my own row-count search over all 195 files.
- "No lemma anywhere states `apr_completion` or `apr_transfer` of either row
  except `five_card_row_biased_levelE`": confirmed. The only other occurrences
  of `apr_completion` at these two rows are the ascription at
  `five_card_rows.v:457` and the recorded `Fail` at `:474`, both already in the
  list, and the manifest's own pins.
- Recorded `Fail`s: the five in the manifest (`:1883-1894`, `:1899`) are about
  the S5 rows and the dependent model slot and are untouched; the three in
  `five_card_rows.v` (`:409`, `:473`, `:571`) and the eight in
  `pgg_analysis_client.v` (`:188-201`) are as STATUS describes, subject to H4.
- The eight-item list for `instances/kim2025/five_card_rows.v`: all eight line
  ranges verified verbatim, including the two ranges round 2 argued about
  (`:383-389` and `:394-400` are what the file has).

### 2.2 Items in STATUS.md that are wrong

**H2. BLOCKING. STATUS.md says the mixing field discharges the SECOND
hypothesis of the transfer inequality. It discharges the FIRST.**

Two occurrences.

- `STATUS.md:542`, the Row 4 table row:
  `` | `:306` | `missing premise \| the ideal distribution equality, as in row 3` | the mixing field discharges it on the cut carrier | ``
- `STATUS.md:593-594`, facade item 1:
  "The mixing field is the cut-carrier bound that discharges the second
  hypothesis, and the section then has a theorem to alias."

The lemma has two hypotheses, in this order
(`security/pgg_collusion_bound.v:977-988`):

    Hypothesis PQ_close : var_dist P Q <= delta.      (* first  *)
    Hypothesis ideal_eq : fdistmap fx Q = fdistmap fy Q.  (* second *)

and `spectral_tail` fills them in that order
(`manifest/pgg_tableau.v:566-570`):

    apply: (var_dist_fdistmap_transfer R _ _ (sa_cut_dist sa) (sc_ideal cert) ...).
    - by rewrite -(sc_Hd cert); exact: (sc_close cert).      (* first  <- mixing  *)
    - exact: (@sc_const _ _ _ _ cert C HC x x').             (* second <- constancy *)

So `sc_close`, the mixing field, discharges `PQ_close`, and `sc_const`, the
constancy field, discharges `ideal_eq`, which is the one the manifest and the
facade both call "the ideal distribution equality" and "the second
hypothesis". STATUS's own S8 paragraph at `:429-431` gets the roles right
("the mixing field is the distance on the cut carrier, and the constancy field
is what makes the ideal usable"); only these two lines swap them.

Why it is blocking rather than cosmetic: the manifest cell at `:306` and the
facade header at `:351-358` are both about the *ideal equality*, and a landing
plan written from STATUS would replace them with a sentence naming the wrong
theorem. The item itself stays in the list, only its reason changes.

**Exact correction.** `STATUS.md:542`, right-hand cell: "the constancy field
`five_card_static_obs_const` is that equality; the mixing field supplies the
cut-carrier distance the inequality's first hypothesis asks for".
`STATUS.md:593-594`: "The constancy field is the ideal distribution equality
that discharges the second hypothesis, and the mixing field is the cut-carrier
bound the first asks for, so the section has two theorems to alias."

**H6. NOTE. "the three `prefixE` and two `modelE` lemmas" (`STATUS.md:684`).**
There are **two** `prefixE` lemmas in the file, `five_card_row_repeated_prefixE`
(`:418`) and `five_card_row_biased_prefixE` (`:428`), and the file's own header
index lists two (`:111-112`). Correction: "the two `prefixE` and two `modelE`
lemmas".

**H7. NOTE. Two line ranges in the `five_card_rows.v` list are short at the
head.** Item 2 gives `:29-33` for the sentence "The manifest's two further
five-card rows are written as programs below, and both stop at `Sampled`". The
sentence begins at `:28` ("The manifest's two"). Item 3 gives `:39-42` for the
spectral-arm clause, but the false claim is the whole sentence `:33-42`, "The
biased row stops there although the manifest places it at `AnalysisBridged`,
because ... neither arm of `certify` carries a bound of that kind: ...", of
which `:39-42` is only the subordinate clause about the spectral arm. After a
landing the spectral arm does carry a bound of that kind, so the head of the
sentence is the part that goes false. Correction: `:28-30` and `:33-42`.

**H9. NOTE. Item 2 calls "both stop at `Sampled`" obsolete.** Under the landing
as the remit states it, where the two Kim programs become certified and
published, that sentence is false, not obsolete. Under the reading of H4 below
it is obsolete. Whichever reading S8 adopts, the word should match it.

**H8. NOTE. The family-name grep result at `STATUS.md:626-632` is incomplete.**
It reports the declarations at `five_card_analysis.v:202-222`, the manifest Row
4 and Row 5 tables and row definitions, and one spelled-type `Check` at
`five_card_analysis.v:402`. The same search also returns
`manifest/pgg_analysis_client.v:41`, `:43` and `:44` (three bare `Check`s),
`instances/kim2025/five_card_analysis.v:45-47` (the facade's own name-mapping
header index) and ten spelled-type `Check`s inside the manifest, at `:1177`,
`:1182`, `:1187`, `:1210`, `:1217`, `:1225`, `:1229`, `:1235`, `:1248` and
`:1253`. **None of them breaks and none becomes false**, because they name
sample adapters and their distribution bridges, which a restatusing does not
move. So the landing list is unaffected and STATUS's conclusion stands. What is
wrong is only the implied exhaustiveness of the reported result.

### 2.3 Items MISSING from STATUS.md

**H1. BLOCKING. Three passages in `manifest/pgg_analysis_manifest.v` state
that the five-card development supplies no ideal distribution equality. All
three become false and none is in the list.**

They carry neither row name, which is why a search keyed to
`five_card_row_biased` and `five_card_row_repeated` missed them.

(a) `manifest/pgg_analysis_manifest.v:244-248`, the Row 3 header table, the
five-card **uniform** row:

    (* | missing premise      | the ideal distribution equality: the second       *)
    (*                          hypothesis of var_dist_fdistmap_transfer, an      *)
    (*                          equality of two reader pushforwards under an      *)
    (*                          ideal distribution, which the five-card           *)
    (*                          development does not supply |                     *)

This is the anchor. Row 4 at `:306` and Row 5 at `:358-360` both say "as in row
3" and point here. `five_card_static_obs_const` is exactly an equality of two
reader pushforwards under an ideal distribution at this development, so
`:247-248` becomes false. A landing that rewrites Rows 4 and 5 and leaves Row 3
alone leaves the manifest asserting, at the place the other two rows cite, the
very thing the landing disproves.

(b) `manifest/pgg_analysis_manifest.v:754-755`, the docstring of
`five_card_row_uniform`:

    reaching AnalysisBridged; the development supplies no ideal-distribution
    equality, so no model transfer is claimed. *)

The uniform row's own status does not change and STATUS is right about that.
The clause is not about the row, it is about the development, and it becomes
false.

(c) `manifest/pgg_analysis_manifest.v:669-673`, the "Absent capabilities"
section:

    (* Five-card development. No transfer-layer result exists: section 7 of its   *)
    (* facade carries typed status aliases and no theorem. The absent premise is  *)
    (* the second hypothesis of var_dist_fdistmap_transfer, an equality of two    *)
    (* reader pushforwards under an ideal distribution, which the development     *)
    (* does not supply.                                                           *)

False on the first sentence under option 2 and on the last sentence under both
options.

**Exact correction.** Add a fourth subsection to S8 under the heading "Three
further manifest passages about the development, not about a row", listing
(a), (b) and (c) with the text above, and state that (a) is the anchor Rows 4
and 5 point at, so it must be rewritten before or with them. Note beside (c)
that its first sentence is option-2-specific and its last sentence goes false
under either option.

**H3. BLOCKING. The header index of `instances/kim2025/five_card_rows.v` states
both programs' level and one declaration the landing deletes. It is not in the
list.**

    78 : (*   five_card_row_repeated_tableau                                           *)
    79 : (*                           == the repeated row as a program, stopping at    *)
    80 : (*                              Sampled                                       *)
    81 : (*   five_card_row_biased_tableau                                              *)
    82 : (*                           == the biased row as a program, stopping at      *)
    83 : (*                              Sampled                                       *)
    84 : (*   five_card_row_repeated_at_manifest_level                                  *)
    85 : (*                           == the repeated row's program read at the        *)
    86 : (*                              manifest row's own completion level           *)
   119 : (*   five_card_row_biased_levelE                                              *)
   120 : (*                           == the manifest's completion level for the       *)
   121 : (*                              biased row, which its program does not        *)
   122 : (*                              reach                                         *)

`:84-86` indexes `five_card_row_repeated_at_manifest_level`, which S8 item 1
deletes or restates, so the entry dangles either way. `:119-122` says the
biased row's program does not reach `AnalysisBridged`; under the landing a
certified biased program does. `:78-83` state both programs' level. The
file-title line `:4`, "the five-card instance's three rows, written as
programs", also becomes a count a landing changes if the new programs are
added under new names.

**Exact correction.** Add to the `five_card_rows.v` list: "9. The header index
at `:78-86` and `:119-122`, and the file-title line `:4`. `:84-86` indexes the
declaration item 1 deletes. `:78-83` and `:119-122` state the two programs'
level and the level gap."

**H4. BLOCKING. S8 never says whether the landing keeps the two `Tableau
Sampled` programs or retypes them, and the two readings give different change
lists.**

STATUS's items 7 and 8, and its closing sentence "Every other theorem in that
file stays true: ... the three `prefixE` and two `modelE` lemmas", are correct
only under the reading where `five_card_row_repeated_tableau` and
`five_card_row_biased_tableau` **keep their type `Tableau Sampled`** and the
four certified programs are added beside them under new names. The remit's own
phrasing, "the two Kim programs become certified and published", reads the
other way.

Under the retype-in-place reading, four further lemmas stop compiling, because
`PublishedRowAt` is not a `TableauAt` and the projection `tableau_at` does not
apply to it:

    manifest/pgg_tableau.v:411-414
      Record TableauAt (b : CompletionLevel) (Q : StackAt b -> Prop) :=
        MkTableau { tableau_at : StackAt b ; tableau_thm : Q tableau_at }.
    manifest/pgg_tableau.v:678-681
      Record PublishedRowAt (c : Reprice) := MkPublishedRow {
        published_at : StackAt AnalysisBridged ; published_row : AnalysisPathRow ;
        published_thm : BridgedProp c published_at }.

The four are `five_card_row_repeated_prefixE` (`:418-425`),
`five_card_row_biased_prefixE` (`:428-435`), `five_card_row_repeated_modelE`
(`:441-444`) and `five_card_row_biased_modelE` (`:447-450`), each of which
applies `tableau_at` or `sp_f (tableau_at ...)` to one of the two programs. And
the recorded `Fail` at `:473-475` would still fail, but on a type mismatch
between `PublishedRow` and `Tableau (apr_completion five_card_row_biased)`
rather than on the level gap, so item 8's stated reason would be wrong.

**Exact correction.** Add one sentence at the head of the `five_card_rows.v`
list: "The landing ADDS the four certified programs under the names of S6 and
S7 and keeps `five_card_row_repeated_tableau` and `five_card_row_biased_tableau`
at `Tableau Sampled`. Retyping those two in place is not available: `tableau_at`
is a projection of `TableauAt` (`manifest/pgg_tableau.v:411-414`) and a
published row is a `PublishedRowAt` (`:678-681`), so
`five_card_row_repeated_prefixE` (`:418-425`),
`five_card_row_biased_prefixE` (`:428-435`),
`five_card_row_repeated_modelE` (`:441-444`) and
`five_card_row_biased_modelE` (`:447-450`) stop typechecking, and the recorded
`Fail` at `:473-475` changes its reason." If the user wants the retype instead,
items 7 and 8 and the closing "stays true" sentence must be rewritten and those
four lemmas added to the list.

**H5. SHOULD-FIX, option 2 only. The file header of
`instances/kim2025/five_card_analysis.v` is not in the list.**

    16 : (* Section 7 is empty for this development and is documented as empty rather  *)
    17 : (* than omitted.                                                              *)

Under option 2 section 7 gains three aliases and the sentence becomes false.
Under option 1 it stays as accurate as it is now. The facade's phase-H1 check
table at `:30-57` would also want a row for the new aliases, which the
manifest's own convention at `:67-72` makes a pinning obligation rather than a
courtesy.

**Exact correction.** Add to the facade list as item 6: "`:16-17`, 'Section 7
is empty for this development', becomes false under option 2. Under option 2
the new aliases also need a line in the phase-H1 check table at `:30-57`, a
name in the manifest's Row 4 and Row 5 tables and a spelled-type `Check` in the
manifest's five-card section 7 beside `:1385-1389`, because `:67-72` requires
every identifier a table names to be pinned."

### 2.4 The two documents outside the `.v` files

`notes/20260919-kim-tableau-sampled-design.md` and
`docs/superpowers/plans/2026-09-19-kim-tableau-sampled.md`.

**Verdict: historical records. Leave both.** Reasons, from the documents
themselves. The design note's status line says "Landed on 2026-09-19 in commit
8dc3ba0" and points at the plan as the "Plan and as-built record". The plan
says "This plan is also the as-built record" and closes with an "As built,
2026-09-19" table, a numbered deviation and a "Not verified, and why" line.
Both are dated accounts of one executed batch, not standing descriptions of the
tree. Rewriting them would destroy the record of what was decided and why, and
the repository convention preserves probe and plan records.

Two qualifications a landing plan should carry.

- The design note's decision 2, "Do not extend the Tableau with a `certify
  EndpointMarginal` arm", is **not** superseded. The spectral landing adds no
  arm. It uses the existing `SpectralDecay` arm of
  `manifest/pgg_tableau.v:152`. The probe's own S8 verdict, "Nothing under
  `manifest/` needs a new arm", agrees.
- What the two documents say that the landing supersedes is the level claim,
  the design note's title and decision 1 and the plan's construction choice 4,
  all of which say both Kim programs stop at `Sampled`. The correct treatment
  is one dated superseding line added to the design note's status block naming
  the new design note, not an edit to the body. The plan's as-built table is a
  record of a compile that happened and must not be touched at all.

One further historical line, for completeness. `soundness-audit.md:336-337`
cautions that "no lemma in the tree proves the ceiling". That is **true today**,
because `var_dist_le2` lives in the probe and the probe is not in
`_CoqProject`. It becomes false the moment `lib/var_dist_supp.v` lands, so the
landing plan should record that this caution expires with the landing.

---

## 3. The two homes (S10), recomputed

### 3.1 File counts

All four figures are right. My own script, run over `.Makefile.rocq.d`
independently of STATUS's, gives:

| landing | STATUS | mine |
|---|---|---|
| option 1, facade left stating the old statuses | 9 | **9** |
| option 1, facade corrected | 10 | **10** |
| option 2 | 11 | **11** |
| option 1 + `card_tnth_count` to `den_boer_encoding.v` | 18 | **18** |
| option 2 + `card_tnth_count` to `den_boer_encoding.v` | 19 | **19** |

The member lists match too. STATUS's phrase "the totals go from 9 or 10 to 18"
is exact rather than approximate: both the 9-set and the 10-set enlarge to the
same 18, because `instances/kim2025/five_card_analysis.vo` is already in
`den_boer_encoding.v`'s sixteen reverse-dependants. `den_boer_encoding.v`'s
closure is 16, as stated.

`instances/psl211/psl211_endpoints.vo` is in **none** of the five landing sets
and in none of the eighteen closures I computed. The freeze rule is respected
by every home and every branch on the page. Confirmed.

### 3.2 Is `instances/kim2025/five_card_mixing.v` placeable below the facade?

**Yes, with no import cycle.** The file would need, and needs no more than:

| import | for |
|---|---|
| `instances/kim2025/five_card_exec.v` | `five_card_algebra`, `five_card_params`, `five_card_sample`, `five_card_sample_cut_distE` |
| `instances/kim2025/five_card_kim.v` | `fc_sigma`, `fc_kim_gens`, `fc_kim_security_bundle`, `kim_security_bundle_centi`, `kim_centi_lt/gt/spec`, `kim_lambda2_at_centi`, `kim_deal_centi_lt`, `kim_one_cut_centiE` |
| `instances/denboer1989/den_boer_encoding.v` | `den_boer_layout` |
| `reconstruct/algebraic_rigidity.v` | `ShuffleMarginalBound`, `sw_rho_dist`, `sw_bound_eps`, `sw_bound` |
| `security/pgg_sample_adapter.v` | `sa_cut_dist` |
| `protocol/pgg_instance.v` | `static_coalition_obs` |
| the new `lib/var_dist_supp.v` | `var_dist_fdistmap_supp_inj`, `fdistmap_inj_uniform_id`, `card_tnth_count` |

None of these requires the facade or the manifest. The only direct requirer of
`instances/kim2025/five_card_analysis.vo` in the whole tree is
`manifest/pgg_analysis_manifest.vo`, and the manifest's reverse closure holds
no `instances/kim2025` file but `five_card_rows.vo`. So the facade may require
the new file, and no cycle arises. `five_card_models.v` is **not** needed by
the mixing and constancy theorems: it supplies `kim_centi_family` and
`kim_biased_family`, which the certificates consume and these three theorems do
not. The new file can therefore sit anywhere between `five_card_exec.v` and
`five_card_analysis.v`, which is what STATUS's "anywhere at or above
`five_card_exec.v`" says.

**H10. SHOULD-FIX, and option 2 fails without it.**
`notes/probes/2026-09-19-kim-spectral-arm/kim_sc_close_probe.v:21` carries

    From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.

That Require is dead. I extracted every identifier in the file's body, stripped
comments and `Require` lines, and intersected it with the declared names of
`pgg_analysis_manifest.v`, `pgg_analysis_status.v`, `pgg_tableau.v` and
`pgg_tableau_syntax.v`. The intersection is empty (the one hit is the tactic
`apply`). So the three mixing declarations do sit below the facade as S10
claims, but the probe file they live in does not, and a landing that copies the
file across keeps a Require of the manifest and makes option 2 a cycle
(`five_card_analysis.v` would require a file that requires the manifest that
requires `five_card_analysis.v`).

**Exact correction.** Add to the option-2 paragraph: "The landed
`five_card_mixing.v` must drop `kim_sc_close_probe.v:21`'s `From pgg_smc
Require Import pgg_analysis_status pgg_analysis_manifest`. It is dead in the
probe and would make option 2 a cycle."

### 3.3 Would the facade then need to import it?

Yes under option 2, and that is the point of option 2: the facade aliases the
three theorems so the manifest's Row 4 and Row 5 tables can name them and the
checker can pin them, mirroring `PGL27Analysis.word_mixing`. Verified: 
`instances/pgl27/pgl27_mixing.v` has seven direct requirers, `pgl27_analysis.vo`
among them, so the precedent is exactly as STATUS describes. No cycle, by 3.2.

---

## 4. The numbers

Every figure reproduces. Python, at this revision:

| quantity | value | where STATUS states it | verdict |
|---|---|---|---|
| `2*sqrt(5)*(1/80)^7` | `2.132480599880019e-13` | `:301` "about `2.13e-13`", `:303` "`2.1325e-13`" | correct |
| `2^-39` | `1.8189894035458565e-12` | `:304` "`1.8190e-12`" | correct |
| ratio `2^-39 / (2*sqrt5*(1/80)^7)` | `8.529922399520068` | `:302` "a factor of 8.53", `:304` "`8.5299`" | correct |
| `sqrt(5)/40` | `0.05590169943749475` | `:364` "about `0.0559`" | correct |
| `sqrt(5)/80` | `0.027950849718747374` | `:411` "`sqrt 5 / 80 = 0.02795`" | correct |
| `1/25` | `0.04` | `:404` "`1 / 25 = 0.04`" | correct |
| `2^-40` | `9.094947017729282e-13` | used only symbolically | n/a |

The comparisons with the ceiling 2 are right in both places they appear in the
probe comments. `kim_spectral_rows_probe.v:164` says the one-cut row's bound is
"at about three percent of the ceiling": `(sqrt5/40)/2 = 2.795%`. `:384-385`
says one twenty-fifth is below two: `0.04 < 2`, and it is exactly 2 per cent of
the ceiling. STATUS's round-1 counterpart, `soundness-audit.md:333`, says the
same. No other numeric figure occurs in the five `.v` files.

One reading note, not a finding. `STATUS.md:410-413` compares "the exact
distance" with "a spectral overestimate `sqrt 5 / 80 = 0.02795`". The two
numbers being compared there are the marginal-bound epsilons, `1/50 = 0.02`
against `sqrt5/80 = 0.02795`, which is what `kim_biased_exact_le_eps` states.
The reader-facing number of form 2 is the repriced `1/25 = 0.04`, twice the
first. The sentence is consistent as written because it names
`kim_biased_exact_le_eps` in the same breath, but a paper drafted from it could
put `0.04` and `0.02795` side by side and draw the wrong conclusion.

---

## 5. The certified proposition, and S9

**In one sentence:** at every real field and every index of the row's model
family, for every coalition of at most one of the five seats and for every two
committed pairs, the sum of absolute differences between the law of that
coalition's static endpoint reading at the first pair and its law at the
second, both taken under the row's own biased cut law, is at most the row's
published number.

Checked against the definition rather than the prose.
`SpectralPropAt` (`manifest/pgg_tableau.v:331-339`) is

    forall (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1})
           (x x' : ex_inputT E),
      (#|C| < profile_k (instance_profile A))%N ->
      var_dist (fdistmap (static_coalition_obs C x) (sa_cut_dist sa))
               (fdistmap (static_coalition_obs C x') (sa_cut_dist sa))
      <= c.

with `profile_k (instance_profile five_card_algebra) = 2`, so "at most one
seat" is exact, and with the cut law `sa_cut_dist sa` the row's own biased law
and not the ideal. The ideal enters only through the certificate's fields.

**S9 still matches, with no discrepancy.** Its citation of
`manifest/pgg_tableau.v:331` is right, its four "it is NOT" bullets are all
accurate, and its two closing remarks are right: the two run arguments range
over all four committed pairs, and the reading of `sa_cut_dist sa` as a
conditional law given the input rests on `kim_input_dist` being a product
(`instances/kim2025/kim_input_privacy.v:58-60`), a property of these two
adapters and not of the arm.

**The round-1 "what a paper may and may not say" material still matches**, and
nothing in round 2 or in the second fix pass moved against it. The three
"may say" bullets, the three "may not say" bullets and the two "take care"
bullets are all consistent with the proposition above and with the corrected
number `2.13e-13`. The one clause that will expire is the tail of
`soundness-audit.md:336-337`, "no lemma in the tree proves the ceiling", which
is true of the production tree today and false once `var_dist_le2` lands, as
noted in 2.4.

The second fix pass's own finding, that
`instances/kim2025/five_card_analysis.v` states the two transfer statuses a
second time at `:364` and `:368` with `exec_transfer_status` shared by the
uniform and the single-biased path, and that the manifest pins those aliases
again at `:1385-1389`, is **correct in every particular**. I verified each line
verbatim. It is now in S8 and is the strongest part of the change list.

---

## Findings, by ID

| ID | Severity | What | Where |
|---|---|---|---|
| H1 | **BLOCKING** | Three manifest passages saying the five-card development supplies no ideal distribution equality are missing from the change list and become false | `manifest/pgg_analysis_manifest.v:244-248`, `:754-755`, `:669-673` |
| H2 | **BLOCKING** | The mixing field is said to discharge the second hypothesis of `var_dist_fdistmap_transfer`. It discharges the first; the constancy field discharges the second | `STATUS.md:542`, `:593-594` against `security/pgg_collusion_bound.v:977-988` and `manifest/pgg_tableau.v:566-570` |
| H3 | **BLOCKING** | The header index of `five_card_rows.v` states both programs' level and indexes a declaration the landing deletes; missing from the list | `instances/kim2025/five_card_rows.v:78-86`, `:119-122`, `:4` |
| H4 | **BLOCKING** | S8 never states whether the two `Tableau Sampled` programs are kept or retyped; under the retype reading four lemmas stop compiling and item 8's reason is wrong | `instances/kim2025/five_card_rows.v:418-425`, `:428-435`, `:441-444`, `:447-450`, `:473-475` |
| H5 | SHOULD-FIX | The facade file header "Section 7 is empty for this development" is missing from the list; false under option 2 | `instances/kim2025/five_card_analysis.v:16-17`, `:30-57` |
| H10 | SHOULD-FIX | The landed mixing file must drop the probe's dead Require of the manifest, or option 2 is a cycle | `notes/probes/2026-09-19-kim-spectral-arm/kim_sc_close_probe.v:21` |
| H6 | NOTE | "three `prefixE`" should be "two" | `STATUS.md:684` |
| H7 | NOTE | Two line ranges short at the head: `:28-30` and `:33-42` | `STATUS.md` items 2 and 3 of the `five_card_rows.v` list |
| H8 | NOTE | The family-name grep result is not exhaustive; none of the extra hits breaks, so the list is unaffected | `STATUS.md:626-632` |
| H9 | NOTE | "obsolete" should be "false", or should match whichever reading H4 settles | `STATUS.md` item 2 |

Nothing found here is a kernel-level unsoundness. No `Admitted`, `Axiom`,
`admit`, `Abort`, `Parameter`, `Hypothesis` or `Conjecture` was introduced, and
no statement or number the kernel checks is disputed. Every blocking finding is
a sentence in `STATUS.md` or a sentence a landing executed from `STATUS.md`
would leave standing and false in a permanent file.
