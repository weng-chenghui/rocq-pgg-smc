# Naming and style audit of the general dealer law landing, round 2

Date: 2026-09-19

Independent read-only audit. Nothing was compiled, no Rocq process was started,
no existing file was edited. `git status --short` shows no tracked file changed
and the only new paths are this report and the round-1 one. Every scan was run
in Python with `\b`.

Method: each of the five LAND `.v` files was diffed against its
`history/*.2026-09-19-before-fix.v` copy, and every changed line of comment text
was then read on its own, without reference to what it replaced, against the
declaration it annotates and against the lemma it cites.

---

## 1. Round-1 findings, current status

| id | status | current evidence |
|---|---|---|
| B1 necessity claim | RESOLVED | `psl211_models_landing.v:1112-1113` now reads "and the uniform deal law meets it." The definite article is gone and no uniqueness is asserted |
| B2 averaging direction | PARTIAL | the wrong word is gone. `:994-997` now says "per-cut" and "cuts" and "deck descriptions". The clause the fix added in its place does not resolve its own pronoun. R2-B1 below |
| S1 pgl27 comment separator | RESOLVED | the block measures 21 `==` comments and 0 em-dash ones. The file is now uniform at 37 of 37 |
| S2 generic file vocabulary | RESOLVED | `dealer_privacy.v` measures 0 "cut" and 0 "deal". Its words are "shuffle" 13, "deck" 21, "observation" 14, "secret" 23, "section" 13 |
| S3 chirality against class | RESOLVED | 0 "class" and 0 "classes" in the PSL block, against 29 "chirality" and 12 "chiralities". The two "class" uses left in the pgl27 block are `pgl27_class_decks_pos` and the class of decks of a secret, which is that instance's own word, `class_decks orbit_class` |
| S4 cut against shuffle | RESOLVED | the PSL block measures 0 "shuffles" and 6 "shuffle", and all six are "shuffle group", `:569,601,785,894,1021,1149`. Production reserves the word the same way, `psl211_models.v:58,187`. Cuts 21 |
| S5 deck description | PARTIAL | "deal description" is 0 in the block and "deck description" is 9. Bare "deal" is still 21 and "deals" 2, and the header was normalised while three of the comments it glosses were not. R2-S3 below |
| S6 apparatus rationale | PARTIAL | the clause is out of the statement comment, `:421-427` now ends "dealer model. *)". Where it landed it duplicates the comment beneath it. R2-S1 below |
| S7 header entries | RESOLVED | five entries at `pgl27_profile_privacy_landing.v:76-81` and three at `psl211_models_landing.v:129-133`. All eight glosses check out against their lemmas. Ordering at R2-N1, widths at R2-S2 |
| S8 header paragraph | PARTIAL | the paragraph is there, `psl211_models_landing.v:44-53`, and its four factual claims are accurate. Its last sentence is not. R2-S4 below |
| S9 mutation move | RESOLVED | `dealer_privacy.v` has 0 `Fail`, three sections `dealer_kernel`, `carrier_transport`, `product_sections` matching its header's Section 1 to 3, and eight declarations matching its header table. `landing_fidelity.v` has the four `Fail` commands. pgl27 keeps 2 and psl211 keeps 1 |
| S10 family split | RESOLVED | `psl211_perdeck_entry_perm_enum` at `:893-895`, use site updated at `:943`, old name absent from the file. Collision scan over 520 files finds the new name nowhere |
| S11 spec L1 counts | RESOLVED | folded into the spec |
| S12 file plan precision | PARTIAL | the pgl27 row is now exact. The psl211 row names a location that holds a third of the material. R2-S5 below |
| S13 imports and scope fix | RESOLVED | spec file plan row 5 names `psl211_blocks`, `psl211_closure`, `Import Num.Theory` and the `%N` annotation |
| N1 scope order | RESOLVED | `dealer_privacy.v:65-67` is fdist, proba, ring |
| N2 import line | OPEN by choice | `:64` still combines. Precedent exists, no action asked |
| N3 hybrid header | OPEN by choice | no action asked |
| N4 compound spelling | OPEN by choice | settled at round 2 B010, not reopened |
| N5 L8 scan scope | RESOLVED | STATUS.md now states what the count covered |
| N6 section case claim | RESOLVED | STATUS.md corrected |
| N7 that word in STATUS.md | RESOLVED | the word-scan is clean across all five `.v` files and STATUS.md |
| N8 lone `by [].` | OPEN by choice | one at `pgl27_profile_privacy_landing.v:456`, 24 in the production tree |
| N9 mutation section name | OPEN by choice | no action asked |
| N10 probe-file identifiers | OPEN by choice | probe file |
| N11 dated measurement | OPEN by choice | precedent in three production files |

Nineteen resolved or closed by choice, four partial, one of which carries the
blocking item.

---

## 2. Findings on the changed text

### R2-B1. BLOCKING. The rewritten `psl211_perdeck_fiber_card_neq` comment

`notes/probes/2026-09-18-general-dealer-law-landing/psl211_models_landing.v:994-997`

```
    chiralities have different numbers of cuts producing one reading.  The
    per-cut symmetry that the all-decks counting argument uses is therefore
    a statement about the average over deck descriptions: at the deck
    description psl211_perdeck_deal it fails. *)
```

The first half is right and should be kept. The clause after the colon does not
resolve its own pronoun. The grammatical antecedent of "it" is "The per-cut
symmetry", and that symmetry is
`psl211_alldecks_per_cut_count`, `instances/psl211/psl211_alldecks.v:1334`,
which fixes a cut and counts deck descriptions. It is not indexed by deck
descriptions, so it cannot fail at one, and it does not fail anywhere: it is the
fact `psl211_alldecks_view_indep` rests on. A reader who takes the sentence at
face value concludes that the counting argument behind this file's main theorem
breaks at `psl211_perdeck_deal`.

Two benign readings also exist, one taking "it" to be the chirality symmetry in
its per-deck-description form and one taking it to be "the statement about the
average" read pointwise. The sentence does not choose between the three, and one
of the three contradicts the file's headline result. That is the failure the
statement-comment rule exists to prevent: a domain expert reading only the
comment cannot tell which claim is being made.

Mitigating, and the reason this is a one-line repair rather than a rethink:
`psl211_perdeck_law_neq:1029-1033`, 35 lines below, already states the same
thought unambiguously, and the fix below borrows its shape.

PASTEABLE, replacing `:993-997` entire:

```
(** psl211_perdeck_fiber_card_neq — at one deck description the two
    chiralities have different numbers of cuts producing one reading.  The
    symmetry the all-decks counting argument uses holds only in its per-cut
    form, which fixes a cut and counts deck descriptions.  The statement with
    the roles exchanged, fixing a deck description and counting cuts, is
    false, and psl211_perdeck_deal witnesses it. *)
```

Every line is under 80 bytes and the vocabulary is the file's.

### R2-S1. SHOULD-FIX. The moved rationale duplicates the comment below it

`pgl27_profile_privacy_landing.v:567-573`

```
(* the premises are declared coalition size first and validity last, so that
   dropping validity leaves an arrow rather than shifting an argument *)
(* Expected failure: the per-deck view law with the validity premise dropped.
   The two premises are declared coalition size first and validity last, so
   omitting the last argument leaves `uniq d ->` as an arrow in the term's
   type, and what is ascribed a bare equality of laws is a function into
   one. *)
```

The two blocks state the same fact in the same words. The mutation comment
already carried the content, so the clause removed from the statement comment
did not need a new home. Round 1 asked for the move without checking that, which
is this auditor's error and is corrected here.

PASTEABLE: delete `:567-568`. The `(* Expected failure: ... *)` block that
follows already says "The two premises are declared coalition size first and
validity last", which is exactly what S6 wanted preserved outside the statement
comment.

### R2-S2. SHOULD-FIX. Seven header lines are a byte short, six of them new

`psl211_models_landing.v`. The header's boxed comment runs at 80 bytes on 127
lines. Seven lines close their `*)` one column early. Line `:67` was already
short before the fix pass, the other six were introduced by it.

| line | fix |
|---|---|
| 67 | `(*                              space                                         *)` |
| 73 | `(*   psl211_perdeck_deal     == the deck description fixing the               *)` |
| 74 | `(*                              counterexample                                *)` |
| 78 | `(*   psl211_fixed_deal_delta == the dealer laying one deck description at     *)` |
| 127 | `(*                              description the reading of three seats is     *)` |
| 128 | `(*                              not independent of the chirality              *)` |

Lines `:117-119` need a rewrap as well as a pad, because the present break puts
a bare numeral at the head of a line, "chiralities have 0 and" then "1 cuts
producing one reading".

PASTEABLE, replacing `:117-119`:

```
(*   psl211_perdeck_raw_countE == at one deck description the two             *)
(*                              chiralities have 0 and 1 cuts producing one   *)
(*                              reading                                       *)
```

`pgl27_profile_privacy_landing.v:9,10,21,22` are also short. Those four are
identical in the pre-fix copy and in the production file
`instances/pgl27/pgl27_profile_privacy.v`, so they are a pre-existing defect of
that file and not the landing's to repair. R2-N2.

### R2-S3. SHOULD-FIX. The header was normalised and three of its glosses were not

The vocabulary pass replaced the compound "deal description" everywhere, 0 left,
and normalised the header. It did not touch bare "deal", which remains 21 times
in the block against 9 "deck description". Production `psl211_models.v` uses
"deck description" 8 times and bare "deal" once. The visible consequence is
three declarations whose header gloss and statement comment now name the same
object differently.

| declaration | header | statement comment |
|---|---|---|
| `psl211_perdeck_deal` | `:73` "the deck description fixing the counterexample" | `:787` "the deal that fixes the counterexample" |
| `psl211_perdeck_raw_countE` | `:117` "at one deck description" | `:888` "even though summing over deals they do" |
| `psl211_dealer_view_indep_of_deck_unsat` | `:110` "uniform law on deck descriptions" | `:1113` "the uniform deal law" |

`psl211_fixed_deal_delta` agrees on both sides and needs nothing.

The narrow repair is the three comments, not all 21 uses. Bare "deal" is
defensible at `:692` and `:748`, where it echoes the wording of
`psl211_alldecks_per_cut_count`'s own comment, and at `:1192`, which is inside a
proof.

PASTEABLE:

`:787`
```
(** psl211_perdeck_deal — the deck description that fixes the counterexample:
    block index zero of the chirality's table, with both labellings the
    identity. *)
```

`:888`
```
    producing a given reading, even though summing over deck descriptions
    they do. *)
```

`:1112-1113`
```
    dealer_shuffle_view_indep is available to this instance, and the uniform
    law on deck descriptions meets it. *)
```

### R2-S4. SHOULD-FIX. Two sentences of the new header paragraph

`psl211_models_landing.v:47` and `:51-52`.

`:47` "The route is the mixed-law condition". A route is not a condition. The
route goes through it.

`:51-52` "Both restate or bound an existing result and replace no proof." The
nearest plural antecedent is "Two refutations" in the preceding sentence, and
the two refutations restate nothing. `psl211_dealer_view_indep_of_deck_unsat`
and `psl211_fixed_deal_view_dep` have no existing counterpart in the tree. The
declaration that restates an existing result is
`psl211_alldecks_view_indep_via_dealer`, which the sentence does not name.
Round 1 supplied this wording, so this too is the auditor's own text corrected.

The paragraph's other four claims all check out: the three coordinates placed in
the sample space, the per-cut count discharging the premise, the per-deck
condition having no solution, and the fixed dealer breaking independence at
three seats.

PASTEABLE, replacing `:44-52`:

```
(* The dealer route. The all-decks independence is obtained a second way,     *)
(* from the dealer model of reconstruct/dealer_privacy.v, by placing the      *)
(* chirality, the deck description and the cut in its sample space. The       *)
(* route goes through the mixed-law condition, whose premise the per-cut      *)
(* count of psl211_alldecks.v discharges, and it restates                     *)
(* psl211_alldecks_view_indep without replacing its proof. Two refutations    *)
(* bound it: the per-deck condition has no solution under this dealer, and    *)
(* under a dealer laying one fixed deck description the reading of three      *)
(* seats is not independent of the chirality.                                 *)
```

Every line is 80 bytes.

### R2-S5. SHOULD-FIX. The spec locates the PSL material in one section of three

`notes/20260918-general-dealer-law-landing-design.md`, file plan row 5, now
reads "The declarations and their order are the landing copy verbatim, Section
`psl211_dealer` at the end of `psl211_models_landing.v`."

`Section psl211_dealer` is `:583-766`. The landed material is `:562-1222`. The
456 lines outside the section carry three `Local Notation`s at `:567-577`, four
`Local Opaque` and `Local Transparent` commands at `:581,771,963,1017,1221,1222`,
the whole raw-count chain, and both refutations. A plan written verbatim from
this row would land a third of the block and drop every declaration the two
refutations depend on.

The pgl27 row does not have this problem: that block is exactly the three
sections the row names.

PASTEABLE, replacing the added clause of row 5:

```
The declarations and their order are the landing copy verbatim, `psl211_models_landing.v:562-1222`, which is the banner comment, three `Local Notation`s, `Section psl211_dealer`, the raw-count chain and the two refutations, together with the four `Local Opaque` and `Local Transparent` commands that bracket them and must be landed in place.
```

### Notes

**R2-N1.** The eight new header entries are appended after the headline results
rather than at their declaration position, `pgl27_profile_privacy_landing.v:76-81`
after `pgl27_view_indep_alldecks_via_dealer`, and
`psl211_models_landing.v:129-133` after `psl211_fixed_deal_view_dep`. Both
files' existing Key results lists follow declaration order, and so does
`instances/pgl27/pgl27_profile_privacy.v`. Reading the punchlines first and the
supporting equations after is a defensible alternative order. No action asked.

**R2-N2.** `pgl27_profile_privacy_landing.v:9,10,21,22` are short of the 80-byte
column. They are byte-identical in the pre-fix copy and in the production file,
so they belong to `instances/pgl27/pgl27_profile_privacy.v` and not to this
landing. Mentioned so that a later reader does not attribute them to it.

**R2-N3.** Round 1's report named four metaphor words as scan targets, which
put them in a report file as words. This report names none of them and refers
only to the banned-vocabulary scan.

---

## 3. Mechanical re-checks

All run in Python with `\b` over the five LAND `.v` files and `STATUS.md`.

| check | result |
|---|---|
| the banned-vocabulary scan, whole words, identifiers and comments | zero hits in all five `.v` files and in `STATUS.md`. The round-1 STATUS.md hit is gone |
| metaphor words for a mathematical result | zero hits |
| lines over 80 bytes | zero, in all five `.v` files |
| `Print Assumptions`, `Time`, `Timeout`, `Show`, `Admitted`, `Abort`, `Axiom`, `Parameter`, `Conjecture` in the four candidate permanent texts | zero |
| `Fail` per file | `dealer_privacy.v` 0, `design_privacy_landing.v` 0, `pgl27_profile_privacy_landing.v` 2, `psl211_models_landing.v` 1, `landing_fidelity.v` 4 |
| lone `by [].` | one, `pgl27_profile_privacy_landing.v:456`, precedent 24 in the production tree |
| collision, `psl211_perdeck_entry_perm_enum` | 520 files scanned, `lib protocol groups security smc reconstruct instances manifest` plus installed `infotheo` and `mathcomp`. No occurrence. The old name is absent from the LAND copy |
| comment separator, pgl27 block | 21 `==`, 0 em-dash. Target file 16 `==`, 0 em-dash |
| comment separator, psl211 block | 45 em-dash, 0 `==`. Target file 35 em-dash, 0 `==` |
| header comment width, `dealer_privacy.v` and `design_privacy_landing.v` | 80 bytes throughout, no off-width line |

Per-block vocabulary, block against the production file it lands in:

| word | dealer_privacy.v | pgl27 block / prod | psl211 block / prod |
|---|---|---|---|
| shuffle, element sense | 13 | 5 / 0 | 0 / 0 |
| shuffle group | included above | included above | 6 / 2 |
| cut | 0 | 0 / 0 | 21 / 20 |
| view | 13, identifiers | 12 / 1 | 0 / 6, identifiers only |
| reading | 0 | 0 / 1 | 23 / 11 |
| observation | 14 | 0 | 0 |
| chirality | 0 | 0 | 41 / 14 |
| class | 0 | 2 / 0, the class of decks of a secret | 0 / 1 |
| deck description | 0 | 0 | 9 / 8 |
| deal | 0 | 0 / 3 | 21 / 1, R2-S3 |

Each block now speaks its own file's language on every axis but the last.

---

## 4. Does the spec now support a verbatim plan

For three of the four homes, yes. `reconstruct/dealer_privacy.v` and
`reconstruct/design_privacy.v` name every declaration and its home. The pgl27
row names its three sections exactly. The "Audit results, 2026-09-19" section
states the three import substitutions a plan must make, the two
`From general_dealer_law_landing Require Import dealer_privacy.` lines becoming
`From pgg_reconstruct Require Import dealer_privacy.` and the
`design_privacy_landing` line being deleted, and it states that the mutation
move carries the two positive controls and the three sections with the four
`Fail` commands.

The psl211 row does not, for the reason at R2-S5. With that clause corrected,
the spec plus the landing copies plus the three substitutions is enough to write
the plan without judgement calls.

---

## What blocks the landing

R2-B1 alone, one sentence in one statement comment, replacement supplied.

## What does not

R2-S1 to R2-S5 and R2-N1 to R2-N3. R2-S1 through R2-S4 are comment and header
edits in the same two files as R2-B1 and should go in the same pass. R2-S5 is
one clause of the spec.

VERDICT: NO-GO
