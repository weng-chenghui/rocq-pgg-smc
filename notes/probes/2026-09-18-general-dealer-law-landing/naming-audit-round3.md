# Naming and style audit of the general dealer law landing, round 3

Date: 2026-09-19

Independent read-only audit. Nothing was compiled, no Rocq process was started,
no existing file was edited. Scope is the five round-2 items and anything a
round-2 replacement introduced. Every scan was run in Python with `\b`.

Method: both touched `.v` files were diffed against their
`history/*.2026-09-19-before-fix2.v` copies, each replaced passage was then read
in place with its neighbours, and the mechanical scans were rerun over all five
LAND files.

The diff confirms what was reported: five passages changed in
`psl211_models_landing.v` and one deletion in
`pgl27_profile_privacy_landing.v`. No other line of either file moved.

---

## 1. The five items

### R2-B1. RESOLVED

`psl211_models_landing.v:995-1000`

```
(** psl211_perdeck_fiber_card_neq — at one deck description the two
    chiralities have different numbers of cuts producing one reading.  The
    symmetry the all-decks counting argument uses holds only in its per-cut
    form, which fixes a cut and counts deck descriptions.  The statement with
    the roles exchanged, fixing a deck description and counting cuts, is
    false, and psl211_perdeck_deal witnesses it. *)
```

The pronoun is gone. Each of the two statements now carries its own quantifier
pair, "fixes a cut and counts deck descriptions" against "fixing a deck
description and counting cuts", so no reading survives in which
`psl211_alldecks_per_cut_count` fails anywhere. The second sentence matches the
annotated lemma at `:1001-1002`,
`#|psl211_perdeck_fiber true| != #|psl211_perdeck_fiber false|`, whose fibers
are sets of cuts at the fixed deck description `psl211_perdeck_deal`.

Read against its neighbours: `psl211_perdeck_raw_countE:886-890` states the same
failure on raw counts and `psl211_perdeck_law_neq` states it on laws. The three
now agree on direction and on vocabulary, and each names a different object, so
the sequence reads as a chain rather than as three attempts at one sentence.

### R2-S1. RESOLVED

`pgl27_profile_privacy_landing.v:559-575`. The duplicated block is gone. The
`(* Expected failure: ... *)` comment sits directly above its `Fail` at `:572`
and still carries the content S6 asked to keep outside the statement comment,
"The two premises are declared coalition size first and validity last, so
omitting the last argument leaves `uniq d ->` as an arrow in the term's type".
The statement comment of `pgl27_alldecks_dealer_view_law` ends at "dealer
model." and states no apparatus rationale.

### R2-S2. RESOLVED

`psl211_models_landing.v`: the header's boxed comment is now 134 lines, every
one exactly 80 bytes, zero off-width. The rewrapped entry at `:117-119` reads

```
(*   psl211_perdeck_raw_countE == at one deck description the two             *)
(*                              chiralities have 0 and 1 cuts producing one   *)
(*                              reading                                       *)
```

with no numeral at the head of a line.

`pgl27_profile_privacy_landing.v:9,10,21,22` were correctly left alone. All four
are byte-identical to `instances/pgl27/pgl27_profile_privacy.v:9,10,21,22`, so
they are that file's defect and repairing them here would make the copy differ
from production for a reason this landing has nothing to do with.

### R2-S3. RESOLVED

The three glosses now agree with their statement comments.

| declaration | header | statement comment |
|---|---|---|
| `psl211_perdeck_deal` | `:73` "the deck description fixing the counterexample" | `:787-789` "the deck description that fixes the counterexample" |
| `psl211_perdeck_raw_countE` | `:117` "at one deck description" | `:889-890` "even though summing over deck descriptions they do" |
| `psl211_dealer_view_indep_of_deck_unsat` | `:110` "uniform law on deck descriptions" | `:1116` "the uniform law on deck descriptions meets it" |

`psl211_fixed_deal_delta` already agreed and is untouched.

One check on the repaired sentence at `:889-890`, because the substitution
changed what it quantifies over. "At a fixed deck description the two
chiralities do not have equally many cuts producing a given reading, even though
summing over deck descriptions they do." Summing over deck descriptions,
`Σ_d #{g : view(b,d,g) = v}` equals `Σ_g #{d : view(b,d,g) = v}`, which
`psl211_alldecks_per_cut_count` makes equal for the two chiralities. The
sentence is true as rewritten.

### R2-S4. RESOLVED

`psl211_models_landing.v:44-52`

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

"Restates" is now attached to `psl211_alldecks_view_indep_via_dealer`, which
does restate an existing theorem, and the two refutations are said to bound the
route rather than to restate anything. A route goes through a condition. Every
line is 80 bytes and every claim checks out against the declarations it
describes.

### R2-S5. RESOLVED

`notes/20260918-general-dealer-law-landing-design.md:132`. Row 5 now reads "The
declarations and their order are the landing copy verbatim: everything the copy
adds after the last line of the production file, which is the banner comment,
three `Local Notation`s, Section `psl211_dealer`, the raw-count chain and the
two refutations, together with the `Local Opaque` and `Local Transparent`
commands that bracket them and are landed in place."

This is better than the round-2 pasteable, which pinned a line range that any
later edit would invalidate. It names the boundary structurally and it names the
seal commands, which was the point.

One observation, not a finding. The clause scopes the new material to what
follows the production file's last line, so it does not itself carry the
header-block additions, the ten-line dealer-route paragraph and the twenty-eight
table rows. Those are carried twice over elsewhere: by the Acceptance condition,
"The plan then quotes the landing copies verbatim", and by ledger row L11. The
round-2 pasteable had the same property, so this is not something the
replacement introduced.

---

## 2. Mechanical re-checks

| check | result |
|---|---|
| the banned-vocabulary scan, whole words, five `.v` files and `STATUS.md` | zero hits |
| metaphor words for a mathematical result, and that word for a bound | zero hits |
| lines over 80 bytes | zero, all five `.v` files |
| header boxed-comment width | `dealer_privacy.v` 80 on 51 lines, `design_privacy_landing.v` 80 on 27, `psl211_models_landing.v` 80 on 134, all with zero off-width. `pgl27_profile_privacy_landing.v` 80 on 78 with the four production-inherited lines |
| `Print Assumptions`, `Time`, `Timeout`, `Show`, `Admitted`, `Abort`, `Axiom`, `Parameter`, `Conjecture` in the four candidate permanent texts | zero |
| `Fail` per file | `dealer_privacy.v` 0, `design_privacy_landing.v` 0, `pgl27_profile_privacy_landing.v` 2, `psl211_models_landing.v` 1, `landing_fidelity.v` 4 |

Vocabulary of the PSL block after the edits: chirality 29 and chiralities 12
against class 0, cut 16 and cuts 7 against shuffles 0 with all 6 "shuffle" uses
reading "shuffle group", deck description 10 against deal description 0.

Bare "deal" stands at 19 and "deals" at 1. Round 2 scoped these out deliberately:
the type is `psl211_deal` and the identifiers are `psl211_perdeck_deal` and
`psl211_dealer_delta`, so the word belongs to the carrier, while the prose word
is "deck description", which is the split production `psl211_models.v` already
has. Nothing here changed that judgement.

---

## 3. Verdict

All five round-2 items are resolved, each replacement reads correctly in place,
none of them made a neighbouring sentence wrong, and every mechanical scan is
clean.

The landing copies together with the three import substitutions recorded in the
spec are fit to be written into the permanent files verbatim. Those
substitutions are the two
`From general_dealer_law_landing Require Import dealer_privacy.` lines becoming
`From pgg_reconstruct Require Import dealer_privacy.`, and the deletion of the
`design_privacy_landing` import, because after the landing the two fiber lemmas
come from `design_privacy` itself.

No naming or style finding remains open against this landing.

VERDICT: GO
