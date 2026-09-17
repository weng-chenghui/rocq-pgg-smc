# Style and statement audit, group A

Scope: `instances/pgl27/pgl27_encoding.v`, `pgl27_encoding_r7.v`,
`pgl27_encoding_r5.v`, `pgl27_leakage_transport.v`, and the parts of
`pgl27_leakage_census.v` changed by `git diff 20da27e..a386865`.
Branch `feat/pgl27-encoding-parameter`, HEAD `a386865`. Read-only; nothing
was compiled.

## Verdict

**PASS-WITH-FIXES.**

Naming, layout and proof idiom are in good shape: no line exceeds 80 columns
in any of the five files, no banned word appears (`apex`, `gate*`, `posit*`,
and the metaphor set `ramp` / `beats` / `escape` / `cap`-as-noun all scan
clean), no status marker or plan/task id or absolute line number appears in
any declaration comment, and the arithmetic in every census and ratio comment
checks out against the statement it sits on. The cross-ratio classes are
attached the right way round everywhere: `subset_class (… rep_harmonic) =
false` and `subset_class (… rep_equianharmonic) = true`
(`pgl27_leakage_transport.v:127`, `:139`), the `_r7` minimum above the
threshold is 5/7 on the harmonic class (`pgl27_encoding_r7.v:218`) and the
`_r5` minimum is 11/14 on the equianharmonic class
(`pgl27_encoding_r5.v:251`), and `pgl27_encoding_r5.v:247-250` correctly says
this is the reverse of the `_r7` ordering.

Four must-fix items remain: one file-header claim that the file's own proofs
contradict, two header claims that promise results the files do not contain,
and one lemma name that asserts the opposite of what its statement says.

---

## `pgl27_leakage_transport.v`

### T1 (must-fix) — header line 19 states something the file's proofs refute

`pgl27_leakage_transport.v:19`

```
(* an instance file supplies its own census numbers and obtains its closed   *)
(* form. Nothing here mentions a particular deck pair.                       *)
```

`pgl27_subset_class_harmonicE` and `pgl27_subset_class_equianharmonicE` both
route through `orbit_encode`, which *is* the `_r7` deck pair:

- `:130` `have Hhs : heart_set (orbit_encode false) = pgl27_code_coalition rep_harmonic.`
- `:133` `by rewrite -Hhs; exact: (orbit_encodeK false).`
- `:142` `have Hhs : heart_set (orbit_encode true) = …`
- `:146` `by rewrite -Hhs; exact: (orbit_encodeK true).`

The *statements* are deck-pair-free, so the file is sound and reusable; only
the header sentence is false, and it is false in the direction that matters
to a reader deciding whether these lemmas transfer to a third deck pair.
This is the exact failure the second-sentence standard is meant to catch: the
kernel cannot see it, and a reader who trusts the header will believe the
file is pair-generic in its evidence as well as in its claims.

**Fix.** Replace the sentence with one that separates statement from proof:

```
(* No statement here names a deck pair. Two proofs below use orbit_encode of *)
(* pgl27_orbit.v as a witness for a fact about the eight positions alone.    *)
```

### T2 (must-fix) — `pgl27_enc_view_mutual_info_ge_one` names the wrong relation

`pgl27_leakage_transport.v:285-288`

```
Lemma pgl27_enc_view_mutual_info_ge_one (k : nat) (C : {set 'I_8}) :
  (forall D : {set 'I_8}, #|D| = k ->
     `I(pgl27_secret R ; pgl27_enc_view R e D) = 1) ->
  (k <= #|C|)%N -> `I(pgl27_secret R ; pgl27_enc_view R e C) = 1.
```

Read against its sibling `pgl27_enc_view_mutual_info_le1` (`:196`), whose
`le1` names the *value*, the suffix `ge_one` reads as "the mutual information
is at least one bit". The conclusion is an equality to 1; the `ge` is about
the *cardinality of the coalition*. A reader who cites this name in a paper
will describe a lower bound that the lemma does not state. The spelling is
also inconsistent with the digit convention used by `le1`, `le3E`, `k4E`.

**Fix.** Put the value in the suffix and the condition last, per
`mainSymbol_suffixes_condition`:

```
Lemma pgl27_enc_view_mutual_info1_card_ge (k : nat) (C : {set 'I_8}) : …
```

and update `:295` (self-reference is not needed) and the header entry at
`:41-42`, which today says "one bit at every coalition of some size k is one
bit at every coalition of at least k positions" — that prose is accurate, so
only the name is wrong.

### T3 (should-fix) — every declaration comment in this file omits the leading name

`pgl27_leakage_transport.v:76`, `:86`, `:96`, `:105`, `:114`, `:123`, `:136`,
`:149`, `:160`, `:175`, `:185`, `:193`, `:202`, `:213`, `:241`, `:254`,
`:267`, `:280` — all eighteen open `(** The …` or `(** Moving …`.

Every other file in the group, and `pgl27_leakage_census.v` itself, opens
with `(** <name> — …`; see `pgl27_encoding.v:99`, `pgl27_encoding_r7.v:59`,
`pgl27_encoding_r5.v:61`, `pgl27_leakage_census.v:212`. The name prefix is
what makes a comment greppable from a citation, and this file is the one a
paper will cite most.

**Fix.** Prefix each with `<name> — `, e.g. `:127` becomes
`(** pgl27_subset_class_harmonicE — the four positions of the harmonic
representative form a quadruple of cross-ratio class false. …`.

### T4 (should-fix) — `pgl27_leak_coalitionE`'s comment is deck-pair-relative, the statement is not

`pgl27_leakage_transport.v:149-154`

```
(** The four heart positions of the identity deal are the positions listed by
    the harmonic representative. …
Lemma pgl27_leak_coalitionE :
  pgl27_leak_coalition = pgl27_code_coalition rep_harmonic.
```

`pgl27_leak_coalition` is `[set i | (val i < 4)%N]`
(`pgl27_secrecy.v:110`), so the statement is a set identity between two
notations for `{0,1,2,3}` and holds at every deck pair. "the identity deal"
is also a term with no referent left in this group: the census pass retired
it, `pgl27_leakage_census.v:212-213` now glosses `code_id` as "the seed the
group table closes from" rather than as the deal of the secret false.

**Fix.** State the identity, then the position:

```
(** pgl27_leak_coalitionE — the coalition witnessing sharpness of the privacy
    threshold is the harmonic four-position representative. The witness
    therefore lies in the cross-ratio class of orbit size 42, so its exact
    leakage is whichever of the two four-position values a deck pair gives
    that class. *)
```

### T5 (should-fix) — `mutual_info_RV_le_entropy` is a generic infotheo fact inside a PGL(2,7) section

`pgl27_leakage_transport.v:187-191`. The statement mentions no PGL(2,7)
object, no deck pair and no coalition; it is `I(S;V) <= H(p_S)` for arbitrary
finite types. It sits inside `Section pgl27_leakage_transport` under
`Variable e : pgl27_encoding`, which it does not use. `lib/proba_entropy_ext.v`
is already imported (`:60`) and carries no such lemma.

**Fix.** Move it to `lib/proba_entropy_ext.v` and drop the `Local`. If it
stays, at minimum hoist it above `Variable e` so the section's parameter list
is honest about which lemmas depend on a deck pair.

### T6 (optional) — section structure hides which results are pair-generic

`Variable e : pgl27_encoding` is declared at `:74`, but `pgl27_card_harmonic`
… `pgl27_card_seven` (`:80`-`:121`), `pgl27_subset_class_harmonicE` (`:127`),
`pgl27_subset_class_equianharmonicE` (`:139`), `pgl27_leak_coalitionE`
(`:153`), `pgl27_secret_entropy` (`:178`) and `mutual_info_RV_le_entropy`
(`:187`) use neither `R`-and-`e` nor `e`. Rocq will not generalize over an
unused section variable, so nothing is wrong in the kernel; the cost is that
a reader cannot see from the structure which half of the file is about the
geometry alone. Splitting into two sections — the geometry-only block before
`Variable e`, the leakage block after — would make T1's distinction
structural rather than a header promise.

---

## `pgl27_encoding.v`

### E1 (should-fix) — `leakage` and `mutual_info` name the same quantity

`pgl27_encoding.v:160` declares `pgl27_enc_view_leakage_le`, whose conclusion
is an inequality between two `` `I(…) `` terms. `pgl27_leakage_transport.v`
names the same quantity `mutual_info` throughout
(`pgl27_enc_view_mutual_info_imset`, `_le1`, `_le3E`, `_k4E` …). One word per
concept, file-wide; here two identifiers for one quantity cross a file
boundary that a reader follows in one direction.

The `_le` suffix is also under-specified: it names the conclusion but not the
condition, which is `C' \subset C`.

**Fix.** `pgl27_enc_view_mutual_info_subset_le`, and update the sole external
user, `pgl27_leakage_r5.v:239`, plus `pgl27_leakage_transport.v:297` and the
header entry at `pgl27_encoding.v:59-60`. Keep the word "leakage" for the
prose; reserve `mutual_info` for identifiers.

### E2 (should-fix) — `enc_code_size` and `enc_code_uniq` have no consumer

`pgl27_encoding.v:102` and `:108`. A repository grep over `*.v` outside
`notes/` and `.claude/` finds no use of either outside this file; their
sibling `enc_code_nthE` (`:118`) is used, at `pgl27_table_bridge.v:191`.

Both are honest facts about the record and either could be claimed in a
paper, but neither is today. `enc_code_uniq` is the nat-level reading of
`enc_deck_ok` and is the natural premise of a census-to-probability step, so
it is the more plausible of the two to keep public.

**Recommendation.** Make `enc_code_size` `Local` (it is one `rewrite` away
from `enc_codeE` and is not a claim a paper would make on its own) and keep
`enc_code_uniq` public as a plausible paper claim. If `enc_code_size` goes
`Local`, drop it from the header list at `:56` and reword that line to cover
`enc_code_uniq` alone.

### E3 (optional) — the header's gloss of `pgl27_enc_view` drops what the view omits

`pgl27_encoding.v:51-52` says "the cards a coalition C sees before the
reveal, under the deck pair e". The declaration comment at `:128-132` is
better: it adds "and ord0 outside C" and says the view refuses to hold the
shuffle. The header entry is where a skimming reader stops.

**Fix.** `pgl27_enc_view R e C == the cards a coalition C sees before the
reveal under the deck pair e, and ord0 elsewhere`.

### E4 (optional) — `@PGL27Encoding` is applied explicitly at both instances

`pgl27_encoding_r7.v:78` and `pgl27_encoding_r5.v:117` both write
`@PGL27Encoding` with all five arguments. With `Set Implicit Arguments`
(`pgl27_encoding.v:79`) the two data fields are inferable from the proof
fields, so the `@` is defensive rather than idiomatic. Either keep it and say
nothing, or add `Arguments PGL27Encoding : clear implicits.` after the record
so the plain application reads cleanly at both instances. Low value; listed
only for completeness.

---

## `pgl27_encoding_r7.v`

### R7-1 (must-fix) — the header promises a ratio for every representative; four of six exist

`pgl27_encoding_r7.v:44-45`

```
(*   pgl27_r7_collision_ratio_* == the identities (336 - m) * q = p * 336     *)
(*     giving the non-collision fraction of each representative as a rational *)
```

The file defines four ratio lemmas: `_harmonic` (`:218`), `_equianharmonic`
(`:226`), `_five` (`:234`), `_six` (`:242`). The census table at `:24-29`
lists six representatives; there is no ratio at three positions and none at
seven.

**Fix.** Say which four, and why the other two are absent:

```
(*   pgl27_r7_collision_ratio_* == the identities (336 - m) * q = p * 336     *)
(*     giving the non-collision fraction of the two four-position            *)
(*     representatives and of the five- and six-position ones; at three       *)
(*     positions the fraction is 0 and at seven it is 1                       *)
```

### R7-2 (should-fix) — the `_neq` family carries two different claims under one suffix

Within this one file:

- `pgl27_r7_collisions_harmonic_neq` (`:185`) is `!= 97`, a separation from a
  neighbouring value.
- `pgl27_r7_collisions_five_neq` (`:200`) is `!= 35`, also a neighbour.
- `pgl27_r7_collisions_equianharmonic_neq` (`:193`) is `!= 96`, a separation
  from the *other class's* count.
- `pgl27_r7_collisions_six_neq` (`:207`) is `!= 0`, a positivity claim.

Four different propositions share one suffix, and the same names recur in
`pgl27_encoding_r5.v` meaning different things again (see R5-2). A reader who
knows `pgl27_r7_collisions_six_neq` cannot guess what
`pgl27_r5_collisions_harmonic_neq` says.

**Fix.** Name the claim, not the connective:

- `_harmonic_neq` → `pgl27_r7_collisions_harmonic_neq97`
- `_five_neq` → `pgl27_r7_collisions_five_neq35`
- `_equianharmonic_neq` → `pgl27_r7_collisions_equianharmonic_neq_harmonic`
- `_six_neq` → `pgl27_r7_collisions_six_neq0` (or state `0 < …` and name it
  `pgl27_r7_collisions_six_gt0`, which is the mathcomp form and reads better
  in the recovery-threshold argument)

None of the four has an external consumer, so the rename is local to this
file.

### R7-3 (should-fix) — header lines 18-19 are development history, not mathematics

`pgl27_encoding_r7.v:18-19`

```
(* This is the pair the development started from, orbit_encode of            *)
(* pgl27_orbit.v, and the pair the earlier leakage results were stated at.   *)
```

"the pair the development started from" and "the earlier leakage results were
stated at" are progress narration. The test applies: after the files are
reorganized and the proofs redone, neither clause is worth saying. The
declaration comment at `:73-76` already carries the surviving content ("Its
decks are the orbit encoder of pgl27_orbit.v, so every leakage value proved
at this encoding is a value of the scheme the rest of the development
executes"), stated positionally.

**Fix.** Replace with the position:

```
(* Its decks are orbit_encode of pgl27_orbit.v, so this is the pair the      *)
(* scheme of pgl27_scheme.v executes and the pair whose leakage values are   *)
(* values of that scheme rather than of a variant.                           *)
```

### R7-4 (should-fix) — the ratio comments state a division the statements do not contain

`pgl27_encoding_r7.v:215`, `:223`, `:231`, `:239` each open with a rational
equation, e.g. `(336 - 96) / 336 = 5 / 7`, while the statement below is the
cross-multiplied nat identity `((336 - …) * 7)%N = (5 * 336)%N`. Nothing in
the statement is a division and nothing is a rational; `%N` subtraction is
truncating. The header at `:44` is type-honest about this and the declaration
comments are not. Same at `pgl27_encoding_r5.v:239` and `:247`.

**Fix.** Lead with the identity and gloss the fraction second:
`(** pgl27_r7_collision_ratio_harmonic — the identity (336 - 96) * 7 = 5 *
336, i.e. a non-collision fraction of five sevenths. Five sevenths of the
shuffles leave a harmonic four-position coalition able to tell the two decks
apart. *)`

### R7-5 (optional) — header content check: passes

`:8-9` lists both decks by position, `:11-13` names cards 0-3 as the hearts
and gives the heart positions `{0,1,2,3}` and `{0,1,2,4}`, `:21-29` gives all
six census numbers, `:31-33` gives the recovery threshold seven and says what
it means for a coalition. All five mandatory items are present.

### R7-6 (optional) — the three-position results duplicate a route already closed

`pgl27_r7_views_uniq_three` (`:130`) and `pgl27_r7_collisions_three` (`:177`)
have no consumer, and the zero leakage they support is already proved from
sharp 3-transitivity by `pgl27_enc_view_mutual_info_le3E`
(`pgl27_leakage_transport.v:205`). The comment at `:126-129` says as much.

**Recommendation.** Keep `pgl27_r7_collisions_three` — "every one of the 336
shuffles leaves three positions unable to tell the decks apart" is the count
form of the privacy threshold and is a plausible paper claim. Make
`pgl27_r7_views_uniq_three` `Local`; it feeds nothing and the intersection it
would license is the whole of the table. Same recommendation for the `_r5`
pair of these.

---

## `pgl27_encoding_r5.v`

### R5-1 (must-fix) — the header promises a ratio for every representative; two of six exist

`pgl27_encoding_r5.v:46-47` carries the same sentence as R7-1, but this file
defines only `pgl27_r5_collision_ratio_harmonic` (`:242`) and
`_equianharmonic` (`:251`). The census table at `:22-27` lists six
representatives. The over-claim is larger here than in `_r7` and it lands on
the more interesting pair, because the whole point of `_r5` is what happens
at and above five positions, where there is no ratio lemma at all.

**Fix.**

```
(*   pgl27_r5_collision_ratio_* == the identities (336 - m) * q = p * 336     *)
(*     giving the non-collision fraction of the two four-position            *)
(*     representatives, the only sizes of this pair at which the fraction is  *)
(*     neither 0 nor 1                                                        *)
```

### R5-2 (should-fix) — the `_neq` names mean something different here than in `_r7`

- `pgl27_r5_collisions_harmonic_neq` (`:224`) is `!= 72`: a separation from
  the *other class*. In `_r7` the identically-shaped name
  `pgl27_r7_collisions_harmonic_neq` is `!= 97`, a neighbour separation.
- `pgl27_r5_collisions_equianharmonic_neq` (`:231`) is `!= 0`: a positivity
  claim. In `_r7` the identically-shaped name is `!= 96`, a class separation.

The two files are read side by side — `pgl27_encoding_r5.v:14`, `:30`,
`:180-181`, `:188-189` and `:250` all compare against `_r7` explicitly — so
the collision of names is worse than it would be in isolation.

**Fix.** `pgl27_r5_collisions_harmonic_neq_equianharmonic` and
`pgl27_r5_collisions_equianharmonic_gt0` (stating `0 < …`), matching the
renames proposed in R7-2. Neither has an external consumer.

### R5-3 (should-fix) — `pgl27_r5_views_uniq_six` and `_seven` support nothing

`:152` and `:160`. Their stated purpose, repeated from the harmonic case, is
"The collision count below is a set-intersection cardinality". But
`pgl27_r5_collisions_six` (`:203`) and `_seven` (`:209`) are both `0`, and an
empty intersection needs no repetition-freeness. Neither lemma has a consumer
(`pgl27_leakage_r5.v` uses only the harmonic, equianharmonic and five
variants), and neither is a claim a paper would make.

**Recommendation.** Delete both, or make them `Local` if the symmetry with
`pgl27_encoding_r7.v` is wanted for a future third pair. If they stay, their
comments must stop asserting a purpose they do not serve — the honest second
sentence is that the census route is uniform in the reveal size, not that the
count below needs them.

### R5-4 (optional) — `pgl27_r5_collisions_six` and `_seven` are implied by `_five`

`rep_five` ⊂ `rep_six` ⊂ `rep_seven` as literal lists
(`pgl27_leakage_census.v:314`, `:318`, `:323`), and a collision at a larger
reveal set restricts to a collision at a smaller one, so
`pgl27_r5_collisions_five = 0` forces both. Each is one cheap `vm_compute`,
and the census table in the header prints all six rows, which a paper would
quote as a table.

**Recommendation.** Keep both as paper claims. Worth one source comment
(`(* … *)`, not the statement comment) recording that they are derivable from
the five-position count, so a later reader does not take the three vanishing
counts as three independent computations.

### R5-5 (should-fix) — `pgl27_r5_hearts` is the file's real content and is under-placed

`:87`. It is the only lemma in either instance file that says *why* the two
deck pairs are comparable, it is listed first under Key results (`:40-41`),
and its comment at `:83-86` is the best in the group. It has no consumer
outside its own file (used at `:101` inside `pgl27_r5_classK`).

**Recommendation.** Keep public — this is a paper claim, not plumbing. No fix
needed; recorded here so it is not swept up by a later unused-declaration
pass.

### R5-6 (optional) — the field-obligation lemmas are public but are plumbing

`pgl27_r5_deck_ok` (`:80`), `pgl27_r5_classK` (`:99`), `pgl27_r5_codeE`
(`:108`), and `pgl27_r7_codeE` (`pgl27_encoding_r7.v:69`) exist only to be
passed to the constructor, and each is reachable afterwards as
`enc_deck_ok pgl27_encoding_r5` and so on. None has an external consumer.

**Recommendation.** `pgl27_r5_classK` is correctness of the scheme at this
pair and is a plausible paper claim — keep it public. Make the three `codeE`
and `deck_ok` obligations `Local`; they are representation bookkeeping and
the record accessor is the API. Note that `pgl27_r5_classK`'s comment
(`:94-98`) already explains the one genuinely interesting thing here, that it
holds by transport from `_r7` rather than by computation.

### R5-7 (optional) — header content check: passes, with one gap

`:8-9` both decks, `:11-13` hearts and heart positions, `:19-27` all six
census numbers, `:29-32` the recovery threshold five and the comparison with
seven. All five mandatory items present.

The gap is at `:31-32`: "The leakage of this pair rises from zero at three
positions to one full bit at five, with a single intermediate size." True, but
it hides that the single intermediate size carries *two* values, 48 and 72
collisions on the two cross-ratio classes, which is the one place this pair
is more interesting than a plain threshold. Suggested addition: "At that one
intermediate size the two cross-ratio classes leak different amounts, 48
collisions on the harmonic class against 72 on the equianharmonic."

---

## `pgl27_leakage_census.v` (changed hunks only)

### C1 (should-fix) — three names for one object across the group

The census pass introduced `deal` as the name of the code-table parameter:

- `:21` "A deck pair enters here as its deal table, the map from the secret
  bit to the eight card codes in position order."
- `:404` `Definition code_views (deal : bool -> seq nat) (b : bool) …`
- `:413` `Definition pgl27_collisions (deal : bool -> seq nat) (S : seq nat)`
- header `:37` and `:39`, `code_views deal b S` and `pgl27_collisions deal S`

The same object is the record field `enc_code` in `pgl27_encoding.v:93`, is
called "the code table of a deck" there (`:99`, `:106`, `:115`), and is
`code_deal_r7` / `code_deal_r5` in the instances, glossed as "nat code
tables" (`pgl27_encoding_r7.v:36`, `pgl27_encoding_r5.v:36`). So one object
carries "deal table", "code table" and "nat code table", and the identifiers
carry `deal`, `enc_code` and `code_deal_*`.

**Fix.** Pick "code table" — it is the term `pgl27_encoding.v` already uses
throughout and it names what the object is rather than what produced it.
Rename the census parameter `deal` to `code` at `:404` and `:413`, update the
header at `:21`, `:37` and `:39`, and consider renaming `code_deal_r7` /
`code_deal_r5` to `code_table_r7` / `code_table_r5` for a clean sweep. The
instance rename touches only the two instance files.

### C2 (optional) — `code_tau` was removed cleanly

`code_tau` no longer appears anywhere in the repository outside `notes/`; the
deletion left no dangling reference, and `code_gens`
(`:218`) never used it. The `code_id` comment was correctly retargeted from
"the deal of the secret false" to "the seed the group table closes from"
(`:212-213`), which is right now that the deal is a parameter. No action.

### C3 (optional) — the census header's Key results list lost four families and gained none

The diff dropped `pgl27_collisions_*` and
`pgl27_collision_ratio_harmonic` from the header list (old `:43-45`), which
is correct since those moved to the instance files. What is now absent is any
pointer from the census header to where a reader finds a concrete count.
`:26` does name the two instance files in the Collisions paragraph, so this is
covered; recorded only to confirm the removal was deliberate and complete.

---

## Checks that found nothing

- **Line length.** No line over 80 columns in any of the five files.
- **Banned vocabulary.** `apex`, `gate`/`gated`/`gating`/`gates`,
  `posit`/`posited`/`positing` do not occur. Metaphor words for results
  (`ramp`, `beats`, `escape`, `smash`, `dodge`, `cap` as a noun) do not
  occur. "rises" at `pgl27_encoding_r5.v:31` is a plain description of a
  monotone sequence of values, not a metaphor for a result.
- **Meta and status markers.** No `key lemma`, `headline`, `important`,
  `TODO`, `deferred`, `reused as-is`, `fully machine-checked`, no plan or
  task ids, no absolute line numbers, no `Kind:` / `Why:` / `Used by:`
  template slots in any declaration comment. `Key results:` appears as a
  file-header section label in all four headers, matching
  `pgl27_leakage_census.v` and the rest of the instance directory; that is
  the repo's header format and is not a declaration comment.
- **Proof idiom.** Every proof is ssreflect: `move=>`, `exact:`, `apply/`,
  `rewrite`, `case:`, `have`. No `pose proof`, no `f_equal`, no bare `auto`,
  no `assert`. No bullets are used and none are needed; the one branching
  proof, `pgl27_enc_view_mutual_info_k4E`
  (`pgl27_leakage_transport.v:226-239`), uses `case H : … ` with the
  indented-first-branch style that mathcomp prefers over bullets at depth
  one. No redundant tactic after the goal closes.
- **`Local` discipline.** `pgl27_card_harmonic` … `pgl27_card_seven` and
  `mutual_info_RV_le_entropy` are correctly `Local`
  (`pgl27_leakage_transport.v:80`-`:187`). `Local Open Scope` is used rather
  than bare `Open Scope` in all five files.
- **Cross-ratio class orientation.** Verified against
  `pgl27_leakage_census.v:304-310` (`rep_harmonic = {0,1,2,3}`,
  `rep_equianharmonic = {0,1,2,4}`), `:345` and `:351` (orbit sizes 42 and
  28), and `pgl27_leakage_transport.v:127`/`:139`
  (`subset_class … rep_harmonic = false`, `… rep_equianharmonic = true`).
  Every comment in the group that names a class names the right one. In
  particular `pgl27_encoding_r5.v:247-250` correctly reports that at `_r5`
  the equianharmonic class has the smaller non-collision fraction (11/14
  against 6/7) and that this reverses the `_r7` ordering (5/7 against 11/14).
- **Arithmetic in comments.** All census and ratio numbers check:
  `_r7` 336-96=240, 240*7=1680=5*336; 336-72=264, 264*14=3696=11*336;
  336-36=300, 300*28=8400=25*336; 336-12=324, 324*28=9072=27*336.
  `_r5` 336-48=288, 288*7=2016=6*336; 336-72=264, 264*14=3696=11*336.
- **Vacuous or over-strong premises.** None found.
  `pgl27_enc_view_mutual_info_k4E` takes both four-position values as
  premises and needs both (one per branch of `subset_class C`).
  `pgl27_enc_view_mutual_info_ge_one` needs its `forall D, #|D| = k` premise
  at the witness `D` only, but the coalition `D` is constructed inside the
  proof (`:291-294`) and is not available to the caller, so the universally
  quantified form is the right interface.
  `pgl27_enc_view_leakage_le`'s `C' \subset C` is used.
  `pgl27_enc_view_indep`'s `#|C| <= 3` is used.
- **Generic lemmas secretly depending on `_r7`.** Only the proof-level
  dependence recorded in T1. No lemma in `pgl27_encoding.v` or
  `pgl27_leakage_transport.v` has `orbit_encode`, `code_deal_r7` or
  `pgl27_encoding_r7` in its *statement*.

---

## Deletion / `Local` candidate summary

| Declaration | External uses | Recommendation | Paper claim? |
|---|---|---|---|
| `enc_code_size` (`pgl27_encoding.v:102`) | 0 | `Local` | no |
| `enc_code_uniq` (`pgl27_encoding.v:108`) | 0 | keep public | yes |
| `enc_code_nthE` (`pgl27_encoding.v:118`) | `pgl27_table_bridge.v:191` | keep | yes |
| `pgl27_r7_codeE` (`_r7.v:69`) | 0 | `Local` | no |
| `pgl27_r5_codeE` (`_r5.v:108`) | 0 | `Local` | no |
| `pgl27_r5_deck_ok` (`_r5.v:80`) | 0 | `Local` | no |
| `pgl27_r5_classK` (`_r5.v:99`) | 0 | keep public | yes |
| `pgl27_r5_hearts` (`_r5.v:87`) | 0 | keep public | yes |
| `pgl27_r7_views_uniq_three` (`_r7.v:130`) | 0 | `Local` or delete | no |
| `pgl27_r5_views_uniq_three` (`_r5.v:169`) | 0 | `Local` or delete | no |
| `pgl27_r5_views_uniq_six` (`_r5.v:152`) | 0 | delete | no |
| `pgl27_r5_views_uniq_seven` (`_r5.v:160`) | 0 | delete | no |
| `pgl27_r7_collisions_three` (`_r7.v:177`) | 0 | keep public | yes |
| `pgl27_r5_collisions_three` (`_r5.v:216`) | 0 | keep public | yes |
| `pgl27_r5_collisions_six`, `_seven` (`_r5.v:203`, `:209`) | 0 | keep, note derivability | yes (table row) |
| `pgl27_r7_collisions_*_neq` ×4 (`_r7.v:185`-`:207`) | 0 | keep, rename per R7-2 | 2 of 4 |
| `pgl27_r5_collisions_*_neq` ×2 (`_r5.v:224`, `:231`) | 0 | keep, rename per R5-2 | yes |
| `pgl27_r7_collision_ratio_*` ×4 | 0 | keep public | yes |
| `pgl27_r5_collision_ratio_*` ×2 | 0 | keep public | yes |

"External uses" counts uses outside the declaring file, over `*.v` in the
repository excluding `notes/` and `.claude/`.

## Fix order

1. T1, R7-1, R5-1 — three header sentences that assert what the files do not
   deliver. Comment-only, no proof touched.
2. T2 — rename `pgl27_enc_view_mutual_info_ge_one`. One call site.
3. R7-2, R5-2 — rename the eight `_neq` lemmas. No external call sites.
4. E1 — rename `pgl27_enc_view_leakage_le`. Two call sites
   (`pgl27_leakage_r5.v:239`, `pgl27_leakage_transport.v:297`).
5. T3, T4, R7-3, R7-4 — comment rewrites.
6. C1 — the `deal` / `code table` sweep, largest mechanical change, no proof
   content.
7. E2, R5-3, R5-6, R7-6 — the `Local` and deletion pass.
8. T5, T6 — relocating the generic entropy lemma and splitting the section.
