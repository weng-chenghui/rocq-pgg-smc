# Style and statement audit, group B

Date: 2026-09-18
Branch: `feat/pgl27-encoding-parameter`
Range audited: `git diff 20da27e..a386865` plus the three file headers.
Files: `instances/pgl27/pgl27_table_bridge.v`, `instances/pgl27/pgl27_view_census.v`,
`instances/pgl27/pgl27_mutual_info.v`.
Unchanged parts are out of scope (rulings in
`notes/probes/2026-09-17-pgl27-leakage-ramp/style-audit-rulings-{A,B,C}.md`).
Read-only: no source edited, no build run.

## Verdict

**PASS-WITH-FIXES.**

One must-fix, six should-fix, five optional. Nothing is mathematically wrong.
The generalisation itself is clean: argument order, implicit status, premise
economy and the absence of residual `_r7` dependence all check out. The defects
are in the comment layer and in two declarations the pass carried forward
without a user.

| # | File | Severity | One line |
|---|---|---|---|
| A1 | view_census | must-fix | two comments still say "deal" / "deal tables" for a thing that no longer exists, and contradict this file's own updated header |
| A2 | view_census | should-fix | `pgl27_view_outside`, `pgl27_view_codesE` public and advertised, used nowhere outside the file |
| A3 | view_census | should-fix | header names only one of the two premises the generic lemmas take |
| A4 | view_census | optional | `pgg_reconstruct` import breaks the `pgg_smc` block |
| A5 | view_census | optional | proofs unfold `coalition_view` across a module boundary |
| B1 | table_bridge | should-fix | `pgl27_code_comp_rowE` has no user anywhere, and is re-advertised as a Key result |
| B2 | table_bridge | should-fix | "the code table of a deck pair" is not a thing; the lemma takes one deck's table |
| B3 | table_bridge | optional | header sentence is about file layout, joined by a semicolon |
| C1 | mutual_info | should-fix | scope statement does not say why a per-pair result misses the all-decks dealer |
| C2 | mutual_info | should-fix | `pgl27_ambiguous_viewsE` comment narrates proof architecture |
| C3 | mutual_info | optional | `pgl27_reachable_view_entropy_ambiguousE` public, used only in its own file |
| C4 | mutual_info | optional | "the view of S" where S is a list of positions |

---

## A. `instances/pgl27/pgl27_view_census.v`

### A1 (must-fix) Stale `deal` vocabulary, contradicting this file's own header

Two declaration comments still name the old fixed-pair carrier.

`pgl27_view_census.v:140-141`

```
(** A repetition-free census view list makes the restricted composite of a
    census row with one deal injective on the census rows. *)
```

`pgl27_view_census.v:156-157`

```
(** Reading the listed coordinates of a protocol view gives the same sequence
    as restricting the corresponding permutation and deal tables. It
    identifies the masked view with the restricted census row. *)
```

The code under both is now `enc_code e b`, the code table of one deck of the
pair (`:144`, `:147`, `:164`). `code_deal` no longer exists anywhere:
`grep -rn --include='*.v' --exclude-dir=notes --exclude-dir=.claude -w code_deal .`
returns 0 hits. Worse, the header entry for the very lemma at `:158` was
updated in this same commit and now says the opposite thing:

`pgl27_view_census.v:30-31`

```
(*   pgl27_view_codesE == the listed coordinates of a protocol view are the   *)
(*     restricted composite of the shuffle table and the deck's code table    *)
```

So the file states two different vocabularies for one lemma, one of which
names a deleted definition. This is the stale-text class.

Fix, `:140-141`:

```
(** A repetition-free census view list makes the restricted composite of a
    census row with one deck's code table injective on the census rows. *)
```

Fix, `:156-157`:

```
(** Reading the listed coordinates of a protocol view gives the same sequence
    as restricting the composite of the shuffle table and that deck's code
    table. It identifies the masked view with the restricted census row. *)
```

### A2 (should-fix) Two public, advertised lemmas with no external user

`pgl27_view_outside` (`:115`) and `pgl27_view_codesE` (`:158`) both took the
new `e` in this diff, so they are in scope. Both are `Lemma`, not
`Local Lemma`, and both are listed under Key results (`:29`, `:30-31`). Neither
is referenced outside `pgl27_view_census.v`:

```
grep -rn --include='*.v' --exclude-dir=notes --exclude-dir=.claude \
  -w pgl27_view_outside .    # only pgl27_view_census.v
grep -rn --include='*.v' --exclude-dir=notes --exclude-dir=.claude \
  -w pgl27_view_codesE .     # only pgl27_view_census.v
```

Internal uses are `:237`, `:273` and `:189`, `:190`, `:223`, `:242`, `:279`
respectively. Under the keep-only-claimed-or-premise rule these are file-local
machinery.

Fix: `Local Lemma pgl27_view_outside ...`, `Local Lemma pgl27_view_codesE ...`,
and delete header lines `:29-31`. Keep `pgl27_view_codesE` public only if a
paper names it as the nat-to-protocol bridge; in that case say so in the header
rather than leaving it as an unexplained export.

Same class but out of this diff's scope, listed for the record:
`pgl27_masked_view_eq` (`:94`, header `:27-28`) and `pgl27_view_codes` (`:74`,
header `:21-22`) are also public with no external user, and were not touched by
this commit.

### A3 (should-fix) Header names one of two premises

`pgl27_view_census.v:14-15`

```
(* Both facts take the repetition-freeness of the census view lists of the    *)
(* deck pair as a premise.                                                    *)
```

Both facts also take `all (fun x => (x < 8)%N) S`, the condition that `S` names
card positions: `pgl27_conditional_view_inj` at `:182`, and
`pgl27_ambiguous_probabilityE` at `:674`. A reader checking the generic lemmas
against the header will not expect the second premise, and it is exactly the
premise an instance file has to discharge by `vm_compute`.

Fix:

```
(* Both facts take two premises: that S lists card positions below eight, and *)
(* that the census view lists of the deck pair are repetition-free. Which     *)
(* reveal sets satisfy the second, and what the collision count is there, are *)
(* facts of the deck pair and are established in pgl27_encoding_r7.v and      *)
(* pgl27_encoding_r5.v.                                                       *)
```

### A4 (optional) Import block

`pgl27_view_census.v:47-51`

```
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import transitivity_privacy.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_secrecy.
```

Every sibling keeps the `pgg_reconstruct` requires contiguous and after the
`pgg_smc` interface line: `pgl27_encoding.v:75-76`, `pgl27_leakage_r7.v:72-74`,
`pgl27_leakage_r5.v:59-61`, `pgl27_profile_privacy.v:58-59`.

Fix: move `:48` to sit after `:51`, or below the whole `pgg_smc` block.

### A5 (optional) Proofs unfold `coalition_view` across a module boundary

`pgl27_view_census.v:120` and `:169`

```
move=> Hi; rewrite /pgl27_enc_view /coalition_view ffunE.
rewrite /pgl27_enc_view /coalition_view ffunE /pgl27_code_coalition inE.
```

`coalition_view` is defined at `reconstruct/transitivity_privacy.v:493` and has
no equation lemma, so these two proofs depend on its definitional shape. This is
also the only reason `pgl27_view_census.v` requires `transitivity_privacy` at
all (A4). There is precedent (`pgl27_profile_privacy.v:236,240`), so this is not
new, but the generalisation is the natural moment to close it.

Fix: add next to `pgl27_enc_view` (`pgl27_encoding.v:133-136`)

```coq
(** The card a coalition sees at one position: the dealt card when the
    position is the coalition's own, and ord0 otherwise. It is the only
    equation a consumer needs, so no file below has to unfold coalition_view. *)
Lemma pgl27_enc_viewE (R : realType) (e : pgl27_encoding) (C : {set 'I_8})
    (u : bool * pgg_gT pgl27_M) (i : 'I_8) :
  pgl27_enc_view R e C u i =
  if i \in C then tnth (enc_deck e u.1) (@pgg_rho pgl27_M u.2 i) else ord0.
Proof. by rewrite /pgl27_enc_view /coalition_view ffunE. Qed.
```

then `rewrite pgl27_enc_viewE` at `:120` and `:169`, and drop the import at
`:48`.

---

## B. `instances/pgl27/pgl27_table_bridge.v`

### B1 (should-fix) `pgl27_code_comp_rowE` has no user

`pgl27_table_bridge.v:194-205`

```coq
(** An indexed census row and its assigned shuffle deal the same card at every
    position. Restricted census views can therefore be compared with the
    protocol's coalition view coordinate by coordinate, at every deck pair. *)
Lemma pgl27_code_comp_rowE (e : pgl27_encoding) (b : bool) (k : 'I_336)
    (i : 'I_8) :
```

Occurrences in the whole tree, excluding `notes/` and `.claude/`: the
declaration at `:197` and the header entry at `:27-28`. Nothing applies it.
`pgl27_view_census.v:174` uses the general `pgl27_code_comp_ptblE` instead.

It was already dead before this commit:
`git grep -n pgl27_code_comp_rowE 20da27e -- instances/` returns only
`:25` (header) and `:202` (declaration). So the generalisation pass gave a dead
lemma a new parameter and re-advertised it under Key results.

Fix: delete `:194-205` and header `:27-28`. If the paper's census-to-group
bridge narrative claims the indexed form, make it `Local Lemma` and still drop
the header entry. Deleting it has a second payoff: it makes the header's own
claim at `:12-14` exactly true, since `pgl27_code_comp_ptblE` would then be the
only lemma in the file that mentions a deck pair.

### B2 (should-fix) "the code table of a deck pair"

`pgl27_table_bridge.v:10-11`

```
(* element occurs as a row, and composing a row with the code table of a deck *)
(* pair reproduces the dealt deck the protocol view reads. Every census count *)
```

`pgl27_code_comp_ptblE` (`:182-186`) composes with `enc_code e b`: the code
table of the single deck that secret `b` is dealt, not of the pair. A pair has
two code tables and the lemma is about one of them, selected by the secret.
Type-honest phrasing matters here because the whole point of the commit is that
`e` carries two decks.

Fix, `:10-11`:

```
(* element occurs as a row, and composing a row with the code table of the    *)
(* deck a secret is dealt reproduces the arrangement the protocol view reads. *)
```

### B3 (optional) Header sentence is about file layout

`pgl27_table_bridge.v:12-14`

```
(* is therefore a count over the shuffle group itself. The identification of  *)
(* the rows with the group is fixed by the geometry; only the last step       *)
(* mentions a deck pair, and it holds at every deck pair.                     *)
```

"only the last step" is a statement about where things sit in the file, and it
is false as written: two lemmas mention the deck pair today (`:182`, `:197`).
After B1 it would be one.

Fix:

```
(* is therefore a count over the shuffle group itself. The identification of  *)
(* the rows with the group is fixed by the geometry. The deck pair enters     *)
(* only in the composition step, which holds at every deck pair.              *)
```

---

## C. `instances/pgl27/pgl27_mutual_info.v`

### C1 (should-fix) Scope statement conflates two dealer models

`pgl27_mutual_info.v:17` and `:35-37`

```
(* Everything here holds at every deck pair. The collision counts that turn   *)
...
(* The statements concern the pre-reveal execution: after the public reveal   *)
(* every player learns the secret by design. The all-decks dealer of          *)
(* pgl27_view_indep_alldecks is not covered.                                  *)
```

Both sentences are true and the dealer model is the right one: every statement
fixes one `e` and is universally quantified over `e`, and the all-decks dealer
of `pgl27_secrecy.v:215` is genuinely untreated. What is missing is the reason
the two differ. A reader who has just read "holds at every deck pair" can
reasonably conclude that the all-decks case follows by instantiation. It does
not: the all-decks dealer draws a deck inside the execution, so the coalition's
posterior is averaged over decks, and a per-pair equality gives no bound on the
average of the mutual informations.

Fix, replacing `:35-37`:

```
(* The statements concern the pre-reveal execution: after the public reveal   *)
(* every player learns the secret by design. Each statement fixes one deck    *)
(* pair and is universally quantified over pairs. The dealer of               *)
(* pgl27_view_indep_alldecks draws a deck inside the execution, so it         *)
(* averages the coalition's posterior over decks; that is a different dealer  *)
(* and is not covered here.                                                   *)
```

### C2 (should-fix) `pgl27_ambiguous_viewsE` narrates proof architecture

`pgl27_mutual_info.v:79-82`

```
(** The ambiguous views of a coalition are the views the generic posterior
    theory calls ambiguous for the pair of per-secret view maps. It is the
    step that lets the support-posterior results of support_posterior.v speak
    about this scheme. *)
```

The second sentence is about which file talks to which, and it stops being true
the moment the proofs are reorganized. It fails the position-versus-meta test.
The first sentence is also weaker than it could be: it says the set matches a
generic definition but never says what ambiguity means for a coalition.

Fix:

```
(** The ambiguous views of a coalition are exactly the views the generic
    posterior theory calls ambiguous for the pair of per-secret view maps. A
    view is ambiguous when both secrets can produce it, so the ambiguous set
    is the event on which a coalition's pre-reveal view leaves the orbit
    secret undetermined. *)
```

Keep the pointer to `support_posterior.v` as a non-rendered `(* ... *)` comment
inside the proof if it is wanted.

### C3 (optional) `pgl27_reachable_view_entropy_ambiguousE` has no external user

`:99`, advertised at `:29-30`, applied only at `:155` inside the same file.
Same class as A2. Unlike A2 this one reads as a genuine API lemma, the entropy
half of the leakage argument, so keep it public if a paper cites it. Otherwise
`Local` plus removing `:29-30`.

### C4 (optional) "the view of S"

`pgl27_mutual_info.v:58-59`

```
(** The proportion of shuffles whose view of S under one secret is not also a
    view of S under the other, at the deck pair e. ...
```

`S : seq nat` is a list of card positions, so a view is taken *at* the positions
listed by `S`, which is the phrasing `pgl27_view_census.v:70` already uses. One
word per concept, file-wide.

Fix: "The proportion of shuffles whose view at the positions listed by S under
one secret is not also such a view under the other, at the deck pair e."

---

## Checks that passed, with evidence

**1. Argument order of the new `e`.** Uniform, no exception. Carrier first,
deck pair second, reveal set third, matching `pgl27_enc_view R e C`
(`pgl27_encoding.v:133`):

- `pgl27_ambiguous_views R e S` (view_census `:82`)
- `pgl27_view_outside R e S u i` (`:115`)
- `pgl27_view_codesE R e S b g` (`:158`)
- `pgl27_conditional_view_inj R e S b` (`:180`)
- `pgl27_ambiguous_probabilityE R e S` (`:672`)
- `pgl27_noncollision_ratio R e S` (mutual_info `:63`)
- `pgl27_reachable_view_entropy_ambiguousE R e S Hinj v` (`:99`)
- `pgl27_view_mutual_info_ambiguityE R e S` (`:135`)

Nat-level helpers, which need no carrier, put `e` first:
`pgl27_code_comp_ptblE e b g t Ht i` (table_bridge `:182`),
`pgl27_code_comp_rowE e b k i` (`:197`), `pgl27_code_views_inj e S b`
(view_census `:142`), `pgl27_code_ambiguous e S u` (`:250`),
`pgl27_code_view_row e S b k` (`:457`),
`card_pgl27_code_ambiguous_false e S` (`:521`).

**2. Implicit status.** Nothing is declared by hand; it falls out of
`Set Implicit Arguments` / `Unset Strict Implicit` (view_census `:53-54`), so
`e` is implicit exactly where it occurs in a premise type
(`pgl27_conditional_view_inj`, `pgl27_ambiguous_probabilityE`,
`pgl27_view_mutual_info_ambiguityE`) and explicit otherwise
(`pgl27_view_codesE`, `card_pgl27_ambiguous_samples`,
`pgl27_noncollision_ratio`). Call sites match: `mutual_info.v:152` passes only
`R` then the three premises, `:149-150` and `:155` use `@` with `R e S`. This is
standard MathComp behaviour under these flags and needs no change. If a stable
`e` position across the public API is wanted, an explicit `Arguments` block is
the only way to get it, since the flags derive it per declaration.

**3. Line length and formatting.** No line exceeds 80 columns in any of the
three files. Every header banner line in the first 40 lines is exactly 80 with
`*)` aligned. No trailing whitespace introduced by the diff.

**4. Banned words.** No `apex`, `gate`/`gated`/`gating`, `posit`/`posited`/
`positing` in any of the three files. No metaphor words for results: no `ramp`,
`beats`, `escape`, `smash`, `dodge`, no `cap` as a noun.

**5. Stale identifiers.** `orbit_encode`, `code_deal`, `code_tau` do not occur
in the three files. `code_deal` is gone from the tree entirely (0 hits over
`*.v` excluding `notes/` and `.claude/`). `orbit_encode` survives only where the
fixed-pair layer is still live (`pgl27_secrecy.v`, `pgl27_recovery.v`,
`pgl27_models.v`), not here. No reference to `pgl27_leakage_ramp.v`. The deleted
names (`pgl27_conditional_view_inj_harmonic`, `pgl27_ambiguous_probability_*E`,
`pgl27_view_mutual_info_harmonicE`, `pgl27_code_deal_orbit_encodeE`) occur
nowhere. `pgl27_views_uniq_*` and `pgl27_collisions_{harmonic,five,seven}` are
gone tree-wide, so nothing was orphaned in `pgl27_leakage_census.v` either. The
numbers 96/72/36/12 and the words harmonic, equianharmonic, `rep_five`,
`rep_six`, `rep_seven` do not occur in the three files.

**6. Cross-file pointers in the headers resolve.** `pgl27_encoding_r7.v` and
`pgl27_encoding_r5.v` exist and do hold what the headers claim: the uniqueness
facts (`pgl27_r7_views_uniq_*` at `:89-130`, `pgl27_r5_views_uniq_*` at
`:128-169`) and the collision counts (`pgl27_r7_collisions_*` at `:142-177`,
`pgl27_r5_collisions_*` at `:182-216`). `pgl27_leakage_r7.v` and
`pgl27_leakage_r5.v` exist and hold the closed forms (`pgl27_leakage_r7.v:275`,
`:296`, `pgl27_leakage_r5.v:89-147`). `pgl27_view_indep_alldecks` exists
(`pgl27_secrecy.v:215`).

**7. Premise economy.** `pgl27_conditional_view_inj` (`:180-183`) takes
`all (fun x => (x < 8)%N) S` and only the single list
`uniq (code_views (enc_code e) b S)`, not both: tight.
`pgl27_ambiguous_probabilityE` (`:672-676`) and
`pgl27_view_mutual_info_ambiguityE` (mutual_info `:135-139`) take both lists,
and both are consumed (`:149-150` for the two injectivity instances, `:152` for
the probability). `card_pgl27_code_ambiguous_true` (`:554`) correctly takes no
uniqueness premise while `card_pgl27_code_ambiguous_false` (`:521`) takes both;
the asymmetry is real and comes from `count_mem_sym` (`:442`). No dead premise
found.

**8. No residual `_r7` dependence.** None of the three files imports an instance
file; the imports are `pgl27_encoding` plus pair-independent modules
(table_bridge `:36-39`, view_census `:47-51`, mutual_info `:45-49`).
`pgl27_collisions (enc_code e) S` and `code_views (enc_code e) b S` take the
code table in the same first position everywhere. The only numeric constant left
is 336, the order of the shuffle group (`pgl27_table_bridge.v:79`), which is a
fact of the geometry and not of the deck pair.
