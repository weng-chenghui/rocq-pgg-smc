# APPLIED: the frozen-files pass, as landed (2026-09-21)

Applied against HEAD `c7f9991`, branch `feat/tableau-extensions-probe`.
Nothing committed. `make` was never run. `instances/psl211/psl211_endpoints.v`
was never compiled, and nothing rebuilt its `.vo`.

22 tracked `.v` files changed, 160 insertions, 158 deletions.

## Stage 1: the files that are NOT frozen, with their compiles

All seven compiled single-file through `scratchpad/rocq1 1500 14000 rocq
compile <flags> FILE`, flags being the `-R` lines of `_CoqProject` plus its
`-arg` lines with every word `-arg` dropped. All green.

| order | file | rows | result |
|---|---|---|---|
| 1 | `groups/pgg_raag_clique.v` | `star3_ntB0/1/2` | rc=0, 3 s |
| 2 | `instances/s5/pgg_raag_s5.v` | B8 + F1 | rc=0, 4 s |
| 3 | `instances/s5/rigidity_s5_instance.v` | F5 | rc=0, 4 s |
| 4 | `security/pgg_schreier.v` | B4 + F4 | rc=0, 4 s |
| 5 | `security/pgg_schreier_weighted.v` | B5 | rc=0, 4 s |
| 6 | `instances/pgl27/pgl27_orbit.v` | B6 | rc=0, 6 s |
| 7 | `instances/psl211/psl211_alldecks.v` | B7 | rc=0, 7 s |

The order is not the sheet's C9 order, and the reason is a dependency fact
C9 did not record. `instances/s5/rigidity_s5_instance.v` has
`security/pgg_schreier.v` in its transitive closure, through intermediates
this pass does not rebuild. Compiling `pgg_schreier.v` first would have left
those intermediates holding the old digest, and `rigidity_s5_instance.v`
would then have failed on inconsistent assumptions rather than on anything
in the sheet. Compiling the S5 chain first and the Schreier pair after it
removes that. I computed the `Require` closure of every tracked `.v` before
compiling and confirmed three things: with this order no intermediate needs
rebuilding, `instances/psl211/psl211_alldecks.v` and
`instances/pgl27/pgl27_orbit.v` have no stage-1 file in their closures at
all, and `instances/psl211/psl211_endpoints.v` has no stage-1 file in its
closure, which is the ruling's claim and it holds.

### Per-row landing, stage 1

| row | file | final lines | as ruled |
|---|---|---|---|
| B8 rename | `instances/s5/pgg_raag_s5.v` | 59-63, 66-70, 73-75 | yes, `s5_n_traces_natB1/2/3` per F13 |
| F1 | `instances/s5/pgg_raag_s5.v` | 24 | yes, the auditor's exact 80-byte line |
| F5 | `instances/s5/rigidity_s5_instance.v` | 31-33 | yes, the auditor's exact three 79-byte lines |
| star3 | `groups/pgg_raag_clique.v` | 252, 255, 258 | yes, `star3_n_traces_natB0/1/2` |
| B4 code | `security/pgg_schreier.v` | 255-256, 387-388, 396-397, 400, 402, 405 | yes |
| F4 comments | `security/pgg_schreier.v` | 59, 60, 94, 321, 376, 394 | yes, the auditor's exact lines |
| B5 | `security/pgg_schreier_weighted.v` | 194-196, 202, 205, 207, 209, 212 | yes |
| B6 | `instances/pgl27/pgl27_orbit.v` | 131-132, 472-473, 478-479, 495 | yes |
| B7 | `instances/psl211/psl211_alldecks.v` | 790-793, 796-797 | yes |
| F17 | `manifest/pgg_tableau_security_property_relations.v` | 470 | yes, "loses" |

The three docstring heads of `pgg_raag_s5.v` were re-laid by hand, as B8
required. `s5_n_traces_natB1` is nine bytes longer than `s5_nt_L1`, so one
word moves down in each and the paragraph re-wraps. Every new line is 72 to
76 bytes, against the 76-byte head lines they replace.

**F17, the declaration read.** `manifest/pgg_tableau_security_property_relations.v:471`
is `ideal_prod_adapter`, the sample adapter that draws the run argument from
the actual model's own law of `arg_read` and the cut from the certificate's
ideal law, the two independent. The comment says the model holds no
coordinate for any coupling between them. "The distance below" is
`var_dist (sa_cut_dist sa) (ic_ideal ic)`, the right-hand side of
`var_dist_joint_reading_arg_le` at line 561-569, which bounds the distance
between the actual joint law and this product one. So the omission loses at
most that distance, and "loses" reads true of it. It is also the owner's own
substitution for this verb in the sheet's table (`costs nothing` becomes
`loses nothing`). Applied as ruled, no alternative wording needed.

**`manifest/pgg_tableau_security_property_relations.v` was NOT compiled, and
the reason is the endpoint file.** Its `Require` closure holds 150 files and
seven of the eight stage-1 files. After their recompiles, compiling it needs
73 intermediate files rebuilt. That is far outside the brief and it is the
kind of pass that ends up rebuilding frozen files. The change there is one
word inside an existing comment on one line, and the comment-stripped token
stream of the file is byte-identical to `HEAD`, which is the evidence the
brief accepts for a comment-only edit.

## Stage 2: the frozen files, no compile

Every Part A row landed as ruled. Where the ruling named a replacement text
(F8 to F12) that text was used, not the sheet's. A38 taken, A0-W left, A2's
measured-time "cost" kept.

| row | file | final lines | note |
|---|---|---|---|
| A1 | `groups/pgg_raag.v` | 1042 | one word in place |
| A2 | `instances/psl211/psl211_endpoints.v` | 6-15 | re-laid at 80; lines 6-9 came out byte-identical |
| A3 | `instances/psl211/psl211_exec.v` | 7-20 | re-laid at 80, F11's wording |
| A4 | `instances/psl211/psl211_exec.v` | 35 | two index lines become one, the `==` column kept |
| A5 | `instances/psl211/psl211_exec.v` | 43 | F6's exact line, was 44 before A4 shortened the box |
| A6 | `instances/psl211/psl211_exec.v` | 98-103 | re-laid |
| A7 | `instances/psl211/psl211_exec.v` | 106-110 | re-laid |
| A8 | `instances/psl211/psl211_exec.v` | 115 | one word in place |
| A9 | `instances/psl211/psl211_exec.v` | 120 | one word in place |
| A10 | `instances/psl211/psl211_exec.v` | 125-130 | re-laid |
| A11 | `instances/psl211/psl211_profile.v` | 75-80 | re-laid |
| A12 | `instances/psl211/psl211_profile.v` | 98-103 | re-laid |
| A13 | `instances/psl211/psl211_profile.v` | 132 | one word in place |
| A14 | `protocol/pgg_algebra_syntax.v` | 41 | one boxed line, re-padded to 80 |
| A15 | `protocol/pgg_algebra_syntax.v` | 83 | one word in place |
| A16 | `protocol/pgg_algebra_syntax.v` | 150-152 | two lines become three, see below |
| A17 | `protocol/pgg_execution_plug.v` | 85 | one word in place |
| A18 | `protocol/pgg_instance.v` | 18-34 | re-laid at 80, F9's wording |
| A19 | `protocol/pgg_instance.v` | 54-57 | re-laid at 80 |
| A20 | `protocol/pgg_instance.v` | 303-304 | re-laid |
| A21 | `protocol/pgg_instance.v` | 315 | one word in place |
| A22 | `protocol/pgg_instance.v` | 363-365 | re-laid |
| A23 | `protocol/pgg_instance.v` | 457 | one word in place |
| A24 | `protocol/pgg_instance.v` | 691 | one word in place |
| A25 | `protocol/pgg_instance.v` | 709 | one word in place |
| A26 | `protocol/pgg_instance.v` | 756 | one word in place |
| A27 | `protocol/pgg_instance.v` | 765 | F8's wording, one line in place |
| A28 | `protocol/pgg_instance.v` | 800 | one line in place |
| A29 | `protocol/pgg_session_types.v` | 110-112 | re-laid |
| A30 | `reconstruct/algebraic_rigidity.v` | 119-126 | F3's three lines at 78, line 124 untouched |
| A31 | `reconstruct/algebraic_rigidity.v` | 156-159 | F10's wording |
| A32 | `reconstruct/algebraic_rigidity.v` | 197 | F2, one line in place, was 194 |
| A33 | `reconstruct/algebraic_rigidity.v` | 391-395 | F12's wording |
| A34 | `reconstruct/covering_scheme.v` | 189 | one line in place |
| A35 | `security/pgg_collusion_bound.v` | 159-164 | re-laid |
| A36 | `security/pgg_collusion_bound.v` | 464-469 | re-laid |
| A37 | `security/pgg_security_solver.v` | 71 | one line in place |
| A38 | `security/pgg_collusion_bound.v` | 391 | one line in place, taken |
| B1 | `instances/psl211/psl211_orbit.v` | 842-845, 851, 871, 1028 | binders, `Arguments` and both intro patterns in ONE edit |
| B2 | `reconstruct/transitivity_privacy.v` | 401, 605, 615 | `l1 l2` to `i j` |
| B3 | `smc/smc_interpreter.v` | none | not touched, per the ruling |

**Layout policy.** `reflow.py` and `apply_tsv.py` were not used at all, per
F7. Every paragraph was laid out by a hand-written wrapper that takes each
block's own opener, its own continuation indent and its own maximum byte
width from the block being replaced, and that preserves two-space sentence
spacing inside a line. Where a row's changed words sit on one line and the
new line stays inside the block's width, only that line was touched. Rows
A1, A8, A9, A13, A14, A15, A17, A21, A23, A24, A25, A26, A27, A28, A32, A34,
A37 and A38 are one-line edits for that reason. No added line anywhere in
the diff exceeds 80 bytes, and no line exceeds the width of its neighbours.

**A16 needed three lines where the sheet has two.** Swapping "buys" for
"gives" makes the line 77 bytes, and the widest line of that comment is 76.
Moving one word down and re-wrapping the two lines into three keeps
everything at 68 or less.

**A20 needed a hand correction after the wrapper ran.** The wrapper pushed
the closing delimiter onto a line of its own. The field comment is now two
lines of 71 and 73 bytes, sitting among sibling field comments of 74 to 78
bytes in the same record.

**A2 needed a hand correction after the wrapper ran.** The greedy wrap split
"343 s" across lines as "343" and "s,". Lines 12 to 15 were re-laid by hand
so the number keeps its unit. Still four lines, still 80 bytes each.

## Addition from the coordinator: F19 in `security/pgg_collusion_bound.v`

Frozen file, comments only, not compiled. All four sentences changed, each
after reading the statement the comment sits on. Every one of the four
measures `var_dist`, so every one says "variation distance".

| line | declaration | statement read | action |
|---|---|---|---|
| 115 | `var_dist_fdistmap` at 126-127 | `var_dist (fdistmap f P) (fdistmap f Q) <= var_dist P Q` | "their TV distance" becomes "their variation distance" |
| 237 | `var_dist_fdistmap_prod_mix` at 238-244 | `var_dist (fdistmap .. (P \`x Q)) (fdistmap .. (P \`x Q')) <= delta` from per-coordinate `var_dist .. <= delta` | "joint convexity of the total variation distance" becomes "joint convexity of the variation distance" |
| 263 | `var_dist_supp_ge` at 266-269 | `2%:R * (1 - #\|S\|%:R / n.+1%:R) <= var_dist P (fdist_uniform (card_ord n.+1))` | "at total variation distance at least 2 (1 - k / n.+1)" becomes "at variation distance at least ...". The lower bound tends to 2 as the support shrinks, and a number above one can only be the un-halved sum |
| 880-882 | `var_dist_fdistmap_unbalanced` at 883-886 | `var_dist (fdistmap f (fdist_uniform_supp ..)) (fdist_uniform card_B) = 2%:R * (#\|B\| - #\|img\|)%:R / #\|B\|%:R` | "gives TV distance 2(\|B\| - \|f @: C\|)/\|B\|" becomes "gives variation distance ...". Three lines re-laid, because "variation" is seven bytes longer than "TV" and line 880 would have reached 81 |

None of the four is about the halved quantity.

**Two more sentences of the same class are left standing, because they were
not among the four named.** `security/pgg_collusion_bound.v:41` says "total
variation distance satisfies the triangle inequality" above
`var_dist_triangle`, whose statement is
`var_dist P M <= var_dist P Q + var_dist Q M`. Line 67 says "an injective
reader transports the total variation distance exactly" above
`var_dist_fdistmap_inj`, whose statement is
`var_dist (fdistmap f P) (fdistmap f Q) = var_dist P Q`. Both measure
`var_dist`, so both would read "variation distance" under the same rule.
Recorded, not changed.

## Self-checks

**1. Comment-stripped token stream against `git show HEAD:<file>`**, using
`scripts/strip_comments.py`.

Byte-identical for all fourteen comment-only files:
`groups/pgg_raag.v`, `instances/psl211/psl211_endpoints.v`,
`instances/psl211/psl211_exec.v`, `instances/psl211/psl211_profile.v`,
`instances/s5/rigidity_s5_instance.v`,
`manifest/pgg_tableau_security_property_relations.v`,
`protocol/pgg_algebra_syntax.v`, `protocol/pgg_execution_plug.v`,
`protocol/pgg_instance.v`, `protocol/pgg_session_types.v`,
`reconstruct/algebraic_rigidity.v`, `reconstruct/covering_scheme.v`,
`security/pgg_collusion_bound.v`, `security/pgg_security_solver.v`.

Identical modulo the rename map, with every differing token listed:

| file | differing tokens | the distinct pairs |
|---|---|---|
| `instances/psl211/psl211_orbit.v` | 16 | `(L1`/`(L`, `L1`/`L`, `L2`/`L'`, `L2.`/`L'.`, `L2;`/`L';`, `L2].`/`L'].`, `[L1`/`[L` |
| `reconstruct/transitivity_privacy.v` | 6 | `l1`/`i`, `l2;`/`j;` |
| `groups/pgg_raag_clique.v` | 3 | `star3_ntB0/1/2` to `star3_n_traces_natB0/1/2` |
| `instances/s5/pgg_raag_s5.v` | 3 | `s5_nt_L1/2/3` to `s5_n_traces_natB1/2/3` |
| `security/pgg_schreier.v` | 19 | `(L1`/`(L`, `L1.`/`L.`, `L2`/`L'`, `L2)%N`/`L')%N`, `L2)%N)`/`L')%N)` |
| `security/pgg_schreier_weighted.v` | 13 | the same five pairs |
| `instances/pgl27/pgl27_orbit.v` | 18 | `(L1`/`(L`, `L1`/`L`, `L2`/`L'`, `L2.`/`L'.`, `L2;`/`L';` |
| `instances/psl211/psl211_alldecks.v` | 12 | `(L1`/`(L`, `L1`/`L`, `L2`/`L'`, `L2.`/`L'.` |

Token stream lengths are equal in every case.

**C1, the `Arguments` line.** `instances/psl211/psl211_orbit.v:851` now reads
`Arguments list_to_set_inj [L L'].`, and a whole-word count of `L1`, `L2`,
`l1`, `l2` over each of the eight renamed files returns zero.

**C5, comment span count.** `common.comment_spans` over each changed file
against `HEAD` is equal everywhere except the two places a ruling changed the
line count: `instances/psl211/psl211_exec.v` 55 to 54, because A4's two boxed
index lines become one, and `reconstruct/algebraic_rigidity.v` 157 to 158,
because F3 splits one boxed line into two. Each boxed one-line comment is its
own top-level span, so both counts are exactly what those two rows imply.

**2. `git diff HEAD --shortstat -- '*.v'`**: 22 files changed, 160
insertions, 158 deletions. A whole-word scan of every ADDED line for apex,
gate and its forms, posit and its forms, arm, port, row, the norm
abbreviation, spend, price, pay, budget, buy, owe, cost, currency, cash,
indist, and for the history words now, no longer, previously: **zero hits**.
A2's kept "cost" does not appear because the wrapper reproduced that line
byte-identically, so it is context in the diff rather than an added line.

**3. The comments of the 35 frozen files after the pass** return exactly two
word hits: `instances/psl211/psl211_endpoints.v:6` "cost 568 s", which is A2
kept by the measured-time precedent, and `security/pgg_collusion_bound.v:12`
"worth", which is A0-W left by the ruling. The Part A0 innocents are intact
and unchanged: 70 occurrences of row and rows in the 35, and the 40 GL(2,q)
and PGL(2,q) names. The only whole-word norm-abbreviation sites left in the
35 are the six lines of `smc/smc_interpreter.v` 187 to 193, which is B3, not
renamed by the ruling.

**4. `git status --short -- '*.v'`** lists the 22 modified files and no
others. `smc/smc_interpreter.v` is not among them and its mtime is still
`Aug 26 12:36:44 2026`. `instances/psl211/psl211_endpoints.vo` is still
`Sep 17 16:32:24 2026`, 52717 bytes, so nothing rebuilt it.

## `.tex` mentions

`git grep -n -E "s5_nt_L|star3_ntB|n_traces_natB" -- 'paper*/'` returns zero
hits across `paper/`, `paper-wadt2026/` and
`paper-wadt2026-baseline-application/`. No `.tex` file was opened or edited.

## Done differently, and why

1. **The compile order of stage 1** is the S5 chain before the Schreier
   pair, not the sheet's C9 order. Reason above.
2. **`manifest/pgg_tableau_security_property_relations.v` was not compiled.**
   Reason above.
3. **Three hand corrections after the layout wrapper**: A2 lines 12-15, A16,
   A20. Each is described above with its byte widths.

## Not done, and open for the owner

1. **The `ntB` family in `groups/pgg_raag_clique.v` is much larger than the
   audit saw, and the ruled rename now splits it.** F13 named
   `star3_ntB0/1/2` at lines 252, 255 and 258, and those three were renamed
   as ruled. A word-boundary search finds nine more members of the same
   convention in the same file, none of them renamed:

   | line | name |
   |---|---|
   | 261 | `star3_ntB3` |
   | 282 | `free3_ntB2` |
   | 304 | `abelian3_ntB2` |
   | 307 | `abelian3_ntB3` |
   | 328 | `path3_ntB2` |
   | 331 | `path3_ntB3` |
   | 1128 | `path4_ntB_check` |
   | 1133 | `star3_ntB_check` |

   `star3_ntB3` sits three lines below `star3_n_traces_natB2`, so the split
   is visible at a glance. None of the nine is a use site of the three
   renamed lemmas, so nothing is broken and the file compiles green. I did
   not extend the rename, because the ruling names three lemmas and the
   rulings win. The ruling's own reason was one word per concept, and on the
   evidence above that reason now argues for either renaming all twelve or
   reverting the three. This is the owner's call and it is one edit either
   way in a file that compiles in three seconds.

2. **`audit-inventory/THEOREM_INDEX.md` and `audit-inventory/theorem_index.tsv`**
   still carry the old `s5_nt_L*` and `star3_ntB*` names, eight matching
   lines in each. They are generated and not compiled. The sheet left this
   undecided and I did not regenerate them.

3. **`security/pgg_collusion_bound.v` lines 41 and 67**, the two further
   "total variation distance" sentences described above.

4. **B3, `smc/smc_interpreter.v`**, not renamed, per the ruling, and the
   vendoring statement stays true.

## What the main session still has to do

The comment-only files are proved unchanged in code by check 1, so the
remaining risk is B1 and B2 alone. One ordered pass over the reverse closure,
`make -j1`, with `instances/psl211/psl211_endpoints.v` compiled once at the
end. A failure in B1 or B2 stops that pass well before the endpoint file is
reached.

---

# Follow-up, same day: the main session's rulings on the two open items

Both applied. Same rules: no `make`, no frozen file compiled, no layout tool,
hand layout, nothing committed. The two open items above are now closed and
the "Not done" list shrinks to the `audit-inventory/` files, which the main
session updates.

## Follow-up 1: the whole `_ntB` family of `groups/pgg_raag_clique.v`

Every identifier containing the fragment `_ntB` now carries `_n_traces_natB`
in its place, so the file has one convention. Eight further names renamed,
on top of the three that landed earlier.

| line | old | new |
|---|---|---|
| 252 | `star3_ntB0` | `star3_n_traces_natB0` (earlier) |
| 255 | `star3_ntB1` | `star3_n_traces_natB1` (earlier) |
| 258 | `star3_ntB2` | `star3_n_traces_natB2` (earlier) |
| 261 | `star3_ntB3` | `star3_n_traces_natB3` |
| 282 | `free3_ntB2` | `free3_n_traces_natB2` |
| 304 | `abelian3_ntB2` | `abelian3_n_traces_natB2` |
| 307 | `abelian3_ntB3` | `abelian3_n_traces_natB3` |
| 328 | `path3_ntB2` | `path3_n_traces_natB2` |
| 331 | `path3_ntB3` | `path3_n_traces_natB3` |
| 1128 | `path4_ntB_check` | `path4_n_traces_natB_check` |
| 1133 | `star3_ntB_check` | `star3_n_traces_natB_check` |

**Inventory.** `grep -n "_ntB" groups/pgg_raag_clique.v` and
`git grep -n "_ntB" -- '*.v'` both return exactly those eight remaining
sites, all of them `Lemma` lines. `git grep -l "_ntB"` over every tracked
file returns three paths only: this file and the two `audit-inventory/`
tables, which are not touched. No other tracked `.v` file mentions any name
of the family, checked by `git grep -n -E "star3_|free3_|abelian3_|path3_|path4_" -- '*.v'`
with `groups/pgg_raag_clique.v` and `notes/` excluded, which returns nothing.
So there are no use sites, and the rename is eight declaration lines.

**No index entry and no comment mentions any of these names.** The file's
header index at lines 24 to 48 names the definitions only: `subseqs_k`,
`all_pairs_comm_sorted`, `cliques_of_size`, `clique_count`, `clique_step`,
`clique_traces`, `clique_traces_free`, `clique_traces_abelian`. The
`vm_compute` lemmas of Part 3 and Part 5 are not indexed. The ruling's rule
about keeping an index `==` column, and about a name too long for its column
standing alone with the gloss beneath, therefore did not arise. The two
comments that head these blocks, at 249 to 251 and at 1138 to 1141, describe
the numbers and name no lemma.

**Names free.** `git grep -w` for each of the eight new names over tracked
`.v` returned nothing before the edit.

**Widths.** The longest resulting line is 73 bytes,
`Lemma abelian3_n_traces_natB3 : n_traces_natB 3 3 complete_comm_nat = 10.`
Nothing approaches 80.

**Compile.** `groups/pgg_raag_clique.v` single-file through the lock, rc=0
in 3 s.

**Nothing else was compiled, and one consequence is worth naming.** No
non-frozen file mentions a renamed name, so there was no second file to
compile under the ruling. Rewriting `groups/pgg_raag_clique.vo` does
invalidate `instances/s5/pgg_raag_s5.vo` and, through it,
`instances/s5/rigidity_s5_instance.vo`, both of which were compiled green
earlier in this pass. I did not recompile them, because the brief forbids
compiling importers and the main session's closure pass covers exactly this.
Their earlier green results still stand as evidence for their own edits,
neither of which mentions a renamed name.

**`.tex`**: `git grep -n "_ntB" -- 'paper*/' '*.tex'` returns nothing. No
`.tex` file was opened or edited.

## Follow-up 2: `security/pgg_collusion_bound.v` lines 41 and 67

Frozen, comments only, not compiled. The F19 rule applied to the two
sentences recorded as residue above. Both declarations measure `var_dist`,
so both sentences now say "variation distance". One line touched in each,
nothing else changed.

| line | declaration | statement read | change |
|---|---|---|---|
| 41 | `var_dist_triangle` at 43-44 | `var_dist P M <= var_dist P Q + var_dist Q M` | "total variation distance satisfies the triangle" becomes "variation distance satisfies the triangle". Line 41 falls from 72 to 67 bytes, line 42 untouched |
| 67 | `var_dist_fdistmap_inj` at 73 | `var_dist (fdistmap f P) (fdistmap f Q) = var_dist P Q` | the word "total" is deleted, so line 67 ends "transports the variation" and line 68 still begins "distance exactly:". Line 67 falls from 80 to 74 bytes, against a block whose other lines reach 78 |

Every "TV distance" and "total variation distance" in the file now reads
"variation distance". `grep -n "TV\|total variation"` over the file returns
nothing.

## Self-checks re-run after the follow-ups

**1. Token stream.** `security/pgg_collusion_bound.v` is still byte-identical
to `git show HEAD:` after comment stripping, so both follow-up 2 edits are
provably comment-only. `groups/pgg_raag_clique.v` is identical modulo the
rename map, 11 differing tokens over 11 distinct pairs, exactly the eleven
listed in the table above and nothing else, with equal token-stream lengths.
Every other file's verdict is unchanged from the first run: fourteen
comment-only files byte-identical, seven renamed files identical modulo their
own maps.

**Whole-word count of every old name**, `star3_ntB0/1/2/3`, `free3_ntB2`,
`abelian3_ntB2/3`, `path3_ntB2/3`, `path4_ntB_check`, `star3_ntB_check`,
`s5_nt_L1/2/3`, over all tracked `.v`: **zero**. Searched with `git grep -w`,
not with `\b`, because BSD `grep -E` ignores `\b` and reports a false
negative.

**2. Added lines.** Zero hits for the barred words and the history words.
Zero added lines over 80 bytes. `git diff HEAD --shortstat -- '*.v'`: 22
files changed, 170 insertions, 168 deletions.

**3. Frozen-file comment scan.** Still exactly two hits, unchanged:
`instances/psl211/psl211_endpoints.v:6` "cost 568 s", which is A2, and
`security/pgg_collusion_bound.v:12` "worth", which is A0-W.

**4. Status.** The same 22 modified `.v` files and no others.
`smc/smc_interpreter.v` still unmodified.
`instances/psl211/psl211_endpoints.vo` still `Sep 17 16:32:24 2026`, 52717
bytes. Nothing rebuilt it.

## Follow-up 3: three economic-word comment sites in non-frozen files

Comments only, nothing compiled, hand layout inside each paragraph's own
width. Two files join the diff, which is now 24 files, 175 insertions, 173
deletions.

- `manifest/pgg_tableau.v` 1501-1502, above `Variant TransferStatusWithoutTheorem`: "owes the manifest the premise it lacks" becomes "names in the manifest the premise it lacks", the manifest's own wording in `manifest/pgg_analysis_status.v`. Two lines re-laid at 74 and 34 bytes, against a block whose widest line is 77.
- `manifest/pgg_tableau.v` 1582-1583, above `Lemma publish_sampled_transferE`: "the manifest then owes that path the premise" becomes "the manifest then states for that path the premise". Two lines re-laid at 69 and 41 bytes, against a block whose widest line is 71.
- `instances/psl211/psl211_colour_reading.v` 246, docstring of `psl211_colour_readingE`: "seat reconciliation is spent" becomes "seat reconciliation is used". One line in place, 73 to 72 bytes, against a block whose widest line is 80.

Checks: the comment-stripped token stream of both files is byte-identical to
`git show HEAD:`; no added line exceeds 80 bytes;
`git grep -n -w "owes\|owed\|owing\|spent\|spends" -- manifest/pgg_tableau.v instances/psl211/psl211_colour_reading.v`
returns nothing; `instances/psl211/psl211_endpoints.vo` is still
`Sep 17 16:32:24 2026`.
