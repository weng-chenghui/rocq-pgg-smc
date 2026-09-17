# Style audit D: `pgl27_leakage_r7.v` and `pgl27_leakage_r5.v` (2026-09-18)

Read-only audit, group D. Branch `feat/pgl27-encoding-parameter`.
Targets: `instances/pgl27/pgl27_leakage_r7.v` (467 lines),
`instances/pgl27/pgl27_leakage_r5.v` (357 lines).

Context read: `pgl27_leakage_transport.v`, `pgl27_encoding_r7.v`,
`pgl27_encoding_r5.v`, `pgl27_trace_encoding.v`, `pgl27_encoding_compare.v`,
`pgl27_secrecy.v`, `pgl27_trace.v`, `pgl27_orbit.v`, `pgl27_leakage_census.v`,
`paper-wadt2026/main.tex`, the plan's amendments F1/F2, and the rulings in
`style-audit-rulings-AB.md` and `style-audit-rulings-C.md`.

Not re-raised: anything ruled REJECT in AB (E1, E4, A5) or C (T8, C6), and the
two occurrences of "the identity deal" in `pgl27_leakage_r7.v`, which a fix
agent is replacing concurrently.

## Verdict: PASS-WITH-FIXES

One must-fix (an ACCEPTED ruling not yet applied to these two files). No
mathematical error, no class mix-up, no banned word, no wrong number, no
hidden `_r5` dependency on `_r7`. The remainder is comment precision, one
unused import, and two redundant public declarations.

---

## A. Findings in both files

### D1. Declaration comments lack the `name` prefix adopted by ruling A-T3 (must-fix, both files)

Every `(** ... *)` comment in both files opens with prose. The sibling files
carry the convention that ruling A-T3 ACCEPTED and commit `afb47d7` applied:

- `pgl27_encoding_compare.v:87` `(** pgl27_compare_heart_setE — the two deck pairs hold their hearts at the`
- `pgl27_encoding_r7.v:58` `(** code_table_r7 — the two decks of this pair as tables of the eight card`
- `pgl27_encoding_r5.v:61` `(** deck_r5 — the two decks of this pair as arrangements of the eight cards:`
- `pgl27_trace_encoding.v:87` `(** pgl27_enc_player_trace — seat i's executed-trace content in the run that`
- `pgl27_leakage_transport.v:209` `(** pgl27_enc_view_mutual_info_le1 — no coalition shares more than one bit`

The last is the generic file these two specialise, so the two audit targets are
the only files in the encoding chain that do not carry the convention.

Against, in the audit targets:

- `pgl27_leakage_r7.v:110` `(** The coalition view at this deck pair is the coalition view of`
- `pgl27_leakage_r5.v:102` `(** The harmonic four-position representative leaves six sevenths of the`

Recommended convention, one for both files, identical to the siblings:
`(** <declaration name> — <fact sentence>. <position sentence>. *)`.

Concrete fix, r7 line 110 and r5 line 102:

```
(** pgl27_r7_viewE — the coalition view at this deck pair is the coalition
    view of pgl27_secrecy.v. ...
```
```
(** pgl27_r5_noncollision_harmonic — the harmonic four-position
    representative leaves six sevenths of the shuffles distinguishable. ...
```

Affects 27 comments in `_r7` (110, 121, 129, 138, 146, 154, 162, 175, 188,
201, 214, 231, 241, 255, 265, 276, 286, 302, 332, 355, 365, 376, 391, 410,
428, 446, 456) and 19 in `_r5` (102, 110, 119, 128, 141, 154, 171, 178, 191,
198, 213, 235, 260, 271, 285, 299, 318, 334, 345). The `(* ... *)` block
separators and the two in-proof source comments (r7:341, r5:246) are not
declaration comments and stay as they are.

### D2. `_ge7E` and `_ge5E` duplicate their `_determines` twin and are used nowhere outside their file (should-fix, both files)

- `pgl27_leakage_r7.v:290` `Lemma pgl27_r7_view_mutual_info_ge7E (C : {set 'I_8}) : (7 <= #|C|)%N -> ... = 1`
- `pgl27_leakage_r7.v:415` `Lemma pgl27_r7_view_determines (C : {set 'I_8}) : (... == 1) = (7 <= #|C|)%N`
- `pgl27_leakage_r5.v:202` / `pgl27_leakage_r5.v:304`, same shape at 5.

`_determines` is the sharp statement and gives `_ge7E` in one step
(`rewrite pgl27_r7_view_determines` then `eqP`). Grep over `*.v` outside
`notes/` and `.claude/`: the only external consumer of either file is
`instances/pgl27/pgl27_encoding_compare.v`, and it uses `pgl27_r7_viewE`,
`pgl27_r7_view_mutual_infoE`, `pgl27_r7_view_determines`,
`pgl27_r5_view_mutual_infoE`, `pgl27_r5_view_determines` and nothing else.
`_ge7E` and `_ge5E` have zero external uses; each is only the internal step at
r7:329, r7:419 and r5:231, r5:309.

**Recommendation: keep `_determines` public, make `_ge7E` and `_ge5E`
`Local`.** Drop their header entries (r7:55-56, r5:44-45) and fold the fact
into the `_determines` entry, which already states it in both directions.

Caveat for the coordinator: `main.tex:1685-1690` cites only
`pgl27_view_dep_k4`, `pgl27_view_leak_k4`, `pgl27_view_indep` and
`pgl27_view_leakage_le`, so the paper as it stands cites neither form. If the
comparison section being written for this branch quotes the one-direction form
in a threshold table, keep them public instead and say so in the header.

### D3. The `_lt1` pairs duplicate case work and sit in the wrong order (optional, both files)

- r7: public `pgl27_r7_view_mutual_info_k6_lt1` (359, `#|C| = 6 -> I < 1`),
  `Local pgl27_r7_le6_lt1` (395, `#|C| <= 6 -> I < 1`).
- r5: public `pgl27_r5_view_mutual_info_k4_lt1` (264), `Local
  pgl27_r5_le4_lt1` (289).

The `Local` lemma is strictly stronger, is declared after the weaker public one
it generalises, and re-derives the same branch: r7:407
`by rewrite (pgl27_r7_k6E E6); lra.` repeats r7:362, and r5:296 repeats
r5:267-268.

Fix: move the `Local` general lemma above the public special case and prove the
special case from it, which removes the duplicate `lra` and makes the
dependency visible:

```
Lemma pgl27_r7_view_mutual_info_k6_lt1 (C : {set 'I_8}) : #|C| = 6 ->
  `I(pgl27_secret R ; pgl27_view R C) < 1.
Proof. by move=> HC; apply: pgl27_r7_le6_lt1; rewrite HC. Qed.
```

Keep the `#|C| = 6` form public: it is the named sharpness witness for the
recovery threshold, and the general form reads as an internal step. Same edit
at r5 with `pgl27_r5_le4_lt1` and `#|C| = 4`.

### D4. `_ge4` names the hypothesis where the reader expects the conclusion (optional, both files)

- `pgl27_leakage_r7.v:381` `pgl27_r7_view_mutual_info_ge4`, statement
  `(4 <= #|C|)%N -> 5%:R / 7%:R <= I`.
- `pgl27_leakage_r5.v:276` `pgl27_r5_view_mutual_info_ge4`, statement
  `(4 <= #|C|)%N -> 11%:R / 14%:R <= I`.

Read alone, `mutual_info_ge4` says the mutual information is at least four. The
4 is a cardinality. Within the file `geN` does consistently name the card
hypothesis (`_ge7E`, `_ge5E`, `_ge4`), so this is internally coherent, which is
why it is optional rather than should-fix.

Two alternatives, coordinator's call:

1. `pgl27_r7_view_mutual_info_min` / `pgl27_r5_view_mutual_info_min`, the
   hypothesis staying visible in the statement. Reads as "the minimum leakage",
   which is what the header calls it (r7:59-60, r5:48-50).
2. `pgl27_r7_view_mutual_info_card_ge4` and likewise for r5, which at least
   marks the 4 as a cardinality.

If D2 is accepted and `_ge7E`/`_ge5E` become `Local`, option 1 costs no
consistency, since `geN`-as-hypothesis then survives only in `Local` names.

Related, lower still: the generic twin was renamed by ruling A-T2 to
`pgl27_enc_view_mutual_info1_card_ge` (`pgl27_leakage_transport.v:305`). If
`_ge7E`/`_ge5E` stay public, `pgl27_r7_view_mutual_info1_card_ge7` mirrors it.

---

## B. `instances/pgl27/pgl27_leakage_r7.v`

### D5. Unused import `pgl27_trace_encoding` (should-fix)

`pgl27_leakage_r7.v:91` `From pgg_smc Require Import pgl27_trace pgl27_trace_encoding.`

Nothing in the file references a declaration of `pgl27_trace_encoding.v`. The
trace statements go through `pgl27_coalition_trace` and
`pgl27_coalition_trace_E` of `pgl27_trace.v` (used at 435, 443, 451, 461); the
encoding-parameterised `pgl27_enc_coalition_trace` /
`pgl27_enc_coalition_traceE` appear only in `_r5`.

Fix: `From pgg_smc Require Import pgl27_trace.` Apply only if the single target
still builds without it, the same caveat ruling C5 attached.

### D6. The header attributes the seven-position carry to the wrong lemma (should-fix)

`pgl27_leakage_r7.v:40-42`:

```
(* (pgl27_view_indep) becomes the value zero; the monotonicity of the mutual  *)
(* information under coalition inclusion (pgl27_view_leakage_le) carries the  *)
(* seven-position value to the whole deck; and the single four-position       *)
```

In the file, `pgl27_view_leakage_le` (`pgl27_secrecy.v:98`) is used once, at
line 350, inside `pgl27_r7_view_mutual_info_eq0`, where it carries the strict
positivity of a four-position subcoalition upward. What carries the
seven-position value to every larger coalition is
`pgl27_enc_view_mutual_info1_card_ge` (`pgl27_leakage_transport.v:305`),
applied at line 294; that lemma ends in `pgl27_enc_view_leakage_le`, the
generic twin, and pairs it with the prior-entropy upper bound
`pgl27_enc_view_mutual_info_le1`. The header names the right principle and the
wrong lemma, and omits that the carry is where a lower and an upper bound meet,
which is the one genuinely interesting step of the file.

Also in that paragraph: `pgl27_view_indep` (`pgl27_secrecy.v:82`),
`pgl27_view_dep_k4` (`:116`) and `pgl27_view_leak_k4` (`:192`) all exist but
appear nowhere in this file. That is fine under the "these values supersede
those statements" reading the paragraph intends, but "The file joins three
statements of pgl27_secrecy.v" (line 38) is vague about which reading applies,
and then names four lemmas.

Fix, replacing lines 38-46:

```
(* The values below supersede three qualitative statements of               *)
(* pgl27_secrecy.v. The independence of a coalition view of at most three   *)
(* positions from the orbit secret (pgl27_view_indep) becomes the value     *)
(* zero, and an equivalence: vanishing mutual information holds exactly at  *)
(* coalitions of at most three positions. The single four-position          *)
(* coalition of strictly positive mutual information (pgl27_view_dep_k4,    *)
(* pgl27_view_leak_k4) becomes the exact value five sevenths there. The     *)
(* value at every coalition of seven or more positions comes from the       *)
(* seven-position representative through                                    *)
(* pgl27_enc_view_mutual_info1_card_ge, where monotonicity under coalition  *)
(* inclusion gives one bit from below and the prior entropy of the secret   *)
(* gives one bit from above.                                                *)
```

### D7. The `_ge4` comment states a monotonicity argument the lemma neither makes nor uses (should-fix)

`pgl27_leakage_r7.v:376-380`:

```
(** A coalition of four or more positions shares at least five sevenths of a
    bit with the orbit secret. Once the privacy threshold is passed the
    leakage never falls back towards zero, so the smallest value above the
    threshold, which this pair reaches on the harmonic class, is a lower
    bound for every larger coalition. *)
```

The proof (383-389) is a case split on the closed form, not a monotonicity
argument; monotonicity in the coalition is `pgl27_view_leakage_le`, which this
lemma does not cite. "so ... is a lower bound for every larger coalition" is a
proof sketch, which the statement-comment standard keeps out of the statement
body. The fact half is correct: at this pair the values above the privacy
threshold are 5/7, 11/14, 25/28, 27/28, 1, whose minimum is 5/7 on the harmonic
class.

Fix: keep the fact, replace the second sentence with a domain-position one.

```
(** pgl27_r7_view_mutual_info_ge4 — a coalition of four or more positions
    shares at least five sevenths of a bit with the orbit secret. It is the
    guarantee read in the adversary's direction rather than the scheme's:
    past the privacy threshold there is no coalition left that learns only a
    negligible amount, and the harmonic four-position coalitions are where
    this pair comes closest to one. *)
```

The same sentence appears at `pgl27_leakage_r5.v:271-275` with 11/14 and the
equianharmonic class, and needs the same treatment; see D11.

### D8. `by rewrite ...; exact: ...` and an unused intro name (optional)

- `pgl27_leakage_r7.v:295` `by rewrite pgl27_r7_viewE; exact: pgl27_r7_k7E.`
  `exact:` already closes the goal, so the leading `by` is redundant. Write
  `by rewrite pgl27_r7_viewE; apply: pgl27_r7_k7E.` or drop the `by`.
- `pgl27_leakage_r7.v:237` `move=> HC; rewrite -pgl27_r7_viewE.` introduces
  `HC`, which is then never named; it is discharged by the `done` inside
  `exact:` at 238. The r5 twin is the clean one-liner
  `pgl27_leakage_r5.v:176` `Proof. exact: pgl27_enc_view_mutual_info_le3E. Qed.`
  Candidate:
  `Proof. by rewrite -pgl27_r7_viewE; exact: pgl27_enc_view_mutual_info_le3E. Qed.`
  This relies on `rewrite` firing under the arrow; if it does not, keep the
  current form. The same `move=> HC` at 250, 261, 272, 282 does bind a name the
  proof then passes explicitly, so those stay.

### D9. Header "Key results" order does not match declaration order (optional)

The header lists `pgl27_r7_view_mutual_info_ge7E` fourth (55-56), but it is
declared at 290, before the closed form at 311; and lists `_ge4` (59-60) before
`_leak_coalitionE` (61-62), which are declared at 381 and 369. `_r5` has the
same inversion for `_ge5E` (header 44-45, declared 202). Either reorder the
header to declaration order or reorder the declarations; if D2 lands, both
inversions disappear with the `_geNE` entries.

---

## C. `instances/pgl27/pgl27_leakage_r5.v`

### D10. "the two thresholds" denotes two different pairs of numbers in one file (should-fix)

- `pgl27_leakage_r5.v:21-23` `(* Five is therefore the recovery threshold of this pair against seven for *)`
  ... `(* ... and a single coalition size lies strictly between the two thresholds. *)`
  Here the two thresholds are the recovery thresholds 5 and 7 of the two pairs,
  and the single size is 6.
- `pgl27_leakage_r5.v:180-181` `Four positions are the only coalition size
  strictly between the two thresholds of this deck pair`. Here they are this
  pair's privacy threshold 3 and recovery threshold 5, and the single size is 4.

Both are true. The same phrase carries two referents 160 lines apart in one
file, and both instances assert "a single size", inviting the reader to
conflate 6 with 4. The user's one-word-per-concept rule applies.

Fix, naming the numbers in both places:

- 21-23: `Five is therefore the recovery threshold of this pair against seven
  for the pair of pgl27_leakage_r7.v, so the size six alone lies strictly
  between the two recovery thresholds.`
- 180-181: `Four positions are the only size strictly between this pair's
  privacy threshold three and its recovery threshold five, and the two
  cross-ratio classes already leak different amounts there.`

### D11. The `_ge4` comment carries the same proof sketch as r7 (should-fix)

`pgl27_leakage_r5.v:271-275`, second sentence: "Once the privacy threshold is
passed the leakage never falls back towards zero, and the smallest value above
the threshold sits on the equianharmonic class at this deck pair, the opposite
class from the pair of pgl27_leakage_r7.v."

The class claim is correct and is exactly amendment F2: at `_r5` the values
above the threshold are 11/14 (equianharmonic), 6/7 (harmonic) and 1, minimum
11/14; at `_r7` they are 5/7 (harmonic), 11/14, 25/28, 27/28, 1, minimum 5/7.
Keep that half. Drop the monotonicity clause for the reason given in D7. The
comparison to `_r7` is the position sentence and should be the whole of it.

```
(** pgl27_r5_view_mutual_info_ge4 — a coalition of four or more positions
    shares at least eleven fourteenths of a bit with the orbit secret. The
    minimum above the privacy threshold sits on the equianharmonic class at
    this pair and on the harmonic class at the pair of pgl27_leakage_r7.v, so
    which cross-ratio class is the safest four-position coalition is fixed by
    the choice of decks and not by the geometry of PGL(2,7). *)
```

### D12. Cross-file count mismatch for the sizes between the two recovery thresholds (should-fix)

- `pgl27_leakage_r5.v:22-23` a single coalition size lies strictly between the
  two thresholds, that is {6}.
- `pgl27_encoding_compare.v:179-181` "Six is the second and last size inside
  the gap between the two recovery thresholds", that is {5, 6}.

Each is defensible under its own reading of "between" and "inside the gap", but
a reader holding both files gets one and two. Recommend fixing this in
`pgl27_leakage_r5.v` only, so no ruling on the comparison file is disturbed:
name the sizes instead of counting them.

`pgl27_leakage_r5.v:21-23` becomes, combining with D10:

```
(* Five is therefore the recovery threshold of this pair against seven for    *)
(* the pair of pgl27_leakage_r7.v. At the sizes five and six a coalition      *)
(* determines the secret at this pair and not at the other.                   *)
```

### D13. Semicolon in the header, against the punctuation of both headers elsewhere (optional)

`pgl27_leakage_r5.v:25` `(* on the equianharmonic class; at the other pair the minimum sits on the *)`.
Both headers otherwise join a claim to its gloss with a colon
(`pgl27_leakage_r7.v:22`, `:28`) or a period. Purely cosmetic; raise only if
the coordinator wants punctuation uniform across the header set.
(`pgl27_leakage_r7.v:40` and `:42` use semicolons inside a three-item list,
which is standard and needs no change.)

### D14. `pgl27_r5_view_mutual_info_ge5E` proof could be one line (optional)

`pgl27_leakage_r5.v:204-207`:

```
apply: (pgl27_enc_view_mutual_info1_card_ge (k := 5)) => D HD.
exact: pgl27_r5_k5E.
```

`by apply: (pgl27_enc_view_mutual_info1_card_ge (k := 5)) => D HD; exact: pgl27_r5_k5E.`
fits in 80 columns. Note the r5 form is already the cleaner of the two: not
introducing the cardinality hypothesis lets `apply:` unify through the arrow, so
r5 needs no `=> //` where r7:294 does. If D8's `le3E` suggestion is taken, r7
moves toward this shape too.

---

## D. Checks that pass, recorded so they are not re-audited

1. **Formatting.** No line over 80 columns in either file, no tab, no trailing
   whitespace. Header block, `Set Implicit Arguments` group, `Import` group,
   scope openings and `Section`/`End` names all match the sibling files and
   each other.
2. **Banned words.** No `apex`, no `gate`/`gated`/`gating`, no
   `posit`/`posited`/`positing`, and none of `ramp`, `beats`, `escape`,
   `dodge`, `smash`, or `cap` as a noun, in either file. (A naive grep appears
   to hit `posit` many times; every hit is the substring inside "position" or
   "positions".)
3. **Every identifier named in either header exists**, at:
   `pgl27_view_indep` secrecy:82, `pgl27_view_dep_k4` secrecy:116,
   `pgl27_view_leak_k4` secrecy:192, `pgl27_view_leakage_le` secrecy:98,
   `pgl27_view_indep_alldecks` secrecy:215, `pgl27_coalition_trace_E`
   trace:416, `pgl27_enc_coalition_traceE` trace_encoding:168.
4. **No class mix-up, F2 satisfied.** Both files put `subset_class C = true`
   (equianharmonic) on 11/14: r7:315, r5:225, and the trace copies r7:438,
   r5:328. Minima: r7 header 24-26 and r7:381-382 say 5/7 on the harmonic class
   (5/7 < 11/14); r5 header 23-26 and r5:276-277 say 11/14 on the
   equianharmonic class (11/14 < 6/7). Both match F2.
5. **Header numbers correct.** `_r7`: decks `0 1 2 3 4 5 6 7` /
   `0 1 2 4 3 5 6 7` (lines 7-8), values 0, 11/14 or 5/7, 25/28, 27/28, 1
   (15-18), threshold seven (22), minimum 5/7 harmonic (24-26). `_r5`: decks
   `0 1 2 3 4 5 6 7` / `0 1 2 4 3 5 7 6` (7-8), values 0, 11/14 or 6/7, 1
   (15-18), threshold five (21), minimum 11/14 equianharmonic (23-26). Every
   number agrees with the statement it summarises.
6. **The 28/42 split** quoted at r7:304-306 and r5:215-216 matches
   `pgl27_orbit.v:518` (28 equianharmonic) and `:528` (42 harmonic), total
   70 = C(8,4).
7. **`_determines` says one full bit iff k <= |C| at the right k** in all four
   places: r7:415-416 and r7:460-461 at 7, r5:304-306 and r5:349-351 at 5.
   Consistent with F1, which identifies the possibilistic recovery threshold of
   a fixed pair with `r_info`.
8. **`Local` helper sets are minimal.** Every `Local Lemma` in both files has at
   least one use inside its file. r7: noncollision_{harmonic, equianharmonic,
   five, six, seven} at 170/183/196/209/222; {harmonic, equianharmonic, five,
   six, seven}E at 251/252/262/273/283 and 373; le3E at 322/339/399; k4E at
   324/348/402; k5E at 326/404; k6E at 328/362/407; k7E at 295; le6_lt1 at 420.
   r5: the same pattern over its nine `Local` lemmas.
9. **`_r5` does not depend on `_r7`.** `pgl27_leakage_r5.v` imports neither
   `pgl27_encoding_r7` nor `pgl27_leakage_r7` nor `pgl27_trace`, and its only
   r5-specific dependency, `pgl27_encoding_r5.v`, imports only `pgg_interface`,
   `pgl27_group`, `pgl27_orbit`, `pgl27_leakage_census` and `pgl27_encoding`
   (encoding_r5:50-55). The r7 cross-references in the `_r5` header and in three
   `_r5` comments are prose only.
10. **The r7 view theorem is on `pgl27_view` and is connected by a conversion
    lemma.** `pgl27_r7_viewE` (113-115, `Proof. by []. Qed.`) is that lemma;
    every r7 step rewrites through it (237, 250, 261, 272, 282, 293, 295, 372),
    so no r7 public statement mentions `pgl27_enc_view`.
11. **The executed-trace theorems are one rewrite from the view theorems**, as
    the plan's corrected sketch intends: r7:443, 453, 463 each
    `rewrite pgl27_coalition_trace_E` then the view lemma; r5:331, 342, 353
    each `rewrite pgl27_enc_coalition_traceE` then the view lemma. The r7 trace
    statements are on the manifest-pinned `pgl27_coalition_trace R C`, which
    T1 requires to stay untouched.
12. **Considered and not raised.** The three `_trace_*` statements in each file
    are each derivable from the `_trace_mutual_infoE` closed form, but the
    parallel view-triple / trace-triple structure is what the headers advertise
    and what a paper's execution claim cites by name. No change recommended.
    Likewise no `pgl27_r7_coalition_traceE` conversion lemma is needed to mirror
    `pgl27_r7_viewE`: nothing consumes one, and the keep-only-what-is-claimed
    criterion argues against adding it.
13. **Both import blocks are copied wholesale from a sibling** and carry more
    than either file needs beyond D5 (`morphism`, `action`, `prime`,
    `primitive_action`, `algebraic_rigidity` are candidates in both). Trimming
    is only worth doing under a single-target build check and is not raised as a
    finding.

---

## E. Public declarations: external use and paper standing

Only external consumer of either file:
`instances/pgl27/pgl27_encoding_compare.v`. Paper checked at
`paper-wadt2026/main.tex`; :1374 claims the privacy cutoff three is sharp,
:1389-1396 quotes the values 5/7, 11/14, 25/28, 27/28 and the exactly-5/7
four-heart coalition, :1685-1690 is the trust table.

| declaration | used outside its file | paper standing | action |
|---|---|---|---|
| `pgl27_r7_viewE` | yes, compare 126/142/161/175/187/202 | supporting | keep |
| `pgl27_r7_view_mutual_infoE` | yes, compare 126-188 | claimed, main.tex:1389-1396 | keep |
| `pgl27_r7_view_determines` | yes, compare 202 | claimed, recovery threshold seven | keep |
| `pgl27_r7_view_mutual_info_ge7E` | no | none | `Local` (D2) |
| `pgl27_r7_view_mutual_info_eq0` | no | claimed, main.tex:1374 | keep |
| `pgl27_r7_view_mutual_info_k6_lt1` | no | claimed, the threshold-is-not-six half | keep, reprove from `le6_lt1` (D3) |
| `pgl27_r7_view_mutual_info_leak_coalitionE` | no | claimed, main.tex:1393-1395 | keep |
| `pgl27_r7_view_mutual_info_ge4` | no | plausible, the r7 half of F2 | keep, rename (D4) |
| `pgl27_r7_trace_mutual_infoE` | comment only, compare:40 | plausible, the values hold of an execution | keep |
| `pgl27_r7_trace_mutual_info_eq0` | no | plausible | keep |
| `pgl27_r7_trace_determines` | no | plausible | keep |
| `pgl27_r5_view_mutual_infoE` | yes, compare 127-188 | plausible, comparison section | keep |
| `pgl27_r5_view_determines` | yes, compare 201 | plausible, recovery threshold five | keep |
| `pgl27_r5_view_mutual_info_ge5E` | no | none | `Local` (D2) |
| `pgl27_r5_view_mutual_info_eq0` | no | plausible, same privacy threshold at both pairs | keep |
| `pgl27_r5_view_mutual_info_k4_lt1` | no | plausible, the threshold-is-not-four half | keep, reprove from `le4_lt1` (D3) |
| `pgl27_r5_view_mutual_info_ge4` | no | plausible, the r5 half of F2 | keep, rename (D4) |
| `pgl27_r5_trace_mutual_infoE` | comment only, compare:41 | plausible | keep |
| `pgl27_r5_trace_mutual_info_eq0` | no | plausible | keep |
| `pgl27_r5_trace_determines` | no | plausible | keep |

No deletion is recommended. The two demotions in D2 are the whole of the
unused-declaration finding. Every other externally unused public declaration is
either already claimed in `main.tex` or is a named fact the comparison section
this branch is building will claim; the coordinator should confirm that section
before any further pruning.

---

## Fix order

1. D1, the `name` comment prefix in both files (must-fix, ACCEPTED ruling A-T3).
2. D2, `_ge7E` and `_ge5E` to `Local`, header entries dropped.
3. D5, drop the `pgl27_trace_encoding` import from `_r7`, build-checked.
4. D6, D7, D10, D11, D12, the comment corrections.
5. D3, D4, D8, D9, D13, D14 at the coordinator's discretion.
