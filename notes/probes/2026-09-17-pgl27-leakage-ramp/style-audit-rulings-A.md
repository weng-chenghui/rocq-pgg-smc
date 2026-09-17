# Style audit A: pgl27_mutual_info.v, pgl27_leakage_ramp.v, census diff

Auditor: rocq-auditor on Opus, read-only, 2026-09-17, at HEAD f202e9f.
Verdict: PASS-WITH-FIXES. 2 blocking, 8 should, 7 nit, 2 info.
Line numbers refer to HEAD f202e9f. Coordinator rulings are in the last column.

| ID | File | Finding | Ruling |
|---|---|---|---|
| B1 | pgl27_leakage_ramp.v header 13-15 | Scope sentence omits the fixed deal orbit_encode and the exclusion of the all-decks dealer | APPLY text B1 |
| B2 | pgl27_mutual_info.v header 7-17, 35-36 | Same scope omission, plus the uniform shuffle is unstated | APPLY text B2 |
| S1 | ramp 81-84, comment of pgl27_card_harmonic | "transport matches coalitions of equal size" is false at size four, which has two orbits | APPLY text S1 |
| S2 | ramp 335-338, pgl27_view_mutual_info_eq0 | "no seating of four players escapes the leakage": metaphor plus a third word for positions | APPLY text S2 |
| S3 | mutual_info 314-317, sevenE | "leakage ramp" metaphor | APPLY text S3 |
| S4 | ramp 305-313 and header line 11 | The comment does not say which Boolean is which class | APPLY text S4, and reword the header so it pairs equianharmonic with 11/14 and harmonic with 5/7 |
| S5 | ramp 359-361, leak_coalitionE | Names another lemma inside a statement comment | APPLY text S5 |
| S6 | mutual_info 117-224 | support_posteriorP_pgl27E and five pgl27_reachable_view_entropy_*E are public, unused outside, unlisted | Make support_posteriorP_pgl27E Local. Keep the five posterior lemmas public and list them in Key results |
| S7 | mutual_info 265-320 | One quantity, two main symbols | RENAME pgl27_mutual_info_{ambiguityE,harmonicE,equianharmonicE,fiveE,sixE,sevenE} to pgl27_view_mutual_info_{...}; update headers and every call site in pgl27_leakage_ramp.v. The file name stays |
| S8 | ramp header Key results | pgl27_subset_class_harmonicE, pgl27_subset_class_equianharmonicE, pgl27_leak_coalitionE unlisted | APPLY: add three entries |
| N1 | ramp 193-197 | Generic mutual_info_RV_le_entropy is Local in an instance file | REJECT for now. lib/proba_entropy_ext.v must not be edited, its rebuild invalidates expensive .vo files. Keep Local |
| N2 | both files | position / card / seat drift | APPLY: "positions" names the coalition and its size; "cards" only for dealt values |
| N3 | ramp 270 | _le1 numeral is a value, the others are cardinalities | KEEP pgl27_view_mutual_info_le1 (infotheo precedent Pr_le1) |
| N4 | mutual_info 219-223 | No pgl27_conditional_view_inj_seven sibling | See audit B ruling on the representative-specific copies |
| N5 | ramp 344 | H4' restates H4 | APPLY: `have [s [Us Ss subsC]] := card_geqP H4.` if it typechecks, else keep |
| N6 | mutual_info 60-62 | "proportion of views" should be a probability | APPLY: "When both lists are injective, it is the probability that one pre-reveal observation is compatible with only one secret." |
| N7 | census 450-452 | pgl27_views_uniq_seven comment restates itself | APPLY: "pgl27_views_uniq_seven — both deals restrict rep_seven injectively. Neither observation list repeats there, so the collision count below is a set-intersection cardinality rather than a raw multiplicity." |
| I1 | both | Unprefixed statement comments | No change. The unprefixed style is the target |
| I2 | census 484-492 | Two older "ramp" metaphors in pgl27_collisions_three and pgl27_collisions_seven | APPLY while the census file is open: say "the smallest value, zero, that pgl27_view_indep states" and "the largest value, reached at seven positions" in the file's own wording |
| (c) | ramp header second paragraph | pgl27_view_dep_k4 is strengthened too and is unnamed | APPLY: name it beside pgl27_view_leak_k4 in the header |

## Replacement texts

### B1, pgl27_leakage_ramp.v, replaces header lines 13-15

```
(* and the full bit from seven positions on. Every value is exact and         *)
(* unconditional on any computational assumption.                             *)
(*                                                                            *)
(* Scope. One pre-reveal observation, a uniform Boolean orbit secret, a       *)
(* uniform shuffle drawn from pgg_G pgl27_M, and for each secret the fixed    *)
(* representative deal orbit_encode of its class. The all-decks dealer of     *)
(* pgl27_view_indep_alldecks, which deals a uniform valid deck of the         *)
(* secret's class, is not covered by any value below.                         *)
```

### B2, pgl27_mutual_info.v, replaces header lines 7-17

```
(* The orbit secret is a uniform bit, the shuffle is uniform on PGL(2,7),     *)
(* and for each secret the dealt arrangement is the fixed representative      *)
(* deal orbit_encode of its class. A coalition observes the masked card       *)
(* values at its own positions before the reveal. When the two census view    *)
(* lists of a coalition are repetition-free, every observation that occurs    *)
(* comes from at most one shuffle per secret, so it leaves one or two         *)
(* compatible secrets and its posterior entropy is the indicator of that      *)
(* ambiguity. The mutual information between the secret and the view is       *)
(* then one minus the census collision ratio, exactly, with no inequality.    *)
(* At the five representative coalitions this value is five sevenths on a     *)
(* harmonic four-subset, eleven fourteenths on an equianharmonic one,         *)
(* twenty-five twenty-eighths at five positions, twenty-seven                 *)
(* twenty-eighths at six, and one bit at seven: seven of the eight            *)
(* positions determine the orbit secret before the reveal.                    *)
```

and replaces the closing lines 35-36

```
(* The statements concern the pre-reveal execution: after the public reveal   *)
(* every player learns the secret by design. The all-decks dealer of          *)
(* pgl27_view_indep_alldecks is not covered.                                  *)
```

### S1

```
(** The harmonic representative lists four of the eight positions. At size
    four the shuffle group has two orbits, so a representative's size
    selects the coalitions its value governs only together with the
    cross-ratio class of its positions. *)
```

### S2

```
(** A coalition shares no information with the orbit secret exactly when it
    holds at most three positions. The privacy threshold three is sharp at
    every coalition of four or more positions and not only at one witness
    coalition, so no four of the eight positions are information-free. *)
```

### S3

```
(** The seven-position coalition shares one bit with the orbit secret, the
    whole prior entropy of the secret. Seven of the eight positions already
    determine the orbit class before the reveal; this is the largest value
    the scheme reaches, the smallest being zero at three positions. *)
```

### S4

```
(** The mutual information between the orbit secret and the view of a
    coalition of the eight positions is zero up to size three, eleven
    fourteenths at size four on the twenty-eight equianharmonic quadruples
    and five sevenths on the forty-two harmonic ones, twenty-five
    twenty-eighths at five, twenty-seven twenty-eighths at six, and one bit
    from seven positions on. The scheme hides the orbit secret completely
    below the privacy threshold three and reveals it completely from seven
    positions on, and between those two sizes it leaks a known exact
    amount rather than an amount bounded only from above. *)
```

### S5

```
(** The four heart positions of the identity deal share five sevenths of a
    bit with the orbit secret. This is the exact value at the coalition
    that witnesses sharpness of the privacy threshold three, where the
    threshold statements give only strict positivity. *)
```
