# P0 probe results — the deck pair as a parameter of the PGL(2,7) instance

Date: 2026-09-18. Branch `feat/pgl27-encoding-parameter`.
Plan: `docs/superpowers/plans/2026-09-18-pgl27-encoding-parameter.md`.
All evidence below is a compiled `.v` file in this directory. Nothing outside
this directory was touched, and no `make` was run.

## Verdicts

| id | question | verdict |
|----|----------|---------|
| Q1 | `_r5` collisions 48, 72, 0, 0, 0; `_r7` sanity 96, 72, 36, 12, 0; uniq views | CONFIRMED |
| Q2 | record shape, both instances buildable | CONFIRMED (one correction: `enc_classK` for a new pair goes through `heart_set`, not computation) |
| Q3 | the chain's concrete-deal steps re-prove over an abstract record | CONFIRMED |
| Q4 | executed trace at an arbitrary deck function, no premise on the deck | CONFIRMED |
| Q5 | threshold privacy at an arbitrary encoding | CONFIRMED |
| — | new finding: a conversion bomb in the agreement lemmas | see "Surprises" |

## Build

`bash notes/probes/2026-09-18-pgl27-encoding-parameter/build.sh <name>`
(binds this directory to the logical name `probe`, so `q3` and `q5` can
`From probe Require Import q2_record`).

| file | compiles | wall clock |
|------|----------|-----------|
| `q0_sig.v` | yes | 4.2 s |
| `q1_collisions_r5.v` | yes | 9.4 s |
| `q1a_calibrate_nolet.v` | yes | 4.7 s |
| `q1b_calibrate_conv.v` | **no, by design** | killed at 600 s |
| `q1c_conv_bisect.v` | yes | 3.6 s |
| `q2_record.v` | yes | 3.9 s |
| `q2b_classK_nofail.v` | yes (ends in `Abort`) | 3.7 s |
| `q3_generic_chain.v` | yes | 4.4 s |
| `q4_trace_enc.v` | yes | 8.2 s |
| `q5_privacy.v` | yes | 4.6 s |

Numbers are a clean rebuild (no `.vo` present). About 3.5 s of every one is `Require`; the proofs themselves are
sub-second throughout.

---

## Q1 — the `_r5` census numbers. CONFIRMED.

`q1_collisions_r5.v` copies nothing: it `Require`s `pgl27_leakage_census` and
generalises only the two definitions that mention the deal,

```
Definition gen_views (deal : bool -> seq nat) (b : bool) (S : seq nat) :=
  [seq code_restrict S (code_comp t (deal b)) | t <- pgl27_group_table].
Definition gen_collisions (deal : bool -> seq nat) (S : seq nat) :=
  count (fun v => v \in gen_views deal false S) (gen_views deal true S).
```

with `deal_r7 := code_deal` and `deal_r5 b := if b then [:: 0;1;2;4;3;5;7;6]
else code_id`.

Collision counts, all by `vm_compute`, all `Closed under the global context`:

| reveal set | `_r7` | `_r5` |
|---|---|---|
| `[:: 0;1;2]` | 336 | 336 |
| `rep_harmonic` `{0,1,2,3}` | 96 | **48** |
| `rep_equianharmonic` `{0,1,2,4}` | 72 | **72** |
| `rep_five` | 36 | **0** |
| `rep_six` | 12 | **0** |
| `rep_seven` | 0 | **0** |

The plan's decks table is exactly reproduced, and the `_r7` numbers come out
of the generalised definitions unchanged, so the generalisation is faithful.

Repetition-freeness at `_r5`: `uniq (gen_views deal_r5 b S)` holds for both
secrets at all five representatives (`q1_r5_uniq_harmonic` …
`q1_r5_uniq_seven`). The A0 amendment asked P0 to decide this in the kernel,
because the python script counts sets; it is decided, affirmatively.

One item of the A0 amendment needs correcting. The three-position view lists
are **also** repetition-free (`q1_r5_uniq_three`), because sharp
3-transitivity makes `g |-> (g 0, g 1, g 2)` a bijection onto the 336 ordered
triples of distinct points. So the ambiguity route is applicable at three
positions too, and there gives `1 - 336/336 = 0`, agreeing with the
independence route. Nothing depends on this, but a statement comment that
says the ambiguity route stops at four positions would be wrong.

Exact ratios for the `_r5` closed form: `(336 - 48) * 7 = 6 * 336`, so the
harmonic value is `6/7`; `(336 - 72) * 14 = 11 * 336`, so the equianharmonic
value is `11/14`. `11/14 < 6/7`, confirming amendment F2: at `_r5` the minimum
above the privacy threshold sits on the **equianharmonic** class, the opposite
of `_r7`. Five, six and seven positions all give `1`, so `r_info = 5`.

Per-declaration cost (`-time`): the first `vm_compute` in the file is 0.93 s
(VM bytecode compilation of the 336-row closure), every later one is
0.04–0.19 s, and every `Qed` matches its tactic. Eighteen such lemmas cost
about 3 s in total.

---

## Q2 — the record. CONFIRMED, with one correction.

### Recommended final shape

```rocq
Record pgl27_encoding := PGL27Encoding {
  enc_deck : bool -> 8.-tuple 'I_8;
  enc_code : bool -> seq nat;
  enc_deck_ok : forall s, deck_ok (enc_deck s);
  enc_classK : forall s, orbit_class (enc_deck s) = s;
  enc_codeE : forall s, enc_code s = [seq val x | x <- enc_deck s]
}.
```

Real names, checked: `deck_ok` (`pgl27_orbit.v:94`, literally `uniq sh`),
`orbit_class` (`:112`), `heart_set` (`:98`), `orbit_encode`, `orbit_encodeK`,
`orbit_encode_deck` (`:349–365`).

Notes on the shape.

- `enc_codeE` is the whole-list form, not the pointwise one. The bridge needs
  the pointwise form `nth 0 (enc_code e s) i = val (tnth (enc_deck e s) i)`,
  which is `pgl27_table_bridge.v:178` verbatim; it is derived in two lines
  (`enc_code_nthE`) and does not belong in the record.
- The A0 amendment asked for "the nat table row has size 8 and is
  duplicate-free" as derived facts. Both are two-line consequences of
  `enc_codeE` plus `enc_deck_ok` (`enc_code_size`, `enc_code_uniq`). They are
  lemmas, not fields.
- `enc_code` is redundant as data (it is determined by `enc_deck`) but must
  stay a field: the instance supplies a literal nat list, which is what makes
  `vm_compute` on the census cheap. Deriving it as `map val (enc_deck e s)`
  would put a tuple projection inside every census evaluation.
- **Under `Set Implicit Arguments` the constructor makes `enc_deck` and
  `enc_code` implicit** (they are inferable from the later fields' types).
  Building an instance needs `@PGL27Encoding`, or the file needs an
  `Arguments PGL27Encoding : clear implicits`. Without it the error is
  `The term "orbit_encode" has type "bool -> 8.-tuple 'I_8" while it is
  expected to have type "forall s : bool, deck_ok (?enc_deck s)"`.

### Both instances build

`enc_r7 := @PGL27Encoding orbit_encode code_deal orbit_encode_deck
orbit_encodeK r7_codeE`, where `r7_codeE : code_deal s = [seq val x | x <-
orbit_encode s]` is `by case: s`.

`enc_r5 := @PGL27Encoding deck_r5 code_r5 deck_r5_ok deck_r5_classK r5_codeE`,
with `deck_r5 true = [tuple 0;1;2;4;3;5;7;6]` (Ordinal literals),
`deck_r5 false = orbit_encode false` spelled out.

| obligation | `_r7` | `_r5` |
|---|---|---|
| `enc_deck_ok` | `orbit_encode_deck` | `by case: s; vm_compute` |
| `enc_classK` | `orbit_encodeK` | via `heart_set`, see below |
| `enc_codeE` | `by case: s` | `by case: s` |

### Correction: `orbit_class` of the `_r5` true deck does NOT compute

`vm_compute` does not reduce `orbit_class deck_r5_true`. `q2b_classK_nofail.v`
shows the residual goal: a nest of unreduced `fix`es, because `orbit_class`
goes through `heart_set`, whose `enum 'I_8` does not reduce. This is exactly
why `pgl27_orbit.v` carries the **`Local`** lemma `orbit_classE` and the
spelled-out `ord8_enum` — and `Local` means E2 cannot use it.

The route that works, and the one E2 should use, is heart-set equality with
the `_r7` deck:

```rocq
Lemma deck_r5_hearts s : heart_set (deck_r5 s) = heart_set (orbit_encode s).
Proof.
apply/setP => x; rewrite !inE /is_heart.
by case: s; case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] ?.
Qed.

Lemma deck_r5_classK s : orbit_class (deck_r5 s) = s.
Proof.
by rewrite /orbit_class deck_r5_hearts -/(orbit_class (orbit_encode s))
  orbit_encodeK.
Qed.
```

This is the plan's own observation ("both true decks put the hearts at
positions `{0,1,2,4}`") turned into the proof, and it is cheaper and more
legible than any computation would have been. It also gives C1's decoder
equality for free: `q2_decoder_agree` is `by rewrite !enc_classK`.

A general instance whose true deck does **not** share heart positions with
`orbit_encode` would have no route at all from outside `pgl27_orbit.v`. If a
third encoding is ever wanted, `orbit_classE` has to be made non-`Local`
first. `_r5` does not need that.

---

## Q3 — the generic chain. CONFIRMED.

### Where the concrete deal is used in a proof

| file | proof-level use of `orbit_encode` / `code_deal` | over an abstract `e`? |
|---|---|---|
| `pgl27_leakage_census.v` | `code_views`, `pgl27_collisions` mention `code_deal` in their **bodies** only; every lemma about them is a `vm_compute` on a fixed `S` | per-encoding by nature: they are the census numbers |
| `pgl27_table_bridge.v` | `pgl27_code_deal_orbit_encodeE` (`case: b; case: i`), consumed by `pgl27_code_comp_ptblE`, consumed by `pgl27_code_comp_rowE` | yes — the record field `enc_codeE` replaces the case analysis outright |
| `pgl27_view_census.v` | only through `pgl27_code_comp_ptblE` and through `pgl27_view`'s body | yes |
| `pgl27_mutual_info.v` | none in any proof (only in the file header prose) | yes |
| `pgl27_leakage_ramp.v` | `pgl27_subset_class_harmonicE`, `_equianharmonicE` use `orbit_encodeK`; `pgl27_view_mutual_info_imset` passes `orbit_encode` as an argument | the first two have encoding-free **statements** (A0 F8, confirmed); the third is generic already |

### Per-encoding facts the generic theorems must take as premises

The list is short, and every entry is a `vm_compute` fact about the
encoding's nat table at one fixed reveal set `S`:

1. `all (fun x => (x < 8)%N) S` — encoding-free, a fact about `S` alone.
2. `uniq (enc_views e false S)`
3. `uniq (enc_views e true S)`
4. the value `enc_collisions e S = m`

That is all. Everything else the chain needs comes from the record's five
fields. In particular `enc_deck_ok` alone discharges the privacy premise
(Q5), and `enc_codeE` alone discharges the whole table bridge.

Items 2–4 are needed once per (encoding, representative) pair: five
representatives, so ten uniqueness facts and five counts per encoding. These
are the ten specialisations the A0 amendment already moves to R7/R5.

### The hard steps, re-proved over a `Variable e : pgl27_encoding`

`q3_generic_chain.v` re-proves, with the source proof scripts essentially
unchanged (only `code_deal b` -> `enc_code e b`, `orbit_encode b` ->
`enc_deck e b`, `pgl27_view` -> `enc_view e`):

- `enc_code_comp_ptblE`, `enc_code_comp_rowE` (the `pgl27_table_bridge.v`
  core). `Closed under the global context`.
- `enc_view_outside`, `enc_view_codesE`, `enc_code_views_inj`,
  `enc_conditional_view_inj` (the `pgl27_view_census.v` injectivity chain).
- `enc_ambiguous_views`, `enc_support_codesP` (the support characterisation
  that carries the census count into the probability).

`pgl27_view_census.v`'s `map_uniq_inj_in` is `Local` and had to be reproved
(13 lines, verbatim). G1 should make it non-`Local` or keep a copy.

### The convertibility the plan asks about

```rocq
Lemma q0_view_is_coalition_view (R : realType) (C : {set 'I_8}) :
  pgl27_view R C
  = coalition_view (@pgg_rho pgl27_M) (fdist_uniform card_bool) pgl27_G_pos
      orbit_encode C.
Proof. by []. Qed.
```

Compiles, cheaply (`q0_sig.v`). So is
`pgl27_secret R = dealt_secret (fdist_uniform card_bool) pgl27_G_pos`.
The generic target of the plan is therefore the source statement on the nose
at `_r7`, and `pgl27_secrecy.v` need not be touched.

Exact signatures (from `About`):

```
coalition_view [N'] [gT] [G] rho [R] secretP card_G_gt0 encode C
dealt_secret   [gT] [G] [R] secretP card_G_gt0
ttrans_view_indep_gen [N'] [gT] [G] [rho] [t] rhoG_ntrans [R] secretP
                      card_G_gt0 [encode] [C] _ _
coalition_view_mutual_info_le [N'] [gT] [G] rho [R] secretP card_G_gt0
                      encode [C C'] _
```

`encode` and `C` are **implicit** in `ttrans_view_indep_gen`, so it must be
applied in the fully `@`-ed form; the natural-looking
`ttrans_view_indep_gen pgl27_3transitive secretP Hpos enc HC Huniq` is
rejected.

### Assumption floor

`Print Assumptions` in `q3_generic_chain.v`:

- `enc_code_comp_ptblE`: `Closed under the global context`.
- `enc_conditional_view_inj`, `enc_support_codesP`:
  `propositional_extensionality`, `functional_extensionality_dep`,
  `constructive_indefinite_description` — the `boolp` floor that every
  statement typed against an `fdist` already carries. No new axiom.

---

## Q4 — the executed trace at an arbitrary deck. CONFIRMED, no premise.

`q4_trace_enc.v` defines, over `Variable enc : bool -> 8.-tuple 'I_8`,

```rocq
Definition enc_player_trace (i : 'I_8) : {RV (pgl27P R) -> 'I_8} :=
  fun u => content_of (nth [::] (run_interp pgl27_fuel
             (pgl27_procs_deck (enc u.1) u.2)).2 (2 + i)).
```

and proves

| lemma | statement | premise on `enc` | Qed |
|---|---|---|---|
| `enc_player_trace_E` | `= fun u => tnth (enc u.1) (pgg_rho u.2 i)` | **none** | 0.015 s |
| `enc_player_trace_full` | `= [:: PGG_idx 0; PGG_hand [:: … ]]` | **none** | 0.017 s |
| `enc_coalition_trace_E` | `= coalition_view rho (fdist_uniform card_bool) pgl27_G_pos enc C` | **none** | 0.005 s |
| `enc_coalition_trace_secrecy` | `H(secret \| trace C) = H(secret)` for `#\|C\| <= 3` | `forall s, uniq (enc s)` | 0.003 s |

The proofs are the `pgl27_alldecks_trace_E` scripts with `u.2.1 -> enc u.1`
and `u.2.2 -> u.2`; `pgl27_procs_deck_abs` and `pgl27_abs_p0..p7` /
`pgl27_full_p0..p7` apply unchanged, because `pgl27_aprocs_abs` already holds
the card readout abstract. `q4_r7_agrees_with_source` checks that at
`orbit_encode` the new seat trace is `pgl27_player_trace` itself.

Deck validity enters only at the privacy step, and there it is `uniq (enc s)`,
which is `deck_ok` by definition (A0 F4 confirmed).

`content_of`, `pgl27_abs_p*` and `pgl27_full_p*` sit inside
`Section pgl27_trace_sec` with `Variable R : realType`, but none of them
mentions `R`, so section discharge prunes it and they are usable at any `R`.

Termination (A0 F7) is not re-proved here. `pgl27_run_terminates` is stated
about `pgl27_procs s w0`, i.e. `orbit_encode`; the abstract-readout twin
`(run_interp pgl27_fuel (pgl27_aprocs_abs g w0)).1 = nseq 10 Finish` is not in
`pgl27_trace.v`. T1 can add it by the same `vm_compute` — the surrounding
`pgl27_abs_p*` lemmas prove that `vm_compute` does go through at abstract `g`
— but it is a new declaration, not a reuse.

Assumption floor: the three main lemmas carry the `boolp` triple, from
`boolp.funext` used to prove the equality of random variables. No new axiom.

---

## Q5 — threshold privacy at an arbitrary encoding. CONFIRMED.

```rocq
Lemma enc_view_indep (e : pgl27_encoding) (C : {set 'I_8}) : (#|C| <= 3)%N ->
  (fdist_uniform card_bool) `x (`U pgl27_G_pos)
  |= coalition_view (@pgg_rho pgl27_M) (fdist_uniform card_bool) pgl27_G_pos
       (enc_deck e) C
  _|_ @dealt_secret (pgg_gT pgl27_M) (pgg_G pgl27_M) R
        (fdist_uniform card_bool) pgl27_G_pos.
Proof.
move=> HC.
exact: (@ttrans_view_indep_gen (pgg_N' pgl27_M) (pgg_gT pgl27_M)
  (pgg_G pgl27_M) (@pgg_rho pgl27_M) 3 pgl27_3transitive R
  (fdist_uniform card_bool) pgl27_G_pos (enc_deck e) C HC (enc_deck_ok e)).
Qed.
```

The premises the generic theorem asks of the encoding are exactly two, and
one of them is not about the encoding:

1. `#|C| <= 3` — about the coalition.
2. `forall b, uniq (enc_deck e b)` — discharged by the record field
   `enc_deck_ok e`, with no conversion step, because `deck_ok sh := uniq sh`.

`orbit_class`, `enc_classK` and `enc_code` play no part: privacy does not care
which class a deck encodes, only that the two decks have distinct cards. The
3-transitivity `pgl27_3transitive` and the group positivity `pgl27_G_pos` are
encoding-free, as the plan says.

`q5_r5_view_indep` is the `_r5` statement, `exact: enc_view_indep`.
`q5_r7_is_source` re-states `pgl27_secrecy.v`'s `pgl27_view_indep` in the
source's own notation and closes it with `exact: (enc_view_indep enc_r7)`,
so the generic form supersedes rather than duplicates the source lemma.

`enc_view_leakage_le` (monotonicity, `coalition_view_mutual_info_le`) needs no
premise on the encoding at all.

Assumption floor: the `boolp` triple on all three. No new axiom.

---

## Surprises

### 1. A conversion bomb in the "generalised = source" agreement lemmas

This is the one finding that changes how G1 must be written.

```rocq
Lemma conv_views (b : bool) (S : seq nat) :
  gen_views deal_r7 b S = code_views b S.
Proof. by []. Qed.        (* DIVERGES *)
```

Measured: the file `q1b_calibrate_conv.v` ran past 600 s of wall clock with no
progress; `q1c_conv_bisect.v` then pinned it to this lemma with
`Timeout 30 by []` giving `Error: Timeout!`. `gen_collisions`'s agreement has
the same problem.

Cause: `gen_views` and `code_views` have different heads, and ssreflect's
`done` does not find the delta-only path; conversion instead descends into
`pgl27_group_table`, which is a transparent `code_closure 30 [:: code_id]`.
This is not the `done`-evaluates-a-hypothesis bomb from earlier campaigns —
the context here is empty. It is a goal-side conversion bomb.

The route that works, in under 0.01 s:

```rocq
Proof. by rewrite /gen_views /deal_r7 /code_views. Qed.
Proof. by rewrite /gen_collisions /pgl27_collisions !conv_views. Qed.
```

For the record-based forms the same shape works with the projection rewritten
first (`q3_generic_chain.v`):

```rocq
Lemma q3_r7_views b S : enc_views enc_r7 b S = code_views b S.
Proof. by rewrite /enc_views /code_views q2_r7_code. Qed.
```

where `q2_r7_code : enc_code enc_r7 = code_deal` is itself `by []` (small
terms, no table).

**Rule for G1 and R7: never close a statement that has the 336-row table on
both sides with `by []`, `//`, `done` or `exact: erefl`. Unfold the named
definitions with `rewrite /name` until both sides are syntactically equal.**
The cost difference measured here is 0.01 s against divergence.

The same caution applies to the source's own `Local Opaque pgl27_group_table`
at `pgl27_view_census.v:552`: that seal is file-local and does not reach a new
file, so every new file in the chain needs its own.

### 2. `pgl27_collisions` re-evaluates the false-view list 336 times

`count (fun v => v \in code_views false S) (code_views true S)` recomputes
`code_views false S` inside the predicate. It does not matter in practice —
the whole 18-lemma probe costs 3 s of VM time, and after the first lemma
warms the bytecode cache each count is 0.04–0.19 s — but if G1 ever touches
that definition, binding the inner list with a `let` is free (`let` is
definitionally transparent, so the agreement lemmas still hold).

### 3. The record constructor's implicit arguments

Reported under Q2. `@PGL27Encoding` or an `Arguments … : clear implicits`.

### 4. `pgl27_view_census.v`'s `map_uniq_inj_in` is `Local`

G1 must either drop the `Local` or copy the 13-line proof into the
generalised file.

### 5. `orbit_classE` is `Local`

Reported under Q2. It is the reason the `_r5` class recovery has to go through
`heart_set`, and it caps how many encodings can be added without editing
`pgl27_orbit.v` (which the plan forbids).

---

## Risks for the implementation tasks

| risk | severity | mitigation, already evidenced |
|---|---|---|
| G1 closes an agreement lemma with `by []` and the build appears to hang | high, easy to hit | the `rewrite /name` route, Surprise 1 |
| E2 tries to prove `_r5`'s `enc_classK` by computation | medium | the `heart_set` route, Q2 |
| E1 writes the instances without `@` on the constructor | low, fails loudly | Q2 |
| T1 assumes `pgl27_run_terminates` transfers to a new encoding | low | it does not; a new abstract-readout `vm_compute` lemma is needed, Q4 |
| R5 states the minimum above the threshold as `6/7` | medium, a wrong claim would compile | it is `11/14`, on the equianharmonic class; Q1 |
| A statement comment says the ambiguity route needs four or more positions | low | it applies at three too, and gives 0 there; Q1 |
| A third encoding is wanted later | out of scope | it would need `orbit_classE` made non-`Local` |

## Print Assumptions, collected

| lemma | file | result |
|---|---|---|
| `q1_r5_harmonic`, `q1_r5_five`, `q1_r5_uniq_seven`, `gen_collisions_r7E` | q1 | Closed under the global context |
| `enc_r5`, `deck_r5_classK`, `enc_code_nthE` | q2 | Closed under the global context |
| `enc_code_comp_ptblE` | q3 | Closed under the global context |
| `enc_conditional_view_inj`, `enc_support_codesP` | q3 | boolp triple |
| `enc_player_trace_E`, `enc_coalition_trace_E`, `enc_coalition_trace_secrecy` | q4 | boolp triple |
| `enc_view_indep`, `q5_r5_view_indep`, `q5_r7_is_source` | q5 | boolp triple |

"boolp triple" is `propositional_extensionality`,
`functional_extensionality_dep`, `constructive_indefinite_description`, the
floor every `fdist`-typed statement in this repository already sits on. No
probe introduced a new axiom.
