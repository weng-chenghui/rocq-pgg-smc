# A0 — independent audit of the flow sketch, `docs/superpowers/plans/2026-09-18-pgl27-encoding-parameter.md`

Date: 2026-09-18. Auditor: rocq-auditor (Opus), read-only, no compilation.
Method: reading the named files against the sketch, per
`~/.claude/reference/dsl-first-flow-design.md` step 8 ("The procedure") and
"Traps the audit caught". Every finding below carries `file:line` evidence.

## Verdict

**GO-WITH-FIXES.**

The chain is real and the two generic load-bearing lemmas
(`coalition_view_mutual_info_imset`, `coalition_view_mutual_info_le`) are
already stated over an arbitrary `encode`, so the generalisation is a genuine
generalisation and not a rename. The executed-run layer is already
deck-generic. The `_r5` deck is a valid deck with the same heart positions as
`orbit_encode true`, and its collision profile is backed by the committed
script.

Nine fixes are required before implementation. Two of them (F1, F2) are
claims in the plan that the files contradict; the rest are missing premises,
missing lines, and name corrections.

---

## Question 1 — does every named lemma exist with the statement the sketch claims?

The sketch names eight things. Actual names and statements:

| sketch token | real name | file:line | status |
|---|---|---|---|
| `pgl27_procs_deck` | `pgl27_procs_deck` | `instances/pgl27/pgl27_run.v:100` | exact |
| `pgl27_procs_deck_abs` | `pgl27_procs_deck_abs` | `instances/pgl27/pgl27_trace.v:448` | exact |
| `pgl27_full_p0..p7` | `pgl27_full_p0` … `pgl27_full_p7` | `instances/pgl27/pgl27_trace.v:163,174,185,196,207,218,229,240` | exact |
| `coalition_trace_E` | **`pgl27_coalition_trace_E`** | `instances/pgl27/pgl27_trace.v:416` | **name approximate — see F3** |
| `ttrans_view_indep_gen` | `ttrans_view_indep_gen` | `reconstruct/transitivity_privacy.v:674` | exact, but wrong premise named — see F4 |
| `pgl27_view_mutual_info_ambiguityE` | `pgl27_view_mutual_info_ambiguityE` | `instances/pgl27/pgl27_mutual_info.v:247` | exact, but **not generic in `e`** — see F5 |
| `coalition_view_mutual_info_imset` | `coalition_view_mutual_info_imset` | `reconstruct/coalition_view_transport.v:55` | exact, generic in `encode` |
| `centropy1_uniform_over_set` (interfaces line) | **not verified** — see "unanswered" |
| `pgl27_aprocs_endpoints` | `pgl27_aprocs_endpoints` | `instances/pgl27/pgl27_trace.v:258` | exact |

Everything else in the interfaces paragraph resolves:
`pgl27_table_bridge.v` exists and its bridge lemma is
`pgl27_code_deal_orbit_encodeE` (`instances/pgl27/pgl27_table_bridge.v:178`)
plus `pgl27_code_comp_ptblE` (`:187`) and `pgl27_code_comp_rowE` (`:202`).

## Question 2 — does every step's cost match the lemma statement?

Every line of the sketch claims cost zero and an exact equality. Checked:

- `pgl27_coalition_trace_E` is an equality of random variables
  (`pgl27_trace.v:416-417`) — zero, exact. Correct.
- `ttrans_view_indep_gen` is an independence statement, converted to the
  value zero by `mutual_info_RVE` + `inde_cond_entropy` in
  `pgl27_leakage_ramp.v:216-218`. Zero, exact. Correct.
- `pgl27_view_mutual_info_ambiguityE` is an equality
  (`pgl27_mutual_info.v:251-252`). Zero, exact. Correct.
- `coalition_view_mutual_info_imset` is an equality
  (`coalition_view_transport.v:57-60`). Zero, exact. Correct.
- **The `|C| = 8` line is NOT an equality chain.** It is an
  antisymmetry argument: `le_anti` applied to `pgl27_view_mutual_info_le1`
  (a **bound**, `pgl27_leakage_ramp.v:282`, proved from
  `mutual_info_RV_le_entropy`, `:204`) and `pgl27_view_leakage_le`
  (a **bound**, `pgl27_secrecy.v:98`). See `pgl27_leakage_ramp.v:291-302`.
  This is the "some hop lemmas are equalities, not bounds" trap in reverse:
  one line of the sketch is two bounds that meet, and the sketch labels it
  as if it were an equality. See F6.

## Question 3 — does the composition typecheck at the endpoints?

**(a) `pgl27_view R C` convertible to the generic `coalition_view`.** YES.

`coalition_view` is
`fun u => [ffun i => if i \in C then tnth (encode u.1) (rho u.2 i) else ord0]`
over `P := secretP `x (`U card_G_gt0)`
(`reconstruct/transitivity_privacy.v:493-495`, `:487`).
`pgl27_view` is the same term with `encode := orbit_encode`,
`rho := @pgg_rho pgl27_M`, `secretP := fdist_uniform card_bool`
(`instances/pgl27/pgl27_secrecy.v:75-77`, `pgl27P` at `:66-67`).
The conversion is already exercised twice by `exact:` with no intervening
rewrite: `pgl27_secrecy.v:86-88` and `pgl27_leakage_ramp.v:187-189`.
So generalising over `enc : bool -> 8.-tuple 'I_8` is a real generalisation of
the `encode` slot the framework already has, not a new abstraction.

Supporting fact: `@pgg_rho pgl27_M` is the *identity* morphism
(`protocol/pgg_interface.v:441-450`, `gen_incl_morph := Morphism
gen_incl_morphM` with underlying map `@id gT`), which is why
`pgl27_leakage_ramp.v:184` can write `g @: C` where the generic lemma writes
`rho g @: C`.

**(b) `coalition_view_mutual_info_imset` generic in `encode`.** YES.
`Variable encode : bool -> N'.+1.-tuple 'I_N'.+1`
(`reconstruct/coalition_view_transport.v:44`), and the theorem's statement
(`:55-60`) carries `encode` as a parameter with **no** hypothesis on it —
no `uniq`, no `deck_ok`, no class-recovery. The transport step is therefore
unconditionally generic in the encoding. Same for
`coalition_view_mutual_info_le` (`reconstruct/transitivity_privacy.v:719-723`,
`encode` declared at `:582`, no hypothesis).

**(c) Is the executed run really generic in the dealt deck?** YES, and more
generic than the sketch says.

- `pgl27_procs_deck (sh : 8.-tuple 'I_8) (w0 : pgg_gT pgl27_M)`
  (`pgl27_run.v:100-101`) takes an arbitrary deck.
- `pgl27_procs_deck_abs sh w0 : pgl27_procs_deck sh w0 = pgl27_aprocs_abs
  (tnth sh) w0` is `Proof. by []. Qed.` (`pgl27_trace.v:448-450`) —
  definitional at an arbitrary `sh`.
- `pgl27_full_p0..p7` and `pgl27_aprocs_endpoints` live in an abstract-leaf
  section over `Variable g : 'I_8 -> 'I_8` and are proved
  `rewrite /pgl27_aprocs_abs; vm_compute; reflexivity`
  (`pgl27_trace.v:163-249`, `:258-270`). The card values are held abstract,
  so these carry to any deck with no re-computation.

**What `pgl27_coalition_trace_E` uses that is specific to `orbit_encode`:**
exactly one step, `pgl27_procs_abs`
(`pgl27_trace.v:277-279`): `pgl27_procs s w0 = pgl27_aprocs_abs (tnth
(orbit_encode s)) w0`, `Proof. by []. Qed.`. It is definitional and its
deck-generic twin already exists as `pgl27_procs_deck_abs`. The chain
`pgl27_coalition_trace_E` (`:416`) → `pgl27_player_trace_E` (`:322`) →
`pgl27_procs_abs` + the abstract `pgl27_abs_p*` is therefore generic once
`pgl27_procs` is replaced by `pgl27_procs_deck (enc s)`. **No `vm_compute`
has to be redone per encoding on this path.** See F7 for the one thing that
does have to be restated.

**(d) Steps that use per-encoding computed facts** (these must become record
premises or per-encoding lemmas — the plan's G1/R7/R5 split must respect
this list):

1. **View uniqueness at the five representatives.**
   `pgl27_views_uniq_harmonic/_equianharmonic/_five/_six/_seven`
   (`pgl27_leakage_census.v:424-458`), each `Proof. by vm_compute. Qed.`
   They are per-encoding: `code_views b S` is built from `code_deal b`
   (`:410-411`, `:405`). Five new `vm_compute` facts per encoding.
2. **Per-secret injectivity `pgl27_conditional_view_inj`.**
   `pgl27_view_census.v:175-177` takes
   `all (fun x => (x < 8)%N) S -> uniq (code_views b S)` as premises, so the
   *general* lemma is already parametric in `S` and will generalise over the
   deal with no new computation. Its five specialisations
   (`pgl27_conditional_view_inj_harmonic` … `_seven`,
   `pgl27_view_census.v:206,223,241,258,275`) each discharge
   `by vm_compute` + the uniqueness fact, so they are per-encoding.
3. **Collision counts.** `pgl27_collisions_harmonic = 96` etc.
   (`pgl27_leakage_census.v:460-497`), all `by vm_compute`. Five per
   encoding. The three-position count `pgl27_collisions [:: 0;1;2] = 336`
   (`:486`) is also per-encoding.
4. **The nat/tuple agreement.** `pgl27_code_deal_orbit_encodeE`
   (`pgl27_table_bridge.v:178-182`), `by case: b; case: i => ...` — sixteen
   cases, mechanical, one per encoding. This is exactly the plan's proposed
   record field "agreement". Correct shape.
5. **Class recovery.** `orbit_encodeK` (`pgl27_orbit.v:359-360`,
   `by case: s; rewrite orbit_classE; vm_compute`) and deck validity
   `orbit_encode_deck` (`:364-365`). Per encoding. Correct: both are
   proposed record fields.

**NOT per-encoding** (must stay in the shared file, not be duplicated per
instance): `pgl27_subset_class_harmonicE` and
`pgl27_subset_class_equianharmonicE` (`pgl27_leakage_ramp.v:143,156`) are
statements about `subset_class` alone — no encoding occurs in either
statement. Their *proofs* route through `heart_set (orbit_encode b)` and
`orbit_encodeK`, which is an accident of convenience. Likewise
`pgl27_leak_coalitionE` (`:170-175`) is encoding-free in both statement and
proof. See F8.

**(e) The monotonicity / `|C| = 8` / `|C| >= 7` steps.**

- `pgl27_view_mutual_info_k8E` (`pgl27_leakage_ramp.v:291-302`) is
  **shape-generic but instance-parametrised**: it needs *some*
  representative whose value is already 1. For `_r7` that is
  `pgl27_view_mutual_info_sevenE` (`:300`); for `_r5` it can be the
  five-position one. The proof shape (`le_anti`, `le1`, `leakage_le`,
  `subsetT`) carries unchanged.
- `pgl27_view_mutual_info_ge7E` (`:307-315`) **is r7-specific**: the
  threshold 7 and the `eqVneq #|C| 7` split are the `_r7` numbers. For `_r5`
  the analogue is a `ge5E` with the split at 5 and a three-way collapse
  (5, 6, 7, 8 all give 1). The sketch has no line for this step at all;
  it is folded into the `|C| = 8` line. See F6.
- `pgl27_view_mutual_infoE` (`:326-333`) has a **different arity of cases**
  per encoding: `_r7` needs five branches (≤3, =4, =5, =6, else), `_r5`
  needs three (≤3, =4, else). The sketch's single `final` line hides this.
- The `|C| <= 3` step depends on the encoding **only through deck validity**.
  `ttrans_view_indep_gen` (`reconstruct/transitivity_privacy.v:674-676`)
  takes `(forall b, uniq (encode b))` and nothing else about `encode`.
  So: no, the `|C| <= 3` step does not depend on the encoding beyond deck
  validity. The sketch is right on this line, modulo the premise name (F4).

## Question 4 — does anything the sketch calls a step live outside the flow?

- **`object census := collisions of e over the 336-row table` (line 38) is
  not an object of the flow.** The flow's objects are random variables over
  `pgl27P R`. `pgl27_collisions S : nat`
  (`pgl27_leakage_census.v:417-418`) is a natural number computed from
  `pgl27_group_table`, with no probability space in sight. It enters the flow
  by *pre-composition*, through the named interface
  `pgl27_ambiguous_probabilityE` (`pgl27_view_census.v:737`) which converts
  the count into `Pr[ambiguous view]`. The sketch's `object` marking is
  wrong; it should be marked as an external component entering by
  pre-composition. See F9.
- **`pgl27_table_bridge.v` enters at two places.** It is the interface for
  the census→view step (sketch line 39) *and* it is what makes
  `pgl27_conditional_view_inj` (`pgl27_view_census.v:175`, proved via
  `pgl27_view_codesE` at `:153` which calls `pgl27_code_comp_ptblE`)
  work, which the sketch attributes to line 40. Per the reference's step 7,
  "a component that enters at more than one place is a sign the flow was cut
  in the wrong place". Not fatal, but the sketch should name it once, at the
  census→view line, and say that the representative-evaluation line consumes
  it too.

---

## The `_r5` deck check (asked separately)

**Which definition decides what a "heart" card is:**
`is_heart (c : 'I_8) : bool := (val c < 4)%N`
— `instances/pgl27/pgl27_orbit.v:90`.
The heart *positions* of a deck are
`heart_set (sh) := [set i | is_heart (tnth sh i)]` — `pgl27_orbit.v:98-99`,
and `orbit_class sh := subset_class (heart_set sh)` — `pgl27_orbit.v:112-113`.

**Validity.** `deck_ok (sh) := uniq sh` — `pgl27_orbit.v:94`.
`0 1 2 4 3 5 7 6` is a permutation of `0..7`, hence `uniq`, hence a valid
deck. Confirmed by reading only; no computation needed.

**Heart positions.** With `is_heart c = (val c < 4)`:
`0 1 2 4 3 5 7 6` places cards `0,1,2,3` at positions `0,1,2,4`, so
`heart_set = {0,1,2,4}`.
`orbit_encode true = [0;1;2;4;3;5;6;7]` (`pgl27_orbit.v:349-353`) places
`0,1,2,3` at positions `0,1,2,4`, so `heart_set = {0,1,2,4}`.
**The heart positions coincide.** Since `orbit_class` factors through
`heart_set`, `orbit_class (enc_r5 true) = orbit_class (orbit_encode true) =
true` by `orbit_encodeK` (`pgl27_orbit.v:359`). The plan's class-recovery
field is therefore discharged for `_r5` without any new `vm_compute` on the
cross-ratio: it reduces to a `heart_set` equality. Worth telling E2.

Independent corroboration from the committed script:
`notes/probes/2026-09-18-pgl27-encoding-dependence/simplest_pairs.out:22`
lists `D_true = (0, 1, 2, 4, 3, 5, 7, 6)` under "curve D" with
`heart positions [0, 1, 2, 4]`, and
`simplest_pairs.py:6` maps curve D to the profile `(48,72,0,0,0)`, which
`encodings.out:9` prices at `['6/7', '11/14', '1', '1', '1']` with
`recovery threshold r = 5`. **The plan's `_r5` row is backed.**

---

## Numbered findings and fixes

### F1 (blocking, plan task C1). "possibilistic r = 7 for both" is false at the fixed-pair dealer.

`docs/superpowers/plans/2026-09-18-pgl27-encoding-parameter.md:87`.

At a fixed deck pair, "the view determines the secret class" is exactly
"no view is shared by the two deals", i.e. `pgl27_collisions S = 0`. For
`_r5` the collision counts at sizes 5, 6 and 7 are all `0`
(`notes/probes/2026-09-18-pgl27-encoding-dependence/encodings.out:9`), so the
possibilistic recovery threshold of `_r5` is **5, not 7**. `r_info` and the
possibilistic `r` are the *same* number in this framework, because
`I = 1 - m/336` equals 1 exactly when `m = 0`; the script computes `r` from
`m = 0` and calls it the recovery threshold
(`notes/probes/2026-09-18-pgl27-encoding-dependence/encodings.py:55-58`).

The claim is true only under the **all-decks** dealer, where the statement is
`pgl27_seven_reveal_class` (`instances/pgl27/pgl27_recovery.v:68-71`): any two
valid decks agreeing off one position have the same class. That lemma is
encoding-free and holds for both instances, which is presumably what was
meant. The paper uses the all-decks reading
(`paper-wadt2026/main.tex:1322`; `paper-wadt2026/analysis/
shinagawa21-paragraph-baseline.tex:1141`, "$r=7$ is a structural property of
the arrangements").

**Fix.** Rewrite C1's third clause as: "the all-decks seven-reveal recovery
`pgl27_seven_reveal_class` is encoding-free and holds for both; at the
fixed-pair dealer the recovery threshold is 7 for `_r7` and 5 for `_r5`, the
same number as `r_info`." And drop `r_info` as a separate name, or state in
the Problem section that `r_info` *is* the possibilistic recovery threshold
of the fixed pair.

### F2 (blocking, plan task R5 and sketch line 42). The `ge4` constant flips class for `_r5`.

`pgl27_leakage_ramp.v:384-392` proves
`pgl27_view_mutual_info_ge4 : 4 <= #|C| -> 5%:R / 7%:R <= I`.
For `_r7` the minimum above the threshold is the **harmonic** value `5/7`,
because `5/7 < 11/14`. For `_r5` the two size-4 values are `6/7` (harmonic)
and `11/14` (equianharmonic), and `11/14 < 12/14 = 6/7`, so the minimum above
the threshold is the **equianharmonic** value `11/14`. The class carrying the
smallest leakage swaps sides.

This also invalidates, for `_r5`, the statement-comment pattern at
`pgl27_leakage_ramp.v:220-224` ("eleven fourteenths … the larger of the two
values") and `:139-142` ("five sevenths … the smaller of the two").

**Fix.** R5's row must say `ge4` constant `11%:R / 14%:R`, at the
equianharmonic class, and the R5 file's statement comments must not be copied
from `_r7`. Add one line to the sketch's `post` section:
`post  which class carries the minimum above the threshold (harmonic for r7, equianharmonic for r5)`.

### F3 (name). `coalition_trace_E` → `pgl27_coalition_trace_E`.

Sketch line 35. Real name at `instances/pgl27/pgl27_trace.v:416`.
**Fix.** Rename in the sketch. Also note it is stated as an equality of
random variables (`pgl27_coalition_trace C = pgl27_view R C`), not as a
distributional identity, which is stronger and worth saying on the line.

### F4 (premise). `ttrans_view_indep_gen` needs `uniq (encode b)`, not `deck_ok (e s)`.

Sketch line 36 annotates `[needs deck_ok (e s)]`.
The real premise is `(forall b, uniq (encode b))` —
`reconstruct/transitivity_privacy.v:675`. The repo happens to define
`deck_ok sh := uniq sh` (`instances/pgl27/pgl27_orbit.v:94`), so
`orbit_encode_deck` is accepted directly at `pgl27_secrecy.v:88`. The two
coincide *today*, by a definitional unfolding that nothing in
`transitivity_privacy.v` knows about.

**Fix.** Write the premise as `uniq (e s)` on the sketch line, and note that
the record's `deck_ok` field discharges it only because
`deck_ok = uniq` definitionally. If E1's record states validity as
`deck_ok (enc s)` rather than `uniq (enc s)`, add a one-line coercion lemma
so the dependence on that definitional accident is visible.

### F5 (missing work, sketch line 39). `pgl27_view_mutual_info_ambiguityE` is *not* generic in `e` today.

Sketch line 39 says "generic in e". The lemma
(`instances/pgl27/pgl27_mutual_info.v:247-252`) is stated over
`pgl27_view R (pgl27_code_coalition S)`, which fixes `orbit_encode` inside
`pgl27_view` (`pgl27_secrecy.v:77`), and it consumes
`pgl27_ambiguous_probabilityE` (`pgl27_view_census.v:737`) and
`pgl27_secret_uniform` (`pgl27_mutual_info.v:236`), neither of which is
encoding-parametric. Generic in `e` is the *goal* of G1, not a property of
the file.

**Fix.** Annotate the line `by pgl27_view_mutual_info_ambiguityE, generalised
over e in G1` so the sketch does not read as a statement about the current
tree. Same for lines 38 and 40, where `pgl27_ambiguous_probabilityE` and the
`_harmonic`/`_five`/… specialisations are all `orbit_encode`-fixed today.

### F6 (missing line, sketch lines 41-42). Two bounds meeting are drawn as one equality, and the `>= 7` step has no line.

`pgl27_view_mutual_info_k8E` (`pgl27_leakage_ramp.v:291-302`) is
`le_anti` over `pgl27_view_mutual_info_le1` (a bound, `:282`) and
`pgl27_view_leakage_le` (a bound, `pgl27_secrecy.v:98`). And
`pgl27_view_mutual_info_ge7E` (`:307`) is a separate step whose threshold is
`_r7`-specific (see Q3(e)).

**Fix.** Replace the single line 41 with two:
```
join   |C| >= r(e)    by monotonicity from the top representative        // I = 1; r7: 7, r5: 5
join   |C| = 8        by le_anti of le1 and leakage_le                   // the only line where two BOUNDS meet
```
and mark the second line as the one non-equality step, so the sketch's own
"every line is unconditional and costs zero" claim in the Monad verdict is
not contradicted by the file.

### F7 (missing obligation, plan task T1). There is no deck-generic termination lemma.

`pgl27_run_terminates` (`instances/pgl27/pgl27_run.v:105-107`) is stated only
for `pgl27_procs s w0` and proved `by vm_compute`. There is no
`pgl27_procs_deck` twin, and none at abstract readout. The `pgl27_full_p*`
lemmas dodge this because they are stated at abstract `g` and close by
`vm_compute; reflexivity` on the trace skeleton
(`pgl27_trace.v:169`), so the flow itself does not need termination — but any
`_r5` claim phrased as "the run terminates and yields …" does.

**Fix.** T1 should add `pgl27_aprocs_terminates (g : 'I_8 -> 'I_8) (w0 : ...)`
at abstract readout, proved by the same `vm_compute`, and derive both
instances from it — or the plan should state explicitly that termination is
not re-claimed per encoding.

### F8 (scope, plan tasks G1/R7/R5). Three lemmas are encoding-free and must not be duplicated per instance.

`pgl27_subset_class_harmonicE` (`pgl27_leakage_ramp.v:143-150`),
`pgl27_subset_class_equianharmonicE` (`:156-164`) and
`pgl27_leak_coalitionE` (`:170-175`) have no `encode` in their statements.
The first two are proved *via* `orbit_encode` and `orbit_encodeK` only
because that was the shortest route; their content is a `subset_class` fact
about `{0,1,2,3}` and `{0,1,2,4}`.

**Fix.** Move all three into the shared generic file that G1 produces (or a
small `pgl27_subset_class_reps.v`), proved directly by
`rewrite /subset_class; vm_compute`, not reproved in `pgl27_leakage_r7.v`
and `pgl27_leakage_r5.v`. Otherwise R5 inherits an `orbit_encode`-routed
proof for a statement that has nothing to do with `_r5`.

### F9 (sketch role, line 38). `census` is not an object of the flow.

`pgl27_collisions S : nat` (`pgl27_leakage_census.v:417-418`) lives outside
the probability space. It is an external component entering by
pre-composition through `pgl27_ambiguous_probabilityE`
(`pgl27_view_census.v:737`).

**Fix.** Change `object census := …` to
`extern census := collisions of e over the 336-row table   [enters by pre-composition through pgl27_ambiguous_probabilityE]`
and keep the running-total comment on that line at the value it had before,
since a pre-composition costs nothing.

---

## Plan task table audit

**Dependency order.** Correct as drawn, with one addition: **R7 and R5
depend on F8's shared file**, and **C1 depends on E2 directly** (it compares
the two encodings' heart positions, which are record fields, not results of
R7/R5). Also `G1` lists four files to generalise but omits the two extra
per-encoding `vm_compute` facts in `pgl27_view_census.v`
(`pgl27_conditional_view_inj_*`, `:206-289`) and
`pgl27_ambiguous_probability_*E` (`:754-825`) — those are ten specialisations
that must move to R7/R5, not stay in G1's files.

**Expensive downstream importers.** Checked with
`grep -rn --include='*.v' --exclude-dir=notes --exclude-dir=.claude` and
`.Makefile.rocq.d`:

- **`pgl27_leakage_ramp.v` has no importer at all.** It is a leaf; nothing
  in the tree `Require`s it. Renaming it to `pgl27_leakage_r7.v` breaks
  nothing in `.v`, only `_CoqProject:187`.
- `pgl27_leakage_census.v` is imported by `pgl27_table_bridge.v:37`,
  `pgl27_view_census.v:48`, `pgl27_mutual_info.v:56`,
  `pgl27_leakage_ramp.v:75`. Nothing else.
- `pgl27_table_bridge.v` is imported by `pgl27_view_census.v:49` only —
  **but it imports `pgl27_mixing`** (`pgl27_table_bridge.v:37`), which is on
  the do-not-edit list and is the tree's most expensive file
  (1104 lines, 237 KB `.vo`). `.Makefile.rocq.d` confirms
  `pgl27_table_bridge.vo: … instances/pgl27/pgl27_mixing.vo …`.
  So every G1/R7/R5 target transitively closes over `pgl27_mixing.vo`,
  `pgl27_secrecy.vo` and `pgl27_orbit.vo`.
  **This makes the plan's build rule at `:58-61` unsatisfiable as written**
  ("if it lists anything under … `pgl27_mixing`, `pgl27_secrecy`,
  `pgl27_orbit`, `pgl27_trace`, STOP"). It only works today because those
  `.vo` files are newer than their `.v` files, so `make -n` prints nothing
  for them.
  **Fix.** Reword to "if `make -n` shows any *recipe* for a file under … ,
  STOP" — the rule is a staleness tripwire, not a closure ban.
- `manifest/pgg_analysis_manifest.v` and `manifest/pgg_analysis_client.v`
  reference `PGL27Analysis.coalition_trace` and
  `PGL27Analysis.coalition_trace_secrecy`
  (`manifest/pgg_analysis_client.v:95`,
  `manifest/pgg_analysis_manifest.v:878,943,994,1010,1056`), which alias
  `pgl27_coalition_trace` / `_secrecy` via `instances/pgl27/pgl27_analysis.v:141,272`.
  **T1 must not change the existing `pgl27_coalition_trace`**; it must add a
  new encoding-parametric one alongside. The plan does not say this.

**Rename / parametrisation blast radius** (greps over
`paper-wadt2026-baseline-application/`, `notes/`, `docs/`, `blueprint*`):

- `pgl27_leakage_ramp`: `_CoqProject:187`,
  `docs/superpowers/plans/2026-09-17-pgl27-entropy-completion.md`,
  and the file itself. **No paper, no blueprint, no manifest.** Safe rename.
- `pgl27_collisions`: `pgl27_view_census.v`, `pgl27_mutual_info.v`,
  `pgl27_leakage_census.v`, `instances/pgl27/pgl_leakage_targets.py`,
  `docs/superpowers/plans/2026-09-17-pgl27-entropy-completion.md`, **and the
  paper**: `paper-wadt2026/main.tex:1379-1382` cites
  `\coqin{pgl27\_collisions}` by name, and
  `paper-wadt2026-baseline-application/candidate-main.tex:1430` repeats it.
  Adding an argument (`pgl27_collisions D S`) keeps the *name* valid but
  changes every cited statement's arity.
  **Fix.** D1's "old/new name table for the paper footnotes" must cover the
  arity change, not only renames. Also `pgl_leakage_targets.py` consumes the
  name and should be updated or annotated.
- `pgl27_mutual_info`, `pgl27_view_census`, `pgl27_table_bridge`,
  `pgl27_leakage_census`: `_CoqProject:183-186` plus the two plan docs;
  `pgl27_leakage_census.v` additionally at `paper-wadt2026/main.tex:1379` and
  `candidate-main.tex:1430` as a **file path**. Keep those four file names.
- No `blueprint*` file exists in the tree; nothing to update there.

**Pre-existing paper staleness surfaced by this audit** (not caused by the
plan, but D1 should record it): `paper-wadt2026/main.tex:1397-1399` says
extending each leakage value from its representative to the whole orbit is
"a pen-and-paper step that the development does not formalize". It is now
formalized — `pgl27_view_mutual_info_imset` (`pgl27_leakage_ramp.v:182`) and
`pgl27_view_mutual_infoE` (`:326`). Similarly `:1385-1388` attributes
`I = 1 - m/336` to a pen-and-paper step; it is
`pgl27_view_mutual_info_ambiguityE` (`pgl27_mutual_info.v:247`).

**Is the proposed record shape sufficient for every generic step?**
The proposed fields are decks, deck validity, class recovery
`orbit_class (enc s) = s`, nat table, agreement. Sufficient for:
`ttrans_view_indep_gen` (needs validity, F4),
`coalition_view_mutual_info_imset` and `_le` (need nothing),
`pgl27_run_recovers_class` (needs class recovery and
`orbit_class_invariant`, which is encoding-free —
`pgl27_orbit.v:289`), the table bridge (needs the nat table + agreement),
and the executed-run layer (needs nothing).
**Two fields are missing:**

1. **`uniq` of the nat table row**, or a proof that the nat table is a
   permutation of `iota 0 8`. Without it, `code_comp t (nat_table b)` is not
   guaranteed to have size 8, which `pgl27_code_comp_ptblE`'s
   `Hsize` step needs (`pgl27_table_bridge.v:192-194`). It follows from
   agreement + deck validity, so it can be a derived lemma rather than a
   field — but it must be stated.
2. **Nothing forces `enc false ≠ enc true` or that the two classes differ.**
   Class recovery `orbit_class (enc s) = s` does force it (at `s = false`
   and `s = true` the classes differ), so this is covered. Good.

The five per-representative `uniq (code_views b S)` facts are deliberately
*not* record fields (they differ per representative, not per encoding alone)
and correctly belong in R7/R5. The plan is right to put them there.

---

## Audit questions I could NOT answer

1. **`centropy1_uniform_over_set` inside `lib/support_posterior.v`.**
   I did not read `lib/support_posterior.v` or
   `lib/mutual_info_recoding.v`. The sketch's interfaces paragraph
   (`plan:50-52`) names `centropy1_uniform_over_set` as the infotheo entry
   point; `pgl27_mutual_info.v:159` in fact routes through
   `support_posterior_entropy_ambiguousE` and `:264` through
   `mutual_info_binary_ambiguityE`. Whether `centropy1_uniform_over_set`
   exists under that name, and whether it is the right thing to name as the
   interface, is **unverified**.
2. **Whether `uniq (code_views b S)` actually holds for the `_r5` deck** at
   the five representatives. The committed script uses Python **sets**
   (`encodings.py:33`, `views = lambda D, S: {…}`), which silently dedupe, so
   the script's `(48, 72, 0, 0, 0)` is a set-intersection size and carries
   **no** evidence about repetition-freeness. `pgl27_view_mutual_info_ambiguityE`
   (`pgl27_mutual_info.v:247-250`) needs `uniq` for **both** secrets at each
   representative, and without it the `_r5` closed form is not established.
   The plan's P0 does list this; I flag that the script cannot substitute.
3. **Whether the `_r5` collision counts match `pgl27_collisions`' definition.**
   `pgl27_collisions S := count (fun v => v \in code_views false S)
   (code_views true S)` (`pgl27_leakage_census.v:417-418`) is a multiplicity
   count, equal to the set-intersection size only under (2). Same caveat.
4. **Whether `pgl27_analysis.v` / `manifest/` re-export anything from
   `pgl27_mutual_info.v` or `pgl27_leakage_ramp.v`.** I grepped for
   `leakage_ramp`, `view_mutual_info` and `noncollision` in `manifest/` and
   `pgl27_analysis.v` and found nothing, but I did not read
   `pgl27_analysis.v` (363 lines) in full.
5. **Section-variable scope of `pgl27_full_p*` and `pgl27_aprocs_endpoints`.**
   I confirmed they are non-`Local` `Lemma`s over `Variable g`/`w0` in an
   `abstract_leaf` section (`pgl27_trace.v:163-249`, `End abstract_leaf.`
   at `:250`), and that `pgl27_player_trace_full` applies them with explicit
   arguments (`:361-375`), but I did not check whether the *enclosing*
   section carries a `Variable R : realType` that would add a dummy argument
   for a new file. Low risk; T1 should check.
6. **`vm_compute` cost of the ten new per-representative facts for `_r5`.**
   Not measurable read-only. The existing ones are `by vm_compute` over a
   336-row transparent closure (`pgl27_leakage_census.v:244`), and the file
   header warns that "PGL(2,7) permutations do not reduce under vm_compute,
   tables do" (`:25-27`). P0 should time one before R5 commits to ten.
