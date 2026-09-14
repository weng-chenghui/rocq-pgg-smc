# PSL(2,11) twelve-card chirality — probe run report

Date: 2026-09-14. Rocq 9.0, MathComp 2.5, infotheo, repo
`/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc`, branch `feat/tableau-syntax`.
Probe directory: `notes/probes/2026-09-14-psl211/`.
Spec under probe: `notes/2026-09-14-003000-psl211-chirality-instance-proposal.md`,
sections 5, 7 (claim ledger L1..L17), 8.

`run.sh` was correct as delivered and is unchanged. Every file below compiles
with `sh run.sh <file>` from the probe directory, exit 0.

## Compilation status

| file | Admitted | wall clock | verdict |
|---|---|---|---|
| `probe_group.v` | 0 | 3.45 s | compiles |
| `probe_orbit.v` | 0 | 75.63 s | compiles |
| `probe_bridge.v` | 0 | 4.02 s | compiles |
| `probe_mixing.v` | 0 | 13.90 s | compiles |
| `probe_decomposition.v` | 15 (by design) + 0 unintended | 4.03 s | compiles |

`probe_decomposition.v` keeps exactly the Admitted supports the brief names,
minus one: `psl211_PI` is now a real definition (see C7 and L13 below).

---

## Ledger verdicts

| # | verdict | evidencing name | file |
|---|---|---|---|
| L1 | **GO** | `psl211_N'`, `psl211_gens_in_G`, `Fail Definition bad_N`, `Fail Definition bad_T` | `probe_group.v` |
| L2 | **GO** | `r4_inj`, `m6_inj`, `r4_permE`, `m6_permE`, `m6_inv_permE` | `probe_group.v` |
| L3 | **GO** | `design5_okA`, `design5_okB`, `design5_mut` | `probe_orbit.v` |
| L4 | **GO** | `stable_r4A`, `stable_r4B`, `stable_m6A`, `stable_m6B`, `stable_rev12A_false` | `probe_orbit.v` |
| L5 | **GO** | `setsA_invariant`, `setsB_invariant`, `setsA_B_disjoint` | `probe_orbit.v` |
| L6 | **GO** | `count_okT` (38.7 s, target was < 5 min), `count_ok5_mut_false` | `probe_orbit.v` |
| L7 | **GO** | `leak6` | `probe_orbit.v` |
| L8 | **GO** | `uniform_fdistmap_of_fibres` (statement fix C2) | `probe_bridge.v` |
| L9 | **GO** | `colour_view_indep_of_laws`, `colour_view_indep_of_fibres` | `probe_bridge.v` |
| L10 | **GO** | `orbit_fibre_card` (statement fix C3) | `probe_bridge.v` |
| L11 | **GO (statement only, as the ledger asks)** | `setsA_orbitE` typechecks, proof deferred | `probe_decomposition.v` |
| L12 | **split: NO-GO on the miniature, GO on the full shape** | `redeal_mini_false` (counter-probe), `redeal_mini_family` (repaired), `psl211_private` | `probe_bridge.v`, `probe_decomposition.v` |
| L13 | **GO, and stronger than claimed** | `orbit_scheme`, `psl211_plug`, `psl211_PI`, `psl211_profile`, `orbit_recon_invariant` | `probe_decomposition.v` |
| L14 | **GO** | `size_elem_table`, `uniq_elem_keys`, `elem_closed_okT`, `size_closure_r4` | `probe_mixing.v` |
| L15 | **GO, roughly 10x cheaper than the spec estimates** | `walk100_total` plus the L = 200/300/400 curve in `scratch_walk_scaling.v` | `probe_mixing.v` |
| L16 | **GO (statements only)** | `psl211_eleven_reveal_class`, `psl211_ten_reveal_ambiguous` typecheck | `probe_decomposition.v` |
| L17 | **GO (statement only)** | `psl211_card` typechecks, proof deferred | `probe_decomposition.v` |

### L1 — mutation checks read

Both `Fail Definition` lines fail for the reason the ledger intends, confirmed
by compiling `scratch_mut_badN.v` and `scratch_mut_badT.v`, which are
`probe_group.v` with the `Fail` removed:

```
scratch_mut_badN.v, line 58:
Error: The term "psl211_gens" has type "2.-tuple {perm 'I_12}"
       while it is expected to have type "2.-tuple {perm 'I_11}".

scratch_mut_badT.v, line 59:
Error: The term "psl211_gens" has type "2.-tuple {perm 'I_12}"
       while it is expected to have type "3.-tuple {perm 'I_12}".
```

`@Gen_PGGTypes 1 9` is rejected on the position count (`N := n.+2`, so 11 not
12) and `@Gen_PGGTypes 2 10` on the generator count (`T := m.+1`, so 3 not 2).
Neither is a spurious failure from an unrelated elaboration problem.

### L12 — NO-GO on `redeal_mini`, with counter-probe

`redeal_mini` as written is **false**. `&&` binds tighter than `\/`, so the
first disjunct pins `S' = SB` and the second pins `S' = SA`; under that pinning
both disjuncts reduce to the same condition `(i \in SB) = (i \in SA)`, and with
`SA = {0,1}`, `SB = {0,2}` that condition fails at `i = 1` and at `i = 2`. The
comment above the toy ("sharing the point pattern counts for every
1-coalition") is wrong for the same reason: one block per class cannot match
1-point counts unless the blocks are equal.

Smallest counter-probe, Qed in `probe_bridge.v`, with the claim text kept
verbatim as `redeal_mini_stmt`:

```coq
Lemma redeal_mini_false : ~ redeal_mini_stmt (@Ordinal 4 1 isT).
Lemma redeal_mini_0     : redeal_mini_stmt (@Ordinal 4 0 isT).
```

The defect is in the toy, not in L12. The re-deal needs each class to be a
*family* of blocks, which is what the repaired miniature states and proves:

```coq
Lemma redeal_mini_family (i : 'I_4) (S : {set 'I_4}) :
  S \in famA -> exists2 S', S' \in famB & (i \in S') = (i \in S).
```

with `famA = [set SA; ~: SA]`, `famB = [set SB; ~: SB]`. The full L12 statement
`psl211_private` typechecks unchanged and slots into `orbit_scheme`'s
`ts_private` field without adjustment, so the ledger's *shape* claim stands; it
is the size-1 miniature that has to be restated.

---

## Timings

All numbers are from `rocq compile -time`, on this machine, with no other
rocqworker running. `tac` is the tactic, `Qed` the kernel re-check.

### `probe_orbit.v` — total 75.63 s

| lemma | tac | Qed |
|---|---|---|
| `design5_okA` (L3) | **0.435 s** | **0.434 s** |
| `design5_okB` | 0.436 s | 0.421 s |
| `design5_mut` | 0.420 s | 0.428 s |
| `stable_r4A` / `stable_r4B` / `stable_m6A` / `stable_m6B` (L4) | 0.014 s each | 0.014 s each |
| `stable_rev12A_false` | 0.014 s | 0.014 s |
| `count_okT` (L6) | **38.671 s** | **0.000 s** |
| `count_ok5_mut_false` | 29.486 s | 0.000 s |
| `leak6` (L7) | 0.001 s | 0.001 s |
| `tables_distinctT` (new, L5) | 0.345 s | — |
| `setsA_B_disjoint` (L5) | 0.175 s | 0.005 s |
| `r4_inj` / `m6_inj` (L2) | 0.008 / 0.009 s | — |
| `Require pgg_interface` | 3.494 s | — |

The L5 block added about 0.55 s to the file. `count_okT` at 38.7 s is
comfortably inside the spec's "< 5 min" target and is the single most expensive
item in the whole probe set.

Note the `Qed` asymmetry: `design5_okA` pays its vm_compute twice (tactic and
kernel), `count_okT` pays it once. Budget the count check at one pass and the
design check at two.

### `probe_mixing.v` — total 13.90 s

| lemma | tac | Qed |
|---|---|---|
| `size_elem_table` (L14) | **6.504 s** | **0.001 s** |
| `uniq_elem_keys` | 0.244 s | 0.243 s |
| `elem_closed_okT` | 1.521 s | — |
| `size_closure_r4` (mutation) | < 0.001 s | — |
| `walk1_total` | 3.875 s | 0.004 s |
| `walk100_total` (L15) | **0.569 s** | **0.636 s** |

`walk1_total`'s 3.875 s is where `succ_table` and `pred_table` are forced; the
VM caches them, so every later `walkN` lemma pays only the walk.

### L15 cost curve (`scratch_walk_scaling.v`, L = 570 deliberately not attempted)

| L | tac | Qed | total |
|---|---|---|---|
| 100 | 0.577 s | 0.575 s | 1.15 s |
| 200 | 1.436 s | 1.464 s | 2.90 s |
| 300 | 2.568 s | 2.608 s | 5.18 s |
| 400 | 4.041 s | 4.087 s | 8.13 s |

Growth sits between `L^1.4` and `L^2`, so L = 570 extrapolates to roughly
15–20 s of walking, on top of about 3.9 s to force the transition tables and
6.5 s for the BFS closure: **the whole L = 570 certificate should land near
30 s, not the five to ten minutes section 4 of the spec estimates.** The spec's
cost paragraph should be corrected; L15 is not a schedule risk.

---

## `Print Assumptions` — all non-Local results of the four zero-Admitted probes

Baseline first. `scratch_baseline.v` measures what `transitivity_privacy.v`
itself carries, so the probe output can be read against a floor rather than
against zero. `inde_prod_fst`, `ttrans_view_indep_gen`,
`ttrans_view_indep_alldecks` and `profile_view_indep` each report exactly:

```
Axioms:
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

Call that set **BOOLP3**.

### `probe_group.v`

```
Print Assumptions r4_inj.            Closed under the global context
Print Assumptions m6_inj.            Closed under the global context
Print Assumptions psl211_N'.         Closed under the global context
Print Assumptions psl211_gens_in_G.  Closed under the global context
Print Assumptions r4_permE.          Closed under the global context
Print Assumptions m6_permE.          Closed under the global context
Print Assumptions m6_inv_permE.      Closed under the global context
```

### `probe_orbit.v`

```
Print Assumptions r4_inj.             Closed under the global context
Print Assumptions m6_inj.             Closed under the global context
Print Assumptions setsA_invariant.    Closed under the global context
Print Assumptions setsB_invariant.    Closed under the global context
Print Assumptions setsA_B_disjoint.   Closed under the global context
```

### `probe_mixing.v` (it has no non-Local lemma; all six are printed anyway)

```
Print Assumptions size_elem_table.    Closed under the global context
Print Assumptions uniq_elem_keys.     Closed under the global context
Print Assumptions elem_closed_okT.    Closed under the global context
Print Assumptions size_closure_r4.    Closed under the global context
Print Assumptions walk1_total.        Closed under the global context
Print Assumptions walk100_total.      Closed under the global context
```

### `probe_bridge.v`

```
Print Assumptions uniform_fdistmap_of_fibres.   BOOLP3
Print Assumptions orbit_fibre_card.             Closed under the global context
Print Assumptions colour_view_indep_of_laws.    BOOLP3
Print Assumptions colour_view_indep_of_fibres.  BOOLP3
Print Assumptions redeal_mini_false.            Closed under the global context
Print Assumptions redeal_mini_0.                Closed under the global context
Print Assumptions redeal_mini_family.           Closed under the global context
```

Nothing outside BOOLP3 appears anywhere, so the probes sit exactly on the
`transitivity_privacy.v` floor. Soundness invariant 1 of spec section 8 ("no new
axiom or assumed constant") holds for every probed row.

### `probe_decomposition.v` — the two requested printouts, verbatim

```
Print Assumptions orbit_recon_invariant.
Axioms:
setsA_invariant :
  forall (g : pgg_gT psl211_M) (S0 : {set 'I_12}),
  g \in pgg_G psl211_M -> ([set g x | x in S0] \in setsA) = (S0 \in setsA)
r4_inj : injective (tbl_fun r4_tbl)
psl211_private :
  forall (s1 s2 : bool) (sh : 12.-tuple 'I_12) (C : {set 'I_12}),
  #|C| < 6 ->
  orbit_valid s1 sh ->
  exists sh' : 12.-tuple 'I_12,
    orbit_valid s2 sh' /\
    (forall i : 'I_12, i \in C -> tnth sh' i = tnth sh i)
orbit_encode_valid : forall s : bool, orbit_valid s (orbit_encode s)
orbit_encode : bool -> 12.-tuple 'I_12
m6_inj : injective (tbl_fun m6_tbl)
heart_set_act :
  forall (g : pgg_gT psl211_M) (sh : 12.-tuple 'I_12),
  heart_set [tuple tnth sh (pgg_rho g i) | i < 12] =
  [set g^-1%g x | x in heart_set sh]
```

```
Print Assumptions psl211_colour_view_indep.
Axioms:
r4_inj : injective (tbl_fun r4_tbl)
psl211_fibres_eq :
  forall (R : realType) (secretP : {fdist bool})
    (card_G_gt0 : 0 < #|pgg_G psl211_M|) (C : {set 'I_12})
    (v : {ffun 'I_12 -> bool}),
  #|C| <= 5 ->
  #|[set g in pgg_G psl211_M | colour_view secretP card_G_gt0 C (true, g) == v]| =
  #|[set g in pgg_G psl211_M | colour_view secretP card_G_gt0 C (false, g) == v]|
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
m6_inj : injective (tbl_fun m6_tbl)
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
colour_view_indep_of_fibres :
  forall (R : realType) (secretP : {fdist bool})
    (card_G_gt0 : 0 < #|pgg_G psl211_M|) (C : {set 'I_12}),
  (forall v : {ffun 'I_12 -> bool},
   #|[set g in pgg_G psl211_M | colour_view secretP card_G_gt0 C (true, g) == v]| =
   #|[set g in pgg_G psl211_M | colour_view secretP card_G_gt0 C (false, g) == v]|) ->
  secretP `x (`U card_G_gt0) |= colour_view secretP card_G_gt0 C _|_
  dealt_secret secretP card_G_gt0
```

Reading these two: every axiom is one of the deliberately Admitted supports plus
BOOLP3. Of them, three are already discharged elsewhere in this probe set —
`r4_inj`, `m6_inj` (Qed in `probe_group.v` and `probe_orbit.v`),
`setsA_invariant` (Qed in `probe_orbit.v`) — and
`colour_view_indep_of_fibres` is Qed in `probe_bridge.v` at a strictly more
general carrier, so instantiating the bridge lemma discharges it too. What
genuinely remains open after this run is `heart_set_act`, `deck_stable`,
`orbit_encode`, `orbit_encode_valid`, `psl211_private`, `psl211_fibres_eq`,
`psl211_eleven_reveal_class`, `psl211_ten_reveal_ambiguous`, `psl211_card`,
`setsA_orbitE`.

`orbit_recon_invariant`, `orbit_scheme`, `psl211_plug`, `psl211_PI`,
`psl211_profile` and `psl211_colour_view_indep` are all defined or Qed, so the
record layer composes.

---

## Statement changes

Eight, all recorded in `CHANGES.md` with before/after/why. One is mathematical:

- **C1 (MATHEMATICAL, flagged): `redeal_mini` is false.** Detailed above.
- C2: `uniform_fdistmap_of_fibres` needed `(`U HA : R.-fdist X)`; `` `U `` leaves
  the realType a hole and nothing else in the statement mentioned `R`.
- C3: `orbit_fibre_card` needed `#|('C_G[x | to])%g|`; `group_scope` is not open
  in `probe_bridge.v`.
- C4: the `taut` probe's `Fail` moved from the `Lemma` sentence onto
  `reflexivity`.
- C5: one argument dropped from the right-hand `colour_law` application in
  `taut` (`G` is implicit after discharge).
- C6: four `%N` -> `%num` in `probe_mixing.v`; under mathcomp `%N` is nat_scope
  and `%num` is `N_scope`.
- C7: `psl211_PI` turned from `Admitted` into a real definition.
- C8: a duplicated `Require Import pgg_interface` removed from
  `probe_orbit.v`.

---

## Things that surprised me

1. **`redeal_mini` is false, and its explanatory comment is wrong too.** This is
   the one place where a ledger claim does not survive contact with the kernel.
   It is a defect of the toy, not of L12.

2. **The `taut` probe as delivered tested nothing.** `Fail` scopes over one
   sentence, so `Fail Lemma taut ... Proof. reflexivity. Qed.` asks whether the
   *statement* is ill-typed and errors with "The command has not failed!" the
   moment it is well-typed. Any probe of this shape anywhere in the spec set
   should be rewritten as `Lemma ... Proof. Fail <tactic>. Abort.` After the
   move, the failure is the intended one: `Unable to unify "colour_law ... C
   false" with "colour_law ... C true"`.

3. **L10 is already in mathcomp under another name.** `amove to A x y :=
   [set a in A | to x a == y]` (`fingroup/action.v` line 198) is literally the
   probe's fibre set, and `amove_act` (line 737) is the coset fact. The whole
   proof is `amove_act` plus `card_rcoset`, and it is the only bridge lemma with
   no axioms at all. The implementation should cite `amove` rather than restate
   the set. The `S : {set {set 'I_12}}` parameter in the probe's statement is
   dead and can go.

4. **L5 needs only half the certificates the ledger budgets.** Generator
   invariance of the table family is an *equality* of memberships, but only the
   forward inclusion has to be computed: an injective self-map of a finite type
   that sends a finite family into itself sends it *onto* itself, so the
   converse is free by cardinality (`stab_of_sub` in `probe_orbit.v`). No
   `stable_m6iA` / `stable_m6iB` certificate is needed, and `m6i_tbl` is used
   only to witness `m6_inj`.

5. **`%N` means `nat` under mathcomp.** `ssrnat` sets `Delimit Scope nat_scope
   with N` and `Delimit Scope N_scope with num`, so `0%N` in a `seq N` context is
   a type error. `probe_mixing.v` did not typecheck as delivered for this reason
   alone. Any future N-arithmetic certificate in this repo must use `%num`.

6. **`` `U `` does not pin its realType.** infotheo's notation is
   `fdist_uniform_supp _ C0`; a lemma whose statement mentions `R` nowhere else
   fails to elaborate. Worth knowing before writing more bridge lemmas.

7. **The cost profile is the opposite of what section 4 predicts.** The spec
   budgets five to ten minutes for the L = 570 walk and treats the count check
   as cheap. Measured: the walk extrapolates to about 30 s end to end, while the
   size-1..5 count check is 38.7 s and its mutation another 29.5 s. L6, not L15,
   is where the in-kernel budget goes.

8. **`psl211_PI` needs no piSMC program.** A `PGGInterface` is `pi_T'`,
   `pi_starts`, `pi_starts_uniq` and nothing else, exactly as `pgl27_PI` is
   built. One expected Admitted disappears from L13.

9. **`vm_compute` Qed cost is not uniform.** `design5_okA` pays its 0.43 s twice
   (tactic then kernel); `count_okT` pays its 38.7 s once, with `Qed` at 0.00 s.
   Do not assume a factor of two either way when budgeting.

10. **Two header comments name lemmas that do not exist.** `probe_orbit.v`'s
    header asks for the time of `design5_okT` (the lemmas are `design5_okA` and
    `design5_okB`); `probe_mixing.v`'s header asks for `elem_table_okT` and
    `walk100_ok` (the lemmas are `elem_closed_okT` and `walk100_total`). No code
    change made; flagged so the plan does not inherit the wrong names.

11. **`colour_view_indep_of_fibres` is not really an axiom of the plan.** It is
    Admitted inside `probe_decomposition.v`, but `probe_bridge.v` proves it at a
    more general carrier (`rho` an arbitrary function, `encode` and `colour`
    arbitrary). Instantiating at `rho := @pgg_rho psl211_M`,
    `encode := orbit_encode`, `colour := is_heart` discharges it. The
    implementation should not re-derive it.

---

## Files

All kept, none deleted, none imported by anything permanent.

```
notes/probes/2026-09-14-psl211/
  psl211_tables.v          (literal data, untouched)
  run.sh                   (untouched, correct as delivered)
  probe_group.v            L1, L2            0 Admitted
  probe_orbit.v            L3..L7            0 Admitted
  probe_bridge.v           L8, L9, L10, L12  0 Admitted
  probe_mixing.v           L14, L15          0 Admitted
  probe_decomposition.v    L11..L13, L16, L17  Admitted supports by design
  scratch_l5.v             cheap development copy of the L5 block
  scratch_mut_badN.v       L1 mutation with Fail removed, to read the error
  scratch_mut_badT.v       L1 mutation with Fail removed, to read the error
  scratch_taut_nofail.v    C4 evidence: reflexivity really fails
  scratch_baseline.v       axiom floor of transitivity_privacy.v
  scratch_walk_scaling.v   L = 200/300/400 walk timings
  CHANGES.md               every statement change, before/after/why
  PROBE-REPORT.md          this file
```

`AUDIT-NAMING.md`, `audit-naming/` and `audit-soundness/` appeared in this
directory while the probe run was in progress. They are another session's work
and were neither read nor written by this run.
