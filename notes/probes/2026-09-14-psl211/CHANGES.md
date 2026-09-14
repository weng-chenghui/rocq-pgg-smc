# Statement changes made during the probe run (2026-09-14)

Every change to a statement as written in the probe files, with before, after,
and why. One change is mathematical and is marked LOUDLY.

---

## C1 (MATHEMATICAL) — `probe_bridge.v`, `redeal_mini` is FALSE

**Before**

```coq
Lemma redeal_mini (i : 'I_4) :
  exists S' : {set 'I_4}, (S' == SB) && ((i \in S') == (i \in SA)) \/
                         (S' == SA) && ((i \in S') == (i \in SB)).
```

**After** — the claim text is preserved verbatim as a `Definition`, and three
lemmas replace the single Admitted one:

```coq
Definition redeal_mini_stmt (i : 'I_4) : Prop :=
  exists S' : {set 'I_4}, (S' == SB) && ((i \in S') == (i \in SA)) \/
                         (S' == SA) && ((i \in S') == (i \in SB)).

Lemma redeal_mini_false : ~ redeal_mini_stmt (@Ordinal 4 1 isT).   (* Qed *)
Lemma redeal_mini_0     : redeal_mini_stmt (@Ordinal 4 0 isT).     (* Qed *)

Local Definition famA : {set {set 'I_4}} := [set SA; ~: SA].
Local Definition famB : {set {set 'I_4}} := [set SB; ~: SB].
Lemma redeal_mini_family (i : 'I_4) (S : {set 'I_4}) :
  S \in famA -> exists2 S', S' \in famB & (i \in S') = (i \in S).   (* Qed *)
```

**Why.** `&&` binds tighter than `\/`, so the first disjunct forces `S' = SB`
and the second forces `S' = SA`. Under that forcing both disjuncts reduce to
the *same* condition, `(i \in SB) = (i \in SA)`. With `SA = {0,1}` and
`SB = {0,2}` that condition is `true = false` at `i = 1` and `false = true` at
`i = 2`, so no `S'` exists and the statement is false at those two positions.
The header comment above the toy ("sharing the point pattern counts for every
1-coalition") is also wrong: one block per class cannot match 1-point counts
unless the blocks are equal. The defect is in the toy, not in L12: a re-deal
needs each class to be a *family* of blocks, which is what `redeal_mini_family`
states and proves.

---

## C2 — `probe_bridge.v`, `uniform_fdistmap_of_fibres`, realType ascription

**Before**

```coq
  fdistmap f0 (`U HA) = fdistmap f1 (`U HA).
```

**After**

```coq
  fdistmap f0 (`U HA : R.-fdist X) = fdistmap f1 (`U HA).
```

**Why.** infotheo's notation is `Notation "'`U' C0" := (fdist_uniform_supp _ C0)`,
leaving the `realType` as a hole. Nothing else in the statement mentions `R`, so
elaboration failed with `Cannot infer the implicit parameter R of fdistmap whose
type is "realType"`. The ascription pins the section's `R`. No mathematical
change.

---

## C3 — `probe_bridge.v`, `orbit_fibre_card`, group-scope delimiter

**Before**

```coq
  #|[set g in G | to x g == y]| = #|'C_G[x | to]|.
```

**After**

```coq
  #|[set g in G | to x g == y]| = #|('C_G[x | to])%g|.
```

**Why.** The file opens `fdist_scope`, `proba_scope` and `ring_scope`;
`group_scope` is not open, so `'C_ _ [ _ | _ ]` had no interpretation
(`Unknown interpretation for notation "'C_ _ [ _ | _ ]"`). No mathematical
change.

---

## C4 — `probe_bridge.v`, the `taut` probe, `Fail` placement

**Before**

```coq
Fail Lemma taut (C : {set 'I_12}) : <statement>.
Proof. reflexivity. Qed.
```

**After**

```coq
Lemma taut (C : {set 'I_12}) : <statement>.
Proof. Fail reflexivity. Abort.
```

**Why.** `Fail` scopes over exactly one sentence. `Fail Lemma ...` therefore
succeeds only when the *statement* is ill-typed, and raises `The command has
not failed!` as soon as the statement typechecks; the `reflexivity` on the next
line is never the thing observed. Moving `Fail` onto `reflexivity` makes the
probe test what it says it tests. Verified independently in
`scratch_taut_nofail.v` (same file with `Fail` removed): the statement
elaborates and `reflexivity` then fails with

```
Unable to unify
 "colour_law id secretP card_gt0 encode (fun c : 'I_12 => (\val c < 6)%N) C false"
with
 "colour_law id secretP card_gt0 encode (fun c : 'I_12 => (\val c < 6)%N) C true".
```

so the failure is reflexivity, not typing.

---

## C5 — `probe_bridge.v`, the `taut` statement, one argument dropped

**Before** (right-hand side of the `taut` equation)

```coq
  = colour_law [set: {perm 'I_12}]%G id secretP card_gt0 encode
      (fun c => (val c < 6)%N) C false.
```

**After**

```coq
  = colour_law id secretP card_gt0 encode (fun c => (val c < 6)%N) C false.
```

**Why.** After section discharge, `G` is an *implicit* argument of `colour_law`
(it occurs in the type of the later argument `card_G_gt0`, and the file runs
under `Set Implicit Arguments` / `Unset Strict Implicit`). The explicit `G` was
therefore one argument too many and landed in the `rho` slot:
`The term "[set: {perm 'I_12}]%G" has type "{group {perm 'I_12}}" while it is
expected to have type "?gT -> {perm 'I_?N'.+1}"`. `G` is now resolved from
`card_gt0` through the canonical `setT_group`. The left-hand `@colour_law`
application, which does pass all eleven arguments, is unchanged. No
mathematical change.

---

## C6 — `probe_mixing.v`, four `%N` scope annotations on `N` literals

**Before**

```coq
  | 0 => 1%N :: nseq 659 0%N
    [seq foldl (fun a k => (a + nth 0%N d k)%num) 0%N ps | ps <- pred_table]
Local Definition total (d : seq N) : N := foldl (fun a x => (a + x)%num) 0%N d.
Local Lemma walk1_total : total (walkN 1) = 3%N.
```

**After** — every one of those literals is now `%num`:

```coq
  | 0 => 1%num :: nseq 659 0%num
    [seq foldl (fun a k => (a + nth 0%num d k)%num) 0%num ps | ps <- pred_table]
Local Definition total (d : seq N) : N := foldl (fun a x => (a + x)%num) 0%num d.
Local Lemma walk1_total : total (walkN 1) = 3%num.
```

**Why.** mathcomp's `ssrnat` rebinds the delimiters: `Delimit Scope N_scope with
num.` and `Delimit Scope nat_scope with N.` (ssrnat.v lines 137, 139). So under
mathcomp `0%N` is the unary natural number zero, not the binary `N` zero, and
`walkN : nat -> seq N` failed to typecheck: `The term "1 :: nseq 659 0" has type
"seq nat" while it is expected to have type "seq N"`. The intended values are
unchanged. No mathematical change.

---

## C7 — `probe_decomposition.v`, `psl211_PI` is defined, not Admitted

**Before**

```coq
Definition psl211_PI : PGGInterface psl211_M. Admitted.
```

**After**

```coq
Lemma psl211_starts_uniq : uniq (ord_tuple 12).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.

Definition psl211_PI : PGGInterface psl211_M :=
  @MkPGGI psl211_M 11 (ord_tuple 12) psl211_starts_uniq.
```

**Why.** A `PGGInterface` is the starting layout alone (`pi_T'`, `pi_starts`,
`pi_starts_uniq`); it does not mention the piSMC program. This is exactly how
`instances/pgl27/pgl27_profile.v` builds `pgl27_PI`. The type is unchanged and
one axiom disappears from `psl211_profile`.

---

## C8 — `probe_orbit.v`, duplicated import removed

**Before** (immediately above the L5 block)

```coq
From pgg_smc Require Import pgg_interface.
```

**After** — removed; `pgg_interface` is already required and imported in the
file header. No statement touched.

---

## Additions that are not statement changes

- `probe_group.v`: `m6_inv_permE` proved (`Admitted` -> `Qed`), statement
  unchanged.
- `probe_orbit.v`: `setsA_invariant`, `setsB_invariant`, `setsA_B_disjoint`
  proved, statements unchanged. The supporting material added, all `Local`:
  `rows_lt12`, `rows_lt12A`, `rows_lt12B`, `r4_valE`, `m6_valE`,
  `imset_list_to_set`, `sets_of_gen_sub`, `stab_of_sub`, `stab_of`, `stab_ofP`,
  `group_set_stab_of`, `stab_of_group`, `gens_sub_stab`, `r4_stabA`, `m6_stabA`,
  `r4_stabB`, `m6_stabB`, `G_sub_stabA`, `G_sub_stabB`, `tables_distinct`,
  `tables_distinctT`.
- `probe_bridge.v`: `uniform_fdistmap_of_fibres`, `orbit_fibre_card`,
  `colour_view_indep_of_laws` proved.
- Every probe file gained a trailing `(* ---- assumption audit ---- *)` block of
  `Print Assumptions` commands.
- Scratch files kept alongside the probes: `scratch_l5.v` (cheap development
  copy of the L5 block), `scratch_mut_badN.v` / `scratch_mut_badT.v` (the two
  L1 mutations with `Fail` removed, to read the error text),
  `scratch_taut_nofail.v` (C4 evidence), `scratch_baseline.v` (the axiom floor
  of `transitivity_privacy.v`), `scratch_walk_scaling.v` (L = 200/300/400 walk
  timings). `run.sh` is unchanged and was correct as delivered.
