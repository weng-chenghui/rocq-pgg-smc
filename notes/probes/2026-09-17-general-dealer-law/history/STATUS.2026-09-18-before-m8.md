# General dealer law probe status

Date: 2026-09-18 (supersedes the earlier 2026-09-18 entries; this one is
after the naming pass)

## Machine-checked

Every file below has a `.vo` in this directory, produced by the single-file
command at the end of this document, run from this directory against the
production `.vo` files as they stand. No production file was rebuilt and no
inconsistent-assumption error appeared.

| File | Claims | Wall | Peak RSS |
|---|---|---|---|
| `dealer_kernel_probe.v` | C1-C3 | 4 s | 1.64 GB |
| `carrier_transport_probe.v` | C4 | 4 s | 1.62 GB |
| `pgl27_deterministic_bridge.v` | C5, C6 | 5 s | 1.69 GB |
| `psl211_alldecks_bridge.v` | C7 | 6 s | 1.74 GB |
| `psl211_per_deck_counter.v` | C8 counting | 29 s | 1.85 GB |
| `psl211_per_deck_law_counter.v` | C8 conclusion | 5 s | 1.70 GB |
| `concrete_instances.v` | C9 | 6 s | 1.78 GB |

C10 is an independent naming audit and is not a compile artifact. Its verdicts
are folded into the files above.

## Logical path and the single-file command

`_CoqProject` now ends with `-Q . general_dealer_law_probe`, so the probe files
form a library and can require one another. `Makefile.rocq` was regenerated
with `rocq makefile -f _CoqProject -o Makefile.rocq`, and
`make -f Makefile.rocq -n` lists only probe `.v` files and no target outside
this directory. The real `make` is not run here: `instances/psl211/psl211_endpoints.v`
is newer than its `.vo` and rebuilding it costs about 900 s and 17 GB.

From this directory, one Rocq process at a time:

```text
opam exec --switch /Users/cheng-huiweng/Projects/coq -- rocq compile \
  -w -projection-no-head-constant -w -redundant-canonical-projection \
  -w -notation-overridden -w -ambiguous-paths \
  -w -notation-incompatible-format \
  -R ../../../lib pgg_smc -R ../../../protocol pgg_smc \
  -R ../../../groups pgg_smc -R ../../../security pgg_smc \
  -R ../../../smc pgg_smc -R ../../../reconstruct pgg_reconstruct \
  -R ../../../instances/denboer1989 pgg_smc \
  -R ../../../instances/kim2025 pgg_smc -R ../../../instances/s5 pgg_smc \
  -R ../../../instances/pgl27 pgg_smc -R ../../../instances/psl211 pgg_smc \
  -R ../../../manifest pgg_smc -Q . general_dealer_law_probe <file>.v
```

The five files that existed before this round were copied to `history/` under
the names `<name>.2026-09-18-before-c9.v` before any edit. `history/` is not
listed in `_CoqProject`.

## Naming

The names below are after the naming pass. Nothing about any statement or any
proof changed in that pass: every file recompiled to the same `Print
Assumptions` output, and the seven mutation errors are the same errors with
the new spellings. The reader names follow the repository rule that a reader
is the law's name minus the trailing P, as in `alldecksP` with
`alldecks_secret` and `alldecks_view`; `dealer_secret` and `dealer_view` were
given up because `protocol/` owns a `dealer_*` party namespace, where
`dealer_view` reads as the dealer's own view. The generic carrier is
`shuffleT` because `reconstruct/transitivity_privacy.v`, the file these
declarations are headed for, says "shuffle" throughout and never "cut"; inside
the two instance files the local notation stays `cutT`.

| Old | New |
|---|---|
| `dealer_secret` | `dealer_shuffle_secret` |
| `dealer_view` | `dealer_shuffle_view` |
| `cutT` (generic files) | `shuffleT` |
| `dealer_shuffleP_missing_cut` | `dealer_shuffleP_missing_shuffle` |
| `pgl_delta`, `pgl_nu` | `pgl27_dealer_delta`, `pgl27_dealer_nu` |
| `pgl_dealerP`, `pgl_dealerP_map` | `pgl27_dealerP`, `pgl27_dealerPE` |
| `pgl_embed`, `pgl_bad_embed` | `pgl27_dealer_embed`, `pgl27_dealer_bad_embed` |
| `pgl_generic_view` | `pgl27_dealer_view` |
| `pgl_view_square`, `pgl_secret_square` | `pgl27_dealer_viewE`, `pgl27_dealer_secretE` |
| `pgl_bad_view_square` | `pgl27_dealer_bad_viewE` |
| `pgl_common_mu` | `pgl27_dealer_mu` |
| `pgl_fixed_view_law` | `pgl27_dealer_view_law` |
| `pgl_generic_indep` | `pgl27_dealer_view_indep` |
| `pgl_indep_via_generic` | `pgl27_view_indep_via_dealer` |
| `pgl_all_delta` | `pgl27_alldecks_dealer_delta` |
| `pgl_all_dealerP`, `pgl_all_dealerP_E` | `pgl27_alldecks_dealerP`, `pgl27_alldecks_dealerPE` |
| `pgl_all_viewE` | `pgl27_alldecks_dealer_viewE` |
| `pgl_deck_view_law` | `pgl27_alldecks_dealer_view_law` |
| `pgl_all_indep_via_generic` | `pgl27_view_indep_alldecks_via_dealer` |
| `psl_deal_pos` | `psl211_deal_pos` |
| `psl_delta`, `psl_nu` | `psl211_dealer_delta`, `psl211_dealer_nu` |
| `psl_genericP`, `psl_law_E` | `psl211_dealerP`, `psl211_dealerPE` |
| `psl_assoc`, `psl_bad_assoc` | `psl211_dealer_assoc`, `psl211_dealer_bad_assoc` |
| `psl_generic_view` | `psl211_dealer_view` |
| `psl_view_square`, `psl_secret_square` | `psl211_dealer_viewE`, `psl211_dealer_secretE` |
| `psl_bad_secret_square` | `psl211_dealer_bad_secretE` |
| `psl_mixed_law`, `psl_mixed_lawE` | `psl211_dealer_mixed_law`, `psl211_dealer_mixed_lawE` |
| `psl_section_law` | `psl211_dealer_sectionE` |
| `psl_generic_indep` | `psl211_dealer_view_indep` |
| `psl_indep_via_generic` | `psl211_alldecks_view_indep_via_dealer` |
| `fdistmap_prod_sections` | `fdistmap_prod_sectionE` |
| `psl_counter_<x>` | `psl211_perdeck_<x>` |
| `psl_counter_testP` | `psl211_perdeck_testE` |
| `psl_entry_perm_enum` | `psl211_entry_perm_enum` |
| `psl_per_deck_fibers_differ` | `psl211_perdeck_fiber_card_neq` |
| `psl211_perdeck_law_differ` | `psl211_perdeck_law_neq` |
| `pgl27_view_indep_realE` | `pgl27_view_indep_at_R` |
| `pgl27_view_indep_alldecks_realE` | `pgl27_view_indep_alldecks_at_R` |
| `psl211_alldecks_view_indep_realE` | `psl211_alldecks_view_indep_at_R` |
| `psl211_dealer_lawE_real` | `psl211_dealerPE_at_R` |

The four wrappers end in `_at_R` and not in `_realE`. The precedent
`notes/probes/2026-09-15-pgl27-view-entropy/concrete_real_instance.v` names
both of its wrappers `..._realE`, but both of those are equations, so `E`
carries its usual meaning there. Three of the four here are independence
statements and not equations, so a suffix that reads as an unfolding lemma
would be wrong on them; `_at_R` names only the carrier, which is what all four
have in common.

The file names still contain the words "bridge" and "counter". Renaming them
would move `_CoqProject`, `Makefile.rocq` and the design note's artifact list,
which is outside this pass; reported rather than done.

## Which bridge instantiates which dealer-model declaration

There are no copies of the dealer-model declarations left. Both copy sections
are deleted and every bridge requires the real ones.

| Declaration | Claim | Instantiated by |
|---|---|---|
| `dealer_shuffleP` | C1 | all three bridges |
| `dealer_shufflePE` | C1 | `psl211_dealerPE`, `pgl27_dealerPE` |
| `dealer_shuffle_secret`, `dealer_shuffle_view` | C1 | all three bridges |
| `dealer_view_indep` | C2 | PGL deterministic, PSL all-decks |
| `dealer_view_indep_of_deck` | C3 | PGL all-decks |
| `inde_RV_fdistmap` | C4 | PGL deterministic, PSL all-decks |

Soundness invariant 8 therefore holds as stated: each of C1 to C4 is reached
through the real declaration by at least one bridge.

PGL all-decks uses C3 with `valid s d := uniq d`. Its first premise is the
extraction of `deck_ok` from membership in `class_decks orbit_class deck_ok s`,
and its second premise is `pgl27_alldecks_dealer_view_law` up to eta.

## C9: the assumption whitelist

All four wrappers of `concrete_instances.v` report exactly the following, and
nothing else. No project-local constant and no `Admitted` appears.

```text
Axioms:
ClassicalDedekindReals.sig_not_dec : forall P : Prop, {~ ~ P} + {~ P}
ClassicalDedekindReals.sig_forall_dec :
  forall P : nat -> Prop,
  (forall n : nat, {P n} + {~ P n}) ->
  {n : nat | ~ P n} + {forall n : nat, P n}
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
Epsilon.epsilon_statement :
  forall (A : Type) (P : A -> Prop),
  inhabited A -> {x : A | (exists x0 : A, P x0) -> P x}
constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

Two entries differ from what the ledger anticipated, and both are benign.
`FunctionalExtensionality.functional_extensionality_dep` is a second,
separately named copy of the same statement, from the standard library rather
than from `boolp`. The sealed `Rdefinitions.RbaseSymbolsImpl.*` and
`RinvImpl.*` constants do not appear at all: they are opaque definitions built
over `ClassicalDedekindReals`, not axioms, which is why the two `sig_*` axioms
appear in their place.

Every lemma of the abstract layer, C1 to C7 included, still reports the three
`boolp` axioms alone. All eight lemmas of `psl211_per_deck_counter.v` still
report `Closed under the global context`, and the four of
`psl211_per_deck_law_counter.v` report the three `boolp` axioms.

## C8: the per-deal conclusion

`psl211_per_deck_counter.v` counts. At the deal `psl211_perdeck_deal`, the
coalition of seats 0, 1 and 2 and the reading that gives them cards 0, 1 and 5,
the fiber of cuts producing that reading has 0 elements in one chirality and 1
in the other.

`psl211_per_deck_law_counter.v` turns that into the statement the general model
needs. For every `realType`,

```coq
Lemma psl211_perdeck_law_neq (R : realType) :
  fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
      (true, psl211_perdeck_deal) g) ((`U psl211_G_pos) : R.-fdist cutT) !=
  fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
      (false, psl211_perdeck_deal) g) ((`U psl211_G_pos) : R.-fdist cutT).

Lemma psl211_perdeck_no_common_law (R : realType)
    (valid : bool -> psl211_deal -> bool) (mu : R.-fdist viewT) :
  (forall b : bool, valid b psl211_perdeck_deal) ->
  ~ (forall (b : bool) (d : psl211_deal),
       (fdist_uniform card_bool : R.-fdist bool) b != 0 -> valid b d ->
       fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
           (b, d) g) ((`U psl211_G_pos) : R.-fdist cutT) = mu).
```

The second is the second premise of `dealer_view_indep_of_deck` written at
PSL(2,11), for an arbitrary validity predicate that accepts that deal, and it
has no solution. So PSL privacy is a property of the average over deals, and
C3 is not available to it, while PGL all-decks reaches its conclusion deck by
deck through exactly that premise.

The step from counts to laws needed one lemma the repository does not have:
`uniform_fdistmap_pointE`, the mass a pushed-forward uniform law gives to one
value. `reconstruct/design_privacy.v` performs that computation inside the
proof of `uniform_fdistmap_fiberE`, as a `have key`, and does not export it;
`pr_countE` is about a product law and a `Pr` event, not about a pushforward
point. The probe's version is that `key` step lifted to a statement.

## Mutations

Seven `Fail Definition` checks, all still failing, each with a one-line comment
naming the intended error. `rocq compile` prints nothing for a `Fail`, so the
texts below were read with `rocq repl -q <flags> < file.v`, which does echo
"The command has indeed failed with message:".

| Mutation | First line of the error |
|---|---|
| `dealer_shuffleP_missing_shuffle` | `The term "secretP `X delta" has type "{fdist ... secretT deckT}" while it is expected to have type "{fdist secretT * (deckT * shuffleT)}".` |
| `dealer_shuffle_view_indep_without_common_law` | `The term "dealer_view_indep (mu:=fdist1 x)" has type "(forall s : secretT, ...) -> dealer_shuffleP ... |= ..." while it is expected to have type "dealer_shuffleP ... |= ...".` |
| `inde_RV_fdistmap_bad_reader` | `The term "proj1 (inde_RV_fdistmap P f X Y)" has type "fdistmap f P |= X _\|_ Y -> P \|= (X \o f) _\|_ (Y \o f)" while it is expected to have type "... _\|_ Ybad".` |
| `pgl27_dealer_bad_viewE` | `The term "erefl" has type "dealer_shuffle_view ... \o pgl27_dealer_bad_embed = dealer_shuffle_view ... \o pgl27_dealer_bad_embed" while it is expected to have type "... = pgl27_view R C".` |
| `pgl27_alldecks_dealer_view_law_without_validity` | `The term "HC" has type "is_true (#\|C\| <= 3)%N" while it is expected to have type "is_true (uniq d)".` |
| `fdistmap_prod_sectionE_without_sections` | `The term "fdistmap_prod_sectionE (h:=h)" has type "(forall g : G, PG g != 0 -> ...) -> fdistmap ... = fdistmap ..." while it is expected to have type "fdistmap ... = fdistmap ...".` |
| `psl211_dealer_bad_secretE` | `The term "erefl" has type "dealer_shuffle_secret ... \o psl211_dealer_bad_assoc = dealer_shuffle_secret ... \o psl211_dealer_bad_assoc" while it is expected to have type "... = psl211_alldecks_secret R".` |

Two positive controls compile immediately before their mutations, so each
mutation is known to fail for the missing premise and not for an unrelated
reason: `dealer_shuffle_view_indep_with_common_law` and
`fdistmap_prod_sectionE_with_sections`. The audit's concern about the second
one is answered: with the lemma's own `(D G V : finType)` binders written out
in a full `@` spelling, the error is the missing premise and nothing else.

`pgl27_alldecks_dealer_view_law_without_validity` is the one mutation whose error is an
argument-position mismatch rather than a leftover arrow. That is still the
intended reason, since the coalition-size argument only lands in the `uniq d`
slot because `uniq d` was dropped.

## Elaboration regime

All seven files now open with

```coq
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
```

which is what `reconstruct/transitivity_privacy.v` uses, so the probe is
elaborated in the regime its permanent home will have. This changed real
behaviour rather than nothing: a section variable or lemma binder that occurs
in the type of a later argument becomes implicit, so every lemma whose premise
mentions `#|C|` has `C` implicit, and `psl211_dealer_sectionE C g HC` stopped
elaborating. Every application of a probe-local declaration is now written
with `@`.

## Measured obstructions

### `idP` is opaque, so no ordinal-indexed structure computes

`inord m` is `insubd ord0 m` and `insub x` branches on `idP`, which is
Qed-opaque. `Eval vm_compute in (val (inord 0 : 'I_12))` therefore returns a
stuck `match idP with ReflectT x => Some (Ordinal x) | ReflectF _ => None end`
in 0.003 s rather than `0`. The same block reaches `ord_enum`, hence every
`{ffun 'I_n -> _}` and every `{set 'I_n}`, and hence `psl211_alldecks_seq`,
whose twelve entries came back as stuck
`perm (inj_id (A:='I_6)) (match idP with ...)` terms in 0.108 s.

Raw data is unaffected: `val (psl211_code12 5)` gives 5 in 0.000 s and
`nth [::] (unzip1 psl211_elem_table) 0` gives `[:: 0; 1; ...; 11]` in 4.95 s,
so the BFS closure itself is cheap. The first C8 draft counted an `ffun`
equality over a deck read through `psl211_alldecks_seq` and was killed at
6.5 GB after 600 s with no answer. The counted term is now raw nat lists only
(`psl211_perdeck_test` over `unzip1 psl211_elem_table`), and three symbolic
lemmas carry it back to the real objects: `psl211_perdeck_seqE` for the deck,
`psl211_perdeck_testE` for the reading, and `psl211_perdeck_raw_viewE` with
`psl211_perdeck_ptbl_enum` for the shuffle group.

### C7: a rewrite that names both chiralities unfolds both tables

In `psl211_dealer_sectionE` the set-shape rewrite was the whole cost. With `Time` on
every sentence and `Fail Timeout 30` on the suspects: the `apply:` took
0.010 s, each `have` 0.012 s, and `rewrite Htrue`, `move: Htrue => ->` and
`rewrite Htrue Hfalse` each hit the 30 s ceiling. The fix keeps the tables out
of every unification that can fail: `uniform_fdistmap_fiberTE` reconciles the
`[set d in [set: D] | _]` and `[set d | _]` comprehension shapes while the two
maps are still section variables, and `psl211_dealer_sectionE` then closes by
`exact:` on a goal that is syntactically `psl211_alldecks_per_cut_count`'s
conclusion. `psl211_alldecks_view` is sealed with `Local Opaque` so the later
transports cannot walk into it either.

### The transport rewrite is NOT one of those shapes

The hypothesis-form pullback that the earlier round kept as a workaround has
been deleted, because the shape it worked around was measured and is fast.
With `Local Opaque psl211_alldecks_view` in force,

```coq
rewrite -(psl211_dealer_viewE C) -psl211_dealer_secretE.
by apply/inde_RV_fdistmap.
```

compiles at the PSL use site inside a `Timeout 20` on each sentence, in a
scratch file whose total wall time including all imports was 5 s. The
difference from `psl211_dealer_sectionE` is that here the goal names the reading once,
under the seal, and the two sides differ in more than the chirality bit, so the
matcher fails at the first constructor instead of descending.

`apply/inde_RV_fdistmap` does fail with "Cannot apply view inde_RV_fdistmap"
when it is used inside the section that defines it, where the statement is
closed over the section variables and has no implicit arguments to unify. After
discharge it works, which is the only place a bridge uses it.

### C8: two tactics that decided a table-sized goal

`by rewrite Heq` at the end of `psl211_perdeck_ptbl_enum` left `done` facing
`perm_eq` of the closure with itself, about 41 s; it is now
`rewrite Heq; exact: perm_refl`. The headline's
`by rewrite !psl211_perdeck_fiberE Htrue Hfalse` put both chiralities of the same
definition in one goal for the matcher; it is now term mode, with each
cardinality pinned to its numeral by `etrans` before the two meet. Together
these took the file from a 499 s run that produced no `.vo` down to 29 s.
`psl211_perdeck_law_neq` is written the same way, each mass pinned in a goal
that names one chirality only and the two brought together by `etrans`.

## Library facts worth keeping

- `eq_in_map` is an iff in mathcomp 2.4, so `apply/eq_in_map`, not `apply:`.
- `count_filter` is `count a1 (filter a2 s) = count (predI a1 a2) s`. The
  cardinality step is `rewrite cardE /enum_mem size_filter count_filter`.
- `inordK` keys on `nat_of_ord (inord _)` while `psl211_alldecks_seq` is
  written with `\val`. These are convertible but not syntactically equal, so
  `inordK` must be applied, not rewritten with.
- `rewrite -Hrow` to turn a bound `6` into `size H` is a dependent type error,
  because the `6` of `{perm 'I_6}` inside the deal is also a `6`. The pattern
  `-[X in _ < X]Hrow` is needed.
- `inE` rewrites a seq membership in preference to a set membership, so
  `psl211_perdeck_raw_viewE` uses `in_set` to unfold the coalition on both sides
  of the goal at once.
- A `case: b` inside a proof whose context already mentions `b` fails with
  "b is used in hypothesis"; the two block-size facts are separate lemmas.
- `fdist_uniformE` gives `#|A|%:R^-1`, so `fdist_uniform card_bool b != 0`
  needs `rewrite fdist_uniformE invr_eq0 pnatr_eq0 card_bool`. Without
  `card_bool` the closing `done` cannot evaluate `#|bool|` and reports
  "No applicable tactic".
- `rocq compile` prints nothing for a `Fail`. `rocq repl -q <flags> < file.v`
  prints "The command has indeed failed with message:" followed by the error.
- This machine's `grep -E` does NOT support the POSIX word-boundary brackets
  `[[:<:]]` and `[[:>:]]`: a pattern using them matches nothing and reports
  success, so a scan written that way is a silent false negative. `grep -E`
  here does honour `\b`. Every identifier and vocabulary scan in this document
  was rerun in Python with `\b` after that was measured.

## Non-compiling checks

- No `Admitted`, `Abort`, `Axiom`, `Time`, `Timeout`, `Fail Timeout` or
  `Show` occurs in a probe `.v` file.
- No probe `.v` line exceeds 80 characters.
- The banned vocabulary scan reports no match.
- Every `Definition`, `Lemma` and `Corollary` in a probe `.v` file carries a
  statement comment naming the mathematical fact and its place in the privacy
  argument. Tactic rationale is in `(* *)` comments inside proofs.
- Every `Local Opaque` is paired with a `Local Transparent` after the last
  declaration that needs the seal, so nothing leaks into a requiring file.
- The diagnostic files used to measure the obstructions above live in the
  session scratchpad, not in this directory. Nothing here was deleted.
- `flow-sketch-audit.md` and `naming-audit.md` still use the old identifiers.
  They are the audit records that the naming pass acted on, so rewriting them
  would falsify what was audited; the table under Naming reconciles them.
- `history/` holds each file as it stood before the C9 round
  (`<name>.2026-09-18-before-c9.v`) and before the naming pass
  (`<name>.2026-09-18-before-rename.v`), plus the STATUS.md of each.
