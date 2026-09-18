# C10 naming and style audit, round 2

Date: 2026-09-18

Independent read-only audit of the probe directory as it stands after the C9
milestones and the rename pass. VERDICT of this round: NO-GO, on one blocking
item. Round 1 is `naming-audit.md` in this directory; its line numbers refer to
the files before these changes and are not valid against the current files.

Nothing was edited, nothing was compiled, no Rocq process was started. Evidence
is `Read`, `awk` and Python `\b` scans, per STATUS.md's warning that this
machine's `grep -E` silently matches nothing for `[[:<:]]`/`[[:>:]]`. `history/`,
`naming-audit.md` and `flow-sketch-audit.md` were excluded from every
old-name scan, as instructed.

Scope: the seven `.v` files listed in `_CoqProject`, 72 declarations.

---

## 1. Disposition of every round-1 finding

Legend: RESOLVED, PARTIAL, OPEN (closeable inside the probe), OPEN-BY-DECISION
(closeable only by editing a production file or the tracked design note), PASS
(was already clean, re-verified).

| ID | Round-2 status | Current evidence |
|---|---|---|
| N001 | RESOLVED, widened | Re-ran the collision scan in Python over all 72 probe declarations against `lib protocol groups security smc reconstruct instances manifest legacy`: **zero** hits. The scan now covers the 70 renamed and new names, not just the 11 of round 1 |
| A001 | RESOLVED (name) / OPEN-BY-DECISION (home) | `uniform_fdistmap_fiberTE`, `psl211_alldecks_bridge.v:78`. Placement in `reconstruct/design_privacy.v` not done by decision |
| A002 | RESOLVED / OPEN-BY-DECISION (home) | One iff `inde_RV_fdistmap`, `carrier_transport_probe.v:33`. Both `GenericCopy` sections gone, `bridge_pushforward` gone, and the hypothesis-form corollary deleted — STATUS.md:306-320 measures the use site under `Timeout 20`, so the workaround it existed for is refuted, not merely dropped. Use sites `pgl27_deterministic_bridge.v:210-211`, `psl211_alldecks_bridge.v:304-305` |
| A003 | RESOLVED (name) | `pgl27_view_indep_alldecks_via_dealer`, `pgl27_deterministic_bridge.v:340`. See D006 for the residual comment gap |
| A004 | RESOLVED (name) | `psl211_alldecks_view_indep_via_dealer`, `psl211_alldecks_bridge.v:293`. See D006 |
| A005 | RESOLVED (name) | `pgl27_view_indep_via_dealer`, `pgl27_deterministic_bridge.v:204`. See D006 |
| A006 | RESOLVED | `dealer_shuffle_secret`, `dealer_kernel_probe.v:38`; no `dealer_secret` anywhere |
| A007 | PASS | unchanged; `inde_RV_fdistmap` is still absent from infotheo |
| A008 | PASS | unchanged; `fdistmap_prod_sectionE` is still not a case of `fdistmap_prod_const` |
| B001 | PASS (precedent confirmed) | `dealer_shuffleP` kept |
| B002 | RESOLVED | `dealer_shuffle_secret:38`, `dealer_shuffle_view:46` |
| B003 | **PARTIAL** | the readers were fixed, but `dealer_view_indep` (`:66`) and `dealer_view_indep_of_deck` (`:86`) still carry the `dealer_view` stem that B003 objected to. See R2-B014 |
| B004 | RESOLVED | one spelling everywhere: `dealer_shufflePE:55`, `pgl27_dealerPE:62`, `pgl27_alldecks_dealerPE:259`, `psl211_dealerPE:168`. No `_E` and no `P_E` left |
| B005 | RESOLVED | every instance name is `pgl27_`- or `psl211_`-prefixed; zero `pgl_`/`psl_`/`psl_counter_` hits |
| B006 | RESOLVED | no `_square`; `pgl27_dealer_viewE:93`, `pgl27_dealer_secretE:102`, `psl211_dealer_viewE:195`, `psl211_dealer_secretE:204` |
| B007 | RESOLVED | no `generic` in any identifier; `_via_dealer` kept, which is repo precedent |
| B008 | RESOLVED (option a) | `psl211_perdeck_testE`, `psl211_per_deck_counter.v:102` |
| B009 | RESOLVED | `psl211_perdeck_fiber_card_neq`, `psl211_per_deck_counter.v:240` |
| B010 | RESOLVED, one NOTE | `psl211_perdeck_*` throughout. NOTE: identifiers say `perdeck`, file names say `per_deck` (`psl211_per_deck_counter.v`, `psl211_per_deck_law_counter.v`). STATUS.md:120-122 reports the file names as deliberately not renamed |
| B011 | RESOLVED | `fdistmap_prod_sectionE`, `psl211_alldecks_bridge.v:40` |
| B012 | RESOLVED | the `_eq` corollary is deleted and its necessity refuted by measurement, STATUS.md:306-320 |
| B013 | PASS | hypothesis names unchanged and still fine |
| C000 | PASS | re-ran the banned-vocabulary scan in Python with `\b` over all seven files: **zero** hits |
| C001 | RESOLVED | "sections" now names only sections (`fdistmap_prod_sectionE:40`); the fiber lemma is `uniform_fdistmap_fiberTE:78` and its comment and name agree |
| C002 | **PARTIAL, reclassified** | `psl211_alldecks_bridge.v` is now all-chirality (13+4, zero "class"); `psl211_per_deck_counter.v` still mixes: "class" at `:31,43,52,121,207`, "classes" at `:128`, against "chirality/chiralities" at `:127,202,235,245`, with `:126-128` using both in one sentence. **But production does the same**: `instances/psl211/psl211_alldecks.v` says "class bit" at `:107,108,149` and "chirality bit" at `:7,9,12`, and `:67` writes "its chirality is the input's class bit". The probe inherits this, it does not invent it, so the fix belongs with the production vocabulary. Downgraded to an implementation-plan NOTE |
| C003 | RESOLVED | each file now picks one prose word: PGL "view" (12/0), PSL "reading" (10/0 and 10/0 and 4/0), generic "observation". The generic file's `_view` identifiers with "observation" prose match production exactly — `reconstruct/design_privacy.v:6-7` and `:85` do the same |
| C004 | **PARTIAL** | generic carrier is `shuffleT` (`dealer_kernel_probe.v:20,23`), prose 9 "shuffle" / 0 "cut". PSL files keep `cutT` and that matches `psl211_models.v` (15+5 cut / 2 shuffle). **PGL does not**: see R2-C007 |
| C005 | **PARTIAL** | `psl211_per_deck_counter.v` still says "deck description" at `:128` and `:234` while saying "deal"/"deals" at `:43,63,64,121,236,237`. One object, two names, same file |
| C006 | RESOLVED (identifiers) | no `bridge_*` identifier remains. File names still contain "bridge"; STATUS.md:120-122 reports this rather than doing it |
| D001 | RESOLVED | scripted check: 72 declarations, 72 preceded by a `(**` statement comment, zero missing, across all seven files |
| D002 | **PARTIAL** | `psl211_alldecks_bridge.v:22-28` now ends "The measurements are in STATUS.md" — exactly the round-1 fix. `psl211_per_deck_counter.v:20-28` still carries "measured 2026-09-18, `Eval vm_compute in val (inord 0)` returns a stuck ..." in a file-level `(* *)` comment |
| D003 | PASS | in-proof rationale comments remain inside proofs and state why a tactic is chosen |
| D004 | RESOLVED | the lemma whose comment stated development rationale is deleted with A002 |
| D005 | PASS | still the exemplars |
| E001 | RESOLVED | all seven files carry the three-line header (`dealer_kernel_probe.v:9-11` and the same in each) |
| E002 | RESOLVED, one adjudication | seven expected-failure comments, two positive controls, seven error texts captured in STATUS.md:232-238. See R2-E010 for the one mutation whose argument I do not fully accept |
| E003 | RESOLVED | zero lone `by [].` lines across all seven files |
| E004 | RESOLVED | three `Local Opaque` / `Local Transparent` pairs: `psl211_alldecks_bridge.v:29/313`, `psl211_per_deck_counter.v:204/258`, `psl211_per_deck_law_counter.v:25/120` |
| E005 | RESOLVED | scripted section-depth check: zero `Print Assumptions` inside a `Section` |
| E006 | PASS | re-verified with `awk`: zero lines over 80 characters; no `Admitted`, `Abort`, `Axiom`, `Time`, `Timeout` or `Show` |
| E007 | RESOLVED | `fdistmap_prod_sectionE` premise reads `forall g, PG g != 0 -> ...` (`psl211_alldecks_bridge.v:43`), and the proof handles the zero-mass cut at `:63-65` |
| E008 | **OPEN, and reclassified** | still two near-identical proofs, `pgl27_deterministic_bridge.v:130-164` and `:286-318`; `diff` shows 27 of ~34 lines identical, differing only in the deck term and the final `ktuple_encode_uniform` arguments. **This is closeable inside the probe** — see R2-E008 |
| F001 | OPEN-BY-DECISION | `Local Lemma alldecks_view_law` still at `reconstruct/transitivity_privacy.v:788` |
| F002 | OPEN-BY-DECISION | note:238 still names `pgl27_alldecks_bridge.v`; C6 is still `pgl27_deterministic_bridge.v` Section `PGLAllDecks` (`:236-376`) |
| F003 | PARTIAL / OPEN-BY-DECISION | `concrete_instances.v` and `naming-audit.md` now exist; `headline_decomposition.v` and `soundness-audit.md` still do not |
| F004 | OPEN-BY-DECISION, widened | the note lists six artifacts; there are now **seven** `.v` files. Neither `psl211_per_deck_counter.v` nor `psl211_per_deck_law_counter.v` is listed |
| F005 | PARTIAL | the probe's generic set is now five declarations (`dealer_shuffleP`, `dealer_shufflePE`, the two readers, the two independence theorems, plus `inde_RV_fdistmap`, `fdistmap_prod_sectionE`, `uniform_fdistmap_fiberTE`, `uniform_fdistmap_pointE`). The note still lists only the original set. See R2-F010 |
| F006 | OPEN-BY-DECISION | note:181 still says C6 derives `ttrans_view_indep_alldecks` |
| F007 | RESOLVED in substance | `psl211_alldecks_view_indep_via_dealer` |
| F008 | OPEN-BY-DECISION | note:243 still lists `Makefile.rocq` "for the project build"; STATUS.md:32-33 still says the real `make` is not run |
| F009 | RESOLVED | the note's spelling and the compiled spelling now agree on the implicit-argument regime, E001 having landed |

**Round-1 tally: 36 findings. 26 RESOLVED, 2 PASS confirmed, 5 PARTIAL, 1 OPEN,
8 OPEN-BY-DECISION** (F001-F008 overlap the PARTIAL count where a file-side half
landed).

---

## 2. New findings on the new material

### R2-B014 — BLOCKING. Two public identifiers name a symbol that no longer exists

`dealer_kernel_probe.v:66` `dealer_view_indep` and `:86`
`dealer_view_indep_of_deck`.

The rename pass renamed the readers to `dealer_shuffle_view` (`:46`) and
`dealer_shuffle_secret` (`:38`) but left the two theorems on the old `dealer_view`
stem. Under `mainSymbol_suffixes` the stem must be a declared symbol, and
`dealer_view` is now not one. The repository is uniform on this point: every
`_indep` theorem's stem is a real reader — `colour_view` →
`colour_view_indep_laws`/`colour_view_indep_fibers` (`reconstruct/design_privacy.v:86,100,113`),
`psl211_alldecks_view` → `psl211_alldecks_view_indep` (`instances/psl211/psl211_models.v:678,427`),
`pgl27_view` → `pgl27_view_indep` (`instances/pgl27/pgl27_secrecy.v:75,82`),
`alldecks_view` → `ttrans_view_indep_alldecks` (`reconstruct/transitivity_privacy.v:782,840`).

Two further reasons this is not cosmetic. First, the file contradicts itself:
its own positive control is `dealer_shuffle_view_indep_with_common_law`
(`:127`), built on the stem the theorem it controls does not use. Second,
round-1 B003's objection was that `dealer_view` reads as the dealer party's own
view against `protocol/`'s `dealer_*` party namespace (`dealer_idx`
`protocol/card_exchange_pismc.v:132`, `exchange_dealer:221`,
`dealer_with_input_encoding` `protocol/pgg_run.v:45`). That misreading survives
verbatim inside `dealer_view_indep`. B003 is therefore only half closed.

These are two of the seven identifiers C10 names as public, so this is a direct
failure of "match project conventions" on a C10 identifier, and it is closeable
inside the probe.

Pasteable, in `dealer_kernel_probe.v` and at the six call sites:

```coq
Lemma dealer_shuffle_view_indep
    (view : secretT -> deckT -> shuffleT -> viewT)
    (mu : R.-fdist viewT) :
  (forall s, secretP s != 0 ->
     fdistmap (fun dg => view s dg.1 dg.2) ((delta s) `x nu) = mu) ->
  dealer_shuffleP |= dealer_shuffle_view view _|_ dealer_shuffle_secret.
```

```coq
Lemma dealer_shuffle_view_indep_of_deck
    (valid : secretT -> deckT -> bool)
    (view : secretT -> deckT -> shuffleT -> viewT)
    (mu : R.-fdist viewT) :
```

Call sites to update: `dealer_kernel_probe.v:96,131,141`,
`pgl27_deterministic_bridge.v:185,367`, `psl211_alldecks_bridge.v:281`, and the
prose references at `dealer_kernel_probe.v:84,126`,
`pgl27_deterministic_bridge.v:170,336`, `psl211_alldecks_bridge.v:269`,
`psl211_per_deck_law_counter.v:96`, plus STATUS.md:134,135,210.

### R2-A009 — implementation-plan. `uniform_fdistmap_pointE` is the `have key` of a production lemma

`psl211_per_deck_law_counter.v:32-43` against
`reconstruct/design_privacy.v:56-64`. The statement is the RHS of the `have key`
inside `uniform_fdistmap_fiberE`, and the proof is that `have`'s script line for
line — `rewrite -sumr_const big_mkcond [RHS]big_mkcond /=.`, `apply: eq_bigr => x _; rewrite !inE /=.`,
`case: (f x == v); last by rewrite andbF.`, `rewrite andbT; case: ifPn => xA.`,
and the two `fdist_uniform_supp_*` closers — with only a leading `fdistmap_E`
added to get from the pushforward's value to the sum.

This is a duplicate of production proof content living in a probe. It is not a
defect of the probe: the probe needs the point form and production does not
export it, and STATUS.md:216-221 says so precisely, naming the home
(`reconstruct/design_privacy.v`), the statement and the reason (`pr_countE` is
about a product law and a `Pr` event, not a pushforward point). Under the
criterion you set, that is a properly specified implementation-plan item.

One thing to add when it is promoted: `uniform_fdistmap_fiberE` should then be
re-proved through it, so the script exists once. Its proof becomes
`by move=> Hfib; apply/fdist_ext => v; rewrite !uniform_fdistmap_pointE Hfib.`
The `.v` comment at `:27-31` already says "the point form of
uniform_fdistmap_fiberE"; it should also say that factoring it out shortens
`fiberE`, because STATUS.md does not travel with the code.

### R2-E008 — OPEN inside the probe, not open-by-decision

Your message groups E008 with F001/Alt-8 as blocked on production edits. They are
different findings and only F001 is blocked.

F001 is about `alldecks_view_law` being `Local`, which would let the probe skip
proving the PGL counting at all. E008 is about the probe proving it **twice**,
and both copies are in one probe file: `pgl27_dealer_view_law` (`:124-165`) and
`pgl27_alldecks_dealer_view_law` (`:280-319`), 27 of ~34 lines identical.

The general one subsumes the special one, and the special one's own proof
already supplies the missing premise: line 164 passes `(orbit_encode_deck s)`
into exactly the `ktuple_encode_uniform` slot that line 318 fills with `Huniq`,
so `orbit_encode_deck s : uniq (orbit_encode s)`. Moving
`pgl27_alldecks_dealer_view_law` ahead of `pgl27_dealer_view_law` — into Section
`PGLDeterministic`, or into a shared section before both — reduces the second to:

```coq
Proof.
move=> HC.
exact: (@pgl27_alldecks_dealer_view_law R C s (orbit_encode s) Hdt
  (orbit_encode_deck s) HC).
Qed.
```

No production file is touched. Non-blocking for C10 (it is script economy, not
naming), but it should not be carried in the implementation plan as if it were
blocked on `alldecks_view_law`.

### R2-C007 — SHOULD-FIX. `cutT` in the PGL bridge contradicts its own instance

`pgl27_deterministic_bridge.v:29` and `:240` declare `Local Notation cutT`, and
the file's prose says "cut" 6 times against "shuffle" once.

STATUS.md:64-67 justifies this with "inside the two instance files the local
notation stays `cutT`". That rule is right for PSL and wrong for PGL. Measured
with `\b` word boundaries:

| File | cut/cuts | shuffle/shuffles |
|---|---|---|
| `instances/pgl27/pgl27_secrecy.v` | 0 | 7 |
| `instances/pgl27/pgl27_orbit.v` | 0 | 20 |
| `instances/psl211/psl211_models.v` | 20 | 2 |
| `instances/psl211/psl211_alldecks.v` | 19 | 2 |
| `reconstruct/transitivity_privacy.v` | 0 | 25 |

PGL's own home never says "cut", so the PGL bridge is drifting from its instance
and from the generic home at once. Fix: `Local Notation shuffleT := (pgg_gT
pgl27_M).` at `:29` and `:240`, the same substitution in the prose at
`:40,41,45,121,201`, and a correction to STATUS.md:64-67 naming PSL only.

### R2-E010 — SHOULD-FIX. Adjudicating the positional mutation

You asked me to judge STATUS.md:247-250 on
`pgl27_alldecks_dealer_view_law_without_validity`
(`pgl27_deterministic_bridge.v:326-332`), whose error is
`The term "HC" has type "is_true (#|C| <= 3)%N" while it is expected to have type "is_true (uniq d)".`

**I accept it in part.** STATUS.md says the positional mismatch "is still the
intended reason, since the coalition-size argument only lands in the `uniq d`
slot because `uniq d` was dropped". That is correct as far as it goes: the
mutation does certify that `uniq d` is present in the signature and consumes an
argument, which is what the ledger's C3 row asks about the *link*.

Where I do not follow it: an argument-position mismatch certifies a syntactic
fact, not a mathematical one. It shows the lemma *has* a `uniq d` premise; it
does not show the lemma *needs* one. A vacuous premise would produce the
identical error. The other six mutations do not have this weakness — four fail
on a leftover arrow or a non-convertible `erefl`, which cannot be produced by a
vacuous premise, and two of those are positively controlled.

The gap is small and is closed cheaply by giving this mutation the positive
control the other two have, which pins the arity and leaves the dropped premise
as the only difference:

```coq
(** pgl27_alldecks_dealer_view_law_with_validity — the positive control for
    the mutation below: with the validity premise supplied the same spelling
    is the per-deck view law, so the failure below is the dropped uniq d and
    not the arity. *)
Definition pgl27_alldecks_dealer_view_law_with_validity
    (C : {set 'I_8}) (s : bool) (d : deckT)
    (Hdt : (0 < #|dtuple_on (size (enum C)) [set: 'I_8]|)%N)
    (Hu : uniq d) (HC : (#|C| <= 3)%N) :
  fdistmap (fun g => pgl27_dealer_view C s d g)
    ((`U pgl27_G_pos) : R.-fdist cutT) = @pgl27_dealer_mu R C Hdt :=
  @pgl27_alldecks_dealer_view_law C s d Hdt Hu HC.
```

The stronger check — that validity is mathematically load-bearing, by exhibiting
a deck with a repeated card whose view law differs from `pgl27_dealer_mu` — is
asserted in prose at `:321-325` ("A deck with a repeated card does not have the
common view law") and compiled nowhere. The ledger does not ask for it, so I do
not require it, but the prose should not assert it as though it had been checked.
Note that the PSL side does compile the analogous necessity claim, in
`psl211_perdeck_no_common_law` (`psl211_per_deck_law_counter.v:100-116`), which
is the strongest single result in the new material.

### R2-E009 — NOTE. The `@` spellings, and the `Arguments` directives to propose

You asked whether the explicit applications are acceptable style or whether
`Arguments` directives should be proposed for the permanent home. Counts: 65 `@`
heads across the seven files, concentrated in `pgl27_deterministic_bridge.v`
(35) and `psl211_alldecks_bridge.v` (14); the heaviest are
`@dealer_shuffle_view` (8), `@pgl27_dealer_mu` (7), `@dealer_shuffle_secret`
(7), `@dealer_view_indep` (5), `@dealer_shuffleP` (5).

The spelling is correct and STATUS.md:252-268 explains why it is needed. But it
is not what the permanent home looks like. The nearest production analogue,
`instances/pgl27/pgl27_secrecy.v:216-219`, states the same shape with no `@` at
all:

```coq
  alldecksP (fdist_uniform card_bool) pgl27_G_pos (R:=R) pgl27_class_decks_pos
  |= alldecks_view (@pgg_rho pgl27_M) (fdist_uniform card_bool) pgl27_G_pos
       pgl27_class_decks_pos C
  _|_ alldecks_secret (fdist_uniform card_bool) pgl27_G_pos
        pgl27_class_decks_pos.
```

There the carrier arguments are implicit and the distribution arguments explicit,
which is exactly the split that removes the `@`. Proposed for the permanent home,
to be compiled before it is adopted:

```coq
Arguments dealer_shuffleP {R secretT deckT shuffleT} secretP delta nu.
Arguments dealer_shuffle_secret {R secretT deckT shuffleT} secretP delta nu.
Arguments dealer_shuffle_view {R secretT deckT shuffleT viewT}
  secretP delta nu view.
Arguments dealer_shuffle_view_indep {R secretT deckT shuffleT viewT}
  secretP delta nu view mu.
```

Non-blocking: `@` is correct, merely verbose, and the directives change no
statement. Worth adding to `dealer_kernel_probe.v` now so the bridges read the
way their permanent siblings will.

### R2-D006 — SHOULD-FIX. The three `_via_dealer` theorems do not name what they restate

`pgl27_deterministic_bridge.v:199-203`, `:334-339`, and
`psl211_alldecks_bridge.v:288-292`.

Each of the three restates an existing theorem verbatim
(`pgl27_view_indep` / `pgl27_view_indep_via_profile`,
`pgl27_view_indep_alldecks`, `psl211_alldecks_view_indep`). The `_via_dealer`
suffix signals "another route", which is the right name, but no comment names the
theorem being re-derived, so a reader cannot tell from the file whether this is a
new result or a second proof of an old one. The repository's own precedent for
exactly this situation states it outright —
`instances/pgl27/pgl27_profile_privacy.v:79-82`: "The statement is
pgl27_view_indep verbatim; only the route differs, so the record-level theorem
costs the instance nothing beyond its two premises."

One clause per comment closes it, for example at `:199`: "The statement is
`pgl27_view_indep` verbatim; only the route differs."

### R2-F010 — SHOULD-FIX. No permanent home is recorded for two of the generic movers

STATUS.md records a home for the dealer declarations
(`reconstruct/transitivity_privacy.v`, at `:64-67`) and for
`uniform_fdistmap_pointE` (`reconstruct/design_privacy.v`, at `:216-221`). It
records none for `inde_RV_fdistmap`, `fdistmap_prod_sectionE` or
`uniform_fdistmap_fiberTE`.

Round 1 proposed homes for all three, but STATUS.md:380-382 states that
`naming-audit.md` "still uses the old identifiers", so a reader who follows the
pointer to recover a home lands on `uniform_fdistmap_sectionsT` and
`fdistmap_prod_sections`, names that no longer exist. Since your criterion for an
implementation-plan item is that the probe state "the proposed permanent name,
statement and home precisely", the home column should be in STATUS.md against the
current names:

| Declaration | Proposed permanent home |
|---|---|
| `dealer_shuffleP`, `dealer_shufflePE`, the two readers, the two independence theorems | `reconstruct/transitivity_privacy.v` |
| `inde_RV_fdistmap` | `reconstruct/transitivity_privacy.v` |
| `fdistmap_prod_sectionE` | `reconstruct/transitivity_privacy.v`, beside `fdistmap_prod_const` |
| `uniform_fdistmap_fiberTE`, `uniform_fdistmap_pointE` | `reconstruct/design_privacy.v`, Section `fibers` |

### New material, rubric A-F, everything else

**A, collisions.** Zero, across all 72 names, Python `\b` scan. Confirms the
rename pass's own check independently.

**B, conventions, the 70 new names.** Every instance name carries `pgl27_` or
`psl211_`; carrier qualifiers are last and spelled out; no development word, no
metaphor, no verb in a lemma name. Specific judgments:

- `_at_R` on the four `concrete_instances.v` wrappers: **accepted, and the
  reasoning is better than the precedent.** `notes/probes/2026-09-15-pgl27-view-entropy/concrete_real_instance.v:26,40`
  names both of its wrappers `..._realE`, and both are equations. Three of the
  four here are independence statements, so `E` would misname them; the one that
  is an equation keeps `PE` and appends the carrier, `psl211_dealerPE_at_R`
  (`:70`). That is the `E`-means-equation rule applied rather than precedent
  copied. NOTE: `_at_R` has no precedent, and the file's own notation for the
  carrier is `Rc` (`:27`), so record the suffix somewhere durable or a third
  probe will invent a third spelling.
- `psl211_perdeck_no_common_law` (`:100`): **precedent confirmed.** The repo has
  `s5_no_secret_dim3`, `s5_no_secret_dim4` (`reconstruct/s5_nogo.v`),
  `partial_sum_no_info` (`reconstruct/pgg_sum_mod.v`), `no_walk`
  (`protocol/pgg_algebra_syntax.v`), and a whole `s5_nogo.v`. Good name for the
  strongest new result.
- `pgl27_dealer_view_law` and `pgl27_alldecks_dealer_view_law` end in `_law`
  while stating equalities, which looks like an `E` violation but is not:
  `reconstruct/transitivity_privacy.v:788` `alldecks_view_law` is the same shape.
  Accepted.
- `pgl27_dealer_delta`/`_nu` and `psl211_dealer_delta`/`_nu`: the Greek-letter
  components carry no mathematics on their own, but they name the generic
  `delta` and `nu` Variables (`dealer_kernel_probe.v:22,23`) and the paper's
  symbols, so they are decodable by anyone who has read the generic file.
  Accepted.
- `uniform_fdistmap_pointE`, `psl211_perdeck_massE`, `psl211_perdeck_law_neq`,
  `psl211_deal_pos` (matching `pgl27_G_pos`, `psl211_G_pos`): all good.
- `fdistmap_prod_sectionE_with_sections` (`:106`) reads awkwardly, but it is a
  control, it is honest, and it parallels
  `dealer_shuffle_view_indep_with_common_law`. NOTE only.

**C, vocabulary.** Banned vocabulary: zero. Residual drift: R2-C007 (PGL "cut"),
C002 (inherited from production), C005 (`deck description` twice in
`psl211_per_deck_counter.v`). The two new files are internally clean.

**D, statement comments.** 72 of 72 declarations carry one. A scripted scan for
status markers, effort estimates, "key lemma" meta, proof strategy and
measurements inside `(** ... *)` blocks returns **zero** hits. The new files'
comments carry both halves: `psl211_perdeck_no_common_law` (`:94-99`) states the
fact and then its position — "the per-deck route to privacy is closed for this
instance, and only the average over deals that dealer_view_indep asks for
remains" — which is the sharpest position sentence in the probe. The `_at_R`
wrappers likewise state why a concrete carrier matters ("it witnesses that the
model's hypotheses have a solution over a field the reader can compute in",
`:33-34`). Residual: D002 (one measurement left in a file-level `(* *)` comment)
and R2-D006.

**E, script and regime.** The header regime is uniform and correct; its
consequence is R2-E009. Seals paired, `Print Assumptions` after `End`, no long
lines, no lone `by []`, mutation errors captured. Residual: R2-E008, R2-E010.

**F, design note.** Unchanged and untouched (`git log` shows the note still at
`9f54a3a`, working tree clean for it), as decided. F002, F004, F006, F008 stand;
F003 is half closed on disk; F004 widens because there are now seven `.v` files
against the note's six.

---

## 3. What blocks C10 and what does not

**Blocking (1).**

- **R2-B014** — `dealer_view_indep` and `dealer_view_indep_of_deck`,
  `dealer_kernel_probe.v:66,86`. Two of the seven C10 public identifiers carry a
  stem that is no longer a declaration, against four repository precedents, and
  the file's own positive control uses the other stem. Closeable inside the probe
  by a mechanical rename plus one compile of the seven files.

**Not blocking, closeable inside the probe (should be done before the
implementation plan).** R2-E008 (duplicated proof), R2-C007 (`cutT` in PGL),
R2-E010 (positive control for the positional mutation), R2-D006 (name the
restated theorem), R2-E009 (`Arguments` directives), R2-F010 (home table), C005
(`deck description`), D002 (last measurement in a source comment).

**Implementation-plan items, properly specified — these do not block C10.**
A001 and A002 placements, R2-A009, F001. For each of these the probe states the
proposed permanent name, the statement and the home precisely, with one
qualification: the home for `inde_RV_fdistmap`, `fdistmap_prod_sectionE` and
`uniform_fdistmap_fiberTE` is recorded only in `naming-audit.md`, which uses the
superseded names, so R2-F010 should land first for the specification to be
readable at the current spellings.

**Implementation-plan items, owned elsewhere.** C002 (production vocabulary),
F002, F004, F006, F008 and the remainder of F003 (the tracked design note, the
user's to edit), and the file renames STATUS.md:120-122 reports.

---

## VERDICT: NO-GO

Round 2 closed 26 of the 36 round-1 findings outright, confirmed 2 more as
already clean, and left 5 partial, 1 open in the probe and 8 open by decision.
The work is close: the collision half of C10 is now verified over all 72
declarations with zero hits, every declaration carries a statement comment with
no status or measurement content, the elaboration regime matches the permanent
home, and the mutation evidence is tabulated with real error texts.

C10 fails on one item. `dealer_view_indep` and `dealer_view_indep_of_deck` are
public identifiers of the proposed dealer model, and after the rename pass their
main symbol does not exist while the same file's control lemma uses the corrected
stem. C10's claim is that the proposed public identifiers match project
conventions; on two of the seven, they do not, and the repository is uniform
about the convention they break.

This is a two-name rename and a recompile. Nothing else in the current probe
blocks C10.
