# C9 flow sketch audit

Date: 2026-09-18

Independent read-only audit; no Rocq process was started. Line numbers refer to
the probe files as they stood before the C9 milestones M1-M7 re-pointed the
bridges and renamed identifiers.

---

AUDIT: C9 `concrete_instances.v` flow sketch vs. the real probe files
Read-only. No Rocq process started. All line numbers are from the files as they stand on disk.

---

## Q1. Does every named object exist with the claimed statement?

Absolute paths (abbreviated below as `KERNEL`, `TRANSPORT`, `PGLBR`, `PSLBR`, `PSLCNT`):
- KERNEL = `/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/notes/probes/2026-09-17-general-dealer-law/dealer_kernel_probe.v`
- TRANSPORT = `.../notes/probes/2026-09-17-general-dealer-law/carrier_transport_probe.v`
- PGLBR = `.../notes/probes/2026-09-17-general-dealer-law/pgl27_deterministic_bridge.v`
- PSLBR = `.../notes/probes/2026-09-17-general-dealer-law/psl211_alldecks_bridge.v`
- PSLCNT = `.../notes/probes/2026-09-17-general-dealer-law/psl211_per_deck_counter.v`

| Sketch name | file:line | verdict |
|---|---|---|
| `dealer_shuffleP` | KERNEL:23 `Definition dealer_shuffleP : R.-fdist (secretT * (deckT * cutT)) := secretP \`X (fun s => (delta s) \`x nu).` | MATCH. Arity after discharge is 7 explicit args (`R secretT deckT cutT secretP delta nu`; `viewT` is not used so not discharged — confirmed by KERNEL:85 `@dealer_shuffleP R secretT deckT cutT secretP delta nu`). The sketch writes it as `dealer_shuffleP P delta nu`, 3 args. Cosmetic. |
| `dealer_secret` / `dealer_view` | KERNEL:27, KERNEL:30-33 | MATCH. `dealer_view` discharges 8 + `view` (KERNEL:86). |
| `dealer_shufflePE` [C1] | KERNEL:35-38 | Exists, but **used by nothing** — no bridge file mentions it. |
| `dealer_view_indep` [C2] | KERNEL:40-45 | MATCH. |
| `dealer_view_indep_of_deck` [C3] | KERNEL:53-60 | Exists, but **used by nothing**. See Q4. |
| `inde_RV_fdistmap_pullback` [C4] | TRANSPORT:23-25 `fdistmap f P \|= X _\|_ Y -> P \|= (X \o f) _\|_ (Y \o f).` | MATCH. Used by nothing. |
| `pgl_delta` / `pgl_nu` | PGLBR:81-84 (`fdist1 (orbit_encode s)`, `` `U pgl27_G_pos``) | MATCH. |
| `pgl_all_delta` | PGLBR:247-248 `` `U (pgl27_class_decks_pos s)`` | MATCH. No `pgl_all_nu` exists; the cut law is written inline as `` `U pgl27_G_pos``. |
| `psl_delta` / `psl_nu` | PSLBR:159, 161 | MATCH, with a caveat: `Definition psl_delta (_ : bool) : R.-fdist dealT := \`U psl_deal_pos` — the PSL dealer law **ignores the secret**. |
| `pgl_fixed_view_law` | PGLBR:137-141 | **MISMATCH with the sketch's step description.** Actual: `Lemma pgl_fixed_view_law (C : {set 'I_8}) (s : bool) (Hdt : (0 < #\|dtuple_on (size (enum C)) [set: 'I_8]\|)%N) : (#\|C\| <= 3)%N -> fdistmap (fun g => pgl_generic_view C s (orbit_encode s) g) pgl_nu = pgl_common_mu C Hdt.` It is a law under **`pgl_nu` alone**, at the single deck `orbit_encode s`, not under `(delta s \`x nu)`. `Hdt` is an explicit lemma argument, not a side condition, and `mu` is `pgl_common_mu C Hdt` (PGLBR:130-135), the uniform law on `dtuple_on k` read as a masked `{ffun 'I_8 -> 'I_8}`, which **depends on the chosen `Hdt` proof term**. |
| `pgl_deck_view_law` | PGLBR:268-272 | **MISMATCH, same reason.** Actual: `uniq d -> (#\|C\| <= 3)%N -> fdistmap (fun g => pgl_generic_view C s d g) ((\`U pgl27_G_pos) : R.-fdist cutT) = pgl_common_mu R C Hdt.` Again a law under the cut law only. Note `s` is a **dummy**: `pgl_generic_view C s d g` (PGLBR:113-116) does not read `s`. Validity is `uniq d`, and `deck_ok sh := uniq sh` at `instances/pgl27/pgl27_orbit.v:94`, so the sketch's "validity `uniq d`" is right. |
| `psl_mixed_lawE` | PSLBR:236-237 | **MISMATCH.** Actual: `(#\|C\| <= 5)%N -> psl_mixed_law C false = psl_mixed_law C true.` It is an **equality between the two chiralities' mixed laws**, not "the law equals one `mu`". The common `mu` is *chosen* afterwards as `psl_mixed_law C true` at PSLBR:259. This is the only one of the three rows that is genuinely a law under `(delta b \`x nu)` (PSLBR:214-217). |
| `psl_section_law` | PSLBR:224-229 | MATCH. Per fixed cut `g`, the two chiralities push `` `U psl_deal_pos`` to the same law. |
| `psl211_alldecks_per_cut_count` | `instances/psl211/psl211_alldecks.v:1334-1337`, section vars `C g v` at :868-870 | MATCH. |
| `pgl_dealerP_map` | PGLBR:93-94 `fdistmap pgl_embed (pgl27P R) = pgl_dealerP.` | MATCH. Direction: `fdistmap` on the LHS carries the **model** law `pgl27P`, the generic law is on the RHS. That is C4's premise shape with `P := pgl27P`, `f := pgl_embed`. |
| `pgl_all_dealerP_E` | PGLBR:254-258, `Proof. by []. Qed.` | **Equality on the same carrier, no map at all.** Both sides are `R.-fdist (bool * (8.-tuple 'I_8 * pgg_gT pgl27_M))` and the proof is `erefl`. The generic law is *definitionally* `alldecksP` (`reconstruct/transitivity_privacy.v:771`). |
| `psl_law_E` | PSLBR:171-172 `fdistmap psl_assoc (psl211_alldecksP R) = psl_genericP.` | MATCH, same direction as `pgl_dealerP_map`. Non-trivial: it proves the uniform law on `bool * dealT` factors as uniform-bool times uniform-deal (PSLBR:183 `rewrite !cardsT card_prod card_bool natrM invfM mulrA`). |
| `*_view_square` / `*_secret_square` | `pgl_view_square` PGLBR:118, `pgl_secret_square` PGLBR:124 (both `Proof. by []. Qed.`); `psl_view_square` PSLBR:192 (`by apply: boolp.funext => -[[b d] g]` — **not** `erefl`), `psl_secret_square` PSLBR:199 (`by []`) | PARTIAL MISMATCH. **There is no `pgl_all_view_square` and no `pgl_all_secret_square`.** What exists for PGL-all is `pgl_all_viewE` (PGLBR:260-266), an equality between the two *view definitions*, not a composite-with-a-map equation; and nothing at all on the secret side. |
| `psl_per_deck_fibers_differ` [C8] | PSLCNT:233-234 `#\|psl_counter_fiber true\| != #\|psl_counter_fiber false\|.` | MATCH. |

Terminals, all three matching the pre-existing theorems exactly:
- `pgl_indep_via_generic` PGLBR:208-209 = `pgl27_view_indep` (`instances/pgl27/pgl27_secrecy.v:82-83`).
- `pgl_all_indep_via_generic` PGLBR:318-325 = `pgl27_view_indep_alldecks` (`pgl27_secrecy.v:215-220`).
- `psl_indep_via_generic` PSLBR:264-268 = `psl211_alldecks_view_indep` (`instances/psl211/psl211_models.v:427-430`).

---

## Q2. Is the claimed gap real?

**Yes, and it is larger than stated.** No bridge file requires either kernel probe (PGLBR:1-12, PSLBR:1-9, PSLCNT:1-8 contain no probe `Require`).

Copies that **are** drop-in replaceable (same definition, same discharged argument order, same explicitness):
- `bridge_dealerP`/`bridge_secret`/`bridge_view`/`bridge_view_indep` (PGLBR:28-48) and `psl_bridge_*` (PSLBR:35-56) vs `dealer_shuffleP`/`dealer_secret`/`dealer_view`/`dealer_view_indep`. Section variable order is identical (`R0 S0 D0 G0 V0 P0 delta0 nu0` vs `R secretT deckT cutT viewT secretP delta nu`), and the use sites confirm the arities (PGLBR:87 uses 7 explicit args, PGLBR:119 uses `@bridge_view` with 8 + view).
- `bridge_pullback` (PGLBR:50-59) / `psl_bridge_pullback` (PSLBR:58-67) vs `inde_RV_fdistmap_pullback`. Discharged order coincides: `R0 A0 B0 TA0 TB0 Q0 f0 X0 Y0` vs `R A B TA TB P f X Y`.

Copies that **have no counterpart in C1-C4**:
- `bridge_pushforward` (PGLBR:61-70) — the converse of C4. **Dead**: no use site anywhere.
- `psl_bridge_pullback_eq` (PSLBR:76-83) — **load-bearing**, used at PSLBR:272. This is the hang workaround.
- `fdistmap_prod_sections` (PSLBR:85-112) — **load-bearing**, used at PSLBR:240.
- `uniform_fdistmap_sectionsT` (PSLBR:127-140) — **load-bearing**, used at PSLBR:231. Wraps `uniform_fdistmap_fiberE` (`reconstruct/design_privacy.v:51`).

And two C1-C3 declarations are instantiated by **nothing**: `dealer_shufflePE` and `dealer_view_indep_of_deck`.

So "replace a copy by the real declaration" is a drop-in for four declarations and impossible for three (they do not exist in the kernel/transport probes). One thing to verify with a single `About` when writing C9: whether `Set Implicit Arguments` leaks into these files from upstream — neither KERNEL nor PGLBR sets it locally, and both import `transitivity_privacy`, so the status should be the same, but it is a one-call check.

---

## Q3. Does the composition typecheck at the endpoints the sketch assumes?

**PGL-det.** Generic carrier `bool * (8.-tuple 'I_8 * pgg_gT pgl27_M)`; model carrier `bool * pgg_gT pgl27_M`; map `pgl_embed : bool * cutT -> bool * (deckT * cutT)` (PGLBR:90-91). C4 lands on `pgl27P |= (bridge_view ... \o pgl_embed) _|_ (bridge_secret ... \o pgl_embed)`; both squares are `erefl`, so `exact:` would close it, and the file instead rewrites (PGLBR:222). No table term, no hang risk. **OK as sketched.**

**PGL-all.** Generic carrier = model carrier, identically. There is **no carrier map**, C4 is not used, and `inde_RV_fdistmap_pullback` cannot appear. What the file does is PGLBR:355 `rewrite -pgl_all_dealerP_E -pgl_all_viewE; exact: Hgen.` — two rewrites of definitional equalities, and the **secret side is discharged by conversion alone** (`alldecks_secret` vs `bridge_secret` never appear in an equation). The sketch's "observe ... by `inde_RV_fdistmap_pullback` [C4]" is simply wrong here.

**PSL-all.** Generic carrier `bool * (psl211_deal * pgg_gT psl211_M)`; model carrier `psl211_inputT * cutT = (bool * psl211_deal) * cutT`; map `psl_assoc` (PSLBR:167-169). C4's conclusion is `psl211_alldecksP R |= (psl_bridge_view ... \o psl_assoc) _|_ (psl_bridge_secret ... \o psl_assoc)`. The secret square is `erefl`, but the **view square is not**: it needs `boolp.funext` plus a case split on the nested pair (PSLBR:197), because `((u.1.1, u.1.2)) = u.1` is not definitional for `prod`. So bare C4 forces a `rewrite psl_view_square` into a goal that holds `psl211_alldecks_view` — exactly the recorded hang. PSLBR:18-25 records the measurement: `rewrite Htrue`, `move: Htrue => ->` and `rewrite Htrue Hfalse` each hit a 30 s `Timeout` against 0.01 s for every other sentence, because the rule and the goal differ only in the chirality bit and the matcher descends into the two 132-row block tables. The compiled route is `Local Opaque psl211_alldecks_view` (PSLBR:26) plus `psl_bridge_pullback_eq`, which takes both squares as hypotheses and consumes them by `move=> <- <-` while `X1`/`Y1` are still variables (PSLBR:83). **A C9 written from the sketch as given would reintroduce the hang.**

The same class of risk sits in PSLCNT (660-row `psl211_elem_table`, `Local Opaque` at PSLCNT:199, term-mode headline at PSLCNT:239-245) — but C8 has no `realType` in it at all, so C9 should not touch it.

---

## Q4. Steps that live outside the flow, and the reverse

**PGL-all is not routed through C3.** PGLBR:339-354 applies `bridge_view_indep` (the C2 shape) and then inlines `fdistmap_prod_const` (`reconstruct/transitivity_privacy.v:216`), extracting validity as `d \in class_decks orbit_class deck_ok s` then `deck_ok d`. `dealer_view_indep_of_deck` is never named. The PGL-det row is the same shape (PGLBR:194-205). So **C3 is instantiated by nothing today**, and the sketch's "feeds C3" describes a file that does not exist.

The C3 route is achievable, so this is a correction and not a refutation: take `valid s d := uniq d`, premise 1 is PGLBR:346-351 verbatim, premise 2 is `pgl_deck_view_law` up to eta (`fdistmap (view s d) nu` vs `fdistmap (fun g => view s d g) nu`). For PGL-det take `valid s d := (d == orbit_encode s)` and premise 2 is `pgl_fixed_view_law`. Either way it is a change to a bridge proof, not a wrapper C9 can add for free.

**Also outside the flow but presented as inside it:** `fdistmap_prod_const` is the lemma that actually lifts both PGL per-deck laws to the mixed law, and it appears nowhere in the sketch. Neither do `pgl_all_viewE`, `psl_bridge_pullback_eq`, `fdistmap_prod_sections`, `uniform_fdistmap_sectionsT`, `Local Opaque psl211_alldecks_view`, nor the external interfaces (`inde_prod_kernel_fst`, `ktuple_encode_uniform`, `uniform_fdistmap_fiberE`, `psl211_alldecks_per_cut_count`).

**PSL and C3.** The sketch's claim is *sound but not compiled*. `psl_delta` is uniform on all of `[set: psl211_deal]` (PSLBR:153-159), so every deal has positive mass under both chiralities, so any `valid` meeting C3's first premise must accept `psl_counter_deal` for both `s`. C8 then gives `#|fiber true| = 0` and `#|fiber false| = 1` (PSLCNT:239-243), and since `psl_nu` is uniform on `pgg_G psl211_M` and `psl_counter_fiber` is cut down to that same group (PSLCNT:203-206), the two `fdistmap (view s d) nu` differ in mass at `psl_counter_view`, so no single `mu` exists. Every step of that is true; **none of it is a lemma in the probe directory.** The inference "C8 shows the PSL line cannot go through C3" is one unwritten step away from what is machine-checked. `psl_per_deck_fibers_differ` is genuinely outside the flow (nothing requires PSLCNT), so calling it "boundary result, not a step" is correct.

---

## Q5. "At a real field"

**The concrete carrier.** `Rdefinitions.R`, given its `realType` structure by `mathcomp/reals_stdlib/Rstruct.v:432`:

```
HB.instance Definition _ := ArchimedeanField_isReal.Build R
  (@Rsup_ub (0 : R)) (real_sup_adherent 0).
```

A sweep of `/Users/cheng-huiweng/Projects/coq/_opam/lib/coq/user-contrib` for real-structure instances returns only this one. `mathcomp/real_closed/realalg.v:897` and `mathcomp/algebra/rat.v:737` build `Num.IntegralDomain_is{Lt,Le}Real`, i.e. real *domains*, not `realType` (no supremum), so they cannot instantiate `R.-fdist`.

**Repo precedent: yes.** `/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/notes/probes/2026-09-15-pgl27-view-entropy/concrete_real_instance.v` instantiates two headline theorems at `Rdefinitions.R` by `exact:` wrappers, imports `Rstruct` at line 3, and was audited GO (`.../2026-09-15-pgl27-view-entropy/soundness-audit.md:13,25`). That is exactly the C9 shape: thin wrappers, no re-derivation.

**Expected whitelist.** Current abstract-`R` report (STATUS.md:27-31) is the three mathcomp `boolp` axioms, declared at `mathcomp/classical/boolp.v:74,77,80`: `functional_extensionality_dep`, `propositional_extensionality`, `constructive_indefinite_description`. Instantiating at `Rdefinitions.R` adds the standard-real carrier's assumptions, which from the sources are:

- `ClassicalDedekindReals.sig_forall_dec` (`Stdlib/Reals/ClassicalDedekindReals.v:110`) and `ClassicalDedekindReals.sig_not_dec` (:115) — the only genuine `Axiom` commands in the construction;
- the opaquely ascribed module constants, because `Module RbaseSymbolsImpl : RbaseSymbolsSig.` (`Stdlib/Reals/Rdefinitions.v:65`) hides `R, Rabst, Rrepr, Rquot1, Rquot2, R0, R1, Rplus, Rmult, Ropp, Rlt` and the six `_def` equations, and `Module RinvImpl : RinvSig.` (:204) hides `Rinv, Rinv_def`;
- possibly `Stdlib.Logic.Epsilon.epsilon_statement` (`Stdlib/Logic/Epsilon.v:20`), since `Rstruct.v:29` imports `Epsilon`.

I could not run Rocq, so treat the third and fourth bullets as *predicted*. The honest acceptance criterion for C9 is: the literal report is the three `boolp` axioms plus the standard-real set above, and contains **no project-local constant and no `Admitted`**. The 2026-09-15 precedent's design note records the same thing only as "the classical real-number assumptions reported by `Print Assumptions`" (`notes/20260915-pgl27-view-census-entropy-design.md:52`), i.e. the exact list was never written down. C9 should paste it in, or the ledger's C9 row stays unfalsifiable.

---

## Q6. The `_CoqProject` logical path

Today `.../2026-09-17-general-dealer-law/_CoqProject` maps twelve production directories and **no path for `.`** (lines 7-18). Worse, the five existing `.vo` files disagree about their own library names. Second line of each `.glob`:

```
carrier_transport_probe.glob         FTop.carrier_transport_probe
dealer_kernel_probe.glob             FTop.dealer_kernel_probe
pgl27_deterministic_bridge.glob      FTop.pgl27_deterministic_bridge
psl211_alldecks_bridge.glob          Fpsl211_alldecks_bridge
psl211_per_deck_counter.glob         Fpsl211_per_deck_counter
```

The first three were built through `Makefile.rocq`, where `coq_makefile` silently inserted `-R . Top` (`Makefile.rocq.conf:35`); the last two through the manual single-file command in `STATUS.md:144-155`, which has no mapping for `.`. So today **no two of them can be required from one file**.

Recommendation, following the 2026-09-15 precedent (`.../2026-09-15-pgl27-view-entropy/_CoqProject` ends with `-Q . pgl27_view_entropy_probe`, and its files cross-require with `From pgl27_view_entropy_probe Require Import ...`): add

```
-Q . general_dealer_law_probe
```

and recompile. Do **not** map the directory into `pgg_smc` or `pgg_reconstruct` — that would put probe modules on the production import path and cut against soundness invariant 9. Cost: all five files must be rebuilt because a `.vo`'s library name is recorded in the file. Measured budget from STATUS.md:17-18 is 5.20 s / 1.75 GB for PSLBR and 29.62 s / 1.85 GB for PSLCNT; the other three are unmeasured but small. C9 does not need PSLCNT (C8 has no `realType`), so that 29.62 s is optional. The `STATUS.md:157-159` warning stands: do not run `make` at the repo root, `instances/psl211/psl211_endpoints.v` is newer than its `.vo` and costs ~900 s / 17 GB.

**Name collisions: none.** Every proposed public identifier (`dealer_shuffleP`, `dealer_secret`, `dealer_view`, `dealer_shufflePE`, `dealer_view_indep`, `dealer_view_indep_of_deck`, `inde_RV_fdistmap_pullback`, `fdistmap_prod_sections`, `uniform_fdistmap_sectionsT`) occurs in the repo only inside this probe directory, and none occurs anywhere in the installed `infotheo` or `mathcomp` sources. No file named `dealer_kernel_probe.v`, `carrier_transport_probe.v`, `pgl27_deterministic_bridge.v`, `psl211_alldecks_bridge.v`, `psl211_per_deck_counter.v` or `concrete_instances.v` exists under any of the twelve mapped production directories. Two near-misses worth handing to the C10 naming audit: `dealer_secret_plug` (`protocol/pgg_execution_plug.v:94`) and `dealt_secret` (`reconstruct/transitivity_privacy.v:499`). The `*P` / `*_secret` / `*_view` triple matches the house convention (`alldecksP`/`alldecks_secret`/`alldecks_view` at `transitivity_privacy.v:771,777,782`; `support_posteriorP`/`_secret`/`_view` at `lib/support_posterior.v:64,71,76`).

---

## Q7. Anything wrong, vacuous, or stronger than the files support

**Soundness invariant 8** ("the three bridges instantiate all generic hypotheses. This is the vacuity check", `notes/20260917-general-dealer-law-feasibility-design.md:221-222`) is **currently false**, and C9 as sketched would not repair it. Against the generic declarations:

- `dealer_shuffleP` / `dealer_secret` / `dealer_view`: instantiated three times — but through copies, so the *real* declarations are instantiated zero times.
- `dealer_shufflePE`: instantiated zero times.
- `dealer_view_indep` [C2]: instantiated three times, through copies.
- `dealer_view_indep_of_deck` [C3]: **zero times**, and the sketch's PGL-all row would have to change a bridge proof to fix it.
- `inde_RV_fdistmap_pullback` [C4]: zero times through the real declaration; twice through copies (PGL-det via `bridge_pullback`, PSL via `psl_bridge_pullback_eq` which *calls* the copy).

Two further vacuity notes the ledger should carry: C2's premise is guarded by `secretP s != 0`, and all three instances set `secretP := fdist_uniform card_bool`, so the guard is discharged by `=> s _` at PGLBR:196, PGLBR:341 and PSLBR:259 and is **never exercised**; and `psl_delta` ignores its secret argument, so secret-dependence of `delta` is exercised only by the two PGL rows (non-degenerately only by `pgl_all_delta`).

Other sketch defects:

- `outside: choice of the concrete R and the Print Assumptions whitelist` puts C9's entire deliverable outside the program. What is left is the C5-C7 flow, which is already compiled. The sketch describes re-deriving the bridges rather than instantiating them, which is both redundant and, for PSL, actively dangerous (Q3).
- `cost 0, exact, unconditional` is attached to one line covering three rows whose premises differ (`#|C| <= 3` twice, `#|C| <= 5` once). "Unconditional" is defensible only in the sense "no computational assumption"; say that.
- No running accumulated value on each line, no `object`/`step`/`terminal` marking on several lines, and no interface marked for any external component. Per the DSL-first rule those are required.

---

## Findings

1. **BLOCKING** — The transport line is wrong for two of three instances. PGL-all uses no carrier map and no C4 (`pgl_all_dealerP_E` is `erefl` on the same carrier, PGLBR:254-258; the composition closes at PGLBR:355 by two rewrites and conversion). PSL cannot use bare C4 because `psl_view_square` is not definitional (PSLBR:197) and the required rewrite is the measured 30 s hang (PSLBR:18-25); the only compiled route is `psl_bridge_pullback_eq` + `Local Opaque psl211_alldecks_view`. Fix the sketch before writing code.
2. **BLOCKING** — C3 (`dealer_view_indep_of_deck`) is instantiated by nothing. The sketch asserts PGL-all "feeds C3", but PGLBR:339-354 uses C2 plus an inlined `fdistmap_prod_const`. Either re-route a PGL row through C3 (achievable: `valid s d := uniq d`, premise 1 = PGLBR:346-351, premise 2 = `pgl_deck_view_law` up to eta) or strike C3 from soundness invariant 8. As sketched, C9 would certify a vacuity check that does not hold.
3. **BLOCKING** — The `_CoqProject` has no path for `.` and the five existing `.vo` files disagree about their own library names (`Top.*` for three, root-less for two). Nothing can require anything until a uniform `-Q . general_dealer_law_probe` is added and the files C9 needs are rebuilt. Budget ~6 s for PSLBR plus the three small files; PSLCNT's 29.62 s is not needed.
4. **SHOULD-FIX** — Three load-bearing lemmas the PSL bridge depends on have no counterpart in C1-C4: `psl_bridge_pullback_eq` (PSLBR:76-83), `fdistmap_prod_sections` (PSLBR:85-112), `uniform_fdistmap_sectionsT` (PSLBR:127-140). The claim "C9 must instantiate the real declarations" cannot be met for the PSL row without first promoting these into the kernel/transport probes, which reopens already-audited C1-C4. Decide which, and say so in the ledger.
5. **SHOULD-FIX** — Two step descriptions misstate what the lemma says. `pgl_fixed_view_law` and `pgl_deck_view_law` are laws under the **cut law alone**, at a fixed deck; the lift to `(delta s \`x nu)` is `fdistmap_prod_const`, which the sketch never names. `psl_mixed_lawE` states `psl_mixed_law C false = psl_mixed_law C true`, an equality of two sections, not "equals one `mu`"; the `mu` is chosen at PSLBR:259.
6. **SHOULD-FIX** — "C8 shows the PSL line cannot go through C3" is sound but not compiled. The bridge from `#|fiber true| = 0 != 1 = #|fiber false|` to "no `mu` satisfies C3's second premise" is an unwritten step. Either compile it (one short lemma: uniform `psl_nu` on `pgg_G psl211_M`, two different fiber cardinalities, hence two different masses at `psl_counter_view`) or mark the sentence as a note rather than a result.
7. **SHOULD-FIX** — The ledger's C9 evidence line, "`Print Assumptions` reports no unexpected axioms", needs the literal expected list written in. Expected: the three `boolp` axioms plus `ClassicalDedekindReals.sig_forall_dec`, `ClassicalDedekindReals.sig_not_dec`, the sealed `Rdefinitions.RbaseSymbolsImpl.*` and `Rdefinitions.RinvImpl.*` constants, and possibly `Epsilon.epsilon_statement`. The 2026-09-15 precedent never recorded its list; do not repeat that.
8. **NOTE** — `bridge_pushforward` (PGLBR:61-70) is dead code with no counterpart in C4. Either delete it or record why the converse direction is kept.
9. **NOTE** — `dealer_shufflePE` (KERNEL:35) is used by nothing. If invariant 8 is meant to cover it, C9 should exercise it; otherwise the ledger should call it a pointwise sanity check rather than a hypothesis.
10. **NOTE** — C2's positivity guard `secretP s != 0` is never exercised (all three instances discharge it with `=> s _`), and `psl_delta` ignores its secret argument. C9 cannot claim either is tested.
11. **NOTE** — One file requiring both the pgl27 and psl211 stacks plus `Rstruct` is untested here; `manifest/pgg_analysis_manifest.v:75` already loads both instance stacks and compiles, so the risk is low, but PSLBR alone peaked at 1.75 GB. If it bites, split C9 into `concrete_instances_pgl.v` and `concrete_instances_psl.v`.
12. **NOTE** — The sketch omits every external interface. `inde_prod_kernel_fst` (`reconstruct/transitivity_privacy.v:167`), `fdistmap_prod_const` (:216), `ktuple_encode_uniform` (:591), `uniform_fdistmap_fiberE` (`reconstruct/design_privacy.v:51`) and `psl211_alldecks_per_cut_count` (`instances/psl211/psl211_alldecks.v:1334`) all enter through `pgg_reconstruct` / `pgg_smc` and must be marked.

---

## Corrected sketch

Two programs, because the sketch conflated them. The first is what C5-C7 already compile; the second is what C9 should be.

**(a) The compiled bridge flow, corrected** (descriptive; do not re-derive it in C9)

```
flow dealer_instance(I), I in {PGL-det, PGL-all, PSL-all}          -- running total = generic hypotheses discharged

object  R : realType                          section variable, all three files        -- 0
object  L := dealer_shuffleP R S D G P delta nu  [C1, 7 explicit args]                 -- 0
          PGL-det : S=bool D=8.-tuple 'I_8 G=pgg_gT pgl27_M   delta=pgl_delta  nu=pgl_nu
          PGL-all : same S D G                                 delta=pgl_all_delta  nu=`U pgl27_G_pos (unnamed)
          PSL-all : S=bool D=psl211_deal G=pgg_gT psl211_M     delta=psl_delta (constant in s)  nu=psl_nu
          P := fdist_uniform card_bool in all three
              (PSL: that factorisation is proved, not definitional -- psl_law_E, PSLBR:183)

step    per-deck law: the cut law pushes to one mu, at a fixed deck                     -- 1
          PGL-det : pgl_fixed_view_law   PGLBR:137   under pgl_nu only, d = orbit_encode s
                    premises  #|C| <= 3 ; mu = pgl_common_mu C Hdt, Hdt an explicit arg
          PGL-all : pgl_deck_view_law    PGLBR:268   under `U pgl27_G_pos only, any d
                    premises  uniq d, #|C| <= 3 ; s is a dummy
                    external: ktuple_encode_uniform  <- pgg_reconstruct.transitivity_privacy:591
          PSL-all : NOT THIS SHAPE. C8 refutes it. skip to the next step.

step    lift the per-deck law to the mixed law under (delta s `x nu)                    -- 2
          PGL-det, PGL-all : fdistmap_prod_const  <- pgg_reconstruct.transitivity_privacy:216
                    inlined at PGLBR:197 and PGLBR:342, NOT routed through C3 today
          PSL-all : psl_mixed_lawE  PSLBR:236  =  the two chiralities' mixed laws are EQUAL
                    <- fdistmap_prod_sections  PSLBR:85   (no C1-C4 counterpart)
                    <- psl_section_law         PSLBR:224
                    <- uniform_fdistmap_sectionsT PSLBR:127 (no C1-C4 counterpart)
                    <- uniform_fdistmap_fiberE <- pgg_reconstruct.design_privacy:51
                    <- psl211_alldecks_per_cut_count <- pgg_smc.psl211_alldecks:1334
                    premise #|C| <= 5 ; mu chosen as psl_mixed_law C true at PSLBR:259

step    L |= dealer_view view _|_ dealer_secret   by dealer_view_indep [C2]             -- 3
          all three; C3 (dealer_view_indep_of_deck) is used by NOTHING
          external: inde_prod_kernel_fst <- pgg_reconstruct.transitivity_privacy:167

step    carry to the model carrier -- THREE DIFFERENT SHAPES                            -- 4
          PGL-det : fdistmap pgl_embed (pgl27P R) = pgl_dealerP   PGLBR:93
                    then C4 (bridge_pullback), then rewrite pgl_view_square, pgl_secret_square
                    both squares are erefl; no table term; safe
          PGL-all : NO MAP. pgl_all_dealerP_E is erefl on the same carrier PGLBR:254
                    rewrite -pgl_all_dealerP_E -pgl_all_viewE ; exact  (PGLBR:355)
                    the secret side closes by conversion; no secret equation exists
          PSL-all : fdistmap psl_assoc (psl211_alldecksP R) = psl_genericP  PSLBR:171
                    then psl_bridge_pullback_eq PSLBR:76 with the two squares AS HYPOTHESES
                    psl_view_square is funext, not erefl, so a rewrite here is the 30 s hang
                    guard: Local Opaque psl211_alldecks_view  PSLBR:26   -- keep it

terminal  pgl_indep_via_generic   = pgl27_view_indep            (pgl27_secrecy.v:82)    -- 5
terminal  pgl_all_indep_via_generic = pgl27_view_indep_alldecks (pgl27_secrecy.v:215)   -- 5
terminal  psl_indep_via_generic   = psl211_alldecks_view_indep  (psl211_models.v:427)   -- 5
          computational assumptions invoked: 0.  premises: #|C| <= 3, 3, 5.

outside  psl_per_deck_fibers_differ [C8] PSLCNT:233 -- boundary result, no R in it.
         the step from it to "no mu satisfies C3 for PSL" is sound but NOT compiled.
outside  bridge_pushforward PGLBR:61 -- dead.
```

**(b) The C9 program**

```
flow concrete_instances.v                              -- running total = closed statements at Rdefinitions.R

object  Rc := Rdefinitions.R                                                            -- 0
          external, enters through  From mathcomp Require Import Rstruct
          the only realType instance in the switch (Rstruct.v:432)
          precedent: notes/probes/2026-09-15-pgl27-view-entropy/concrete_real_instance.v

step    require the bridges by logical path                                             -- 0
          From general_dealer_law_probe Require Import dealer_kernel_probe
            carrier_transport_probe pgl27_deterministic_bridge psl211_alldecks_bridge.
          precondition: -Q . general_dealer_law_probe in _CoqProject, all four rebuilt.
          psl211_per_deck_counter is NOT required: C8 has no realType.

step    wrapper 1  pgl27P Rc |= pgl27_view Rc C _|_ pgl27_secret Rc                     -- 1
          := pgl_indep_via_generic Rc C HC          body is `exact:`, no re-derivation
step    wrapper 2  alldecksP ... |= alldecks_view ... _|_ alldecks_secret ...           -- 2
          := pgl_all_indep_via_generic Rc C HC
step    wrapper 3  psl211_alldecksP Rc |= (fun u => psl211_alldecks_view C u.1 u.2)
                   _|_ psl211_alldecks_secret Rc                                        -- 3
          := psl_indep_via_generic Rc C HC
          the declared type of each wrapper is the PRE-EXISTING theorem's type; that
          identity, not the proof, is what C9 certifies.

step    exercise the two generic declarations no bridge reaches                         -- 5
          dealer_shufflePE at Rc, and dealer_view_indep_of_deck at PGL-all
          (valid s d := uniq d; premise 1 = PGLBR:346-351; premise 2 = pgl_deck_view_law)
          without this line soundness invariant 8 stays false.

terminal Print Assumptions on all five                                                  -- 5
          expected: functional_extensionality_dep, propositional_extensionality,
          constructive_indefinite_description  (mathcomp/classical/boolp.v:74,77,80)
          + ClassicalDedekindReals.sig_forall_dec, sig_not_dec
          + the sealed Rdefinitions.RbaseSymbolsImpl.* and RinvImpl.* constants
          + possibly Epsilon.epsilon_statement
          acceptance: no project-local constant, no Admitted.  Paste the literal list.

outside  nothing.  R and the whitelist are C9's deliverable, not its context.
```

Monad verdict, for the record: the bridge flow is a parameterised monad indexed by (sample carrier, reader pair). Bind is `inde_RV_fdistmap_pullback` composed with the two square equations; unit is the identity reindexing with `erefl` squares. Associativity holds only up to `fdistmap_comp`, and the PSL leg shows the laws are propositional rather than definitional — which is exactly why `psl_bridge_pullback_eq` has to exist.

---

VERDICT: GO
