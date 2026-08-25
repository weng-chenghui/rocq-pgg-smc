# Five-Card ε-Family Refactor Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: use subagent-driven-development or executing-plans to implement task-by-task. Steps use checkbox (`- [ ]`) syntax.
> **Rocq adaptation:** "tests" are `rocq_check`/`rocq_compile_file` (rocq-mcp) and `make -j1 <file>.vo` builds. Proof bodies marked DELEGATE are developed by the `rocq-prover` agent during execution (give it the exact statement, line range, and in-scope variables, per project CLAUDE.md). Never run concurrent `make`; always `-j1`.

**Goal:** Unify den Boer and Kim into one ε-parameterized five-card profile (`den Boer = ε=0`, `Kim = ε≠0`) and retire all Reed-Solomon coupling from the Kim instance.

**Architecture:** Both members share the 5-weighted-generator `C_5` group `FiveCardKim_M`, the `bool` secret, the `fcI` three-consecutive-hearts `ReconPlug`, and one weighted-Schreier `SecurityWitness` parameterized by the bias `ε`. den Boer becomes the `ε=0` instance (perfect, `var_dist=0`); Kim is the `ε≠0` instance. Kim's RS genus-0 covering, `AlgebraicRigidity`, and the `kim_covering_realised` axiom are deleted (vacuous for `|C_5|=5`, no consumer), exactly as was already done for den Boer.

**Tech stack:** Rocq + MathComp + infotheo; HB structures; `pgg_smc`/`pgg_reconstruct` logical paths; `make -j1`; rocq-mcp; pre-commit rocq-audit gate.

---

## Key facts (verified against the tree)

- `FiveCard_M := @Gen_PGGTypes 0 3 fc_sigmas` (1 generator, `N=5`) — `five_card_group.v`.
- `FiveCardKim_M := @Gen_PGGTypes 4 3 fc_kim_sigmas` (5 generators, `N=5`) — `five_card_kim.v:133`. Same group `⟨σ⟩≅C_5`, same `N`, different generating set.
- `fcI_scheme : ThresholdScheme bool 'I_5` depends only on `N=5`, not on the generators — reusable as-is for `FiveCardKim_M`.
- `den_boer_plug := @MkReconPlug FiveCard_M bool fcI_scheme fc_content (mfun (pgg_rho FiveCard_M)) fcI_perm_compatible` — `den_boer_profile.v`.
- `FiveCard_PI := @MkPGGI FiveCard_M 4 (ord_tuple 5) fc_starts_uniq`.
- `den_boer_profile R := @MkMonodromyProfile R FiveCard_M bool FiveCard_PI (fc_security_uniform R) den_boer_plug` — `den_boer_profile.v:39`.
- `fc_kim_security_witness (L) : SecurityWitness R FiveCardKim_M` — `five_card_kim.v:505`; built in a section with `Variable eps`, `Hypothesis eps_lt_inv5 : eps < 1/5`, `eps_gt_neg4inv5 : -(4/5) < eps`. Both hypotheses hold at `ε=0`; at `ε=0`, `sw_bound_eps = (8/5)·((5/4)·0)^L = 0`.
- `FiveCard_M` is referenced only inside `instances/denboer1989/` (4 files); `uniform_security_witness` only by den Boer + its home `security/pgg_uniform_security.v`.
- Kim's RS block (`rigidity_kim_instance.v`): `kim_covering` (:73), `kim_covering_realised` **Axiom** (:85), `kim_genus0_automorphism` (:97), `kim_threshold_witness` (:103), `kim_rigidity` (:108), `kim_tradeoff` (:122), `kim_ts_recon_correct` (:138); RS imports `reed_solomon` (:30), `cover_genus0`, `rs_code_5sheets` (:36), `curve_realisation` (:37). No `.v` consumer of any `kim_*` rigidity def.

## File structure

- **Create** `instances/kim2025/five_card_family.v` — `FiveCardKim_PI`, `five_card_plug`, `five_card_profile ε`, and the two members. Imports `five_card_kim` (for `FiveCardKim_M`, the witness) and den Boer's `five_card_scheme_I5` (for `fcI_scheme`, `fc_content`). One new directed dependency `kim2025 → denboer1989` (no cycle).
- **Modify** `instances/denboer1989/five_card_scheme_I5.v` — add `fcI_perm_compatible_kim` (the invariance proof transported to `FiveCardKim_M`'s `pgg_G`).
- **Modify** `instances/denboer1989/den_boer_profile.v` — `den_boer_profile := five_card_profile 0`; migrate the program/PI/correctness/commit-duality from `FiveCard_M` to `FiveCardKim_M`.
- **Modify** `instances/denboer1989/five_card_security.v` — drop den Boer's use of `fc_security_uniform`; migrate residual `FiveCard_M` references.
- **Modify** `instances/kim2025/rigidity_kim_instance.v` — delete the RS block + RS imports; keep `kim_complexity` only if it is RS-free (relocate to `five_card_kim.v` if so).
- **Possibly delete** `FiveCard_M` and `fc_sigmas` from `five_card_group.v` once unreferenced (keep `fc_sigma`, the underlying 5-cycle, since `fc_kim_sigmas` is built from it).
- **Update** paper section 6 (notes) to the merged 6.1 five-card family.

---

## Per-task Stage 4 quality gate + commit policy (token-saving variant)

Every task that produces or edits a `.v` proof runs this gate **before** its commit. The proving is done by `rocq-prover` (project-aware); the MathComp *style* (idiom + naming) is enforced by the audit. To avoid double-spending the Stage-2 audit budget (daily 2M cap), there is **no separate auditor call** — the pre-commit gate is the single Stage-2 run and the enforcement point.

- [ ] **Stage 4a — golf:** dispatch the `proof-golfer` agent on the task's changed file(s) (`--search=quick`). Apply only the directness/brevity wins it verifies by `rocq_compile`; revert anything that fails. (Golf is generic-Coq directness, not idiom; the idiom/naming check is the gate in 4b. Golf does not touch the Stage-2 budget.)
- [ ] **Stage 4b — commit; the gate is the single audit:** commit **normally** so the pre-commit gate runs `rocq-auditor` once (blocking). This is the only Stage-2 spend and the enforcement point:

  ```bash
  git add <files>
  git commit -m "<message>"
  ```

  If the gate **blocks** on error-severity findings (A001-A004 idiom `have`/`congr`/`done`; B001 `eqVneq`; E001 dead tail; F001/G001/I001 naming + role-matched suffix; H-series role tags): fix them, re-verify with `rocq_check`/`make -j1`, then **re-land with the sanctioned bypass** so the fix commit does not trigger a second blocking run:

  ```bash
  ROCQ_AUDIT_BYPASS=1 git commit -m "<message>"
  ```

  **Never use `git commit -n` / `--no-verify`.** Per project `CLAUDE.md` it is forbidden AND ineffective: the Claude Code `PreToolUse(Bash)` hook fires on `git commit` regardless of `-n`. `ROCQ_AUDIT_BYPASS=1` runs the gate advisory (non-blocking) and logs to `.claude/audit/state/bypass.log` + `refs/notes/audit-bypass`. To ignore the hook *totally* you must disable the Claude `PreToolUse` hook in `settings.json` (global to all commits — out of scope).

Below, each code task's commit step is a plain `git commit` (the gate audits once); use the `ROCQ_AUDIT_BYPASS=1` form only to re-land after the gate blocks and you have fixed the findings.

---

## Task 1: Pre-flight — branch, dependency scan, baseline green

**Files:** none (read-only + branch)

- [ ] **Step 1: Create a working branch**

```bash
cd /Users/cheng-huiweng/Projects/coq/infotheo-pgg
git checkout -b five-card-epsilon-family
```

- [ ] **Step 2: Confirm no external consumer of Kim's rigidity / FiveCard_M leakage**

```bash
grep -rn "kim_rigidity\|kim_covering\|kim_threshold_witness\|kim_ts_recon_correct" --include="*.v" pgg-smc | grep -v "rigidity_kim_instance.v"
grep -rln "rigidity_kim_instance" --include="*.v" pgg-smc
grep -rln "FiveCard_M" --include="*.v" pgg-smc | grep -v "instances/denboer1989"
```
Expected: first two empty (or only stale notes); third empty. If `rigidity_kim_instance` is imported anywhere, note the importer and adjust Task 5.

- [ ] **Step 3: Record baseline build of the touched files**

```bash
cd /Users/cheng-huiweng/Projects/coq/infotheo-pgg
make -j1 pgg-smc/instances/kim2025/five_card_kim.vo
make -j1 pgg-smc/instances/denboer1989/den_boer_profile.vo
make -j1 pgg-smc/instances/kim2025/rigidity_kim_instance.vo
```
Expected: all succeed (current green). This is the regression baseline.

- [ ] **Step 4: Commit the branch point (no code change yet)**

```bash
git commit --allow-empty -m "chore: branch point for five-card epsilon-family refactor"
```

---

## Task 2: Transport the reconstruction invariance to `FiveCardKim_M`

**Files:**
- Modify: `instances/denboer1989/five_card_scheme_I5.v`

`den_boer_plug` needs `rp_recon_invariant` at `FiveCardKim_M`'s `pgg_G`. The existing `fcI_perm_compatible` is stated for `FiveCard_M`. Both groups are `⟨σ⟩=C_5`, so the statement transports; the proof script changes only in the generating-set expression.

- [ ] **Step 1: State the transported lemma (DELEGATE proof to rocq-prover)**

Target statement (mirror the existing `fcI_perm_compatible`, retargeted):

```coq
(** @composes: five_card_plug
    fcI_perm_compatible_kim — fcI reconstruction is invariant under the full
    FiveCardKim_M group. Same C_5 action as FiveCard_M; transported to the
    5-generator presentation. *)
Lemma fcI_perm_compatible_kim :
  @ts_recon_perm_invariant _ (pgg_G FiveCardKim_M) _ _ fcI_scheme
    (morphism.mfun (@pgg_rho FiveCardKim_M)).
Proof. (* DELEGATE: adapt fcI_perm_compatible; pgg_G FiveCardKim_M = <<σ-powers>> = C_5. *) Admitted.
```

- [ ] **Step 2: Develop the proof with rocq-mcp / rocq-prover**

Give the prover: the exact statement above, the existing `fcI_perm_compatible` proof for reference, and the fact `pgg_G FiveCardKim_M = pgg_G FiveCard_M` as groups (both `⟨σ⟩`). Use `rocq_start`→`rocq_query`→`rocq_step_multi`→apply once.

- [ ] **Step 3: Verify the file compiles**

Run: `make -j1 pgg-smc/instances/denboer1989/five_card_scheme_I5.vo`
Expected: success, no `Admitted`, no new axioms (`rocq_assumptions` clean).

- [ ] **Step 4: Stage 4a golf, then commit (gate audits once)**

Run Stage 4a (golf) on `five_card_scheme_I5.v`, then commit normally (gate audits once; on block, fix + `ROCQ_AUDIT_BYPASS=1` re-land):

```bash
git add pgg-smc/instances/denboer1989/five_card_scheme_I5.v
git commit -m "denboer: transport fcI reconstruction invariance to FiveCardKim_M"
```

---

## Task 3: Create the shared `five_card_family.v` (additive, build stays green)

**Files:**
- Create: `instances/kim2025/five_card_family.v`

- [ ] **Step 1: Header, imports, scope**

```coq
(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* The five-card trick as one epsilon-family: den Boer = eps 0 (uniform,      *)
(* perfect), Kim & Cetinkaya = eps <> 0 (biased). Shared group FiveCardKim_M, *)
(* bool secret, fcI three-consecutive-hearts plug; eps enters only through    *)
(* the weighted-Schreier security witness.                                    *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface card_exchange_pismc.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import five_card_kim.            (* FiveCardKim_M, fc_kim_security_witness *)
From pgg_smc Require Import five_card_scheme_I5.      (* fcI_scheme, fc_content, fcI_perm_compatible_kim *)
From pgg_smc Require Import five_card_program.        (* fc_content, the AND program *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
```

- [ ] **Step 2: Starting interface for the 5-generator group**

```coq
(** @composes: five_card_profile
    fc_kim_starts_uniq — the five start positions are distinct. *)
Lemma fc_kim_starts_uniq : uniq (ord_tuple 5).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.

(** @intent: the concrete five-sheet starting interface for FiveCardKim_M. *)
Definition FiveCardKim_PI : PGGInterface FiveCardKim_M :=
  @MkPGGI FiveCardKim_M 4 (ord_tuple 5) fc_kim_starts_uniq.
```

- [ ] **Step 3: The shared reconstruction plug at `FiveCardKim_M`**

```coq
(** @intent: the five-card reconstruction plug (bool secret, 'I_5 shares):
    fcI_scheme, identity content, C_5 monodromy, transported invariance.
    Shared by den Boer (eps=0) and Kim (eps<>0). *)
Definition five_card_plug : ReconPlug FiveCardKim_M bool :=
  @MkReconPlug FiveCardKim_M bool fcI_scheme fc_content
    (morphism.mfun (@pgg_rho FiveCardKim_M)) fcI_perm_compatible_kim.
```

- [ ] **Step 4: The ε-parameterized profile**

`fc_kim_security_witness` lives in a section over `Variable eps` + the two positivity hypotheses. Expose a closed form taking `ε` and its bounds explicitly (refactor the section to a definition if it is not already applicable outside the section), then:

```coq
(** @intent: the five-card trick as a profile parameterized by the bias eps
    and the shuffle count L. den Boer = (eps := 0); Kim = (eps <> 0). *)
Definition five_card_profile (R : realType) (eps : R)
    (Hlo : - (4%:R / 5%:R) < eps) (Hhi : eps < 5%:R^-1) (L : nat)
    : MonodromyProfile R :=
  @MkMonodromyProfile R FiveCardKim_M bool FiveCardKim_PI
    (fc_kim_security_witness eps Hlo Hhi L) five_card_plug.
```

DELEGATE if `fc_kim_security_witness` must be lifted out of its section: ask rocq-prover to re-state it as a top-level `Definition fc_kim_security_witness (eps : R) (Hlo Hhi) (L) : SecurityWitness R FiveCardKim_M` preserving the existing proof terms.

- [ ] **Step 5: ε=0 perfect-security sanity lemma**

```coq
(** @main security: at eps = 0 the five-card witness is perfect. *)
Lemma five_card_eps0_perfect (R : realType) (L : nat)
    (H0lo : - (4%:R / 5%:R) < (0:R)) (H0hi : (0:R) < 5%:R^-1) :
  sw_bound_eps (fc_kim_security_witness (0:R) H0lo H0hi L) = 0.
Proof. (* DELEGATE: reduce (8/5)*((5/4)*|0|)^L = 0. *) Admitted.
```

- [ ] **Step 6: Register the file in the build and compile**

Add `pgg-smc/instances/kim2025/five_card_family.v` to `_CoqProject` if files are listed there (check first).
Run: `make -j1 pgg-smc/instances/kim2025/five_card_family.vo`
Expected: success, no `Admitted` remaining.

- [ ] **Step 7: Stage 4a golf, then commit (gate audits once)**

Run Stage 4a (golf) on `five_card_family.v`, then commit normally (gate audits once; on block, fix + `ROCQ_AUDIT_BYPASS=1` re-land):

```bash
git add pgg-smc/instances/kim2025/five_card_family.v pgg-smc/_CoqProject
git commit -m "five-card: shared epsilon-family profile (FiveCardKim_M, bool, fcI plug)"
```

---

## Task 4: Repoint Kim to the family; delete Kim's RS block

**Files:**
- Modify: `instances/kim2025/rigidity_kim_instance.v`

- [ ] **Step 1: Add `kim_profile`**

In `five_card_family.v` (or a thin `kim2025` re-export), add:

```coq
(** @intent: Kim & Cetinkaya = the biased five-card profile (eps <> 0). *)
Definition kim_profile (R : realType) (eps : R)
    (Hlo : - (4%:R / 5%:R) < eps) (Hhi : eps < 5%:R^-1) (L : nat)
    : MonodromyProfile R := five_card_profile eps Hlo Hhi L.
```

- [ ] **Step 2: Delete the RS block and RS imports**

In `rigidity_kim_instance.v`, remove `kim_covering`, `kim_covering_realised` (Axiom), `kim_genus0_automorphism`, `kim_threshold_witness`, `kim_rigidity`, `kim_tradeoff`, `kim_ts_recon_correct`, and the imports `reed_solomon`, `cover_genus0`, `rs_code_5sheets`, `curve_realisation`, `ssralg_ext` (if only RS used it). Keep `kim_complexity` only if it is RS-free; otherwise move it to `five_card_kim.v`.

- [ ] **Step 3: Verify no `RS5_witness_trivial` / RS symbol remains in the file**

```bash
grep -nE "RS5_witness_trivial|reed_solomon|rs_code|genus0_covering|realised_by_curve" pgg-smc/instances/kim2025/rigidity_kim_instance.v
```
Expected: empty.

- [ ] **Step 4: Compile (or remove the file from the build if now empty)**

Run: `make -j1 pgg-smc/instances/kim2025/rigidity_kim_instance.vo`
Expected: success. If the file is now empty, delete it and drop it from `_CoqProject`.

- [ ] **Step 5: Confirm the `kim_covering_realised` axiom is gone**

```bash
grep -rn "kim_covering_realised" --include="*.v" pgg-smc
```
Expected: empty. (Axiom eliminated.)

- [ ] **Step 6: Stage 4a golf, then commit (gate audits once)**

Run Stage 4a (golf) on the changed `kim2025/` files, then commit normally (gate audits once; on block, fix + `ROCQ_AUDIT_BYPASS=1` re-land):

```bash
git add pgg-smc/instances/kim2025/
git commit -m "kim: retire RS covering/rigidity + kim_covering_realised axiom; use shared family"
```

---

## Task 5: Migrate den Boer onto `FiveCardKim_M` (`den_boer_profile := five_card_profile 0`)

**Files:**
- Modify: `instances/denboer1989/den_boer_profile.v`
- Modify: `instances/denboer1989/five_card_security.v`

- [ ] **Step 1: Redefine `den_boer_profile` as the ε=0 instance**

```coq
From pgg_smc Require Import five_card_family.

(** @intent: den Boer = the five-card family at eps = 0 (uniform cut, perfect).*)
Definition den_boer_profile (R : realType) : MonodromyProfile R :=
  five_card_profile (0:R) (den_boer_eps0_lo R) (den_boer_eps0_hi R) 0.
```

where `den_boer_eps0_lo`/`den_boer_eps0_hi` are the two trivially-true positivity facts at `ε=0` (DELEGATE: `by rewrite; ...` numeric bounds `-(4/5) < 0` and `0 < 1/5`).

- [ ] **Step 2: Migrate the program / PI / commit-duality from `FiveCard_M` to `FiveCardKim_M`**

Repoint `FiveCard_PI → FiveCardKim_PI`, `den_boer_plug → five_card_plug`, and every `FiveCard_M` occurrence in `den_boer_profile.v` (the dealer-with-commit program, `den_boer_players`, `den_boer_ap_input*`, the `den_boer_commit_input*_dual` lemmas, `den_boer_committed_protocol_correct`) to `FiveCardKim_M`. DELEGATE the proof re-runs; the `native_compute` duality lemmas should re-run unchanged in shape.

- [ ] **Step 3: Drop `fc_security_uniform` usage**

Remove den Boer's construction/use of `fc_security_uniform` in `five_card_security.v` (the general `uniform_security_witness` stays in `security/pgg_uniform_security.v`). Migrate any residual `FiveCard_M` references in this file to `FiveCardKim_M`, or delete now-dead lemmas (e.g. `fc_eps_zero`) that the family supersedes.

- [ ] **Step 4: Compile den Boer**

```bash
make -j1 pgg-smc/instances/denboer1989/five_card_security.vo
make -j1 pgg-smc/instances/denboer1989/den_boer_profile.vo
```
Expected: success; `rocq_assumptions` shows no new axioms.

- [ ] **Step 5: Confirm `run_k_den_boer` (= 2) and recovery still hold**

Run (rocq-mcp `rocq_check`): `Lemma run_k_den_boer (R:realType) : run_k (den_boer_profile R) = 2.` still `by []` or a one-liner.
Expected: closes.

- [ ] **Step 6: Stage 4a golf, then commit (gate audits once)**

Run Stage 4a (golf) on the changed `denboer1989/` files, then commit normally (gate audits once; on block, fix + `ROCQ_AUDIT_BYPASS=1` re-land):

```bash
git add pgg-smc/instances/denboer1989/
git commit -m "denboer: den_boer_profile := five_card_profile 0 (migrate to FiveCardKim_M)"
```

---

## Task 6: Retire the now-dead `FiveCard_M` (1-generator group)

**Files:**
- Modify: `instances/denboer1989/five_card_group.v`

- [ ] **Step 1: Confirm `FiveCard_M` and `fc_sigmas` are unreferenced**

```bash
grep -rn "FiveCard_M\b" --include="*.v" pgg-smc
grep -rn "fc_sigmas\b" --include="*.v" pgg-smc
```
Expected: empty (all migrated). Keep `fc_sigma` (the 5-cycle) — `fc_kim_sigmas` is built from it.

- [ ] **Step 2: Delete `FiveCard_M`, `fc_sigmas`, and now-orphan rewrite lemmas (`fc_sigmasE`, `fc_gens_agree`) if unused**

DELEGATE: confirm each removed lemma has no remaining caller before deletion (`grep`), then delete.

- [ ] **Step 3: Full rebuild of the den Boer + Kim instance files**

```bash
make -j1 pgg-smc/instances/denboer1989/five_card_group.vo
make -j1 pgg-smc/instances/denboer1989/five_card_scheme_I5.vo
make -j1 pgg-smc/instances/denboer1989/den_boer_profile.vo
make -j1 pgg-smc/instances/kim2025/five_card_kim.vo
make -j1 pgg-smc/instances/kim2025/five_card_family.vo
```
Expected: all succeed.

- [ ] **Step 4: Stage 4a golf, then commit (gate audits once)**

Run Stage 4a (golf) on `five_card_group.v`, then commit normally (gate audits once; on block, fix + `ROCQ_AUDIT_BYPASS=1` re-land):

```bash
git add pgg-smc/instances/denboer1989/five_card_group.v
git commit -m "denboer: retire the 1-generator FiveCard_M (unified on FiveCardKim_M)"
```

---

## Task 7: Downstream sweep, audit, finalize

**Files:** any importer of the changed profiles (landscape/demo).

- [ ] **Step 1: Find and rebuild downstream importers**

```bash
grep -rln "den_boer_profile\|kim_profile\|rigidity_kim_instance\|five_card_security" --include="*.v" pgg-smc/reconstruct pgg-smc/protocol pgg-smc/instances
```
Rebuild each hit with `make -j1 <file>.vo`. Expected: all succeed. Fix any reference to deleted Kim rigidity defs (there should be none per Task 1).

- [ ] **Step 2: Axiom-hygiene check**

For `den_boer_profile`, `kim_profile`, `five_card_profile`: run rocq-mcp `rocq_assumptions`. Expected: the only axioms are the pre-existing justified ones (e.g. `s5_group_order_eq` is unrelated); `kim_covering_realised` must be **absent**.

- [ ] **Step 3: Full targeted build**

```bash
cd /Users/cheng-huiweng/Projects/coq/infotheo-pgg
make -j1   # or the targeted .vo list above; single-threaded only
```
Expected: clean build of the pgg-smc tree.

- [ ] **Step 4: Update the section-6 notes to the merged family**

Edit the section-6 outline (notes) so 6.1 is the single five-card family (den Boer ε=0, Kim ε≠0), recovery = `fcI`, and 6.4.4 keeps the S5 `RS5_witness_trivial` cleanup flag.

- [ ] **Step 5: Final Stage 4a golf across the changed set, then commit (gate audits once)**

Run Stage 4a (golf) over the new proofs in the changed set. Then commit normally so the gate runs the auditor once over all staged `.v` — H-series role tags on new `Lemma`/`Definition`, I-series naming, A/B/E idiom:

```bash
git add -A pgg-smc
git commit -m "five-card: unify den Boer/Kim as one epsilon-family; RS fully retired"
```
If the gate blocks, fix the findings, re-verify, then re-land with `ROCQ_AUDIT_BYPASS=1 git commit -m "..."` (logged to `refs/notes/audit-bypass`).

---

## Self-review notes

- **Spec coverage:** retire Kim RS (Tasks 4), unify on `FiveCardKim_M`+bool+fcI (Tasks 2,3,5), den Boer = ε=0 (Task 5), delete the axiom (Task 4 Step 5), drop dead `FiveCard_M` (Task 6). All covered.
- **Risk:** the den Boer migration (Task 5) touches a working instance; the `fcI` invariance transport (Task 2) and the `native_compute` duality re-runs are the only real proof work, both low-risk since the group and `N=5` action are unchanged.
- **Out of scope (separate plan):** `s5/rigidity_s5_instance.v` still imports `RS5_witness_trivial` despite S5 being the no-go; retire that vacuous block in a follow-up, mirroring Tasks 2/4.
