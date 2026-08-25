# rocq-pgg-smc Extraction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Stand up `~/Projects/coq/rocq-pgg-smc` as a standalone Rocq 9 project containing the pgg-smc formalization, building against the installed `coq-infotheo` package, with all `dumas2017dual`/`du2002` dependence eliminated.

**Architecture:** Copy the pgg-smc tree (prefix dropped), keep the `pgg_smc`/`pgg_reconstruct` namespaces, qualify infotheo imports, inline ~300 lines of banned-subtree lemmas into a new `lib/proba_entropy_ext.v` plus one in-file inline, then build with `rocq makefile` and repair to green.

**Tech Stack:** Rocq 9.0.0, `rocq makefile` (coq_makefile), opam switch `~/Projects/coq/_opam`, installed `coq-infotheo` (pin of `~/Projects/coq/infotheo` @ `dumas2017dual`, commit b5a899f7), MathComp 2.5, mathcomp-analysis 1.15.

**Conventions for all tasks:** `SRC=/Users/cheng-huiweng/Projects/coq/infotheo-pgg/pgg-smc`, `DST=/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc`, `PIN=/Users/cheng-huiweng/Projects/coq/infotheo`. Never write to `SRC` or anywhere under `infotheo-pgg`. Never write to `PIN`. All commits happen in `DST`. The opam switch is already active in the user's shell profile; if `rocq` is not found, prefix commands with `eval $(opam env --switch=/Users/cheng-huiweng/Projects/coq)`.

---

### Task 1: Scaffold and copy (mechanical)

**Files:**
- Create: `DST/.gitignore`, `DST/README.md`, `DST/LICENSE`
- Create (by copy): `DST/{lib,protocol,groups,security,reconstruct,instances,manifest,blueprint,notes,paper,paper-wadt2026,paper-wadt2026-baseline-application,audit-inventory,scripts}/`

- [ ] **Step 1: Copy the tree**

```bash
cd /Users/cheng-huiweng/Projects/coq/rocq-pgg-smc
rsync -a \
  --exclude='*.vo' --exclude='*.vos' --exclude='*.vok' --exclude='*.glob' \
  --exclude='*.aux' --exclude='.*.aux' --exclude='*.d' --exclude='.DS_Store' \
  --exclude='__pycache__/' --exclude='*.pyc' --exclude='.lia.cache' \
  --exclude='/paper-wadt2026/tmp/' \
  /Users/cheng-huiweng/Projects/coq/infotheo-pgg/pgg-smc/ ./
rmdir fault_tolerance 2>/dev/null || true
```

- [ ] **Step 2: Verify the copy**

Run: `find . -name '*.v' -not -path './.git/*' | wc -l` — Expected: `152`.
Run: `find . -name '*.vo' | wc -l` — Expected: `0`.
Run: `git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg status --porcelain | wc -l` — Expected: `179` (unchanged baseline).

- [ ] **Step 3: Write `.gitignore`**

```gitignore
*.vo
*.vos
*.vok
*.glob
*.aux
.*.aux
*.d
.DS_Store
__pycache__/
*.pyc
.lia.cache
Makefile.rocq
Makefile.rocq.conf
.Makefile.rocq.d
build.log
```

- [ ] **Step 4: Copy LICENSE and write README.md**

```bash
cp /Users/cheng-huiweng/Projects/coq/infotheo-pgg/LICENSE ./LICENSE
```

`README.md`:

```markdown
# rocq-pgg-smc

Formalization of PGG-SMC: group-based secure multiparty computation
(card-based protocols, RAAG hopping, entropy security bounds), in Rocq,
over the infotheo library.

Extracted 2026-08-26 from the `pgg-smc/` subtree of the infotheo-pgg
fork; see `docs/superpowers/specs/2026-08-26-rocq-pgg-smc-extraction-design.md`.

## Build

Requires the opam switch at `~/Projects/coq` (Rocq 9.0.0, MathComp 2.5,
`coq-infotheo` pinned to `~/Projects/coq/infotheo#dumas2017dual`).

    make -j8        # compile everything in _CoqProject
    make clean

Logical namespaces: `pgg_smc` (most directories), `pgg_reconstruct`
(`reconstruct/`).
```

- [ ] **Step 5: Commit**

```bash
git add -A && git commit -m "import: pgg-smc tree from infotheo-pgg (build artifacts excluded)"
```

---

### Task 2: Build system and opam metadata (mechanical)

**Files:**
- Create: `DST/_CoqProject`, `DST/Makefile`, `DST/rocq-pgg-smc.opam`

- [ ] **Step 1: Generate `_CoqProject`**

Header (verbatim):

```
-arg -w -arg -projection-no-head-constant
-arg -w -arg -redundant-canonical-projection
-arg -w -arg -notation-overridden
-arg -w -arg -ambiguous-paths
-arg -w -arg -notation-incompatible-format

-R lib pgg_smc
-R protocol pgg_smc
-R groups pgg_smc
-R security pgg_smc
-R reconstruct pgg_reconstruct
-R instances/denboer1989 pgg_smc
-R instances/kim2025 pgg_smc
-R instances/s5 pgg_smc
-R instances/s5x5 pgg_smc
-R instances/oc pgg_smc
-R instances/star pgg_smc
-R instances/abelian pgg_smc
-R instances/cyclic pgg_smc
-R instances/monster pgg_smc
-R instances/pgl27 pgg_smc
-R manifest pgg_smc
```

Then the file list: take lines 133–280 of
`/Users/cheng-huiweng/Projects/coq/infotheo-pgg/_CoqProject` (every line
starting with `pgg-smc/`), strip the leading `pgg-smc/` from each, preserve
order exactly. There must be 148 entries. Do NOT add `-R . infotheo`.

Verify: `grep -c '\.v$' _CoqProject` → `148`; every listed file exists:
`while read -r f; do case $f in *.v) [ -f "$f" ] || echo "MISSING $f";; esac; done < _CoqProject` → no output.

- [ ] **Step 2: Write `Makefile`**

```make
# Delegating wrapper; the real makefile is generated by rocq makefile.
ROCQMAKEFILE := Makefile.rocq

all: $(ROCQMAKEFILE)
	$(MAKE) -f $(ROCQMAKEFILE) all

$(ROCQMAKEFILE): _CoqProject
	rocq makefile -f _CoqProject -o $(ROCQMAKEFILE)

%.vo: $(ROCQMAKEFILE) %.v
	$(MAKE) -f $(ROCQMAKEFILE) $@

install: $(ROCQMAKEFILE)
	$(MAKE) -f $(ROCQMAKEFILE) install

clean: $(ROCQMAKEFILE)
	$(MAKE) -f $(ROCQMAKEFILE) clean
	rm -f $(ROCQMAKEFILE) $(ROCQMAKEFILE).conf

.PHONY: all install clean
```

- [ ] **Step 3: Verify generation**

Run: `make Makefile.rocq` — Expected: creates `Makefile.rocq` without error.

- [ ] **Step 4: Write `rocq-pgg-smc.opam`**

Verify each dependency name exists first: `opam list --installed --short | grep -E 'rocq-|coq-'` and prefer the `rocq-*` name when that exact package is installed, else the `coq-*` name. Template (adjust names per the check):

```opam
opam-version: "2.0"
name: "rocq-pgg-smc"
version: "dev"
synopsis: "Group-based secure multiparty computation over infotheo"
description: """
Formalization of PGG-SMC: card-based SMC protocols, RAAG hopping,
and entropy security bounds, built on infotheo and MathComp."""
maintainer: "snowmantw@gmail.com"
authors: ["Cheng-Hui Weng"]
license: "LGPL-2.1-or-later"
homepage: "https://github.com/weng-chenghui/rocq-pgg-smc"
bug-reports: "https://github.com/weng-chenghui/rocq-pgg-smc/issues"
depends: [
  "rocq-core" {>= "9.0" & < "9.2~"}
  "rocq-stdlib"
  "coq-infotheo"
  "coq-mathcomp-ssreflect" {>= "2.5.0" & < "2.6~"}
  "coq-mathcomp-fingroup"
  "coq-mathcomp-algebra"
  "coq-mathcomp-solvable"
  "coq-mathcomp-classical"
  "coq-mathcomp-reals"
  "coq-hierarchy-builder"
]
build: [make "-j%{jobs}%"]
install: [make "install"]
dev-repo: "git+https://github.com/weng-chenghui/rocq-pgg-smc.git"
```

Check the license identifier against `LICENSE` content and correct if it
is not LGPL-2.1 (use the SPDX id matching the actual file).

- [ ] **Step 5: Commit**

```bash
git add _CoqProject Makefile rocq-pgg-smc.opam && git commit -m "build: _CoqProject, rocq makefile wrapper, opam metadata"
```

---

### Task 3: Qualify plain infotheo imports (mechanical)

**Files:**
- Modify: ~90 `.v` files under `DST` (script-driven)
- Create: `DST/scripts/qualify_infotheo_imports.py`

- [ ] **Step 1: Write the rewrite script**

`scripts/qualify_infotheo_imports.py`:

```python
#!/usr/bin/env python3
"""One-shot: move plain-Require'd infotheo modules under From infotheo."""
import re, sys, pathlib

INFOTHEO = {  # modules resolving into installed infotheo (allowed surface)
    "realType_ext", "ssr_ext", "ssralg_ext", "fdist", "proba",
    "jfdist_cond", "entropy", "dft", "hamming", "linearcode",
    "pismc", "reed_solomon", "smc_interpreter", "smc_session_types",
}
BANNED = {  # handled by Tasks 4-5, never qualified here
    "entropy_fiber", "extra_proba", "extra_entropy", "rouche_capelli",
    "spp_proba", "spp_entropy",
}
pat = re.compile(r"^Require (Import|Export) ([^.]+)\.\s*$")
changed = []
for p in sorted(pathlib.Path(".").rglob("*.v")):
    if ".git" in p.parts:
        continue
    lines, out, touched = p.read_text().splitlines(True), [], False
    for line in lines:
        m = pat.match(line)
        if not m:
            out.append(line)
            continue
        kind, mods = m.group(1), m.group(2).split()
        info = [x for x in mods if x in INFOTHEO]
        rest = [x for x in mods if x not in INFOTHEO]
        if not info:
            out.append(line)
            continue
        touched = True
        out.append(f"From infotheo Require {kind} {' '.join(info)}.\n")
        if rest:
            out.append(f"Require {kind} {' '.join(rest)}.\n")
    if touched:
        p.write_text("".join(out))
        changed.append(str(p))
print("\n".join(changed), file=sys.stderr)
print(f"{len(changed)} files rewritten", file=sys.stderr)
```

- [ ] **Step 2: Run it and inspect**

```bash
cd /Users/cheng-huiweng/Projects/coq/rocq-pgg-smc && python3 scripts/qualify_infotheo_imports.py
```

Expected: roughly 60–90 files rewritten (the exploration counted 34 files
for the smc trio alone, plus reconstruct/instances/lib files).

- [ ] **Step 3: Verify no allowed-module plain requires remain**

```bash
grep -rnE '^Require (Import|Export)' --include='*.v' . \
  | grep -wE 'realType_ext|ssr_ext|ssralg_ext|fdist|proba|jfdist_cond|entropy|dft|hamming|linearcode|pismc|reed_solomon|smc_interpreter|smc_session_types' || echo CLEAN
```

Expected: `CLEAN`. Also confirm internal requires survived:
`grep -rn 'Require Import pgg_interface' --include='*.v' . | wc -l` → `19`.
Spot-check `git diff --stat` for sanity (no file should lose lines other
than by the 1-to-2 line splits).

- [ ] **Step 4: Commit**

```bash
git add -A && git commit -m "refactor: qualify plain infotheo requires as From infotheo"
```

---

### Task 4: Helper file `lib/proba_entropy_ext.v` (proving)

**Files:**
- Create: `DST/lib/proba_entropy_ext.v`
- Modify: `DST/_CoqProject` (insert `lib/proba_entropy_ext.v` immediately after the `lib/perm_uniform.v` line)

Copy the following declarations VERBATIM (statement and proof) from the
pinned infotheo sources into the new file, in this order (dependency
order). Do not restate or improve proofs; adjust only what the new
context forces (section wrappers, `Local Open Scope`, implicit-argument
declarations that lived at the source file's top).

From `PIN/dumas2017dual/lib/extra_algebra.v`:
1. `logr_eq1` (lines 37–44)

From `PIN/du2002/spp_proba.v` (locate by name; line hints from audit):
2. `inde_RV_ev` (64–66)
3. `inde_RV_events'` (68–83)
4. `preimg_tt` (87–90)
5. `inde_unit_RV` (near the above; locate by `Lemma inde_unit_RV`)
6. `inde_rv_cprP` (163–169)
7. `add_RV` (Section add_RV, 209) with its `` X `+ Y `` notation if the
   copied statements below use it
8. `pr_add_eqE'` (212–223)
9. `big_fin_img` (225–233)
10. `pr_add_eqE` (235–243)
11. `add_RV_unif` (264–270)
12. `Pr_fdist_cond_RV` (289–290)
13. `fdist_cond_indep` (294–302)
14. `lemma_3_5` (335–354)
15. `lemma_3_5'` (358–363)
16. `sub_RV`, `neg_RV` (260–261)

From `PIN/dumas2017dual/lib/extra_proba.v`:
17. `pair_notin_fin_img_fst` (43–62)
18. `sum_cPr_eq` (67–90)
19. `cond_prob_zero_outside_constraint` (161–183)
20. `fdist_proj23_RV3` (238–243)

From `PIN/du2002/spp_entropy.v`:
21. `neg_RV_dist_eq` (347–358)
22. `neg_RV_inde_eq` (360–371)

From `PIN/dumas2017dual/lib/extra_entropy.v`:
23. `cinde_cond_mutual_info0` (73–114) — its proof calls
    `fdist_proj23_RV3` and `logr_eq1`, both above
24. `inde_cond_entropy` (559–569)

- [ ] **Step 1: Create the file**

File header comment (provenance, non-rendered):

```coq
(* Lemmas inlined from the pinned infotheo repository
   (~/Projects/coq/infotheo @ dumas2017dual, commit b5a899f7), from
   du2002/spp_proba.v, du2002/spp_entropy.v, dumas2017dual/lib/
   {extra_algebra,extra_proba,extra_entropy}.v, so that this project
   depends only on core infotheo + smc/. Statements and proofs verbatim
   except section plumbing. *)
```

Imports for the file: mirror each source file's own header, restricted to
core infotheo + mathcomp, e.g.
`From mathcomp Require Import all_ssreflect all_algebra.`,
`From mathcomp Require Import reals boolp.`,
`From infotheo Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist proba jfdist_cond graphoid entropy.`
(trim to what the copied lemmas actually need; the source headers are the
authority). Each declaration gets a one-to-two-line statement comment
(fact + role), per the statement-comment rules; no status markers.

- [ ] **Step 2: Register and compile it**

Add `lib/proba_entropy_ext.v` to `_CoqProject` after `lib/perm_uniform.v`.

```bash
make lib/proba_entropy_ext.vo
```

Expected: compiles cleanly. If a proof breaks, repair with minimal edits
(missing import, scope, implicit args). Escalate to the fallback ladder
(vendor whole module + DEVIATIONS.md) only after two failed repair rounds.

- [ ] **Step 3: Soundness check**

```bash
grep -nE 'Admitted|admit\.|Axiom' lib/proba_entropy_ext.v || echo CLEAN
```

Expected: `CLEAN`.

- [ ] **Step 4: Commit**

```bash
git add lib/proba_entropy_ext.v _CoqProject && git commit -m "feat: proba_entropy_ext with lemmas inlined from du2002/dumas2017dual"
```

---

### Task 5: Rewrite the seven banned-import consumers (proving)

**Files:**
- Modify: `DST/lib/perm_uniform.v`, `DST/security/pgg_leakage_product.v`,
  `DST/security/pgg_randomized_sharing.v`,
  `DST/instances/denboer1989/den_boer_encoding.v`,
  `DST/instances/kim2025/kim_input_privacy.v`,
  `DST/instances/kim2025/five_card_exec.v`,
  `DST/reconstruct/hyperelliptic_code.v`

- [ ] **Step 1: `lib/perm_uniform.v`** — delete the line
  `Require Import entropy_fiber extra_proba.` (imports are dead; audit
  found zero symbol/notation use and no side effects). Build:
  `make lib/perm_uniform.vo` → success.

- [ ] **Step 2: `security/pgg_leakage_product.v`** — delete
  `Require Import spp_proba.`; `inde_RV_comp` now resolves to the
  byte-identical core lemma in infotheo `probability/proba.v`. Build the
  file's target → success.

- [ ] **Step 3: `security/pgg_randomized_sharing.v`** — replace
  `Require Import spp_proba spp_entropy.` with
  `From pgg_smc Require Import proba_entropy_ext.`. Uses:
  `inde_RV_comp` (core), `add_RV`/`sub_RV`/`neg_RV` unfolds,
  `neg_RV_dist_eq`, `neg_RV_inde_eq`, `lemma_3_5'` (all in the helper).
  Build → success.

- [ ] **Step 4: `instances/denboer1989/den_boer_encoding.v`** — replace
  `From infotheo.dumas2017dual.lib Require Import extra_entropy.` with
  `From pgg_smc Require Import proba_entropy_ext.` (uses
  `cinde_cond_mutual_info0` at lines ~346, ~378). Build → success.

- [ ] **Step 5: `instances/kim2025/kim_input_privacy.v`** — add
  `From pgg_smc Require Import proba_entropy_ext.`; rewrite qualified
  references: `extra_proba.fdist_proj23_RV3` → `fdist_proj23_RV3`,
  `extra_proba.sum_cPr_eq` → `sum_cPr_eq`,
  `extra_proba.cond_prob_zero_outside_constraint` →
  `cond_prob_zero_outside_constraint` (lines ~93, ~105, ~120, ~128).
  Build → success.

- [ ] **Step 6: `instances/kim2025/five_card_exec.v`** — add
  `From pgg_smc Require Import proba_entropy_ext.`; rewrite
  `extra_entropy.inde_cond_entropy` → `inde_cond_entropy` (line ~752) and
  `spp_proba.inde_unit_RV` → `inde_unit_RV` (line ~753; this reference was
  a latent build-order bug in the monorepo). Build → success.

- [ ] **Step 7: `reconstruct/hyperelliptic_code.v`** — delete
  `rouche_capelli` from its requires; insert as private lemmas (verbatim
  from `PIN/dumas2017dual/lib/rouche_capelli.v`) before first use:
  `mxrank_sub_eqmx` (109–113), `rouche1` (117–126),
  `exists_nonzero_kernel` (146–153). All are pure mathcomp `mxalgebra`.
  Do NOT copy the file's HB/FinVector instances or its global
  `Open Scope ring_scope` (the file already opens it). Build → success.

- [ ] **Step 8: Grep gate and commit**

```bash
grep -rnE 'dumas2017dual|du2002|homomorphic_encryption|spp_proba|spp_entropy|extra_proba|extra_entropy|extra_algebra|entropy_fiber|rouche_capelli' \
  --include='*.v' . | grep -v 'lib/proba_entropy_ext.v' | grep -v '(\*' || echo CLEAN
```

Expected: `CLEAN`, modulo hits that sit inside comments (the helper's
provenance header is excluded wholesale; for every other residual hit,
open the file and confirm the line is within a `(* ... *)` comment —
a hit in live code is a failure).

```bash
git add -A && git commit -m "refactor: eliminate du2002/dumas2017dual imports via proba_entropy_ext"
```

---

### Task 6: Full build to green (proving)

- [ ] **Step 1: Full build**

```bash
cd /Users/cheng-huiweng/Projects/coq/rocq-pgg-smc && make -j8 2>&1 | tee build.log; tail -5 build.log
```

- [ ] **Step 2: Repair loop** — for each failing file: read the exact
error, fix minimally (import order, qualification collisions, notation
scope). The most likely failure classes and their first-line fixes:
  - unqualified name now ambiguous between infotheo and pgg_smc → prefix
    with `proba.`/module name or reorder imports;
  - a notation from a formerly-plain-required module lost → check the
    `From infotheo Require Import` line includes the module;
  - helper lemma statement mismatch (implicit args) → compare against the
    pinned source and align the helper, not the consumer.
  One semantic change per compile. Strategy-switch discipline applies
  (see CLAUDE.md): fix the step, do not change the approach without cause.

- [ ] **Step 3: Verify zero failures**

Run: `make -j8 2>&1 | tail -3` — Expected: no `Error`, exit 0.

- [ ] **Step 4: Commit**

```bash
git add -A && git commit -m "fix: repairs for standalone build against installed infotheo"
```

---

### Task 7: Blueprint script portability (mechanical)

**Files:**
- Modify: `DST/blueprint/make_blueprint.sh`

- [ ] **Step 1: Fix the `-R` flag block** — the script reconstructs
loadpath flags assuming the infotheo-pgg monorepo (`pgg-smc/...` paths and
`-R . infotheo`). Rewrite that block to emit exactly the `-R` lines of the
new `_CoqProject` (root-level dirs, no `-R . infotheo`), and point its
"repo root (has _CoqProject)" detection at `DST`.

- [ ] **Step 2: Fix the plastex default** — replace

```bash
PLASTEX="${PLASTEX:-/Users/cheng-huiweng/Projects/coq/infotheo-itp/dumas2017dual/blueprint/.venv/bin/plastex}"
```

with

```bash
PLASTEX="${PLASTEX:-$(command -v plastex || true)}"
```

keeping the env override. Do not run the blueprint build (out of gate).

- [ ] **Step 3: Syntax check and commit**

Run: `bash -n blueprint/make_blueprint.sh` — Expected: no output.

```bash
git add blueprint/make_blueprint.sh && git commit -m "fix: blueprint script paths for standalone layout"
```

---

### Task 8: Final verification (verification)

- [ ] **Step 1: Clean rebuild**

```bash
cd /Users/cheng-huiweng/Projects/coq/rocq-pgg-smc && make clean && make -j8 2>&1 | tail -3
```

Expected: full success from scratch. Count artifacts:
`find . -name '*.vo' -not -path './.git/*' | wc -l` → `149`.

- [ ] **Step 2: Grep gate** (same command as Task 5 Step 8) → `CLEAN`.

- [ ] **Step 3: Soundness parity** — for every tracked `.v`, compare
`Admitted|admit\.|Axiom` counts against the corresponding
`SRC/pgg-smc/...` file:

```bash
for f in $(git ls-files '*.v'); do
  new=$(grep -cE 'Admitted|admit\.|Axiom' "$f")
  case "$f" in lib/proba_entropy_ext.v) old=0;; *) old=$(grep -cE 'Admitted|admit\.|Axiom' "/Users/cheng-huiweng/Projects/coq/infotheo-pgg/pgg-smc/$f" 2>/dev/null || echo '?');; esac
  [ "$new" = "$old" ] || echo "DELTA $f: $old -> $new"
done
```

Expected: no `DELTA` lines (or only deltas explained by deleted banned
imports, listed and justified in the final report).

- [ ] **Step 4: Source-repo untouched check**

```bash
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg status --porcelain | diff - /private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq/1bbec039-5315-434b-ae0b-5eadd95c8a47/scratchpad/infotheo-pgg-status-before.txt && echo UNTOUCHED
```

Expected: `UNTOUCHED`.

- [ ] **Step 5: Regeneration reproducibility**

```bash
rm -f Makefile.rocq Makefile.rocq.conf && make Makefile.rocq && echo REGEN-OK
```

Expected: `REGEN-OK`.

- [ ] **Step 6: Final commit (if anything is dirty) and report**

```bash
git status --porcelain && git add -A && git commit -m "chore: post-verification tidy" || true
git log --oneline
```

Produce the verification report (build result, gate results, deviations
taken or none) as the task's return value.
