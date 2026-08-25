# rocq-pgg-smc extraction design

Date: 2026-08-26
Status: approved (user pre-approved autonomous execution; scope constraints given 2026-08-26)

## Goal

Extract the `pgg-smc/` subtree of `~/Projects/coq/infotheo-pgg` into a standalone
Rocq project at `~/Projects/coq/rocq-pgg-smc` that builds against the installed
`coq-infotheo` opam package instead of living inside an infotheo fork.
Done means: a fresh `make` in the new repo compiles every `.v` file in its
`_CoqProject` cleanly, with infotheo-pgg left byte-for-byte untouched.

## User decisions (recorded)

1. Name and place: repo `~/Projects/coq/rocq-pgg-smc`, opam package
   `rocq-pgg-smc` (rocq-era naming, mirrors `rocq-bignums`). Logical
   namespaces unchanged: `pgg_smc` and `pgg_reconstruct`.
2. Fresh git repo, no carried history. infotheo-pgg retains the history.
3. infotheo-pgg is NOT modified in any way.
4. Carry everything: `.v` sources plus `blueprint/`, `notes/`, `paper/`,
   `paper-wadt2026/`, `paper-wadt2026-baseline-application/`,
   `audit-inventory/`, `scripts/`, `manifest/` (build artifacts and caches
   excluded, see Copy rules).
5. Qualify all plain `Require Import` lines that resolve into infotheo as
   `From infotheo Require Import ...`. Internal pgg_smc-to-pgg_smc plain
   requires stay as-is.
6. The four orphan `.v` files not in `_CoqProject`
   (`instances/star/rigidity_star_instance.v`, `protocol/pgg_program.v`,
   `security/debug_morph.v`, `security/pgg_schreier_test.v`) are copied but
   stay out of the build.
7. Dependency surface constraint (user, 2026-08-26): the new repo must NOT
   depend on infotheo's `dumas2017dual/`, `du2002/`, or
   `homomorphic_encryption/` subtrees. Core infotheo (`lib/`, `probability/`,
   `information_theory/`, `ecc_classic/`) plus `smc/` (piSMC language:
   `pismc`, `smc_interpreter`, `smc_session_types`) is the allowed surface.
8. Autonomous execution: subagents do all jobs through to a verified local
   build; mechanical work on Sonnet, proving/verification on Opus-class
   agents.

## Facts the design rests on (established by exploration, 2026-08-25/26)

- Toolchain: Rocq 9.0.0 in the opam switch `~/Projects/coq/_opam`;
  `rocq makefile` works; `coq_makefile` coexists as a shim.
- `coq-infotheo` dev is opam-pinned to `~/Projects/coq/infotheo` branch
  `dumas2017dual` (commit b5a899f7) and installed at
  `_opam/lib/coq/user-contrib/infotheo/`.
- All 26 infotheo modules pgg-smc imports exist in the installed package.
  The two files where infotheo-pgg's own infotheo layer diverges from the
  pin (`entropy.v`, `smc_interpreter.v`) diverge only in regions whose
  symbols pgg-smc never references; the installed version is usable.
- pgg-smc: 152 `.v` on disk, 148 in `_CoqProject`, currently compiled.
- Two logical roots today: `pgg_smc` (lib, protocol, groups, security,
  instances/*, manifest) and `pgg_reconstruct` (reconstruct). Five
  `-arg -w` warning-suppression flags in `_CoqProject`.
- ~90 files use plain `Require Import` resolving into infotheo by suffix
  search; exact per-file mapping is in the exploration report (module ->
  installed path table).
- Banned-subtree usage (full audit, symbol-level, .glob-verified):
  - `lib/perm_uniform.v` imports `entropy_fiber`, `extra_proba`: ZERO
    symbols used, no side effects. Fix: drop both imports.
  - `security/pgg_leakage_product.v` imports `spp_proba`: only
    `inde_RV_comp`, which exists byte-identically in core
    `probability/proba.v`. Fix: drop the import.
  - `instances/denboer1989/den_boer_encoding.v` imports `extra_entropy`:
    uses only `cinde_cond_mutual_info0` (42 lines; needs `fdist_proj23_RV3`
    6 lines, `logr_eq1` 8 lines). Fix: inline into shared helper.
  - `instances/kim2025/kim_input_privacy.v` reaches `extra_proba.*`
    qualified (via transitive Require): needs `fdist_proj23_RV3`,
    `sum_cPr_eq` (24 lines + `pair_notin_fin_img_fst` ~20),
    `cond_prob_zero_outside_constraint` (23 lines). Fix: same helper;
    rewrite qualified references.
  - `instances/kim2025/five_card_exec.v` reaches `extra_entropy.inde_cond_entropy`
    (11 lines) and `spp_proba.inde_unit_RV` qualified. The `spp_proba`
    reference has NO visible Require path and may only compile today due to
    a stale interactive session: latent build-order bug. Fix: inline both
    into the helper; rewrite references.
  - `reconstruct/hyperelliptic_code.v` imports `rouche_capelli`: uses only
    `rouche1` + `exists_nonzero_kernel` (+ `mxrank_sub_eqmx`), ~25 lines of
    pure mathcomp mxalgebra. Fix: inline privately into the file itself.
  - `security/pgg_randomized_sharing.v` imports `spp_proba`, `spp_entropy`:
    uses `inde_RV_comp` (core, free), `add_RV`/`sub_RV`/`neg_RV`
    (one-liners), `neg_RV_dist_eq`/`neg_RV_inde_eq` (24 lines), and
    `lemma_3_5'` whose self-contained chain is ~140 lines
    (`inde_RV_ev`, `inde_RV_events'`, `preimg_tt`, `inde_rv_cprP`,
    `pr_add_eqE'`, `big_fin_img`, `pr_add_eqE`, `add_RV_unif`,
    `Pr_fdist_cond_RV`, `fdist_cond_indep`, `lemma_3_5`, `lemma_3_5'`).
    Fix: inline the chain into the helper.
  - All inlined material depends only on core infotheo + mathcomp; none of
    it pulls further banned modules once `logr_eq1`, `fdist_proj23_RV3`
    are carried along.
- The installed package has a stray duplicate `rouche_capelli.vo`; moot
  once the import is eliminated.
- `blueprint/make_blueprint.sh` hardcodes a plastex path under the sibling
  repo `infotheo-itp` and reconstructs `-R` flags assuming the infotheo-pgg
  monorepo layout; both need adjusting.
- pgg-smc directly imports mathcomp (ssreflect core, fingroup incl.
  morphism/action/perm, algebra incl. matrix/poly/zmodp/finalg/mxalgebra,
  order), `boolp` (mathcomp-classical), `reals` (mathcomp-reals), HB, and
  Stdlib (`Lia`, `BinNat`, `Nnat`, `Wf_nat`).

## Repo layout

```
rocq-pgg-smc/
  _CoqProject
  Makefile                  (delegating wrapper; regenerates via rocq makefile)
  rocq-pgg-smc.opam
  README.md
  .gitignore
  LICENSE                   (copied from infotheo; the work derives from it)
  lib/  protocol/  groups/  security/  reconstruct/
  instances/{abelian,cyclic,denboer1989,kim2025,monster,oc,pgl27,s5,s5x5,star}/
  manifest/
  blueprint/  notes/  paper/  paper-wadt2026/
  paper-wadt2026-baseline-application/  audit-inventory/  scripts/
  docs/superpowers/{specs,plans}/
  DEVIATIONS.md             (only if a fallback was taken; absent otherwise)
```

The `pgg-smc/` prefix is dropped: its children become repo-root directories.
`fault_tolerance/` is empty and is not carried (git cannot track it).

## _CoqProject

- Same five `-arg -w` flags as today.
- `-R` lines: each of `lib`, `protocol`, `groups`, `security`,
  `instances/<each>`, `manifest` maps to `pgg_smc`; `reconstruct` maps to
  `pgg_reconstruct`. No `-R . infotheo` (infotheo comes from the installed
  package via the standard loadpath).
- File list: the 148 current entries with the `pgg-smc/` prefix stripped,
  plus the new helper `lib/proba_entropy_ext.v` inserted before its first
  consumer. Order otherwise preserved (it is a valid dependency order today).

## Build system

`rocq makefile -f _CoqProject -o Makefile.rocq` generates the real
makefile; a small committed `Makefile` wraps it (targets: `all` [default],
`clean`, `install`, pass-through `%.vo`), regenerating `Makefile.rocq`
whenever `_CoqProject` changes. Generated files (`Makefile.rocq`,
`Makefile.rocq.conf`, `.Makefile.rocq.d`) are gitignored.

## opam package

`rocq-pgg-smc.opam`, name `rocq-pgg-smc`, version `dev`, following the
rocq-era convention observed on `rocq-bignums`. Depends: `rocq-core`
(>= 9.0 & < 9.2~), `rocq-stdlib`, `coq-infotheo` (the actual installed
package name for the pinned infotheo), and the mathcomp/HB packages
pgg-smc imports directly; the implementing agent verifies each dependency
name against `opam list` in the switch, preferring `rocq-*` names where
installed and the `coq-*` name otherwise. Build/install stanzas mirror
`rocq-bignums` (`make -j%{jobs}%` / `make install`). The opam file is
declarative metadata; the acceptance gate is `make`, not `opam install`.

## Source transformations

1. Copy (rules below), dropping the `pgg-smc/` prefix.
2. Import qualification: every plain `Require Import`/`Require Export`
   whose modules resolve into infotheo is rewritten to
   `From infotheo Require Import ...`. Lines mixing infotheo and pgg_smc
   modules are split into two lines. Internal pgg_smc plain requires are
   untouched. The `From infotheo.dumas2017dual.lib Require` line in
   `den_boer_encoding.v` is removed as part of transformation 3.
3. Banned-import elimination, per the audit above:
   - New file `lib/proba_entropy_ext.v` (namespace `pgg_smc`): the
     inlined lemma set (`logr_eq1`, `fdist_proj23_RV3`,
     `pair_notin_fin_img_fst`, `sum_cPr_eq`,
     `cond_prob_zero_outside_constraint`, `cinde_cond_mutual_info0`,
     `inde_cond_entropy`, `inde_unit_RV`, `add_RV`, `sub_RV`, `neg_RV`,
     `neg_RV_dist_eq`, `neg_RV_inde_eq`, and the `lemma_3_5'` chain).
     Statements and proofs are copied from the pinned infotheo sources
     (known-good), with a provenance header comment naming the source
     files and commit. Comments on each declaration follow the
     statement-comment rules (fact + position, no meta).
   - `lib/perm_uniform.v`: delete the two dead imports.
   - `security/pgg_leakage_product.v`: delete the `spp_proba` import
     (resolution moves to core `proba.inde_RV_comp`).
   - `security/pgg_randomized_sharing.v`,
     `instances/denboer1989/den_boer_encoding.v`,
     `instances/kim2025/kim_input_privacy.v`,
     `instances/kim2025/five_card_exec.v`: import the helper; rewrite
     qualified `extra_proba.*`/`extra_entropy.*`/`spp_proba.*` references
     to the helper's names.
   - `reconstruct/hyperelliptic_code.v`: inline `mxrank_sub_eqmx`,
     `rouche1`, `exists_nonzero_kernel` as private lemmas in-file; drop
     the `rouche_capelli` import.
4. `blueprint/make_blueprint.sh`: regenerate its `-R` flag block for the
   new layout; replace the hardcoded plastex default with a
   `command -v plastex` fallback behind the existing `PLASTEX` env
   override. Blueprint generation is adapted but NOT run as part of the
   build gate.

Fallback ladder for transformation 3 (per file): if an inlined proof does
not re-check after two repair rounds by an Opus agent, vendor the whole
source module as a `pgg_smc` lib file with a provenance header and record
the deviation in `DEVIATIONS.md`. Importing `dumas2017dual`/`du2002`/
`homomorphic_encryption` from installed infotheo is never acceptable.

## Copy rules

rsync from `infotheo-pgg/pgg-smc/` excluding: `*.vo`, `*.vos`, `*.vok`,
`*.glob`, `*.aux`, `.*.aux`, `*.d`, `.DS_Store`, `__pycache__/`, `*.pyc`,
`.lia.cache`, `paper-wadt2026/tmp/`. LaTeX build residue is carried as-is
(harmless, and per-directory filtering is not worth the complexity).
`.claude/` and `.cursor/` inside pgg-smc are carried. The same patterns
go into `.gitignore`.

## Verification (definition of done)

1. From a clean state (`git clean -xdf` equivalent scratch checkout or
   `make clean`), `make -j` succeeds: all `_CoqProject` files compile.
2. Grep gate over tracked `.v` files: no references to `dumas2017dual`,
   `du2002`, `homomorphic_encryption`, `spp_proba`, `spp_entropy`,
   `extra_proba`, `extra_entropy`, `extra_algebra`, `entropy_fiber`,
   `rouche_capelli` outside comments.
3. Soundness parity: no `Admitted`/`admit`/`Axiom` occurrences in the new
   tree that are not present in the corresponding infotheo-pgg source
   file; `lib/proba_entropy_ext.v` and all inlined lemmas end in `Qed`.
4. `git -C ~/Projects/coq/infotheo-pgg status --porcelain` shows no new
   modifications relative to the pre-extraction snapshot (taken before
   work starts).
5. `rocq makefile -f _CoqProject -o Makefile.rocq` regenerates without
   error (reproducibility of the build setup).

## Team routing

- Sonnet (mechanical): scaffold, copy, `_CoqProject`/Makefile/opam/README/
  .gitignore authoring, import-qualification rewrite, blueprint script fix.
- Opus (proving/verification): helper-file construction and consumer
  rewrites, hyperelliptic inlining, build-failure repair
  (`rocq:proof-repair`-style loop), final verification pass.
- Controller audits proving agents ~every 5 minutes; wrong-track agents
  are stopped and relaunched with tighter constraints rather than waited
  out.
