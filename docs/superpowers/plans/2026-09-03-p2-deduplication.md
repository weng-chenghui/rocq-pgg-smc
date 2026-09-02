# P2 De-duplication Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Execute the seven-item duplication-removal campaign of
`docs/superpowers/specs/2026-09-02-p2-deduplication-design.md` without
changing any exported statement.

**Architecture:** A statement-surface extractor script is built first
and gates every wave; waves run sequentially (W4, W1, W2, W3, W5, W6,
W7), one implementer and one reviewer per wave, one commit per work
item. The spec (at commit `156b306`) is the authority on scope and
mechanism; this plan adds the exact commands, code, and check
sequences.

**Tech Stack:** Rocq 9.0.0 (opam switch
`/Users/cheng-huiweng/Projects/coq/_opam`), MathComp 2.5, coq-infotheo
>= 0.9.7, `make` wrapper over `rocq makefile`, Python 3 for the gate
scripts.

**Conventions for every task:**
- Repo root: `/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc`. Always
  `cd` there first (the parent directory is not a git repo).
- Build logs: capture to a file and judge from the file, never from
  wrapped tool output (a PostToolUse hook decorates build results).
  Standard build command:
  `make -j8 > /tmp/p2-build-<wave>.log 2>&1; echo EXIT=$? >> /tmp/p2-build-<wave>.log`
  then check `tail -3 /tmp/p2-build-<wave>.log` shows `EXIT=0`.
- Stage only named files. Never `git add -A`.
- Never introduce `Admitted`, `admit`, or `Axiom`.
- Do not edit vendored `smc/*`, `lib/proba_entropy_ext.v`, or the
  orphans (`instances/star/rigidity_star_instance.v`,
  `security/debug_morph.v`, `security/pgg_schreier_test.v`).
- Line numbers below are baseline-`43b7974` hints; re-locate by
  declaration name.

---

### Task 1: Statement-surface gate script

**Files:**
- Create: `scripts/statement_surface.py`
- Reuses: `scripts/strip_comments.py` (imported as a module)

- [ ] **Step 1: Write the script**

```python
#!/usr/bin/env python3
"""Extract the exported statement surface of the _CoqProject tree.

One stdout line per exported declaration, sorted:

    file|section.path|kind|name|ctxhash|statement

statement is the declaration sentence with comments stripped and
whitespace normalized; for Definition/Fixpoint/Instance it is cut at
the first top-level `:=` (bodies are not surface). ctxhash is a
sha1 over the enclosing sections' Variable/Hypothesis/Context
sentences, because section discharge changes a statement with zero
text change. `Local` declarations and `Let`s are non-exported: they
are printed only under --local. HB.* generated names are out of this
extractor's reach (accepted risk, see the P2 spec's gate contract).

Usage:
    statement_surface.py [--rev COMMIT] [--local]

With --rev, files are read from that git revision (via `git show`),
so the before-surface of any wave is regenerated on demand and no
snapshot is stored.
"""
import hashlib
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from strip_comments import strip

KINDS = {"Definition", "Lemma", "Theorem", "Corollary", "Record",
         "Fixpoint", "Instance", "Axiom", "Notation"}
BODY_CUT = {"Definition", "Fixpoint", "Instance"}
CTX = {"Variable", "Variables", "Hypothesis", "Hypotheses", "Context"}
NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def sentences(text):
    """Split comment-stripped, whitespace-normalized Rocq source into
    sentences: a `.` followed by a space or EOF ends one, unless it is
    the second dot of `..` or sits inside a string literal."""
    out, cur, in_str = [], [], False
    n = len(text)
    for i, c in enumerate(text):
        cur.append(c)
        if c == '"':
            in_str = not in_str
        elif c == "." and not in_str:
            nxt = text[i + 1] if i + 1 < n else " "
            prev = text[i - 1] if i else " "
            if nxt == " " and prev != ".":
                out.append("".join(cur).strip())
                cur = []
    tail = "".join(cur).strip()
    if tail:
        out.append(tail)
    return out


def cut_body(s):
    """Truncate before the first top-level `:=` (outside all brackets
    and strings): the type is surface, the body is not."""
    depth, in_str = 0, False
    for i in range(len(s) - 1):
        c = s[i]
        if in_str:
            in_str = c != '"'
            continue
        if c == '"':
            in_str = True
        elif c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and s[i + 1] == "=" and depth == 0:
            return s[:i].rstrip()
    return s


def parse_file(fname, text, exported, local_out):
    stack = []  # [(section_name, [ctx sentences])]
    for s in sentences(strip_text(text)):
        while s.startswith("#["):
            j = s.find("]")
            if j < 0:
                break
            s = s[j + 1:].lstrip()
        toks = s.split(" ", 2)
        if not toks or not toks[0]:
            continue
        head = toks[0]
        if head in ("Section", "Module"):
            if len(toks) > 1:
                stack.append((toks[1].rstrip("."), []))
            continue
        if head == "End" or head == "End.":
            if stack:
                stack.pop()
            continue
        is_local = False
        if head in ("Local", "Global"):
            is_local = head == "Local"
            s = s[len(head):].lstrip()
            toks = s.split(" ", 2)
            head = toks[0] if toks and toks[0] else ""
        if head in CTX:
            if stack:
                stack[-1][1].append(s)
            continue
        if head not in KINDS:
            continue
        rest = s[len(head):].lstrip()
        if head == "Notation":
            m = re.match(r'"((?:[^"\\]|\\.)*)"', rest)
            name = m.group(1) if m else rest.split(" ", 1)[0]
        else:
            m = NAME_RE.match(rest)
            if not m:
                continue
            name = m.group(0)
        stmt = cut_body(s) if head in BODY_CUT else s
        secpath = ".".join(n for n, _ in stack)
        ctx = " | ".join(c for _, cl in stack for c in cl)
        ctxhash = hashlib.sha1(ctx.encode()).hexdigest()[:12]
        line = f"{fname}|{secpath}|{head}|{name}|{ctxhash}|{stmt}"
        (local_out if is_local else exported).append(line)


def strip_text(text):
    return strip(text)


def read_source(fname, rev):
    if rev:
        r = subprocess.run(["git", "show", f"{rev}:{fname}"],
                           capture_output=True, text=True)
        return r.stdout if r.returncode == 0 else None
    p = Path(fname)
    return p.read_text(encoding="utf-8") if p.exists() else None


def main():
    rev = None
    want_local = False
    args = sys.argv[1:]
    while args:
        a = args.pop(0)
        if a == "--rev":
            rev = args.pop(0)
        elif a == "--local":
            want_local = True
        else:
            sys.exit(f"unknown arg {a}")
    cp = read_source("_CoqProject", rev)
    if cp is None:
        sys.exit("cannot read _CoqProject")
    files = [l.strip() for l in cp.splitlines()
             if l.strip().endswith(".v") and not l.strip().startswith("-")]
    exported, local_out = [], []
    for f in files:
        src = read_source(f, rev)
        if src is None:
            print(f"MISSING|{f}", file=sys.stderr)
            continue
        parse_file(f, src, exported, local_out)
    for line in sorted(local_out if want_local else exported):
        print(line)


if __name__ == "__main__":
    main()
```

- [ ] **Step 2: Smoke-test it**

Run:
```bash
cd /Users/cheng-huiweng/Projects/coq/rocq-pgg-smc
python3 scripts/statement_surface.py > /tmp/p2-surface-base.txt
wc -l /tmp/p2-surface-base.txt
grep -c '^protocol/pgg_interface.v' /tmp/p2-surface-base.txt
grep 'Lemma|cartier_foata|' /tmp/p2-surface-base.txt | head -1
grep '|Axiom|' /tmp/p2-surface-base.txt | wc -l
python3 scripts/statement_surface.py --rev HEAD > /tmp/p2-surface-rev.txt
diff /tmp/p2-surface-base.txt /tmp/p2-surface-rev.txt && echo REV-OK
```
Expected: total in the low thousands; pgg_interface has dozens of
entries; the `cartier_foata` lemma appears once; Axiom count is
exactly 16; `REV-OK` prints (worktree is clean, so `--rev HEAD`
must agree byte-for-byte).

- [ ] **Step 3: Commit**

```bash
git add scripts/statement_surface.py
git commit -m "scripts: statement-surface extractor (P2 gate)"
```

**Gate procedure used by every wave below** (referred to as GATE):
```bash
cd /Users/cheng-huiweng/Projects/coq/rocq-pgg-smc
python3 scripts/statement_surface.py --rev <pre-wave-commit> > /tmp/p2-before.txt
python3 scripts/statement_surface.py > /tmp/p2-after.txt
diff /tmp/p2-before.txt /tmp/p2-after.txt > /tmp/p2-surface.diff; wc -l /tmp/p2-surface.diff
grep -rn "Admitted\|^Axiom\| Axiom " --include='*.v' $(grep '\.v$' _CoqProject) | grep -cv '(\*'   # expect Axiom 16, Admitted 0
```
The surface diff must contain ONLY the wave's authorized changes
(named per wave). Any other line is a policy violation: revert.

---

### Task 2: W4 — dead files (implementer: Sonnet)

**Files:**
- Delete: `protocol/pgg_correctness.v`, `protocol/pgg_program.v`
- Modify: `_CoqProject` (remove the `protocol/pgg_correctness.v` line)
- Modify: `protocol/card_exchange_pismc.v` (delete the two comment
  lines "Cross-equality with pgg_program.v and interpreter
  integration are / verified in pgg_correctness.v (not in this
  file)." — the claim is false and is deleted, not redirected)

- [ ] **Step 1:** Edit `_CoqProject`: remove the line
  `protocol/pgg_correctness.v`. Edit the comment in
  `card_exchange_pismc.v`. Then
  `git rm protocol/pgg_correctness.v protocol/pgg_program.v`.
- [ ] **Step 2:** Full rebuild (`make -j8`, log-captured), expect
  `EXIT=0`. Note: `Makefile.rocq` is regenerated from `_CoqProject`
  by the wrapper.
- [ ] **Step 3:** GATE. Authorized diff: exactly the 8 removed
  entries of `protocol/pgg_correctness.v` (`pgg_correctness`,
  `pgg_correctness1`, `pgg_correctnessV`, `pgg_injective`,
  `pgg_distinctness`, `pgg_bijectivity`, `starts_tnth_inj`,
  `endpoints_card`; `pgg_program.v` was never in the surface).
- [ ] **Step 4:** Reviewer (Opus) audits diff against spec W4.
- [ ] **Step 5:** Commit:
```bash
git add _CoqProject protocol/card_exchange_pismc.v
git commit -m "dedup(W4): delete pgg_correctness.v and orphan pgg_program.v

pgg_correctness re-derived endpointM/endpoint1/endpointV/endpoint_inj/
endpoint_starts_uniq from pgg_interface; pgg_bijectivity,
starts_tnth_inj, endpoints_card were dead exports nothing consumed.
The false cross-reference comment in card_exchange_pismc.v is deleted."
```

---

### Task 3: W1 — raag foata hoist (implementer: Opus)

**Files:**
- Modify: `groups/pgg_raag.v` (hoist 27 declarations out of
  `Section raag_gen_reflect`, baseline lines 1211-1897)
- Modify: `groups/pgg_raag_cartier_foata.v` (delete
  `Section foata_infrastructure`, retarget `not_sorted_descent`)
- ONE commit for both files.

The 27 declarations, in file order (verify mechanically: everything
from `Let foldl_maxn_shift` up to but excluding `Let comm_nat_sym`,
the first `Let` using a section variable):
`foldl_maxn_shift, foata_depth_at_bigop, foata_depth_at_perm,
foata_pairs_split', foata_pairs_vals, size_foata_pairs',
foata_depth_comm_rcons, foata_pairs_prefix, nth_foata_pairs_val,
nth_foata_pairs_depth, foata_pairs_perm_prefix,
foata_pairs_swap_adj, dv_leq_trans, dv_leq_anti, dv_leq_total,
sort_perm_eq_dv, foata_nf_swap_adj, foata_depth_noncomm_lb,
foata_descent_comm', foata_nf_sorted, not_sorted_descent',
w_split_nat, foata_inv (a Definition), foata_inv_zero,
foata_pairs_swap_nth, foata_inv_swap_lt, foata_nf_sound`
(if the mechanical boundary yields a slightly different list, the
boundary wins; record the difference).

- [ ] **Step 1:** In `pgg_raag.v`, create a new top-level
  `Section foata_infrastructure.` ... `End foata_infrastructure.`
  placed AFTER the `foata_nf`/`n_traces_natB` definitions and BEFORE
  `Section raag_theory`. Move the 27 declarations there verbatim,
  changing `Let` to `Lemma` (and `Let foata_inv ... :=` to
  `Definition foata_inv ... :=`). Renames while moving:
  `size_foata_pairs'` -> `size_foata_pairs`,
  `foata_descent_comm'` -> `foata_descent_comm`.
  `not_sorted_descent'` KEEPS its prime (`pgg_raag.v` already exports
  an unprimed `not_sorted_descent` over `seq nat`).
  `foata_pairs_split'` keeps its prime (primed in both files).
  Update every use site of the two renamed lemmas inside the
  remainder of `Section raag_gen_reflect`.
- [ ] **Step 2:** Compile `pgg_raag.v` alone first:
  `make groups/pgg_raag.vo` (log-captured), expect EXIT=0.
- [ ] **Step 3:** In `pgg_raag_cartier_foata.v`, delete the whole
  `Section foata_infrastructure.` ... `End foata_infrastructure.`
  block (statement-identical restatements of the 27, including its
  `Let foldl_maxn_shift`). Retarget the file's remaining uses of its
  deleted `not_sorted_descent` (the `seq (nat * nat)` one; ~2 sites)
  to the imported `not_sorted_descent'`. The other 26 names resolve
  unchanged via the existing `From pgg_smc Require Import pgg_raag`.
  Keep the header's section inventory comment accurate: rewrite its
  `Section foata_infrastructure` line to say the infrastructure now
  lives in `pgg_raag.v`.
- [ ] **Step 4:** Rebuild the two files and all downstream
  (`make -j8`, log-captured), expect EXIT=0.
- [ ] **Step 5:** GATE. Authorized diff: the relocation set — the 26
  entries moving file/section from `pgg_raag_cartier_foata.v` to
  `pgg_raag.v` with kind+name+statement preserved (modulo the two
  renames and the primed survivor, which appear as
  remove-old-name/add-new-name pairs); plus the NEW exported
  `foldl_maxn_shift` (was a `Let` in both files); plus cartier_foata's
  `not_sorted_descent` entry removed. No other change.
- [ ] **Step 6:** Reviewer (Opus) audits diff against spec W1,
  checking specifically that no statement text changed.
- [ ] **Step 7:** Commit both files:
```bash
git add groups/pgg_raag.v groups/pgg_raag_cartier_foata.v
git commit -m "dedup(W1): hoist foata infrastructure to pgg_raag.v exports

27 section-local Lets (26 lemmas + Definition foata_inv) exported from
a new top-level section; cartier_foata's statement-identical
restatements deleted. Renames: size_foata_pairs' -> size_foata_pairs,
foata_descent_comm' -> foata_descent_comm; not_sorted_descent' keeps
its prime (unprimed name taken at seq nat); foldl_maxn_shift newly
exported."
```

---

### Task 4: W2 — s5x5 pile generic sections (implementer: Sonnet)

**Files:**
- Modify: `instances/s5x5/s5x5_models.v` (20 pile declarations),
  `instances/s5x5/s5x5_mixing.v` (14), `instances/s5x5/s5x5_exec.v`
  (6). Do NOT touch `s5x5_analysis.v` (re-export facade),
  `s5x5_trace.v` (zero sites), or `s5x5_pile.v`.
- One commit per file (three commits), each gated.

- [ ] **Step 1 (per file, starting with the smallest, s5x5_exec.v):**
  identify the pile1/pile2 mirrored declaration pairs. For each pair
  decide: parametric over the quadruple (embedding `widen5to10` /
  `rshift5to10`, pile-uniform fdist `fdist_uniform_pile1` /
  `fdist_uniform_pile2`, the TV-bound lemma, the uniform-distance
  lemma) — or structurally different (like `prod_encode_pile1_lt` /
  `prod_encode_pile2_ge`, which differ in hypothesis polarity).
  Structural pairs are LEFT IN PLACE and listed in the commit
  message.
- [ ] **Step 2:** For the parametric pairs, add one
  `Section pile_generic.` inside the file (name it
  `pile_generic_<file>` if `pile_generic` collides), with
  `Variable`s/`Hypothesis`es for the quadruple, prove each fact ONCE,
  `End`, then re-establish every original exported name as an
  instantiation whose statement is byte-identical to the deleted
  original (copy the original statement text verbatim; the proof is
  `exact: (generic_name ...)` or `apply:` with the four instances).
  Byte-check each: the GATE will verify.
- [ ] **Step 3 (per file):** `make -j8` (log-captured), EXIT=0.
- [ ] **Step 4 (per file):** GATE. Authorized diff: ONLY added
  entries (the generic section's exports, if any are non-Local; make
  the generic lemmas `Local Lemma` inside the section where possible
  so the surface gains nothing). Existing entries unchanged.
- [ ] **Step 5 (per file):** Reviewer (Opus). Commit:
```bash
git add instances/s5x5/<file>
git commit -m "dedup(W2): factor pile1/pile2 mirror in <file> through pile_generic

<n> mirrored pairs instantiated from one parametric section
(embedding, pile fdist, TV bound, uniform distance); structural
non-mirror pairs left in place: <list or 'none'>."
```

---

### Task 5: W3 — cover_genus1/2 via higher_genus (implementer: Opus)

**Files:**
- Modify: `reconstruct/cover_genus1.v` (reorder sections,
  instantiate), `reconstruct/cover_genus2.v` (add import,
  instantiate). One commit per file.

- [ ] **Step 1:** In `cover_genus1.v`, move `Section higher_genus`
  (baseline :295-494) BEFORE `Section genus1` (baseline :50-289).
  Rebuild the file alone (`make reconstruct/cover_genus1.vo`),
  EXIT=0 — this move must be a no-op.
- [ ] **Step 2:** Inside `Section genus1`, keep `genus1_hurwitz` and
  `genus1_ramif_ge_nbr` with their concrete proofs (they are the
  instantiation's ARGUMENTS). Re-prove the downstream trio by
  instantiating: `genus1_data` from `higher_genus_data`,
  `genus1_covering` from `higher_genus_covering`, `elliptic_gap` and
  `genus1_vs_genus0` from `higher_genus_gap_bound` — at g:=1,
  ramif_g:=ramif1, discharging the two hypotheses with the concrete
  lemmas. Expect two convertibility frictions (`cd_n_branch := 3` vs
  `g + 2`; `+ 2` vs `+ 2 * g`): resolve with a `rewrite`/`congr` in
  the instantiating proof, never by changing the exported statement.
  A statement that turns out not to be an instance keeps its concrete
  proof and is recorded in the commit message.
- [ ] **Step 3:** `make -j8`, EXIT=0. GATE: no surface change at all
  for this file is the target (section reorder changes the
  section-path field of the moved entries — that path change for
  `higher_genus`/`genus1` entries is the only authorized diff).
  Reviewer (Opus). Commit `cover_genus1.v`:
  `dedup(W3): derive genus1 covering trio from higher_genus`.
- [ ] **Step 4:** In `cover_genus2.v`, add
  `From pgg_smc Require Import cover_genus1.` (import order: after
  the other pgg_smc imports; no cycle — nothing imports cover_genus2
  except downstream). Instantiate its concrete derivation the same
  way at g:=2, keeping its Riemann-Hurwitz inputs concrete.
  `make -j8`, EXIT=0. GATE: authorized diff none (statements
  unchanged; import is not surface). Reviewer. Commit:
  `dedup(W3): derive genus2 covering from higher_genus at g:=2`.

---

### Task 6: W5 — rigidity witnesses (implementer: Opus)

**Files:**
- Modify: `instances/abelian/rigidity_abelian_instance.v`,
  `instances/cyclic/rigidity_cyclic_instance.v`,
  `instances/oc/rigidity_oc_instance.v`. One commit per file.

- [ ] **Step 1 (per file):** locate the hand-rolled RS-code block
  (11 section variables/hypotheses, e.g. abelian baseline :170-187)
  and its consumption (`genus0_covering HG qn an HN sigma_fix0
  code_auto`, abelian baseline :194). Bind the witness as a
  section-local `Let` (NEVER a `Definition`/`Variable` — the arity
  trap):
```coq
Let rsw : RSCodeWitness _ := MkRSCodeWitness primeq qn an HN sigma_fix0 code_auto.
```
  (adjust field order to the actual `MkRSCodeWitness` constructor in
  `reconstruct/cover_genus0.v`), and re-derive the file's covering
  from `genus0_covering_witness rsw`. Delete the now-redundant
  intermediate derivation lines. The 11 variables/hypotheses
  themselves STAY (they are the instance's data).
- [ ] **Step 2 (per file):** `make -j8`, EXIT=0. GATE: authorized
  diff none (Let is not surface; section context unchanged since the
  variables stay). If the ctxhash of the file's exports changes, the
  variables were touched — revert. Reviewer (Opus). Commit:
  `dedup(W5): route <family> rigidity through genus0_covering_witness`.
- [ ] **Step 3:** Inspect `rigidity_kim_instance.v`,
  `rigidity_monster_instance.v`, `rigidity_s5_instance.v`,
  `rigidity_s5x5_instance.v` for the same verbatim block; apply the
  same change only where verbatim; record the inspection result in
  the last commit message. No-net-increase gate applies: if a file's
  change saves nothing, skip it and record.

---

### Task 7: W6 — schreier shared rate section (implementer: Opus)

**Files:**
- Modify: `security/pgg_schreier.v` and/or
  `security/pgg_schreier_weighted.v`. One commit.

The five pairs: `convergence_rate_ge0/weighted_convergence_rate_ge0`,
`convergence_rate_lt1/weighted_convergence_rate_lt1`,
`schreier_epsilon_ge0/weighted_schreier_epsilon_ge0`,
`schreier_epsilon_decreasing/weighted_schreier_epsilon_decreasing`,
`security_monotone/weighted_security_monotone`.

- [ ] **Step 1:** Check the import direction between the two files
  (`grep Require security/pgg_schreier*.v`). Put a shared section in
  the imported one (or, if neither imports the other, in whichever
  both already transitively import — else add the one import,
  direction: weighted imports unweighted, matching the name
  precedence). The shared section is over `lam : R` with hypotheses
  `0 < lam` and `lam <= 1`, containing the four rate/epsilon facts
  once, as `Local Lemma`s (they are new machinery; keep them off the
  surface).
- [ ] **Step 2:** Re-prove both members of pairs 1-4 as one-line
  applications of the shared facts; statements unchanged. Pair 5
  (`security_monotone`): attempt a further section parametric in the
  endpoint law; if the parametrization would force any exported
  statement to change, SKIP pair 5 and record.
- [ ] **Step 3:** `make -j8`, EXIT=0. GATE: authorized diff none (all
  additions are Local). No-net-increase check:
  `git diff --stat` must not show a net gain. Reviewer (Opus).
  Commit: `dedup(W6): factor schreier rate lemmas through a shared
  lam section`.

---

### Task 8: W7 tail (implementers: Sonnet for 8a-8d, Opus for 8e)

One commit per sub-item, each gated (`GATE`: authorized diff per
sub-item, default none).

- [ ] **8a (W7.3):** `reconstruct/pgg_protocol_landscape.v`: replace
  `ar_genus1_gap2`'s copy-pasted proof body with
  `Proof. exact: genus1_universal_option. Qed.` (same file; its
  siblings at baseline :356/:375 already use this form). Rebuild,
  GATE (no diff), commit
  `dedup(W7): ar_genus1_gap2 via genus1_universal_option`.
- [ ] **8b (W7.4):** in `instances/pgl27/pgl27_word_privacy.v`,
  promote `Let pow2_split` to an exported
  `Fact pow2_split : (2%:R : R)^-40 + 2%:R^-40 = 2%:R^-39.` (same
  statement/proof, directly after its section's `Variable R`);
  delete the identical `Let` in `instances/pgl27/pgl27_models.v`
  (which imports `pgl27_word_privacy`). Rebuild, GATE (one added
  entry), commit `dedup(W7): single pow2_split Fact`.
- [ ] **8c (W7.1):** in `instances/kim2025/kim_secrecy.v`, add
  `From pgg_smc Require Import denboer_secrecy.` and redefine
  `kim_mechanism := denboer_mechanism R` (body edit, granted by the
  policy exception), deleting the duplicated construction lines;
  `kim_view_secrecy` keeps its statement and one-line proof. If
  Qed-opacity of `denboer_indep` breaks the file, revert and record
  as skipped. Rebuild, GATE (no statement change; `kim_mechanism`'s
  surface entry is its type, unchanged), commit
  `dedup(W7): kim_mechanism aliases denboer_mechanism`.
- [ ] **8d (W7.5):** `groups/pgg_raag_clique.v`: factor ONLY
  `spos_unfold/sneg_unfold` and `spos_pascal_core/sneg_pascal_core`
  through a parity-parametric `Local Lemma` IF net lines do not
  increase (check with `git diff --stat` before committing);
  otherwise revert and record as skipped. Rebuild, GATE, commit or
  record.
- [ ] **8e (W7.6):** `mk_player_aprocs`. Define once, in
  `protocol/pgg_run.v` or wherever `mk_aproc`'s consumers already
  import (verify with `grep -l "mk_aproc" --include='*.v' -r . |
  xargs grep -l "Require.*pgg_run"`; pick the common-import file):
```coq
Definition mk_player_aprocs (ps : seq (nat * proc)) : seq aproc :=
  [seq mk_aproc (exchange_player p.1 p.2) | p <- ps].
```
  (Adjust the exact shape to what the 85 definition-body sites
  actually repeat — read three sites first; the helper MUST produce a
  term convertible to the old bodies.) Rewrite ONLY definition-body
  sites, file by file, rebuilding after each file. The 40 in-statement
  sites (the seven `*_endpoints` lemmas listed in the spec) are
  untouchable. Containment: if a downstream proof that unfolds a
  rewritten definition breaks and one local `rewrite
  /mk_player_aprocs` does not fix it, `git checkout -- <file>` and
  record the file as skipped. GATE after each file (definition
  bodies are not surface; expect zero diff except the one added
  helper entry). One commit for the whole sub-item, listing per-file
  outcomes. Commit: `dedup(W7): mk_player_aprocs helper for
  exchange-player boilerplate`.

---

### Task 9: Close-out

- [ ] **Step 1:** Final full clean-ish verification: `make -j8`
  (log-captured) EXIT=0; GATE against `156b306`'s successor (the
  pre-W4 commit) reviewing the cumulative authorized diff; Admitted 0
  / Axiom 16 in `_CoqProject` files; total net line delta reported
  via `git diff --stat <pre-W4>..HEAD -- '*.v' _CoqProject`.
- [ ] **Step 2:** Append a P2 section to
  `docs/style/scan-2026-08-26/P0-P1-CLOSEOUT.md`: per-item outcome
  (done/skipped-and-why), line delta, the two spec-recorded skips
  (W7.2, and any runtime skips), commit list.
- [ ] **Step 3:** Update the project memory file
  (`rocq-pgg-smc-standalone-repo.md`) if any gotcha of lasting value
  emerged (e.g. the not_sorted_descent name-type split).
- [ ] **Step 4:** Commit docs:
  `docs: P2 close-out (waves W4,W1,W2,W3,W5,W6,W7)`.

---

## Self-review notes

Spec coverage: W1..W7 map to Tasks 3,4,5,6,7,8; the gate script and
its contract map to Task 1; W7.2's authorized skip is recorded in
Task 9's close-out rather than as a no-op task. Gate 4 (line-count
direction) is enforced in Tasks 4-8 via `git diff --stat` checks.
Type consistency: the extractor's field order
(file|section|kind|name|ctxhash|statement) is used consistently in
all GATE descriptions. Known open judgment calls delegated to
implementers with explicit skip-and-record escapes: W2 structural
pairs, W3 non-instance statements, W5 no-saving files, W6 pair 5,
W7.1 opacity, W7.5 net-lines, W7.6 fragile files.
