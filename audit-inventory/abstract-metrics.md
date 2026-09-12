# Abstract metrics: reproducible counts for wadt2026-abstract.tex

> Snapshot of the pre-extraction tree (infotheo-pgg, 2026-03). Line numbers,
> names (e.g. path_Hcomm, Hcard_remaining) and the file set predate the P2
> de-duplication, the R3 renames and the 2026-09-12 legacy/ move; the
> abstract-metrics pins are the WADT 2026 abstract's evidence and are kept
> as recorded. Regenerate only for a new submission.

The WADT 2026 extended abstract claims **75 files, 17K LOC, 47 main
theorems**. The first two are exactly correct under the rule and
recipe below; the third should be amended to **46** (the abstract's
47 over-counted by one because of a comment-line false positive in
`reconstruct/massey.v:213`; see the "Main theorems recipe"
section). These three numbers are
pinned by `pgg-smc/scripts/abstract_metrics.sh`. This document
records the rule and recipe behind each number so that a reviewer
can audit them without re-deriving the conventions.

## Exclusion rule for files and LOC

```
find pgg-smc -name '*.v' \
  -not -name 'debug_*' \
  -not -name '*demo*' \
  -not -name '*test*' \
  -not -name '*solver*'
```

The four exclusion patterns drop the following six files from the
total 81 `.v` files in pgg-smc, leaving 75:

- `security/debug_morph.v`
- `security/pgg_security_demo.v`
- `security/pgg_entropy_security_demo.v`
- `reconstruct/pgg_landscape_demo.v`
- `security/pgg_schreier_test.v`
- `security/pgg_security_solver.v`

This rule differs from `audit-inventory/scope.txt`, which is a
narrower transitive-import-closure scope of 65 files used by the
rocq-audit pipeline. The two rules are not interchangeable; the
abstract uses the broader exclude-by-filename rule because it
matches what an external reader would compute by inspecting the
directory listing.

## Code-only LOC recipe

The 17K figure is **code-only LOC**: block comments and blank lines
removed from the 75 in-scope files, then non-empty lines counted.
The recipe is the Python regex strip:

```python
import re
src = re.sub(r'\(\*.*?\*\)', '', src, flags=re.DOTALL)
non_empty = [line for line in src.splitlines() if line.strip()]
```

Applied across the 75 files, this yields **17,412** lines, rounded
to 17K in the abstract.

The naive alternative of removing only lines that begin with `(*`
overcounts (~20,764) because most comment lines do not start with
the comment open. Do not use that variant.

## Main theorems recipe

The 46 figure counts top-level `Theorem` and `Corollary`
declarations in the 75 in-scope files. The shell pattern is

```
grep -cE '^[[:space:]]*Theorem[[:space:]]+[A-Za-z_]' <file>
grep -cE '^[[:space:]]*Corollary[[:space:]]+[A-Za-z_]' <file>
```

Summed across the 75 files, this yields 42 Theorems plus 4
Corollaries, for 46. `Lemma`, `Definition`, `Fixpoint`, and
`Proposition` are deliberately excluded; only entries declared as
`Theorem` or `Corollary` count as "main" by this convention.

The pinned value 46 supersedes the figure 47 quoted in early
drafts of `wadt2026-abstract.tex`. The 47 figure used a looser
regex (`\w+` instead of `[A-Za-z_]`) that incorrectly counted a
comment line in `reconstruct/massey.v:213` reading
"`Theorem 1, derived from the dual code's minimum distance.`"
as a declaration. The corrected count excludes this match.

## Reproducing

```
$ bash pgg-smc/scripts/abstract_metrics.sh
files=75
LOC_raw=30298
LOC_code=17412
theorems=42
corollaries=4
main=46

excluded files (must equal the six listed in abstract-metrics.md):
  reconstruct/pgg_landscape_demo.v
  security/debug_morph.v
  security/pgg_entropy_security_demo.v
  security/pgg_schreier_test.v
  security/pgg_security_demo.v
  security/pgg_security_solver.v
```

The script exits non-zero if any pinned value drifts. Treat a drift
as a signal to refresh either the abstract or the pinned values.
