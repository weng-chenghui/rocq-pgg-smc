# Coordinator rulings on style audit C (2026-09-18)

| id | ruling |
|----|--------|
| T1 | ACCEPT. Try `by []`, then `exact: erefl`, then the unfolding rewrite; keep the first that compiles. If none does, keep the current proof and apply the T2 fallback sentence. |
| T2 | Conditional on T1, as the auditor wrote. |
| T3 | ACCEPT the proposed comment. |
| T4 | ACCEPT both header entries. |
| T5 | ACCEPT. |
| T6 | ACCEPT the source comment. |
| T7 | ACCEPT. |
| T8 | REJECT. Consistency with the frozen twins wins. |
| T9, T10 | No change; noted. |
| C1 | ACCEPT the proposed comment (must-fix). |
| C2 | ACCEPT: prove `pgl27_compare_classE` through `pgl27_compare_heart_setE`. |
| C3 | ACCEPT the proposed header text. |
| C4 | ACCEPT the appended paragraph. |
| C5 | ACCEPT if the single target still builds without it. |
| C6 | REJECT (no change). |
| C7 | No change. |
