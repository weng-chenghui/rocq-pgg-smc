# P0 + P1 close-out — 2026-08-26

P0: 11 per-file commits (fix(P0): ...). All ten correctness-adjacent
items fixed after independent claim verification: the vacuous
secure_edge_bound theorem deleted; the S_(m+2)-vs-RAAG header and the
iff overclaim corrected; misleading axiom narration removed; the
deck-pairing comment bugs fixed; four axiom-class declarations now
carry citations/evidence pointers. New finding stated honestly in the
code: pgg_uc_security's Conjecture is vacuous as stated (ideal_exec
discards its Simulator).

P1: 9 batch commits (style(P1): ...). ~2,477 declaration comments
rewritten or written across 145 files; zero template tokens remain
outside vendored files; ~85 provably false "Used by:" claims deleted;
all process narration/ticket IDs removed. Verification: every file
mechanically proven comment-only against HEAD (scripts/
strip_comments.py); full rebuild 153/153 EXIT=0, then incremental
rebuild after review fixes 88 files EXIT=0. An Opus sampling review
(42 mandatory + 13 extra samples, numeric claims checked against
statements) returned COMMIT WITH FIXES; all 21 mandated fix sites
applied. Along the way agents found and fixed 9 additional factually
wrong comments beyond the scan's list.

Deviation from formal-comment-review skill: commits are per directory
batch, not per file (11-agent fan-out; per-file commits would have
raced). Undo granularity is per batch.

## Deferred follow-ups (not part of P0/P1)
1. DONE (commit 41fa5ed): "sheet" -> "card position" unified in
   comment prose, 191 replacements / 38 files; covering-theory sense
   kept (multi_covering, cover_tradeoff Klein bound, rigidity_s5x5
   Bring's-curve section); identifier glosses per file.
2. Docstring carrier policy: batches disagreed on (** *) coqdoc vs
   (* *) plain (net 3399 -> 3154 docstrings). Pick a policy per
   generated-docs intent.
3. Banner-box alignment: ~60 new lines off modal box width in 16
   files; one orphan half-line (manifest:855). Mechanical sed pass.
4. Two axiom-citation gaps flagged in rigidity_s5x5_instance.v
   (s5x5_inverse_galois_realised, s5x5_multi_realised) — need real
   sources, not fabricated ones.
5. Vendored files (smc/, lib/proba_entropy_ext.v) untouched pending
   the provenance-policy decision.
