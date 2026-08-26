# Scan batch: protocol/ (13 files, 3182 lines)

33 findings. Key results:

- [R2|A] systemic: five distinct comment-tag vocabularies (Kind:/Why:/Used
  by:, @intent:/@main/@composes:, Kind:/What:/Used-by: hyphenated, bare
  restatements, tag-free) drifting BETWEEN and WITHIN files
  (pgg_observed_execution.v and pgg_monodromy_profile.v mix two dialects
  each). pgg_interface.v is the source vocabulary (44 Kind:/34 Why:).
  pgg_correctness.v worst by density (pure type restatements; pgg_injective
  has no comment).
- [E3|A] strongest candidates in tree:
  * endpoint/compute (pgg_interface.v; nested endpoint (g*h) s =
    endpoint h (endpoint g s)) -> Local Notation or package rho as
    mathcomp action (x ^ y family).
  * run-context triple `x w0 P_idx` applied to 12 head symbols ~30x in
    pgg_execution_plug.v; `(oe_profile oe) (oe_execution oe)` 19x +
    `x w0 (oe_P_idx oe)` 23x in pgg_observed_execution.v -> run-context
    bundle record or scoped notation.
  * content_obs x (w0, tnth (pi_starts (mp_PI mp)) i) 7x nested 3-deep.
- [E1|A] card_protocol_posterior.v:111,131,197,234 — (HF : output_marginal
  F != 0) repeated across 4 lemmas -> sub-Section hoist + named predicate
  (E4).
- [R9|B] card_exchange_pismc.v:400-435,481-515 — 12 structurally identical
  duality lemmas; pgg_program.v [orphan] duplicates pgg_interface.v's
  pgg_protocol_ops verbatim (delete or justify in header, R10).
- [R2|A] pgg_uc_security.v:86-91 — Conjecture uc_simulation (Axiom-class)
  without literature citation (UC framework/Canetti) + roadmap narration
  above the statement.
- [R8|A] card_protocol_posterior.v:274 — channel_is_endpoint_dist should
  be *E-suffixed (equational). Header/code name mismatch at :18 vs :233;
  stale "stated as an axiom" comment with no axiom.
- R1: ~130 >80-char lines batch-wide, mostly inside R2 template blocks.
- Healthy files: pgg_run.v, card_protocol.v, pgg_session_types.v (modulo
  uneven comment depth).
- audit-quick.sh §25 note: ~115 raw @ hits are false positives (doc tags,
  dependent-type @sproc); only card_protocol_posterior.v:168 is a real
  tactic @ needing verification.
