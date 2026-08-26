# Scan batch: security/ files 14-25 (pgg_schreier.v .. pgg_word_analysis.v)

31 findings (R2 grouped: 64 comment instances). Key results:

- DOMINANT [R2|A]: stacked statement-comment template (Kind:/Why:/Used by:/
  Naming:, and @intent:/@composes:/@main variants) in 10 of 12 files, ~64
  instances. Worst: pgg_security_solver.v (25x), pgg_word_analysis.v (10x,
  4-slot). Most >80-char R1 hits live inside these blocks. Fix: one
  formal-comment-review pass over security/.
- [R9|B]: pgg_schreier.v (310-315,322-327,368-374,388-399,402-414) and
  pgg_schreier_weighted.v (168-173,180-185,193-200,203-216,219-230) are a
  near-complete duplicate pair: 5 lemma/proof pairs identical modulo
  sc->wsc renaming. Fix: shared spectral-bound interface both certificates
  instantiate.
- [E1|A]: pgg_trace_secrecy.v:38-45 trace_secrecy_of_view — 8 binders + 3
  chained hypotheses over 6 lines; premise `cancel trace_of view_of`
  repeated with trace_secrecy_of_witness (61-66). Fix: shared Section over
  the (trace_of, view_of) cancellation pair.
- [E1|A]: pgg_word_analysis.v:257-262 comm_pair_count_full_comm — 6-line
  double-forall prefix. Fix: name the two premises (comm_total,
  word_no_adjacent_repeat) and/or Section-hoist.
- [R5|B]: pgg_schreier_weighted.v:410 and pgg_security.v:121,135 — numerical
  occurrence selectors {1}; pgg_word_analysis.v:343 — bullets on 2 subgoals.
- [R10/R9]: security/pgg_schreier_test.v [orphan] — sole lemma duplicates
  and Admits pgg_schreier.v:word_eval_cons; safe to delete.
- E1-compliant templates worth citing: pgg_schreier.v's four Sections,
  pgg_schreier_weighted.v unif_offdiag_convergence,
  pgg_uniform_security.v uniform_security.
- Minor: pgg_security.v R5 selectors + 1-line header (R4|C);
  pgg_security_solver.v should split its ~50 Eval vm_compute demos into a
  _demo companion (R4|C); assorted low-confidence R6 qualifications
  (Order.POrderTheory.*, FDist.ge0) needing per-site verification.

Full per-file detail lives in the scan agent transcript; this summary is
the aggregation source.
