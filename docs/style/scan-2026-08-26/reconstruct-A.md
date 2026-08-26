# Scan batch: reconstruct/ files 1-17 (ag_code.v .. invariant_profiler.v)

30 findings. Key results:

- DOMINANT [R2|A]: stacked comment template (Kind:/What:/Why:/Used by:/
  Naming:/Why waived:/@intent:/@composes:) in ALL 17 files. Several files
  have genuinely good domain-position prose trapped in the slots
  (invariant_profiler.v best-in-batch; dropout_witness.v record fields and
  cover_tradeoff.v sections 1-3 are the template-free models to copy).
- ARCHITECTURAL [R9|B]+[E5|C]: cover_genus1.v:295-497 defines a GENERIC
  higher_genus section, while cover_genus1.v:50-289 (g:=1 hardcoded) and
  cover_genus2.v:52-292 (g:=2) re-derive the identical ~250-line block
  concretely (suffix renames only). Fix: instantiate higher_genus_covering
  at g:=1 and g:=2; mirror cover_genus0.v's RSCodeWitness factoring.
- [E1|A]: algebraic_rigidity.v:454-471 ar_protocol_correct — 5+ premises,
  G_stable's forall spans 5 lines, `cs_scheme (tw_covering (ar_threshold
  ar))` nested 3-deep repeated 8+ times (also E3 candidate; siblings
  already use `let cs :=`). cover_genus0.v:185-201 genus0_secret_invariant
  repeats the same G_stable premise shape — factor a shared predicate (E4).
  gap_dimension.v:37-40 gap_dim_window — 4 premises over 3 lines.
- [R7|C]: non-Local `Open Scope ring_scope.` in ag_code.v:29,
  ag_massey_bridge.v:28, ag_multiplicative.v:31, coord_perm_compatible.v:27,
  hyperelliptic_code.v:37.
- [R5|B]: hyperelliptic_code.v:484-552 hyp_priv_surj — 8 brace-focus
  `have H : T. { ... }` blocks (banned; use indentation + by/exact:).
- [R10|C]: hyperelliptic_code.v:565-577 Section genus2 declares unused
  Variables/Hypotheses, no content.
- Structurally clean models: coord_perm_compatible.v (best sections),
  cover_tradeoff.v (best prose), input_encoding.v (best generality).

Raw >80-char breakdown: scratchpad/audit17.txt (agent-side).
