# Scan batch: security/ files 1-13 (debug_morph.v .. pgg_sample_adapter.v)

39 findings. Key results:

- [E4|B] repeated premise fragments crying for named predicates:
  * Hypothesis HC : (0 < #|C|) — 4 sections of pgg_collusion_bound.v +
    2 of pgg_entropy_security.v (6 total)
  * Hypothesis TN : (T <= N) — 3 sections (coalition_below_threshold)
  * Hypothesis Hlfree : @weval_inj M L — 4 sections
  * Hreg regularity forall — duplicated across 2 sections of
    pgg_abelian_collapse.v (regular_action predicate)
  * Q_ge0/Q_row_sum/Q_col_sum doubly-stochastic triple + Q_symm/alpha_ge0
    restated across Sections in pgg_mixing.v (DoublyStochastic Q predicate)
- [R9|B] pgg_collusion_bound.v:312-415 collusion_bound_unconditional
  duplicates collusion_bound_k at k=1 (identical premise shape and
  one-line proof) -> derive from the general lemma.
- [E1|A] pgg_mixing.v:668-679 symm_ds_TV_bound re-inlines the
  alpha/Rayleigh premises its own Section TV_bound already hoists;
  pgg_collusion_bound.v:1240-1245 same pattern.
- [R2|A] Kind:/Why:/Used by:/Naming: template in 5/13 files, always on
  the "important" lemmas (worst Naming: lines 145-172 chars — main R1
  driver). NOTE inter-scanner disagreement: this scanner deems
  @main/@composes/@intent COMPLIANT; protocol/reconstruct scanners flag
  them as banned variants. Adjudication needed at consolidation (user
  rule bans all label scaffolding; keep the prose).
- [R2|A] pgg_entropy_security_demo.v:160-163 Axiom oc_entropy_bound_axiom
  without literature citation (only internal GAP/SageMath note).
- [R3|A] H-prefixed hypotheses beyond 5-line scope common in
  pgg_collusion_bound.v + debug_morph.v (incl. a LEMMA named
  Hcard_remaining); absent in pgg_mixing/pgg_sample_adapter (achievable).
- [R5|B] pgg_sample_adapter.v:265,280 funext on ffun goals -> apply/ffunP;
  pgg_entropy_security.v:766 move=> H; exact: H.
- [R6|C] boolp.funext qualified 7x in pgg_randomized_sharing.v + 2x
  canonical_sharing.
- Exemplary files: pgg_leakage_witness.v, pgg_fdist_rV_indep.v,
  pgg_cyclic_cut_leakage.v, pgg_sample_adapter.v (header).
