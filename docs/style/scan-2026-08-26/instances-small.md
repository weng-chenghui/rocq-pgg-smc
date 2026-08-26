# Scan batch: instances/{abelian,cyclic,oc,star,monster} (13 files)

33 findings. Key results:

- [R9|B] PRIME: the AlgebraicRigidity Instance section (~35-line
  Hypothesis+covering+threshold+rigidity block) is copy-pasted modulo
  prefix across rigidity_{abelian:163-207,cyclic:112-149,oc:251-289,
  star:129-168}_instance.v; the *_complexity/*_tradeoff tail is identical
  in ALL FIVE (incl. monster:182-197). Fix: one parametric section over
  MonodromyReprWithGeneratorType with RS-code hypotheses as
  Variables/Hypothesis; instances instantiate.
- [E1|A] abelian_word_collapse.v:34-195 — (Habel : abelian G) repeated
  across 6 lemmas + (forall i, P i -> F i \in G) across 4 -> hoist
  Hypothesis Habel once in Section freq_vector.
- [R2|A] both failure modes: template bloat (abel_profile.v 32/32 stacked
  Kind:/What:/Why:/Used-by: PLUS redundant @tags; abelian_models.v 54;
  rigidity_abelian 4-slot 176-char record line) AND total absence
  (pgg_raag_star.v 2/21 documented, pgg_oc_param.v 2/13,
  rigidity_cyclic 5/9 uncommented).
- [R5|B] genuine: abel_profile.v:238,331 have -> ... by [] (inline it);
  rigidity_cyclic:82 same; pgg_oc_param.v:83,104,112,123 banned { }
  tactic braces; rigidity_oc:156,157,218,219 redundant %R in open
  ring_scope. False positive rejected: pgg_abelian.v:188 (`; last` form).
- [R10|C] pgg_raag_star.v:76-78 — three unused Lets (n0_ne_n1 etc.),
  distinctness re-derived locally at every use site instead.
- [R1|B] ~90 over-80 lines batch-wide, mostly template-comment-driven
  (worst 153-176 chars in Why:/Naming: lines).
- R3 clean batch-wide; E5 concreteness exception applied; star orphan
  confirmed ([orphan] rigidity_star_instance.v, has 1 Admitted, out of
  scan scope).
