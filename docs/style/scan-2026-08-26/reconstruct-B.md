# Scan batch: reconstruct/ files 18-35 (lagrange.v .. transitivity_privacy.v)

37 findings (18 A / 14 B / 5 C). Key results:

- CORRECTNESS-ADJACENT [R2|A]: pgg_threshold.v:247-254 secure_edge_bound
  concludes literally `True` — a vacuous theorem dressed as a security
  bound, with roadmap narration as its comment. Formalize or delete.
- COMMENT BUGS [R2|A]: pgg_deck_pairing.v:58-60 comment describes the
  NEXT lemma, not its own; :67-74 comment claims is_involution is used
  but the proof discards it. Comments actively misstate the mathematics.
- [E1|A] strongest case: transitivity_privacy.v:895-908 profile_view_indep
  — 10 parameters, 14-line statement. Also pgg_covering_correctness.v:52-64
  (8-line G_stable inline; the fix pattern exists in pgg_dealer_bridge.v),
  pgg_protocol_landscape.v:311-329, pgg_sharing_framework.v:293-305,
  pgg_deck_pairing.v:203-212.
- [E4|B]: coalition bound (#|C| <= t) repeated 5x in
  transitivity_privacy.v (the catalog's own canonical example); the
  cast_tuple/tnth chain 3x in pgg_dealer_bridge.v; sw security clause 3x
  in pgg_protocol_landscape.v; content-perm-stability shape re-derived
  inline despite a named predicate existing (pgg_sharing_framework.v);
  recoverable_bits fragment 3x in pgg_threshold.v.
- [R9|B]: pgg_protocol_landscape.v:160-167 vs 384-390 — identical
  statement AND proof script copy-pasted (ar_genus1_gap2 should call
  genus1_universal_option); transitivity_privacy.v:337-345 vs 711-717 —
  5-line Variable/Hypothesis block copy-pasted between sections;
  pgg_threshold.v ramp_security_reconstruction re-derives ramp_threshold.
- [R2|A] template plague: s5_nogo.v worst (~26 four-slot instances, good
  What: prose trapped inside); rs_massey_bridge.v densest per line
  (13/15); pgg_assignment.v (22); massey.v (21); product_threshold.v (12);
  transitivity_privacy.v ~30 @tag lines appended to otherwise-good prose.
- [R6|C] boolp.funext qualified 5x in transitivity_privacy.v.
- Clean models: lagrange.v, pgg_landscape_demo.v (Q/A style),
  rs_privacy.v (correct non-rendered (* *) proof-strategy comments).
