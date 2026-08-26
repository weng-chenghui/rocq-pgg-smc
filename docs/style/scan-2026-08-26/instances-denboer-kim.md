# Scan batch: instances/denboer1989 (9) + instances/kim2025 (10)

24 concrete findings + 1 systemic. Key results:

- [R2|A] systemic in 18/19 files (only kim_run.v clean): Kind:/Why:/
  Used-by:/@composes:/@main/@intent/Naming: stacks. Extremes:
  five_card_family.v:52-67 FIVE slots on one comment; :173 leaks audit
  ticket ID "G001" (plan-task token) into a rendered comment;
  five_card_program.v:117 a 188-char Naming: line (batch's worst R1);
  five_card_exec.v 23x defensive "Naming: intentional" markers.
- [R9|B] kim_secrecy.v:30-54 vs denboer_secrecy.v:24-51 — line-for-line
  identical modulo dbP->kimP rename (normalized-diff confirmed) ->
  factor parametric lemma; kim_run.v already shows the correct
  delegating pattern.
- [E1/R9|A] den_boer_profile.v:148-163 vs 302-309 — byte-identical
  theorem statement restated; second proved by exact: first.
- [E1/R9|A] five_card_kim.v:574-583 fc_kim_security_bound restates as
  fresh binders the eps triple its own Section kim_security already
  hoists; proof is exact: kim_spectral_convergence -> delete or move
  into the section.
- [E1|A] five_card_leakage.v:350-357 (+3 repeats) — 4-premise hterm
  shape re-derived locally in 4 proofs -> one parametric lemma.
  five_card_family.v:175-179, kim_input_privacy.v:718-724 (+[R3|A]
  bare H1/H2/H3 leaking into the conclusion type).
- [R9|B] five_card_leakage.v:249-262 — leak_k1 locally re-proves 3
  top-level lemmas from the same file.
- [R10|C] rigidity_kim_instance.v:43-49 — 5 unused Section binders left
  from a retired Reed-Solomon block (header admits it).
- [R2|A] five_card_analysis.v:112-114,200-202 — two pure-tautology alias
  comments (other ~50 are fine).
- R1: 261 >80 lines batch-wide. R5: zero hits (clean batch).
- Reference exemplars: kim_run.v (zero findings), five_card_models.v
  (correct hypothesis sectioning), den_boer_encoding.v.
