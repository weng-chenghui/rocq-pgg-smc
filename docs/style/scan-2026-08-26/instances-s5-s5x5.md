# Scan batch: instances/s5 (10) + instances/s5x5 (11)

~55 discrete findings. Key results:

- HEADLINE [R9|A]: duplication has two layers, and the bigger is
  INTRA-FILE pile1/pile2 doubling inside s5x5:
  * s5x5_mixing.v — entire lazy-Rayleigh derivation mirrored ~140 lines
    (s5_lazy_tnth_0..7 vs '_0..7, invol/count/Q_eq/TV_bound pairs);
    the batch's single worst file.
  * s5x5_models.v — ~20 pile1/pile2 lemma pairs spanning 232-1397; the
    963-line excess over s5_models.v is duplication, not content.
  * s5x5_exec.v — ~23 pairs (map_val/stab/idx_inj/layoutE/embedK...).
  * Fix shape: Section pile_generic parametrized by embedding/shift,
    instantiated at pile1 (id) and pile2 (shift-by-5).
- [R9|A] cross-file: s5_run.v vs s5x5_run.v ~90% identical (dealer_run/
  saprocs/procs/terminates modulo 5->10, 150->300); s5_exec.v vs
  s5x5_exec.v 7-lemma block byte-identical modulo carrier;
  s5{x5}_secrecy view lemmas = per-component helper conjoined by hand.
- [R2|A] systemic (~500 tag occurrences, 15/21 files): Kind:47 in
  s5x5_mixing, @intent: 76 in s5x5_analysis. WORST INSTANCE:
  s5_models.v:348-355 — process narration "Amended work package A
  (user-approved 2026-08-13)... recorded in the completion response"
  in the file body. s5x5_pile.v:62-71 — "no caller committed yet"
  status marker + naming apologia; its pile1 sibling lemma has NO
  comment at all.
- [R2|A/B] axioms: s5_mixing.v:188-195 s5_rayleigh_Q2_R — computational
  certificate cited informally 3 paragraphs away; make it a one-line
  pointer with fixed hash above the Axiom. rigidity_s5_instance.v:268
  s5_group_order_eq — "Kind: axiom." only, no citation (contrast the
  same file's exemplary Edge (1978) Bring's-curve citation).
- [E1|A] s5_mixing.v — (R : realType) re-bound in 8/15 lemmas + the
  R/L/s triple verbatim in 2; s5_models.v shows the correct Section
  pattern. [E1|B] rigidity_s5_instance HG_s5 premise hoisted twice in
  two sections.
- [R10|B] BOTH rigidity files carry an orphaned
  *_rigidity_cryptographically_secure section (s5:354-398,
  s5x5:601-640), repo-wide unreferenced, absent from the header
  inventory — delete or wire in as the headline result.
- [R3|B/C] bare H for load-bearing bounds (s5x5_exec.v:528,536);
  rs1/rs2 opaque names (s5x5_trace.v:215); ~25 Hxxx subject-names.
- R1: s5x5_mixing.v 68 and s5x5_trace.v 63 over-80 lines (worst).
- vm_compute per-index lemmas (s5_trace abs_p0..4 / s5x5 ..p9):
  deliberate, documented in-file; Ltac helper suggested only.
- Clean models: s5_secrecy.v/s5x5_secrecy.v style; s5x5_run.v proof
  factoring (ironically better than s5's).
