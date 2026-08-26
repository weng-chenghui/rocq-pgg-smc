# Scan batch: instances/pgl27/ (15 files, 6138 lines)

16 findings; family unusually clean, severity concentrated in 2 files.

- [E1|A] pgl27_profile_privacy.v:109-123 & 267-279 — two negated-universal
  lemmas with 8-9 premises over 13-15 lines, premises verbatim-shared ->
  Section hoist or a named profile_view_indep_statement Definition.
- [E1|A] pgl27_mixing.v:850-862 mixing_bound_gen — 4 binders + 6 anonymous
  hypothesis arrows over 12 lines, single call site -> dedicated Section.
- [R2|A] pgl27_mixing.v — 76/76 Local Lemmas without any statement comment
  (siblings document everything); add fact+position one-liners at least to
  the ~15 bridge lemmas.
- [R9|B] pow2_split (2^-40 + 2^-40 = 2^-39) byte-identical Let in
  pgl27_word_privacy.v:160 and pgl27_models.v:398 -> promote to shared
  arithmetic helper.
- [R9|B] pgl27_trace.v:94-244 — 16 per-index vm_compute lemmas + the 8-way
  case split copy-pasted 3x (330-347, 492-507, 651-666); intentional for
  vm_compute per file's own comment, but the same shape likely recurs in
  s5/s5x5 traces -> cross-cutting agent to judge a generator/congruence
  factoring.
- [R4|B] pgl27_{secrecy,word_privacy,trace,profile_privacy}.v — headers
  missing the "Definitions:" list the other 11 siblings carry.
- [R1|B] ~22 >80 lines (worst: pgl27_trace.v:34 import at 96 chars).
- [R5|C] pgl27_mixing.v:767 move=> H; exact: H -> by [].
- R10: zero dead code found family-wide (leakage_census clean).
- Clean exemplars: pgl27_orbit.v (best documented), pgl27_scheme.v,
  pgl27_exec.v.
