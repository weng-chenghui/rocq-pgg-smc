# Scan batch: groups/ (7 files; ~570 raw findings, top 40 reported)

- [R9|B] LARGEST IN TREE: pgg_raag_cartier_foata.v:48-655 — the entire
  ~600-line Section foata_infrastructure verbatim-duplicates
  pgg_raag.v:1161-1856 (admitted in its own header) -> delete, import.
- FALSE DOC CLAIMS [R2|A]: ~20 "Used by:" slots provably false across
  free_group_ball (9), pgg_raag_clique (6), pgg_weval_inj (5);
  pgg_raag_clique:1231-1247 says "we state this as an axiom" two lines
  before "proven in ..." (misleads trust-boundary readers);
  pgg_raag_path:19 header names a lemma that does not exist;
  pgg_cycle.v: header asserts order/relations over ZERO Lemmas (E5|B),
  and claims a downstream pipeline with zero tree references.
- DOMAIN HONESTY [R2|A]: pgg_raag_path header: built group is S_(m+2),
  not the RAAG presentation claimed; "iff" only proved one way.
- [E3|A]: pgg_raag.v nat-level adjacent swap spelled 12x (add nswap);
  cartier_foata swap-word 11x + a 7-line swap-chain proposition
  verbatim 7x (add swap_at/swap_chain); clique Pascal-sum hand-written
  20+x with bigop imported and unused; weval_inj: ONE operation spelled
  4 ways (file's own comment calls it a group action);
  @Ordinal 5 k isT 4x here, 349x tree-wide -> notation/inord.
- STRUCTURE [R4|A]: pgg_raag_clique.v zero Sections in 1393 lines;
  pgg_raag.v zero Notation/Implicit Types/Local in 2442 lines.
- [R8|A]: raag_Hcomm — banned H-prefix as EXPORTED HB mixin field API
  (-> raag_sigmas_comm); path_Hcomm sibling; sphere_size/ball_size
  misuse mathcomp `size` for cardinality; cycle_r/cycle_s squat on
  fingroup's cycle_ namespace (cycle_s isn't even a cycle);
  n_traces_natB wrong "B" suffix; cta_*/sp_* opaque exports.
- [R9|A]: clique spos_*/sneg_* 7 mirror pairs (~90 lines) -> pred-nat
  parameter; cartier_foata: same 4-line induction pasted 12x in one
  lemma; weval_inj A_4 instance duplicates pgg_oc_param's own stated
  special case; free_group_ball re-proves mathcomp predn_exp.
- [E1|A]: two premise clusters repeated verbatim across 4 lemmas each
  in pgg_raag.v; unused Hypothesis leaking into ball_size_ge1's
  signature; the Ordinal-proof-term issue (see groups-pgg_raag_path.md).
- [R10|C]: ~45 lines commented-out monologue in pgg_raag.v; cartier_
  foata Section whose Variables no declaration uses; free_group_ball
  `reduced` (the object the file is named for) has zero uses.
- Verdicts: cartier_foata = the mathematical center (genuine sign-
  reversing involution, axiom-free) with its core 3 objects
  uncommented; pgg_raag = hub, highest finding density; weval_inj =
  cleanest proof scripts.

Sub-report with full per-line detail for pgg_raag_path.v:
groups-pgg_raag_path.md (76 findings).
