# Scan batch: lib/ (2) + smc/ (4, vendored) + manifest/ (3)

38 findings (90 raw, deduped). Key results:

- lib/perm_uniform.v: [E1|A] two premise clusters repeated verbatim
  (injective s/injective v/k<=N across 3 lemmas of Section
  prescribed_set; s_inj/v_inj across 4 of prescribed_value even though
  s,v ARE section variables); [E4|B] freshness premise 6-7x and the
  `let target := [set sigma | sigma s_new == v_new]` conclusion 4x ->
  name fresh_pair / perm_target; [R2|A] 11 Kind:/Why:/Used-by:
  comments, one provably STALE (prescribed0 claims "Used by:
  Sn_k_transitive" but is never called — R10 too); [R10|C]
  collusion_uniform/collusion_zero ("Proposition 4") unreferenced
  tree-wide (collusion_bound re-derives directly).
- lib/proba_entropy_ext.v [vendored, candidate-only]: lemma_3_4/
  lemma_3_5/lemma_3_5' opaque paper-number names (R8|A); Section
  proba_extra un-hoisted binder quadruple (E1); `+ notation non-Local
  without level; bare H/H_* hypothesis names.
- manifest/pgg_analysis_manifest.v: [E3|A] 'I_(pi_T' (mp_PI p)).+1
  seat-ordinal shape 51+ uses -> Local Notation seatT p; [R2|A] @intent:
  on all 17 row Definitions + process citations ("Request 5.3",
  "user-approved 2026-08-13 amendment") standing in for content.
  Zero R1 hits in 2938 lines (most disciplined file).
- manifest/pgg_analysis_client.v: clean (deliberate qualified names =
  R6 exception).
- smc/ [all vendored — fixes may be declined for provenance]:
  * smc_session_types.v: [R10|C] ~200-line "Temp note:" chat-transcript
    block (stale line refs, markdown table in comment) — delete; three
    scratch test Sections in the build; ~500 lines unreferenced
    senv-termination apparatus (isStepDecreasing never HB-registered,
    senv_suffices never defined); [R2|A] proof-strategy narration in 7
    statement comments; [R4|B] "Phase 1 Test"/"Phase 2 preview" section
    names.
  * smc_interpreter.v: [R2|A] rstep_disjoint comment is unfinished
    draft prose ending mid-thought; 15 undocumented declarations;
    [R10|C] ~100-line unreferenced relational-semantics apparatus
    (matches the known divergence vs pinned infotheo).
  * graded_resource.v: header is a roadmap not a description (R4);
    mixin/section pair never wired together (R9); ~85 lines
    forward-looking infra unreferenced (R10).
  * pismc.v: clean (1 long line).
- Cross-file: the comment-tag habit in 5/9 files.
