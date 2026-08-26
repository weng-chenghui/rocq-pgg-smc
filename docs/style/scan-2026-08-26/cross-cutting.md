# Cross-cutting scan: E3 frequency table + R9 tree-wide duplication

## E3 verdicts
- endpoint 510 uses/56 files, endpoints 167/42, word_eval 232/28:
  NOTATION-worthy. PRIMARY PROPOSAL: package rho as a mathcomp action —
  all three is_action laws are ALREADY PROVED (endpointM = act_morph,
  endpoint1 = identity, endpoint_inj via perm_inj); `Canonical
  rho_action := Action ...` is direct packaging, inheriting orbit,
  'C[s|to] (= the Hreg semiregularity hypothesis repeated 3x in
  pgg_abelian_collapse.v!), astab/astabs, [transitive ...] vocabulary.
  Evidence of demand: pgg_security_demo.v hand-rolls orbit_of/
  is_transitive at nat level; s5x5_pile.v and pgl27_group.v already
  reach for astabs_group (perm_action _) piecemeal.
- word_eval/endpoints: secondary scoped-notation candidates (pgg_scope).
- compute/dealt_hand/start_sheet: BELOW THRESHOLD — counts were inflated
  by the two duplicate files in R9 #1/#2 plus vm_compute tactic hits.
- Notation inventory: pgl27_M/pgl27_Msym non-Local (15/3 files) vs every
  sibling family's per-file Local re-declaration — pick one convention;
  RAAGDesc := GroupDesc (only parsing) shim is an unfinished rename
  (consumers use only the alias) — rename the record, delete the shim;
  dead Reserved Notation "u *d w"/"u \*d w" in smc/smc_interpreter.v
  [vendored]; masksvec/othermasks and "[> ps ]" should be Local/scoped.

## R9 top findings
1. protocol/pgg_correctness.v (87 lines, BUILT) re-derives 6
   pgg_interface.v theorems from scratch (endpointM/1/V/inj/
   starts_uniq/card); imported once, referenced only by a COMMENT.
   Delete (or derive by reference for the paper).
2. protocol/pgg_program.v [orphan] duplicates pgg_interface.v
   pgg_protocol_ops verbatim. Delete.
3. Rigidity cluster (abelian/oc/star/cyclic): the RS-code
   Variables/Hypothesis block restated 4x — while cover_genus0.v
   ALREADY provides the factoring (RSCodeWitness record +
   genus0_covering_witness), unused by all four. Build one witness
   value per family.
4. kim_secrecy.v re-proves denboer_secrecy.v byte-identically (its own
   header admits protocol-independence); alias like kim_trace.v does.
5. s5x5_view_secrecy re-derives both components instead of invoking
   s5_view_secrecy twice (or a generic product-secrecy lemma in
   pgg_leakage_product.v).
6. `mk_aproc (exchange_player PI (@Ordinal N k isT))` repeated 125x
   tree-wide -> mk_player_aprocs helper in card_exchange_pismc.v
   (vm_compute-safe).
7. *_analysis.v facade cluster: interface-conformance boilerplate;
   Module Type/functor would collapse it (lower urgency).
8. Per-player-index lemma quintuplets (denboer_trace etc.): pair the
   #6 helper with one parametric forall-i lemma proved by case+vm_compute.
