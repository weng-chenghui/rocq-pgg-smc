# R3 revised: H-prefixed hypothesis cleanup — 2026-09-03

Supersedes the one-line R3 entry in CONSOLIDATED.md. Basis: full-tree
inventory (140 `Hypothesis Hxxx` declarations + 3 exported API names +
~40 statement-level binders), and the ruling that MathComp style is the
criterion (reference.md §14: meaningful names, never `H`/`H'`; `H`
collides with the subgroup-variable convention; measured against the
installed mathcomp tree, bare/numbered-H intros are residue, not idiom).

Naming rules applied throughout:
- Governing principle (user ruling 2026-09-03): a peer reviewer must be
  able to read the CONCEPT off the name. When the hypothesis embodies a
  named domain concept, name the concept (`lfree` = "the group looks
  free up to L", pgg_weval_inj.v:15's own gloss) — this outranks
  mechanically transliterating the statement (`weval_inj_L`).
  Transliteration remains correct only for bookkeeping facts with no
  concept beyond the inequality itself (`r_gt1`, `le_kn`, `card_A`).
- Stem already meaningful (`Hdeck_uniq`, `Hoffdiag`): drop the `H`,
  attach the subject where needed (`deck_ok_uniq`, `Q_diag`).
- Stem opaque (`Hr`, `Hn`, `HC`, `H1`): name the content
  (`r_gt1`, `card_A`, `card_C_gt0`, `inv5_gt0`).
- One word per concept across files: the pointwise-evaluation
  injectivity hypothesis appears in three files under three names
  (`Hregular`, `Hinj_s`, `Hpe`) — all become `pe_inj`.
- In-repo models to align with: pgg_mixing.v's `Q_ge0`/`Q_row_sum`/
  `Q_col_sum`/`Q_symm`; pgg_collusion_bound.v:314's `TN`.
- Defining equations take mathcomp's `def*`/`*E` shape (`defN`,
  `gens_natE`); cancellation hypotheses take the `K` suffix (`fK`).

Verification protocol, per commit:
1. scripts/statement_surface.py before/after — the diff must be exactly
   the authorized rename set (name-column and statement-text changes for
   the listed identifiers; ctxhash changes only for sections whose
   Hypothesis was renamed).
2. Per-file collision check before sed: the target name must not already
   exist in the file.
3. Comment sweep in the same commit: every comment/header line naming a
   renamed identifier is updated (e.g. pgg_raag.v:883/1027 narrate
   raag_Hcomm; pgg_raag_path.v:34/135 narrate path_Hcomm).
4. Full `make -j8` EXIT=0 judged from a captured log, then a fixpoint
   pass compiling 0 files.
5. Grep each old identifier at word boundary in the edited files → 0.
6. Stage named files only; one commit per action item (A3 per
   directory).

## A1 — exported API names (1 commit, first)

- `raag_Hcomm` mixin field (groups/pgg_raag.v:895/915, alias :948)
  → `raag_sigmas_comm`, aligning with raag_comm_sym/raag_comm_irrefl.
- `path_Hcomm` / `path_Hcomm_sigmas` (groups/pgg_raag_path.v:182/206)
  → `path_gen_comm` / `path_gen_comm_sigmas`, aligning with
  path_gen_tuple/path_gen_inj_sigmas.
- `Hcard_remaining` Lemma (security/pgg_collusion_bound.v:459)
  → `card_remaining` (mathcomp `card_*` family).

## A2 — statement-level binders (2 commits)

A2a, the `Hw0` family: `(Hw0 : w0 \in pgg_G _)` → `Gw0` (mathcomp
membership naming, `Gx : x \in G`). 32 sites over 10 files: s5_exec,
s5_run, rigidity_s5_instance, pgl27_trace, pgl27_run, pgl27_exec,
rigidity_oc_instance, five_card_exec, s5x5_exec, s5x5_run.

A2b, the rest:
- kim_input_privacy.v:750–751 `H1`/`H2`/`H3` → `inv5_gt0` /
  `neg4inv5_lt0` / `gap_gt0` (H1, H2 appear in the conclusion term
  `@kim_inputs R 0 H1 H2`, so the exported statement text changes).
- s5x5_exec.v:542 `(H : pgg_rho … < 5)` → `rho_lt5`; :550
  `(H : pgg_rho … - 5 < 5)` → `rho_sub_lt5`.
- transitivity_privacy.v:140 `bij_uniform (H : #|A| = n.+1)` → `card_A`.
- pgg_sharing_framework.v:220/229 `cast_tuple (H : n = m)` → `eq_nm`
  (castmx's `eq_mn` precedent).
- pgg_execution_plug.v:312 inner `forall Hsz : …` → `sz_ep`.

## A3 — the 140 Hypothesis declarations (per-directory commits: security, groups, reconstruct, protocol, instances)

Order relations → content names:
- `Hr : 1 < r` → `r_gt1`: pgg_security.v:137, free_group_ball.v:238.
- `Hr : 0 < r` → `r_gt0`: free_group_ball.v:59, 162.
- `Hd2 : 1 < d` → `d_gt1`: coord_perm_compatible.v:142, 211;
  massey.v:93.
- `Hk`/`Hkn`/`Hkg`/`Hkgn` → `k_gt0`/`le_kn`/`lt_gk`/`lt_kgn`:
  ag_massey_bridge.v:43–46, ag_multiplicative.v:177–180,
  hyperelliptic_code.v:410–413, ag_code.v:96–97; suffixed variants
  keep their suffix (ag_multiplicative.v:196–200 `k2_gt0` etc.;
  cover_genus1.v:133–136, 356–359 `k_g_gt0`/`…_ec`;
  cover_genus2.v:158–161 `…_g2`).
- `Hparam*` → `low_redundancy` (+ `_g`/`_ec`/`_g2`):
  ag_massey_bridge.v:83, cover_genus1.v:165, 389, cover_genus2.v:191.
  Concept: `n <= k + g + 1` is `n - k <= g + 1`, the low-redundancy
  regime in which the AG-Massey privacy/recovery threshold gap closes
  to `2 * g` (the file's own gloss at ag_massey_bridge.v:81-82 derives
  exactly this). Keep a one-line gloss comment at each declaration.
- `Hdeg_f_le*` → `deg_f_le` (+ suffix): hyperelliptic_code.v:172,
  cover_genus1.v:141, 365, cover_genus2.v:167.
- `HT : 0 < T'` → `T'_gt0` (pgg_assignment.v:217); `HT : 1 < T'` →
  `T'_gt1` (pgg_threshold.v:148); `HT : T <= N` → `TN`
  (pgg_interface.v:568, matching collusion_bound's existing `TN`).
- `HCleB` → `le_card_CB` (collusion_bound:1096); `HPQ` → `PQ_close`
  (:1314; concept: P and Q are delta-close in variation distance);
  `Hbound` → `H_min_floor` (entropy_security_demo:259; concept: H_min
  is a floor on every per-seat entropy).

Cardinalities:
- `HC : 0 < #|C|` → `card_C_gt0`: collusion_bound:153, 827, 991,
  1092; entropy_security:160, 194; transitivity_privacy:267.
- `Hn : #|A| = n.+1` → `card_A` (uniform_security:53,
  collusion_bound:152); `Hn : #|B| = n.+1` → `card_B` (:994, 1095);
  `Hbal : #|C| = n.+1` → `card_C` (:995).
- `HG : 0 < #|G|` → `card_G_gt0` (transitivity_privacy:484, 581,
  749); `HG : 1 < #|G|` → `card_G_gt1` (cover_genus0:65,
  cover_genus1:57, 267, cover_genus2:64).
- `HG_ncycle`/`HG_s5`/`HG_s5_crypto`/`HG_oc`/`HG_abel` →
  `card_G_<inst>_gt1`: rigidity_cyclic:129, rigidity_s5:375, 427,
  rigidity_oc:276, rigidity_abelian:166, pgg_landscape_demo:195.
- `HrhoG_pos` → `card_rhoG_gt0` (uniform_security:110);
  `Hremaining_pos` → `card_remaining_gt0` (collusion_bound:442);
  `Hpop` → `card_class_decks_gt0` (transitivity_privacy:765).

Defining equations:
- `HN : N = #|F|` → `defN`: ag_massey_bridge:98, rs_massey_bridge:203,
  cover_genus0:123; rigidity's `(pgg_N' R).+1 = #|GF m' primeq|` →
  `defN`: rigidity_cyclic:140, rigidity_oc:287, rigidity_abelian:177,
  pgg_landscape_demo:194.
- `HN_g`/`HN_ec`/`HN_g2` → `defN_g`/`defN_ec`/`defN_g2`
  (cover_genus1:106, 324, cover_genus2:126); `Hn_ec`/`Hn_g2` →
  `def_n_ec`/`def_n_g2` (cover_genus1:328, cover_genus2:130).
- `Hm_eq` → `def_m_deg`, `Hm_dual_eq` → `def_m_deg_dual`
  (hyperelliptic_code:394, 420).
- `Hgens` → `gens_natE` (pgg_weval_inj:151); `Hcomm_nat` →
  `comm_natE` (pgg_raag:1904).
- `HT`/`HT_eq : ts_T' _ = pi_T' _` → `eq_T'`:
  pgg_covering_correctness:47, pgg_sharing_framework:253,
  ag_multiplicative:218. NOTE: ag_multiplicative:218's statement text
  references `Hk Hkn Hkgn` — rename in the same commit as that file's
  quartet.
- `Hsat` → `Lstar_sat` (entropy_security_demo:47).

Cancellation pairs (K suffix):
- rs_massey_bridge:40–41 `Hgf`/`Hfg` → `gK`/`fK`;
  coord_perm_compatible:286–287 `Hgi`/`Hfg` → `g_invK`/`fK`.

Injectivity / regularity / transitivity:
- `Hlfree`/`Hweval : @weval_inj M L` → `lfree` (7 sites): the concept
  is "the group looks free up to word length L" (pgg_weval_inj.v:15's
  own gloss). collusion_bound:625, 890, 1197, 1259;
  entropy_security:494; pgg_weval_inj:246; entropy_security_demo:89.
- `Hregular` (uniform_security:113), `Hinj_s` (collusion_bound:897),
  `Hpe` (entropy_security_demo:90) → `pe_inj`, one word for one
  concept: pointwise evaluation separates cuts (demo's comment already
  calls it pe_inj; uniform's "Regularity" gloss stays as the comment).
- `Htrans` → `rhoG_trans` (uniform_security:119);
  `Htrans : ntransitive …` → `rhoG_ntrans` (transitivity_privacy:302,
  578, 746).
- `Hreg` → `endpoint_free` (abelian_collapse:45, 78; the statement is
  freeness — one endpoint agreement forces equality of group
  elements — while the comment's "regular = free + transitive" names
  the pair, whose transitive half lives elsewhere); `Habel` → `abelG`
  (:75).
- `Hfij` → `neq_fij` (word_analysis:394); `Hfix0` → `sigma_fix0`
  (coord_perm_compatible:61, 145).

Q-matrix family (align with pgg_mixing.v):
- schreier_weighted:375–377 `Hdiag`/`Hoffdiag`/`Hcol` →
  `Q_diag`/`Q_offdiag`/`Q_col_sum`.

Drop-the-H:
- transitivity_privacy:362/752 `Hdeck_uniq` → `deck_ok_uniq`;
  363/753 `Hinv` → `orbit_class_inv`; 365/755 `Hdeck_stable` →
  `deck_ok_stable`; 367 `Hpopulated` → `orbit_class_onto`.
- pgg_execution_plug:303 `Hterm` → `exec_term`; 307 `Hep` →
  `endpoint_eq`; 312 `Hrecon` → `static_recovery` (the comment's own
  phrase); pgg_sample_adapter:227 `Hep` → `endpoint_eq`.
- s5x5_mixing:566 `HfdU` → `fdU_two_valued`; collusion_bound:1315
  `Hideal` → `ideal_eq`; massey:401 `HMDS` → `mdsC`.

## A4 — explicitly out of scope

- pgg_sharing_framework.v:276 `(H : {group gT})`: `H` IS the mathcomp
  subgroup convention here; keep.
- Proof-script-internal names (`have H1`, `/andP[H1 _]`, ~27 sites in
  s5/s5x5 alone): R5 territory. The right fix there is usually
  restructuring the intro pattern so the name disappears, not
  renaming; kept out so this batch stays verifiable as names-only.
- Vendored smc/ quartet, lib/proba_entropy_ext.v, orphan
  rigidity_star_instance.v: untouched.

## Open name choices (user veto before execution)

Resolved 2026-09-03 by the concept-legibility ruling: `lfree` (not
`weval_inj_L`); `path_gen_comm` (reads "path generators commute", the
RAAG relation, vs `path_genC` whose C suffix belongs on commuted
operations and doubles as set complement); `Gw0` (membership is the
whole concept; mathcomp's attested `Ax : x \in A` juxtaposition).

The remaining judgment calls were confirmed by the user 2026-09-03:
`low_redundancy` for `Hparam*`, and `endpoint_free` for `Hreg`
(`endpoint` verified as the covering-theory term — the endpoint of the
lifted path defining monodromy, per pgg_interface.v:18's gloss —
not a software borrowing). No open choices remain.
