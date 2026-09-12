# Post-legacy architecture: the chain from a piSMC program to the security analysis

Date: 2026-09-12. Read-only analysis. No `.v` file was modified.

## Scope

This note describes the repository as it will stand after every file outside the
"kept" set is moved to `legacy/`. The kept set is 91 `.v` files: the vendored
piSMC layer (`smc/`), two library files (`lib/`), the protocol layer
(`protocol/`), four `groups/` files, thirteen `reconstruct/` files, fourteen
`security/` files, `manifest/pgg_analysis_status.v`, and all files in the four
instance directories `instances/denboer1989` (9), `instances/kim2025` (10),
`instances/pgl27` (15), `instances/s5` (10).

Every import edge below was extracted from `.Makefile.rocq.d` and restricted to
the kept set, so the diagram is the real `.vo` dependency graph, not a design
intention. Every identifier carries a `file:line` citation.

Two facts frame everything that follows.

**There is exactly one `isMonodromyRepr` HB instance in the whole kept set**, at
`protocol/pgg_interface.v:523-524`, inside the generic `Gen_PGGTypes` template.
No instance directory declares one.

**There are three `Axiom`s and one `Parameter` in the kept set**, all confined to
the S5 instance and the curve-realisation hook:
`reconstruct/curve_realisation.v:69` (`Parameter realised_by_curve`),
`instances/s5/rigidity_s5_instance.v:277` (`s5_group_order_eq`),
`instances/s5/rigidity_s5_instance.v:309` (`s5_brings_covering_realised`),
`instances/s5/s5_mixing.v:186` (`s5_rayleigh_Q2_R`).
There is no `Admitted`, no `Abort` and no `admit` anywhere in the kept set.

---

## (a) Layer diagram of the kept files

Arrows point from a file to the files it requires. Only kept-set edges are shown.

```
LAYER 0 -- vendored piSMC (smc/, from the infotheo fork @ b5a899f7)

    smc_interpreter.v          graded_resource.v
         |                          |
         +------------+-------------+
                      v
              smc_session_types.v  ------> pismc.v
                      |                       |
                      +-----------+-----------+
                                  |
LAYER 1 -- the group interface    |          lib/perm_uniform.v
                                  |          lib/proba_entropy_ext.v
    protocol/pgg_interface.v      |               (leaves; no kept deps)
      * Record PGGTypes           |
      * HB isMonodromyRepr        |
      * HB hasGenerators          |
      * Record PGGInterface       |
      * Definition Gen_PGGTypes   |     <-- THE plug-in point
            |                     |
            +----> groups/pgg_weval_inj.v
            |            |
            |            +----> groups/pgg_raag.v ----> groups/pgg_raag_clique.v
            |                        |                          |
            |                        +----> groups/pgg_raag_path.v <--+
            |
            +----> reconstruct/pgg_sum_mod.v
            |            v
            |      reconstruct/pgg_sharing_framework.v   (Record ThresholdScheme)
            |            v
            |      reconstruct/covering_scheme.v         (ReconPlug, CoveringScheme)
            |            |          |
            |            |          +----> reconstruct/curve_realisation.v
            |            |          +----> reconstruct/cover_tradeoff.v <-- pgl_bound.v
            |            |          +----> reconstruct/input_encoding.v
            |            |          +----> reconstruct/transitivity_privacy.v
            |            v
            +----> security/pgg_collusion_bound.v
                         |         |          |
                         |         |          +----> security/pgg_weighted_words.v
                         |         +----> security/pgg_schreier.v
                         |                    |         |
                         |                    |         +--> security/pgg_mixing.v
                         |                    +--> security/pgg_schreier_weighted.v
                         v
                   reconstruct/algebraic_rigidity.v
                   (SecurityExact / SecurityAsymptotic / ShuffleMarginalBound /
                    ShuffleCertificateBundle / ThresholdWitness / AlgebraicRigidity)
                         ^
                         |  security/pgg_security_solver.v (leaf: SecurityParams, GroupDesc)
                         |
LAYER 2 -- the shared piSMC program and its execution stack
                         |
    protocol/pgg_session_types.v  (typed Reveal/Deal/Announce/Observe wrappers)
                         v
    protocol/card_exchange_pismc.v
      * exchange_dealer :222   exchange_player :240   exchange_verifier :257
                         v
    protocol/pgg_input_commitment.v   (pgg_commit :63, pgg_commit_prologue,
                         |             exchange_dealer_with_commit :114)
                         v
    protocol/pgg_run.v   (dealer_with_input_encoding :47, endpoints_of_trace :65)
                         v
    protocol/pgg_monodromy_profile.v   (Record MonodromyProfile :54;
                         |              run_party :86, run_verifier :90, run_recover)
                         v
    protocol/pgg_execution_plug.v      (Record ExecutionPlug :58;
                         |              dealer_secret_plug :94, committed_input_plug :109;
                         |              exec_run :179, exec_endpoints :184, exec_decode :269,
                         |              exec_run_recovers :329, exec_run_correct :377)
                         v
    protocol/pgg_observed_execution.v  (Module OE, Record ObservedExecution :90;
                         |              oe_run_recovers :158, oe_run_correct :178)
                         v
    security/pgg_sample_adapter.v      (Record SampleAdapter :111; sa_seat_view,
                         |              sa_coalition_view, sa_cut_dist, sa_*_dist)
                         v
    manifest/pgg_analysis_status.v     (CompletionLevel, TransferStatus, PggAxiom,
                                        Record AnalysisModelFamily :100)

LAYER 3 -- the leakage / secrecy tail (independent of the program layer)

    security/pgg_leakage_witness.v   (Record LeakageWitness :31)
        |         |          |
        |         |          +----> security/pgg_trace_secrecy.v
        |         +----> security/pgg_cyclic_cut_leakage.v  (Record CyclicCutData :30)
        |                     |
        +----> security/pgg_randomized_sharing.v (Record RandomizedSharing :39)
                     |               |
                     |               +----> security/pgg_sharing_mechanism.v
                     |                       (Variant SharingMechanism, mechanism_leakage :46)
                     +----> security/pgg_canonical_sharing.v <-- security/pgg_fdist_rV_indep.v
                             (unif_randomized_sharing :106)

LAYER 4 -- the four instances

  FIVE-CARD FAMILY (den Boer 1989 + Kim 2025) -- one program, two dealing biases
    instances/denboer1989/five_card_group.v  <-- reconstruct/pgg_deck_pairing.v
        v
    instances/denboer1989/five_card_program.v
        v
    instances/denboer1989/five_card_scheme_I5.v  (fcI_scheme :197)
        v
    instances/kim2025/five_card_kim.v            (FiveCardKim_M :135)
        v
    instances/kim2025/five_card_family.v         (FiveCardKim_PI :138, five_card_plug :147,
        |                                         five_card_profile :160)
        +--> instances/denboer1989/den_boer_profile.v (den_boer_profile := five_card_profile :67)
        +--> instances/denboer1989/five_card_leakage.v
        +--> instances/denboer1989/den_boer_encoding.v (den_boer_encoding :101)
        +--> instances/denboer1989/den_boer_run.v      (den_boer_procs :142)
        +--> instances/denboer1989/denboer_secrecy.v   (denboer_ccd :35, denboer_mechanism :38)
        +--> instances/denboer1989/denboer_trace.v
        +--> instances/kim2025/kim_run.v  kim_secrecy.v  kim_trace.v   (alias shells)
        +--> instances/kim2025/kim_input_privacy.v      (kim_input_private :716)
        v
    instances/kim2025/five_card_exec.v   (five_card_exec_plug :144, five_card_observed :422)
        v
    instances/kim2025/five_card_models.v (kim samples + three AnalysisModelFamily values)
        v
    instances/kim2025/five_card_analysis.v  (Module FiveCardAnalysis :98)
    instances/kim2025/rigidity_kim_instance.v  (leaf; only kim_complexity :59)

  PGL(2,7)
    instances/pgl27/pgl27_group.v  <-- reconstruct/pgl_bound.v      (Notation pgl27_M :97)
        v
    instances/pgl27/pgl27_orbit.v
        v
    instances/pgl27/pgl27_scheme.v  <-- reconstruct/transitivity_privacy.v
        |                               (orbit_scheme :79, pgl27_plug :95)
        v
    instances/pgl27/pgl27_profile.v (pgl27_PI :54, pgl27_marginal_bound :101,
        |                            pgl27_certificate_bundle :108, pgl27_profile :117)
        +--> pgl27_run.v :66,:73,:80   +--> pgl27_secrecy.v   +--> pgl27_mixing.v
        +--> pgl27_recovery.v --> pgl27_leakage_census.v (leaf)
        +--> pgl27_profile_privacy.v (leaf; a second, constant-deck MonodromyProfile :211)
        v
    instances/pgl27/pgl27_trace.v  ---> pgl27_word_privacy.v
        v
    instances/pgl27/pgl27_exec.v   (pgl27_exec_plug :106, pgl27_observed :304,
        |                           pgl27_sample :329, pgl27_word_sample :438)
        v
    instances/pgl27/pgl27_models.v ---> instances/pgl27/pgl27_analysis.v (Module PGL27Analysis :86)

  S5 (path RAAG on 5 card positions)
    groups/pgg_raag_path.v  (path_gen_tuple :75, HB Path_isRAAG :280)
        v
    instances/s5/pgg_raag_s5.v      (s5_weval_inj1 :62; nat-level oracle)
        v
    instances/s5/s5_mixing.v        (AXIOM s5_rayleigh_Q2_R :186;
        |                            s5_spectral_convergence_proved :200)
        v
    instances/s5/rigidity_s5_instance.v  <-- cover_tradeoff.v, curve_realisation.v
        |   (AXIOM s5_group_order_eq :277, AXIOM s5_brings_covering_realised :309,
        |    s5_brings_covering :349, s5_covering :439, s5_rigidity :461)
        v
    instances/s5/s5_profile.v  (s5_PI :38, s5_plug :47 = cs_plug s5_brings_covering,
        |                       s5_profile :55)
        +--> instances/s5/s5_run.v :39,:59,:66,:72
        +--> instances/s5/s5_secrecy.v (s5_view_secrecy :35, ..._concrete :49)
        v
    instances/s5/s5_trace.v  (s5_rs :115, s5_trace_secrecy :171)
        v
    instances/s5/s5_exec.v   (s5_exec_plug :136, s5_observed :289,
        |                     s5_rand_exec_plug :616, s5_rand_observed :758)
        v
    instances/s5/s5_models.v ---> instances/s5/s5_analysis.v (Module S5Analysis :74)

LAYER 5 -- the manifest

    manifest/pgg_analysis_manifest.v  (to be trimmed) requires the three facades
    FiveCardAnalysis, PGL27Analysis, S5Analysis and defines the seven surviving
    rows: pgl27_row_exact :1171, pgl27_row_word :1182, five_card_row_uniform :1193,
    five_card_row_biased :1203, five_card_row_repeated :1213, s5_row_det :1223,
    s5_row_rand :1233, s5_row_word (after :1246).
```

Three structural points the diagram makes that prose easily hides.

1. **den Boer has no group, no interface, no plug, no profile, no execution plug
   and no observed execution of its own.** All six live in `instances/kim2025/`
   and `instances/denboer1989/` imports them. `den_boer_profile.v:67` is literally
   `Definition den_boer_profile : MonodromyProfile := five_card_profile.` The
   directory names invert the dependency: the 2025 file is the base, the 1989
   file the specialisation at bias `eps = 0`.

2. **`reconstruct/algebraic_rigidity.v` sits *below* the program layer**, not
   above it: `protocol/card_exchange_pismc.v` requires it. So the genus/threshold
   vocabulary is a prerequisite of the shared piSMC program file even for
   instances that never build a `CoveringScheme`.

3. **The leakage tail (Layer 3) never touches the program layer.** `LeakageWitness`,
   `CyclicCutData`, `RandomizedSharing` and `SharingMechanism` know nothing about
   `MonodromyProfile`, `ExecutionPlug` or the interpreter. The instances join the
   two halves by proving a random-variable identity
   (`five_card_exec.v:544`, `s5_models.v:161`, `pgl27_trace.v:323`) and then
   applying `security/pgg_trace_secrecy.v:41 trace_secrecy_of_view`.

---

## (b) Every `Record` in the kept files

`R` denotes a `realType` section variable, `M` a `MonodromyReprType`.

| File:line | Record | Fields (name : type, abbreviated) | Consumed by |
|---|---|---|---|
| `smc/smc_session_types.v:1259` | `aproc_ctx` | `ctx_procs : seq (proc data)`; `ctx_trace : seq data`; `ctx_idx : nat` | `aproc_step` (same file); interpreter internals only. Not used by any protocol or instance file. |
| `protocol/pgg_interface.v:38` | `PGGTypes` (`MkPGG`) | `pgg_gT : finGroupType`; `pgg_N' : nat`; `pgg_G : {group pgg_gT}` | Built once, generically, by `Gen_PGGTypes` (`:521`). Carrier of the HB mixins `isMonodromyRepr` (`:55`), `hasGenerators` (`:63`), `isRAAG0` (`groups/pgg_raag.v:892`). |
| `protocol/pgg_interface.v:360` | `PGGInterface M` (`MkPGGI`) | `pi_T' : nat`; `pi_starts : pi_T'.+1.-tuple 'I_(pgg_N' M).+1`; `pi_starts_uniq : uniq pi_starts` | `start_sheet`, `dealt_hand`, `compute`, `endpoints` (same file); every `exchange_*` program; field `mp_PI` of `MonodromyProfile`. Instantiated as `FiveCardKim_PI` (`five_card_family.v:138`), `pgl27_PI` (`pgl27_profile.v:54`), `s5_PI` (`s5_profile.v:38`). |
| `protocol/pgg_monodromy_profile.v:54` | `MonodromyProfile` (`MkMonodromyProfile`) | `mp_M : MonodromyReprWithGeneratorType`; `mp_secretT : Type`; `mp_PI : PGGInterface mp_M`; `mp_plug : ReconPlug mp_M mp_secretT` | `run_party :86`, `run_verifier :90`, `run_recover :95`, `profile_k :101`, `profile_private :106`, `profile_recon_encode :112`; index of `ExecutionPlug`, `SampleAdapter`; field `oe_profile`. Instantiated 4x in the kept set: `five_card_profile` (`five_card_family.v:160`), `pgl27_profile` (`pgl27_profile.v:117`), `constant_deck_profile` (`pgl27_profile_privacy.v:211`), `s5_profile` (`s5_profile.v:55`). |
| `protocol/pgg_execution_plug.v:58` | `ExecutionPlug mp` (`MkExecutionPlug`) | `ep_inputT : Type`; `ep_players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp))`; `ep_players : seq 'I_...`; `ep_playersE : ep_players = enum ...`; `ep_content : ep_inputT -> seq 'I_N -> ('I_N -> 'I_N)`; `ep_input_procs : ep_inputT -> seq (aproc ...)`; `ep_fuel : nat` | `exec_run :179`, `exec_endpoints :184`, `exec_decode :269`, `exec_static_endpoints :277`, `exec_run_recovers :329`, `exec_run_correct :377`; field `oe_execution`; index of `SampleAdapter`. Never built by `MkExecutionPlug` directly: always via `dealer_secret_plug :94` or `committed_input_plug :109`. |
| `protocol/pgg_observed_execution.v:90` | `OE.ObservedExecution` (`MkObservedExecution`) | `oe_profile : MonodromyProfile`; `oe_execution : ExecutionPlug oe_profile`; `oe_P_idx : nat`; `oe_content_obs : ep_inputT -> gT * 'I_N -> 'I_N`; `oe_expected : ep_inputT -> mp_secretT`; `oe_terminates`; `oe_endpoints`; `oe_static_recon` | `oe_endpoints_size :146`, `oe_run_recovers :158`, `oe_run_correct :178`, `oe_seat_endpointE :203`, `oe_coalition_endpointsE :218`, the five `oe_*_trace :244-280`; index of `AnalysisModelFamily`. Instantiated: `five_card_observed` (`five_card_exec.v:422`), `pgl27_observed` (`pgl27_exec.v:304`), `s5_observed` (`s5_exec.v:289`), `s5_rand_observed` (`s5_exec.v:758`). |
| `reconstruct/pgg_sharing_framework.v:47` | `ThresholdScheme secretT shareT` (`MkThresholdScheme`) | `ts_T' : nat`; `ts_k' : nat`; `ts_valid : secretT -> tuple -> Prop`; `ts_recon : tuple -> secretT`; `ts_encode : secretT -> tuple`; `ts_correct`; `ts_private`; `ts_encode_valid` | `ts_recon_encode :78`, `ts_T :86`, `ts_k :92`, `ts_recon_perm_invariant :114`, `sum_mod_scheme` (`:128-211`), `pgg_recon_endpoints` (`:238-304`); field `rp_scheme`. Instantiated: `fcI_scheme` (`five_card_scheme_I5.v:197`, 5 shares, `ts_k' = 1`), `orbit_scheme` (`pgl27_scheme.v:79`, 8 shares, `ts_k' = 3`), `constant_deck_scheme` (`pgl27_profile_privacy.v:180`), `s5_scheme := sum_mod_scheme 3 4` (`s5_run.v:39`, 5 shares, `ts_k' = 4`). |
| `reconstruct/covering_scheme.v:75` | `CoveringData M` (`MkCoveringData`) | `cd_base_genus`, `cd_n_branch`, `cd_total_ramif`, `cd_genus : nat`; `cd_ramif_ge_n_branch`; `cd_hurwitz` (Riemann-Hurwitz, nat form) | `cd_fully_ramified :86`, `genus_from_hurwitz :93`, `hurwitz_base0` (`:202-252`); field `cs_data`; field `rcd_data`. **Instantiated exactly once in the kept set**: `s5_brings_covering_data` (`rigidity_s5_instance.v:300`, genus 4, degree 120, ramification 246). |
| `reconstruct/covering_scheme.v:122` | `ReconPlug M secretT` (`MkReconPlug`) | `rp_scheme : ThresholdScheme secretT 'I_(pgg_N' M).+1`; `rp_content : 'I_N -> 'I_N`; `rp_monodromy : pgg_gT M -> {perm 'I_(ts_T' rp_scheme).+1}`; `rp_recon_invariant` | Field `mp_plug` of `MonodromyProfile`; field `cs_plug`; index of `InputEncoding`; `recon_from_layout` (`input_encoding.v:67`). Instantiated: `five_card_plug` (`five_card_family.v:147`), `pgl27_plug` (`pgl27_scheme.v:95`), `constant_deck_plug` (`pgl27_profile_privacy.v:204`), `s5_plug` (`s5_profile.v:47`, projected out of `s5_brings_covering`). |
| `reconstruct/covering_scheme.v:146` | `CoveringScheme M` (`MkCoveringScheme`) | `cs_plug : ReconPlug M 'I_(pgg_N' M).+1`; `cs_data : CoveringData M`; `cs_gap : ts_T <= ts_k + 2 * cd_genus` | `genus0_exact :169`, `higher_genus_wider_gap :182`, `gap_bound :192`; field `tw_covering` of `ThresholdWitness`; `security_threshold_tradeoff` (`cover_tradeoff.v:140`), `search_gap_tradeoff` (`:188`). **Instantiated exactly once in the kept set**: `s5_brings_covering` (`rigidity_s5_instance.v:349`), aliased `s5_covering` (`:439`). |
| `reconstruct/curve_realisation.v:81` | `RealisedCoveringData M` (`MkRealisedCoveringData`) | `rcd_data : CoveringData M`; `rcd_realised : realised_by_curve rcd_data` | **Nothing in the kept set.** The kept S5 instance passes the two components separately (`s5_brings_covering_data`, `Axiom s5_brings_covering_realised`). |
| `reconstruct/input_encoding.v:31` | `InputEncoding M secretT plug inputT` (`MkInputEncoding`) | `ie_assemble : inputT -> tuple 'I_N`; `ie_output : inputT -> secretT`; `ie_assemble_valid`; `ie_orbit` (equal-output inputs lie in one cut orbit) | `ie_output_correct :51`, `recon_from_layout_output :80`. **Instantiated exactly once in the whole repository**: `den_boer_encoding` (`den_boer_encoding.v:101`), at `inputT = bool * bool`, `ie_output = fun ab => ab.1 && ab.2`. |
| `reconstruct/algebraic_rigidity.v:99` | `SecurityExact rho` (`MkSecurityExact`) | `se_eps : R`; `se_exact : forall s, var_dist (one-position pushforward of rho) uniform = se_eps` | Optional field `scb_exact`. Not populated by any kept instance (all four pass `None` or build the bundle through `shuffle_bundle_of_bound :285`). |
| `reconstruct/algebraic_rigidity.v:131` | `SecurityAsymptotic` (`MkSecurityAsymptotic`) | `sa_spectral_gap`, `sa_eps_inf : R`; `sa_gap_pos`, `sa_gap_le1`, `sa_eps_inf_ge0`; `sa_rho_L : nat -> R.-fdist {perm 'I_N}`; `sa_convergence` | Optional field `scb_asymptotic`. Instantiated: `fc_kim_asymptotic` (`five_card_kim.v:482`), `s5_asymptotic` (`rigidity_s5_instance.v:188`). |
| `reconstruct/algebraic_rigidity.v:154` | `ShuffleMarginalBound R M` (`MkShuffleMarginalBound`) | `sw_L : nat`; `sw_bound_eps : R`; `sw_rho_dist : R.-fdist {perm 'I_N}`; `sw_bound : forall s, var_dist (pushforward at s) uniform <= sw_bound_eps` | Field `scb_bound`; `SecurityProfile :572`; `CertifiedSolution :621`. Instantiated: `den_boer_marginal_bound` (`den_boer_profile.v:72`), `pgl27_marginal_bound` (`pgl27_profile.v:101`), `s5_security_witness_1` (`rigidity_s5_instance.v:156`). |
| `reconstruct/algebraic_rigidity.v:182` | `ShuffleCertificateBundle R M` (`MkShuffleCertificateBundle`) | `scb_bound : ShuffleMarginalBound`; `scb_exact : option (SecurityExact ...)`; `scb_asymptotic : option SecurityAsymptotic` | Field `ar_security` of `AlgebraicRigidity`. Instantiated: `fc_kim_security_bundle` (`five_card_kim.v:497`), `kim_security_bundle_centi` (`:630`), `pgl27_certificate_bundle` (`pgl27_profile.v:108`), `s5_security_witness_schreier` (`rigidity_s5_instance.v:205`). |
| `reconstruct/algebraic_rigidity.v:218` | `ThresholdWitness M` (`MkThresholdWitness`) | `tw_covering : CoveringScheme M`; `tw_genus0_klein : cd_genus = 0 -> #\|G\| <= klein_genus0_bound M` | Field `ar_threshold`. **Instantiated only by S5**: `s5_threshold_witness_concrete` (`rigidity_s5_instance.v:397`), `s5_threshold_witness` (`:452`). |
| `reconstruct/algebraic_rigidity.v:230` | `AlgebraicRigidity R M` (`MkAlgebraicRigidity`) | `ar_security : ShuffleCertificateBundle R M`; `ar_threshold : ThresholdWitness M` | `ar_gap_bound`, `ar_security_profile :587`, `ar_protocol_correct` (same file). **Instantiated only by S5**: `s5_rigidity_cryptographically_secure` (`rigidity_s5_instance.v:408`), `s5_rigidity` (`:461`). |
| `reconstruct/algebraic_rigidity.v:572` | `SecurityProfile R M` (`MkSecurityProfile`) | `sp_Lstar : nat`; `sp_witness : ShuffleMarginalBound`; `sp_at_Lstar`; `sp_nontrivial : sw_bound_eps < 2` | `ar_security_profile :587`. No kept instance builds one. |
| `reconstruct/algebraic_rigidity.v:621` | `CertifiedSolution R M` (`MkCertifiedSolution`) | `cs_params : SecurityParams`; `cs_witness : ShuffleMarginalBound`; `cs_L_eq`; `cs_denom_pos`; `cs_eps_le` | `certified_from_bound` (same file). No kept instance builds one. |
| `security/pgg_leakage_witness.v:31` | `LeakageWitness P` (`MkLeakageWitness`) | `lw_secretT`, `lw_viewT : finType`; `lw_secret : {RV P -> lw_secretT}`; `lw_view : {RV P -> lw_viewT}`; `lw_indep : P \|= lw_view _\|_ lw_secret` | `leakage_of_view_indep :44`; `trace_secrecy_of_witness` (`pgg_trace_secrecy.v:67`); target of `mechanism_leakage` (`pgg_sharing_mechanism.v:46`). No instance builds one directly; all four reach it through `SharingMechanism`. |
| `security/pgg_cyclic_cut_leakage.v:30` | `CyclicCutData P` (`MkCyclicCutData`) | `ccd_secretT`, `ccd_viewT : finType`; `ccd_secret`; `ccd_view`; `ccd_indep` | `cyclic_cut_leakage :39`; constructor argument of `CyclicCut`. Instantiated: `denboer_ccd` (`denboer_secrecy.v:35`), shared by Kim (`kim_secrecy.v:41`). |
| `security/pgg_randomized_sharing.v:39` | `RandomizedSharing P N' T'` (`MkRandomizedSharing`) | `rsh_secret : {RV P -> 'Z_N}`; `rsh_mask : 'I_T' -> {RV P -> 'Z_N}`; `rsh_mask_unif`; `rsh_masks_indep`; `rsh_mask_indep` | `rsh_share :50`, `rsh_view :57`, `additive_allbut_indep :63`, `additive_view_indep`, `additive_leakage` (same file); constructor argument of `Additive`. Instantiated: `unif_randomized_sharing` (`pgg_canonical_sharing.v:106`), used as `s5_rs` (`s5_trace.v:115`). |
| `security/pgg_sample_adapter.v:111` | `SampleAdapter R mp e` (`MkSampleAdapter`) | `sa_sampleT : finType`; `sa_sampleP : R.-fdist sa_sampleT`; `sa_arg : sa_sampleT -> ep_inputT e`; `sa_cut : sa_sampleT -> pgg_gT (mp_M mp)` | `sa_run`, `sa_seat_view`, `sa_coalition_view`, `sa_seat_dist`, `sa_coalition_dist`, `sa_cut_dist`, `sa_joint_dist`, `sa_static_*` (same file); field `amf_sample`. Instantiated 9x across the four instances (`five_card_exec.v:465`; `five_card_models.v:139,161,382`; `pgl27_exec.v:329,438`; `pgl27_models.v` fixed variants; `s5_models.v:113,253`). |
| `security/pgg_schreier.v:304` | `SchreierCertificate` (`MkSchreierCertificate`) | `sc_lambda_gap : R`; `sc_lambda_pos`; `sc_lambda_le1`; `sc_convergence : var_dist <= sqrt N * (1 - gap)^L` | `convergence_rate`, `schreier_epsilon` and the bridge lemmas of the same file. **No kept instance builds one** (S5 builds a `SecurityAsymptotic` instead; see `algebraic_rigidity.v:131` comment on the circular dependency). |
| `security/pgg_schreier_weighted.v:139` | `WeightedSchreierCertificate` (`MkWeightedSchreierCertificate`) | `wsc_doubly_stochastic`; `wsc_lambda_gap : R`; `wsc_lambda_pos`; `wsc_lambda_le1`; `wsc_convergence` (over `endpoint_dist_weighted`) | `weighted_convergence_rate`, `weighted_schreier_epsilon` (same file). Instantiated once: `fc_kim_schreier_cert` (`five_card_kim.v:437`). |
| `security/pgg_security_solver.v:35` | `SecurityParams` (`MkSP`) | `sp_Tg`, `sp_N`, `sp_L : nat`; `sp_eps : nat * nat` | `sp_consistent :43`, `epsilon_endpoint_rat :52`, `solve_L_aux`, `star_to_generic :182`, `group_template :576`; field `cs_params` of `CertifiedSolution`. Computable layer; no kept instance consumes its output as a proof. |
| `security/pgg_security_solver.v:172` | `StarParams` (`MkStarP`) | `star_m`, `star_L : nat`; `star_eps : nat * nat` | `star_to_generic :182`, `star_solve`. Star family only; **no kept instance**. |
| `security/pgg_security_solver.v:371` | `GroupDesc` (`MkGroupDesc`) | `gd_Tg`, `gd_N : nat`; `gd_comm : nat -> nat -> bool`; `gd_gens : nat -> nat -> nat` | `group_template :576` and the per-family templates in the same file. **No kept instance** consumes it. |
| `security/pgg_security_solver.v:551` | `SecuritySpec` (`MkSecuritySpec`) | `ss_target_eps : option (nat * nat)`; `ss_L : option nat` | Argument of `gt_solve`. **No kept instance.** |
| `security/pgg_security_solver.v:556` | `GroupTemplate` (`MkGroupTemplate`) | `gt_Tg`, `gt_N : nat`; `gt_solve : SecuritySpec -> option SecurityParams` | `group_template :576`. **No kept instance.** |
| `manifest/pgg_analysis_status.v:100` | `AnalysisModelFamily observed` (`MkAnalysisModelFamily`) | `amf_index : realType -> Type`; `amf_sample : forall R, amf_index R -> SampleAdapter R (OE.oe_execution observed)` | `AnalysisModelSlot :127`; field `apr_model` of `AnalysisPathRow` in the manifest. Instantiated: `five_card_uniform_family` (`five_card_models.v:426`), `kim_biased_family` (`:435`), `kim_centi_family` (`:443`), `pgl27_exact_family` (`pgl27_models.v:410`), `pgl27_word_family` (`:417`), `s5_rand_family` (`s5_models.v:447`), `s5_word_family` (`:455`). |

Two auxiliary type declarations that are not `Record`s but carry the same role:

- `security/pgg_sharing_mechanism.v` `Variant SharingMechanism := Additive (rs : RandomizedSharing P N' T') (C : {set 'I_T'.+1}) (HC : #|C| < T'.+1) | CyclicCut (cc : CyclicCutData P)`, with `mechanism_leakage :46` mapping either arm into one `LeakageWitness`. Both arms are exercised: `CyclicCut` by the five-card family (`denboer_secrecy.v:38`), `Additive` by S5 (`s5_secrecy.v:35`).
- `protocol/pgg_interface.v:300` `Inductive pgg_data (N : nat) := PGG_sheet | PGG_hand | PGG_idx`, the session-typed wire alphabet, with tag projection `pgg_data_dtype`.

---

## (c) The concrete chain, per instance

### C.1 den Boer 1989 — with-input (two-party AND)

The den Boer instance shares its entire program with Kim. What is specific to
den Boer is the *encoding* of two private input bits into a five-card layout, and
the *bias* `eps = 0` of the dealing distribution.

| Stage | Identifier | Location |
|---|---|---|
| group plug | `FiveCardKim_M := @Gen_PGGTypes 4 3 fc_kim_sigmas` (C_5 acting on 5 card positions, 5 generators `sigma^0..sigma^4`) | `instances/kim2025/five_card_kim.v:135` |
| generator | `fc_sigma : {perm 'I_5}`, the 5-cycle | `instances/denboer1989/five_card_group.v:83` |
| interface | `FiveCardKim_PI := @MkPGGI FiveCardKim_M 4 (ord_tuple 5) ord_tuple5_uniq` (5 seats) | `instances/kim2025/five_card_family.v:138` |
| threshold scheme | `fcI_scheme : ThresholdScheme bool 'I_5 := @MkThresholdScheme bool 'I_5 4 1 ...` (5 shares, privacy threshold 2) | `instances/denboer1989/five_card_scheme_I5.v:197` |
| recon plug | `five_card_plug : ReconPlug FiveCardKim_M bool` | `instances/kim2025/five_card_family.v:147` |
| profile | `den_boer_profile : MonodromyProfile := five_card_profile` | `instances/denboer1989/den_boer_profile.v:67`; base at `five_card_family.v:160` |
| input encoding | `den_boer_encoding : InputEncoding five_card_plug (bool * bool)`, `ie_output = fun ab => ab.1 && ab.2` | `instances/denboer1989/den_boer_encoding.v:101` |
| **piSMC program term** | `den_boer_dealer_run := dealer_with_input_encoding FiveCardKim_PI (fun committed => tnth (den_boer_layout (den_boer_decode committed))) [:: w0] [:: 7; 8] den_boer_players P_idx` | `instances/denboer1989/den_boer_run.v:127` |
| | `den_boer_saprocs` (dealer + verifier + 5 players + 2 commit processes = 9 processes) | `den_boer_run.v:134` |
| | `den_boer_procs := erase_aprocs (den_boer_saprocs ...)` | `den_boer_run.v:142` |
| | reuses `exchange_verifier` (`card_exchange_pismc.v:257`) and `player_aprocs`/`exchange_player` (`:251`, `:240`) verbatim | |
| commit stage | `pgg_commit`, `pgg_commit_prologue`, `exchange_dealer_with_commit` | `protocol/pgg_input_commitment.v:63,:87,:114`; used at `den_boer_profile.v:192-199`, duality certified at `den_boer_profile.v:226,:234,:241,:249` |
| execution plug | `five_card_exec_plug := @committed_input_plug mpF (bool*bool) erefl ... (fun ab => [:: pgg_commit ... 7 ...; pgg_commit ... 8 ...]) 100` | `instances/kim2025/five_card_exec.v:144` |
| observed execution | `five_card_observed`, aliased `den_boer_observed` at `:430`; `oe_expected = fun ab => ab.1 && ab.2` | `instances/kim2025/five_card_exec.v:422` |
| trace object | `denboer_player_trace (i : 'I_5) : {RV dbP -> 'I_5}` | `instances/denboer1989/denboer_trace.v:120`; executed twin `five_card_exec_trace` (`five_card_exec.v`), identified at `five_card_exec.v:544` |
| leakage witness | `denboer_ccd : CyclicCutData dbP := MkCyclicCutData ... (Secret R) (ViewA R [:: 0%N]) denboer_indep` | `instances/denboer1989/denboer_secrecy.v:35` |
| | `denboer_mechanism : SharingMechanism dbP 0 0 := CyclicCut denboer_ccd` | `denboer_secrecy.v:38` |
| | resting on `leak_k1 : `I( Secret ; ViewA [:: 0%N] ) = 0` | `instances/denboer1989/five_card_leakage.v:256` |

**Reconstruction / correctness theorems.**
`FiveCardKim_protocol_correct` (`den_boer_profile.v:139`) and
`den_boer_committed_protocol_correct` (`:272`): for `P \in pgg_G FiveCardKim_M`
and a valid share tuple, `pgg_recon_endpoints ... P = s`. `den_boer_profile.v`
has no `Section`, so both are closed; the group-membership and validity
conditions are explicit premises. **But their validity premise is satisfiable
only at `s = false`** — see (d)(v) item 5, which is machine-checked. The
theorems that actually compute the AND are the layout-carrying ones below.

`den_boer_run_output` (`den_boer_run.v:28`):
`P \in pgg_G FiveCardKim_M -> pgg_recon_endpoints ... (tnth (den_boer_layout ab)) P = ab.1 && ab.2`.
`den_boer_run_recovers` (`den_boer_run.v:198`), the executed-trace form:
`fc_three_consec [seq decode_bool x | x <- endpoints_of_trace (nth [::] (run_interp 100 (den_boer_procs a b w0 0)).2 1)] = a && b`,
supported by `den_boer_run_terminates` (`:147`, `= nseq 9 Finish`, by `vm_compute`).
`fc_correct` (`five_card_program.v:104`), the pen-and-paper statement:
`k < 5 -> fc_three_consec (fc_shuffle k (fc_arrange a b)) = a && b`.
Executed forms: `five_card_exec_recovers` (`five_card_exec.v:260`),
`five_card_exec_correct` (`:273`, the termination + endpoint-count + recovery
conjunction), `five_card_observed_recovers` (`:439`).
All three sit in `Section five_card_execution` (`five_card_exec.v:122`) whose only
declaration is `Variable R : realType` (`:127`). **No `Hypothesis`, no `Axiom`.**
The bridge that makes the shared `exec_*` stack agree with den Boer's own process
list is definitional: `five_card_exec_procsE` (`five_card_exec.v:181`,
`exec_procs ... = den_boer_procs a b w0 P_idx`, proof `by []`).

**Security theorems.**
`leak_view_set : forall S, `I( Secret ; ViewS S ) = leak S` (`five_card_leakage.v:1052`),
the exact per-coalition leakage function.
`denboer_view_secrecy` (`denboer_secrecy.v:48`): zero mutual information and
unchanged conditional entropy for the one-card view.
`denboer_trace_secrecy` (`denboer_trace.v:194`) and
`five_card_exec_trace_secrecy` (`five_card_exec.v:556`): the same, transported to
the executed interpreter trace via `trace_secrecy_of_view`
(`security/pgg_trace_secrecy.v:41`).
`den_boer_perfect : sw_bound_eps (den_boer_marginal_bound R) = 0`
(`den_boer_profile.v:82`) — one uniform cyclic cut gives an exactly zero endpoint
marginal distance. Its three side conditions are discharged at
`den_boer_profile.v:46,:52,:58` and passed as explicit arguments.
`den_boer_input_private (A : seq nat) : cond_mutual_info (`p_ [% Inputs, ViewA R A, Secret R]) = 0`
(`den_boer_encoding.v:337`) and `input_private_ViewS` (`:367`) — the *exact zero*
that Kim's `kim_leak_bound eps` degenerates to at `eps = 0`, resting on
`den_boer_cinde` (`:222`).
Section scope for all of these: `Variable R : realType` only. **No undischarged
hypothesis and no axiom** — the nine den Boer files contain no `Hypothesis`,
no `Axiom`, no `Admitted`, no `Abort`. The only other section variables in the
directory are the abstract readout `g`, committed values `va vb` and cut `w0` of
`Section abstract_leaf` (`denboer_trace.v:43-46`), all instantiated concretely at
`denboer_trace.v:139-152`.

### C.2 Kim 2025 — with-input, biased dealing

Kim is the same program at a non-zero bias `eps`. `kim_run.v`, `kim_secrecy.v`
and `kim_trace.v` are alias shells: `kim_procs := den_boer_procs`
(`kim_run.v:28`), `kim_mechanism := denboer_mechanism` (`kim_secrecy.v:41`),
`kim_player_trace := denboer_player_trace R` (`kim_trace.v:40`).

Kim's own mathematical content is exactly two things.

1. **The biased-shuffle spectral analysis.** `kim_weight_dist` (the circulant
   `W_eps`), `kim_lambda2 := 5/4 * |eps|`, and
   `kim_spectral_convergence : var_dist (endpoint_dist_weighted W L s) uniform
   <= sqrt 5 * kim_lambda2 ^+ L` (`five_card_kim.v:403`), with the exact equality
   at `:453`, the `WeightedSchreierCertificate` at `:437`, the
   `SecurityAsymptotic` at `:482` and the bundle at `:497`.
   Section `kim_security` (`:351`) carries three hypotheses:
   `eps_lt : eps < 5%:R^-1` (`:355`), `eps_gt : - (4%:R * 5%:R^-1) < eps` (`:356`),
   `eps_spectral : |eps| < 4%:R / 5%:R` (`:359`).
   **Both discharges exist**: at `eps = 1/100` by `kim_centi_lt` (`:585`),
   `kim_centi_gt` (`:591`), `kim_centi_spec` (`:602`), consumed by
   `kim_security_bundle_centi` (`:630`); at `eps = 0` by `den_boer_eps0_lt/gt/spectral`
   (`den_boer_profile.v:46,:52,:58`).
   Closed numeric consequences in the hypothesis-free `Section kim_concrete`
   (`:543`, only `Variable R`): `kim_bound_centi` (`:612`),
   `kim_deal_centi_lt` (`:636`), `kim_one_cut_centiE` (`:651`).

2. **The `O(eps^2)` input-privacy bound.**
   `kim_input_private (A : seq nat) : cond_mutual_info (`p_ [% kim_inputs, kim_view A, kim_secret]) <= kim_leak_bound eps`
   (`instances/kim2025/kim_input_privacy.v:716`), where
   `kim_leak_bound e := 12 * log(e) * e^2 / (1/5 - |e|)` (`:78`).
   Section `kim_input_privacy` (`:44`) carries `eps_lt_inv5` (`:47`),
   `eps_gt_neg4inv5` (`:48`) and `eps_small : 0 < 5%:R^-1 - |eps|` (`:439`).
   Executed transport: `five_card_colour_view_leak_bound` (`five_card_models.v:360`),
   inside `Section five_card_input_privacy_transport` (`:350`) which re-declares
   `Hypothesis eps_small` (`:351`).

Kim's execution and observation objects are the shared ones (`five_card_exec_plug`,
`five_card_observed`). The three `AnalysisModelFamily` values are
`five_card_uniform_family` (`five_card_models.v:426`), `kim_biased_family` (`:435`)
and `kim_centi_family` (`:443`); the facade is `Module FiveCardAnalysis`
(`five_card_analysis.v:98`).

`instances/kim2025/rigidity_kim_instance.v` builds no `AlgebraicRigidity`. Its
only content is `kim_complexity (L) : search_space M_kim L <= #|pgg_G M_kim|`
(`:59`), and the five section declarations `R` (`:43`), `eps` (`:46`),
`eps_lt` (`:47`), `eps_gt` (`:48`), `eps_spectral` (`:49`) are all dead for it —
the proof is `exact: search_space_leG`. The file header (`:11-17`) records that
the Reed-Solomon rigidity block was removed as vacuous for `|C_5| = 5`.

### C.3 PGL(2,7) — pure secret sharing, 8 cards

| Stage | Identifier | Location |
|---|---|---|
| group plug | `Notation pgl27_M := (@Gen_PGGTypes 2 6 pgl27_gens)` (3 generators, 8 card positions) | `instances/pgl27/pgl27_group.v:97` |
| generators | `pgl27_gens : 3.-tuple {perm 'I_8}` | `pgl27_group.v` (see `code_tr`/`code_sc`/`code_inv` at `pgl27_orbit.v`) |
| transitivity | `pgl27_3transitive : ntransitive 3 (pgg_rho @* pgg_G) [set: 'I_8] 'P` | `pgl27_group.v:304` |
| interface | `pgl27_PI` (8 seats) | `instances/pgl27/pgl27_profile.v:54` |
| threshold scheme | `orbit_scheme : ThresholdScheme bool 'I_8 := @MkThresholdScheme bool 'I_8 (pgg_N' pgl27_M) 3 ...` (8 shares, `ts_k' = 3`, so privacy for `#\|C\| <= 3`) | `instances/pgl27/pgl27_scheme.v:79` |
| recon plug | `pgl27_plug : ReconPlug pgl27_M bool` | `pgl27_scheme.v:95` |
| profile | `pgl27_profile := @MkMonodromyProfile pgl27_M bool pgl27_PI pgl27_plug` | `instances/pgl27/pgl27_profile.v:117` |
| marginal bound | `pgl27_marginal_bound : ShuffleMarginalBound R pgl27_M`; `pgl27_certificate_bundle` | `pgl27_profile.v:101`, `:108` |
| second generator tuple | `pgl27_sym_sigmas : 5.-tuple {perm 'I_8}` (the 3 generators plus the 2 non-involutive inverses), used only for the word walk; `Notation pgl27_Msym := (Gen_PGGTypes pgl27_sym_sigmas)`; both tuples generate the same group by `pgl27_gen5_eq` | `pgl27_mixing.v:58`, `pgl27_word_privacy.v:52`, `pgl27_mixing.v:505` |
| **piSMC program term** | `pgl27_dealer_run (s) (w0) := dealer_with_input_encoding pgl27_PI (fun _ => tnth (ts_encode orbit_scheme s)) [:: w0] [::] pgl27_players 0` | `instances/pgl27/pgl27_run.v:66` |
| | `pgl27_saprocs :73`, `pgl27_procs :80` (dealer + verifier + 8 players = 10 processes, `pgl27_fuel = 220`) | `pgl27_run.v:50,:73,:80` |
| | shared programs also reached through the profile wrappers: `run_party_pgl27 :210` (`run_party pgl27_profile i = exchange_player pgl27_PI i`, proof `by []`), `run_recover_pgl27 :198`. **The only kept use of `run_party` / `run_recover`** — the other three instances call `exchange_player` / `exchange_verifier` directly | `pgl27_run.v:198,:210` |
| execution plug | `pgl27_exec_plug := @dealer_secret_plug mpP bool erefl pgl27_players pgl27_players_enumE (fun s _ => tnth (ts_encode orbit_scheme s)) pgl27_fuel` (`pgl27_fuel = 220`) | `instances/pgl27/pgl27_exec.v:106` |
| observed execution | `pgl27_observed`, `oe_content_obs = pgl27_content_obs`, `oe_expected = id` on `bool` | `pgl27_exec.v:304` |
| trace objects | `pgl27_player_trace (i)` `:316`, `pgl27_coalition_trace (C)` `:410`, plus the all-decks and deck-prior variants `:470`, `:627` | `instances/pgl27/pgl27_trace.v` |
| sample adapters | `pgl27_sample` (exact uniform on the group) `:329`; `pgl27_word_sample` (200-letter word) `:438` | `instances/pgl27/pgl27_exec.v` |
| model families | `pgl27_exact_family :410`, `pgl27_word_family :417` | `instances/pgl27/pgl27_models.v` |

**Reconstruction / correctness theorems.**
`pgl27_run_recovers_class` (`pgl27_trace.v:286`);
`pgl27_exec_recovers` (`pgl27_exec.v:192`);
`pgl27_exec_correct` (`:206`);
`pgl27_observed_recovers` (`:313`);
`pgl27_word_run_recovers (s) (w : 200.-tuple 'I_5)` (`pgl27_word_privacy.v:58`).
Sections carry `Variable R : realType` only. **No `Hypothesis`, no `Axiom`
anywhere in the 15 pgl27 files.**

**Security theorems.**
- `pgl27_view_indep (C) : #|C| <= 3 -> pgl27P |= pgl27_view C _|_ pgl27_secret`
  (`pgl27_secrecy.v:82`), proved from `ttrans_view_indep_gen`
  (`reconstruct/transitivity_privacy.v`) at `t = 3` via `pgl27_3transitive`.
- `pgl27_trace_secrecy (i)` (`pgl27_trace.v:396`) and
  `pgl27_coalition_trace_secrecy (C)` (`:429`): the executed trace form.
- `pgl27_exec_exact_view_indep (C) : #|C| <= 3 -> ...` (`pgl27_models.v:367`), at
  the executed sample adapter.
- `pgl27_word_view_indist (C) (s) (s') : #|C| <= 3 -> var_dist (view law at s) (view law at s') <= 2^-39`
  (`pgl27_word_privacy.v:172`), and its executed-trace transport
  `pgl27_word_trace_indist` (`:193`).
- `pgl27_view_mixing` (`pgl27_word_privacy.v:218`).
- `pgl27_word_view_indist_via_transfer` (`pgl27_models.v:387`), the same bound
  routed through the generic `var_dist_fdistmap_transfer`, whose base premise is
  **discharged** by `pgl27_word_mixing` at `pgl27_models.v:397`.
- Sharpness: `pgl27_view_dep_k4` (`pgl27_secrecy.v:116`) and
  `pgl27_view_leak_k4` (`:192`) exhibit a concrete 4-coalition
  (`pgl27_leak_coalition`, `:110`) with strictly positive mutual information. The
  privacy threshold 3 is proved tight, not merely claimed.

**Three structural absences, each with a reason.**

- **No `CoveringScheme`, hence no genus, no `ThresholdWitness`, no
  `AlgebraicRigidity`.** This is a type mismatch, not an omission:
  `CoveringScheme` requires `cs_plug : ReconPlug M 'I_(pgg_N' M).+1`
  (`reconstruct/covering_scheme.v:147`), a position-valued secret, while
  `pgl27_plug : ReconPlug pgl27_M bool` (`pgl27_scheme.v:95`). A boolean secret
  cannot enter the genus machinery as it stands.
- **No `LeakageWitness` value.** pgl27 states independence directly as
  `pgl27P |= pgl27_view C _|_ pgl27_secret` and never packages it into the
  `SharingMechanism`/`LeakageWitness` interface that den Boer, Kim and S5 use.
- **No formal isomorphism `pgg_G pgl27_M ~= pgl2 'F_7`.** What is proved is
  `#|pgl2 'F_7| = 336` (`pgl27_group.v:157`, from `card_pgl2` at
  `reconstruct/pgl_bound.v:167`) and, separately,
  `#|pgg_G pgl27_M| = 336` (`pgl27_mixing.v:522`), plus three Moebius
  identifications of the generators (`pgl27_group.v:131,:139,:147`). The name
  "PGL(2,7)" rests on matching order and generator shape, not on a kernel-checked
  isomorphism.

**Negative and sharpness results**, which are a real part of this instance's
content:
`pgl27_view_dep_k4` (`pgl27_secrecy.v:116`) and `pgl27_view_leak_k4` (`:192`) —
threshold 3 is tight;
`profile_view_indep_sharp` (`pgl27_profile_privacy.v:117`) — the record-level
privacy statement fails at coalition size `t.+1`;
`constant_deck_view_dep` (`:224`) and `profile_distinct_deck_necessary` (`:269`) —
dropping the distinct-deck premise makes the theorem false. These last three are
what the second, degenerate `MonodromyProfile` (`constant_deck_profile`, `:210`,
over `constant_deck_scheme :178`, `constant_deck_plug :203`,
`constant_deck_monodromy = fun _ => 1%g` at `:188`) exists to exhibit. It is a
counterexample object, not a protocol.

`pgl27_recovery.v` and `pgl27_leakage_census.v` chart the leakage ramp:
private up to three (`pgl27_view_indep`), leaky from four
(`pgl27_view_leak_k4`), ambiguous through six
(`pgl27_reveal_ambiguous :131`), determined at seven
(`pgl27_seven_reveal_determines :37`, `pgl27_seven_reveal_class :68`), while the
implemented decoder reads all eight. The census quantifies it with a
`vm_compute` collision count per reveal set: 336 at three cards
(`pgl27_leakage_census.v:443`), 96 / 72 at four (`:417`, `:423`), 36 at five
(`:430`), 12 at six (`:436`), 0 at seven (`:450`).

### C.4 S5 — pure secret sharing, two dealing modes

| Stage | Identifier | Location |
|---|---|---|
| group plug | `@Gen_PGGTypes 3 3 (path_gen_tuple 3)` — the four adjacent transpositions of 5 card positions, generating all of `Sym('I_5)` | `groups/pgg_raag_path.v:75` (`path_gen_tuple`), template at `protocol/pgg_interface.v:521` |
| RAAG structure | `HB.instance Path_isRAAG` (path commutation graph, `path_comm :139`) | `groups/pgg_raag_path.v:280` |
| word-eval injectivity | `s5_weval_inj1 : @weval_inj (@Gen_PGGTypes 3 3 (path_gen_tuple 3)) 1` | `instances/s5/pgg_raag_s5.v:62` |
| spectral input | **`Axiom s5_rayleigh_Q2_R`** (Rayleigh bound on `Q^2` over sum-zero vectors) | `instances/s5/s5_mixing.v:186` |
| mixing bound | `s5_spectral_convergence_proved :200`, `s5_spectral_convergence_gap :255`; `s5_alpha_R = 181/200`, `s5_gap_R = 19/200` | `instances/s5/s5_mixing.v` |
| covering data | **`Axiom s5_group_order_eq : #\|pgg_G s5_brings_M\| = 120`** `:277`; `s5_hurwitz :291`; `s5_brings_covering_data :300` (genus 4, base genus 0, 4 branch points, ramification 246) | `instances/s5/rigidity_s5_instance.v` |
| curve marker | **`Axiom s5_brings_covering_realised : realised_by_curve s5_brings_covering_data`** (Edge 1978, Bring's curve) | `rigidity_s5_instance.v:309` |
| covering scheme | `s5_brings_covering : CoveringScheme s5_brings_M :349`; `s5_covering :439` | `rigidity_s5_instance.v` |
| rigidity | `s5_threshold_witness :452`; `s5_rigidity : AlgebraicRigidity R s5_M :461` (fiber bound `eps = 6/5` at `L = 1`); `s5_rigidity_cryptographically_secure :408` (Schreier bundle at `L = 286`) | `rigidity_s5_instance.v` |
| interface | `s5_PI` (5 seats, `ord_tuple 5`) | `instances/s5/s5_profile.v:38` |
| threshold scheme | `s5_scheme : ThresholdScheme 'I_5 'I_5 := @sum_mod_scheme 3 4` (5 shares, `ts_k' = 4`, so `ts_T = ts_k = 5`) | `instances/s5/s5_run.v:39` |
| recon plug | `s5_plug := cs_plug s5_brings_covering` | `instances/s5/s5_profile.v:47` |
| profile | `s5_profile := @MkMonodromyProfile (@Gen_PGGTypes 3 3 (path_gen_tuple 3)) 'I_5 s5_PI s5_plug`; `profile_k_s5 = 5` `:63` | `s5_profile.v:55` |
| **piSMC program term** | `s5_dealer_run (s) (w0) := dealer_with_input_encoding s5_PI (fun _ => tnth (ts_encode s5_scheme s)) [:: w0] [::] s5_players 0` | `instances/s5/s5_run.v:59` |
| | `s5_saprocs :66` (7 processes), `s5_procs :72`; `s5_run_terminates :75`; `s5_run_recovers :133` | `s5_run.v` |
| execution plugs | `s5_exec_plug := @dealer_secret_plug mpS 'I_5 ... 150` `:136`; `s5_rand_exec_plug := @dealer_secret_plug mpS 'rV['Z_5]_5 ... 150` `:616` | `instances/s5/s5_exec.v` |
| observed executions | `s5_observed :289` (`oe_expected = fun s : 'I_5 => s`); `s5_rand_observed :758` (`oe_expected = fun u => s5_codec (s5_tape_secret u)`) | `s5_exec.v` |
| randomized sharing | `s5_rs := @unif_randomized_sharing R 3 4` | `instances/s5/s5_trace.v:115` |
| trace objects | `s5_player_trace (i)` `:135`, identified with `rsh_share s5_rs i` at `:141`; executed reader `s5_sample_content_trace` (`s5_models.v:150`), identified at `:161` | |
| sample adapters | `s5_rand_sample :113` (tape, cut fixed to `1%g`); `s5_word_sample :253` (secret prior x uniform word of length `L`) | `instances/s5/s5_models.v` |
| model families | `s5_rand_family :447`, `s5_word_family :455` | `s5_models.v` |

**Reconstruction / correctness theorems**, all in `Section s5_execution`
(`s5_exec.v:99`) which has **no `Variable` and no `Hypothesis`**:
`s5_exec_recovers :252`, `s5_exec_correct :267`, `s5_observed_recovers :299`,
`s5_rand_exec_recovers :721`, `s5_rand_correct :737`, `s5_rand_observed_recovers :768`.
Underlying: `s5_run_recovers` (`s5_run.v:133`), `s5_rand_run_recovers` (`s5_exec.v:582`).

**Security theorems.**
- Exact secrecy, hypothesis-free (section scope `Variable R : realType`, plus
  `U`, `P` in `s5_secrecy.v`):
  `s5_view_secrecy (rs) (C) (HC : #|C| < 5)` (`s5_secrecy.v:35`),
  `s5_view_secrecy_concrete` (`:49`),
  `s5_trace_secrecy (i)` (`s5_trace.v:171`),
  `s5_exec_trace_secrecy (i)` (`s5_models.v:176`),
  `s5_exec_coalition_secrecy (C) (HC : #|C| < 5)` (`s5_models.v:209`).
- Endpoint marginal mixing, **conditional on `s5_rayleigh_Q2_R`**:
  `s5_word_endpoint_bound (s)` (`s5_models.v:297`),
  `s5_exec_endpoint_bound (secretP) (L) (i)` (`s5_models.v:389`).
- Model transfer, **conditional on an undischarged premise**:
  `s5_word_base_premise (Q) (delta) := var_dist (sa_cut_dist s5_word_sample) Q <= delta`
  (`s5_models.v:316`) and `s5_word_transfer_conditional` (`:326`). The file pins
  the carrier mismatch with two `Fail Check` guards (`s5_models.v:345`, `:432`):
  the spectral theorem bounds a pushforward on `'I_5`, the premise lives on
  `{perm 'I_5}`. `s5_analysis.v:332-343` records that for the group-uniform ideal
  the premise is *unsatisfiable*.

The two rigidity sections declare `Hypothesis card_G_s5_gt1 : 1 < #|pgg_G s5_M|`
(`rigidity_s5_instance.v:375`, `:427`), but no proof in the file references it, so
neither `s5_rigidity` nor `s5_rigidity_cryptographically_secure` is generalised
over it. It constrains nothing.

**Assumption ledger for S5.**

| result class | rests on |
|---|---|
| correctness (`s5_run_recovers`, `s5_exec_correct`, `s5_rand_correct`, both `*_observed_recovers`) | `s5_group_order_eq` only |
| exact secrecy (`s5_trace_secrecy`, `s5_view_secrecy*`, `s5_exec_trace_secrecy`, `s5_exec_coalition_secrecy`) | `s5_group_order_eq` only |
| `s5_rigidity` (fiber bound) | `s5_group_order_eq` only |
| `s5_rigidity_cryptographically_secure`, `s5_word_endpoint_bound`, `s5_exec_endpoint_bound` | `s5_group_order_eq` **and** `s5_rayleigh_Q2_R` |
| anything at all | `s5_brings_covering_realised` — **nothing** |

`s5_group_order_eq` reaches even the correctness theorems because it is consumed
by `s5_hurwitz` (`:294`), which is a field of `s5_brings_covering_data`, hence of
`s5_brings_covering`, from which `s5_plug` (`s5_profile.v:47`) is projected, hence
`s5_profile`, hence every value in `s5_run.v`, `s5_exec.v`, `s5_models.v` and
`s5_analysis.v`. The manifest states this at `pgg_analysis_manifest.v:432` and
marks all three S5 rows `AcceptsAxioms`.

---

## (d) Evaluation: is it still "one SMC framework, plug in a different group"?

**Short answer: yes at the program layer, and the claim is stronger than it
looks; no at the reconstruction/rigidity layer, where three of the four
instances bypass the machinery entirely.**

### (d)(i) What is shared verbatim, what is re-implemented

**Shared verbatim by all four instances** (no per-instance variant exists):

| Shared object | Location | Evidence of reuse |
|---|---|---|
| `exchange_dealer` | `protocol/card_exchange_pismc.v:222` | reached by all four through `dealer_with_input_encoding` (`protocol/pgg_run.v:47`) |
| `exchange_player` | `card_exchange_pismc.v:240` | `den_boer_run.v:134`, `pgl27_run.v:73`, `s5_run.v:66` (via `player_aprocs :251`) |
| `exchange_verifier` | `card_exchange_pismc.v:257` | same three sites |
| `pgg_commit_prologue` | `protocol/pgg_input_commitment.v:87` | all four, though pgl27 and S5 pass `inputs = [::]` |
| `endpoints_of_trace` | `protocol/pgg_run.v:65` | all four, through `exec_endpoints` |
| the whole `exec_*` stack (`exec_run`, `exec_procs`, `exec_endpoints`, `exec_decode`, `exec_static_endpoints`, `exec_run_recovers`, `exec_run_correct`) | `protocol/pgg_execution_plug.v:156-387` | 30 uses in kim2025, 20 in pgl27, 44 in s5 |
| `OE.oe_run_recovers` / `oe_run_correct` | `protocol/pgg_observed_execution.v:158,:178` | every `*_observed_recovers` theorem |
| the `sa_*` sample layer | `security/pgg_sample_adapter.v` | 9 `SampleAdapter` values across the four |
| `mechanism_leakage` + `leakage_of_view_indep` | `pgg_sharing_mechanism.v:46`, `pgg_leakage_witness.v:44` | den Boer/Kim via `CyclicCut`, S5 via `Additive` |
| `trace_secrecy_of_view` | `security/pgg_trace_secrecy.v:41` | all trace-secrecy theorems in all four |
| `Gen_PGGTypes` + its two `HB.instance`s | `protocol/pgg_interface.v:521,:523,:534` | all four |

**Per-instance re-implementations.** These are genuinely different objects, not
variants of a shared one:

- The **threshold scheme** is written from scratch each time: `fcI_scheme`
  (`five_card_scheme_I5.v:197`, a three-consecutive-hearts boolean read),
  `orbit_scheme` (`pgl27_scheme.v:79`, an orbit-class boolean read),
  `s5_scheme = sum_mod_scheme 3 4` (`s5_run.v:39`, the one library instance).
  Only S5 reuses the framework's own `sum_mod_scheme`.
- The **privacy argument** is different mathematics in each family:
  exact enumeration of the cyclic-cut orbit for the five-card family
  (`five_card_leakage.v:1052`), a `t`-transitivity re-dealing bridge for pgl27
  (`transitivity_privacy.v` at `t = 3`), one-time-pad additive masking for S5
  (`pgg_randomized_sharing.v` + `pgg_canonical_sharing.v`).
- The **mixing argument** is different in each: a weighted Schreier certificate
  for Kim (`pgg_schreier_weighted.v`, used only there), a symmetric
  doubly-stochastic Rayleigh bound for S5 (`pgg_mixing.v`, used only there), and
  for pgl27 a direct uniform-on-the-group argument that needs neither.
- Each instance re-writes its own `*_players` list, `*_content_obs`,
  `*_procsE`/`*_terminates`/`*_endpoints` unfolding lemmas, and its own
  `Module *Analysis` facade. That block is ~60% of each instance directory and is
  structurally identical across instances but not factored.
- The profile-level wrappers `run_party`, `run_verifier`, `run_recover`
  (`protocol/pgg_monodromy_profile.v:86,:90,:95`) are *nominally* the shared
  entry point but are used by **pgl27 alone** (`pgl27_run.v:198,:210`), and there
  only as `by []` corollaries confirming the identification. den Boer, Kim and S5
  bypass them and call `exchange_player` / `exchange_verifier` /
  `player_aprocs` directly. The reuse is real; the intended API is not the one
  being used.

**Within the five-card family, sharing is total.** den Boer and Kim share the
group (`FiveCardKim_M`), the interface, the plug, the profile (`den_boer_profile
:= five_card_profile`, `den_boer_profile.v:67`), the execution plug, the observed
execution, the process list (`kim_procs := den_boer_procs`, `kim_run.v:28`), the
leakage mechanism (`kim_mechanism := denboer_mechanism`, `kim_secrecy.v:41`) and
the trace (`kim_player_trace := denboer_player_trace R`, `kim_trace.v:40`). The
only difference is the numeric bias fed to `fc_kim_security_bundle`. Counting them
as two instances of the framework overstates the framework's coverage: they are
two parameter values of one instance.

### (d)(ii) Do the instances split into the two claimed families?

**Yes, and the split is mechanically visible in the code: it is the choice of
`ExecutionPlug` smart constructor.**

| Instance | constructor | `ep_inputT` | `ep_input_procs` | family |
|---|---|---|---|---|
| den Boer / Kim | `committed_input_plug` (`five_card_exec.v:145`) | `(bool * bool)` | two `pgg_commit` processes at parties 7 and 8 | with-input |
| PGL(2,7) | `dealer_secret_plug` (`pgl27_exec.v:107`) | `bool` | `[::]` | secret sharing |
| S5 (deterministic) | `dealer_secret_plug` (`s5_exec.v:137`) | `'I_5` | `[::]` | secret sharing |
| S5 (randomized) | `dealer_secret_plug` (`s5_exec.v:617`) | `'rV['Z_5]_5` (sampler tape) | `[::]` | secret sharing |

`committed_input_plug` (`protocol/pgg_execution_plug.v:109`) is used **exactly
once in the repository**. `dealer_secret_plug` (`:94`) hard-wires
`ep_input_procs := fun _ => [::]`, so a dealer-secret run provably spawns no
committing party.

Which shared records each family actually instantiates:

| Record | with-input (den Boer / Kim) | secret sharing (pgl27 / S5) |
|---|---|---|
| `PGGInterface` | yes, `FiveCardKim_PI` | yes, `pgl27_PI`, `s5_PI` |
| `ThresholdScheme` | yes, `fcI_scheme` | yes, `orbit_scheme`, `s5_scheme` |
| `ReconPlug` | yes, `five_card_plug` | yes, `pgl27_plug`, `s5_plug` |
| `MonodromyProfile` | yes, `five_card_profile` | yes, `pgl27_profile`, `s5_profile` |
| `ExecutionPlug` | yes, via `committed_input_plug` | yes, via `dealer_secret_plug` |
| `ObservedExecution` | yes, `five_card_observed` | yes, `pgl27_observed`, `s5_observed`, `s5_rand_observed` |
| `SampleAdapter` / `AnalysisModelFamily` | yes (3 families) | yes (2 + 2 families) |
| **input commitment** (`pgg_commit`, `exchange_dealer_with_commit`) | **yes, genuinely** (`den_boer_profile.v:192`, duality certified `:226-:249`) | **degenerate**: `pgg_commit_prologue` is present in the term but every call passes `inputs = [::]` (`pgl27_run.v`, `s5_run.v:62`) and the content function discards the committed list |
| **`InputEncoding`** | **yes, uniquely**: `den_boer_encoding` (`den_boer_encoding.v:101`), `ie_output = fun ab => ab.1 && ab.2` | **no** |
| **`CoveringData` / `CoveringScheme`** | **no** | **S5 only** (`rigidity_s5_instance.v:300,:349`). pgl27 is *type-barred*: `CoveringScheme` needs `cs_plug : ReconPlug M 'I_(pgg_N' M).+1` (`covering_scheme.v:147`) but `pgl27_plug : ReconPlug pgl27_M bool` |
| **`ThresholdWitness` / `AlgebraicRigidity`** | **no** (`rigidity_kim_instance.v` builds neither) | **S5 only** (`:397,:452`, `:408,:461`) |
| `LeakageWitness` (via `SharingMechanism`) | `CyclicCut` arm (`denboer_secrecy.v:38`) | S5: `Additive` arm (`s5_secrecy.v:35`). **pgl27 uses neither** — it goes directly through `transitivity_privacy.v`'s `ttrans_view_indep_gen` and states independence without building a `SharingMechanism` |
| `RandomizedSharing` | no | S5 only (`s5_trace.v:115`) |

So the two-family claim holds, with two qualifications the code makes explicit.
First, the with-input family has exactly one member's worth of program content.
Second, the secret-sharing family is itself split: pgl27's privacy comes from
group transitivity and does not touch the `SharingMechanism`/`LeakageWitness`
interface at all, while S5's comes from additive masking and does.

### (d)(iii) What the plug-in point IS, and whether all four go through it

There are two answers, and the gap between them is the finding.

**The declared plug-in point** is the HB structure `MonodromyReprType`
(`protocol/pgg_interface.v:59`) over `Record PGGTypes` (`:38`), together with
`Record PGGInterface M` (`:360`) and `Record ReconPlug M secretT`
(`covering_scheme.v:122`). A new group would in principle supply
`pgg_gT`, `pgg_N'`, `pgg_G`, a representation `pgg_rho : {morphism G >-> {perm 'I_N}}`,
a starting layout, and a reconstruction plug.

**The actual plug-in point exercised by all four instances** is narrower: a tuple
of permutations. `Section generated_instance` (`protocol/pgg_interface.v:490`)
takes `sigmas : T.-tuple {perm 'I_N}` (`:498`) and builds
`Gen_PGGTypes := @MkPGG gT N.-1 G` (`:521`) with `pgg_rho := gen_incl_morph`
(`:519`), the **identity inclusion** of the generated subgroup into `S_N`. The
two `HB.instance` declarations at `:523` and `:534` are the only ones in the kept
set.

All four instances go through it:

- `FiveCardKim_M := @Gen_PGGTypes 4 3 fc_kim_sigmas` (`five_card_kim.v:135`)
- `Notation pgl27_M := (@Gen_PGGTypes 2 6 pgl27_gens)` (`pgl27_group.v:97`)
- `@Gen_PGGTypes 3 3 (path_gen_tuple 3)` for S5 (`s5_profile.v:38` and the local
  notations at `s5_run.v:30`, `s5_trace.v:39`, `s5_exec.v:106`, `s5_models.v:91`)
- den Boer reuses `FiveCardKim_M`

**None bypasses it, and none exercises the general case.** Because `pgg_rho` is
always an inclusion, no kept instance tests a monodromy representation of a group
that is not already given as a permutation subgroup of `S_N`. The framework's
generality claim — that `pgg_gT` may be "an arbitrary finite group type ...
specified by its own presentation rather than as a pre-chosen subgroup of `S_n`"
(`pgg_interface.v:49-54`) — is not exercised anywhere in the kept set after the
move. The file's own comment names cyclic, abelian, Coxeter, star and monster as
the instantiations that justify it; of those, only the Coxeter/RAAG one (S5) and
the cyclic one (five-card) survive, and both arrive as permutation tuples.

Practically, then, adding a new group after the move means writing:
a `Tg.-tuple {perm 'I_N}`, a `PGGInterface`, a `ThresholdScheme` with its
`ts_correct`/`ts_private` proofs, a `ReconPlug` with `rp_recon_invariant`, and
then a `MonodromyProfile` — after which `run_party`, `run_verifier`,
`run_recover`, the whole `exec_*` stack, `ObservedExecution` and the
`SampleAdapter` layer come for free. The threshold scheme and its privacy proof
are the real cost; the program is genuinely free.

### (d)(iv) Kept files with no consumer among the four instances

Computed as the complement of the transitive closure of the four instance
directories over the kept-set dependency graph. **Exactly four core files are
dead with respect to the four instances**, and all four are among the files kept
by explicit user decision rather than by dependency closure:

1. `protocol/card_protocol_posterior.v` — no kept file requires it, and it
   requires no kept file. A self-contained Bayesian bridge
   (`input_output_joint`, `posterior`, `posterior_bias_le_var_dist_scaled`,
   `Section card_posterior :60`, `Section pgg_posterior_bridge :270`).
2. `reconstruct/s5_nogo.v` — no consumer. Its four theorems
   (`s5_no_secret_dim3 :391`, `s5_no_secret_dim4 :405`,
   `s5_gap_window_infeasible :421`, `s5_gap_infeasible :439`) are a negative
   result about `S_5` on `GF(5)^6` that the kept S5 instance never invokes.
3. `reconstruct/gap_dimension.v` — consumed only by `s5_nogo.v`.
4. `reconstruct/invariant_profiler.v` — consumed only by `s5_nogo.v`.

A further finding of the same kind, at declaration rather than file granularity:
`reconstruct/input_encoding.v` is `Require`d by
`protocol/pgg_execution_plug.v`, `protocol/pgg_observed_execution.v`,
`security/pgg_sample_adapter.v` and ten instance files, but **none of its four
exports** (`InputEncoding :31`, `ie_output_correct :51`, `recon_from_layout :67`,
`recon_from_layout_output :80`) **is referenced outside
`instances/denboer1989/den_boer_encoding.v`**. Every other import of that file is
vestigial.

Eight files in the instance directories have no kept consumer, but three of those
are the analysis facades that the trimmed `manifest/pgg_analysis_manifest.v`
requires (`five_card_analysis.v`, `pgl27_analysis.v`, `s5_analysis.v`), and the
rest are terminal results rather than dead code:
`instances/kim2025/kim_run.v`, `kim_trace.v`, `rigidity_kim_instance.v`;
`instances/pgl27/pgl27_leakage_census.v` (and `pgl27_recovery.v`, reachable only
through it), `pgl27_profile_privacy.v`. Of these, `rigidity_kim_instance.v` is the
weakest: its single lemma `kim_complexity` (`:59`) is one line of generic
combinatorics and its five section declarations are all unused.

Records with no kept inhabitant, i.e. dead at the type level:
`RealisedCoveringData` (`curve_realisation.v:81`),
`SecurityExact` (`algebraic_rigidity.v:99`),
`SecurityProfile` (`:572`), `CertifiedSolution` (`:621`),
`SchreierCertificate` (`pgg_schreier.v:304`),
and all five records of `security/pgg_security_solver.v` (`:35`, `:172`, `:371`,
`:551`, `:556`). The last group means the entire computable dealer-solver layer is
unexercised by the four instances, even though `pgg_security_solver.v` is a
`Require` of `protocol/card_exchange_pismc.v` and `reconstruct/algebraic_rigidity.v`.

### (d)(v) Security theorems conditional on an undischarged hypothesis or axiom

Six items, in decreasing severity.

1. **Every S5 theorem, including correctness, depends on
   `Axiom s5_group_order_eq`** (`instances/s5/rigidity_s5_instance.v:277`).
   Route: `:294 s5_hurwitz` -> `:300 s5_brings_covering_data` ->
   `:349 s5_brings_covering` -> `s5_profile.v:47 s5_plug` -> `:55 s5_profile` ->
   every declaration in `s5_run.v`, `s5_exec.v`, `s5_models.v`, `s5_analysis.v`.
   This is a provable statement (`#|Sym('I_5)| = 120`) left as an axiom, and the
   repository declares it: all three S5 manifest rows carry
   `AcceptsAxioms [:: AxS5GroupOrder]` (`pgg_analysis_manifest.v:1225,:1236`).

2. **The S5 mixing bounds depend on `Axiom s5_rayleigh_Q2_R`**
   (`instances/s5/s5_mixing.v:186`), consumed at `s5_mixing.v:211`. Affects
   `s5_spectral_convergence_proved :200`, `s5_spectral_convergence_gap :255`,
   `s5_asymptotic` (`rigidity_s5_instance.v:188`),
   `s5_security_witness_schreier` (`:205`),
   `s5_rigidity_cryptographically_secure` (`:408`),
   `s5_word_endpoint_bound` (`s5_models.v:297`),
   `s5_exec_endpoint_bound` (`s5_models.v:389`). The justification is an external
   numerical SoS certificate (`instances/s5/s5_spectral_certificate.py/.md`,
   described at `s5_mixing.v:103-136`), so the certificate itself is not
   machine-checked; only its conclusion enters Rocq. The SoS data that *is* in the
   file (`s5_sos_lower_triangular :143`, `s5_sos_diagonal :154`) is referenced by
   no proof.

3. **`s5_word_transfer_conditional` (`instances/s5/s5_models.v:326`) is
   conditional on `s5_word_base_premise` (`:316`), which nothing proves**, and
   which `s5_analysis.v:332-343` records as *unsatisfiable* for the
   group-uniform reference distribution. The file itself pins the carrier
   mismatch with two `Fail Check` guards (`s5_models.v:345`, `:432`). The
   consequence is that S5 has **no proved bound between its shuffle distribution
   and group-uniform on `{perm 'I_5}`**: `s5_word_endpoint_bound` bounds a single
   seat's position marginal on `'I_5`, and `s5_exec_endpoint_bound` compares
   against `s5_ideal_reading` (`s5_models.v:376`), which is neither uniform nor
   secret-independent. Contrast pgl27, whose corresponding transfer premise **is**
   discharged, by `pgl27_word_mixing` at `pgl27_models.v:397`.

4. **Kim's input-privacy bound is never instantiated at a closed bias with all
   three side conditions proved.** `kim_input_private`
   (`kim_input_privacy.v:716`) is stated under `eps_lt_inv5 :47`,
   `eps_gt_neg4inv5 :48` and `eps_small :439`. Its executed transport
   `five_card_colour_view_leak_bound` (`five_card_models.v:360`) re-declares
   `Hypothesis eps_small` (`:351`). At `eps = 1/100` the first two are discharged
   (`kim_centi_lt` `five_card_kim.v:585`, `kim_centi_gt` `:591`) but **`eps_small`
   at `1/100` is proved nowhere**; the `eps = 0` corollary
   `kim_input_private0` (`:749`) takes all three as explicit arguments and proves
   none. The manifest row `five_card_row_biased`
   (`pgg_analysis_manifest.v:1203`) nevertheless reaches `AnalysisBridged` citing
   `colour_view_leak_bound`. The missing proof is arithmetically trivial
   (`0 < 1/5 - 1/100`); the gap is that nobody wrote it.

5. **den Boer's two profile-level correctness theorems are vacuous at
   `s = true`.** `FiveCardKim_protocol_correct` (`den_boer_profile.v:139`) and
   `den_boer_committed_protocol_correct` (`:272`) carry the premise
   `ts_valid fcI_scheme s T`, where `T` is the *fixed* tuple
   `[tuple fc_content (tnth (cast_tuple _ (pi_starts FiveCardKim_PI)) j) | j < 5]`.
   Since `fc_content = id` (`five_card_program.v:185`) and
   `pi_starts FiveCardKim_PI = ord_tuple 5` (`five_card_family.v:138`), that
   tuple is the identity layout, whose decoded row is
   `[:: false; true; false; false; false]`, which has no three consecutive
   hearts. So the premise holds only at `s = false`, and the theorems recover a
   constant rather than the AND. **Machine-checked**: a scratch file proving
   `prem_tupleE`, `prem_decodeE`, `prem_three_consec`,
   `prem_forces_false (s) : ts_valid fcI_scheme s prem_tuple -> s = false` and
   `prem_no_true : ~ ts_valid fcI_scheme true prem_tuple` compiles against the
   built `.vo` files.
   This is not a soundness problem and not a gap in the protocol: the
   layout-carrying theorems `den_boer_run_output` (`den_boer_run.v:28`),
   `den_boer_run_recovers` (`:198`) and `five_card_exec_correct`
   (`five_card_exec.v:273`) prove the real statement, recovery of
   `ab.1 && ab.2`, non-vacuously. The codebase says as much at
   `den_boer_run.v:13-20`. What is misleading is only the docstring at
   `den_boer_profile.v:132-138`, which describes
   `FiveCardKim_protocol_correct` as "the end-to-end guarantee for the five-card
   trick" and "the den Boer member's correctness theorem"; a reader who stops
   there will over-read it. The cheap fix is to restate the premise over
   `tnth (den_boer_layout ab)` instead of the fixed identity layout, or to
   rewrite the docstring to point at `den_boer_run_output`.

6. **A declared axiom with no consumer.**
   `Axiom s5_brings_covering_realised` (`rigidity_s5_instance.v:309`) is
   referenced by nothing in the repository — only the declaration and four
   comments. Its type is itself a global `Parameter realised_by_curve`
   (`reconstruct/curve_realisation.v:69`), deliberately opaque. No S5 result
   depends on it, and correspondingly `manifest/pgg_analysis_status.v:76-79` has
   no `PggAxiom` constructor for it. It is a documentation marker, not a trust
   dependency — but it is a real `Axiom` in the kernel's sense and a reader
   auditing `Print Assumptions` output should know it is inert.

Not in this list, for the record: **the pgl27 chain and the five-card
correctness and secrecy chains carry no undischarged hypothesis and no axiom**
(item 5 above is a vacuous premise, not an assumption).
Every theorem in the fifteen pgl27 files and every correctness and trace-secrecy
theorem of the five-card family is stated in a section whose only declaration is
`Variable R : realType`. The manifest agrees, marking all five non-S5 rows
`BaselineClassicalOnly` (`pgg_analysis_manifest.v:1173,:1184,:1195,:1205,:1215`).

---

## Verification notes

Every `file:line` in this note was read directly. The dependency graph was
extracted from `.Makefile.rocq.d` and filtered to the kept set with a script; the
"no kept consumer" list in (d)(iv) is the complement of a transitive closure over
that graph, not a judgement.

One claim was machine-checked rather than derived: the `s = false` vacuity of
`FiveCardKim_protocol_correct`, item 5 of (d)(v). The scratch file lives outside
the repository and compiles against the built `.vo` files with
`rocq compile $(grep '^-R' _CoqProject | tr '\n' ' ') -w none vac.v`; its final
lemma is `prem_no_true : ~ ts_valid fcI_scheme true prem_tuple`.

`Print Assumptions` was **not** run: the axiom
reachability claims in (c) and (d)(v) are term-level dependency traces through
`grep`, corroborated by the repository's own `AssumptionStatus` annotations in
`manifest/pgg_analysis_manifest.v`. Confirming them mechanically would require
compiling and running `Print Assumptions` on `S5Analysis.exec_correct`,
`S5Analysis.exec_coalition_secrecy`, `PGL27Analysis.exec_view_indist` and
`FiveCardAnalysis.colour_view_leak_bound`.
