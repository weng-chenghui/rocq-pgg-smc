# Spectral witnesses for PGL(2,7) and S_5, then retire the free-words layer

Date: 2026-09-12. Approved by the user (steps 1-4, including the change to
the S_5 rigidity instance in step 3). EXECUTED 2026-09-13: step 1 in
5a1c862..75e8053, step 2 in 8d584a7, step 3 in dd1ac60, step 4 in
19c5092 and 10dab7c; close-out in docs/style/scan-2026-08-26/P0-P1-CLOSEOUT.md.

## Why

The kept tree's only consumer of `weval_inj` ("the group looks free up to
length L") is `s5_security_witness_1` (instances/s5/rigidity_s5_instance.v),
a `ShuffleMarginalBound` at L = 1 with epsilon = 6/5: vacuous, since a
variation distance never exceeds 1. Every alphabet the four kept instances
use contains an involution or an inverse pair, so `weval_inj` fails from
L = 2 or 3 on; the concept belongs to the Monster-style symbolic route,
which is in legacy/. The all-L security statements the instances do have
are Schreier spectral bounds, which need no `weval_inj`.

## Steps, one commit each (statement-surface gate on every one)

1. PGL(2,7) Rayleigh route (spec notes/20260912-pgl27-rayleigh-design.md):
   new instances/pgl27/pgl27_spectral.v with an in-kernel rounded-LDL^T
   certificate; generic `psd_of_dominant`, `psd_of_ldl`, and the
   inverse-closed Schreier bridge in a NEW section of security/pgg_mixing.v.
   Adds only; existing statements untouched. `symm_ds_TV_bound` re-derived
   from the new bridge (proof body only).
2. Discharge `Axiom s5_rayleigh_Q2_R` (instances/s5/s5_mixing.v:186) with
   the same certificate machinery at the SAME alpha = 181/200: den = 1000,
   c = 11/50, eps = 1/2000 (soundness audit S5). Generator script
   instances/s5/s5_spectral_certificate.py rewritten to emit the rounded
   certificate; the old `s5_sos_*` lists and the certificate .md are
   replaced. Axiom count of the kept tree drops from 2 to 1
   (`s5_group_order_eq` remains). Statement of the discharged lemma is the
   axiom's statement verbatim.
3. `s5_rigidity`'s security half becomes the spectral witness: the orphan
   `Section s5_rigidity_cryptographically_secure` (rigidity_s5_instance.v:367)
   is folded into the main definition, `s5_security_witness_1` and
   `s5_endpoint_bound_fiber` are deleted. This CHANGES the exported
   `s5_rigidity` (epsilon from the vacuous 6/5 to sqrt 5 * (181/200)^L at
   the chosen L); recorded as an authorised surface change. The
   `s5_analysis` facade rows and the manifest row `s5_row_word` that cite the
   old witness are updated in the same commit.
4. Relocation wave: `weval_inj`, `weval_injB`, `weval_injP`,
   `weval_inj_search_space`, `gen_inj_weval_inj1` (protocol/pgg_interface.v),
   `security_witness_fiber`, `security_witness_endpoint_inj`,
   `var_dist_endpoint_direct` and the `lfree` sections
   (reconstruct/algebraic_rigidity.v, security/pgg_collusion_bound.v),
   `security_witness_schreier`'s `Hlfree` variant (security/pgg_schreier.v),
   `raag_weval_inj1` (groups/pgg_raag.v), `s5_weval_inj1`
   (instances/s5/pgg_raag_s5.v), and the whole of groups/pgg_weval_inj.v
   (reflection procedure plus the OC data) move to
   legacy/security/pgg_free_words.v (and legacy/groups/pgg_weval_inj.v).
   `achievable` and `search_space` stay if a kept lemma other than the
   moved ones uses them (cover_tradeoff.v's search_space_leG does; check
   at execution). Gate: surface diff is exactly the moved names, ctxhash
   unchanged for everything that stays.

After step 4 the kept tree states security in exactly two forms: exact
independence (view / trace secrecy) and Schreier spectral decay.

## Verification per step

statement_surface.py --rev HEAD before/after; full make -j8 EXIT=0 from a
captured log; fixpoint 0; Print Assumptions on every new headline listing
only propositional_extensionality, functional_extensionality_dep,
constructive_indefinite_description.
