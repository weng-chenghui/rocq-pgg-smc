# PGL(2,7) Rayleigh route: an all-L spectral bound with an in-kernel certificate

Date: 2026-09-12. Status: spec under probe (rocq-probe-first-spec). Executes
after the legacy/ move; every file named here is in the kept set.

## Goal

Give the PGL(2,7) word shuffle the same asymptotic security statement the S_5
and Kim instances already have: for every word length L and every card
position s,

    var_dist (endpoint marginal at s of rho_from_words L pgl27_sym_sigmas)
             (uniform on 'I_8)
      <= sqrt 8 * (7/8)^L.

Today PGL(2,7) has only the fixed-length certificate `pgl27_word_mixing`
(L = 200, 2^-40, instances/pgl27/pgl27_mixing.v:1021). The new statement is
the per-seat endpoint marginal bound `ShuffleMarginalBound` consumes; it is
NOT the coalition-view bound (`pgl27_word_view_indist` stays the L = 200
coalition statement; an all-L coalition bound would need Cayley-graph mixing
on the 336 group elements and is out of scope).

## Approaches considered

A. In-kernel Rayleigh certificate (chosen). Reuse `symm_ds_TV_bound`'s
   machinery (security/pgg_mixing.v) and discharge its Rayleigh premise by a
   sum-of-squares certificate whose numbers are small enough for
   `mathcomp-algebra-tactics` (`lra`/`ring`, installed 1.2.7, already imported
   by lib/proba_entropy_ext.v). No new axiom.
B. External certificate + Axiom, as instances/s5/s5_mixing.v does
   (`Axiom s5_rayleigh_Q2_R`, Python LDL^T with 10^18 numerators). Rejected:
   adds a trust boundary the repo's rules discourage, and A's rounding trick
   makes it unnecessary.
C. Doeblin minorisation (Q^3 entrywise >= 1/125, contraction 117/125 per
   three steps, ~0.978 per step). Fully in-kernel with tiny numbers but a
   far weaker rate and a new generic contraction lemma. Kept as fallback if
   A's arithmetic probe fails.

## Mathematics of A

Q := schreier_transition R pgl27_sym_sigmas, 8x8, entries k/5. The
generator multiset is inverse-closed (tr, tr^-1, sc, sc^-1, inv with inv an
involution), so Q is symmetric and doubly stochastic; this is the only new
generic fact (the existing bridge assumes every generator is an involution).

Numerically lambda_2(Q) ~ 0.8626 on the sum-zero subspace; alpha := 7/8.

Certificate (generated and checked by
instances/pgl27/pgl27_spectral_certificate.py, exact rationals):

    M' := alpha^2 I - Q^2 + (1/32) J          (J = all-ones matrix)
    M'  = L D L^T + E   exactly,
    D >= 0 entrywise, E row- and column-diagonally dominant, E_ii >= 0,

with L rounded to 1/100, D floored to 1/100, E the exact residual
(common denominator 1.6e9, numerators <= ~2e7). Then for every v,
v^T M' v = sum_k D_k (L^T v)_k^2 + v^T E v >= 0, and for sum-zero v the J
term vanishes, so <v, Q^2 v> <= alpha^2 <v, v>.

## Claim ledger

| # | Claim | Passing evidence | Status |
|---|---|---|---|
| 1 | `symm_ds_TV_bound` (pgg_mixing.v:658) needs only Q symmetric doubly stochastic; the involution hypothesis is used solely by `schreier_transition_symm` and `..._doubly_stochastic_col` | probe: generic lemmas `schreier_transition_symm_invclosed` / `..._col_invclosed` under an index bijection f with sigma_(f k) = sigma_k^-1, Qed; `symm_ds_TV_bound_invclosed` Qed | pending |
| 2 | pgl27_sym_sigmas is inverse-closed via f = [1;0;3;2;4] | probe: `pgl27_sym_sigmas_invclosed` Qed by computation (`permE`, `vm_compute`, `perm_invE`/`mulVg`) | pending |
| 3 | The 64 entries of `schreier_transition R pgl27_sym_sigmas` equal the literal table Q (k/5) | probe: `pgl27_Q_E` Qed; `schreier_gen_count` computed per (i,j) | pending |
| 4 | Generic: S = L *m diag_mx D *m L^T + E with D >= 0 and E doubly diagonally dominant implies v^T S v >= 0 for all v | probe: `psd_of_ldl_cert` Qed at general n (uses 2|ab| <= a^2 + b^2) | pending |
| 5 | The certificate identity M' = L D L^T + E holds entrywise with the literal tables | probe: `pgl27_cert_identity` Qed by `matrixP` + `mxE` + bigop expansion + `lra`; wall time recorded | pending |
| 6 | D >= 0 and E dominance hold for the literal tables | probe: `lra`/`norm_num`-style on 8 + 16 literal inequalities | pending |
| 7 | For sum-zero v, v^T J v = 0, hence v^T (alpha^2 I - Q^2) v = v^T M' v | probe: `sumzero_J` Qed | pending |
| 8 | Headline `pgl27_spectral_convergence` composes 1-7 through `symm_ds_TV_bound_invclosed` | decomposition probe: headline Qed from Admitted supports | pending |
| 9 | Transfer to the weighted law: `rho_weighted_is_uniform` (pgg_weighted_words.v:146) rewrites `rho_from_words_weighted _ Wuni` to `rho_from_words` | probe: one rewrite at m = 4, N'' = 6, L arbitrary | pending |
| 10 | Packaging: `SchreierCertificate` value `pgl27_schreier_cert` with sc_lambda_gap = 1/8, and `SecurityAsymptotic` via `security_witness_schreier_asymptotic` | probe: the two Definitions typecheck at pgl27_sym_sigmas (m = 4, n' = 6) | pending |
| 11 | alpha = 7/8 exceeds the true lambda_2 | not a kernel claim; the kernel checks the certificate. Exact Sturm count (soundness audit): no eigenvalue other than 1 has modulus >= 7/8; lambda_2 = 0.8626490514 | informational |

### Probe results (2026-09-12)

All three probe files compile. probe_pgl27_generic.v and probe_pgl27_cert.v
have zero Admitted; probe_pgl27_decomposition.v keeps exactly its four
intended Admitted supports and derives the headline, the weighted transfer,
the gap lemmas and `pgl27_schreier_cert` (Defined) from them.

| Row | Verdict | Evidence |
|---|---|---|
| 1 | GO | `schreier_transition_symm_invclosed`, `..._col_invclosed`, `schreier_endpoint_eq_Q_power_invclosed` (replayed: the original does carry sigmas_invol) and `symm_ds_TV_bound_invclosed` Qed; Print Assumptions = the three classical axioms only |
| 2 | GO | `pgl27_sym_sigmas_invclosed` Qed, closed under the global context; inv_perm reached as `tnth pgl27_gens (Ordinal 2)` (Local in pgl27_group.v) |
| 3 | GO | `pgl27_Q_E` Qed via `pgl27_gen_countE` (cardinality as a 5-term sum over the letter table) + 64-way case split + vm_compute; mutation (row 7 last entry 4 -> 3) fails with "No applicable tactic" |
| 4 | GO | `psd_of_dominant`, `psd_of_ldl` Qed at general n; classical axioms only |
| 5 | GO | `pgl27_cert_identity` Qed (matrixP, mxE, 8-term expansion, lra); whole cert probe compiles in 148 s wall; mutation (last D entry 1 -> 2) fails with "Cannot find witness" |
| 6 | GO | `pgl27_Dc_ge0`, `pgl27_Ec_le_Ac`, `pgl27_Ec_ge_negAc`, `pgl27_Ac_row_dominant`, `pgl27_Ac_col_dominant` Qed |
| 7 | GO | `sumzero_const_form`, `rayleigh_of_shift` Qed |
| 8 | GO | headline Qed from the Admitted supports; Print Assumptions lists exactly the four supports plus the classical axioms |
| 9 | GO | `rho_weighted_is_uniform` rewrites directly at `fdist_uniform (card_ord 5)` (no eq_irrelevance needed) |
| 10 | GO | `pgl27_schreier_cert` Defined; `pgl27_security_asymptotic` typechecks |

Cost note: the 64-entry certificate identity dominates compile time (about
two minutes). Acceptable for one permanent file; the implementation plan
records the per-entry route so a faster variant (per-row lemmas, or
`vm_compute` on an int-scaled form) can replace it later without changing
the statement.

## Soundness invariants

- No new Axiom, Parameter, or Conjecture; `Print Assumptions` on the
  headline must be closed under the global context except for the classical
  axioms the real-number layer already carries (record the exact list).
- The bound is the per-seat endpoint marginal distance under the UNIFORM word
  law; average over words, worst case over seats and over L. No adversary,
  no computational assumption.
- Vacuity: sqrt 8 * (7/8)^L < 1 exactly when L >= 8; at L = 200 the bound is
  about 2^-37, weaker than the fixed-L 2^-40 certificate, as expected of a
  spectral bound with a sqrt N prefactor.
- Type honesty: an inequality between two reals (variation distances), not a
  statement about coalition views.
- Cited library objects: `symm_ds_TV_bound`, `schreier_transition`,
  `schreier_gen_count`, `cV_inner` (pgg_mixing.v / pgg_schreier.v);
  `rho_weighted_is_uniform` (pgg_weighted_words.v); `SchreierCertificate`,
  `security_witness_schreier_asymptotic` (pgg_schreier.v);
  `diag_mx`, `mulmx`, `trmx`, `mxE`, `big_ord_recl` (mathcomp matrix/bigop);
  `lra` (mathcomp algebra_tactics). Each is exercised in the probe at the
  real carrier `'M[R]_8`, `R : realType`.

## Deliverable file

instances/pgl27/pgl27_spectral.v (new): certificate tables as literals,
`pgl27_Q_E`, `pgl27_rayleigh_Q2`, `pgl27_spectral_convergence`,
`pgl27_spectral_convergence_gap`, `pgl27_schreier_cert`,
`pgl27_security_asymptotic`. Generic lemmas go to security/pgg_mixing.v
(inverse-closed bridge) and a small new section there for the certificate
PSD lemma. Existing statements are not changed.

## Probe files (kept, never imported)

scratchpad/probe_pgl27_generic.v (claims 1, 4, 7),
scratchpad/probe_pgl27_cert.v (claims 2, 3, 5, 6),
scratchpad/probe_pgl27_decomposition.v (claims 8, 9, 10).

## Audit findings

### Naming / precedent audit (2026-09-12, Opus, NO-GO pending fixes; all folded in below)

1. `tr_perm`, `sc_perm`, `inv_perm` are `Local Definition`s in
   pgl27_group.v:84-86; only `pgl27_gens` is exported. Claim 2 is restated
   through `tnth pgl27_gens (@Ordinal 3 k isT)`. ACCEPTED.
2. pgl27_mixing.v already holds the alphabet pairing and its facts as
   `Local`s: `inv_letter` (:154, the table [:: 1; 0; 3; 2; 4]),
   `ptbl_inv_letter` (:670), `ptbl_sym` (:332), `ptbl_inj` (:350),
   `ptbl_geninv2` (:657). The permanent file un-Localises and reuses them;
   `pgl27_sym_swap` becomes `pgl27_inv_letter` (the file's own word) and
   `inv_perm_invol` is folded into `pgl27_sym_sigmas_inv_closed`. ACCEPTED.
3. Claim 9 is stated as `endpoint_dist_weighted R 6 4 L pgl27_sym_sigmas
   Wuni s` (pgg_weighted_words.v:99), the form `pgl27_endpoint_mixing`
   (pgl27_mixing.v:1037) already uses. ACCEPTED.
4. Names: `pgl27_alpha_R`, `pgl27_gap_R` (mirror s5); headline
   `pgl27_spectral_convergence` plus `pgl27_spectral_convergence_gap` (no
   `_proved` status suffix); suffix `_inv_closed` (mathcomp `invr_closed`,
   repo `elem_closed`); `pgl27_shift_mx` for M'; `pgl27_cert_lower`,
   `pgl27_cert_diag`, `pgl27_cert_resid`, `pgl27_cert_bound` for L, D, E, A;
   `pgl27_cert_mx` for the table-to-matrix helper (`tbl` is the group
   file's word for permutation tables); `psd_of_dominant`, `psd_of_ldl`,
   `rayleigh_of_shift`, `sumzero_const_form`, `_E` suffixes kept. In
   `psd_of_ldl` the matrix argument is `A`, never `L` (word length
   everywhere else). ACCEPTED.
5. `symm_ds_TV_bound` carries a dead hypothesis `alpha <= 1` (its body
   `symm_ds_TV_bound_cV` :501 never uses it). The inverse-closed variant
   drops it; the old statement is untouched. ACCEPTED.
6. Placement: `statement_surface.py`'s ctxhash covers every enclosing
   Variable/Hypothesis, so adding `f` and its hypotheses to an existing
   section of pgg_mixing.v would silently change the surface of four
   exported lemmas. The inverse-closed bridge opens a NEW section; the PSD
   lemmas take a new section too. Gate: `statement_surface.py --rev HEAD`
   before/after shows only additions. ACCEPTED.
7. Claim 10's only `MkSchreierCertificate` precedent is now
   legacy/instances/monster/rigidity_monster_instance.v:328 (term-mode
   construction). The kept tree builds no SchreierCertificate today;
   pgl27's will be the first. The `@` on `SchreierCertificate` is
   redundant. ACCEPTED (precedent cited as legacy).
8. Style: docstrings `(** name — ... *)` on every permanent declaration;
   no `0%R` inside ring_scope; line width <= 80. ACCEPTED.

### Soundness audit (2026-09-12, Opus, GO; evidence in scratchpad/audit_sound_*)

1. Ledger row 1 corrected: `sigmas_invol` is consumed by THREE lemmas,
   `schreier_transition_symm` (:557), `..._doubly_stochastic_col` (:584)
   and `schreier_endpoint_eq_Q_power` (:605, through its symmetry
   argument). Inverse-closure suffices for each, since
   #{k : sigma_k j = i} = #{k : sigma_k i = j} through the bijection
   k -> f k. Involutions are the f = id case, so the permanent file derives
   the old `symm_ds_TV_bound` from the new bridge instead of duplicating
   the machinery (proof-body change only; statement untouched). ACCEPTED.
2. "the only new generic fact" was wrong: `psd_of_dominant` and
   `psd_of_ldl` are new generic facts too (no PSD, Gershgorin or
   diagonal-dominance lemma exists in mathcomp, infotheo or the repo).
   ACCEPTED.
3. Claim 11 upgraded from numeric to exact: the auditor's independent
   exact-rational recomputation reproduces every table (Q, M', L, D, E, A)
   and the identity M' = L D L^T + E over the rationals; charpoly(Q) =
   x^8 - (6/5)x^7 - (21/25)x^6 + (146/125)x^5 + (99/625)x^4 - (38/125)x^3
   - (22/15625)x^2 + (1368/78125)x + 117/78125, and a Sturm count shows
   no eigenvalue other than 1 has |lambda| >= 7/8; lambda_2 =
   0.8626490514. lambda_min(E) = 0.0077 > 0 and lambda_min(M') = 1/64
   exactly (set by the all-ones direction alpha^2 - 1 + c, so c = 1/4 is
   the binding parameter with 1/64 of room). ACCEPTED.
4. `weval_inj` FAILS for pgl27_sym_sigmas at every L >= 2 (the words
   (0,1) and (1,0) both evaluate to the identity, since letter 1 is the
   inverse of letter 0). Hence `security_witness_schreier` (which takes a
   weval_inj premise) is unavailable at the symmetrized alphabet; only
   `security_witness_schreier_asymptotic` is. The deliverable states this
   in the file header. ACCEPTED.
5. Classical baseline recorded verbatim: `Print Assumptions` on
   `symm_ds_TV_bound`, `schreier_endpoint_eq_Q_power`,
   `rho_weighted_is_uniform` and `pgl27_word_mixing` lists exactly
   `propositional_extensionality`, `functional_extensionality_dep`,
   `constructive_indefinite_description`. The headline must list nothing
   beyond these three. ACCEPTED.
6. Certificate numbers quoted at the reduced denominator: E and A over
   10^6 with largest numerator 27934; L over 100; D over 100; M' over 1600.
   ACCEPTED (section "Mathematics of A" corrected below).
7. Claim 9 hazard: `rho_weighted_is_uniform` is stated at
   `fdist_uniform card_Tg` where `card_Tg : #|'I_Tg| = Tg.-1.+1` is a
   section-local proof term; the probe writes `fdist_uniform (card_ord 5)`.
   Same type, different proof term; the rewrite may need `eq_irrelevance`
   or the statement is made at `endpoint_dist_weighted ... Wuni` as the
   naming audit already asked. ACCEPTED.
8. `Axiom s5_rayleigh_Q2_R` (instances/s5/s5_mixing.v:186) is dischargeable
   by the same route WITHOUT changing its alpha = 181/200: den = 1000,
   c = 11/50, eps = 1/2000, D = [237/1000; 23/125; 103/500; 343/1000;
   1/1000], E over 10^9 with largest numerator 1399700, smallest row slack
   11/10^6. At den = 100 the smallest alpha of the form k/100 with a
   certificate is 91/100 (90/100 is below lambda_2 = 0.9045). Recorded as
   a follow-up task, not part of this deliverable.
9. Non-vacuity confirmed: sqrt 8 * (7/8)^L < 1 exactly from L >= 8
   (L = 7 gives 1.1107, L = 8 gives 0.9719); at L = 200 the bound is
   2^-37.03. The hypothesis set of `psd_of_dominant` is satisfiable
   (audit_sound_vac.v: n = 1 and n = 2 instances proved) and is a real
   restriction (a negative E fails it).

### Corrected numbers (supersede "Mathematics of A")

L rounded to 1/100, D floored to 1/100, E the exact residual with common
denominator 10^6 and numerators at most 27934; A = |E| off the diagonal.
Row slacks E_ii - sum_{j<>i} A_ij: 9/1600, 173/40000, 7993/10^6,
5529/10^6, 4311/10^6, 989/250000, 8481/10^6, 1081/200000.
