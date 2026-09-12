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
| 11 | alpha = 7/8 exceeds the true lambda_2 | not a kernel claim; the kernel checks the certificate. Python reports lambda_2^2 ~ 0.7442 < 49/64 = 0.7656 | informational |

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

scratchpad/probe_pgl27_rayleigh.v, scratchpad/probe_pgl27_decomposition.v.

## Audit findings

(filled after the soundness and naming audits)
