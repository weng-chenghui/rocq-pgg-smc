# S_5 Schreier spectral certificate

`s5_spectral_certificate.py` is the untrusted search that produced the
tables in `s5_mixing.v`; the kernel checks everything that matters.

## What is certified

For the 5x5 transition matrix Q of the walk on `'I_5` driven by the four
adjacent transpositions (0 1), (1 2), (2 3), (3 4) (`path_gen_tuple 3`):

> for every real column 5-vector v with v_0 + ... + v_4 = 0,
> `<v, Q^2 v> <= alpha^2 <v, v>`, alpha = 181/200.

Equivalently `alpha^2 I - Q^2` is positive semidefinite on the mean-zero
hyperplane. Through `symm_ds_TV_bound` (security/pgg_mixing.v) this gives
`var_dist(Q^L delta_s, uniform) <= sqrt 5 * alpha^L` for every L and s.

## Certificate shape

    M' := alpha^2 I - Q^2 + (c/5) J,     c = 11/50, J the all-ones matrix
    M'  = L D L^T + E                     exactly over the rationals
    D >= 0 entrywise
    E row- and column-diagonally dominated by A := |E| off the diagonal

L is the exact LDL^T of `M' - eps I` (eps = 1/2000) rounded to 1/1000, D
the exact pivots floored to 1/1000, E the exact residual; E and A are
stated over the denominator 10^9 with numerators below 1.4 * 10^6. On a
sum-zero v the J term vanishes, so M' PSD gives the Rayleigh bound. The
generic lemmas `psd_of_ldl` and `psd_of_dominant` (pgg_mixing.v) turn the
identity and the dominance into the quadratic-form inequality; the
identity itself is 25 rational equalities discharged by `lra`.

## History

Until 2026-09-13 the Rayleigh bound was `Axiom s5_rayleigh_Q2_R`, backed
by an exact rational LDL^T whose numerators reached 10^18 and exceeded the
tactic budget. The rounded certificate keeps every number small enough
for in-kernel checking at the same alpha; the axiom is now a lemma.

Numerically the second-largest eigenvalue of Q is 0.9045 (lambda_2^2 =
0.818136 against alpha^2 = 0.819025): alpha is within 0.0005 of the true
gap, which is why den = 1000 and eps = 1/2000 are needed.
