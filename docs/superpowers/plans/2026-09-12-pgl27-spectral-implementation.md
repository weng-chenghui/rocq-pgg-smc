# PGL(2,7) spectral bound: implementation plan

Spec: notes/20260912-pgl27-rayleigh-design.md (all ledger rows GO; audits
folded). Probe sources (verbatim proof bodies to copy):
scratchpad/probe_pgl27_generic.v, probe_pgl27_cert.v,
probe_pgl27_decomposition.v (scratchpad =
/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc/8c60a23f-3425-4b84-97af-e3668389e61c/scratchpad).
Names follow the naming audit (spec section "Audit findings", item 4).

Gate on every task: `python3 scripts/statement_surface.py --rev HEAD` vs the
working tree shows additions only (task 3 also shows the authorised
un-Local changes); per-file compile via `make <file>.vo`; `Print Assumptions`
on every new lemma lists at most propositional_extensionality,
functional_extensionality_dep, constructive_indefinite_description. One
commit per task; no --amend, no --no-verify.

## Task 1 — security/pgg_mixing.v: inverse-closed bridge (new section)

Append, after `End schreier_TV_bound`, a NEW section:

```
Section schreier_inv_closed.
Variable R : realType.
Variable m n' : nat.
Let Tg := m.+1.
Let N := n'.+2.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Variable f : 'I_Tg -> 'I_Tg.
Hypothesis fK : involutive f.
Hypothesis sigmas_fV :
  forall k : 'I_Tg, tnth sigmas (f k) = ((tnth sigmas k)^-1)%g.
Lemma schreier_transition_symm_inv_closed : ...      (probe: schreier_transition_symm_invclosed)
Lemma schreier_transition_col_inv_closed (j : 'I_N) : ...   (probe: ..._col_invclosed)
Lemma schreier_endpoint_eq_Q_power_inv_closed (L : nat) (s a : 'I_N) : ...
Lemma symm_ds_TV_bound_inv_closed (alpha : R) (L : nat) (s : 'I_N) :
  0 <= alpha -> (Rayleigh premise) -> var_dist ... <= Num.sqrt N%:R * alpha ^+ L.
End schreier_inv_closed.
```

Statements and proofs verbatim from probe_pgl27_generic.v lines 42-140 with
the `_invclosed` suffix renamed `_inv_closed` and the dead `alpha <= 1`
premise dropped from `symm_ds_TV_bound_inv_closed` (the probe carried it
unused; `symm_ds_TV_bound_cV` never needs it). Existing lemmas untouched;
`symm_ds_TV_bound`'s body is NOT rewritten in this task (keeps the diff
comment-free and additions-only; the re-derivation is task 6).

Docstrings: fact + position, e.g. for the symmetry lemma: "Under an
inverse-closed generator multiset the Schreier transition matrix is
symmetric: the walk treats a step and its reverse alike. This is the one
structural input the doubly-stochastic mixing bound needs beyond row
stochasticity, and it is weaker than the involution hypothesis the
adjacent-transposition instances satisfy (f = id)."

Header inventory of pgg_mixing.v gains the four names.

## Task 2 — security/pgg_mixing.v: certificate PSD lemmas (new section)

Append a NEW section `Section psd_certificate` with, verbatim from
probe_pgl27_generic.v lines 162-end: `cV_quad_formE`, `big_offdiag_exchange`,
the `2|ab| <= a^2 + b^2` helper, `psd_of_dominant`, `psd_of_ldl` (matrix
argument named `A`, not `L`), and section `sumzero_shift` with
`sumzero_const_form`, `rayleigh_of_shift`. Docstring for `psd_of_dominant`:
"A matrix whose off-diagonal entries are dominated, row- and column-wise,
by a nonnegative matrix whose sums stay below the diagonal has a
nonnegative quadratic form. Stated with the dominating matrix A as data so
that a concrete certificate discharges every premise by linear arithmetic
on literals; this is the residual half of a rounded LDL^T certificate."

## Task 3 — instances/pgl27/pgl27_mixing.v: un-Localise the alphabet facts

Turn `Local Definition inv_letter` (:154), `Local Lemma ptbl_sym` (:332),
`ptbl_inj` (:350), `ptbl_geninv2` (:657), `ptbl_inv_letter` (:670) into
exported declarations under the names `pgl27_inv_letter`, and keep the
lemma names (they are the file's own vocabulary). Authorised surface
change: exactly these five additions. If the existing Local names are
consumed by later Local proofs in the file, keep an alias
`Local Notation` so nothing else changes. Compile: `make
instances/pgl27/pgl27_mixing.vo`; dependents recompile (pgl27_word_privacy
etc.) with no edits.

## Task 4 — instances/pgl27/pgl27_spectral.v (new file, in _CoqProject after pgl27_mixing.v)

Header: fact + position, and the honesty note from the spec (per-seat
endpoint marginal, not coalition view; weval_inj fails at L >= 2 on the
symmetrized alphabet so only the asymptotic witness is packaged).

Contents, in order, verbatim from probe_pgl27_cert.v and
probe_pgl27_decomposition.v with the audited names:

1. `pgl27_alpha_R (R) : R := 7%:R / 8%:R`, `pgl27_alpha_R_ge0`,
   `pgl27_alpha_R_lt1`, `pgl27_gap_R`, `pgl27_gap_R_pos`, `pgl27_gap_R_le1`,
   `pgl27_gap_R_one_minus` (mirror s5_mixing.v section 1).
2. `pgl27_inv_letterK : involutive pgl27_inv_letter` (probe pgl27_sym_swapK)
   and `pgl27_sym_sigmas_inv_closed` (probe pgl27_sym_sigmas_invclosed,
   with `inv_perm_invol` folded in as a `have`, or reusing `ptbl_geninv2`
   from task 3 if it states the same fact).
3. `pgl27_Q_tbl`, `pgl27_Q`, `sym_tbl` (rename `pgl27_letter_tbl`),
   `perm_inv_val` helper (rename `pgl27_perm_inv_val`, Local),
   `pgl27_gen_val` (probe sym_val), `pgl27_gen_countE`, `pgl27_Q_E`.
4. Certificate tables `pgl27_shift_tbl`, `pgl27_cert_lower_tbl`,
   `pgl27_cert_diag_tbl`, `pgl27_cert_resid_tbl`, `pgl27_cert_bound_tbl`;
   `pgl27_cert_mx` (probe tbl_mx); `pgl27_shift_mx`, `pgl27_cert_lower`,
   `pgl27_cert_diag`, `pgl27_cert_resid`, `pgl27_cert_bound`;
   `pgl27_shift_mxE` (probe pgl27_Mp_E); `pgl27_cert_identity`;
   `pgl27_cert_diag_ge0`, `pgl27_cert_resid_le_bound`,
   `pgl27_cert_resid_ge_neg_bound`, `pgl27_cert_bound_row_dominant`,
   `pgl27_cert_bound_col_dominant`.
5. `pgl27_rayleigh_Q2` proved from 3-4 via `rayleigh_of_shift`,
   `psd_of_ldl`, `psd_of_dominant` (this is the one proof not in a probe as
   a single lemma; its pieces all are).
6. `pgl27_spectral_convergence` (headline) via
   `symm_ds_TV_bound_inv_closed`; `pgl27_spectral_convergence_gap`;
   `pgl27_spectral_convergence_weighted` stated as
   `endpoint_dist_weighted R 6 4 L pgl27_sym_sigmas Wuni s` if that form
   compiles, else the probe's fdistmap form; `pgl27_schreier_cert` in term
   mode (monster precedent, now legacy); `pgl27_security_asymptotic`.
7. Reference to instances/pgl27/pgl27_spectral_certificate.py in the
   header as the untrusted generator of the tables.

Compile budget: the certificate identity took 148 s in the probe; accept
for now, record the time in the commit message.

## Task 5 — docs

Update instances/pgl27/README-style header lists if any; add the four new
manifest-relevant names nowhere (manifest rows unchanged in this campaign).
Update the close-out note with the axiom count (unchanged: the file adds
none) and the Print Assumptions transcript.

## Task 6 (optional, proof-body only) — re-derive symm_ds_TV_bound

Replace the body of `symm_ds_TV_bound` by an application of
`symm_ds_TV_bound_inv_closed` at f = id (`sigmas_invol` gives
`tnth sigmas k = (tnth sigmas k)^-1` via `mulgV`-style reasoning). Statement
untouched; surface identical.
