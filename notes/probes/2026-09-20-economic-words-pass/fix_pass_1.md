# Fix pass 1 on the economic-words pass (2026-09-20)

Comments-only. Twelve files. Every line below was verified at 80 bytes or
less; comment-stripped token identity against HEAD was checked for all twelve
files and holds. Nothing was compiled.

"Old" is the working-tree text before this fix pass, that is, the text the two
Opus audits read.

---

## Item 1. The column-dominance docstring, two files

### `instances/s5/s5_mixing.v` 394-396

Old:

```
(** s5_cert_bound_col_dominant — each column of the dominating matrix sums
    to at most the residual's diagonal entry in that column.  Column
    dominance, the second of the two slack conditions psd_of_dominant needs. *)
```

New:

```
(** s5_cert_bound_col_dominant — each column of the dominating matrix sums
    to at most the residual's diagonal entry in that column.  Column
    dominance, the second of the two sum conditions psd_of_dominant needs
    beside its two entrywise ones. *)
```

### `instances/pgl27/pgl27_spectral.v` 515-517

Old:

```
(** pgl27_cert_bound_col_dominant — each column of the dominating matrix sums
    to at most the residual's diagonal entry in that column.  Column
    dominance, the second of the two slack conditions psd_of_dominant needs. *)
```

New:

```
(** pgl27_cert_bound_col_dominant — each column of the dominating matrix sums
    to at most the residual's diagonal entry in that column.  Column
    dominance, the second of the two sum conditions psd_of_dominant needs
    beside its two entrywise ones. *)
```

Evidence for the new sentence: `psd_of_dominant`, `security/pgg_mixing.v:939`,
takes four hypotheses:

```
  (forall i j, i != j -> E i j <= A i j) ->
  (forall i j, i != j -> - E i j <= A i j) ->
  (forall i, \sum_(j | j != i) A i j <= E i i) ->
  (forall j, \sum_(i | i != j) A i j <= E j j) ->
```

The first two are entrywise, the last two are the row-sum and column-sum
conditions. The column lemma of each instance file discharges the fourth.

### The sibling row-dominance docstrings: unchanged

Neither sibling said "the first of the two slack conditions" or anything
similar, so neither was touched. Both read, verbatim:

`instances/s5/s5_mixing.v` 382-385:

```
(** s5_cert_bound_row_dominant — each row of the dominating matrix sums to
    at most the residual's diagonal entry in that row.  Row dominance; with
    column dominance it is what makes the residual's quadratic form
    nonnegative without any factorisation of the residual itself. *)
```

`instances/pgl27/pgl27_spectral.v` 503-506:

```
(** pgl27_cert_bound_row_dominant — each row of the dominating matrix sums to
    at most the residual's diagonal entry in that row.  Row dominance; with
    column dominance it is what makes the residual's quadratic form
    nonnegative without any factorisation of the residual itself. *)
```

---

## Item 2. crosses -> hops, two files

### `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v` 1052-1057

Old:

```
    the two marginals the den Boer uniform execution has, where the reading
    and the conjunction are independent outright. The certificate crosses to
    the ideal once and so loses that number once, where the
    input-indistinguishability row crosses twice. Its transfer status is
    IdealFinite, the same the input-indistinguishability row carries, and the
    two certificates compare against the same ideal cut. *)
```

New:

```
    the two marginals the den Boer uniform execution has, where the reading and
    the conjunction are independent outright. The certificate hops to the ideal
    once and so loses that number once, where the input-indistinguishability row
    hops twice. Its transfer status is IdealFinite, the same the
    input-indistinguishability row carries, and the two certificates compare
    against the same ideal cut. *)
```

### `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` 892-900

Old:

```
    distance field, pgl27_word_proximity_close, puts the joint law of a
    coalition's reading with the dealt secret within that number of the same
    joint law under the prior-indexed exact execution, where the reading and
    the secret are independent outright, so the ideal side is the product of
    its two marginals. The certificate crosses to the ideal once and so loses
    that number once, where the input-indistinguishability certificate
    crosses twice. Its transfer status is
    IdealFinite, the same the input-indistinguishability row carries, and the
    two certificates compare against the same ideal cut. *)
```

New:

```
    distance field, pgl27_word_proximity_close, puts the joint law of a
    coalition's reading with the dealt secret within that number of the same
    joint law under the prior-indexed exact execution, where the reading and the
    secret are independent outright, so the ideal side is the product of its two
    marginals. The certificate hops to the ideal once and so loses that number
    once, where the input-indistinguishability row hops twice. Its transfer
    status is IdealFinite, the same the input-indistinguishability row carries,
    and the two certificates compare against the same ideal cut. *)
```

The pgl27 paragraph said "input-indistinguishability certificate crosses
twice" where the ruling's sentence says "row". The ruling's word is true of
this file: the docstring at 840-849 of the same file records that the
input-indistinguishability arm "loses that bound at each of two hops, one per
dealt secret", and the row it publishes concludes at 2^-39, twice the
proximity certificate's 2^-40. The short line at the old 898 is gone.

---

## Item 3. `security/var_dist_joint_law.v` 150-152, proof comment

Old:

```
(* Each marginal of the joint law is within d of the corresponding factor by
   data processing, and replacing the two factors one at a time loses d at
   each hop, so the three hops together give 3 * d. *)
```

New:

```
(* The hypothesis gives the first hop. Each marginal of the joint law is within
   d of the corresponding factor by data processing, so replacing the two
   factors one at a time gives the other two, and the three hops each lose at
   most d, so the total is 3 * d. *)
```

Proof steps that make it true, `var_dist_own_marginals`:

- `H : var_dist J (Mr `x Ms) <= d` is the hypothesis, used as the first
  summand of the first `lerD` after `var_dist_triangle _ (Mr `x Ms) _`.
- `Hr` and `Hs` get each marginal within `d` of the corresponding factor from
  `var_dist_fdistmap` composed with `H`.
- The second `var_dist_triangle _ (Mr `x (fdistmap snd J)) _` splits the
  remainder into the two factor replacements, closed by `var_dist_prodR` and
  `var_dist_prodL`.
- `H3 : 3%:R * d = d + (d + d)` is the three hops summed.

---

## Item 4. `instances/psl211/psl211_reading_constancy.v` 754-757

Old:

```
    below the reciprocal of the group order. The first distance bounds the
    loss of replacing the exact shuffle by one a dealer can perform, the
    second is a certificate's own distance field, and a row over any cut law
    but the group-uniform one loses both. *)
```

New:

```
    below the reciprocal of the group order. The first number bounds the loss of
    replacing the exact shuffle by one a dealer can perform, the second is a
    certificate's own distance field, and an ideal that far from such a cut law
    is within their sum of the group-uniform law. *)
```

Evidence: the statement takes `var_dist (`U psl211_G_pos) W <= d` and
`var_dist W ideal <= eps`, and the proof's first step is

```
have Hclose : var_dist ((`U psl211_G_pos) : R.-fdist cutT) ideal <= d + eps.
  apply: (Order.POrderTheory.le_trans (var_dist_triangle _ W _)).
  exact: lerD HW Hi.
```

so an ideal within `eps` of such a `W` is within `d + eps` of the
group-uniform law, which is the last clause.

---

## Item 5. `manifest/pgg_tableau_syntax.v` 154-155

Old:

```
   written: the fourth component is the only statistical one, and the fifth
   is exact. *)
```

New:

```
   written: the fourth component is an inequality at the first component's
   epsilon, and the fifth is an equation. *)
```

Evidence, from `mk_indistinguishability` itself. The fourth component is

```
    (Hc : forall (R : realType) (idx : amf_index (sp_f x) R),
            var_dist (sw_rho_dist (b R idx)) (u R idx)
            <= sw_bound_eps (b R idx))
```

an inequality whose right side is the epsilon of the first component `b`. The
fifth is

```
    (Hk : ... fdistmap (static_coalition_obs C y) (u R idx)
              = fdistmap (static_coalition_obs C y') (u R idx))
```

an equation of laws.

---

## Item 6. `manifest/pgg_tableau_syntax.v` 79-80, boxed comment

Old (the first line lost its space before the closing delimiter, 80 bytes
each):

```
(* because ssreflect already reserves it, measured on 2026-09-19 by binding it*)
(* in a file that requires nothing but ssreflect.                             *)
```

New (80 bytes each, space before `*)`):

```
(* because ssreflect already reserves it, measured on 2026-09-19 by binding   *)
(* it in a file that requires nothing but ssreflect.                          *)
```

The two lines carry the same words as before, split one word earlier.

---

## Item 7. `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v` 847

Old:

```
   conversion, and only reflexivity reaches it: the refine path ssreflect's
```

New (80 bytes, so the rest of the paragraph is unchanged):

```
   conversion, and only reflexivity reaches it: the refine path that ssreflect's
```

---

## Item 8 and 9a. `instances/pgl27/pgl27_exec.v` 351-353

Old:

```
    commits an input, and the fuel is pgl27_fuel.  The
    dealer-dealt mode is what leaves the instance owing termination alone
    among the three run facts. *)
```

New:

```
    commits an input, and the interpreter fuel is pgl27_fuel.  The dealer-dealt
    mode is what leaves termination as the instance's only obligation among the
    three run facts. *)
```

---

## Item 9b. `instances/s5/s5_exec.v` 363-365

Old:

```
    party commits an input, and the interpreter fuel is 150. The
    dealer-dealt mode is what leaves the instance owing termination alone
    among the three run facts. *)
```

New:

```
    party commits an input, and the interpreter fuel is 150. The dealer-dealt
    mode is what leaves termination as the instance's only obligation among the
    three run facts. *)
```

## Item 9c. `instances/s5/s5_exec.v` 911

Old:

```
    run owing a reconstruction obligation of its own. *)
```

New:

```
    run with a reconstruction obligation of its own. *)
```

## Item 9d. `instances/s5/tableau/s5_tableau_executable.v` 87

Old:

```
    into the record, which is what leaves this mode owing a reconstruction
```

New:

```
    into the record, which is what leaves this mode with a reconstruction
```

---

## Item 10. `instances/s5/s5_exec.v` 936-937

Old:

```
    content readout, so instantiating it at the additive layout uses no
    reduction of this run's own, and the two modes share one decision. *)
```

New:

```
    content readout, so this run uses no reduction of its own to instantiate it
    at the additive layout, and the two modes share one decision. *)
```

Every other clause of the sentence is kept. The claim holds of the
declaration: `s5_supplied_endpoints` is defined as
`supplied_endpointsE s5_profile_endpoints`, with no `vm_compute` and no
reduction step of its own, unlike `s5_supplied_terminates` just above it.

---

## Item 11. "gives a factor" -> "contributes a factor"

### `instances/s5/s5_mixing.v` 480

Old:

```
    of the word gives a factor 1 - gap. *)
```

New:

```
    of the word contributes a factor 1 - gap. *)
```

### `instances/pgl27/pgl27_spectral.v` 106

Old:

```
    one letter of the word gives a factor 1 - gap. *)
```

New:

```
    one letter of the word contributes a factor 1 - gap. *)
```

Both files already say "contributes" for the same fact further down:
`instances/s5/s5_mixing.v:511` and `instances/pgl27/pgl27_spectral.v:587`.

---

## Item 12. `security/pgg_mixing.v` 901-903

Old:

```
    sum of the two squares.  The elementary inequality that lets an
    off-diagonal entry be absorbed by the two diagonal entries it sits
    between. *)
```

New:

```
    sum of the two squares.  The elementary inequality that lets the two
    diagonal entries an off-diagonal entry sits between dominate it. *)
```

"dominate" is not false of the declaration. `abs_prod_le_sqr` states
`2%:R * `|a * b| <= a ^+ 2 + b ^+ 2`, and the lemma directly below,
`pointwise_dom`, uses it to bound an off-diagonal contribution
`e * (a * b)` from below by `- (al * (a ^+ 2 + b ^+ 2) / 2%:R)`, that is, half
of `al` charged to each of the two coordinates `a` and `b` the entry couples.
Those two coordinates are the ones whose diagonal entries carry the row and
column sums in `psd_of_dominant`, and the file's own vocabulary for that
relation is dominance: "dominating matrix", "dominated", "diagonal-dominance
argument", `psd_of_dominant`.

---

## Item 13. "charging" -> "giving mass to", `instances/psl211/psl211_secrecy.v`

### Line 13, boxed header (80 bytes, space before `*)`)

Old:

```
(* prior charging both chiralities, the law already depends on it.            *)
```

New:

```
(* prior giving mass to both chiralities, the law already depends on it.      *)
```

Lines 10-12 of that paragraph did not have to move.

### Lines 37-38, the header index entry (80 bytes each)

Old:

```
(*   psl211_colour_view_dep_k6 == at a prior charging both chiralities, a     *)
(*     six-position coalition's colour view depends on the chirality          *)
```

New:

```
(*   psl211_colour_view_dep_k6 == at a prior giving mass to both chiralities, *)
(*     a six-position coalition's colour view depends on the chirality        *)
```

No word touches `==`: it keeps a space on each side.

### Lines 323-327, the docstring

Old:

```
(** psl211_colour_view_dep_k6 — under a prior charging both chiralities, the
    colour view of the six positions of the mirror representative is not
    independent of the dealt chirality. The five-position threshold is sharp:
    one more position already separates the two block systems, and the
    coalition that achieves it is a block of one of them. *)
```

New:

```
(** psl211_colour_view_dep_k6 — under a prior giving mass to both chiralities,
    the colour view of the six positions of the mirror representative is not
    independent of the dealt chirality. The five-position threshold is sharp:
    one more position already separates the two block systems, and the coalition
    that achieves it is a block of one of them. *)
```

The hypotheses of `psl211_colour_view_dep_k6` are `secretP true != 0` and
`secretP false != 0`, that is, the prior puts nonzero mass on each chirality.

---

## Verification performed

- Comment-stripped token identity against `HEAD` for all twelve files: equal,
  token for token, in every file.
- Every line that differs from `HEAD` in these twelve files: at most 80 bytes.
- The five boxed lines touched (`psl211_secrecy.v` 13, 37, 38 and
  `pgg_tableau_syntax.v` 79, 80): exactly 80 bytes each and each ends with a
  space before `*)`.
- No file was compiled and no git command that writes was run.
