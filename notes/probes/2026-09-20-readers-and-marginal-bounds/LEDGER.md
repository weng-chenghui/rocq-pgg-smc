# Ledger: a second reader at Sampled, and one-seat marginal bounds

Probe of `notes/20260920-readers-and-marginal-bounds-probe-design.md`, rows
R1-R10. No production file was edited. Everything below compiled on
2026-09-20/21 against the tree at branch `feat/tableau-extensions-probe`,
Rocq 9.0.0, through the lock wrapper, capped at 900 s.

## Flow: how a trace theorem becomes a proposition at a reader

Accumulated value is the published variation distance, the sum of absolute
differences (twice the literature's total variation).

```
reader  canonical := static_coalition_obs                     -- 0      (definition)
reader  trace     := pgl27_coalition_trace                    -- 0      (definition)
prop    P(r,c)    := ReaderIndistinguishabilityPropAt sa r c  -- 0      (schema)
cite    pgl27_word_trace_indistinguishability                 -- 2^-39  (theorem, #|C| <= 3)
seat    P(trace, 2^-39)                                       -- 2^-39  (R4)
factor  canonical = id . trace   (pgl27_coalition_trace_E)    -- 2^-39  (R5)
derive  P(canonical, 2^-39)      (var_dist_fdistmap)          -- 2^-39  (R3, number unchanged)
compare indistinguishability_tail (pgl27_word_cert)           -- 2^-39  (= 2^-40 + 2^-40)
link    pgl27_content_traceE                                  -- 2^-39  (R7, cited)
-- outside the security properties, no constructor of SecurityEvidence:
prop    SeatMarginalPropAt sa i ideal c                       -- (own)  (R8)
seat    s5_exec_endpoint_bound                                -- sqrt 5 * alpha^L
seat    CutMarginalPropAt (five_card_repeated_endpoint_lt)    -- 2^-40  (strict, widened by ltW)
vacuity SeatMarginalPropAt _ _ 2                              -- 2      (R9, holds always)
```

Monad verdict: none. The reader generalisation is a reindexing, a functor from
static readers and factorisation maps into Prop ordered by implication;
post-processing is functoriality along a factorisation arrow, not a bind. The
Tableau's own `tableau_bind` is untouched, and `StackAt Sampled` does not
change.

Interfaces through which each existing result enters:

| existing result | enters through |
|---|---|
| `pgl27_word_trace_indistinguishability` | `exact:` at `@`-applied form, after `pgl27_word_cut_distE` |
| `pgl27_coalition_trace_E`, `pgl27_static_obsE` | the factorisation hypothesis of R3 |
| `var_dist_fdistmap` (`pgg_collusion_bound`) | the proof of R3 |
| `pgl27_view_indep` | the independence field of R6 at the trace reader |
| `pgl27_content_traceE` | R7, cited, not reproved |
| `indistinguishability_tail`, `pgl27_word_cert` | the comparison route of R5 |
| `s5_exec_endpoint_bound`, `five_card_repeated_endpoint_lt` | `exact:` / `ltW` at R8 |
| `var_dist_le2` (`lib/var_dist_supp.v`) | R9 |

## Files

| file | rows | compile |
|---|---|---|
| `r_framework.v` | R1, R2, R3, R6 framework part, R8 definitions, R9 | exit 0, 7 s |
| `r_pgl27.v` | R4, R5, R6 trace part, R7 | exit 0, 4 s |
| `r_marginals.v` | R8 instances | exit 0, 4 s |
| `a1_assumptions.v` | R10 | exit 0, 16 s |

Message-reading and bisect files, kept: `b1_bisect_attempt_1.v`,
`b2_bisect_attempt_1.v`, `b2_bisect_attempt_2.v`, `d1_goal_shape.v`,
`d2_arities.v`, `f1_c6_message.v`, `f2_c7_message.v`, `f3_c8_message.v`,
`f4_marginal_message.v`, `f5_r2_mutation_message.v`, `f6_m1_message.v`,
`m1_trace_reader_erefl.v`, `r_pgl27_attempt_1.v`. Zero `Admitted`, zero
`Abort` outside `d1_goal_shape.v` (which aborts a goal it only prints), zero
`Axiom`.

Files that do NOT compile, kept on purpose, none of them required by
anything:

- `b2_bisect_attempt_1.v`: the `Timeout`-guarded `ltac:()` bisect whose
  one-liner mis-parses. Fails with "unresolved implicit arguments". Kept
  because that misleading message is the point of trap 2 below.
- `b2_bisect_attempt_2.v`: the same bisect with ordinary proofs. Runs until
  the 300 s cap at `rewrite (Hfun x) (Hfun x') -!fdistmap_comp`, which is how
  the divergence of trap 1 was located.
- `r_pgl27_attempt_1.v`: the first draft of `r_pgl27.v`, before the `@`
  fix. Fails at `exact: (pgl27_word_trace_indistinguishability R C x x' HC)`
  with "Cannot apply lemma", trap 3.
- The six `f*_message.v` files and `d1_goal_shape.v` are meant to fail or to
  print: each `f*` reproduces one `Fail` guard without the `Fail`, so exits 1
  with the quoted message, and `d1_goal_shape.v` compiles (exit 0) but only
  prints goals.

## Rows

### R1 GO

`r_framework.v`, `StaticReader`, `coalition_reading_reader`.

```coq
Record StaticReader := MkStaticReader {
  sr_T : {set seats} -> finType ;
  sr_read : forall C : {set seats},
    ex_inputT E -> pgg_gT (mp_M (instance_profile A)) -> sr_T C }.

Definition coalition_reading_reader : StaticReader :=
  @MkStaticReader (fun _ => [the finType of {ffun seats -> cards}])
    (@static_coalition_obs A E).
```

`seats := 'I_(pi_T' (mp_PI (instance_profile A))).+1`,
`cards := 'I_(pgg_N' (mp_M (instance_profile A))).+1`. The value type of
`static_coalition_obs C x g` at the pinned carrier is
`[the finType of {ffun seats -> cards}]`, printed by
`coalition_reading_readerTE`, closed by `erefl`. The canonical reader's
reading is the framework's own, `coalition_reading_readE`, also `erefl`.

Departure from the spec: the spec wrote `sr_read : forall C, ex_inputT E ->
cut -> sr_T C` with "cut" unnamed; the cut carrier is
`pgg_gT (mp_M (instance_profile A))`.

### R2 GO

`r_framework.v`, `reader_indistinguishability_canonicalE`.

```coq
Lemma reader_indistinguishability_canonicalE
    (cert : IndistinguishabilityCert sa) (c : R) :
  ReaderIndistinguishabilityPropAt (coalition_reading_reader E) c
  = IndistinguishabilityPropAt cert c.
Proof. exact: erefl. Qed.
```

Closed by conversion, for every certificate and every number. The reader form
is

```coq
Definition ReaderIndistinguishabilityPropAt (r : StaticReader E) (c : R)
    : Prop :=
  forall (C : {set seats}) (x x' : ex_inputT E),
    (#|C| < profile_k (instance_profile A))%N ->
    var_dist (fdistmap (sr_read r C x) (sa_cut_dist sa))
             (fdistmap (sr_read r C x') (sa_cut_dist sa))
    <= c.
```

`IndistinguishabilityPropAt` ignores its `cert` argument in its body, so the
reader form needs no certificate.

Mutation, `r_framework.v`, `Fail Definition canonicalE_at_another_reader`: at
an abstract reader the same equation is refused. Message read in
`f5_r2_mutation_message.v` (the same command without `Fail`), verbatim:

```
File "./notes/probes/2026-09-20-readers-and-marginal-bounds/f5_r2_mutation_message.v", line 48, characters 8-20:
Error: Cannot apply lemma erefl
```

Second mutation, at the concrete other reader of this tree,
`m1_trace_reader_erefl.v`: `sr_read (coalition_reading_reader
pgl27_dealt_params) C x g = sr_read (pgl27_trace_reader R) C x g` is refused
by `erefl` inside a `Timeout 60`, so the two PGL(2,7) readers are
propositionally equal (R5) and not convertible. The `erefl` fails fast, it
does not reduce the interpreter. Message in `f6_m1_message.v`:

```
File "./notes/probes/2026-09-20-readers-and-marginal-bounds/f6_m1_message.v", line 48, characters 8-20:
Error: Cannot apply lemma erefl
```

### R3 GO

`r_framework.v`, `reader_indistinguishability_postprocessing`, `Qed`.

```coq
Lemma reader_indistinguishability_postprocessing
    (r r' : StaticReader E)
    (f : forall C : {set seats}, sr_T r C -> sr_T r' C)
    (Hf : forall (C : {set seats}) (x : ex_inputT E)
                 (g : pgg_gT (mp_M (instance_profile A))),
            sr_read r' C x g = f C (sr_read r C x g))
    (c : R) :
  ReaderIndistinguishabilityPropAt r c ->
  ReaderIndistinguishabilityPropAt r' c.
```

From `fdistmap_comp` and `var_dist_fdistmap`.

Mutation, `r_framework.v`, `Fail Definition
postprocessing_without_factorisation`: the same script without `Hf` does not
close. Message read in `f3_c8_message.v`:

```
File "./notes/probes/2026-09-20-readers-and-marginal-bounds/f3_c8_message.v", line 49, characters 8-70:
Error: Cannot apply lemma (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _))
```

### R4 GO

`r_pgl27.v`, `pgl27_trace_reader` and
`pgl27_word_trace_indistinguishability_at_reader`, `Qed`, no new mathematics.

```coq
Definition pgl27_trace_reader : StaticReader pgl27_dealt_params :=
  @MkStaticReader pgl27_algebra pgl27_dealt_params
    (fun _ => [the finType of {ffun 'I_8 -> 'I_8}])
    (fun C x g => pgl27_coalition_trace R C (x, g)).

Theorem pgl27_word_trace_indistinguishability_at_reader
    (secretP : R.-fdist bool) :
  @ReaderIndistinguishabilityPropAt R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP) pgl27_trace_reader (2%:R^-39).
Proof.
move=> C x x' HC.
rewrite (pgl27_word_cut_distE secretP).
exact: (@pgl27_word_trace_indistinguishability R C x x' HC).
Qed.
```

Threshold, `pgl27_threshold_readE`, closed by `erefl`:

```coq
  (#|C| < profile_k (instance_profile pgl27_algebra))%N = (#|C| <= 3)%N
```

`profile_k (instance_profile pgl27_algebra)` reduces to 4, and `#|C| < 4` and
`#|C| <= 3` are the same term after `subn` reduction, so the framework's
threshold hypothesis is the cited theorem's hypothesis with no coercion.

Departure from the spec: the trace reader takes the real field as a parameter,
`pgl27_trace_reader (R : realType)`. `pgl27_coalition_trace` is discharged
with `R` explicit because its type mentions the sample distribution
`pgl27P R`, so an `R`-free reader would need a second definition. Since
`ReaderIndistinguishabilityPropAt` already fixes `R` through the adapter, the
parameter costs nothing.

### R5 GO, both directions, with the identity

`r_pgl27.v`, `pgl27_reading_of_trace` and `pgl27_trace_of_reading`, both
`Qed`.

```coq
Lemma pgl27_reading_of_trace (C) (x) (g) :
  sr_read (coalition_reading_reader pgl27_dealt_params) C x g
  = id (sr_read pgl27_trace_reader C x g).
```

Each reader is the identity function of the other. Neither is finer. The
obstacle the spec allowed for does not arise at this instance: what a
coalition's interpreter rows carry and what its seats hold after the shuffle
are one finite function, by `pgl27_coalition_trace_E` and `pgl27_static_obsE`.
The two are equal propositionally and not by conversion, see the second
mutation of R2.

R3 then gives the reading's proposition from the trace theorem at the same
number, `pgl27_word_reading_indistinguishability_by_postprocessing`, `Qed`.

The comparison the spec asked for:
`pgl27_word_reading_indistinguishability_by_certificate` proves the identical
statement through `indistinguishability_tail (@pgl27_word_cert R secretP)`,
and `pgl27_word_cert_epsE` closes by `erefl`:

```coq
  cert_eps (@pgl27_word_cert R secretP) = 2%:R^-40 + 2%:R^-40 :> R
```

so the certificate route's own bound is `2^-40 + 2^-40`, which `pow2_split`
makes `2^-39`. The two routes publish the same number and neither is the
weaker statement.

### R6 GO for the framework part and for the trace instance; the spec's
intended bridge is not the route, and no such bridge exists in the tree

Framework, `r_framework.v`:

```coq
Definition ReaderExactPropAt (r : StaticReader E) (secretT : finType)
    (secret : {RV (sa_sampleP sa) -> secretT}) : Prop :=
  forall C : {set seats},
    (#|C| < profile_k (instance_profile A))%N ->
    sa_sampleP sa |= (fun u => sr_read r C (sa.(sa_arg) u) (sa.(sa_cut) u))
                     _|_ secret.

Definition reader_exact_of_witness (w : ExactWitness sa)
  : ReaderExactPropAt (coalition_reading_reader E) (ew_secret w) :=
  @ew_indep _ _ _ _ w.
```

The canonical instance is the witness's independence field itself, by
conversion, with no proof term of its own. `reader_exact_executed` carries it
to the conjunct of `ExactProp` that speaks of `sa_coalition_view`, in one line,
along the `Sampled` link lemma given as a hypothesis of the same shape the
framework's `exact_tail` takes.

Trace instance, `r_pgl27.v`, `pgl27_trace_exact_at_reader`, `Qed`:

```coq
Theorem pgl27_trace_exact_at_reader :
  @ReaderExactPropAt R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_exact_family R tt) pgl27_trace_reader bool
    (pgl27_secret R).
```

Departure from the spec, with the reason. The spec asks for the trace instance
"from `pgl27_coalition_trace_secrecy`", an entropy equality, and for the
bridge from that equality to independence. That bridge is not needed and does
not exist in this tree:

- `pgl27_coalition_trace_secrecy` is itself proved from `pgl27_view_indep`
  through `trace_secrecy_of_view`, so the independence is upstream of the
  entropy equality, not downstream of it. The probe uses the upstream fact.
- I searched the tree's infotheo for a converse. `probability/proba.v` has
  `inde_RV_events`, `inde_RVP`, `cinde_RV_events`, `cinde_RV_unit`,
  `inde_RV_sym`, all reformulations of independence, and
  `information_theory/entropy.v` has `inde_RV_joint_entropyE`, which goes from
  independence to entropy. There is no lemma taking
  `` `H( X | Y ) = `H `p_ X `` to `P |= Y _|_ X`. `pgl27_view_secrecy` does not
  contain one either: it runs in the same direction as everything else.

So the statement the spec wanted stated is, as a comment and not as an
`Admitted`: a converse of the form

```coq
(* forall (P : R.-fdist U) (X : {RV P -> A}) (Y : {RV P -> B}),
     `H( X | Y ) = `H `p_ X -> P |= Y _|_ X *)
```

is missing from the tree, and a landing that wanted it would have to prove it
(the standard route is the non-negativity of mutual information with the
equality case through `psumr_eq0P`). Nothing in this probe or in the spec's
own decision needs it.

`pgl27_trace_entropy_of_reader` records the direction that does hold: the
instance's published entropy equality for the trace, at the framework's
threshold.

### R7 GO, cited

`r_pgl27.v`, `pgl27_exec_trace_link`, `Qed`, from the existing
`pgl27_content_traceE` of `instances/pgl27/pgl27_models.v`:

```coq
Lemma pgl27_exec_trace_link (secretP : R.-fdist bool) (C) :
  (fun u => pgl27_exec_content_trace C
              ((amf_sample pgl27_word_family R secretP).(sa_arg) u)
              ((amf_sample pgl27_word_family R secretP).(sa_cut) u))
  = (fun u => sr_read pgl27_trace_reader C
                ((amf_sample pgl27_word_family R secretP).(sa_arg) u)
                ((amf_sample pgl27_word_family R secretP).(sa_cut) u)).
```

The lemma exists, so nothing was reproved. Its shape is the `Sampled` link
lemma's shape at the trace reader.

### R8 GO, and two definitions are needed

`r_framework.v`:

```coq
Definition SeatMarginalPropAt (i : seats)
    (ideal : R.-fdist 'I_(pgg_N' (mp_M (instance_profile A))).+1) (c : R)
    : Prop :=
  var_dist (@sa_seat_dist R (instance_profile A) (instance_exec E) sa 0 i)
           ideal
  <= c.

Definition CutMarginalPropAt (T : finType)
    (read : pgg_gT (mp_M (instance_profile A)) -> T)
    (ideal : R.-fdist T) (c : R) : Prop :=
  var_dist (fdistmap read (sa_cut_dist sa)) ideal <= c.
```

Instances, `r_marginals.v`, both `Qed`:

```coq
Theorem s5_exec_endpoint_bound_as_marginal (R : realType)
    (secretP : R.-fdist 'I_5) (L : nat)
    (i : 'I_(pi_T' (mp_PI (instance_profile s5_algebra))).+1) :
  @SeatMarginalPropAt R s5_algebra s5_dealt_params
    (s5_word_sample secretP L) i (s5_ideal_reading secretP)
    (Num.sqrt 5%:R * (s5_alpha_R R) ^+ L).
Proof. exact: (s5_exec_endpoint_bound secretP L i). Qed.

Theorem five_card_repeated_endpoint_as_marginal (R : realType) (s : 'I_5) :
  @CutMarginalPropAt R five_card_algebra five_card_params
    (amf_sample kim_centi_family R tt) _
    (fun sigma : {perm 'I_5} => sigma s) (fdist_uniform (card_ord 5))
    (2%:R^-40).
Proof.
exact: (Order.POrderTheory.ltW (five_card_repeated_endpoint_lt R s)).
Qed.
```

Two definitions are needed, and the reason is a carrier difference, not a
presentation choice. `SeatMarginalPropAt` compares the law of `sa_seat_dist`,
the pushforward of the sample distribution along the executed seat reader,
whose values are card contents read through the instance's encoder.
`five_card_repeated_endpoint_lt` compares the law of
`fun sigma : {perm 'I_5} => sigma s`, the position the cut sends one starting
position to, a function of the shuffle alone with no encoder and no seat. The
two are different readings of one run, so no substitution of arguments turns
one proposition into the other. The refusal is recorded in `r_marginals.v` as
a `Fail Check`, message read in `f4_marginal_message.v`:

```
File "./notes/probes/2026-09-20-readers-and-marginal-bounds/f4_marginal_message.v", line 35, characters 3-46:
Error:
In environment
R : realType
s : 'I_5
The term "five_card_repeated_endpoint_as_marginal R s" has type
 "CutMarginalPropAt (amf_sample kim_centi_family R tt)
    ((fun_of_perm (T:='I_5))^~ s) (fdist_uniform (card_ord 5)) 
    (2 ^- 40)"
while it is expected to have type
 "SeatMarginalPropAt (amf_sample kim_centi_family R tt) s
    (fdist_uniform (card_ord 5)) (2 ^- 40)".
```

The five-card bound is strict, `< 2^-40`; the proposition is stated at `<=`
and the instance widens by `ltW`. A landing that wants the strict form needs a
third definition or a strictness parameter.

### R9 GO

`r_framework.v`, `seat_marginal_at_two` and `cut_marginal_at_two`, both from
`var_dist_le2` of `lib/var_dist_supp.v`, both `Qed`. Every model and every
ideal satisfy each form at two.

Type-level refusals, both in `r_framework.v`, messages read in
`f1_c6_message.v` and `f2_c7_message.v`:

```
The term "seat_marginal_at_two sa i ideal" has type
 "SeatMarginalPropAt sa i ideal 2"
while it is expected to have type "IndistinguishabilityPropAt cert 2".
```

```
The term "seat_marginal_at_two sa i ideal" has type
 "SeatMarginalPropAt sa i ideal 2"
while it is expected to have type
 "ReaderExactPropAt sa (coalition_reading_reader E) secret".
```

Both are recorded type-level facts and not prose: the seat form's type has no
second run argument and no secret to quantify, so it cannot inhabit either
proposition of a security property.

### R10 GO

`a1_assumptions.v`, twelve `Print Assumptions`, exit 0, 16 s. Ten of the twelve
print exactly

```
propositional_extensionality
functional_extensionality_dep
constructive_indefinite_description
```

the boolp trio every statement over an `fdist` record in this tree carries.
The two exceptions are `s5_exec_endpoint_bound_as_marginal` and its cited
theorem `s5_exec_endpoint_bound`, which both additionally carry

```
rigidity_s5_instance.s5_group_order_eq :
  #|pgg_interface.pgg_G
      (pgg_interface.Gen_PGGTypes (n:=3) (pgg_raag_path.path_gen_tuple 3))| =
  120%R
```

identically. So no restatement adds an axiom beyond its cited theorem's own,
and the one custom axiom in the set is the S_5 group-order axiom the manifest
already records for that path.

## Departures from the spec, collected

1. R1: the spec's unnamed "cut" is `pgg_gT (mp_M (instance_profile A))`.
2. R4: `pgl27_trace_reader` takes the real field as a parameter, because
   `pgl27_coalition_trace` is discharged with `R` explicit. Harmless, the
   proposition fixes `R` through the adapter anyway.
3. R6: the spec's route through `pgl27_coalition_trace_secrecy` is the wrong
   way round for this tree. The probe uses `pgl27_view_indep`, which is the
   fact the entropy equality is derived from, and reports that the converse
   bridge does not exist in the tree.
4. R8: two definitions, not one, and the five-card instance is widened from
   `<` to `<=`.
5. The spec says `r_pgl27.v` carries R4, R5, R6 trace part and R7 with imports
   from `pgl27_models.v` and `pgl27_exec.v`. The certificate comparison of R5
   needs `pgl27_word_cert`, which lives in
   `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v`, so `r_pgl27.v`
   requires that file too.

## What misled me, and what cost time

1. **`rewrite -!fdistmap_comp` does not terminate.** The first draft of R3 used
   it. The compile ran 10 minutes at 5 GB before I killed it. `fdistmap_comp`
   is `fdistmap g (fdistmap h P) = fdistmap (g \o h) P`; read right to left
   under `!`, its pattern matches the image of *any* reader, because the
   second pass unifies the bare reader with a composition. The fix is one
   rewrite per side at its own instance, through a `have` that names the
   composed law. This is the repository's standing rule about `!` on
   unbounded-match lemmas, and `fdistmap_comp` belongs on that list.
2. **A `Timeout`-guarded `ltac:()` one-liner silently mis-parses.** In
   `b2_bisect_attempt_1.v` the `have H : T by tac; rest` form let `by` swallow
   the rest of the script, and the error was "unresolved implicit arguments",
   which reads like a typing problem and is not one. Bisecting with ordinary
   `Proof. ... Qed.` blocks and `rocq compile -time` named the offending
   *tactic* directly and was both cheaper and honest.
3. **`Unset Strict Implicit` makes conclusion-only arguments implicit.**
   `pgl27_word_trace_indistinguishability` is declared with `(C : {set 'I_8})`
   and discharges as `forall (R : realType) [C : {set 'I_8}] (s s' : bool)`,
   with `C` implicit because it occurs only in the conclusion. A positional
   `exact: (lemma R C x x' HC)` then binds `C` to `s`, and the only message is
   `Error: Cannot apply lemma (...)`, which says nothing about arity. Printing
   the arities with `About` in one throwaway file (`d2_arities.v`) settled six
   call sites at once and was faster than guessing at any one of them.
4. **Another agent was rebuilding production throughout.** Three ordered
   passes died on `inconsistent assumptions` over `var_dist_supp`,
   `five_card_mixing` and `pgl27_models` before the fourth went through. The
   spec's rule of restarting the whole pass after three minutes is right;
   retrying one file does not converge, because the stale library moves.
5. A minor one: `sr_T`/`sr_read` are record projections, so
   `Arguments sr_T {A E} r C.` is rejected with
   `Flag "rename" expected to rename s into r`. Name no binders there.
