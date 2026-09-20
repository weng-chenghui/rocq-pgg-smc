# Landing of the two reading probes: what went into production (2026-09-21)

Steps 1 to 4 of the order of work in
`notes/20260920-readers-and-marginal-bounds-probe-design.md`, section "Second
probe, its audit, and the landing plan for tracker 4.1 and 4.4". Step 5 (the
reverse closure, the combined audit, the commit) is the main session's.

## Flow: `psl211_colour_view_indep` becomes `ReadingExactIndependence`

One step per line, the trailing comment counting the declarations landed so
far.

```
object   psl211P secretP                              // a law on bool * PSL(2,11), no adapter, no run   [0]
adapt    psl211P -> psl211_dealt_sample
           iface MkSampleAdapter(fst, snd)            // law, argument, cut, cut law: four equations     [5]
object   psl211_colour_reading
           iface MkStaticReading                      // C, run argument, cut |-> {ffun seats -> bool}   [6]
same     psl211_colour_view = that reading
           by psl211_colour_readingE, _funE           // one term, no seat reconciliation here           [8]
object   static_coalition_reading psl211_dealt_params
           iface manifest/pgg_tableau_reading.v       // the card-identity reading of the framework      [8]
factor   colour = psl211_colour_of_reading o identity
           by psl211_colour_reading_factorsE          // the map is not injective                       [10]
step     indistinguishability at card identity
           -> at colour
           by reading_indistinguishability_postprocessing
                                                      // transports a bound, produces none              [11]
eval     ReadingExactIndependence at colour
           by psl211_colour_view_indep                // #|C| < 6 meets #|C| <= 5 through -ltnS          [12]
eval     sharpness at #|C| = 6
           by psl211_colour_view_dep_k6               // psl211_leak_coalition, both priors positive     [14]
refute   ReadingExactIndependence at card identity
           by psl211_dealt_raw_countE, _fiberE        // false at one coalition of three, and 3 < 6      [17]
outside  seat and cut marginal bounds
           iface manifest/pgg_tableau_marginal_bounds.v
                                                      // no coalition, no second argument, no secret     [21]
outside  pgl27_coalition_trace_static_obsE            // the two PGL(2,7) readings are one               [22]
```

The refuted reading sits beside the colour one at the same model, the same
adapter and a coalition of the same run: the colour reading's exact
independence is therefore not the image of the card-identity reading's under
the post-processing law, that one being false.

Monad verdict: no monad. Nothing accumulates along the flow. The one
connecting operation, `reading_indistinguishability_postprocessing`, is a
morphism of a preorder of readings, arrows being factorisations, and it keeps
the number fixed rather than adding to it; the exact form carries no
composition law in this landing.

Interfaces every existing theorem enters through:

| theorem | enters as | interface |
|---|---|---|
| `psl211_colour_view_indep` | terminal evaluation | `psl211_colour_reading_funE` |
| `psl211_colour_view_dep_k6` | terminal evaluation | `psl211_colour_reading_funE` |
| `psl211_leak_coalition_card6`, `profile_k_psl211_algebra` | threshold reconciliation | `psl211_leak_coalition_not_below_k` |
| `psl211_dealt_static_obsE` | observation change | `psl211_colour_reading_factorsE` |
| `psl211_dealt_raw_countE`, `psl211_dealt_fiberE`, `psl211_dealt_view`, `psl211_perdeck_coalition_below_k` | step justification of the refutation | `psl211_dealt_perdeck_readingE` |
| `var_dist_fdistmap`, `fdistmap_comp` | step justification | `reading_indistinguishability_postprocessing` |
| `ew_indep` of `ExactWitness` | packaging | `exact_independence_of_witness` |
| `sampled_viewE_prop`-shaped link | hypothesis, not proved here | `exact_independence_executed_of_reading` |
| `s5_exec_endpoint_bound` | pre-composition outside the flow | `s5_word_seat_marginal` |
| `five_card_repeated_endpoint_lt` | pre-composition outside the flow | `five_card_repeated_cut_marginal` |
| `pgl27_coalition_trace_E`, `pgl27_static_obsE` | observation change | `pgl27_coalition_trace_static_obsE` |
| `var_dist_le2` | terminal evaluation | `seat_marginal_prop_at2`, `cut_marginal_prop_at2` |

## What landed, per file

### `manifest/pgg_tableau_reading.v` (new, 247 lines)

`_CoqProject` line added after `manifest/pgg_tableau_security_property_relations.v`.
Requires `manifest/pgg_tableau.v` and `security/pgg_sample_adapter.v`.
Required by `instances/psl211/psl211_colour_reading.v` and by nothing in
`manifest/`.

```
Record StaticReading := MkStaticReading {
  sr_readT : {set seats} -> finType ;
  sr_read : forall C : {set seats},
    ex_inputT E -> pgg_gT (mp_M (instance_profile A)) -> sr_readT C }.

Definition static_coalition_reading : StaticReading :=
  @MkStaticReading (fun _ => [the finType of {ffun seats -> cards}])
    (@static_coalition_obs A E).

Lemma static_coalition_readingTE (C : {set seats}) :
  sr_readT static_coalition_reading C
  = [the finType of {ffun seats -> cards}].

Lemma static_coalition_readE (C : {set seats}) (x : ex_inputT E)
    (g : pgg_gT (mp_M (instance_profile A))) :
  sr_read static_coalition_reading C x g = static_coalition_obs C x g.

Definition ReadingIndistinguishabilityPropAt (r : StaticReading E) (c : R)
    : Prop :=
  forall (C : {set seats}) (x x' : ex_inputT E),
    (#|C| < profile_k (instance_profile A))%N ->
    var_dist (fdistmap (sr_read r C x) (sa_cut_dist sa))
             (fdistmap (sr_read r C x') (sa_cut_dist sa))
    <= c.

Lemma reading_indistinguishability_static_coalitionE
    (cert : IndistinguishabilityCert sa) (c : R) :
  ReadingIndistinguishabilityPropAt (static_coalition_reading E) c
  = IndistinguishabilityPropAt cert c.

Lemma reading_indistinguishability_postprocessing
    (r r' : StaticReading E)
    (f : forall C : {set seats}, sr_readT r C -> sr_readT r' C)
    (Hf : forall (C : {set seats}) (x : ex_inputT E)
                 (g : pgg_gT (mp_M (instance_profile A))),
            sr_read r' C x g = f C (sr_read r C x g))
    (c : R) :
  ReadingIndistinguishabilityPropAt r c ->
  ReadingIndistinguishabilityPropAt r' c.

Definition ReadingExactIndependence (r : StaticReading E) (secretT : finType)
    (secret : {RV (sa_sampleP sa) -> secretT}) : Prop :=
  forall C : {set seats},
    (#|C| < profile_k (instance_profile A))%N ->
    sa_sampleP sa |= (fun u => sr_read r C (sa.(sa_arg) u) (sa.(sa_cut) u))
                     _|_ secret.

Definition exact_independence_of_witness (w : ExactWitness sa)
  : ReadingExactIndependence (static_coalition_reading E) (ew_secret w) :=
  @ew_indep _ _ _ _ w.

Lemma exact_independence_executed_of_reading (secretT : finType)
    (secret : {RV (sa_sampleP sa) -> secretT})
    (Hview : forall C : {set seats},
       @sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C
       = (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u))) :
  ReadingExactIndependence (static_coalition_reading E) secret ->
  forall C : {set seats}, (#|C| < profile_k (instance_profile A))%N ->
    sa_sampleP sa
    |= (@sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C)
       _|_ secret.

Arguments StaticReading {A} E.
Arguments sr_readT {A E}.
Arguments sr_read {A E}.
Arguments static_coalition_reading {A} E.
Arguments ReadingIndistinguishabilityPropAt {R A E} sa r c.
Arguments ReadingExactIndependence {R A E} sa r {secretT} secret.
Arguments reading_indistinguishability_postprocessing {R A E sa} r r' f Hf c.
```

Comments: S1's replacement sits on the record, S2 on the header, S3's relation
replaces "finer", S4 is the amendment's wording (independence, and the entropy
forms are not restated), P7's restriction is in the header, P16's factor two
is on `ReadingIndistinguishabilityPropAt` and in the header.

### `manifest/pgg_tableau_marginal_bounds.v` (new, 120 lines)

`_CoqProject` line after the reading leaf. Requires
`security/pgg_sample_adapter.v` and `lib/var_dist_supp.v`, and not the reading
leaf.

```
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

Lemma seat_marginal_prop_at2 (i : seats)
    (ideal : R.-fdist 'I_(pgg_N' (mp_M (instance_profile A))).+1) :
  SeatMarginalPropAt i ideal 2%:R.

Lemma cut_marginal_prop_at2 (T : finType)
    (read : pgg_gT (mp_M (instance_profile A)) -> T) (ideal : R.-fdist T) :
  CutMarginalPropAt read ideal 2%:R.

Arguments SeatMarginalPropAt {R A E} sa i ideal c.
Arguments CutMarginalPropAt {R A E} sa {T} read ideal c.
Arguments seat_marginal_prop_at2 {R A E} sa i ideal.
Arguments cut_marginal_prop_at2 {R A E} sa {T} read ideal.
```

S5 and S6 applied: the propositions are said not to be among the three the
security evidence proves, and the run index zero is named as the
process-identifier base.

### `instances/pgl27/pgl27_proximity.v` (one lemma, one import, header and index)

```
Lemma pgl27_coalition_trace_static_obsE (R : realType) (C : {set 'I_8})
    (s : bool) (g : pgg_gT pgl27_M) :
  pgl27_coalition_trace R C (s, g)
  = @static_coalition_obs pgl27_algebra pgl27_dealt_params C s g.
Proof.
by rewrite (pgl27_coalition_trace_E R C) (pgl27_static_obsE R C s g).
Qed.
```

### `instances/s5/tableau/s5_tableau_sampled.v`

```
Lemma s5_word_seat_marginal (R : realType) (secretP : R.-fdist 'I_5)
    (L : nat)
    (i : 'I_(pi_T' (mp_PI (instance_profile s5_algebra))).+1) :
  @SeatMarginalPropAt R s5_algebra s5_dealt_params
    (s5_word_sample secretP L) i (s5_ideal_reading secretP)
    (Num.sqrt 5%:R * (s5_alpha_R R) ^+ L).
Proof. exact: (s5_exec_endpoint_bound secretP L i). Qed.
```

### `instances/kim2025/tableau/five_card_tableau_sampled.v`

```
Lemma five_card_repeated_cut_marginal (R : realType) (s : 'I_5) :
  @CutMarginalPropAt R five_card_algebra five_card_params
    (amf_sample kim_centi_family R tt) _
    (fun sigma : {perm 'I_5} => sigma s) (fdist_uniform (card_ord 5))
    (2%:R^-40).
Proof.
exact: (Order.POrderTheory.ltW (five_card_repeated_endpoint_lt R s)).
Qed.
```

### `instances/psl211/psl211_colour_reading.v` (new, 478 lines)

`_CoqProject` line after `instances/psl211/psl211_reading_constancy.v`.
Nineteen declarations, in the order: `psl211_dealt_inputTE`,
`psl211_dealt_sample`, `psl211_dealt_sample_lawE`, `_argE`, `_cutE`,
`_cut_distE`, `psl211_colour_reading`, `psl211_colour_readingE`,
`psl211_colour_reading_funE`, `psl211_colour_of_reading`,
`psl211_colour_reading_factorsE`,
`psl211_colour_indistinguishability_of_coalition_reading`,
`psl211_colour_of_reading_collides`, `psl211_colour_reading_indep`,
`psl211_leak_coalition_not_below_k`, `psl211_colour_reading_dep_k6`,
`psl211_dealt_perdeck_reading`, `psl211_dealt_perdeck_readingE`,
`psl211_dealt_reading_indep_false`. Statements verbatim from the second probe
up to the renames of the audit's "Names" section; every statement and every
`Arguments` line is read back in `landing_fidelity.v`.

Comments: Q2's sentence on the adapter, on `psl211_colour_reading_indep` and
on `psl211_dealt_reading_indep_false`; Q3's replacement on
`psl211_colour_readingE`; Q5's on `psl211_colour_of_reading_collides`; Q6's on
`psl211_colour_indistinguishability_of_coalition_reading`; Q7's and Q9's on
`psl211_dealt_reading_indep_false`; S9 to S13 and S16, S17 applied. Nothing
was placed under `instances/psl211/tableau/`.

### `instances/psl211/psl211_reading_constancy.v` (two sentences, comment only)

Header, in the "Dealt mode" paragraph, and the docstring of
`psl211_dealt_constancy_false`. Both said the tree carries no dealer-dealt
sample adapter through which a certificate's ideal could be pinned. Both now
name `psl211_dealt_sample`, say that no certificate is built over it, and say
that the dealer-dealt parameters carry no endpoints statement, so there is no
program and no path over them either. No declaration, statement, proof or name
in that file changed.

## Compile times, one Rocq process at a time through the shared lock

| file | wall |
|---|---|
| `landing_draft_reading.v` | 106 s (lock wait included) |
| `landing_draft_marginal_bounds.v` | 4 s |
| `landing_draft_colour_reading.v` | 16 s |
| `manifest/pgg_tableau_reading.v` | 3 s |
| `manifest/pgg_tableau_marginal_bounds.v` | 4 s |
| `instances/psl211/psl211_reading_constancy.v` | 22 s |
| `instances/psl211/psl211_colour_reading.v` | 16 s |
| `instances/pgl27/pgl27_proximity.v` | 4 s |
| `instances/s5/tableau/s5_tableau_sampled.v` | 3 s |
| `instances/kim2025/tableau/five_card_tableau_sampled.v` | 4 s |
| `landing_fidelity.v` | 4 s |

No unedited production file had to be recompiled: the only edited file below a
new one is `psl211_reading_constancy.v`, and it was recompiled first.

## `Print Assumptions`, compiled in `landing_fidelity.v`

| declaration | assumptions |
|---|---|
| `psl211_colour_reading_indep` | the three classical |
| `psl211_colour_reading_dep_k6` | the three classical |
| `psl211_dealt_reading_indep_false` | the three classical |
| `psl211_colour_reading_factorsE` | Closed under the global context |
| `psl211_colour_indistinguishability_of_coalition_reading` | the three classical |
| `pgl27_coalition_trace_static_obsE` | the three classical |
| `s5_word_seat_marginal` | `rigidity_s5_instance.s5_group_order_eq` and the three classical |
| `five_card_repeated_cut_marginal` | the three classical |
| `seat_marginal_prop_at2` | the three classical |
| `cut_marginal_prop_at2` | the three classical |

The three classical are `propositional_extensionality`,
`functional_extensionality_dep` and `constructive_indefinite_description`. No
assumption beyond what each cited theorem already carries.

## Departures from the plan, with the reason

1. **`pgl27_coalition_trace_static_obsE` sits after `pgl27_static_obs_funE`,
   not immediately after `pgl27_static_obsE`.** The docstring of
   `pgl27_static_obs_funE` opens "The same identification with the cut left
   free"; inserting between the two would make that sentence point at the
   trace lemma and become false. The new lemma closes the same section, beside
   both.
2. **`pgl27_proximity.v` gains one import, `pgl27_trace`.** The audit's
   placement row says "no new import". `Require Import` is not transitive in
   Rocq and that file uses no name of `pgl27_trace.v` today, so
   `pgl27_coalition_trace` and `pgl27_coalition_trace_E` are not in scope
   without it. The module is already in the file's load set through
   `pgl27_models.v`, so the build graph is unchanged.
3. **`s5_tableau_sampled.v` gains four imports and one scope.**
   `pgg_interface`, `pgg_session_types` and `pgg_monodromy_profile` for
   `pi_T'` and `mp_PI` in the seat type, `s5_mixing` for `s5_alpha_R`,
   `pgg_tableau_marginal_bounds` for the proposition, and
   `Local Open Scope fdist_scope` for `R.-fdist`, without which the statement
   fails to parse. The scope is opened before `ring_scope`, so `ring_scope`
   stays the innermost as before, and the file's existing definition compiled
   unchanged.
4. **`Arguments cut_marginal_prop_at2 {R A E} sa {T} read ideal.` is new.**
   The probe carried no such line for `cut_marginal_at_two`. It is added for
   symmetry with `seat_marginal_prop_at2`, and nothing consumes it yet.
5. **One existing header sentence of `five_card_tableau_sampled.v` was
   rewritten**, "Two of the statements here" to "Three", a third statement of
   that kind now being in the file. Allowed as header prose of a file that
   receives a declaration.
6. **Two proof lines were rewrapped**, the `Proof. ... Qed.` one-liner of
   `psl211_colour_readingE` and the `apply/pfwd1_neq0` line inside
   `psl211_dealt_reading_indep_false`, each measuring 81 bytes in the probe.
   Tactic text is otherwise the probe's verbatim.
7. **No `Print Assumptions` in production.** The probes ran them in the files;
   the landing runs them in `landing_fidelity.v`.
8. **The probe's `Fail` mutation blocks did not land.** `r_framework.v`'s
   `marginal_is_not_evidence` and `postprocessing_mutation` sections are
   evidence about the probe, and the placement table lists only the
   declarations. Finding P12 already records that those two refusals show only
   that two definitions have different types.
9. **The PGL(2,7) trace instance of the propositions did not land**, per the
   spec's amendment 6, only the identification lemma.

## What is left

1. The reverse closure of the four edited production files, recompiled
   single-file by the main session:
   `instances/psl211/tableau/*` and `manifest/pgg_analysis_client.v` over
   `psl211_reading_constancy.v`; `instances/pgl27/tableau/*` over
   `pgl27_proximity.v`; `instances/s5/tableau/s5_tableau_analysis_bridged.v`
   and `s5_tableau_checks.v`; `instances/kim2025/tableau/*`.
2. The combined naming, comment and layout audit of the landing, and the fix
   pass and commit.
3. Not in this landing, per the plan: a program or a path over the
   fixed-dealer colour model, the S_5 countermodel as a theorem, and a
   post-processing law for the exact form.

## Fix pass (2026-09-21)

Comments only. Eight files touched, no code token changed, nothing compiled
and no Rocq process started. Findings E1 to E19 and E23 of
`audit-landing.md` applied with the auditor's replacements, rewrapped to each
site's own comment style; E20 added one header line to `landing_fidelity.v`;
E21, E22, E24 and E25 need no production change. Backticks of the audit's
markdown are dropped at sites whose files write bare identifiers.

### `manifest/pgg_tableau_reading.v`

**E18**, on the record.

old:
```
   deck and the cut alone is a theorem about it. The value type depends on the
   coalition because a coalition of a different size reads a different
   amount. *)
```
new:
```
   deck and the cut alone is a theorem about it. The value type may depend on
   the coalition; both readings of this tree return a seat-indexed map at
   every coalition and do not use that freedom. *)
```

**E1**, on `static_coalition_reading`.

old:
```
(* A coalition's static endpoint reading as a reading. It is the reading every
   proposition of the Tableau is stated at today, and the reading the link
   lemma of the Sampled level identifies with the executed coalition view. *)
```
new:
```
(* A coalition's static endpoint reading as a reading. The
   input-indistinguishability proposition of the Tableau is stated at it; the
   exact-independence and the ideal-proximity propositions are stated at the
   executed coalition view, which the link lemma of the Sampled level
   identifies with it. *)
```

**E10**, on `reading_indistinguishability_static_coalitionE`.

old: `   reading form does not, and nothing the framework proves today changes. *)`
new: `   reading form does not. *)`

**E2**, on `ReadingExactIndependence`.

old:
```
   independent of the secret. It is an independence and not a numeric bound,
   so it is the conjunct the framework's entropy forms are derived from, and
   those forms are not restated here. *)
```
new:
```
   independent of the secret. It is an independence and not a numeric bound.
   The framework's entropy forms sit inside ExactProp, derived there from
   independence of the executed coalition view, which this proposition reaches
   at a coalition's static reading along the link lemma of the Sampled level;
   none of those forms is restated here. *)
```

### `manifest/pgg_tableau_marginal_bounds.v`

**E6** at `:9` and **E7** at `:11-12`.

old:
```
(* the cut form compares the law of one finite reading of the model's cut.    *)
(* Neither mentions a coalition, a second run argument or a secret, so        *)
(* neither is one of the three propositions the security evidence proves, and *)
(* no constructor of SecurityEvidence carries either.                         *)
```
new:
```
(* the cut form compares the law of one finite function of the model's cut.   *)
(* Neither mentions a coalition, a second run argument or a secret, so        *)
(* neither is one of the three propositions the security evidence proves.     *)
```

**E8**, the build-graph sentence.

old:
```
(* This file is required by the instance files that state an instance of      *)
(* either proposition and by nothing in manifest/. It does not require        *)
(* manifest/pgg_tableau_reading.v: a marginal bound is not a statement at a   *)
(* reading, the seat form reading one seat and the cut form one position of   *)
(* the shuffle.                                                               *)
```
new:
```
(* It does not require manifest/pgg_tableau_reading.v: a marginal bound is    *)
(* not a statement at a reading, the seat form reading one seat and the cut   *)
(* form one position of the shuffle.                                          *)
```

**E6** at the index entry.

old: `(*   CutMarginalPropAt          == one finite reading of the cut has a law    *)`
new: `(*   CutMarginalPropAt          == one finite function of the cut has a law   *)`

**E5**, on `SeatMarginalPropAt`.

old:
```
   process-identifier base zero every statement of the framework uses, is
   within c of a named ideal law. It mentions no coalition, no second run
   argument and no secret, so it is not a statement about what an adversary
   distinguishes; it compares one model's one-seat law with one named law and
   says nothing more. The number bounds a sum of absolute differences, twice
   the total variation distance of the literature. *)
```
new:
```
   selection index zero every statement of the framework fixes, the single
   entry of the run's one-element deck and so the cut itself, is within c of a
   named ideal law. It mentions no coalition, no second run argument and no
   secret, so it is not a statement about what an adversary distinguishes; it
   compares one model's one-seat law with one named law and says nothing more.
   The number bounds a sum of absolute differences, twice the total variation
   distance of the literature. *)
```

**E6** and **E11**, on `CutMarginalPropAt`.

old:
```
(* A one-position marginal bound on the cut: the law of one finite reading of
   the model's cut is within c of a named ideal law. The reading is a function
   of the shuffle alone and not of the run argument, so this states less than
   the seat form: it is about the model's randomness and not about what any
   seat sees. Like the seat form it mentions no coalition, no second run
   argument and no secret, and its number is a sum of absolute differences. *)
```
new:
```
(* A one-position marginal bound on the cut: the law of one finite function of
   the model's cut is within c of a named ideal law. That function is of the
   shuffle alone and not of the run argument, so it speaks of the model's
   randomness and not of what any seat sees. Like the seat form it mentions no
   coalition, no second run argument and no secret, and its number is a sum of
   absolute differences. *)
```

### `instances/psl211/psl211_colour_reading.v`

**E19**.

old: `(* Two readings of one run are separated here. The colour reading is a        *)`
new: `(* Two readings of one model are separated here. The colour reading is a      *)`

**E9**.

old: `(* is about an executed run. This file is required by nothing.                *)`
new: `(* is about an executed run.                                                  *)`

**E13**, the two index entries swapped so that they run in file order
(`psl211_colour_indistinguishability_of_coalition_reading` at `:287`,
`psl211_colour_of_reading_collides` at `:307`). The six lines moved verbatim,
so the `==` column and the continuation column are the file's own, 32 and 35
counted from one, as on every neighbouring entry.

old:
```
(*   psl211_colour_of_reading_collides                                        *)
(*                             == that colour map is not injective at a       *)
(*                                nonempty coalition                          *)
(*   psl211_colour_indistinguishability_of_coalition_reading                  *)
(*                             == the post-processing law at that             *)
(*                                factorisation                               *)
```
new:
```
(*   psl211_colour_indistinguishability_of_coalition_reading                  *)
(*                             == the post-processing law at that             *)
(*                                factorisation                               *)
(*   psl211_colour_of_reading_collides                                        *)
(*                             == that colour map is not injective at a       *)
(*                                nonempty coalition                          *)
```

**E17**, on `psl211_dealt_sample_cut_distE`.

old:
```
    law on the shuffle group, whatever the prior on the chirality. Every
    proposition stated at a reading pushes the reading forward along this law,
    so it is the law the colour theorems' own uniformity hypothesis meets. *)
```
new:
```
    law on the shuffle group, whatever the prior on the chirality. The
    input-indistinguishability proposition at a reading pushes the reading
    forward along this law, so it is the law the colour theorems' own
    uniformity hypothesis meets. *)
```

**E16**, on `psl211_colour_reading`.

old:
```
    what a coalition holding cards of two indistinguishable colours sees, and
    it holds no card identity. *)
```
new:
```
    what a coalition sees when it can tell the colour at each of its
    positions and not which card of that colour lies there. *)
```

**E3**, on `psl211_colour_reading_indep`.

old:
```
    six. The statement is an independence and not a numeric bound, so it is
    the conjunct the framework's entropy forms are derived from, and those
    forms are not restated here. The dealer-dealt parameters carry no
    endpoints statement, so this is a statement about the model's law and the
    static reading, and not about an executed run. *)
```
new:
```
    six. The statement is an independence and not a numeric bound, and no
    entropy form of the framework is restated at it. The dealer-dealt
    parameters carry no endpoints statement, so this is a statement about the
    model's law and the static reading, and not about an executed run. *)
```

### `instances/psl211/psl211_reading_constancy.v`

**E4**, one sentence at both sites.

header, old:
```
(* A dealer-dealt sample adapter now exists, psl211_dealt_sample of           *)
(* instances/psl211/psl211_colour_reading.v, so an ideal can be pinned to     *)
(* these parameters, and no certificate is built over it. The dealt           *)
(* parameters carry no endpoints statement, so there is no program and no     *)
(* path over them either.                                                     *)
```
header, new:
```
(* An ideal can be pinned to these parameters through the dealer-dealt sample *)
(* adapter psl211_dealt_sample of instances/psl211/psl211_colour_reading.v,   *)
(* and no certificate is built over it. The dealt parameters carry no         *)
(* endpoints statement, so there is no program and no path over them either.  *)
```

docstring on `psl211_dealt_constancy_false`, old:
```
    no certificate. The dealer-dealt sample adapter psl211_dealt_sample of
    instances/psl211/psl211_colour_reading.v pins an ideal to these
    parameters, and no certificate is built over it. The dealt parameters
    carry no endpoints statement, so there is no program and no path over
    them either. *)
```
new:
```
    no certificate. An ideal can be pinned to these parameters through the
    dealer-dealt sample adapter psl211_dealt_sample of
    instances/psl211/psl211_colour_reading.v, and no certificate is built over
    it. The dealt parameters carry no endpoints statement, so there is no
    program and no path over them either. *)
```

### `instances/kim2025/tableau/five_card_tableau_sampled.v`

**E12**, the index entry.

old:
```
(*                           == the same, at 2^-40 and not below it, as a     *)
(*                              one-position marginal bound on the cut        *)
```
new:
```
(*                           == the same comparison as a one-position         *)
(*                              marginal bound on the cut, at most 2^-40      *)
```

**E6**, on `five_card_repeated_cut_marginal`.

old:
```
    number at this magnitude is read as. The reading compared is a function
    of the shuffle alone, the position the cut sends one starting position
    to, and not what any seat holds, so the statement names no seat, no set
    of seats and no secret and is not security evidence. The number is a sum
    of absolute differences, twice the total variation distance of the
```
new:
```
    number at this magnitude is read as. The function compared is of the
    shuffle alone, the position the cut sends one starting position to, and
    not what any seat holds, so the statement names no seat, no set of seats
    and no secret and is not security evidence. The number is a sum of
    absolute differences, twice the total variation distance of the
```

### `instances/s5/tableau/s5_tableau_sampled.v`

**E14**, the index heading.

old: `(* Lemmas:                                                                    *)`
new: `(* Key results:                                                               *)`

### `instances/pgl27/pgl27_proximity.v`

**E15**, three pre-existing places, the noun only.

index, old: `(*   pgl27_static_obsE       == the framework's seat reader is the instance's *)`
index, new: `(*   pgl27_static_obsE       == the framework's reading is the instance's     *)`

docstring on `pgl27_static_obs_funE`, old:
```
    two laws obtained by pushing a reader forward along a distribution on cuts,
    so it needs the reader as one function and not as its values. *)
```
new:
```
    two laws obtained by pushing a reading forward along a distribution on
    cuts, so it needs the reading as one function and not as its values. *)
```

After the pass the file has no occurrence of the word "reader".

**E23**, on `pgl27_coalition_trace_static_obsE`.

old:
```
    each member's seat holds after the shuffle, and at these eight cards the
    two are one finite map. Every theorem this instance publishes about the
    trace and every theorem it publishes about the reading are therefore one
    statement each, and the two numbers 2^-39 the tree publishes, one at the
    trace and one at the reading, are one number. *)
```
new:
```
    each member's seat holds after the shuffle, and at this instance's eight
    seats the two are one finite map. Every theorem this instance publishes
    about the trace and every theorem it publishes about the reading are
    therefore one statement each, and the two numbers 2^-39 the tree
    publishes, one at the trace and one at the reading, are one number. *)
```

### `notes/probes/2026-09-21-psl211-colour-reader/landing_fidelity.v`

**E20**, one header line added after the existing paragraph, with a blank
comment line before it.

```
(*                                                                            *)
(* The bodies of the four propositions are pinned by production, not here.    *)
```

### What E5 was checked against

The auditor's full replacement is supported and was written whole. `P_idx` is
the fifth argument of `sa_run`, passed to `exec_run mp e (sa_arg u) (sa_cut u)
P_idx` (`security/pgg_sample_adapter.v:136,143-144`). `exec_dealer` builds the
run's dealer as `dealer_with_input_encoding (mp_PI mp) (ep_content x)
[:: w0] (exec_input_ids x) (ep_players) P_idx`
(`protocol/pgg_execution_plug.v:156-159`), so the deck is the one-element list
`[:: w0]` whose single entry is the run's cut, `sa_cut u`.
`dealer_with_input_encoding` hands `W` and `P_idx` to `exchange_dealer`
(`protocol/pgg_run.v:45-51`), where `W` is the dealer's word table and `P_idx`
the selection index into it: "the dealer evaluates words into group elements,
producing a lookup table W ... and picks a selection index P_idx ... Player i
looks up entry P_idx" (`protocol/card_exchange_pismc.v:69-76`). At index zero
the entry selected from `[:: w0]` is `w0`, the cut itself. The framework's
statements fix that index: `SeatMarginalPropAt` uses `@sa_seat_dist ... sa 0 i`
and `pgg_tableau_reading.v` uses `@sa_coalition_view ... sa 0 C`. The three
files were opened read-only and are unchanged.

### Findings not applied

- **E20 (production part), E21, E22, E24, E25**: the audit asks for no
  production change; E20's one header line went into the fidelity file.
- Nothing else was deferred. E15 was scoped to the three places the audit
  quotes; the word "reader" in the human sense survives at
  `five_card_tableau_sampled.v:8,181` and `s5_tableau_sampled.v:8`, outside
  this finding.

### Finishing checks

1. **Comment-stripped token identity**, all eight touched files against their
   pre-pass copies, nested `(* *)` removed and the remainder compared
   token-by-token: identical, zero differences. Token counts 663, 272, 1194,
   3023, 450, 157, 748, 1536.
2. **Width**: no line of any touched file exceeds 80 bytes, measured on the
   encoded line. Every boxed line added is exactly 80 with one space before
   the closing delimiter. No added line carries trailing whitespace.
3. **Vocabulary** on every added line: no occurrence of the two barred nouns,
   of a word from the owner's list, of a capital-L-and-digit token, of an
   abbreviation of "indistinguishability", of a status or history word
   ("now", "today", "existing", "new"), or of a plan, ledger or audit token.
4. **Order and columns**: the swapped index entries of
   `psl211_colour_reading.v` now run in file order, at the file's own columns.
5. Nothing under `notes/probes/` was deleted, no git command that writes was
   run, no file of the forward closure of `psl211_endpoints.v` was touched,
   and nothing was compiled.
