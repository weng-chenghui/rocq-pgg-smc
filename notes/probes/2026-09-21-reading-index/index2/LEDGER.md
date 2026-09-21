# Probe B round 2: the regression fixed, and the rows that were open

Spec: `notes/20260921-reading-index-and-surface-prepositions-probe-design.md`.
Round 1 evidence stays in `../index/` untouched. This directory is round 2.
Production is read-only; every compile went through the `rocq1` lock.

## The two numbers

| | rocq s for `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` | slowest sentence |
|---|---|---|
| production baseline (`baseline/`, production framework) | **6.8** | 2.2 s, a `Require Import` |
| round 1, sigma payload | 86.1 | `exact: erefl` **64.6 s** |
| **round 2, two statements** | **8.6 (1.26x the baseline)** | **3.9 s, a `Require Import`** |

The pass criterion is met: within 1.5x of the baseline, and no sentence over
10 s. Every `exact: erefl` in the file is now at most 0.004 s, including
`pgl27_word_published_sampledE`, which was the 64.6 s sentence. The slowest
three sentences are a `From mathcomp Require Import` at 3.9 s, a
`From infotheo Require Import` at 2.0 s and a `by rewrite -Hd.` at 1.9 s,
which is the same profile the production baseline has.

## 1. The fix

The coordinator's proposed signature,
`certify_exact_at (r : forall x : StackAt Sampled, EndpointReading (projT1 x))`,
**cannot be used for an instance reading and was not implemented.** The
reading of a concrete instance has type `EndpointReading psl211_algebra`, and
`fun _ : StackAt Sampled => psl211_colour_endpoint_reading` does not
typecheck against `forall x, EndpointReading (projT1 x)`, because `projT1 x`
is a variable. Every variant that puts the reading before `x` founders on the
same point: the reading's algebra must BE `projT1 x`, so a reading given
before `x` cannot be typed, and a reading given after `x` cannot be given at
all, the bind passing the statement unapplied.

What was implemented instead, and what works, is **two statements per
property**: one whose payload mentions no reading, and one whose payload
carries it.

```coq
(* the payload of a program that names no reading: a plain function, as in
   production, at the coalition's own endpoint reading *)
Definition ExactPayload (x : StackAt Sampled) : Type :=
  forall (R : realType) (idx : amf_index (sp_f x) R),
    ExactWitness (amf_sample (sp_f x) R idx)
      (coalition_endpoint_reading (projT1 x)).

(* the payload of a program that names one *)
Definition ExactPayloadOfReading (x : StackAt Sampled) : Type :=
  { r : EndpointReading (projT1 x)
  & forall (R : realType) (idx : amf_index (sp_f x) R),
      ExactWitness (amf_sample (sp_f x) R idx) r }.

Definition exact_of_reading (x : StackAt Sampled)
    (r : EndpointReading (projT1 x))
    (w : forall (R : realType) (idx : amf_index (sp_f x) R),
           ExactWitness (amf_sample (sp_f x) R idx) r)
  : ExactPayloadOfReading x := existT _ r w.
```

`certify_exact` keeps production's body verbatim and reads `p R idx`;
`certify_exact_of_reading` is its twin reading `projT2 p R idx`. The same for
input indistinguishability and ideal proximity. The surface keeps
production's bare rules UNCHANGED and adds three reading rules:

```coq
Notation "s 'certify' 'ExactIndependence' 'of' r 'by' w" :=
  (s ;;; certify_exact_of_reading of (exact_of_reading (tableau_at s) r w))
  (at level 90, left associativity, r at level 0, w at level 0).
```

**Why this is the fix.** The cost in round 1 was not the reading term. It was
the `existT` in the payload of EVERY program: its type argument is the lambda
`fun r => forall R idx, Cert (amf_sample (sp_f x) R idx) r`, so comparing two
spellings of one program forces conversion through `sp_f (tableau_at s)` on
both sides, and the Sampled coordinate holds a `vm_compute`-proved
termination fact. Round 1 already showed the reading term was innocent:
replacing `coalition_endpoint_reading _` by `_`, so that the stored reading
was the closed term the certificate is annotated at, left the cost at 64.6 s.
With the two statements, a program that names no reading carries the
instance's own certificate as its payload, exactly as in production, and the
`existT` appears only in the one program that names a reading.

### What the fix costs and what it buys

- `reading_of` is unchanged and still a function of the program. Its
  equations still go by `exact: erefl`:
  `psl211_colour_published_readingE` and
  `psl211_colour_published_propertyE` in `k12_k14_psl211.v` compile as they
  did.
- `of r` is still a TYPE ASCRIPTION on the evidence: the payload's type is
  `ExactWitness ... r`, so a witness at another reading is rejected where it
  is written.
- **The 7 raw-bind sites of round 1 are down to 0.** The bare spellings and
  the raw `;;; certify_exact of pgl27_exact_witness` form expand exactly as
  in production, so every equation that displays the desugaring is unchanged.
- The `ExactLeakAt` change of round 1 is gone too: `ExactLeakAt`,
  `exact_leaks` and `pgl27_exact_leak4` are production's text unchanged.
- `mk_indistinguishability` keeps production's five clause types and gains
  only the reading inside the constructor application.

### The change count (K6, recounted)

| kind of change | round 1 | round 2 |
|---|---|---|
| return annotation gains `(coalition_endpoint_reading ALG)` | 18 | 18 |
| `@Mk...` constructor application gains the reading | 16 | 16 |
| `InputDistinguishabilityPropAt` use gains the reading | 3 | 3 |
| `(cert : IndistinguishabilityCert sa)` binder gains the reading | 5 | 5 |
| `InputDistinguishabilityObstruction` application gains the reading | 1 | 1 |
| `ExactLeakAt` annotation use | 1 | **0** |
| raw-bind desugaring sites | 7 | **0** |
| **total** | **51** | **43** |

All 43 are type annotations and constructor argument lists. **No proof script
changed in any instance file.**

## 2. Everything recompiled against the new framework

| file | rocq s |
|---|---|
| `staged/manifest/pgg_tableau.v` | 12.8 |
| `staged/manifest/pgg_tableau_syntax.v` | 4.3 |
| `staged/manifest/pgg_tableau_reading.v` | 3.6 |
| `staged/instances/pgl27/tableau/pgl27_tableau_algebraic.v` | 3.6 |
| `staged/instances/pgl27/tableau/pgl27_tableau_executable.v` | 3.7 |
| `staged/instances/pgl27/tableau/pgl27_tableau_observed.v` | 3.9 |
| `staged/instances/pgl27/tableau/pgl27_tableau_sampled.v` | 3.7 |
| `staged/instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` | **8.6** |
| `staged/instances/pgl27/tableau/pgl27_tableau_checks.v` | 4.5 |
| `staged/instances/psl211/psl211_reading_constancy.v` | 22.2 |
| `staged/instances/psl211/tableau/*.v` (six files) | 3.8 to 5.1 |
| `staged/instances/psl211/psl211_colour_reading.v` | 16.1 |
| `staged/instances/kim2025/tableau/*.v` (five files) | 3.6 to 7.7 |
| `k5_default_reading.v` | 4.4 |
| `k7_k11_tails.v` | 4.7 |
| `k12_k14_psl211.v` | 44.9 (40.8 of it two `Print Assumptions`) |
| `k17_vacuity.v` | 5.8 |

All `rc=0`. Nothing over 120 s; nothing over 25 s apart from the two
`Print Assumptions`. K5, K7 to K10, K12 to K14 and K17 all still hold, with
their files byte-identical to round 1.

## 3. The remaining rows

### K15 — the distinguishability GO, the obstruction program measured apart

`k15a_distinguishable.v`, `rc=0`, **rocq 4.6 s**. The card-identity sentence
IS an obstruction of the existing kind, at the reciprocal of the order of the
shuffle group:

```coq
Lemma psl211_dealt_input_distinguishable (R : realType)
    (secretP : R.-fdist bool) :
  InputDistinguishabilityPropAt (psl211_dealt_sample secretP)
    (coalition_endpoint_reading psl211_algebra)
    ((#|pgg_G psl211_M|%:R)^-1 : R).
```

The witnesses are `psl211_perdeck_coalition`, three of the twelve positions,
below the threshold of six by `psl211_perdeck_coalition_below_k`, and the two
chiralities `true` and `false` of one deal. The number is one cut's mass,
`1/660`, and the route is the one round 1 predicted: `psl211_dealt_raw_countE`
gives the two fibre counts 0 and 1, `psl211_dealt_fiberE` turns them into
cardinalities, `psl211_dealt_massE` reads each as a mass of the uniform cut
law, and `leq_var_dist` of `infotheo/probability/variation_dist.v:51` bounds
the sum of absolute differences below by the one term at
`psl211_dealt_view`. The number and the coalition are exactly what round 1
predicted; nothing turned out different.

Each mass is pinned in a `have` naming ONE chirality and the two are brought
together in term mode, as `psl211_dealt_constancy_false` does, because a
rewrite in a goal holding both chiralities searches a goal holding both deck
tables.

**A second conversion trap, found and fixed here.** The goal the existential
leaves reads the endpoints through the identity reading, and the two masses
are stated at the bare reader. Leaving that identification to the conversion
that closes the goal does NOT return: the first attempt ran 6 CPU minutes and
was killed, and the second, which only moved the cut-law rewrite, ran 423 s
and was killed too. The fix is to discharge the identification in its own
`have`, in a statement naming one chirality, where it is one iota step and
one eta step:

```coq
have Hred (b : bool) :
    (fun g : cutT => @er_of_endpoints psl211_algebra
        (coalition_endpoint_reading psl211_algebra) psl211_perdeck_coalition
        (@static_coalition_obs psl211_algebra psl211_dealt_params
           psl211_perdeck_coalition b g))
  = @static_coalition_obs psl211_algebra psl211_dealt_params
      psl211_perdeck_coalition b.
  exact: erefl.
```

then `rewrite (Hred true) (Hred false) (psl211_dealt_sample_cut_distE
secretP); exact: Hle.` With it the lemma costs 4.6 s. **The rule to carry to
the landing: at PSL(2,11), never let the reading wrapper be removed by the
conversion that closes a goal holding both chiralities; remove it by an
`erefl` lemma stated at one chirality first.**

The obstruction program is `k15b_obstruction.v`, `rc=0`, **rocq 4.4 s**:

```coq
Definition psl211_dealt_obstruction
  : ObstructionPayload (tableau_at psl211_dealt_prefix) :=
  fun (R : realType) (secretP : R.-fdist bool) =>
    @InputDistinguishabilityObstruction R psl211_algebra psl211_dealt_params
      (amf_sample psl211_dealt_family R secretP)
      (coalition_endpoint_reading psl211_algebra)
      ((#|pgg_G psl211_M|%:R)^-1).

Lemma psl211_dealt_obstruction_prop :
  ObstructionPayloadProp psl211_dealt_obstruction.

Definition psl211_dealt_obstruction_published : PublishedObstruction :=
  psl211_dealt_prefix
    |> publish Obstruction psl211_dealt_obstruction
       by psl211_dealt_obstruction_prop BaselineClassicalOnly.

Lemma psl211_dealt_obstruction_published_kindE :
  published_obstruction_kind psl211_dealt_obstruction_published
  = psl211_dealt_obstruction.
Proof. exact: erefl. Qed.

Corollary psl211_dealt_no_close_ideal (R : realType) (secretP : R.-fdist bool)
    (eps : R) :
  eps + eps < (#|pgg_G psl211_M|%:R)^-1 ->
  forall cert : IndistinguishabilityCert (psl211_dealt_sample secretP)
                  (coalition_endpoint_reading psl211_algebra),
    var_dist (sa_cut_dist (psl211_dealt_sample secretP)) (ic_ideal cert)
    <= eps -> False.
```

**K15 is GO**, at c = 1/660, the coalition `psl211_perdeck_coalition` and the
two chiralities, exactly as round 1 predicted. One model now carries two
programs at two readings: `psl211_colour_published` certifying exact
independence of the COLOUR reading below six positions, and
`psl211_dealt_obstruction_published` publishing input distinguishability of
the CARD-IDENTITY reading at three. That pair is what the spec was written
for, and neither program was writable before the index.

NOT measured, and removed from the split: `psl211_dealt_obstruction_published`'s
`_pathE` equation and `Print Assumptions` on it. They were in the combined
file that did not return, and I dropped both when splitting, so I cannot say
which of the two was the cost. Both should be re-measured at the landing, one
at a time.

### K11 for ideal proximity — the certificate route, ATTEMPTED AND NOT CLOSED

The route is right and the statement is written, but the construction does
NOT compile. It is in `attempts/k11c_idealproximity_ATTEMPT.v`, which is off
the compile path; `k7_k11_tails.v` is the round-1 file and is green.

The error is at the constructor application:
`Cannot apply lemma (MkIdealProximityCert (ipc_eps:=ipc_eps cert))`. What the
application will not accept is the third field: `ipc_secret` must have type
`{RV (sa_sampleP sa) -> ew_secretT (exact_witness_postprocessing Hf
(ipc_witness cert))}` and the term given has `ew_secretT (ipc_witness cert)`.
The two are equal by one iota step through the record the construction
builds, but `exact_witness_postprocessing` is built by `apply` and closed
with `Defined`, and the application does not see through it. The next attempt
should build that witness by a `Definition` with an explicit
`@MkExactWitness` instead, or cast the field type.

The statement attempted was:

```coq
Definition idealproximity_cert_postprocessing (r r' : EndpointReading A)
    (f : forall C : {set seats}, @er_readT A r C -> @er_readT A r' C)
    (Hf : reading_factors f) (cert : IdealProximityCert sa r)
  : IdealProximityCert sa r'.

Lemma idealproximity_cert_postprocessing_epsE ... :
  ipc_eps (idealproximity_cert_postprocessing Hf cert) = ipc_eps cert.
Lemma idealproximity_cert_postprocessing_idealE ... :
  ipc_ideal (idealproximity_cert_postprocessing Hf cert) = ipc_ideal cert.

Corollary idealproximity_prop_postprocessing ... (Hview) (Hideal) :
  IdealProximityPropAt (idealproximity_cert_postprocessing Hf cert)
    (ipc_eps cert).
```

The certificate's witness is replaced by the post-processed one, the ideal
model, the secret and the number are untouched, and `ipc_close` at the
coarser reading would follow from `ipc_close` at the finer one by one
`var_dist_fdistmap`: on the certificate both sides are joint laws of a
reading with a secret and both are images under the map that carries the
reading and leaves the secret alone. **No lemma pushing a map through a
product is needed**, which is what blocked the free-reading route in round 1,
so the route is still the right one. It is the record construction and not
the mathematics that is unfinished.

### The mutation messages

`msg/` holds, for each guarded command, a copy without its `Fail` and the
message the compile produced. `rocq compile` prints nothing for a `Fail` that
does fail, so this is the only way to read them.

- `msg/k5_rebuild.v` / `.msg` — the K5 field-by-field rebuild at
  `blind_reading`. The message is a unification failure between
  `pfwd1 [% fun u => er_of_endpoints blind_reading C (static_coalition_obs C
  (sa_arg u) (sa_cut u)), ew_secret w] (x0, y) = ...` and the same statement
  with the bare reader: the independence field is about a different random
  variable, which is exactly what the guard asserts.
- `msg/k10_two_readings.v` / `.msg` — the K10 mutation pairing an obstruction
  at one reading with a certificate at another. The message shows the two
  `var_dist` inequalities side by side, one at `er_of_endpoints r' C` and one
  at `er_of_endpoints r C`, and says the term has the first type while the
  second is expected. Invariant 5 of the spec is therefore enforced by
  typing.

Not captured: a mutation message for K14. `k12_k14_psl211.v` carries no
`Fail` guard, so there was nothing to strip; the natural one, claiming the
colour program's `reading_of` at the default reading, was not written.

### Item 6: where the dealer-dealt endpoint obligation should live

`instances/psl211/psl211_exec.v` is frozen. The file proposed is
`instances/psl211/psl211_models.v`, which is NOT frozen and which already
carries the all-decks twins `psl211_alldecks_endpoints` and
`psl211_alldecks_observed`:

```coq
Definition psl211_dealt_endpoints : instance_endpoints_stmt psl211_dealt_params
  := profile_endpointsE psl211_profile_endpoints.

Definition psl211_dealt_observed : OE.ObservedExecution :=
  instance_observed psl211_dealt_terminates psl211_dealt_endpoints
    psl211_dealt_recon.
```

Neither definition needs a Require that file does not already have:
`profile_endpointsE` is in `pgg_instance`, `psl211_profile_endpoints` in
`psl211_endpoints`, and the three run facts in `psl211_exec`, all three of
which `psl211_models.v` already requires for the all-decks twins. So no new
edge is added to the dependency graph and no cycle is possible.
`m6_dealt_endpoints_home.v` has EXACTLY that file's Require lines and nothing
else, and it compiles, `rc=0`, rocq 3.9 s. That is the evidence.

The model family and the programs do NOT belong there. `psl211_dealt_family`
needs `psl211_dealt_sample`, which lives in
`instances/psl211/psl211_colour_reading.v`, and that file requires
`psl211_models.v`, so putting the family in `psl211_models.v` would reverse an
existing edge. A file requiring `pgg_tableau` must not sit below the manifest
at all, which is the cycle the 2026-09-19 manifest note recorded. The family,
the Sampled prefix and the two programs belong in a new
`instances/psl211/tableau/psl211_tableau_dealt.v`, beside the other Tableau
files of the instance, requiring `psl211_colour_reading` and
`pgg_tableau_syntax`.

### Item 5: the two manifest files

Measured, not migrated. `manifest/pgg_tableau_marginal_bounds.v` does NOT
require `pgg_tableau`: its Require lines stop at `pgg_instance`,
`pgg_sample_adapter` and `var_dist_supp`, so the landing does not have to
carry it and it has ZERO sites.
`manifest/pgg_tableau_security_property_relations.v` does require it and has
**14 sites** naming one of the three records, at lines 177, 203, 214, 223,
233, 278, 317, 331, 374, 388, 391, 417, 451 and 568 of the production file;
line 451 is an `@ic_const _ _ _ _` that needs one more `_`. No production
file imports it, so it was not on the compile path of anything measured
here, and it was left for the landing.

## 5. The audits' additions (items 7 to 10)

### S2 — a correction to round 1's own ledger

Round 1's K10 paragraph said "invariant 5 of the spec therefore holds by
typing and not by argument". **That is false and is withdrawn.** A `Fail` on
one proof term records only that `le_trans Hge (Hp C x x' HC)` does not
typecheck; it is not a proof that no cross-reading bound exists, and the
soundness auditor compiled one that does
(`audit-soundness/s_monotone.v:audit_number_ge_across_readings`). The
correct statement: the framework's number bound AS STATED pairs an
obstruction and a certificate at ONE reading, and a bound across two
readings holds when one reading factors through the other and is a separate
lemma, now `indistinguishability_number_ge_across_readings`. Spec 3.4's
"says nothing across two readings" needs the same correction.

### Item 8 — monotonicity of distinguishability in the reading, LANDED

In `staged1/manifest/pgg_tableau_reading.v`, compiled `rc=0`, rocq 3.7 s:

```coq
Definition reading_factors (r r' : CoalitionReading A)
    (f : forall C : {set seats}, @cr_readT A r C -> @cr_readT A r' C) : Prop :=
  forall (C : {set seats}) (v : {ffun seats -> cards}),
    @cr_read A r' C v = f C (@cr_read A r C v).

Lemma reading_factors_coalition_endpoint_reading (r : CoalitionReading A) :
  @reading_factors (coalition_endpoint_reading A) r (@cr_read A r).

Lemma reading_indistinguishability_postprocessing (r r' : CoalitionReading A)
    (f : ...) (Hf : reading_factors r r' f) (c : R) :
  ReadingIndistinguishabilityPropAt sa r c ->
  ReadingIndistinguishabilityPropAt sa r' c.

Lemma input_distinguishability_prop_finer (r r' : CoalitionReading A)
    (f : ...) (Hf : reading_factors r r' f) (c : R) :
  InputDistinguishabilityPropAt sa r' c -> InputDistinguishabilityPropAt sa r c.

Corollary input_distinguishability_prop_coalition_endpoint_reading
    (r : CoalitionReading A) (c : R) :
  InputDistinguishabilityPropAt sa r c ->
  InputDistinguishabilityPropAt sa (coalition_endpoint_reading A) c.

Lemma indistinguishability_number_ge_across_readings (r r' : CoalitionReading A)
    (f : ...) (Hf : reading_factors r r' f)
    (cert : IndistinguishabilityCert sa r) (c c' : R) :
  InputDistinguishabilityPropAt sa r' c ->
  IndistinguishabilityPropAt cert c' -> c <= c'.
```

The cross-reading bound was three lines, so it is in. The file now holds
lemmas about readings and nothing else; `ReadingExactIndependence` and
`exact_independence_of_witness` stay because the PSL(2,11) instance states
its colour theorem at the first.

### Items 7 and 9 — the single record, in `staged1/`

`staged1/` is the one-record tree; `staged/` keeps the two-record variant,
which is green end to end, as the alternative the pass condition asks for.

Applied and COMPILING (`staged1/manifest/pgg_tableau.v` rc=0, rocq 13.0 s;
`staged1/manifest/pgg_tableau_reading.v` rc=0, rocq 3.7 s;
`staged1/instances/psl211/psl211_reading_constancy.v` rc=0, rocq 21.9 s):

- `EndpointReading` -> `CoalitionReading`, `MkEndpointReading` ->
  `MkCoalitionReading`, `er_readT` -> `cr_readT`, `er_of_endpoints` ->
  `cr_read`; `coalition_endpoint_reading` keeps its name.
- `StaticReading`, `static_coalition_reading`, their two lemmas, the bridge
  `static_reading_of_endpoint_reading` and its `E` lemma, and the two
  `_at`/`_endpointE` twins are DELETED.
- ONE free-reading proposition, `ReadingIndistinguishabilityPropAt sa r c`,
  in `pgg_tableau.v`, used by `IndistinguishabilityPropAt`.
- `ExactPropAtReading` and `IdealProximityPropAtReading` are gone, their
  bodies INLINED into `ExactProp` and `IdealProximityPropAt`.
- Statements renamed `certify_reading_exact`,
  `certify_reading_indistinguishability`, `certify_reading_idealproximity`;
  the unindexed `certify_exact`, `certify_indistinguishability` and
  `certify_idealproximity` stay as definitions and are how the default is
  expressed.
- Four reading readers added beside `certify_exact_propertyE`:
  `certify_exact_readingE`, `certify_indistinguishability_readingE`,
  `certify_idealproximity_readingE`, each concluding
  `ab_reading ... R idx = coalition_endpoint_reading (projT1 x)`, and
  `certify_reading_exact_readingE` concluding `= projT1 p`. **Every one
  quantifies over the real field AND the index** (S8).

### Item 7's count — and the STOP

`instances/psl211/psl211_colour_reading.v`, staged two-record against
staged1 one-record: **100 changed lines**, classified as 29
statement/annotation, 12 comment, 1 tactic and 58 unclassified by the
crude classifier (they are continuation lines of the statements above them,
so the honest reading is that the change is overwhelmingly statements and
comments).

**But the file does NOT compile, and the pass condition therefore fails.**
`rc=1` at `psl211_colour_readingE`: "No applicable tactic". Two things
broke, and both are real rework rather than annotation:

1. `psl211_colour_readingE` proved `psl211_colour_view secretP C u =
   sr_read psl211_colour_reading C (arg u) (cut u)` by `ffunP` and `ffunE`
   alone, because with two records the colour reading was written directly
   at the run argument and the cut and no seat reconciliation entered. With
   ONE record the colour reading IS the colour map applied to the endpoint
   map, so this lemma now needs the reconciliation that the two-record file
   proved separately as `psl211_colour_reading_factorsE` (renamed
   `psl211_colour_of_reading_obsE` here, and it has to move above this
   lemma). The two lemmas merge, and the merged proof is the concatenation
   of the two old proofs.
2. `psl211_colour_reading_funE`'s statement cannot be rewritten
   mechanically: `cr_read` takes ONE argument where `sr_read` took two, so
   every use site changes shape rather than name.

Per the pass condition I stopped there and did not rework the proofs.
**Recommendation: the single record is right and the rest of it landed
cleanly; the psl211 file needs a hand pass of about two proofs, not a
mechanical one, and that pass should be its own step of the landing with
the merged lemma named once.** Everything else of items 7, 8 and 9 is in
`staged1/` and compiles.

### Item 10 — not run

`Print Assumptions` on the three tails and on
`input_distinguishability_prop_finer` was not run.

## 4. Still open

- `manifest/pgg_tableau_security_property_relations.v`, 14 sites, counted
  above and not migrated.
- The K14 mutation message, and the `_pathE` and `Print Assumptions` of the
  obstruction program.
- K11 for ideal proximity, as above.
- Item 7 for `instances/psl211/psl211_colour_reading.v` (two proofs), and
  item 10.
