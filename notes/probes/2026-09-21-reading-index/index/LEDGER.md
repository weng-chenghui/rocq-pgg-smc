# Probe B: the reading as an index of the security claim (2026-09-21)

Spec: `notes/20260921-reading-index-and-surface-prepositions-probe-design.md`,
sections 3.2 to 3.4, ledger rows K5 to K15, K17, K18.
Repository HEAD at the start of the probe: `2fc0108`.
Nothing in the production tree was written or recompiled. Everything below
lives under `notes/probes/2026-09-21-reading-index/index/`. Every compile
went through the machine-wide `rocq1` lock, one Rocq process at a time.

## 0. Summary

| row | verdict | where it is shown |
|---|---|---|
| K5 | GO | `k5_default_reading.v` |
| K6 | GO for all four instances, with a measured cost and one conversion regression | `staged/instances/`, section 3 |
| K7 | GO | `staged/manifest/pgg_tableau.v`, `k7_k11_tails.v` |
| K8 | GO, the transfer lemma was already general | `staged/manifest/pgg_tableau.v` |
| K9 | GO | `staged/manifest/pgg_tableau.v` |
| K10 | GO, mutation fails as required | `staged/manifest/pgg_tableau.v`, `k7_k11_tails.v` |
| K11 | GO for exact independence and input indistinguishability; NOT REACHED for ideal proximity | `k7_k11_tails.v` |
| K12 | GO | `k12_k14_psl211.v` |
| K13 | GO, and it corrects a claim in the tree | `k12_k14_psl211.v` |
| K14 | GO, three classical axioms only | `k12_k14_psl211.v`, `assumptions-k14.txt` |
| K15 | NOT REACHED, with the route and the numbers found | section 4 |
| K17 | GO | `k17_vacuity.v` |
| K18 | one file flagged over 120 s, cause identified | section 5 |

Not reached, and honestly so: the fallback design of spec 3.3 was not
implemented and therefore not compared; the restatement of
`psl211_alldecks_obstruction_published` at the default reading was not
written; `manifest/pgg_tableau_security_property_relations.v` was not
migrated; the K5, K10 and K14 mutation ERROR MESSAGES were not captured to a
file, only the `Fail` guards were run. Section 6 says what I think is worth
landing.

## 1. What was built

`staged/` holds copies of the framework files and of the instance Tableau
files, bound to `pgg_smc` by `-R` lines placed AFTER production's in
`_CoqProject`, so a `Require` resolves to the staged copy (Rocq 9.0.0 takes
the LAST matching entry). `compile.py` reports the wall time, which includes
waiting for probe A to release the lock, and the sum of the `-time` sentence
times, which is the number to read.

### The design (spec 3.2, preferred form of 3.3)

```coq
Record EndpointReading (A : PGGAlgebraic) := MkEndpointReading {
  er_readT : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1} -> finType ;
  er_of_endpoints : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    {ffun 'I_(pi_T' (mp_PI (instance_profile A))).+1
       -> 'I_(pgg_N' (mp_M (instance_profile A))).+1} -> er_readT C }.

Definition coalition_endpoint_reading (A : PGGAlgebraic) : EndpointReading A :=
  @MkEndpointReading A
    (fun _ => [the finType of {ffun 'I_(pi_T' (mp_PI (instance_profile A))).+1
                                 -> 'I_(pgg_N' (mp_M (instance_profile A))).+1}])
    (fun _ v => v).

Variant SecurityEvidence (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) : Type :=
  | ExactIndependence (r : EndpointReading A) of ExactWitness sa r
  | InputIndistinguishability (r : EndpointReading A)
      of IndistinguishabilityCert sa r
  | IdealProximity (r : EndpointReading A) of IdealProximityCert sa r.

Definition evidence_reading (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (p : SecurityEvidence sa) : EndpointReading A :=
  match p with
  | @ExactIndependence _ _ _ _ r _ => r
  | @InputIndistinguishability _ _ _ _ r _ => r
  | @IdealProximity _ _ _ _ r _ => r
  end.

Definition ab_reading (q : StackAt AnalysisBridged) (R : realType)
    (idx : amf_index (ab_f q) R) : EndpointReading (projT1 q) :=
  @evidence_reading R (projT1 q) (projT1 (projT2 q)) _ (ab_evidence q R idx).

Definition reading_of (c : ConcludedBound) (p : PublishedAt c) (R : realType)
    (idx : amf_index (ab_f (published_at p)) R)
  : EndpointReading (projT1 (published_at p)) :=
  ab_reading (published_at p) R idx.
```

`SecurityEvidence sa`, the payload type NAMES, `StackAt` and every terminal
keep their types. The reading of each constructor is an implicit argument,
inferred from the witness or the certificate, so `ExactIndependence w` still
reads as it read before.

### Departures from the spec, each forced, each measured

1. **`EndpointReading` is indexed by the algebra alone, not by the execution
   parameters.** Nothing in the record mentions `E`.
   `StaticReading` keeps its `E`, and the bridge is
   `static_reading_of_endpoint_reading E r`, added to the staged
   `pgg_tableau_reading.v` with
   `static_reading_of_coalition_endpoint_readingE` proving that the identity
   endpoint reading IS `static_coalition_reading`, by `exact: erefl`.

2. **The three PAYLOAD types are sigmas.**
   ```coq
   Definition ExactPayload (x : StackAt Sampled) : Type :=
     { r : EndpointReading (projT1 x)
     & forall (R : realType) (idx : amf_index (sp_f x) R),
         ExactWitness (amf_sample (sp_f x) R idx) r }.
   ```
   Forced: `tableau_bind` passes a certify statement UNAPPLIED and its
   payload type is `P x` for one `x`, so a reading argument cannot sit
   between `x` and the payload. The reading is therefore uniform over the
   real field and the model index, which is stronger than the alternative and
   is what makes `reading_of` a function of the program rather than of the
   field. **This sigma is where the conversion regression of section 5 comes
   from, and section 6 proposes the way out.**

3. **The three propositions are thin wrappers over free-reading forms.**
   `ExactPropAtReading`, `IndistinguishabilityPropAtReading` and
   `IdealProximityPropAtReading` take the reading free and no evidence;
   `ExactProp w`, `IndistinguishabilityPropAt cert c` and
   `IdealProximityPropAt cert c` are those at the reading the evidence is
   indexed by. Forced: K11 states a proposition at a second reading, for
   which no certificate exists.

4. **Implicit arguments of a constructor are NOT omitted in a `match` pattern
   in Rocq 9.0.0.** `ExactIndependence _` is rejected with "The constructor
   ExactIndependence (in type SecurityEvidence) is expected to be applied to
   2 arguments while it is actually applied to 1 argument." Every pattern in
   `evidence_property`, `EvidenceProp`, `ConcludePayload` and
   `evidence_conclude` gained one `_`, and `evidence_reading` reads the
   reading through `@`-patterns.

5. **`manifest/pgg_tableau_security_property_relations.v` was not migrated.**
   No production file imports it (only a probe of 2026-09-20 does), so it is
   not on the compile path of anything the ledger needed. It has 10 sites
   that mention one of the three records and would need the same treatment.
   Recorded, not done.

### Surface used in the probe

Probe A owns the surface. So that K6 could measure the index alone, the
staged syntax file KEEPS the bare spellings and ADDS the reading forms:

```coq
Notation "s 'certify' 'ExactIndependence' w" :=
  (s ;;; certify_exact of (@exact_of_reading (tableau_at s) _ w)) ...
Notation "s 'certify' 'ExactIndependence' 'of' r 'by' w" :=
  (s ;;; certify_exact of (@exact_of_reading (tableau_at s) r w)) ...
```

and the same for the other two properties. In the second rule the clause
`of r` IS a type ascription on the evidence: the payload's type is
`ExactWitness ... r`, so a witness at another reading is rejected where it is
written. That is the property spec 3.3 wanted from the index, and the probe
confirms it.

## 2. The rows

### K5 — GO

`k5_default_reading.v`, `rocq 4.3 s`. It carries VERBATIM copies of the three
records and the four propositions of `manifest/pgg_tableau.v` at HEAD
`2fc0108`, under a `0` suffix, and proves, with `r0` for
`coalition_endpoint_reading A`:

```coq
Lemma k5_exact (w : ExactWitness sa r0) :
  ExactProp w = ExactProp0 (exact0_of w).
Lemma k5_exact_back (w : ExactWitness0 sa) :
  ExactProp (exact_of0 w) = ExactProp0 w.
Lemma k5_indistinguishability (cert : IndistinguishabilityCert sa r0) (c : R) :
  IndistinguishabilityPropAt cert c
  = IndistinguishabilityPropAt0 (indist0_of cert) c.
Lemma k5_indistinguishability_back (cert : IndistinguishabilityCert0 sa)
    (c : R) :
  IndistinguishabilityPropAt (indist_of0 cert) c
  = IndistinguishabilityPropAt0 cert c.
Lemma k5_idealproximity (cert : IdealProximityCert sa r0) (c : R) :
  IdealProximityPropAt cert c = IdealProximityPropAt0 (prox0_of cert) c.
Lemma k5_input_distinguishability (c : R) :
  InputDistinguishabilityPropAt sa r0 c = InputDistinguishabilityPropAt0 sa c.
```

all by `exact: erefl`, each universally quantified over the evidence, the
evidence being a VARIABLE and never a constructor application.

**What is and is not convertible.** `exact0_of`, `indist0_of`, `prox0_of` and
the two back maps are FIELD-BY-FIELD copies with no transport anywhere in
them, and they typecheck; so at the default reading each field type of the
indexed record is convertible with the corresponding field type of today's
record, and an existing witness is a witness of the indexed record and back.
What is NOT convertible is the two record TYPES, which are distinct
inductives: `ExactWitness sa r0 = ExactWitness0 sa` cannot be stated by
`erefl`, which is why the equations go through a rebuild. Conversion needs
eta (today's text writes the executed view as `sa_coalition_view ... C`, the
indexed text as `fun u => er_of_endpoints r C (sa_coalition_view ... C u)`)
and one iota step on the reading record. It does NOT need the evidence to be
a constructor application, so **existing `erefl` equations survive**.

Mutation, guarded by `Fail` in the same file, with `blind_reading` the
reading sending every endpoint map to the constant map at card zero: the
field-by-field rebuild does not typecheck, and
`ExactProp w = ExactProp0 w0` has no `erefl` proof.

Two traps found and recorded:
- `Fail Lemma name : statement.` does NOT fail here. A `Fail` on a `Lemma`
  command checks the statement alone, and an equation between two
  propositions typechecks at every reading. A mutation of an equation must be
  written `Fail Definition name : statement := erefl.`
- `rocq compile` prints NOTHING for a `Fail` that does fail, so the guard is
  machine-checked but its message is not on the console. Capturing the
  messages needs the `Fail` stripped and the compile allowed to fail; that
  was not done (see section 0).

### K6 — GO, with the cost measured

`pgl27_exact_witness`, `pgl27_word_cert` and `pgl27_word_proximity_cert`
typecheck against the staged framework **with no change to their proof
scripts**. The whole pgl27 Tableau chain compiles, `pgl27_tableau_algebraic`
through `pgl27_tableau_checks`, all `rc=0`.

Changes counted by the generator script over the staged instance files
(pgl27, kim2025, psl211, s5):

| kind of change | count |
|---|---|
| return annotation gains `(coalition_endpoint_reading ALG)` | 18 |
| `@Mk...` constructor application gains the reading | 16 |
| `InputDistinguishabilityPropAt` use gains the reading | 3 |
| `(cert : IndistinguishabilityCert sa)` binder gains the reading (`psl211_reading_constancy.v`) | 5 |
| `ExactLeakAt` annotation use gains `@exact_of_reading` | 1 |
| raw-bind desugaring sites `;;; certify_X of cert` | 7 |
| `InputDistinguishabilityObstruction` application gains the reading | 1 |
| **total** | **51** |

Of these, the first four kinds are type annotations, which the spec allows.
`ExactLeakAt`'s proof script (`pgl27_exact_leak4`) survived unchanged even
though the annotation now applies the reading inside the mutual-information
term.

**The changes a notation cannot absorb are the seven raw-bind sites.** They
are the definitions and equations that write a program through
`tableau_bind` directly, to display the desugaring. They must name the stack
coordinate explicitly:

```coq
;;; certify_indistinguishability
       of (@indistinguishability_of_reading
            (tableau_at (pgl27_dealt ;;; sample_step of pgl27_word_family))
            (coalition_endpoint_reading pgl27_algebra) pgl27_word_cert)
```

Leaving the coordinate implicit does not elaborate: unifying `sp_f ?x` with
`pgl27_word_family` is a projection unification Rocq does not solve, and the
error names `?x` and `?r` together.

### K7, K8, K9 — GO

All three composition laws are proved at a free reading INSIDE the staged
framework, with their proof scripts otherwise unchanged. `k7_k11_tails.v`
records their types with `Check`:

```coq
Lemma exact_tail (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E)) (r : EndpointReading A)
    (w : ExactWitness sa r)
    (Hview : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
       @sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C
       = (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u))) :
  ExactProp w.

Lemma indistinguishability_tail (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (r : EndpointReading A) (cert : IndistinguishabilityCert sa r) :
  IndistinguishabilityPropAt cert (cert_eps cert).

Lemma idealproximity_tail (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (r : EndpointReading A) (cert : IdealProximityCert sa r)
    (Hview : ...) (Hideal : ...) :
  IdealProximityPropAt cert (ipc_eps cert).
```

`exact_tail` needed one change beyond the binder: the `have Hi` is now stated
at the reading-composed view. `indistinguishability_tail` needed the two maps
handed to the transfer lemma to be the reading-composed ones.
`idealproximity_tail` needed one `rewrite /IdealProximityPropAtReading` to
expose the wrapper before `rewrite (Hview C) (Hideal C)`.

**K8, the transfer lemma.** It is `var_dist_fdistmap_transfer`,
`security/pgg_collusion_bound.v:987`, inside `Section var_dist_transfer` with
`Variables (fx fy : A -> B)`:

```coq
Lemma var_dist_fdistmap_transfer :
  var_dist (fdistmap fx P) (fdistmap fy P) <= delta + delta.
```

It is stated for ARBITRARY maps and not for `static_coalition_obs`, so it was
**already general**. `pgg_collusion_bound` is frozen, and invariant 7 of the
spec does not bite: no generalisation of a frozen file is needed.

### K10 — GO

Both lemmas are at a free reading, with the SAME reading on both sides
enforced by the certificate's index:

```coq
Lemma indistinguishability_number_ge_of_input_distinguishability
    (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E)) (r : EndpointReading A)
    (cert : IndistinguishabilityCert sa r) (c c' : R) :
  InputDistinguishabilityPropAt sa r c ->
  IndistinguishabilityPropAt cert c' -> c <= c'.

Lemma no_indistinguishability_cert_ideal_close_of_input_distinguishability
    (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E)) (r : EndpointReading A)
    (c eps : R) :
  InputDistinguishabilityPropAt sa r c -> eps + eps < c ->
  forall cert : IndistinguishabilityCert sa r,
    var_dist (sa_cut_dist sa) (ic_ideal cert) <= eps -> False.
```

The mutation, in `k7_k11_tails.v`, is machine-checked to fail:

```coq
Fail Definition k10_mutation (r r' : EndpointReading A)
    (cert : IndistinguishabilityCert sa r') (c c' : R)
    (Hd : InputDistinguishabilityPropAt sa r c)
    (Hp : IndistinguishabilityPropAt cert c') : c <= c' :=
  let: ex_intro C (ex_intro x (ex_intro x' (conj HC Hge))) := Hd in
  Order.POrderTheory.le_trans Hge (Hp C x x' HC).
```

The statement typechecks, both sides being propositions, and the proof term
does not: at two readings the two propositions are about two different
pushforwards. Invariant 5 of the spec therefore holds by typing and not by
argument.

### K11 — GO for two of the three

The factorisation is stated on the readings, not on a model:

```coq
Definition reading_factors (r r' : EndpointReading A)
    (f : forall C : {set seats}, @er_readT A r C -> @er_readT A r' C) : Prop :=
  forall (C : {set seats})
         (v : {ffun seats -> 'I_(pgg_N' (mp_M (instance_profile A))).+1}),
    @er_of_endpoints A r' C v = f C (@er_of_endpoints A r C v).
```

Input indistinguishability:

```coq
Lemma reading_indistinguishability_postprocessing_at
    (r r' : EndpointReading A)
    (f : forall C : {set seats}, @er_readT A r C -> @er_readT A r' C)
    (Hf : reading_factors f) (c : R) :
  IndistinguishabilityPropAtReading sa r c ->
  IndistinguishabilityPropAtReading sa r' c.
```

Exact independence, as a construction rather than a consequence:

```coq
Definition exact_witness_postprocessing (r r' : EndpointReading A)
    (f : forall C : {set seats}, @er_readT A r C -> @er_readT A r' C)
    (Hf : reading_factors f) (w : ExactWitness sa r) : ExactWitness sa r'.

Lemma exact_witness_postprocessing_secretE ... :
  ew_secret (exact_witness_postprocessing Hf w) = ew_secret w.

Corollary exact_prop_postprocessing (r r' : EndpointReading A) (f) (Hf)
    (w : ExactWitness sa r) (Hview : ...) :
  ExactProp (exact_witness_postprocessing Hf w).
```

The exact case is the fourth conjunct of `ExactProp` read as a construction,
and it runs from the finer reading to the coarser one only, which is
invariant 4.

**Ideal proximity, NOT REACHED.** The obstacle is exact and is recorded here.
The free-reading proposition compares a joint law with a PRODUCT of two
marginals, and pushing the reading forward turns the left side into
`fdistmap F (...)` by `fdistmap_comp` but leaves the right side needing

```coq
fdistmap (fun p : T1 * T2 => (g p.1, p.2)) (P `x Q) = (fdistmap g P) `x Q
```

which I did not find in infotheo and did not prove. A `Search _ fdistmap (_
`x _).` is left at the end of `k7_k11_tails.v` for the next session. There is
a second route that avoids the lemma altogether and is probably the right
one: state post-processing on the CERTIFICATE rather than on the free-reading
proposition, building `cert' : IdealProximityCert sa r'` from `cert` with
`ipc_witness` replaced by `exact_witness_postprocessing Hf (ipc_witness
cert)` and the same `ipc_eps`. Then both sides of `ipc_close` are joint laws,
both are images under `fun p => (f C p.1, p.2)`, and one
`var_dist_fdistmap` closes it with no product lemma. Not written.

A `` `o `` trap was found: `f C `o X` in a bare `have ->` equation leaves the
distribution of the right factor unsolved ("Unable to find an instance for
the variables t, t"). The composition has to be written out as
`fun u => f C (X u)` and the view lemma applied to the result.

### K12 — GO

```coq
Definition psl211_colour_endpoint_reading : EndpointReading psl211_algebra :=
  @MkEndpointReading psl211_algebra
    (fun _ => [the finType of {ffun seats -> bool}])
    psl211_colour_of_reading.

Lemma psl211_colour_endpoint_readingTE (C : {set seats}) :
  @er_readT psl211_algebra psl211_colour_endpoint_reading C
  = [the finType of {ffun seats -> bool}].
Proof. exact: erefl. Qed.

Lemma psl211_colour_endpoint_reading_staticE (C : {set seats})
    (b : ex_inputT psl211_dealt_params) (g : cutT) :
  sr_read (static_reading_of_endpoint_reading psl211_dealt_params
             psl211_colour_endpoint_reading) C b g
  = sr_read psl211_colour_reading C b g.
Proof. exact: (esym (psl211_colour_reading_factorsE C b g)). Qed.
```

The static form is `psl211_colour_reading` pointwise, by the instance's own
factorisation lemma and nothing else. Departure: the identification is
pointwise and not an equation between the two `StaticReading` records; a
record equality would need funext under the dependent second field and was
not attempted.

### K13 — GO, and it corrects a claim in the tree

`sampled_viewE_prop` needs the three run facts, and of them the dealer-dealt
run of PSL(2,11) names only two in the tree. The header of
`instances/psl211/psl211_colour_reading.v` states as a fact that "The
dealer-dealt parameters carry no endpoints statement, so there is no Observed
and no Sampled level over them, no program and no path." **That is true of
what the tree HAS and false of what is provable.** The missing fact is one
line, from the profile's own abstract-readout equation, which is exactly how
the all-decks run gets its own:

```coq
Definition psl211_dealt_endpoints : instance_endpoints_stmt psl211_dealt_params
  := profile_endpointsE psl211_profile_endpoints.

Definition psl211_dealt_observed : OE.ObservedExecution :=
  instance_observed psl211_dealt_terminates psl211_dealt_endpoints
    psl211_dealt_recon.

Definition psl211_dealt_family : AnalysisModelFamily psl211_dealt_observed :=
  @MkAnalysisModelFamily psl211_dealt_observed
    (fun R : realType => R.-fdist bool)
    (fun (R : realType) (secretP : R.-fdist bool) =>
       psl211_dealt_sample secretP).

Definition psl211_dealt_prefix : Tableau Sampled :=
  psl211_algebra dealt fuel psl211_fuel
    execute terminates by psl211_dealt_terminates
            endpoints  by psl211_dealt_endpoints
            recon      by psl211_dealt_recon
    sample psl211_dealt_family.

Lemma psl211_dealt_prefix_viewE :
  sampled_viewE_prop (sp_f (tableau_at psl211_dealt_prefix)).
Proof. exact: (proj2 (tableau_thm psl211_dealt_prefix)). Qed.
```

`profile_endpointsE` is `protocol/pgg_instance.v:757` and
`psl211_profile_endpoints` is `instances/psl211/psl211_endpoints.v:50`, which
is a frozen file and was NOT compiled; its `.vo` was required as it stands.
The model family is indexed by the prior on the chirality, one member per
prior at every real field, because the instance's colour theorems hold under
every prior and the two that refute independence need one giving mass to
both chiralities. The header sentence quoted above should be corrected at the
landing.

### K14 — GO

```coq
Definition psl211_colour_witness (R : realType) (secretP : R.-fdist bool)
  : ExactWitness (psl211_dealt_sample secretP) psl211_colour_endpoint_reading.

Definition psl211_colour_published : Published :=
  psl211_dealt_prefix
    certify ExactIndependence of psl211_colour_endpoint_reading
            by psl211_colour_witness
    |> publish StaticExecutedOnly BaselineClassicalOnly.

Lemma psl211_colour_published_readingE (R : realType)
    (secretP : R.-fdist bool) :
  reading_of psl211_colour_published R secretP
  = psl211_colour_endpoint_reading.
Proof. exact: erefl. Qed.

Lemma psl211_colour_published_propertyE (R : realType)
    (secretP : R.-fdist bool) :
  security_property_of psl211_colour_published R secretP
  = ExactIndependenceProperty.
Proof. exact: erefl. Qed.

Lemma psl211_colour_published_pathE :
  published_path psl211_colour_published
  = @MkAnalysisPath psl211_dealt_observed AnalysisBridged psl211_dealt_family
      StaticExecutedOnly BaselineClassicalOnly.
Proof. exact: erefl. Qed.
```

The witness's independence field is `psl211_colour_reading_indep` transported
along `psl211_colour_reading_factorsE`; nothing else.

`Print Assumptions psl211_colour_published` and `Print Assumptions
psl211_colour_published_readingE`, saved in `assumptions-k14.txt`, report
`propositional_extensionality`, `functional_extensionality_dep` and
`constructive_indefinite_description` and nothing else. No custom axiom, no
`s5_group_order_eq`. Invariant 1 holds. Each `Print Assumptions` costs about
20 s.

**This is the row the spec exists for.** One model, `psl211_dealt_sample`,
now carries a program certifying exact independence AT THE COLOUR READING,
and the reading is on the published value and readable by conversion. The
card-identity sentence about the same model is K15.

### K17 — GO

`k17_vacuity.v`, `rocq 6.1 s`. All hypotheses inhabited at PGL(2,7) and at
the default reading:

- K7 at the exact model: `k17_exact_prop : ExactProp (pgl27_exact_witness R tt)`
  from `exact_tail` and `proj2 (tableau_thm pgl27_exact_sampled) R tt`.
- K8 at the word model of the same algebra:
  `k17_indistinguishability_prop`.
- K9 at the word model's proximity certificate: `k17_idealproximity_prop`,
  with the two link lemmas taken from `pgl27_word_sampled` and
  `pgl27_prior_exact_sampled`.
- K10: `k17_distinguishable_at_0 : InputDistinguishabilityPropAt (amf_sample
  pgl27_word_family R secretP) r0 0`, the empty coalition and one run
  argument taken twice, closed by `var_dist_refl`; and
  `k17_number_bound : 0 <= cert_eps (pgl27_word_cert secretP)`. Zero is the
  only number this model supports, the same file proving it not
  distinguishable above 2^-39.
- K11: `k17_identity_factors : @reading_factors pgl27_algebra r0 r0 (fun _ v
  => v)` by `by []`, and the witness and proposition it carries.

So the hypothesis set is not vacuous, and the two properties that mention a
certificate and the one that does not are all inhabited over one algebra.

### K15 — NOT REACHED

I did not prove it and I will not claim it. What I did establish is the route
and the numbers, so the next session can finish it or reject it on evidence.

The ingredients are all in `instances/psl211/psl211_reading_constancy.v`:

- `psl211_perdeck_coalition`, three of the twelve positions, with
  `psl211_perdeck_coalition_below_k` proving it below the threshold of six.
- `psl211_dealt_view`, a card-identity reading of those three positions.
- `psl211_dealt_fiber b`, the cuts carrying the encoder deck of chirality `b`
  to that reading, with `psl211_dealt_fiberE` giving its cardinality and
  `psl211_dealt_raw_countE : psl211_dealt_raw_count true = 0 /\
  psl211_dealt_raw_count false = 1`.
- `psl211_dealt_sample_cut_distE`, the cut law of the fixed-dealer model is
  uniform on the 660-element group whatever the prior.

So the pushforward of the card-identity reading at chirality `true` gives
`psl211_dealt_view` mass 0 and at `false` mass 1/660, and since `var_dist` is
the sum of absolute differences, the two readings are at least 1/660 apart.
That is a positive number, a coalition below the threshold and two run
arguments, which is exactly `InputDistinguishabilityPropAt
(psl211_dealt_sample secretP) (coalition_endpoint_reading psl211_algebra)
(1/660)` together with `0 < 1/660`, so the card-identity sentence IS an
obstruction of the existing kind. **Expected verdict GO at c = 1/660**, and
the missing work is two steps: reading the fibre cardinality off the uniform
law as a mass, and bounding the sum of absolute differences below by one of
its terms. Neither is deep and neither is written.

Note that this number does not come from `psl211_dealt_reading_indep_false`,
which is a failed independence and gives no two run arguments by itself, as
the spec anticipated. It comes from the fibre counts that lemma's proof uses.

## 3. The conversion regression (K18, and the reason for section 6)

Measured on one file, with the SAME text compiled twice: once against
production's framework (`baseline/`, a copy of
`instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` compiled with
production's `-R` lines only) and once against the staged framework.

| | rocq s | slowest sentence |
|---|---|---|
| production baseline | **6.8** | 2.2 s, a `From mathcomp Require Import` |
| staged, reading index | **86.1** | **`exact: erefl` 64.6 s**, then two `Qed.` at 6.3 s and 5.2 s |

The 64.6 s sentence is `pgl27_word_published_sampledE`:

```coq
Lemma pgl27_word_published_sampledE :
  (pgl27_word_sampled
     certify InputIndistinguishability pgl27_word_cert
     |> publish IdealFinite BaselineClassicalOnly)
  = pgl27_word_published.
Proof. exact: erefl. Qed.
```

The two sides differ only by unfolding the name `pgl27_word_sampled`. Before
the index, the payload was `pgl27_word_cert` and mentioned nothing of the
stack, so conversion compared the two programs structurally. With the sigma
payload the term carries the type family `fun r => forall R idx,
IndistinguishabilityCert (amf_sample (sp_f (tableau_at s)) R idx) r`, and `s`
is the name on one side and its unfolding on the other, so conversion has to
reduce `sp_f (tableau_at ...)` through the whole Sampled coordinate, which
holds the `vm_compute`-proved termination fact.

I tried one mitigation and it did NOT work: writing `_` for the reading in
the bare notation, so that the stored reading is the closed term the
certificate is annotated at, left the cost at 64.6 s. That is the evidence
that the cost is the SIGMA and not the reading term.

Timings of everything else, `rocq` column, all under 120 s:

| file | rocq s |
|---|---|
| `staged/manifest/pgg_tableau.v` | 13.8 |
| `staged/manifest/pgg_tableau_syntax.v` | 4.2 |
| `staged/manifest/pgg_tableau_reading.v` | 3.9 |
| `staged/instances/pgl27/tableau/pgl27_tableau_algebraic.v` | 3.7 |
| `staged/instances/pgl27/tableau/pgl27_tableau_executable.v` | 3.7 |
| `staged/instances/pgl27/tableau/pgl27_tableau_observed.v` | 3.9 |
| `staged/instances/pgl27/tableau/pgl27_tableau_sampled.v` | 3.7 |
| `staged/instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` | **86.1 FLAGGED** |
| `staged/instances/pgl27/tableau/pgl27_tableau_checks.v` | 4.7 |
| `staged/instances/psl211/psl211_reading_constancy.v` | 21.8 |
| `staged/instances/psl211/psl211_colour_reading.v` | 16.2 |
| `k5_default_reading.v` | 4.3 |
| `k7_k11_tails.v` | 4.5 |
| `k12_k14_psl211.v` | 45.0 (of which 40.8 is two `Print Assumptions`) |
| `k17_vacuity.v` | 6.1 |

The PSL(2,11) and Kim Tableau chains all compile, `rc=0`, and neither shows
the regression:

| file | rocq s |
|---|---|
| `staged/instances/psl211/tableau/psl211_tableau_algebraic.v` | 3.9 |
| `staged/instances/psl211/tableau/psl211_tableau_executable.v` | 3.9 |
| `staged/instances/psl211/tableau/psl211_tableau_observed.v` | 5.0 |
| `staged/instances/psl211/tableau/psl211_tableau_sampled.v` | 3.9 |
| `staged/instances/psl211/tableau/psl211_tableau_analysis_bridged.v` | 4.9 |
| `staged/instances/psl211/tableau/psl211_tableau_checks.v` | 4.2 |
| `staged/instances/kim2025/tableau/five_card_tableau_algebraic.v` | 3.5 |
| `staged/instances/kim2025/tableau/five_card_tableau_executable.v` | 3.5 |
| `staged/instances/kim2025/tableau/five_card_tableau_observed.v` | 3.5 |
| `staged/instances/kim2025/tableau/five_card_tableau_sampled.v` | 3.8 |
| `staged/instances/kim2025/tableau/five_card_tableau_analysis_bridged.v` | 7.5 |

So the regression is confined to ONE file and, inside it, to the two
program-equality lemmas that compare a named Sampled value with its
unfolding. Kim's bridged file is 1288 lines and costs 7.5 s with the index
in place, which is evidence that the sigma is cheap wherever a program is
not compared with its own unfolding.

`psl211_tableau_analysis_bridged.v` needed one change beyond the mechanical
ones: `@InputDistinguishabilityObstruction` gained the reading, because the
obstruction kind now carries it (spec 3.5, `InputDistinguishability of r at
c`):

```coq
    @InputDistinguishabilityObstruction R psl211_algebra
      psl211_alldecks_params (amf_sample psl211_exact_family R idx)
      (coalition_endpoint_reading psl211_algebra)
      ((#|pgg_G psl211_M|%:R)^-1).
```

Its four consequence lemmas and `psl211_alldecks_obstruction_published`
compile unchanged, so the all-decks obstruction IS carried at the default
reading, with its `_pathE` and the rest of `psl211_tableau_checks.v` still
holding. That is most of what the last bullet of the task asked for; what was
NOT done is a separate restatement of it naming the default reading in its
own text.

## 4. What I think is worth landing, and what is not

**Worth landing.**

1. `EndpointReading`, `coalition_endpoint_reading`, the index on the three
   records, `evidence_reading`, `ab_reading`, `reading_of`, and the three
   free-reading propositions. K5 shows the default costs nothing in meaning,
   K7 to K11 show the mathematics goes through, and K14 shows the row the
   spec was written for becomes a program.
2. `static_reading_of_endpoint_reading` and its two identification lemmas in
   `pgg_tableau_reading.v`. Cheap, and it keeps `StaticReading` as the
   general notion exactly as spec 3.2 says.
3. The `of r` clause as a type ascription. It works, and a program's text
   cannot name a reading its evidence is not about.
4. K13's one-line endpoints fact for the dealer-dealt PSL(2,11) run, and the
   correction of the header sentence in `psl211_colour_reading.v` that says
   no such level exists.
5. K11 for exact independence and input indistinguishability.

**Not worth landing as it stands: the sigma payload.** Section 3 measures a
13-fold regression on one instance file, and the cause is structural. The way
out that I believe works, and that I did NOT probe, is to let the reading
enter the STATEMENT as a stack-indexed family rather than the PAYLOAD as a
sigma:

```coq
Definition certify_exact_at
    (r : forall x : StackAt Sampled, EndpointReading (projT1 x))
    (x : StackAt Sampled) (q : StackProp Sampled x)
    (p : forall (R : realType) (idx : amf_index (sp_f x) R),
           ExactWitness (amf_sample (sp_f x) R idx) (r x))
  : Tableau AnalysisBridged := ...
```

`tableau_bind` infers its payload family `P` from the statement it is given,
and `certify_exact_at (fun _ => psl211_colour_endpoint_reading)` is such a
statement, so the surface `of r` can supply `fun _ => r` and the payload type
goes back to a plain function, as it is today. The default rule keeps
`certify_exact` with the payload at `coalition_endpoint_reading (projT1 x)`,
which mentions the coordinate no more than today's `sp_f x` already does.
**Before the landing plan is written, this variant should be probed on
`pgl27_tableau_analysis_bridged.v` alone and its timing compared with the
6.8 s baseline.** If it does not recover the baseline, the fallback of spec
3.3 (the reading as a first field, with the `of r` clause checked by an
`erefl` side condition rather than by the type) is the next thing to measure.

**Not worth landing: nothing else found.** No soundness problem was found.
The attack model is untouched, the three classical axioms are the only ones
on the new theorem, and the mutation checks that were run all failed as they
should.

## 5. Files

- `_CoqProject`, `_CoqProject.baseline`, `compile.py`
- `staged/manifest/{pgg_tableau,pgg_tableau_syntax,pgg_tableau_reading}.v`
- `staged/instances/{pgl27,kim2025,psl211,s5}/...`
- `baseline/pgl27_tableau_analysis_bridged.v` (production text, production
  framework, the 6.8 s measurement)
- `k5_default_reading.v`, `k7_k11_tails.v`, `k12_k14_psl211.v`,
  `k17_vacuity.v`
- `assumptions-k14.txt`, `chains.log`
