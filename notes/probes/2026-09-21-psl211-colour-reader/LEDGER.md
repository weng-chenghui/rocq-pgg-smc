# The PSL(2,11) colour reader: does a genuinely different reader fit the record

Probe for tracker 4.1b, the follow-up the spec
`notes/20260920-readers-and-marginal-bounds-probe-design.md` asks for in its
last section, and the instance the soundness audit
`notes/probes/2026-09-20-readers-and-marginal-bounds/audit-soundness.md` names
in P20 and P21. No production file was edited. Three files in this directory,
all compiled from source, no `Admitted`, no `Abort`, no `Axiom`, no
`Hypothesis`.

Vocabulary as fixed for this probe: a Tableau value is a PROGRAM, the
manifest's record is a PATH, a program certifies a SECURITY PROPERTY with
SECURITY EVIDENCE.

## Verdict

**GO.** A reader genuinely different from the coalition's card-identity
reading fits `StaticReader` unchanged, carries a proved exact-independence
theorem at the framework's own threshold, and separates from the canonical
reader by a compiled negative: over one adapter and at one coalition of three
of the twelve positions, the exact-independence proposition holds at the
colour reader and is false at the canonical one. The generalisation the first
probe compiled therefore has a customer, and it is not the canonical reader
under a second name.

One obstacle the audit predicted, the absence of a sample adapter over
`psl211P`, is real and was construction; it took one `Definition` and one
four-line lemma. One obstacle it predicted, a seat-indexing reconciliation of
the shape of `pgl27_static_obsE`, is needed only where the framework's own
reading enters, and the tree already proves it
(`psl211_dealt_static_obsE`).

## The flow

```
open   psl211P secretP                                     -- 0 statements
                                                            (bool * cut, prior x uniform)
adapt  psl211P  as SampleAdapter over psl211_dealt_params  -- 1  (C1, psl211_colour_sample)
read   cut law of that adapter = `U psl211_G_pos           -- 2  (C1, cut_distE)
define colour reader : StaticReader psl211_dealt_params    -- 3  (C2, record unchanged)
bridge psl211_colour_view secretP C = reader at (arg, cut) -- 4  (C2, funE; via ffunE only)
factor colour reader = colour_of_reading o canonical       -- 5  (C3; via psl211_dealt_static_obsE)
derive P_indist(canonical, c) -> P_indist(colour, c)       -- 6  (C3b, framework post-processing)
certify ReaderExactPropAt(adapter, colour, secret)         -- 7  (C4, from psl211_colour_view_indep)
bound  leak coalition not below profile_k                  -- 8  (C5, 6 = profile_k)
refute independence at the leak coalition                  -- 9  (C5, from psl211_colour_view_dep_k6)
refute injectivity of colour_of_reading                    -- 10 (C6a)
refute ReaderExactPropAt(adapter, canonical, secret)       -- 11 (C6b, from psl211_dealt_raw_countE)
rewrite the record's statement comment                     -- 12 (C7, prose checked against C2)
```

Monad verdict: no monad. The repeated operation is a change of reader along a
factorisation, a single reindexing functor, and the readers over one execution
form a preorder under "the second factors through the first" rather than a
Kleisli category; the framework's post-processing law is that preorder acting
on propositions, contravariantly in nothing and covariantly in the number.

Interface each existing theorem enters through:

| existing result | file | enters through |
|---|---|---|
| `psl211_colour_view_indep` | `instances/psl211/psl211_secrecy.v:307` | `psl211_colour_reader_funE` (C2) plus `profile_k_psl211_algebra` |
| `psl211_colour_view_dep_k6` | `instances/psl211/psl211_secrecy.v:328` | `psl211_colour_reader_funE` (C2) plus `profile_k_psl211_algebra` |
| `psl211_dealt_static_obsE` | `instances/psl211/psl211_reading_constancy.v:887` | `psl211_colour_reader_factorsE` (C3) |
| `psl211_dealt_raw_countE`, `psl211_dealt_fiberE`, `psl211_perdeck_coalition_below_k` | `instances/psl211/psl211_reading_constancy.v` | `psl211_canonical_reader_not_exact` (C6b) |
| `reader_indistinguishability_postprocessing` | `notes/probes/2026-09-20-readers-and-marginal-bounds/r_framework.v:149` | `psl211_colour_indistinguishability_of_reading` (C3b) |
| `MkStaticReader`, `ReaderExactPropAt`, `ReaderIndistinguishabilityPropAt`, `coalition_reading_reader` | same probe file | used unchanged, no field added |
| `MkSampleAdapter`, `sa_cut_dist` | `security/pgg_sample_adapter.v` | `psl211_colour_sample` (C1) |
| `profile_k_psl211_algebra`, `psl211_dealt_params` | `instances/psl211/psl211_exec.v` (frozen, `.vo` required only) | C1, C4, C5 |

## Ledger

| id | verdict | where | note |
|---|---|---|---|
| C1 | **GO** | `c_adapter.v` | adapter over the EXISTING `psl211_dealt_params`; cut law computed |
| C2 | **GO** | `c_reader.v` | the colour view is a function of the run argument and the cut alone |
| C3 | **GO** | `c_reader.v` | factorisation holds in the direction card identity to colour |
| C3b | **GO** (added) | `c_reader.v` | the framework's post-processing law discharged at this factorisation |
| C4 | **GO** | `c_exact.v` | thresholds meet on the nose, five positions against `profile_k` six |
| C5 | **GO** | `c_exact.v` | sharpness stated at the reader, with the coalition's size pinned to `profile_k` |
| C6 | **GO**, two forms | `c_reader.v` | the colour map is not injective, and the two readers' propositions differ in truth value over one adapter |
| C7 | **GO** | `c_reader.v:86-95` | sentence written and checked against C2's definition |

## The statements, verbatim

### C1 `notes/probes/2026-09-21-psl211-colour-reader/c_adapter.v`

```coq
Definition psl211_colour_sample (R : realType) (secretP : R.-fdist bool)
  : SampleAdapter R (instance_exec psl211_dealt_params) :=
  @MkSampleAdapter R (instance_profile psl211_algebra)
    (instance_exec psl211_dealt_params)
    ((bool * pgg_gT psl211_M)%type : finType)
    (psl211P secretP) fst snd.

Lemma psl211_colour_sample_cut_distE (R : realType) (secretP : R.-fdist bool) :
  @sa_cut_dist R (instance_profile psl211_algebra)
    (instance_exec psl211_dealt_params) (psl211_colour_sample secretP)
  = (`U psl211_G_pos : R.-fdist (pgg_gT psl211_M)).
```

Also `psl211_colour_inputTE : ep_inputT (instance_exec psl211_dealt_params) =
bool`, `psl211_colour_sample_lawE`, `psl211_colour_sample_argE`,
`psl211_colour_sample_cutE`, each `by []`.

**Which execution, and why.** `psl211_dealt_params`, the dealer-dealt run of
`instances/psl211/psl211_exec.v`. `psl211P = secretP `x (`U psl211_G_pos)` has
the chirality bit as its first coordinate, and the colour view reads the fixed
encoder deck of that bit through the shuffle; the run argument of the
execution therefore has to be the bit, and `ex_inputT psl211_dealt_params` is
the algebra's secret carrier, `bool`. `psl211_alldecks_params` does not fit:
its run argument is a whole deck description, its law `psl211_alldecksP`
redraws the deck, and the existing `psl211_alldecks_sample` is an adapter over
a different sample space and a different execution. The weighted-word family
draws the cut from a walk and not uniformly. So the audit's P21 is confirmed:
no existing family has `psl211P` as its law, and this row is construction.

### C2 `c_reader.v`

```coq
Definition psl211_colour_reader : StaticReader psl211_dealt_params :=
  @MkStaticReader psl211_algebra psl211_dealt_params
    (fun _ => [the finType of {ffun seats -> bool}])
    (fun (C : {set seats}) (b : ex_inputT psl211_dealt_params) (g : cutT) =>
       [ffun i => if i \in C
                  then psl211_is_heart
                         (tnth (psl211_orbit_encode b) (@pgg_rho psl211_M g i))
                  else false]).

Lemma psl211_colour_readerE (R : realType) (secretP : R.-fdist bool)
    (C : {set seats}) (u : bool * pgg_gT psl211_M) :
  psl211_colour_view secretP C u
  = sr_read psl211_colour_reader C
      ((psl211_colour_sample secretP).(sa_arg) u)
      ((psl211_colour_sample secretP).(sa_cut) u).
Proof. by apply/ffunP => i; rewrite /psl211_colour_view /colour_view !ffunE. Qed.

Lemma psl211_colour_reader_funE (R : realType) (secretP : R.-fdist bool)
    (C : {set seats}) :
  psl211_colour_view secretP C
  = (fun u => sr_read psl211_colour_reader C
                ((psl211_colour_sample secretP).(sa_arg) u)
                ((psl211_colour_sample secretP).(sa_cut) u)).
```

with `seats := 'I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1` and
`cutT := pgg_gT (mp_M (instance_profile psl211_algebra))`.

The colour view IS a function of the run argument and the cut alone, so the
record's shape is not an obstacle. The seat-indexing reconciliation the audit
expected here is not needed for the bridge: `colour_view` of
`reconstruct/design_privacy.v` indexes the shuffle at `i` and the reader does
too, so the two agree by `ffunE`. It is needed one step later, in C3, where
the framework's `static_coalition_obs` indexes at
`tnth (pi_starts (mp_PI (instance_profile psl211_algebra))) i`; the tree
already proves that step at these parameters, `psl211_dealt_static_obsE` of
`instances/psl211/psl211_reading_constancy.v`, so no counterpart of
`pgl27_static_obsE` had to be written.

### C3 and C3b `c_reader.v`

```coq
Definition psl211_colour_of_reading (C : {set seats})
    (v : {ffun seats -> cards}) : {ffun seats -> bool} :=
  [ffun i => if i \in C then psl211_is_heart (v i) else false].

Lemma psl211_colour_reader_factorsE (C : {set seats})
    (b : ex_inputT psl211_dealt_params) (g : cutT) :
  sr_read psl211_colour_reader C b g
  = psl211_colour_of_reading C
      (sr_read (coalition_reading_reader psl211_dealt_params) C b g).

Lemma psl211_colour_indistinguishability_of_reading (R : realType)
    (secretP : R.-fdist bool) (c : R) :
  ReaderIndistinguishabilityPropAt (psl211_colour_sample secretP)
    (coalition_reading_reader psl211_dealt_params) c ->
  ReaderIndistinguishabilityPropAt (psl211_colour_sample secretP)
    psl211_colour_reader c.
```

The map takes the coalition as an argument because the canonical reader
returns card zero outside the coalition and card zero is a heart. C3b is the
first discharge of the framework's post-processing law at a factorisation that
is not the identity; at the eight-card instance the first probe discharged it
at `f = id`. It transports a bound and produces none: over this adapter the
canonical reader has no such proposition at any small number, by C6b and by
`psl211_dealt_constancy_false`.

### C4 `c_exact.v`

```coq
Lemma psl211_colour_reader_exact (R : realType) (secretP : R.-fdist bool) :
  ReaderExactPropAt (psl211_colour_sample secretP) psl211_colour_reader
    (psl211_secret secretP).
Proof.
move=> C HC.
have HC5 : (#|C| <= 5)%N by rewrite -ltnS -profile_k_psl211_algebra; exact: HC.
by rewrite -psl211_colour_reader_funE; exact: psl211_colour_view_indep HC5.
Qed.
```

Three lines and no new mathematics, which is what a restatement should cost.
The threshold conversion is `-ltnS` against `profile_k_psl211_algebra`: the
framework's `#|C| < profile_k (instance_profile psl211_algebra)` and the
instance's `#|C| <= 5` are the same premise because the derived profile
declares six.

### C5 `c_exact.v`

```coq
Lemma psl211_leak_coalition_not_below_k :
  ~~ (#|psl211_leak_coalition| < profile_k (instance_profile psl211_algebra))%N.

Lemma psl211_colour_reader_dep_at_threshold (R : realType)
    (secretP : R.-fdist bool) :
  secretP true != 0 -> secretP false != 0 ->
  (#|psl211_leak_coalition| = profile_k (instance_profile psl211_algebra))%N /\
  ~ sa_sampleP (psl211_colour_sample secretP)
      |= (fun u => sr_read psl211_colour_reader psl211_leak_coalition
                     ((psl211_colour_sample secretP).(sa_arg) u)
                     ((psl211_colour_sample secretP).(sa_cut) u))
         _|_ psl211_secret secretP.
```

The first lemma is what keeps the two statements from contradicting each
other: the refuting coalition has exactly `profile_k` positions and is
therefore outside the range C4 covers. The two positivity premises are the
cited theorem's own and are part of the mathematics, a prior supported on one
chirality making every reader independent of the secret.

### C6 `c_reader.v`

```coq
Lemma psl211_colour_of_reading_collides (C : {set seats}) (i0 : seats) :
  i0 \in C ->
  exists v w : {ffun seats -> cards},
    v != w /\ psl211_colour_of_reading C v = psl211_colour_of_reading C w.

Definition psl211_perdeck_static_view (R : realType) (secretP : R.-fdist bool)
  : {RV (psl211P secretP) -> {ffun seats -> cards}} :=
  fun u => @static_coalition_obs psl211_algebra psl211_dealt_params
             psl211_perdeck_coalition u.1 u.2.

Lemma psl211_canonical_reader_funE (R : realType) (secretP : R.-fdist bool) :
  (fun u => sr_read (coalition_reading_reader psl211_dealt_params)
              psl211_perdeck_coalition
              ((psl211_colour_sample secretP).(sa_arg) u)
              ((psl211_colour_sample secretP).(sa_cut) u))
  = psl211_perdeck_static_view secretP.
Proof. by []. Qed.

Lemma psl211_canonical_reader_not_exact (R : realType)
    (secretP : R.-fdist bool) :
  secretP true != 0 -> secretP false != 0 ->
  ~ ReaderExactPropAt (psl211_colour_sample secretP)
      (coalition_reading_reader psl211_dealt_params) (psl211_secret secretP).
```

The first form is the weak one asked for, non-injectivity of the factorising
map: two readings giving one position of the coalition two different hearts
have one colour reading, so the identity of C3 is a factorisation in one
direction only.

The second form is the one that decides the row. Three of the twelve
positions are below the threshold of six, so C4 grants the colour reader
independence there, and the same proposition at the canonical reader over the
same adapter is FALSE. What separates them is the card identity: the encoder
decks of the two chiralities reach one reading of those three seats under
exactly one cut and under none, `psl211_dealt_raw_countE`, while their colour
patterns on five positions or fewer are equidistributed,
`psl211_colour_fiber_cardE`. So the colour reader's theorem is not the image
of any canonical-reader proposition over this adapter, and the two published
statements are two statements and not one number under two names, which is
what the eight-card trace turned out to be (audit P4, P5).

The proof reuses the instance's own counterexample machinery, in the shape
`psl211_colour_view_dep_k6` uses: a value the fiber of one secret misses
entirely, positive mass for the other secret and for the missed secret, and
the product form of independence at that pair.

### C7 the record's statement comment

Written at `c_reader.v:86-95`, above the instance it is checked against:

> A static reader of an execution is a family of functions of the coalition,
> the run argument and the cut, valued in a finite type that may depend on
> the coalition. That is the whole of what the type constrains. It does not
> say that a reader is a group action, nor that it ignores the interpreter's
> messages; a reader whose body reads the run is typed by the same record.
> That a given reader is a function of the dealt deck and the cut alone is a
> theorem about that reader, here the definition itself and, against the
> framework's own reading, `psl211_colour_reader_factorsE`.

This replaces the sentence audit P15 found false, which claimed the record
omits the interpreter state.

## Compile times and axiom footprint

Final ordered pass, one Rocq process at a time through the shared lock,
`rocq compile` on this machine, 2026-09-21:

| file | wall |
|---|---|
| `c_adapter.v` | 4.16 s |
| `c_reader.v` | 17.32 s |
| `c_exact.v` | 4.61 s |

`notes/probes/2026-09-20-readers-and-marginal-bounds/r_framework.v` was
recompiled first, 7.9 s: its `.vo` of 00:06 predated `manifest/pgg_tableau.vo`
of 00:31 and the first attempt at `c_reader.v` failed with "Compiled library
readersprobe.r_framework makes inconsistent assumptions over library
pgg_smc.pgg_tableau". That was staleness and not a concurrent rebuild; after
the recompilation the whole pass is green and was run again end to end.

`Print Assumptions`, compiled in the files:

| declaration | assumptions |
|---|---|
| `psl211_colour_sample_cut_distE` | the three classical ones (`propositional_extensionality`, `functional_extensionality_dep`, `constructive_indefinite_description`) |
| `psl211_colour_reader_funE` | the three classical ones |
| `psl211_colour_reader_factorsE` | **Closed under the global context** |
| `psl211_canonical_reader_not_exact` | the three classical ones |
| `psl211_colour_reader_exact` | the three classical ones |
| `psl211_colour_reader_dep_at_threshold` | the three classical ones |

No assumption beyond what the cited theorems already carry, and no
instance-specific axiom: in particular nothing here rests on
`rigidity_s5_instance.s5_group_order_eq` or on any table axiom. The three
classical ones enter through `boolp` with the first `fdist`.

## Departures from the task's ledger

1. **C2's reconciliation lemma.** The task asked for it "as its own lemma, as
   `pgl27_static_obsE` does". None was written, because the bridge needs none
   and the step it would prove is already in the tree at these parameters
   (`psl211_dealt_static_obsE`). Recorded rather than duplicated.
2. **C6 delivered in two forms.** The task offered non-injectivity of `f` as
   an alternative to exhibiting readings; the stronger separation, two
   propositions differing in truth value over one adapter at one coalition,
   was available from the tree's own counterexample and is compiled as well.
3. **One row added, C3b.** The framework's post-processing law discharged at
   this factorisation. It is the row that shows the first probe's `R3` does
   something at a coarsening rather than at the identity map.
4. **No `Fail` was compiled.** Every negative in this probe is a proved
   negative, so the trap that a passing `Fail` prints nothing does not arise.

## What is left

1. **No post-processing law for the exact form.** `r_framework.v` proves
   post-processing for `ReaderIndistinguishabilityPropAt` only. Its companion
   for `ReaderExactPropAt`, independence preserved along a factorisation, is
   the natural next lemma and is not compiled here. At this instance it would
   be the wrong direction anyway: independence at the colour reader does not
   come from the canonical one, it is the canonical one that fails.
2. **The all-decks comparison is argued and not compiled.** The tree's
   card-identity independence `psl211_alldecks_static_indep` is stated at
   `psl211_alldecksP`, a different sample space, so no `ReaderExactPropAt`
   over `psl211_colour_sample` follows from it. That is a difference of types
   and not a theorem, and audit P24 already records it; nothing was compiled
   to restate it.
3. **No program, no path, no manifest row.** `psl211P` now has an adapter and
   the colour reader now has its two propositions, and nothing in
   `manifest/` or in `instances/psl211/tableau/` was touched. Whether a
   program is published over this model is a separate decision, and it would
   need the executed link lemma for this adapter, which the dealt mode does
   not carry.
4. **Landing homes, if the framework lands.** `StaticReader`, the two reader
   propositions and the post-processing law would go to a new leaf file above
   `manifest/pgg_tableau.v`, with the record's comment as rewritten in C7;
   `psl211_colour_sample` and the colour reader to `instances/psl211/`, in a
   file that sees both `psl211_secrecy.v` and `psl211_reading_constancy.v`;
   `psl211_canonical_reader_not_exact` beside `psl211_dealt_constancy_false`,
   whose machinery it reuses.
