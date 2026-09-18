# General dealer law probe: independent soundness audit

Date: 2026-09-18

Independent audit; files as of the rename pass. The auditor wrote none of the
probe files and judged them without reference to the earlier
`flow-sketch-audit.md` and `naming-audit.md`, which were written against older
file versions and older identifier names. `history/` was read only to check
STATUS.md's claim that the rename pass changed no statement and no proof.

Every compile below was run by the auditor from this directory with the
single-file command in STATUS.md, one Rocq process at a time, with `-o`
directing every output into a session scratch directory. No `.vo` in this
directory and no production file was rebuilt or touched. No checksum or
inconsistent-assumptions error appeared. `make` was not run anywhere.

## Findings

| id | severity | file:line | claim | evidence |
|---|---|---|---|---|
| F1 | SHOULD-FIX | `pgl27_deterministic_bridge.v:326-332` | The all-decks validity mutation does not test that validity is needed. It drops `uniq d` from the ascribed statement and then feeds `HC : (#\|C\| <= 3)%N` into the `uniq d` argument slot. The failure is an argument-position mismatch between two adjacent `is_true` premises and would not have arisen had the two premises been declared in the other order. It shows neither that the unvalidated statement is unprovable nor that it is false. | Recaptured error, S5. |
| F2 | SHOULD-FIX | design note `C6` row, line 181, vs `pgl27_deterministic_bridge.v:280-319` | C6's stated passing evidence is reuse of `alldecks_view_law`. That lemma is reachable by its qualified name, so the reuse was available. The probe instead routes PGL all-decks through C3 and proves a new per-deck law from `ktuple_encode_uniform`, 35 lines that are 88% textually identical to the probe's own `pgl27_dealer_view_law` proof at lines 130-165 and that reproduce the counting content C6 asked not to reproduce. Sound, but it is new mathematical content the ledger did not anticipate and it changes the implementation cost. | `Fail Check alldecks_view_law` succeeds, `Check transitivity_privacy.alldecks_view_law` succeeds; similarity measurement, S7. |
| F3 | SHOULD-FIX | `psl211_per_deck_law_counter.v:100-116` | `psl211_perdeck_no_common_law` carries the hypothesis `forall b, valid b psl211_perdeck_deal` as a hand-written assumption. Nothing compiled connects it to C3's first premise under the PSL dealer law, and nothing compiled states that C3's two premises are jointly unsatisfiable. The step from "no common law at this deal" to "C3 is not available to PSL", which is the sentence the paper will lean on, is carried in STATUS.md prose (lines 213-214), not in the kernel. It is two lines away; the auditor compiled it. | `audit_c3_link.v`, S4(d). |
| F4 | NOTE | `dealer_kernel_probe.v:69`, `:91`; `pgl27_deterministic_bridge.v:187`, `:366`; `psl211_alldecks_bridge.v:283` | The `secretP s != 0` guard in C2 and C3 is never exercised. All three instances use `fdist_uniform card_bool`, which is nowhere zero, and every use discards the guard (`=> s _`, `=> b _`, `move=> s d _ Hu`). The guard is correct but untested. | Reading, S3. |
| F5 | NOTE | `pgl27_deterministic_bridge.v:267-273`, `:372-373` | PGL all-decks has a named view-reader equation but no named secret-reader equation. The identity `dealer_shuffle_secret ... = alldecks_secret ...` is discharged by conversion inside `exact: Hgen`. Both are `fun u => u.1`, so this is sound, but soundness invariant 7 asks for both reader equations and only one is stated. | Reading plus `transitivity_privacy.v:777`, S2(e). |
| F6 | NOTE | `pgl27_deterministic_bridge.v:225`, `:326`; `psl211_alldecks_bridge.v:220` | Three mutations have no declared positive control and rest on the good-version lemma earlier in the file (`pgl27_dealer_viewE` L93, `pgl27_alldecks_dealer_view_law` L280, `psl211_dealer_secretE` L204). STATUS.md line 243 says the two declared controls make "each mutation known to fail for the missing premise", which overstates what is declared. | S5. |
| F7 | NOTE | design note lines 235-244 | The artifact list names `pgl27_alldecks_bridge.v` and `headline_decomposition.v`. Neither exists. C6 lives in `pgl27_deterministic_bridge.v` Section `PGLAllDecks`; no decomposition file was needed because nothing was admitted. | `ls`, S7. |
| F8 | NOTE | `pgl27_deterministic_bridge.v:52-53` | The statement comment on `pgl27_dealer_embed` asserts "It is injective and its image is the support of the dealer law". Neither is proved. Both are true and neither is load-bearing, because `pgl27_dealerPE` is what the proofs use. | Reading, S7. |
| F9 | NOTE | `psl211_alldecks_bridge.v:40`, `:78`; `psl211_per_deck_law_counter.v:32` | The probe's generic surface is larger than the design note proposed. Beyond the seven declarations of "Proposed generic declarations", it introduces `fdistmap_prod_sectionE`, `uniform_fdistmap_fiberTE` and `uniform_fdistmap_pointE`, none of which exists in the production tree. STATUS.md discloses only the third. The implementation plan must size the permanent module for ten declarations, not seven. | Repository grep, S7. |
| F10 | NOTE | STATUS.md line 32 | "`make -f Makefile.rocq -n` lists only probe `.v` files and no target outside this directory" was not re-run, because running `make` is forbidden here. The equivalent was checked statically and holds. | `_CoqProject`, `.Makefile.rocq.d`, S6. |

No BLOCKING finding.

## S1 Invariant 1: no assumed constant, and the assumption reports

No `Axiom`, `Admitted`, `Abort`, `Parameter`, `Conjecture`, `admit` or
`give_up` occurs in any probe `.v` file. Scanned with Python word boundaries,
because this machine's `grep -E` silently matches nothing for
`[[:<:]]`/`[[:>:]]`.

Two `Hypothesis` declarations exist, both inside mutation sections, and both
are discharged as premises of the closed statement:

- `dealer_kernel_probe.v:113` `Hmix`, in `Section Mutations`. It becomes a
  premise of the positive control `dealer_shuffle_view_indep_with_common_law`.
  The three headline lemmas live in `Section DealerKernel`, which declares no
  `Hypothesis` at all, so none of them depends on it.
- `psl211_alldecks_bridge.v:100` `Hs`, in `Section ProductSectionMutation`. It
  becomes a premise of `fdistmap_prod_sectionE_with_sections`. The two lemmas
  of `Section UniformPushforwardLaws` are closed before it is declared.

Every other `Variable`/`Variables` declares genuinely universally quantified
data: carriers, distributions, maps and readers. No section variable stands in
for a proof obligation.

Every `Print Assumptions` sits after the enclosing `End`, so each reports the
discharged constant:

- `dealer_kernel_probe.v`: `End DealerKernel` L103, `End Mutations` L144,
  reports L146-148.
- `carrier_transport_probe.v`: `End CarrierTransport` L40, `End Mutation` L56,
  report L58.
- `pgl27_deterministic_bridge.v`: `End PGLDeterministic` L230, reports
  L232-234; `End PGLAllDecks` L376, reports L378-380.
- `psl211_alldecks_bridge.v`: `End UniformPushforwardLaws` L93,
  `End ProductSectionMutation` L119, `End PSLBridge` L308, reports L315-321.
- `psl211_per_deck_counter.v`, `psl211_per_deck_law_counter.v`,
  `concrete_instances.v`: no sections; reports at the end of file.

Recompiled, wall time and peak resident set as measured by `/usr/bin/time -l`:

| file | exit | wall | peak RSS | STATUS.md says |
|---|---|---|---|---|
| `dealer_kernel_probe.v` | 0 | 4.11 s | 1.643 GB | 4 s, 1.64 GB |
| `carrier_transport_probe.v` | 0 | 4.02 s | 1.620 GB | 4 s, 1.62 GB |
| `pgl27_deterministic_bridge.v` | 0 | 5.03 s | 1.692 GB | 5 s, 1.69 GB |
| `psl211_alldecks_bridge.v` | 0 | 5.79 s | 1.742 GB | 6 s, 1.74 GB |
| `psl211_per_deck_counter.v` | 0 | 29.10 s | 1.849 GB | 29 s, 1.85 GB |
| `psl211_per_deck_law_counter.v` | 0 | 4.76 s | 1.702 GB | 5 s, 1.70 GB |
| `concrete_instances.v` | 0 | 5.64 s | 1.776 GB | 6 s, 1.78 GB |

Assumption reports. Counted `Axioms:` blocks against the number of
`Print Assumptions` commands per file: 3/3, 1/1, 6/6, 7/7, 0/8, 4/4, 4/4.
`psl211_per_deck_counter.v` printed `Closed under the global context` eight
times and nothing else.

Abstract-R files, every block verbatim and identical:

```text
Axioms:
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

`concrete_instances.v`, every one of the four blocks verbatim:

```text
Axioms:
ClassicalDedekindReals.sig_not_dec : forall P : Prop, {~ ~ P} + {~ P}
ClassicalDedekindReals.sig_forall_dec :
  forall P : nat -> Prop,
  (forall n : nat, {P n} + {~ P n}) ->
  {n : nat | ~ P n} + {forall n : nat, P n}
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
Epsilon.epsilon_statement :
  forall (A : Type) (P : A -> Prop),
  inhabited A -> {x : A | (exists x0 : A, P x0) -> P x}
constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

This is exactly the expected list and nothing else. No project-local constant
appears anywhere. Invariant 1 holds.

## S2 Statement fidelity

### (a) The joint law and its factorization

`dealer_kernel_probe.v:32-33`

```coq
Definition dealer_shuffleP : R.-fdist (secretT * (deckT * shuffleT)) :=
  secretP `X (fun s => (delta s) `x nu).
```

This is the design note's proposed form character for character, with `cutT`
renamed `shuffleT`. Soundness invariant 3 asks for average-case over `secretP`,
then conditional over `delta s`, then over the independent `nu`, and that is
what the kernel product `` `X `` followed by the independent product `` `x ``
expresses: the deck may depend on the drawn secret, the shuffle may not.

`dealer_kernel_probe.v:55-58` states the pointwise factorization

```coq
Lemma dealer_shufflePE s d g :
  dealer_shuffleP (s, (d, g)) = secretP s * (delta s d * nu g).
```

again identical to the design note. C1 is met.

### (b) The two privacy premises, and the over-strong reading

`dealer_view_indep` (`dealer_kernel_probe.v:66-71`) has premise

```coq
  (forall s, secretP s != 0 ->
     fdistmap (fun dg => view s dg.1 dg.2) ((delta s) `x nu) = mu) ->
```

with `mu : R.-fdist viewT` a lemma parameter. That is "every positive-mass
secret has the same mixed view law", and nothing weaker. Invariant 4 holds.

`dealer_view_indep_of_deck` (`:86-93`) has

```coq
  (forall s d, delta s d != 0 -> valid s d) ->
  (forall s d, secretP s != 0 -> valid s d -> fdistmap (view s d) nu = mu) ->
```

which is invariant 5's "every positive-mass deck is valid" and "every valid
deck has the same view law under `nu`". The extra `secretP s != 0` in the
second premise only weakens the premise, hence strengthens the lemma.

The over-strong reading would be the conclusion with no premise at all:

```coq
  forall delta view,
    dealer_shuffleP |= dealer_shuffle_view view _|_ dealer_shuffle_secret
```

The file does not prove it, and it contains a mutation that is exactly the
attempt to assert it from the file's own lemma. `dealer_kernel_probe.v:137-142`
ascribes the bare independence statement to `dealer_view_indep` applied without
the premise, and it fails:

```text
The term "dealer_view_indep (mu:=fdist1 x)" has type
 "(forall s : secretT,
   secretP s != 0 ->
   fdistmap (fun dg => view s dg.1 dg.2) (delta s) `x nu = fdist1 x) ->
  dealer_shuffleP secretP delta nu |= dealer_shuffle_view secretP delta nu
                                        view _|_ dealer_shuffle_secret
                                                 secretP delta nu"
while it is expected to have type
 "dealer_shuffleP secretP delta nu |= dealer_shuffle_view secretP delta nu
                                        view _|_ dealer_shuffle_secret
                                                 secretP delta nu"
```

The positive control `dealer_shuffle_view_indep_with_common_law` is reported
`is defined` immediately before this failure in the same run, so the spelling
is otherwise well formed and the failure is the dropped premise.

### (c) Each bridge headline against the production theorem

The auditor compiled the type-identity check directly, with

```coq
Definition audit_same_type (A : Type) (x y : A) : Type := A.
```

which forces the second term's type to be convertible with the first's. All six
directions elaborated:

```text
audit_same_type pgl27_view_indep_via_dealer pgl27_view_indep
     : Type
audit_same_type pgl27_view_indep pgl27_view_indep_via_dealer
     : Type
audit_same_type pgl27_view_indep_alldecks_via_dealer
  pgl27_view_indep_alldecks
     : Type
audit_same_type pgl27_view_indep_alldecks
  pgl27_view_indep_alldecks_via_dealer
     : Type
audit_same_type psl211_alldecks_view_indep_via_dealer
  psl211_alldecks_view_indep
     : Type
audit_same_type psl211_alldecks_view_indep
  psl211_alldecks_view_indep_via_dealer
     : Type
```

Additionally each pair was ascribed one hand-written type and both members
accepted it, which rules out a coincidence of the conversion check:

```coq
Definition audit_det_bridge_at_prod_type :
  forall (R : realType) (C : {set 'I_8}), (#|C| <= 3)%N ->
    pgl27P R |= pgl27_view R C _|_ pgl27_secret R
  := @pgl27_view_indep_via_dealer.
Definition audit_det_prod_at_prod_type : (* same type *) := @pgl27_view_indep.
```

and likewise for the PSL pair. The production theorems are
`instances/pgl27/pgl27_secrecy.v:82` and `:215`, and
`instances/psl211/psl211_models.v:427`.

### (d) Each bridge passes through the real generic declaration

Read from the `.glob` reference records, which name the defining module, so a
local copy could not masquerade as the real declaration. Cross-module
references only:

`pgl27_deterministic_bridge.glob`

```text
 2x  general_dealer_law_probe.dealer_kernel_probe.dealer_shuffleP
 3x  general_dealer_law_probe.dealer_kernel_probe.dealer_shufflePE
 2x  general_dealer_law_probe.dealer_kernel_probe.dealer_shuffle_secret
 4x  general_dealer_law_probe.dealer_kernel_probe.dealer_shuffle_view
 2x  general_dealer_law_probe.dealer_kernel_probe.dealer_view_indep
 1x  general_dealer_law_probe.dealer_kernel_probe.dealer_view_indep_of_deck
 2x  general_dealer_law_probe.carrier_transport_probe.inde_RV_fdistmap
 2x  pgg_reconstruct.transitivity_privacy.fdistmap_prod_const
 6x  pgg_reconstruct.transitivity_privacy.ktuple_encode_uniform
 2x  pgg_reconstruct.transitivity_privacy.alldecksP
 1x  pgg_reconstruct.transitivity_privacy.alldecks_secret
 2x  pgg_reconstruct.transitivity_privacy.alldecks_view
```

`psl211_alldecks_bridge.glob`

```text
 1x  general_dealer_law_probe.dealer_kernel_probe.dealer_shuffleP
 3x  general_dealer_law_probe.dealer_kernel_probe.dealer_shufflePE
 3x  general_dealer_law_probe.dealer_kernel_probe.dealer_shuffle_secret
 2x  general_dealer_law_probe.dealer_kernel_probe.dealer_shuffle_view
 2x  general_dealer_law_probe.dealer_kernel_probe.dealer_view_indep
 2x  general_dealer_law_probe.carrier_transport_probe.inde_RV_fdistmap
 2x  pgg_reconstruct.design_privacy.uniform_fdistmap_fiberE
```

`dealer_view_indep_of_deck` appears zero times in the PSL bridge. So C3 is
instantiated by the PGL all-decks arm alone, which is what STATUS.md's table
says. No copies of the dealer-model declarations remain in any bridge; every
reference crosses a module boundary into `dealer_kernel_probe` or
`carrier_transport_probe`.

### (e) The carrier-transport equations

Invariant 7 asks for a distribution equality and commuting equations for the
secret and the view reader.

- PGL deterministic: `pgl27_dealerPE` (L62, a genuine pushforward equality
  along `pgl27_dealer_embed`), `pgl27_dealer_viewE` (L93),
  `pgl27_dealer_secretE` (L102). All three present. Met.
- PSL all-decks: `psl211_dealerPE` (L168, pushforward along the reassociation),
  `psl211_dealer_viewE` (L195), `psl211_dealer_secretE` (L204). Met.
- PGL all-decks: `pgl27_alldecks_dealerPE` (L259) is definitional, `Proof. by
  []`, and correctly so: `transitivity_privacy.v:771` defines
  ``alldecksP := secretP `X (fun s => (`U (card_class_decks_gt0 s)) `x (`U
  card_G_gt0))``, which is `dealer_shuffleP` at
  `pgl27_alldecks_dealer_delta` and `` `U pgl27_G_pos `` written in another
  vocabulary. There is no carrier to transport, so invariant 7's demand is
  vacuous on this arm and is met in the only sense available: the view reader
  equation `pgl27_alldecks_dealer_viewE` is stated and proved, and the secret
  reader identity holds by conversion because `alldecks_secret` and
  `dealer_shuffle_secret` are both `fun u => u.1`. Finding F5 records that the
  secret equation is used but not stated.

## S3 Vacuity, invariant 8

Which claim each bridge instantiates, from the `.glob` records above:

| declaration | claim | instantiated by |
|---|---|---|
| `dealer_shuffleP`, `dealer_shufflePE`, `dealer_shuffle_secret`, `dealer_shuffle_view` | C1 | all three bridge arms |
| `dealer_view_indep` | C2 | PGL deterministic, PSL all-decks |
| `dealer_view_indep_of_deck` | C3 | PGL all-decks only |
| `inde_RV_fdistmap` | C4 | PGL deterministic, PSL all-decks |

Each of C1 to C4 is reached through the real declaration by at least one arm,
so invariant 8 holds as stated.

Joint satisfiability is witnessed, not argued: `concrete_instances.v` compiles
all three headlines at `Rdefinitions.R`, so the generic hypotheses have a
solution over a concrete field, and `Print Assumptions` adds only the expected
real-number axioms.

Is any hypothesis exercised trivially?

- The `secretP s != 0` guard is not exercised. Every instance's secret prior is
  `fdist_uniform card_bool`, which is nowhere zero, and all three uses discard
  the guard. Finding F4.
- Secret-dependence of `delta` is exercised, on the PGL side and only there.
  `pgl27_dealer_delta s = fdist1 (orbit_encode s)` and
  `pgl27_alldecks_dealer_delta s = `U (pgl27_class_decks_pos s)` both depend on
  the secret; `psl211_dealer_delta (_ : bool)` ignores it by construction
  (`psl211_alldecks_bridge.v:142`). So the general model's secret-dependent
  kernel is not idle: it is what the PGL arms use and what the PSL arm
  deliberately does not.
- Both premises of C3 are exercised non-trivially by the PGL all-decks arm:
  `Hvalid` extracts `deck_ok` from class membership through
  `fdist_uniform_supp_notin` (L354-361), and `Hlaw` is the per-deck counting
  lemma (L362-366). Neither is a tautology.

Is any headline true for a degenerate reason? No. The carriers are all
inhabited and their positivity is proved (`pgl27_G_pos`, `psl211_G_pos`,
`pgl27_class_decks_pos`, `psl211_deal_pos`, `psl211_alldecks_gt0`). The
coalition bounds `#|C| <= 3` and `#|C| <= 5` are the instances' own published
privacy thresholds, not artefacts, and admit non-empty `C`. `pgl27_dealer_mu`
is a genuine law because its `Hdt` positivity obligation is discharged from an
exhibited tuple, not assumed.

Concrete-R wrappers. Each was checked against the production theorem at
`Rdefinitions.R` by the same conversion test, and all passed:

```text
audit_same_type pgl27_view_indep_at_R
  (pgl27_view_indep Rdefinitions.RbaseSymbolsImpl.R)
     : Type
audit_same_type (pgl27_view_indep Rdefinitions.RbaseSymbolsImpl.R)
  pgl27_view_indep_at_R
     : Type
audit_same_type pgl27_view_indep_alldecks_at_R
  (pgl27_view_indep_alldecks Rdefinitions.RbaseSymbolsImpl.R)
     : Type
audit_same_type psl211_alldecks_view_indep_at_R
  (psl211_alldecks_view_indep Rdefinitions.RbaseSymbolsImpl.R)
     : Type
```

Nothing is weakened: the coalition bound, the law, the view and the secret are
the production ones. The fourth wrapper `psl211_dealerPE_at_R` is the probe's
own factorization at `Rdefinitions.R` and claims nothing about production.

## S4 C8 and its consequence

### (a) The objects are the real ones, and the coalition is three seats

`psl211_perdeck_fiber_card_neq` (`psl211_per_deck_counter.v:240-253`) is stated
over `psl211_perdeck_fiber`, whose definition (L208-211) is a subset of
`pgg_G psl211_M`, the actual group, cut out by
`psl211_alldecks_view psl211_perdeck_coalition (b, psl211_perdeck_deal) g ==
psl211_perdeck_view`, the real instance reading at a real element of
`psl211_deal` (`(ord0, 1%g, 1%g)`, L32). No surrogate appears.

The coalition size was compiled by the auditor:

```coq
Lemma audit_coalition_card : #|psl211_perdeck_coalition| = 3.
```

`Print Assumptions` reports `Closed under the global context`. Also compiled:
seats 0, 1 and 2 are members and seat 3 is not. Three is well under the
privacy threshold of five, which is what makes this a counterexample to the
per-deck route rather than an above-threshold leak.

### (b) What the reading says, inside and outside the coalition

`psl211_perdeck_coalition := [set i : seatT | val i \in [:: 0; 1; 2]]` denotes
seats 0, 1, 2, as the comment says.

`psl211_perdeck_view := [ffun i => psl211_code12 (nth 0 [:: 0; 1; 5] (val i))]`
denotes cards 0, 1, 5 at those seats. Compiled by the auditor:

```coq
Lemma audit_perdeck_view_in :
  [&& val (psl211_perdeck_view (@Ordinal 12 0 isT)) == 0,
      val (psl211_perdeck_view (@Ordinal 12 1 isT)) == 1 &
      val (psl211_perdeck_view (@Ordinal 12 2 isT)) == 5].
```

Outside the coalition the reading is card 0, because `nth` falls through to its
default:

```coq
Lemma audit_perdeck_view_off (i : 'I_12) :
  (3 <= val i)%N -> psl211_perdeck_view i = ord0.
```

and the instance reading returns `ord0` outside `C`
(`psl211_alldecks.v:678-682`):

```coq
Lemma audit_alldecks_view_off (C : {set 'I_12}) (x : psl211_inputT)
    (g : pgg_gT psl211_M) (i : 'I_12) :
  i \notin C -> psl211_alldecks_view C x g i = ord0.
```

Both compiled. So the off-coalition value does matter and the chosen reading
agrees with it. Had it not agreed, both fibers would be empty and
`psl211_perdeck_raw_count false = 1` would be impossible. The compiled count of
1 is therefore itself evidence of the agreement, and the agreement is
independently established inside `psl211_perdeck_testE`'s `nth_default` branch
(`psl211_per_deck_counter.v:117`). The auditor confirms this reasoning rather
than refuting it.

`psl211_code12` rather than `inord` is the right choice and not merely a
convenience: `psl211_code12 k = Ordinal (ltn_pmod k (ltn0Sn 11))`
(`psl211_alldecks.v:114`) reduces, while `inord` does not, because `insub`
branches on the opaque `idP`.

### (c) The chain from the raw count to the real objects

No gap was found. Specifically:

- `%% 12` hides nothing. It is exactly the `val` of `psl211_code12`, and
  `psl211_perdeck_testE` (L102-118) proves the boolean test equivalent to the
  `ffun` equality instead of assuming it. The raw codes are in range anyway:
  heart codes are `val (ph _) < 6` and club codes `6 + val (pc _) < 12`
  (`psl211_alldecks.v:135-140`).
- The `nth` defaults cannot make the raw and real objects disagree silently.
  `psl211_alldecks_seq` is a `map` over `iota 0 12`, so it has length 12, and
  the index into it is `nth 0 (psl211_ptbl g) (val i) = val (g i) < 12` by
  `psl211_perdeck_ptbl_nth` (L153-158). More decisively,
  `psl211_perdeck_raw_viewE` (L161-175) is proved as an equation between the
  raw reading and the real reading, so any default silently taken would have
  made that equation false, not silently accepted. The same argument covers
  `nth [::]` inside `psl211_alldecks_row`: the row and corow size lemmas
  (L54-61) compute to 6 for both chiralities, which the empty default could not
  do.
- The `perm_eq` is used in a direction-insensitive way.
  `psl211_perdeck_ptbl_enum` (L180-199) gives
  `perm_eq [seq psl211_ptbl g | g <- enum (pgg_G psl211_M)] (unzip1
  psl211_elem_table)`, and `psl211_perdeck_fiberE` (L230-231) consumes it as
  `perm_size (perm_filter _ ...)`, which only needs equal sizes.
- No lemma statement is weaker than its comment claims. Each of
  `psl211_perdeck_seqE`, `psl211_perdeck_testE`, `psl211_perdeck_raw_viewE`,
  `psl211_perdeck_ptbl_enum` and `psl211_perdeck_fiberE` states exactly the
  correspondence its comment describes, and all eight lemmas of the file report
  `Closed under the global context`, so the counting rests on no axiom at all.

### (d) The law counter, and what it needs to mean what it says

`psl211_perdeck_law_neq` (`psl211_per_deck_law_counter.v:60-92`) turns the
fiber counts into two different laws over an arbitrary `realType`, through
`uniform_fdistmap_pointE`. STATUS.md's account of that lemma's provenance is
accurate: `reconstruct/design_privacy.v:56-64` performs the same computation
as a `have key` inside the proof of `uniform_fdistmap_fiberE` and does not
export it, and `pr_countE` (`design_privacy.v:170`) is about `Pr` of an event
under a product law, not a pushforward point.

`psl211_perdeck_no_common_law` (L100-116) is the negation of
`dealer_view_indep_of_deck`'s second premise at the PSL data. The auditor
machine-checked that identification rather than reading it off. In
`audit_c3_link.v` the two hypotheses

```coq
Hypothesis H1 : forall (s : bool) (d : psl211_deal),
  @psl211_dealer_delta R s d != 0 -> valid s d.
Hypothesis H2 : forall (s : bool) (d : psl211_deal),
  (fdist_uniform card_bool : R.-fdist bool) s != 0 -> valid s d ->
  fdistmap (psl211_dealer_view psl211_perdeck_coalition s d)
    (@psl211_dealer_nu R) = mu.
```

are accepted in the two premise slots of `@dealer_view_indep_of_deck` at the
PSL instantiation, so they are C3's premises and not a paraphrase.

The hypothesis `forall b, valid b psl211_perdeck_deal` is the right one and it
is forced. Under the PSL dealer law `delta` is uniform on the whole deal type,
so `psl211_dealer_delta R b d != 0` for every `d`, and C3's first premise then
gives validity at every deal, in particular at `psl211_perdeck_deal`. The
auditor compiled this together with the second premise:

```coq
Lemma audit_c3_premises_false : False.
```

reported with the three `boolp` axioms and nothing else. So the cleaner
statement, that C3's two premises are jointly unsatisfiable for the PSL dealer
law, is derivable, is two lines from what the probe proves, and is not in the
probe. Finding F3.

### (e) What C8 refutes, precisely

Shown, all machine-checked:

1. At the single deal `psl211_perdeck_deal`, coalition {0,1,2}, reading
   (0,1,5), the number of cuts producing that reading is 0 under one chirality
   and 1 under the other.
2. Hence the two conditional view laws given that deal differ, at every
   `realType`.
3. Hence no single `mu` is the conditional law under both chiralities at that
   deal.
4. Hence, with the auditor's one-step addition, C3's two premises have no
   joint solution for the PSL dealer law. The per-deck route is closed.

Not shown: that per-deck privacy fails as a security property. Fibers of size 0
and 1 say that a party who knows the deal description and sees reading (0,1,5)
at seats 0, 1, 2 learns the chirality with certainty at that reading. Whether
that is a privacy failure in the paper's model depends on whether the deal
description is public. In the PSL all-decks model it is not: the deal is a
hidden draw, uniform and independent of the chirality, and
`psl211_alldecks_view_indep` says the reading is independent of the chirality
after averaging over it. C8 therefore refutes the route, not the instance's
privacy theorem, and it becomes a statement about privacy itself only under a
threat model in which the deal is revealed to the coalition. The probe is
entitled to the first claim only, and STATUS.md line 213 makes exactly that
claim.

## S5 Mutations

All seven were recaptured by the auditor with
`rocq repl -q <flags> < <file>.v`, which echoes the message that
`rocq compile` swallows. All seven still fail, and the first `The term` line of
each matches STATUS.md's table:

```text
dealer_kernel_probe #1: The term "secretP `X delta" has type
dealer_kernel_probe #2: The term "dealer_view_indep (mu:=fdist1 x)" has type
carrier_transport_probe #1: The term "proj1 (inde_RV_fdistmap P f X Y)" has type
pgl27_deterministic_bridge #1: The term "erefl" has type
pgl27_deterministic_bridge #2: The term "HC" has type "is_true (#|C| <= 3)%N"
psl211_alldecks_bridge #1: The term "fdistmap_prod_sectionE (h:=h)" has type
psl211_alldecks_bridge #2: The term "erefl" has type
```

Two positive controls are declared and both are reported `is defined`
immediately before their mutation in the same run:
`dealer_shuffle_view_indep_with_common_law` and
`fdistmap_prod_sectionE_with_sections`.

Judgement, mutation by mutation.

1. `dealer_shuffleP_missing_shuffle`. Intended reason, and it fires: the error
   prints the term's actual inferred type
   `{fdist Datatypes_prod__canonical__fintype_Finite secretT deckT}`, so the
   spelling elaborates and the mismatch is precisely the missing third
   coordinate. No separate control is needed, because the error itself
   discloses a well-formed type. The auditor compiled the control anyway:
   ``Definition audit_missing_shuffle_control : R.-fdist (secretT * deckT) :=
   secretP `X delta`` compiles.
2. `dealer_shuffle_view_indep_without_common_law`. Intended reason, leftover
   arrow, declared control present. This is the check for invariant 4 and it
   fires.
3. `inde_RV_fdistmap_bad_reader`. Intended reason. The error prints the correct
   statement as the term's type and the unification failure names the two
   readers, `pfwd1 (Y \o f) y` against `` `Pr[ (Ybad) = (y) ] ``. Self-
   controlling for the same reason as 1.
4. `pgl27_dealer_bad_viewE`. Intended reason: `erefl` cannot bridge
   `orbit_encode (~~ b)` and `orbit_encode b`. No declared control, but the
   good version `pgl27_dealer_viewE` at L93 compiles by `by []` twenty lines
   earlier, which is the control in fact if not in name.
5. `pgl27_alldecks_dealer_view_law_without_validity`. This is the one
   STATUS.md itself flags, and the auditor's judgement is that the flag
   understates the problem. The mutation drops `uniq d` from the ascribed
   statement and supplies `HC : (#|C| <= 3)%N` in the `uniq d` slot; the
   failure is an argument-position mismatch between two adjacent `is_true`
   premises. Had the two premises been declared in the other order, `HC` would
   have landed correctly and the mutation would have failed later or not at
   all, so the test is fragile in a way unrelated to validity. It shows neither
   that the unvalidated statement is unprovable nor that it is false. The
   honest test is one of: supply the lemma one argument short, so the failure
   is a leftover arrow as in mutations 2 and 6, with `pgl27_alldecks_dealer_view_law`
   named as the positive control; or exhibit a deck with a repeated card at
   which the equation fails, which is the only thing that shows validity is
   needed for truth rather than for typing. Finding F1.
6. `fdistmap_prod_sectionE_without_sections`. Intended reason, leftover arrow,
   declared control present.
7. `psl211_dealer_bad_secretE`. Intended reason: `erefl` cannot bridge `~~ b`
   and `b`. Implicit control `psl211_dealer_secretE` at L204.

So of the five without a declared control, 1 and 3 need none because the error
prints the well-formed inferred type, 4 and 7 have an implicit control in the
good-version lemma immediately above, and 5 is the weak one. No mutation is
meaningless. STATUS.md's sentence that the two declared controls make "each
mutation known to fail for the missing premise" should name the implicit
controls. Finding F6.

## S6 Invariants 2 and 9, and scope

Invariant 2, no computational premise. A word-boundary scan of all seven
`.v` files for `negligible`, `advantage`, `adversary`, `poly`, `epsilon`,
`approx`, `PPT`, `hardness` and related vocabulary returns nothing. Every
result is an exact equality or disequality of distributions over an arbitrary
`realType`, or an exact independence. The three `vm_compute` uses
(`psl211_per_deck_counter.v:56`, `:61`, `:132`) are kernel conversions
producing proofs of `nat` facts, not premises; that file reports
`Closed under the global context` for all eight of its lemmas, so nothing at
all is assumed there.

Invariant 9, no permanent source imports a probe file. A recursive search of
`lib protocol groups security smc reconstruct instances manifest` for
`general_dealer_law_probe` and for each of the seven probe file names returns
no hit. The repository root `_CoqProject` and `Makefile*` do not mention the
probe library or this directory.

Nothing in the production tree was modified: `git status --porcelain
--untracked-files=no` is empty at the start and at the end of the audit.

The probe directory is unchanged by this audit. `shasum -a 256 -c` over all
seven `.v` files, the three `.md` files and `_CoqProject` reports `OK` for
every entry, and the probe's own `.vo` timestamps are still those of the
original run.

Scope of the build. `_CoqProject` lists exactly the seven probe `.v` files and
ends with `-Q . general_dealer_law_probe`. `.Makefile.rocq.d` contains no
target whose path leaves this directory. `make` was not run. Finding F10.

## S7 Other observations a paper reviewer would raise

**STATUS.md's assertions against compiled lemmas.** Every sentence in STATUS.md
that asserts a mathematical fact was traced to a named compiled lemma, and all
of them hold. The measured costs, the assumption reports, the seven mutation
messages, the instantiation table, the C8 counts, the provenance of
`uniform_fdistmap_pointE`, and the statement of `psl211_perdeck_no_common_law`
all check out; the details are in the sections above. Two sentences are process
claims rather than mathematical ones and were handled differently: the `make -n`
claim was checked statically because running `make` is forbidden here (F10),
and the `Eval vm_compute in val (inord 0)` timings are measurements that
justify a design choice and carry no result.

**The naming pass changed no statement and no proof.** STATUS.md claims this.
The auditor checked it by applying the rename table to each `history/*.2026-09-18-before-rename.v`
copy, stripping comments and normalising whitespace, and comparing. Five of the
seven files are then character-identical. The two residual differences are one
identifier the published table omits
(`pgl_deck_view_law_without_validity` became
`pgl27_alldecks_dealer_view_law_without_validity`) and one `;` that became a
`.` when a line was split for the 80-column rule, inside
`psl211_dealer_mixed_lawE`. The claim holds.

**The probe's generic surface is larger than the design note proposed.** The
design note's "Proposed generic declarations" section names seven items. The
probe also introduces `fdistmap_prod_sectionE`, `uniform_fdistmap_fiberTE` and
`uniform_fdistmap_pointE`, and a search of the production tree confirms none of
the three exists there. STATUS.md discloses only the third as new. An
implementation plan sized on the design note would undercount the permanent
module by three declarations and by the refactoring of
`design_privacy.uniform_fdistmap_fiberE` that `uniform_fdistmap_pointE` invites.
Finding F9.

**The PGL all-decks arm reproduces counting content.** Recorded as F2. The
concrete measurement: the proof of `pgl27_dealer_view_law` (L130-165) and the
proof of `pgl27_alldecks_dealer_view_law` (L285-319) are 88% textually
identical, and both build the same `Hcomp` reindexing before applying
`ktuple_encode_uniform`. A permanent module should factor the shared block into
one lemma parameterised by the deck.

**Mechanical checks.** No probe `.v` line exceeds 80 characters. No `Time`,
`Timeout`, `Fail Timeout` or `Show` occurs. Every `Definition`, `Lemma` and
`Corollary` in every probe `.v` file is preceded by a `(** ... *)` statement
comment. Every `Local Opaque` is released by a `Local Transparent` before the
file's `Print Assumptions` block, so no seal leaks into a requiring file. The
banned-vocabulary scan over the probe `.v` files and STATUS.md returns nothing.

## What the paper may claim, and what it may not

May claim. One dealer law `secretP `X (fun s => delta s `x nu)` represents all
three concrete models, and all three of the development's existing privacy
statements are recovered through it with statements convertible with the
originals, at an arbitrary real field and at the standard real line, on the
three `boolp` axioms alone. Privacy follows from the model when every
positive-mass secret induces the same mixed observation law, and, as a stronger
sufficient condition, when every positive-mass deck is valid and every valid
deck induces the same observation law under the shuffle alone. The PGL(2,7)
rows satisfy the stronger condition, deck by deck, from 3-transitivity. The
PSL(2,11) row satisfies only the weaker one, and its privacy is a property of
the uniform average over deal descriptions: at one explicit deal, one coalition
of three seats and one reading, the two chiralities admit 0 and 1 producing
cuts, so no law on readings is their common conditional law at that deal, and
the per-deck condition has no solution for this instance.

May not claim. That any dealer law preserves privacy. Nothing in the probe
supports it and the mutation at `dealer_kernel_probe.v:137` is a machine-checked
demonstration that the file's own lemma does not yield it. That the PSL(2,11)
instance lacks per-deck privacy as a security property: what is proved is that
the per-deck route is closed, which is a statement about the sufficient
condition and not about the instance. Upgrading it to a privacy failure needs
the further assumption that the deal description is public, which the all-decks
model does not make. That the PGL all-decks arm reuses the existing counting
lemma: it proves a new per-deck law instead, and the implementation cost should
be stated accordingly.

VERDICT: GO
