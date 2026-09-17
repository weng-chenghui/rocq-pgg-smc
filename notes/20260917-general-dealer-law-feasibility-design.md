# General dealer law feasibility probe

Date: 2026-09-17

Status: probe-first validation in progress

## Problem

The paper models a secret-dependent dealer distribution by a family
`delta : secretT -> R.-fdist deckT` and an independent shuffle law `nu`.
The current development has no common declaration for that law. It has three
relevant concrete forms instead.

1. The current PGL exact row samples a secret and a shuffle. Its deck is the
   deterministic value `orbit_encode s` and is not present in the sample
   carrier.
2. The PGL all-decks theorem samples a uniform valid deck for each secret and
   then samples a uniform shuffle.
3. The PSL all-decks row samples a uniform pair of a chirality and a deck
   description, then samples a uniform shuffle. Its proof uses an average over
   all deck descriptions.

The feasibility question is whether one generic dealer law can represent all
three models and enter their existing privacy proof chains without replacing
the instance-specific mathematics by an unsupported stronger claim.

## Scope

This is a feasibility spike. Probe files are retained, but no permanent Rocq
module is implemented at this stage. The probe checks the general probability
law, its privacy transfer theorem, and bridges to the three concrete models.

The probe does not claim that every valid dealer distribution is private.
Privacy requires the mixed view law to be independent of the secret. PGL may
establish that premise per deck. PSL may establish it only after averaging
under its uniform dealer distribution.

## Pinned carrier

The generic probe uses the weakest finite probability carrier needed by the
paper model.

```coq
Variables (R : realType) (secretT deckT cutT viewT : finType).
Variable secretP : R.-fdist secretT.
Variable delta : secretT -> R.-fdist deckT.
Variable nu : R.-fdist cutT.
```

The concrete bridge probes instantiate this carrier at the live PGL and PSL
types under the opam switch `/Users/cheng-huiweng/Projects/coq`.

## Considered representations

### A. Canonical nested carrier

Use `secretT * (deckT * cutT)` and define the law directly by a kernel product.
This matches the paper and lets `inde_prod_kernel_fst` prove the general privacy
transfer. Concrete models with another product association need a pushforward
bridge.

### B. Arbitrary sample carrier with projections

Keep each instance's current sample carrier and describe the dealer law by an
equality after pushing it through secret, deck, and cut projections. This
reduces carrier conversion in instances, but the definition no longer displays
the paper's factorization directly.

### C. A dealer-law record

Package the carrier, projections, factorization, and validity premise in one
record. This is useful only after the representation and bridges have been
compiled. Introducing the record during the probe would hide which field is
actually needed by the proof.

The probe uses A. It keeps the paper equation visible and tests whether the
required pushforward bridges are small enough to justify that choice. A
permanent record remains outside this spike.

## Proposed generic declarations

```coq
Definition dealer_shuffleP
    : R.-fdist (secretT * (deckT * cutT)) :=
  secretP `X (fun s => delta s `x nu).

Definition dealer_secret
    : {RV dealer_shuffleP -> secretT} := fun u => u.1.

Definition dealer_view
    (view : secretT -> deckT -> cutT -> viewT)
    : {RV dealer_shuffleP -> viewT} :=
  fun u => view u.1 u.2.1 u.2.2.
```

The pointwise law must compile as follows.

```coq
Lemma dealer_shufflePE s d g :
  dealer_shuffleP (s, (d, g)) = secretP s * (delta s d * nu g).
```

The headline privacy transfer has a mixed-law premise. This premise is the
exact place where the concrete PGL or PSL argument enters.

```coq
Lemma dealer_view_indep
    (view : secretT -> deckT -> cutT -> viewT)
    (mu : R.-fdist viewT) :
  (forall s, secretP s != 0 ->
     fdistmap (fun dg => view s dg.1 dg.2) (delta s `x nu) = mu) ->
  dealer_shuffleP |= dealer_view view _|_ dealer_secret.
```

A stronger sufficient premise may be useful for transitive PGL models.

```coq
Lemma dealer_view_indep_of_deck
    (valid : secretT -> deckT -> bool)
    (view : secretT -> deckT -> cutT -> viewT)
    (mu : R.-fdist viewT) :
  (forall s d, delta s d != 0 -> valid s d) ->
  (forall s d, secretP s != 0 -> valid s d ->
     fdistmap (view s d) nu = mu) ->
  dealer_shuffleP |= dealer_view view _|_ dealer_secret.
```

The first theorem should reuse `inde_prod_kernel_fst`. The second should use
`fdistmap_prod_const` to establish the first theorem's mixed-law premise.

## Required concrete bridges

### PGL deterministic row

Instantiate `delta s` as `fdist1 (orbit_encode s)`. Prove that pushing the
generic law through the map that drops the deterministic deck gives `pgl27P`.
Prove separately that the generic view under the deterministic deck is
`pgl27_view`. A carrier-transport lemma must then move independence from the
generic law back to the current PGL sample carrier.

The transport lemma has this mathematical shape.

```coq
Lemma inde_RV_fdistmap_pullback
    (A B TA TB : finType) (P : R.-fdist A)
    (f : A -> B) (X : B -> TA) (Y : B -> TB) :
  fdistmap f P |= X _|_ Y ->
  P |= X \o f _|_ Y \o f.
```

### PGL all-decks theorem

Instantiate `delta s` as the uniform distribution on `class_decks s` and `nu`
as the uniform group distribution. The generic law should be definitionally
equal, or reducibly equal, to `alldecksP`. The existing
`alldecks_view_law` should discharge the mixed-law premise without reproducing
its counting proof.

### PSL all-decks row

Instantiate `deckT` as `psl211_deal`. The generic carrier is
`bool * (psl211_deal * pgg_gT psl211_M)`, while the current carrier is
`(bool * psl211_deal) * pgg_gT psl211_M`. Prove equality after the product
reassociation map. Prove that the reassociated generic view is
`psl211_alldecks_view`.

The current PSL fiber-counting theorem may discharge only the mixed-law
premise for the uniform `delta`. The probe must not claim a per-deck law unless
it compiles. A failed per-deck attempt must be reduced to a counter-probe that
shows whether the claim is false or only the attempted proof is wrong.

## Claim ledger

| ID | Checkable claim | Passing evidence |
|---|---|---|
| C1 | `dealer_shuffleP` elaborates at arbitrary finite carriers and has the stated pointwise factorization. | A `Qed` theorem using the actual kernel and product constructors. Dropping one product factor in a mutation must fail. |
| C2 | A secret-independent mixed view law implies independence of `dealer_view` and `dealer_secret`. | A `Qed` miniature using `inde_prod_kernel_fst`. Removing the common `mu` premise must make the mutation fail. |
| C3 | Per-deck constant view laws plus supported validity imply the mixed-law premise. | A `Qed` miniature using `fdistmap_prod_const`, then C2. Removing validity from the link to the per-deck theorem must fail in the PGL instantiation. |
| C4 | Independence transports from a pushforward law to the original carrier through composed readers. | `inde_RV_fdistmap_pullback` ends in `Qed` and is mutation-checked with a reader that does not commute. |
| C5 | The deterministic PGL model is a pushforward instance of the generic law and its view commutes with the bridge. | Compiled distribution and view equations, followed by a theorem deriving the existing PGL independence statement through C2 to C4. A wrong secret encoding must fail the view equation. |
| C6 | The PGL all-decks law is an instance of the generic law. | A compiled equality with `alldecksP`, followed by reuse of `alldecks_view_law` to derive `ttrans_view_indep_alldecks` through C2. |
| C7 | The PSL uniform all-decks law is a reassociated instance of the generic law. | Compiled distribution and view equations, followed by a theorem deriving `psl211_alldecks_view_indep` through C2 and C4 while reusing its fiber-counting content. |
| C8 | The general theorem does not silently strengthen PSL from uniform average privacy to privacy for every dealer law. | Either a compiled per-deck theorem or a compiled concrete counterexample. Failure to prove it without an isolating counter-probe is not evidence. |
| C9 | The generic hypotheses are jointly satisfiable. | Concrete PGL and PSL instantiations compile at a real field and `Print Assumptions` reports no unexpected axioms. |
| C10 | Proposed public identifiers do not collide and match project and MathComp conventions. | Repository search plus an independent naming audit with compiled alternatives for every objection. |

## Cited objects

| Object | File | Required statement shape |
|---|---|---|
| `inde_prod_kernel_fst` | `reconstruct/transitivity_privacy.v` | A constant conditional pushforward under `P `X W` implies independence from the first coordinate. |
| `fdistmap_prod_const` | `reconstruct/transitivity_privacy.v` | Constant section pushforwards imply a constant pushforward of a kernel product. |
| `alldecksP` | `reconstruct/transitivity_privacy.v` | Uniform valid deck per secret, paired with an independent uniform group element. |
| `alldecks_view_law` | `reconstruct/transitivity_privacy.v` | The PGL-style all-decks conditional view law is constant. |
| `pgl27P` | `instances/pgl27/pgl27_secrecy.v` | Uniform Boolean secret paired with a uniform group shuffle. |
| `pgl27_view` | `instances/pgl27/pgl27_secrecy.v` | The masked view of `orbit_encode s` after the sampled action. |
| `pgl27_view_indep_alldecks` | `instances/pgl27/pgl27_secrecy.v` | The PGL uniform all-decks privacy theorem. |
| `psl211_alldecksP` | `instances/psl211/psl211_models.v` | Uniform deck description paired with a uniform group shuffle. |
| `psl211_alldecks_view_indep` | `instances/psl211/psl211_models.v` | The PSL five-seat uniform all-decks privacy theorem. |
| `fdistmap_comp` | installed Infotheo `probability/fdist.v` | Composition of pushforwards. |
| `inde_RV_comp` | installed Infotheo `probability/proba.v` | Post-processing preserves independence. It does not by itself transport the sample carrier. |

## Soundness invariants

1. No probe adds an axiom or assumed constant. Every non-decomposition result
   ends in `Qed` and is checked with `Print Assumptions`.
2. The joint-law equality is information-theoretic. No computational premise
   is used to claim equality of distributions.
3. The model is average-case over `secretP`, then conditional over `delta s`,
   then over the independent law `nu`. The quantifier order is fixed in
   `dealer_shuffleP`.
4. `dealer_view_indep` does not claim privacy for arbitrary `delta`. It claims
   privacy when every positive-mass secret has the same mixed view law.
5. `dealer_view_indep_of_deck` is applicable only when every positive-mass deck
   is valid and every valid deck has the same view law under `nu`.
6. The PGL bridge may use per-deck transitivity. The PSL bridge must retain the
   uniform average over deck descriptions unless a stronger statement is
   compiled.
7. Carrier transport must prove both a distribution equality and commuting
   equations for the secret and view readers.
8. The PGL deterministic bridge, PGL all-decks bridge, and PSL all-decks bridge
   instantiate all generic hypotheses. This is the vacuity check.
9. Probe files are retained and are never imported by permanent source.

## Probe artifacts

The retained scratch directory is:

```text
notes/probes/2026-09-17-general-dealer-law/
```

It will contain:

1. `dealer_kernel_probe.v` for C1 to C3.
2. `carrier_transport_probe.v` for C4.
3. `pgl27_deterministic_bridge.v` for C5.
4. `pgl27_alldecks_bridge.v` for C6.
5. `psl211_alldecks_bridge.v` for C7 and C8.
6. `concrete_instances.v` for C9.
7. `headline_decomposition.v` for the allowed decomposition-only admitted
   supporting statements.
8. `_CoqProject` and `Makefile.rocq` for the project build.
9. `soundness-audit.md` and `naming-audit.md` for independent verdicts.

## Acceptance condition

The general dealer model is feasible only if C1 to C7 and C9 to C10 are GO.
C8 may conclude either that PSL has a stronger per-deck theorem or that its
privacy genuinely depends on the uniform dealer average. In both cases the
general mixed-law theorem must bridge to the current PSL row without assuming
the stronger alternative.

Every probe except `headline_decomposition.v` must contain no `Admitted`,
`Abort`, or `Axiom`. Each mutation must fail for the intended reason. The final
spec requires independent soundness and naming reports ending in
`VERDICT: GO` before an implementation plan is written.
