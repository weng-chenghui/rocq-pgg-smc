# PGL(2,7) view census and posterior entropy probe design

Date: 2026-09-15

Status: approved for probe-first validation

## Problem

`pgl27_leakage_census.v` computes collisions between two lists of restricted
views. The lists are produced from a 336-row nat table. The security model in
`pgl27_secrecy.v` instead samples a permutation from `pgg_G pgl27_M` and observes
the random variable `pgl27_view`. No current theorem identifies these two
representations. The collision counts therefore do not yet justify a
probability statement about `pgl27_view`.

The entropy step has a second premise. For a fixed secret, each reachable view
must have one shuffle preimage. When a view occurs for both secrets, its
posterior on the Boolean secret is uniform and has entropy one. When it occurs
for only one secret, the posterior is deterministic and has entropy zero.
The existing `pgl27_views_uniq_*` results provide the required injectivity for
four representative reveal sets, but this implication has not been connected
to the random variable.

## Scope

The first version covers these four representatives:

1. `rep_harmonic`
2. `rep_equianharmonic`
3. `rep_five`
4. `rep_six`

The statements use a uniform Boolean secret and a uniform shuffle from
`pgg_G pgl27_M`. They concern one pre-reveal observation by a fixed coalition.
They are exact information-theoretic equalities for every `R : realType`.

The first version does not quantify over every coalition of size four, five,
or six. Transport from a representative to another coalition in the same
orbit is a later supporting result. The first version also does not include
the seven-position representative.

## Pinned carrier

Every probability and entropy probe is instantiated at the weakest carrier
promised by the result:

```coq
Variable R : realType.
```

The concrete vacuity probe uses MathComp's constructive real carrier that is
already accepted by the project's `realType` interfaces. The table and group
bridge is independent of `R`.

## Chosen representation bridge

Index the nat table by `'I_336` and convert each row to a permutation of
`'I_8`. A computed certificate establishes that every row has eight distinct
entries below eight. A second computed certificate establishes that every
converted permutation belongs to `pgg_G pgl27_M`. Row uniqueness and
`pgl27_card` then give a bijection between table indices and group elements.

For a sequence `S : seq nat`, define its coalition as the positions whose
natural-number values occur in `S`. Compare a full masked `pgl27_view` with the
restricted nat view by reading the coordinates listed in `S`. For each valid
representative, equality of the full masked views is equivalent to equality of
their restricted nat sequences.

This bridge is preferred to recomputing the same numeric probabilities at the
group level. A second computation could agree numerically while leaving the
connection between `code_views` and `pgl27_view` unproved.

## Target statement shapes

The probe will refine names and implicit arguments, but the mathematical
statements are fixed as follows.

```coq
Definition pgl27_code_coalition (S : seq nat) : {set 'I_8} :=
  [set i | val i \in S].

Definition pgl27_ambiguous_views
    (R : realType) (S : seq nat) : {set {ffun 'I_8 -> 'I_8}} :=
  [set v |
     [exists g in pgg_G pgl27_M,
        pgl27_view R (pgl27_code_coalition S) (false, g) == v] &&
     [exists g in pgg_G pgl27_M,
        pgl27_view R (pgl27_code_coalition S) (true, g) == v]].
```

For each of the four representatives, the collision probability statement is:

```coq
`Pr[
  pgl27_view R (pgl27_code_coalition S)
    \in pgl27_ambiguous_views R S
] = (pgl27_collisions S)%:R / 336%:R.
```

For each of the four representatives, every reachable view satisfies:

```coq
`Pr[pgl27_view R (pgl27_code_coalition S) = v] != 0 ->
`H[
  pgl27_secret R |
  pgl27_view R (pgl27_code_coalition S) = v
] = (v \in pgl27_ambiguous_views R S)%:R.
```

The right side coerces a Boolean membership test into `R`, so it is exactly
zero or one. The statement does not assign a posterior entropy to unreachable
views.

## Supporting proof shapes

1. The table rows define permutations and their application agrees with
   `nth` on the corresponding row.
2. The table-index-to-permutation map is injective, belongs to
   `pgg_G pgl27_M`, and is surjective onto that group by cardinality.
3. `code_deal b` agrees pointwise with `orbit_encode b`.
4. `code_comp` agrees with the order of application in `pgl27_view`.
5. For a valid representative, equality of masked full views is equivalent to
   equality of the restricted nat sequences.
6. `pgl27_views_uniq_*` makes the conditional view map injective for each
   secret.
7. The ambiguous event contains two source points, one for each secret, for
   every ambiguous reachable view. A non-ambiguous reachable view contains one
   source point.
8. Uniform sampling on the source makes the posterior uniform on this one- or
   two-element compatible-secret set.
9. `centropy1_uniform_over_set` turns the compatible-secret set size into its
   logarithm. `log 1 = 0` and `log 2 = 1` give the requested result.
10. `mutual_info_binary_ambiguityE` accepts the posterior theorem directly as
    its second premise. This is a downstream composition check, not a third
    requested headline result.

## Claim ledger

| ID | Checkable claim | Passing evidence |
|---|---|---|
| C1 | Every row of `pgl27_group_table` has length eight, contains distinct entries, and contains only values below eight. | A closed computed certificate and a failed mutation with one duplicated or out-of-range entry. |
| C2 | Every table row converts to an element of `pgg_G pgl27_M`. | A closed computed membership certificate at the permutation carrier and a failed mutation using a permutation outside the group. |
| C3 | The converted table rows enumerate `pgg_G pgl27_M` exactly once. | Injectivity from `pgl27_group_table_uniq`, membership from C2, `pgl27_card`, and a surjectivity lemma ending in `Qed`. |
| C4 | The nat deal agrees with `orbit_encode` for both secrets. | A pointwise lemma ending in `Qed` and a mutation that swaps a different pair of codes. |
| C5 | A table row and its converted permutation produce the same restricted view. | A miniature bridge theorem using `code_comp`, `code_deal`, `orbit_encode`, and `pgl27_view`, ending in `Qed`. |
| C6 | For each representative, equality of restricted nat views is equivalent to equality of full masked views. | Four instantiated lemmas ending in `Qed`, plus a mutation using a sequence that does not enumerate its coalition uniquely. |
| C7 | The two per-secret view maps are injective for each representative. | Derivations from the four existing `pgl27_views_uniq_*` lemmas through C3 to C6. |
| C8 | The probability of the ambiguous-view event is `pgl27_collisions S / 336`. | A generic counting miniature and four representative instantiations ending in `Qed`. A tautology probe must confirm the equality is not definitional. |
| C9 | Every reachable posterior is uniform on one or two compatible secrets. | A conditional-probability miniature over a uniform Boolean product distribution, ending in `Qed`. |
| C10 | Every reachable posterior entropy is exactly zero or one according to ambiguous-view membership. | An application of `centropy1_uniform_over_set` at `R : realType`, followed by `log 1` or `log 2`, with four representative instantiations ending in `Qed`. |
| C11 | The entropy theorem composes with `mutual_info_binary_ambiguityE`. | A separate decomposition probe derives the mutual-information shape to `Qed` from admitted supporting declarations. |
| C12 | The section hypotheses are jointly satisfiable. | A concrete representative instantiation compiles without assumptions beyond the constructive real libraries already used by the project. |
| C13 | The proposed identifiers do not collide with live declarations and follow project and MathComp naming conventions. | Repository search and the independent naming audit. |
| C14 | Transport to every same-orbit coalition is outside the first version and needs an explicit invariance theorem. | The spec names no universal coalition headline. The audit confirms that no such conclusion follows silently from a representative theorem. |

## Cited library and project objects

| Object | File | Required statement shape | Probe use |
|---|---|---|---|
| `pgl27_group_table` | `instances/pgl27/pgl27_leakage_census.v` | A repetition-free sequence of 336 nat rows. | Indexed source of the table permutations. |
| `pgl27_group_table_size` | `instances/pgl27/pgl27_leakage_census.v` | `size pgl27_group_table = 336`. | Bounds every table index. |
| `pgl27_group_table_uniq` | `instances/pgl27/pgl27_leakage_census.v` | `uniq pgl27_group_table`. | Proves table-permutation injectivity. |
| `pgl27_views_uniq_harmonic` | `instances/pgl27/pgl27_leakage_census.v` | Both secret-indexed harmonic view lists are unique. | Proves C7 for `rep_harmonic`. |
| `pgl27_views_uniq_equianharmonic` | `instances/pgl27/pgl27_leakage_census.v` | Both secret-indexed equianharmonic view lists are unique. | Proves C7 for `rep_equianharmonic`. |
| `pgl27_views_uniq_five` | `instances/pgl27/pgl27_leakage_census.v` | Both secret-indexed five-position view lists are unique. | Proves C7 for `rep_five`. |
| `pgl27_views_uniq_six` | `instances/pgl27/pgl27_leakage_census.v` | Both secret-indexed six-position view lists are unique. | Proves C7 for `rep_six`. |
| `pgl27_collisions` | `instances/pgl27/pgl27_leakage_census.v` | Counts members of the false view list inside the true view list. | Right side of C8. |
| `pgl27_card` | `instances/pgl27/pgl27_mixing.v` | `#|pgg_G pgl27_M| = 336`. | Completes the finite bijection in C3. |
| `pgl27P` | `instances/pgl27/pgl27_secrecy.v` | Product of uniform Boolean secret and uniform group shuffle. | Probability source for C8 to C10. |
| `pgl27_secret` | `instances/pgl27/pgl27_secrecy.v` | First projection of the product sample. | Posterior variable in C9 and C10. |
| `pgl27_view` | `instances/pgl27/pgl27_secrecy.v` | Masked coalition observation of the encoded deck after the shuffle action. | Event and conditioning variable in C5 to C10. |
| `centropy1_uniform_over_set` | installed `infotheo/dumas2017dual/entropy_fiber/entropy_fiber.v` | Uniform conditional probability on a positive finite set gives entropy equal to the logarithm of its cardinality. | Converts C9 into C10. |
| `mutual_info_binary_ambiguityE` | `lib/proba_entropy_ext.v` | A uniform Boolean secret and a zero-or-one posterior theorem give mutual information `1 - Pr[ambiguous]`. | Decomposition and downstream compatibility probe. |

## Soundness invariants

1. No probe or planned permanent result introduces an axiom, assumed constant,
   or admitted proof. The decomposition probe is the sole exception allowed by
   the probe-first workflow. Its supporting declarations are admitted only to
   check composition and are never imported.
2. Every probability equality is information-theoretic and uses the exact
   uniform distribution in `pgl27P`. No computational-security premise is
   converted into distributional equality.
3. The result is per representative coalition, averaged over the uniform
   Boolean secret and uniform group shuffle. It is a single pre-reveal
   observation. The quantifier over `R : realType` is universal. There is no
   numeric regime in which these exact equalities become vacuous.
4. The view contains exactly the masked card values defined by `pgl27_view`.
   It does not include the public reconstruction reveal or a composed protocol
   transcript.
5. The posterior statement is restricted to reachable views. Without this
   premise, the conditional probability denominator may be zero.
6. The zero-or-one entropy conclusion depends on per-secret injectivity. A
   collision count without injectivity is insufficient because a shared view
   could have unequal multiplicities under the two secrets.
7. The bridge proves equality of the two enumerated experiments. Agreement of
   their final numeric counts alone is not accepted as evidence.
8. Every cited object is exercised at the pinned carrier in compiled code.
9. The hypothesis set is instantiated by all four existing representatives,
   so the generic statement cannot pass only because its premises are
   contradictory.

## Probe artifacts

The retained scratch directory will be:

```text
notes/probes/2026-09-15-pgl27-view-entropy/
```

It will contain:

1. `table_group_bridge.v` for C1 to C5.
2. `view_collision_probability.v` for C6 to C8.
3. `posterior_entropy.v` for C9 and C10.
4. `headline_decomposition.v` for C11. This file alone may contain admitted
   supporting declarations.
5. Mutation files or `Fail` checks that establish sensitivity.
6. Independent soundness and naming audit reports.

No permanent Rocq file may import these probe files.

## Acceptance condition

The specification is ready for an implementation plan only when C1 to C13 are
marked GO with compiled evidence, C14 remains an explicit later extension, the
soundness audit returns `VERDICT: GO`, the naming audit returns `VERDICT: GO`,
and every accepted finding has been folded into this note and committed.
