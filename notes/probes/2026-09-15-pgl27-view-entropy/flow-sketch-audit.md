## 1. Named lemmas and interfaces

The sketch's object names are readable DSL aliases, not claimed Rocq
declarations. `census_rows` is `pgl27_group_table`, exposed by the
`pgl27_leakage_census` module. `group_actions` is represented by
`pgl27_table_perm` together with its membership, injectivity, and surjectivity
lemmas in `table_group_bridge.v:47-181`. `masked_views` is
`pgl27_view R (pgl27_code_coalition S)`, and its census bridge is
`pgl27_view_codesE` at `view_collision_probability.v:189-206`.

Rocq MCP confirms the external interfaces:
`pgl27P : forall R, {fdist bool * pgg_gT pgl27_M}`,
`pgl27_view : forall R, {set 'I_8} -> RV (pgl27P R) -> ffun`,
`pgl27_collisions : seq nat -> nat`, and
`mutual_info_binary_ambiguityE` with the uniform-secret and reachable
posterior premises used by the sketch. The four C8 endpoints are at
`ambiguous_probability.v:530-582`, the four connected C10 endpoints are at
`headline_connection.v:24-84`, and the four C11 endpoints are at
`headline_decomposition.v:52-99`.

## 2. Source, coalition, event, and secret identity

`probe_view_definitions.v:14-31` defines the coalition conversion, restricted
view, and ambiguous-view event once. Repository search finds no second
definition in the probes. C8 at `ambiguous_probability.v:530-582`, C10 at
`posterior_entropy.v:338-390`, and the connection wrappers at
`headline_connection.v:24-84` all use `pgl27P R`, `pgl27_secret R`,
`pgl27_view R (pgl27_code_coalition S)`, and
`pgl27_ambiguous_views R S` with the same representative `S`. Rocq MCP
closed the harmonic connection wrapper by exact application of the posterior
theorem, so no transport or conversion is hidden between those objects.

## 3. Composition endpoints

The imports and theorem applications now follow the sketch. C5 enters C6 and
C7 because `view_collision_probability.v:12-13` imports the shared objects
and table bridge. C8 imports those bridges at
`ambiguous_probability.v:13-15`. C10 imports the shared objects and C6/C7 at
`posterior_entropy.v:291-292`. `headline_connection.v:8-10` imports C8 and
C10 and exposes the latter with the exact C8 event. Finally,
`headline_decomposition.v:9-11` imports C8 and the connection endpoints, and
each representative proof composes the matching pair.

Rocq MCP closed the harmonic C11 proof in 4 ms with the connection theorem and
the harmonic C8 equation. The other three proofs have the same form at
`headline_decomposition.v:70-72,83-85,96-98`. The monad verdict is accurate
when read as category-like composition in `Prop`: equalities, implications,
and exact theorem applications compose propositionally, while the shared
definitions make the object endpoints definitionally identical. There is no
computational effect that would require a plain, graded, or parameterised
monad.

## 4. Items outside the flow

The malformed-row, outside-permutation, changed-deal, omitted-coordinate,
injectivity, reachability, non-definitional, and neighbouring-count checks are
validation probes. They remain outside the value flow and are Local at
`table_group_bridge.v:36-43,104-110,194-202`,
`view_collision_probability.v:115-156`,
`ambiguous_probability.v:584-608`, and
`posterior_entropy_mutations.v:10-56`.

`concrete_real_instance.v` is a satisfiability witness for the carrier, and
the `Print Assumptions` commands are trust checks. Neither produces the
probability-to-entropy value. Orbit transport to every coalition remains C14,
outside this representative-only flow. The final endpoints are exactly the
four named representatives.

VERDICT: GO
