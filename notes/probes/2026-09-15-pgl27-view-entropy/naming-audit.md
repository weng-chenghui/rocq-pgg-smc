## Findings

| # | Claim (spec location) | Verdict | Evidence | Fix |
|---|---|---|---|---|
| 1 | C6 wording and mutation, spec lines 147 | GO | `view_collision_probability.v:20-26` states that repeated positions do not affect masked-view equivalence. Lines 133-156 give the omitted-observed-coordinate counterexample. Neither statement assumes that the sequence is unique. | None. |
| 2 | Representative-only scope, spec lines 26-40, 152, and 155 | GO | `headline_decomposition.v:52-99` exports exactly four mutual-information equations for `rep_harmonic`, `rep_equianharmonic`, `rep_five`, and `rep_six`. Rocq MCP opened the harmonic theorem with a goal containing `rep_harmonic`, and its source proof closed in 4 ms. No final theorem quantifies over an arbitrary coalition. | None. |
| 3 | Stable probe imports, spec lines 214-229 | GO | `_CoqProject:7-29` records the project roots and `-Q . pgl27_view_entropy_probe`. Lines 31-39 list all nine files in dependency order. `Makefile.rocq.conf:35-36` contains the same mapping, and the final ordered build used it successfully. | None. |
| 4 | Single-source coalition, view, and ambiguity objects, C13 at spec line 154 | GO | Repository search finds `pgl27_code_coalition`, `pgl27_view_codes`, and `pgl27_ambiguous_views` defined only at `probe_view_definitions.v:14`, `:19`, and `:25`. C8, C10, and C11 import that module instead of redeclaring these objects. | None. |
| 5 | C8, C10, and C11 object identity, spec lines 149-152 | GO | C8 uses `pgl27P R` through `pgl27_view R (pgl27_code_coalition S)` and `pgl27_ambiguous_views R S` at `ambiguous_probability.v:530-582`. C10 uses the same terms at `posterior_entropy.v:338-390`. The four wrappers at `headline_connection.v:24-84` have those exact statements. Rocq MCP closed the harmonic wrapper with `exact: posterior_entropy.pgl27_reachable_view_entropy_harmonicE.` in 0 ms. | None. |
| 6 | C11 composition endpoints, spec lines 134-136 and 152 | GO | `headline_decomposition.v:9-11` imports the shared definitions, C8, and `headline_connection`. Each final proof at lines 57-59, 70-72, 83-85, and 96-98 supplies the representative `memE` posterior theorem and then rewrites the matching C8 probability equation. Rocq MCP checked the harmonic proof to completion. | None. |
| 7 | Identifier discipline, `E` suffixes, and Local helpers, C13 at spec line 154 | GO | The public C8 equations at `ambiguous_probability.v:530-582`, C10 equations at `posterior_entropy.v:314-390`, connection equations at `headline_connection.v:24-84`, and C11 equations at `headline_decomposition.v:52-99` use the `E` suffix. Generic and mutation declarations are Local at `table_group_bridge.v:36-43,104-110,194-202`, `view_collision_probability.v:115-184`, and `posterior_entropy_mutations.v:10-43`. A repository search found no live declaration with any exported probe name outside this directory. | None. |
| 8 | Statement comments | GO | Shared-object comments at `probe_view_definitions.v:12-31` state the mathematical fact and its security meaning. Bridge comments at `view_collision_probability.v:20-55,186-188` now describe equality and observation semantics without usage narration or bracketed identifiers. Representative C8, C10, connection, and C11 statements each have a fact-and-position comment. Timing text remains an ordinary proof comment at `view_collision_probability.v:178-181`, not a declaration comment. | None. |
| 9 | MathComp setup, names, and physical form | GO | Every one of the nine files begins with `From HB Require Import structures.` and contains all three setup commands. Mechanical searches found no line over 80 columns, tab, or trailing whitespace. The MathComp quick audit reported only conditional explicit-`@` candidates. Inspection shows these sites provide otherwise hidden carriers, indices, or dependent arguments. | None. |
| 10 | Probe-only dependency direction, spec lines 214-231 | GO | The source chain is `probe_view_definitions.v` to `table_group_bridge.v` to `view_collision_probability.v` to `ambiguous_probability.v`, with `posterior_entropy.v`, `headline_connection.v`, and `headline_decomposition.v` consuming that chain. Repository search outside the probe directory found no permanent `.v` import of `pgl27_view_entropy_probe`. | None. |
| 11 | External interface types used by the flow | GO | Rocq MCP reports `pgl27P : forall R, {fdist bool * pgg_gT pgl27_M}`, `pgl27_view : forall R, {set 'I_8} -> {RV (pgl27P R) -> {ffun 'I_8 -> 'I_8}}`, and `pgl27_collisions : seq nat -> nat`. It also reports that `mutual_info_binary_ambiguityE` takes a uniform Boolean marginal and the reachable-view posterior indicator used by C10. | None. |

## Blocking findings

None.

## What I compiled

- The final ordered build ran
  `/usr/local/bin/opam exec --switch=/Users/cheng-huiweng/Projects/coq -- make -f Makefile.rocq -j1`
  in the probe directory and returned exit code 0. It compiled the nine files
  through the probe-local `-Q` mapping. The only admitted declaration reported
  for the decomposition file was the spec-permitted
  `pgl27_secret_uniform`.
- Rocq MCP opened
  `pgl27_reachable_view_entropy_harmonic_memE` and closed its source proof
  with the qualified posterior theorem in 0 ms.
- Rocq MCP opened `pgl27_mutual_info_ambiguity_harmonicE` and closed its
  source proof from the connection endpoint and C8 equation in 4 ms.
- An earlier direct `rocq_compile_file` call did not read the probe-local
  `_CoqProject` and therefore lacked the `pgg_smc` path. The final ordered
  build above used the recorded configuration and supersedes that tool-context
  failure.

VERDICT: GO
