# rocq-pgg-smc

Formalization of PGG-SMC: group-based secure multiparty computation
(card-based protocols, RAAG hopping, entropy security bounds), in Rocq,
over the infotheo library.

Extracted 2026-08-26 from the `pgg-smc/` subtree of the infotheo-pgg
fork; see `docs/superpowers/specs/2026-08-26-rocq-pgg-smc-extraction-design.md`.

## Build

Requires Rocq 9.0, MathComp 2.5, and the published `coq-infotheo`
package, version 0.9.7 or later (`opam install coq-infotheo`). A
`coq-infotheo` dev pin also works; the sources are verified against
both (0.9.7 release and the dumas2017dual dev line).

    make -j8        # compile everything in _CoqProject
    make clean

The piSMC language modules (`smc/`: `graded_resource`, `smc_interpreter`,
`smc_session_types`, `pismc`) are vendored into this repository — they
are fork-only work absent from released infotheo.

Logical namespaces: `pgg_smc` (most directories, including `smc/`),
`pgg_reconstruct` (`reconstruct/`).
