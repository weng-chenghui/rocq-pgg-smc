# rocq-pgg-smc

Formalization of PGG-SMC: group-based secure multiparty computation
(card-based protocols, RAAG hopping, entropy security bounds), in Rocq,
over the infotheo library.

Extracted 2026-08-26 from the `pgg-smc/` subtree of the infotheo-pgg
fork; see `docs/superpowers/specs/2026-08-26-rocq-pgg-smc-extraction-design.md`.

## Build

Requires the opam switch at `~/Projects/coq` (Rocq 9.0.0, MathComp 2.5,
`coq-infotheo` pinned to `~/Projects/coq/infotheo#dumas2017dual`).

    make -j8        # compile everything in _CoqProject
    make clean

Logical namespaces: `pgg_smc` (most directories), `pgg_reconstruct`
(`reconstruct/`).
