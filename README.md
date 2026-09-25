# rocq-pgg-smc

Formalization of PGG-SMC (Parametric Group Game SMC): group-based secure
multiparty computation — card-based protocols, RAAG hopping, entropy
security bounds — in Rocq, over the infotheo library. A PGG is a protocol
game parametric over an instance (G, N, rho): a finite group G acting on
N card positions through a permutation representation rho, with
dealer-sampled words and entropy-quantified coalition security.
(Historical note: PGG formerly expanded to "Parametric Geometry Group";
the geometry reading is retired, 2026-08-26.)

Extracted 2026-08-26 from the `pgg-smc/` subtree of the infotheo-pgg
fork; see `docs/superpowers/specs/2026-08-26-rocq-pgg-smc-extraction-design.md`.

## Build

Requires Rocq 9.0, MathComp 2.5, and the published `coq-infotheo`
package, version 0.9.7 or later (`opam install coq-infotheo`). A
`coq-infotheo` dev pin also works; the sources are verified against
both (0.9.7 release and the dumas2017dual dev line).

    make -j8        # compile everything in _CoqProject
    make clean

### Building with Docker

The image installs the Rocq toolchain and the MathComp dependencies at build
time. Running the container compiles every source listed in the flattened
`_CoqProject` with `make`.

```shell
make docker-build
docker run --rm rocq-pgg-smc-flat
```

The Make target first creates `dist/pgg-smc-flat.tar.gz` from committed `HEAD`.
The flattening step excludes the complete `legacy/` tree and verifies the flat
development with the configured host opam switch. The Docker build then
installs the dependency constraints from `rocq-pgg-smc.opam` and copies only
the flattened sources into the image. The first build can take a long time
while opam compiles the Rocq dependencies.

A successful run ends with `make` exiting with status 0 and no `Error` line in
the output. To build the image and run this check in one command, use:

```shell
make docker-check
```

The check compiles one Rocq file at a time by default. In the current Docker
image, compiling `pgl27_group.v` was observed to use about 5.4 GiB of memory.
Using all available CPU cores can therefore exhaust Docker Desktop's memory
when several Rocq processes run together, in which case `make` reports the
affected process as `Killed`.

The container also raises its soft stack limit from Alpine's 8 MiB default.
The computation in `pgl27_spectral.v` exceeds that default and otherwise ends
with `Stack overflow`.

Limiting parallelism does not reduce the memory required by one Rocq process.
On this machine, `psl211_endpoints.v` reached about 15.3 GiB and caused severe
swapping under a 15.6 GiB Docker memory limit. Increase Docker Desktop's memory
limit before the full check if it approaches that limit even with one job.

Set `DOCKER_JOBS` to choose the number of parallel Rocq compilation jobs:

```shell
make docker-check DOCKER_JOBS=2
```

Increase this value only when the Docker memory limit can hold the concurrent
Rocq processes.

To inspect the image or keep its compiled files, start a shell:

```shell
docker run --rm -it --env ROCQ_JOBS=1 rocq-pgg-smc-flat sh
ulimit -s unlimited
opam exec -- make -f Makefile.rocq -j"${ROCQ_JOBS:-1}"
```

The piSMC language modules (`smc/`: `graded_resource`, `smc_interpreter`,
`smc_session_types`, `pismc`) are vendored into this repository — they
are fork-only work absent from released infotheo.

Logical namespaces: `pgg_smc` (most directories, including `smc/`),
`pgg_reconstruct` (`reconstruct/`).
