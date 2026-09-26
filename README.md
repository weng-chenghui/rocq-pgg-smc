# rocq-pgg-smc

Formalization of PGG-SMC (Parametric Group Game SMC): group-based secure
multiparty computation — card-based protocols, entropy
security bounds — in Rocq, over the infotheo library. A PGG is a protocol
game parametric over an instance (G, N, rho): a finite group G acting on
N card positions through a permutation representation rho, with
dealer-sampled words and entropy-quantified coalition security.
(Historical note: PGG formerly expanded to "Parametric Geometry Group";
the geometry reading is retired, 2026-08-26.)

Extracted 2026-08-26 from the `pgg-smc/` subtree of the infotheo-pgg
fork; see `docs/superpowers/specs/2026-08-26-rocq-pgg-smc-extraction-design.md`.

## Building with Docker

Docker needs no local Rocq installation. The image installs the dependencies,
compiles every source in the flattened `_CoqProject`, and installs the result.
All of this happens during `docker build`.

```shell
make docker-build                      # flatten HEAD, then build the image
docker run --rm rocq-pgg-smc-flat      # check the installed development
docker run --rm -it rocq-pgg-smc-flat sh   # open a shell in the image
```

`make docker-build` first writes `dist/pgg-smc-flat.tar.gz` from the committed
`HEAD`. Uncommitted changes are not included. The flattened archive leaves out
the whole `legacy/` tree. The Docker build installs the dependency constraints
from `rocq-pgg-smc.opam` and copies only the flattened sources into the image.
The first build can take a long time while opam installs dependencies and Rocq
compiles the development.

Running the image without a command checks that an installed module is
present. It prints nothing and exits with status 0 on success. To build the
image and run this check in one step, use:

```shell
make docker-check
```

### Memory and parallel jobs

`DOCKER_JOBS` sets the number of Rocq files compiled at the same time during
the image build. The default is 1:

```shell
make docker-build DOCKER_JOBS=2
```

Raise it only when Docker has enough memory for several Rocq processes at
once. Compiling `pgl27_group.v` alone used about 5.4 GiB. When several such
processes run together, Docker Desktop can run out of memory and `make`
reports the process as `Killed`.

One job does not lower the memory needed by a single file. In one measured
build, `psl211_endpoints.v` reached about 15.3 GiB and caused heavy swapping
under a 15.6 GiB Docker memory limit. Set Docker Desktop's memory limit well
above that before a full build.

The build also raises the stack limit above the usual 8 MiB default. The
computation in `pgl27_spectral.v` needs more than that and otherwise stops
with `Stack overflow`.

## Building locally

Requires Rocq 9.0 or 9.1, MathComp 2.5, and the published `coq-infotheo`
package, version 0.9.7 or later. A `coq-infotheo` dev pin also works. The
sources are checked against both the 0.9.7 release and the dumas2017dual dev
line. The full dependency list is in `rocq-pgg-smc.opam`, and opam can
install it:

```shell
opam install ./rocq-pgg-smc.opam --deps-only
```

Then build:

```shell
make -j8          # compile everything in _CoqProject
make install      # optional: install the compiled library
```

To remove the build outputs later, run `make clean`.

## GitHub releases and Docker packages

The release for the WADT 2026 paper is
https://github.com/weng-chenghui/rocq-pgg-smc/releases/tag/WADT2026-r1.

Each push to `main` also creates a commit-specific prerelease as soon as the
flattened source archive is ready. The release tag has the form
`wadt2026-<full-commit-sha>`. It does not wait for Rocq compilation.

A second job downloads that exact archive from the release, compiles and
installs it in a Docker image, and publishes the image to GitHub Container
Registry under the full commit SHA. When that job finishes, it adds the
image digest and pull command to the same release. If the image build fails,
the source release stays available. Repeated runs keep the first released
source archive, so the release and the image use the same input.

The flattened archive is a source artifact, not an installable opam package.
Rocq has no portable package format for compiled `.vo` files. The Docker
image supplies the compiled development together with the Rocq and library
versions used to build it.

## Layout

The piSMC language modules (`smc/`: `graded_resource`, `smc_interpreter`,
`smc_session_types`, `pismc`) are vendored into this repository — they
are fork-only work absent from released infotheo.

Logical namespaces: `pgg_smc` (most directories, including `smc/`),
`pgg_reconstruct` (`reconstruct/`). The flattened archive and the Docker
image use the single namespace `pgg_smc` for both.
