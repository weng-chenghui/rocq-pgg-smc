# syntax=docker/dockerfile:1

FROM ocaml/opam:alpine-3.21-ocaml-4.14 AS dependencies

RUN sudo apk add --no-cache clang gmp-dev linux-headers pkgconf
RUN opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam update

WORKDIR /home/opam/rocq-pgg-smc
COPY --chown=opam:opam rocq-pgg-smc.opam .
RUN opam install --deps-only -y -j"$(nproc)" ./rocq-pgg-smc.opam && \
    opam clean -a -c -s --logs

FROM dependencies AS artifact

COPY --chown=opam:opam dist/pgg-smc-flat.tar.gz /tmp/pgg-smc-flat.tar.gz
RUN tar -xzf /tmp/pgg-smc-flat.tar.gz -C . && \
    rm /tmp/pgg-smc-flat.tar.gz && \
    opam exec -- rocq makefile -f _CoqProject -o Makefile.rocq

CMD ["sh", "-c", "ulimit -s unlimited && opam exec -- make -f Makefile.rocq -j\"${ROCQ_JOBS:-1}\""]
