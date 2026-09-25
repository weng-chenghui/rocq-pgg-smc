# syntax=docker/dockerfile:1

FROM mathcomp/mathcomp@sha256:ad95400eeb7f6fecb9d3b85673bf58990ae5800d9a8c41fd533e2f9678754cbc

USER root
ENV OPAMROOT=/home/rocq/.opam
WORKDIR /workspace

COPY rocq-pgg-smc.opam .
RUN eval "$(opam env --set-switch)" && \
    opam install ./rocq-pgg-smc.opam --deps-only --yes

COPY dist/pgg-smc-flat.tar.gz /tmp/pgg-smc-flat.tar.gz
ARG ROCQ_JOBS=1
RUN tar -xzf /tmp/pgg-smc-flat.tar.gz -C . && \
    rm /tmp/pgg-smc-flat.tar.gz && \
    opam exec -- rocq makefile -f _CoqProject -o Makefile.rocq && \
    ulimit -s unlimited && \
    case "$ROCQ_JOBS" in ''|*[!0-9]*|0) exit 2;; esac && \
    opam exec -- make -f Makefile.rocq -j"${ROCQ_JOBS}" && \
    opam exec -- make -f Makefile.rocq install

ARG SOURCE_URL="https://github.com/weng-chenghui/rocq-pgg-smc"
ARG SOURCE_REVISION
LABEL org.opencontainers.image.source="${SOURCE_URL}" \
      org.opencontainers.image.revision="${SOURCE_REVISION}" \
      org.opencontainers.image.title="rocq-pgg-smc" \
      org.opencontainers.image.description="Compiled flattened PGG-SMC Rocq development"

USER rocq
ENTRYPOINT ["opam", "exec", "--"]
CMD ["sh", "-c", "find \"$(opam var lib)\" -path '*/pgg_smc/pgg_instance.vo' -print -quit | grep -q ."]
