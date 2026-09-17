#!/bin/bash
# Compile one probe file of this directory against the repo load path,
# with the probe directory itself bound to the logical name "probe".
R=/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc
P=notes/probes/2026-09-18-pgl27-encoding-parameter
cd "$R" || exit 1
LIBS=$(grep "^COQMF_COQLIBS_NOML" Makefile.rocq.conf | sed "s/^[^=]*= *//")
exec rocq compile $LIBS -Q "$P" probe -w none "$P/$1.v"
