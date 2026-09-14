#!/bin/sh
# Compile one probe with the project's real flags (from Makefile.rocq), from the
# probe directory so that `Load "psl211_tables.v"` resolves.  Usage: ./run.sh probe_group.v
set -e
ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$(dirname "$0")"
exec rocq compile -q \
  -w -projection-no-head-constant -w -redundant-canonical-projection \
  -w -notation-overridden -w -ambiguous-paths -w -notation-incompatible-format \
  -w -deprecated-native-compiler-option -native-compiler no \
  -R "$ROOT/lib" pgg_smc -R "$ROOT/protocol" pgg_smc -R "$ROOT/groups" pgg_smc \
  -R "$ROOT/security" pgg_smc -R "$ROOT/smc" pgg_smc -R "$ROOT/reconstruct" pgg_reconstruct \
  -R "$ROOT/instances/pgl27" pgg_smc -R "$ROOT/manifest" pgg_smc \
  "$@"
