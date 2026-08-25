#!/usr/bin/env bash
# Build the PGG framework blueprint: the HTML + dependency graph, plus the
# coqdoc API pages the \rocq{...} node links point at (the \dochome target).
set -euo pipefail

BP="$(cd "$(dirname "$0")" && pwd)"          # .../rocq-pgg-smc/blueprint
REPO="$(cd "$BP/.." && pwd)"                 # repo root (has _CoqProject)

# Reuse the rocqblueprint/plasTeX install from the dumas2017dual blueprint venv
# (document-agnostic). Override with PLASTEX=... if it lives elsewhere.
PLASTEX="${PLASTEX:-$(command -v plastex || true)}"

# -R mappings matching _CoqProject so coqdoc emits pgg_reconstruct.<mod>.html
# and pgg_smc.<mod>.html, the filenames the \rocq{...} links resolve to.
RFLAGS=(-R lib pgg_smc -R protocol pgg_smc -R groups pgg_smc -R security pgg_smc
  -R reconstruct pgg_reconstruct
  -R instances/denboer1989 pgg_smc -R instances/kim2025 pgg_smc
  -R instances/s5 pgg_smc -R instances/s5x5 pgg_smc
  -R instances/oc pgg_smc -R instances/star pgg_smc
  -R instances/abelian pgg_smc -R instances/cyclic pgg_smc
  -R instances/monster pgg_smc -R instances/pgl27 pgg_smc
  -R manifest pgg_smc)

# Modules referenced by \rocq{...} in content.tex (their .glob is present after
# a normal project build).
MODULES=(
  protocol/pgg_interface.v
  protocol/pgg_monodromy_profile.v
  protocol/card_exchange_pismc.v
  protocol/pgg_input_commitment.v
  reconstruct/pgg_sharing_framework.v
  reconstruct/covering_scheme.v
  reconstruct/input_encoding.v
  reconstruct/algebraic_rigidity.v
  reconstruct/cover_tradeoff.v
  reconstruct/s5_nogo.v
  reconstruct/invariant_profiler.v
  reconstruct/gap_dimension.v
  reconstruct/cover_genus0.v
  reconstruct/cover_genus1.v
  reconstruct/cover_genus2.v
  reconstruct/combinatorial_rigidity.v
  instances/denboer1989/five_card_scheme_I5.v
  instances/denboer1989/den_boer_encoding.v
  instances/denboer1989/den_boer_run.v
  instances/denboer1989/den_boer_profile.v
  instances/denboer1989/five_card_leakage.v
  instances/kim2025/five_card_kim.v
  instances/kim2025/five_card_family.v
  instances/kim2025/rigidity_kim_instance.v
  instances/s5/rigidity_s5_instance.v
  instances/s5/s5_mixing.v
  instances/s5x5/rigidity_s5x5_instance.v
  instances/s5x5/s5x5_pile.v
)

echo "[1/3] blueprint HTML + dependency graph (plastex)"
rm -rf "$BP/web"
( cd "$BP/src" && "$PLASTEX" -c plastex.cfg web.tex )

echo "[2/3] coqdoc API pages -> web/coqdoc (the \\dochome target)"
mkdir -p "$BP/web/coqdoc"
( cd "$REPO" && coqdoc --html --no-externals --utf8 "${RFLAGS[@]}" \
    -d "$BP/web/coqdoc" "${MODULES[@]}" )

echo "[3/3] static dependency-graph image (web/dep_graph.png)"
if command -v dot >/dev/null 2>&1; then
  grep -oE 'digraph[^`]*' "$BP/web/dep_graph_document.html" > "$BP/web/dep_graph.gv" || true
  dot -Tpng "$BP/web/dep_graph.gv" -o "$BP/web/dep_graph.png" 2>/dev/null || true
fi

echo "Done. Serve with:  (cd '$BP/web' && python3 -m http.server 8000)"
echo "Then open http://127.0.0.1:8000/  and click 'Dependency graph'."
