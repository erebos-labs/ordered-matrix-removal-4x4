#!/bin/sh
# Full integrated source rebuild; dependency binaries are reused as disclosed.
set -eu
: "${LEAN4_BIN:?Set LEAN4_BIN to a verified official Lean 4.34.1 bin directory}"
ROOT=$(CDPATH= cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
export PATH="$LEAN4_BIN:$PATH"
export LEAN_NUM_THREADS=2
export RAYON_NUM_THREADS=2
export MATHLIB_NO_CACHE_ON_UPDATE=1
case "${1:-}" in
  '') DOWNLOAD='' ;;
  --download) DOWNLOAD='--download' ;;
  *) printf '%s\n' 'Usage: reproduce_followup.sh [--download]' >&2; exit 2 ;;
esac
mkdir -p evidence
python3 checkers/verify_release.py > evidence/integrity.log 2>&1
python3 checkers/bootstrap.py $DOWNLOAD > evidence/dependencies.log 2>&1
if [ -n "$DOWNLOAD" ]; then
  export MATHLIB_CACHE_DIR="${MATHLIB_CACHE_DIR:-$ROOT/tooling/mathlib-cache}"
  "$LEAN4_BIN/lake" exe cache --repo=leanprover-community/mathlib4 get \
    Mathlib.Analysis.SpecificLimits.Normed Mathlib.Analysis.SpecialFunctions.Pow.Real \
    Mathlib.Tactic.Linarith Mathlib.Tactic.Ring Mathlib.Tactic.FieldSimp Mathlib.Tactic.NormNum \
    > evidence/rebuild-cache.log 2>&1
fi
python3 checkers/rebuild_bounded.py > evidence/rebuild-proofs.log 2>&1
mkdir -p .lake/build/lib/lean/checkers
for CHECK in CheckTerminalAnchor CheckPenultimateRepair IndependentDepth4 ExpectedTerminalStatement Nonvacuity AxiomClosure; do
  "$LEAN4_BIN/lake" env lean -j2 -o ".lake/build/lib/lean/checkers/$CHECK.olean" "checkers/$CHECK.lean" > "evidence/$CHECK.log" 2>&1
done
"$LEAN4_BIN/lake" env lean -j2 audit/checkers/IndependentStatements.lean > evidence/IndependentStatements.log 2>&1
"$LEAN4_BIN/lake" env lean -j2 checkers/ExportHost.lean > evidence/ExportHost.log 2>&1
python3 checkers/check_host.py --exports evidence --fixtures fixtures/research --output evidence/host-comparison.json > evidence/host-comparison.log 2>&1
python3 audit/checkers/compare_hosts.py > evidence/independent-host.log 2>&1
python3 checkers/check_penultimate_repair.py > evidence/penultimate-physical.log 2>&1
python3 checkers/check_terminal_anchor.py > evidence/terminal-anchor-finite.log 2>&1
for MODULE in TerminalAnchorRepair TerminalAnchorCount PenultimateRepair Repairs; do
  "$LEAN4_BIN/lake" env "$LEAN4_BIN/leanchecker" -v "OrderedMatrixRemoval4.$MODULE" > "evidence/kernel-$MODULE.log" 2>&1
done
for CHECK in ExpectedTerminalStatement IndependentDepth4 Nonvacuity AxiomClosure; do
  "$LEAN4_BIN/lake" env "$LEAN4_BIN/leanchecker" -v "checkers.$CHECK" > "evidence/kernel-$CHECK.log" 2>&1
done
python3 checkers/verify_release.py > evidence/integrity-after.log 2>&1
printf '%s\n' 'Integrated source rebuild, quantified/literal statements, finite checks and new-module kernel replay passed.'
