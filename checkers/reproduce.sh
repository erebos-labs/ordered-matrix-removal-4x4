#!/bin/sh
# Release packaging wrapper; the frozen Lean proof files are unchanged.
set -eu
: "${LEAN4_BIN:?Set LEAN4_BIN to a verified official Lean 4.34.1 bin directory}"
ROOT=$(CDPATH= cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
export PATH="$LEAN4_BIN:$PATH"
export LEAN_NUM_THREADS=2
export RAYON_NUM_THREADS=2
export MATHLIB_NO_CACHE_ON_UPDATE=1
mkdir -p evidence
python3 checkers/verify_release.py
python3 checkers/bootstrap.py --download
export MATHLIB_CACHE_DIR="${MATHLIB_CACHE_DIR:-$ROOT/tooling/mathlib-cache}"
"$LEAN4_BIN/lake" exe cache --repo=leanprover-community/mathlib4 get \
  Mathlib.Analysis.SpecificLimits.Normed Mathlib.Analysis.SpecialFunctions.Pow.Real \
  Mathlib.Tactic.Linarith Mathlib.Tactic.Ring Mathlib.Tactic.FieldSimp Mathlib.Tactic.NormNum \
  > evidence/rebuild-cache.log 2>&1
python3 checkers/rebuild_bounded.py > evidence/rebuild-proofs.log 2>&1
printf '%s\n' 'All 36 frozen project modules and quantified statements rebuilt; inspect evidence/rebuild-proofs.log for axioms.'
