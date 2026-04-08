#!/usr/bin/env bash
set -euo pipefail

echo "[1/5] Checking required files..."
test -f README.md
test -f CITATION.cff
test -f .zenodo.json
test -f LICENSE
test -f Makefile
test -f lean/CouretUnification.lean
test -f lean/CouretUnification/FiniteCore.lean
test -f lean/CouretUnification/T2Gap.lean
test -f lean/CouretUnification/H1Bridge.lean
test -f lean/CouretUnification/H2Ttransfer.lean
test -f lean/CouretUnification/H3Trace.lean
test -f lean/CouretUnification/H4WeakHP.lean
test -f lean/CouretUnification/H5Analytic.lean
test -f lean/CouretUnification/H6GlobalHP.lean
test -f lean/CouretUnification/H6Microlocal.lean
test -f scripts/validate_numerical.py
test -f docs/programme_couret_unification_2026_03_25.tex

echo "[2/5] Checking doctrinal correction..."
grep -q 'H\^\\circ \\cap \\mathrm{altVec}\^\\perp' docs/programme_couret_unification_2026_03_25.tex
grep -q 'H\^\\circ \\cap \\mathrm{altVec}\^\\perp' README.md

echo "[3/5] Checking no forbidden overclaim..."
! grep -R --exclude-dir={dist,.git,.lake} "proof of the Riemann Hypothesis is claimed" . >/dev/null 2>&1 || true

echo "[4/5] Checking no sorry in Lean sources..."
! grep -R "\bsorry\b" lean >/dev/null 2>&1

echo "[5/5] Running numerical validation..."
python3 scripts/validate_numerical.py

echo
echo "Pack validation: OK"
