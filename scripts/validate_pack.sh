#!/usr/bin/env bash
# validate_pack.sh — Couret-Unification v32
# Validates the Lean pack structure and invariants.
set -euo pipefail

PASS=0
FAIL=0

check() {
  if eval "$1" >/dev/null 2>&1; then
    echo "  ✓ $2"
    PASS=$((PASS + 1))
  else
    echo "  ✗ $2"
    FAIL=$((FAIL + 1))
  fi
}

echo "═══════════════════════════════════════════"
echo "  Couret-Unification — Pack Validation"
echo "═══════════════════════════════════════════"

# ──── 1. Structure ────
echo ""
echo "[1/5] Required files..."
check "test -f README.md" "README.md"
check "test -f LICENSE" "LICENSE"
check "test -f CITATION.cff" "CITATION.cff"
check "test -f lakefile.toml" "lakefile."
check "test -f lean/CouretUnification.lean" "Root import file"

# ──── 2. Core files (v32 structure) ────
echo ""
echo "[2/5] Core Lean files..."
check "test -f lean/CouretUnification/Core/Mod30.lean" "Core/Mod30"
check "test -f lean/CouretUnification/Core/Characters30.lean" "Core/Characters30"
check "test -f lean/CouretUnification/Core/CayleySpectrum.lean" "Core/CayleySpectrum"
check "test -f lean/CouretUnification/Core/Classification63.lean" "Core/Classification63"
check "test -f lean/CouretUnification/Core/CenteredEigenspace.lean" "Core/CenteredEigenspace"
check "test -f lean/CouretUnification/Core/ParsevalL5.lean" "Core/ParsevalL5"
check "test -f lean/CouretUnification/Core/FormuleLk.lean" "Core/FormuleLk"
check "test -f lean/CouretUnification/Core/Kurtosis.lean" "Core/Kurtosis"
check "test -f lean/CouretUnification/Core/Lambda.lean" "Core/Lambda"
check "test -f lean/CouretUnification/Core/TCAutoInverse.lean" "Core/TCAutoInverse"
check "test -f lean/CouretUnification/Core/CayleyConnected.lean" "Core/CayleyConnected"
check "test -f lean/CouretUnification/Core/ComponentSpectrum.lean" "Core/ComponentSpectrum"
check "test -f lean/CouretUnification/Core/OddDimComplexObstruction.lean" "Core/OddDimComplexObstruction"
check "test -f lean/CouretUnification/Core/DefectProjection.lean" "Core/DefectProjection"
check "test -f lean/CouretUnification/Core/CharPoly.lean" "Core/CharPoly"
check "test -f lean/CouretUnification/Core/MultiplicityUniqueness.lean" "Core/MultiplicityUniqueness"
check "test -f lean/CouretUnification/Core/TraceRecurrence.lean" "Core/TraceRecurrence"
check "test -f lean/CouretUnification/Core/MersenneMod30.lean" "Core/MersenneMod30"
check "test -f lean/CouretUnification/Core/CarlemanUniqueness.lean" "Core/CarlemanUniqueness"
check "test -f lean/CouretUnification/Core/Classification63Detail.lean" "Core/Classification63Detail"

# ──── 3. Spectral/Tower files ────
echo ""
echo "[3/5] Spectral and Tower files..."
check "test -f lean/CouretUnification/Spectral/FiniteCore.lean" "Spectral/FiniteCore"
check "test -f lean/CouretUnification/Spectral/T2Gap.lean" "Spectral/T2Gap"
check "test -f lean/CouretUnification/Spectral/H1Bridge.lean" "Spectral/H1Bridge"
check "test -f lean/CouretUnification/Spectral/H3Trace.lean" "Spectral/H3Trace"
check "test -f lean/CouretUnification/Tower/PrimorialCharacterTower.lean" "Tower/PrimorialCharacterTower"
check "test -f lean/CouretUnification/Tower/ConcreteKernel210.lean" "Tower/ConcreteKernel210"

# ──── 4. Invariants ────
echo ""
echo "[4/5] Epistemic invariants..."
check "! (lake build 2>&1 | grep -F 'declaration uses \`sorry\`')" "No real sorry in Lean declarations"
check "grep -q 'RHClaimed' README.md" "RHClaimed mentioned in README"

# ──── 5. Scripts ────
echo ""
echo "[5/5] Scripts..."
check "test -f scripts/test_veff.gp" "scripts/test_veff.gp"
check "test -f scripts/channel_bridge_v3.py" "scripts/channel_bridge_v3.py"
check "test -f scripts/evidence_veff.py" "scripts/evidence_veff.py"
check "test -f scripts/compute_moments.py" "scripts/compute_moments.py"

# ──── Summary ────
echo ""
echo "═══════════════════════════════════════════"
TOTAL=$((PASS + FAIL))
echo "  Results: $PASS/$TOTAL passed"
if [ "$FAIL" -eq 0 ]; then
  echo "  Pack validation: ✓ OK"
  exit 0
else
  echo "  Pack validation: ✗ $FAIL FAILURES"
  exit 1
fi
