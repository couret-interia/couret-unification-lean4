#!/usr/bin/env bash
# validate_pack.sh — Couret-Unification v35
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
check "test -f lakefile.lean" "lakefile.lean"
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

# ──── 3. Spectral ────
echo ""
echo "[3/5] Spectral files..."
check "test -f lean/CouretUnification/Spectral/FiniteCore.lean" "Spectral/FiniteCore"
check "test -f lean/CouretUnification/Spectral/T2Gap.lean" "Spectral/T2Gap"

# ──── 4. Invariants ────
echo ""
echo "[4/5] Epistemic invariants..."

# (a) Compteur des sorries doctrinaux (2 attendus : Lemma7, RouteC)
EXPECTED_SORRIES=2
SORRY_COUNT=$(lake build 2>&1 | grep -cF 'declaration uses `sorry`' || true)
check "[ \"$SORRY_COUNT\" -eq \"$EXPECTED_SORRIES\" ]" \
  "Exactly $EXPECTED_SORRIES doctrinal sorries (Lemma7Residual:6, RouteC:765, found: $SORRY_COUNT)"

# (b) Garde épistémique : RHClaimed = false déclaré dans le README
check "grep -qF 'RHClaimed = false' README.md" \
  "RHClaimed = false declared in README"

# (c) Garde épistémique globale : aucun fichier ne revendique RHClaimed = true
FAIL_BEFORE_RHCLAIMED=$FAIL
RHCLAIMED_TRUE_MATCHES=""

check "! grep -rqF 'RHClaimed = true' \
       --include='*.lean' --include='*.md' --include='*.py' \
       lean/ docs/ python/ scripts/ README.md 2>/dev/null" \
  "RHClaimed = true absent from entire repo"

if [ "$FAIL_BEFORE_RHCLAIMED" -lt "$FAIL" ]; then
  RHCLAIMED_TRUE_MATCHES=$(
    grep -rnF 'RHClaimed = true' \
      --include='*.lean' --include='*.md' --include='*.py' \
      lean/ docs/ python/ scripts/ README.md 2>/dev/null || true
  )
fi

# ──── 5. Scripts ────
echo ""
echo "[5/5] Scripts..."
check "test -f pari/test_veff.gp" "pari/test_veff.gp"
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
  # Affiche le(s) fichier(s) RHClaimed = true en cause
  if [ "$RHCLAIMED_TRUE_MATCHES" ]; then
    echo ""
    echo "══ 'RHClaimed = true' files ══"
    echo "$RHCLAIMED_TRUE_MATCHES"
    echo ""
  fi
  exit 1
fi
