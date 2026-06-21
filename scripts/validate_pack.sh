#!/usr/bin/env bash
# validate_pack.sh — Couret-Unification v38.5.12
# Validates the Lean pack structure and invariants.
set -euo pipefail

PASS=0
FAIL=0

check() {
  if eval "$1" >/dev/null 2>&1; then
    echo -e "  ✓ $2"
    PASS=$((PASS + 1))
  else
    echo -e "  ✗ $2"
    FAIL=$((FAIL + 1))
  fi
}

echo "═════════════════════════════════════════════════"
echo "  Couret-Unification — Pack Validation v38.5.12"
echo "═════════════════════════════════════════════════"

# ──── 1. Structure ────
echo ""
echo "[1/5] Fichiers Requis..."
check "test -f README.md" "README.md"
check "test -f LICENSE" "LICENSE"
check "test -f CITATION.cff" "CITATION.cff"
check "test -f lakefile.lean" "lakefile.lean"
check "test -f lean/CouretUnification.lean" "Root import file"

# ──── 2. Core facades / pivots (v38 structure) ────
echo ""
echo "[2/5] Fichiers Lean Core facades / pivots..."
check "test -f lean/CouretUnification.lean" "root package facade"
check "test -f lean/CouretUnification/All.lean" "All aggregator"
check "test -f lean/CouretUnification/Frozen.lean" "Frozen strict facade"
check "test -f lean/CouretUnification/Active.lean" "Active working facade"
# Noyau fini exact / Core (portent l’ossature)
# - FiniteCore → façade doctrinale du noyau fini
# - U30 → unités mod 30
# - CenteredSpace30 → espace centré
# - Convolution30 → opérateur fini
# - Characters30 / Characters30Bridge → couche spectrale/caractères
# - Arithmetic → pont arithmétique commun
check "test -f lean/CouretUnification/Core/FiniteCore.lean" "Core/FiniteCore facade"
check "test -f lean/CouretUnification/Core/U30.lean" "Core/U30"
check "test -f lean/CouretUnification/Core/Mod30.lean" "Core/Mod30"
check "test -f lean/CouretUnification/Core/UnitsBridge.lean" "Core/UnitsBridge"
check "test -f lean/CouretUnification/Core/CenteredSpace30.lean" "Core/CenteredSpace30"
check "test -f lean/CouretUnification/Core/Convolution30.lean" "Core/Convolution30"
check "test -f lean/CouretUnification/Core/Characters30.lean" "Core/Characters30"
check "test -f lean/CouretUnification/Core/Characters30Bridge.lean" "Core/Characters30Bridge"
check "test -f lean/CouretUnification/Core/Arithmetic.lean" "Core/Arithmetic"

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
check "test -f lean/CouretUnification/Core/QuadraticResonance.lean" "Core/QuadraticResonance"

# Couche Finite / FiniteDefect
check "test -f lean/CouretUnification/Finite/Foundations.lean" "Finite/Foundations"
check "test -f lean/CouretUnification/FiniteDefect/T1_to_T7.lean" "FiniteDefect/T1_to_T7"
# Logic / H3 — pivots actifs
check "test -f lean/CouretUnification/Logic/H3/PhaseBComposition.lean" "Logic/H3/PhaseBComposition"
check "test -f lean/CouretUnification/Logic/H3/RouteC.lean" "Logic/H3/RouteC"
check "test -f lean/CouretUnification/Logic/H3/Lemma7Residual.lean" "Logic/H3/Lemma7Residual"
check "test -f lean/CouretUnification/Logic/H3/SpectralBridge.lean" "Logic/H3/SpectralBridge"
# Analytic / AnalyticHorizon
check "test -f lean/CouretUnification/Logic/OpenLocks.lean" "Logic/OpenLocks"
check "test -f lean/CouretUnification/AnalyticHorizon/Det2Transport.lean" "AnalyticHorizon/Det2Transport"
# ResGold v38.5
check "test -f lean/CouretUnification/ResGold.lean" "ResGold facade"
check "test -f lean/CouretUnification/ResGold/L0_LocalLemma.lean" "ResGold/L0"
check "test -f lean/CouretUnification/ResGold/L1_ConductorOne.lean" "ResGold/L1"
check "test -f lean/CouretUnification/ResGold/L2_MertensAsymptotic.lean" "ResGold/L2"

# ──── 3. Spectral ────
echo ""
echo "[3/5] Spectral (fichiers)..."
check "test -f lean/CouretUnification/Spectral/FiniteCore.lean" "Spectral/FiniteCore"
check "test -f lean/CouretUnification/Spectral/T2Gap.lean" "Spectral/T2Gap"

# ──── 4. Invariants ────
echo ""
echo "[4/5] Invariants épistemiques..."

# (a) Compteur des sorries doctrinaux (10 attendus)
EXPECTED_SORRIES=10
SORRIES="
    Attendu :
    - Logic :
      - L6RatioEstimateDerived:66          [ANALYTIC ASSEMBLY]
      - L10NoGoTheorem:63:206              [1 CONCEPTUEL + 1 UPSTREAM]
    - Logic.H3 :
      - Lemma7Residual:6                   [L7 / RÉSIDU SUR LIGNE CRITIQUE]
      - RouteC:765                         [LOCK 3 / EXISTENCE OPÉRATEUR]
    - AnalyticHorizon :
      - Det2Transport:64                   [INSTANCIATION]
    - Analytic :
      - GammaFactor:62:80:93:109           [PONT ARCHIMÉDIEN / GAMMA]
"
SORRY_COUNT=$(lake build 2>&1 | grep -cF 'declaration uses `sorry`' || true)
check "[ \"$SORRY_COUNT\" -eq \"$EXPECTED_SORRIES\" ]" \
  "Exactement $EXPECTED_SORRIES sorry doctrinaux, trouvé: $SORRY_COUNT $SORRIES"

FROZEN_SORRIES=$(lake build CouretUnification.Frozen 2>&1 | grep -cF 'declaration uses `sorry`' || true)
ACTIVE_SORRIES=$(lake build CouretUnification.Active 2>&1 | grep -cF 'declaration uses `sorry`' || true)
check "[ \"$FROZEN_SORRIES\" -eq 0 ]" "FROZEN strictement pur (0 sorry)"
check "[ \"$ACTIVE_SORRIES\" -eq \"$EXPECTED_SORRIES\" ]" "ACTIVE comptable ($EXPECTED_SORRIES sorries documentés)"

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

check "test -f scripts/validate_pack.sh" "scripts/validate_pack.sh"
check "test -f scripts/sorry_audit.sh" "scripts/sorry_audit.sh"
check "test -f scripts/audit_structure_collisions.sh" "scripts/audit_structure_collisions.sh"
check "test -f scripts/audit_doctrine.sh" "scripts/audit_doctrine.sh"
check "test -f scripts/check_frozen_invariants.sh" "scripts/check_frozen_invariants.sh"
check "test -f scripts/run_all_tests.sh" "scripts/run_all_tests.sh"
check "test -f scripts/audit_orphans.sh" "scripts/audit_orphans.sh"
check "test -f scripts/audit_reachability.sh" "scripts/audit_reachability.sh"
check "test -f scripts/lib/lean_strip_comments.awk" "scripts/lib/lean_strip_comments.awk"

# ──── Summary ────
echo ""
echo "═══════════════════════════════════════════"
TOTAL=$((PASS + FAIL))
echo "  Résultats : $PASS/$TOTAL passés"
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
