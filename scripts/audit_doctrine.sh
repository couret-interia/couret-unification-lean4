#!/usr/bin/env bash
# ──────────────────────────────────────────────────────────────────────
#  audit_doctrine.sh (ancien audit_v38_harmonisee.sh)
# ──────────────────────────────────────────────────────────────────────
#  Audit anti-glissement doctrinal pour le pack v38 harmonisée.
#
#  Étend le script v38 unifié avec les phases additionnelles imposées
#  par les nouvelles couches (DefectOperator30, Logic/Lock3/, FCI/).
#
#  Usage :
#      ./audit_doctrine.sh [<repo_root>]
#  Defaults to current working directory if no argument is given.
#
#  Exit code :
#      0 = doctrine respectée
#      1 = au moins une violation détectée
# ──────────────────────────────────────────────────────────────────────
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

ROOT="${ROOT_DIR}/${1:-.}"
LEAN_DIR="${ROOT}/CouretUnification"

if [[ ! -d "${LEAN_DIR}" ]]; then
  echo "[audit] ERROR: ${LEAN_DIR} not found" >&2
  exit 1
fi

echo "╔═══════════════════════════════════════════════════════════════════════╗"
echo "║   AUDIT v38.4 anti-glissement doctrinal global — Couret-Unification   ║"
echo "╚═══════════════════════════════════════════════════════════════════════╝"
echo ""
echo "[v38 audit] starting global doctrine check in $LEAN_DIR"
echo "anti-slippage: no abusive promotion to 'closed'"
echo "doctrine: RHClaimed = false (invariant)"
echo

FAIL=0

check_forbidden() {
  local label="$1"
  local pattern="$2"
  if grep -rEn "${pattern}" "${LEAN_DIR}" 2>/dev/null; then
    echo "✗ ${label}"
    FAIL=1
  else
    echo "✓ ${label}"
  fi
}

# ──────────────────────────────────────────────────────────────────────
# Phases v38 unifiée (préservées)
# ──────────────────────────────────────────────────────────────────────

check_forbidden "[01/13] RHClaimed := true (forbidden)"             'RHClaimed[[:space:]]*:=[[:space:]]*true'
check_forbidden "[02/13] TraceFormulaOK := closed (forbidden)"      'TraceFormulaOK[[:space:]]*:.*\.closed|TraceFormulaOK[[:space:]]*:=[[:space:]]*BridgeStatus\.closed'
check_forbidden "[03/13] Det2XiBridgeOK := closed (forbidden)"      'Det2XiBridgeOK[[:space:]]*:.*\.closed|Det2XiBridgeOK[[:space:]]*:=[[:space:]]*BridgeStatus\.closed'
check_forbidden "[04/13] ZeroMatchingOK := closed (forbidden)"      'ZeroMatchingOK[[:space:]]*:.*\.closed|ZeroMatchingOK[[:space:]]*:=[[:space:]]*BridgeStatus\.closed'
check_forbidden "[05/13] CarlemanAtomicityOK := closed (forbidden)" 'CarlemanAtomicityOK[[:space:]]*:.*\.closed|CarlemanAtomicityOK[[:space:]]*:=[[:space:]]*BridgeStatus\.closed'
check_forbidden "[06/13] ResidualZeroOK := closed (forbidden)"      'ResidualZeroOK[[:space:]]*:.*\.closed|ResidualZeroOK[[:space:]]*:=[[:space:]]*BridgeStatus\.closed'
check_forbidden "[07/13] theorem ⊢ RHClaimed = true (forbidden)"    'theorem[[:space:]]+[^:]*:[[:space:]]*RHClaimed[[:space:]]*=[[:space:]]*true'

# ──────────────────────────────────────────────────────────────────────
# Phases additionnelles v38 harmonisée
# ──────────────────────────────────────────────────────────────────────

check_forbidden "[08/13] DefectOperator30Status := closed (forbidden)"   'DefectOperator30Status[[:space:]]*:.*\.closed|DefectOperator30Status[[:space:]]*:=[[:space:]]*BridgeStatus\.closed'
check_forbidden "[09/13] ProtectedMinusTraceOK := closed (forbidden)"    'ProtectedMinusTraceOK[[:space:]]*:.*\.closed|ProtectedMinusTraceOK[[:space:]]*:=[[:space:]]*BridgeStatus\.closed'

# Phase 10 : aucun théorème dont la conclusion est PhantomMass19 → RHClaimed = true
check_forbidden "[10/13] PhantomMass19 → RHClaimed = true (forbidden)"   'PhantomMass19[^→]*→[^:]*RHClaimed[[:space:]]*=[[:space:]]*true'

# Phase 11 : aucune redefinition de MeanBelow / SlopeBelow / EnergyBelow / GridNoiseVanishes
# en dehors de LocalDebiasing.lean (la vacuité explicite doit y rester centralisée tant
# qu'elle n'est pas levée).
LEAK=$(grep -rEln 'def[[:space:]]+(MeanBelow|SlopeBelow|EnergyBelow|GridNoiseVanishes)[[:space:]]' "${LEAN_DIR}" 2>/dev/null \
  | grep -v 'LocalDebiasing\.lean' || true)
if [[ -n "${LEAK}" ]]; then
  echo "${LEAK}"
  echo "✗ [11/13] Lock3 predicate leakage outside LocalDebiasing.lean"
  FAIL=1
else
  echo "✓ [11/13] Lock3 predicates centralised"
fi

# Phase 12 : aucun axiome introduit dans Logic/Lock3/ ni dans FCI/
AXIOMS=$(grep -rEln '^[[:space:]]*axiom[[:space:]]' \
  "${LEAN_DIR}/Logic/Lock3" "${LEAN_DIR}/FCI" 2>/dev/null || true)
if [[ -n "${AXIOMS}" ]]; then
  echo "${AXIOMS}"
  echo "✗ [12/13] axiom declarations found"
  FAIL=1
else
  echo "✓ [12/13] no axiom declarations"
fi

# Phase 13 : Lock3Certified vacuity witness must remain present
if grep -rEn 'Lock3Certified_is_currently_vacuous' "${LEAN_DIR}/Logic/Lock3" >/dev/null 2>&1; then
  echo "✓ [13/13] vacuity witness present"
else
  echo "✗ [13/13] vacuity witness absent — vacuity must remain explicit"
  FAIL=1
fi
echo

# ──────────────────────────────────────────────────────────────────────
# Bilan
# ──────────────────────────────────────────────────────────────────────
echo "────────────────────────────────────────────"
echo " Bilan"
echo "────────────────────────────────────────────"

if [[ ${FAIL} -eq 0 ]]; then
  echo "✓ anti-slippage doctrine preserved"
  EXIT_CODE=0
else
  echo "✗ at least one phase reported a violation"
  EXIT_CODE=1
fi
echo ""
echo "════════════════════════════════════════"
echo "  Fin Audit Doctrine v38.4 harmonisée"
echo "════════════════════════════════════════"

exit $EXIT_CODE
