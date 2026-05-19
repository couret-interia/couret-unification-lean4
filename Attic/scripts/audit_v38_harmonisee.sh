#!/usr/bin/env bash
# ──────────────────────────────────────────────────────────────────────
#  audit_v38_harmonisee.sh
# ──────────────────────────────────────────────────────────────────────
#  Audit anti-glissement doctrinal pour le pack v38 harmonisée.
#
#  Étend le script v38 unifié avec les phases additionnelles imposées
#  par les nouvelles couches (DefectOperator30, Logic/Lock3/, FCI/).
#
#  Usage :
#      ./audit_v38_harmonisee.sh [<repo_root>]
#  Defaults to current working directory if no argument is given.
#
#  Exit code :
#      0 = doctrine respectée
#      1 = au moins une violation détectée
# ──────────────────────────────────────────────────────────────────────
set -euo pipefail

ROOT="${1:-.}"
LEAN_DIR="${ROOT}/CouretUnification"

if [[ ! -d "${LEAN_DIR}" ]]; then
  echo "[audit] ERROR: ${LEAN_DIR} not found" >&2
  exit 1
fi

echo "[v38h audit] starting global doctrine check"
echo "[v38h audit] anti-slippage: no abusive promotion to 'closed'"
echo "[v38h audit] doctrine: RHClaimed = false (invariant)"
echo

FAIL=0

check_forbidden() {
  local label="$1"
  local pattern="$2"
  echo "[v38h audit] ${label}"
  if grep -rEn "${pattern}" "${LEAN_DIR}" 2>/dev/null; then
    echo "[v38h audit] FAIL: ${label}"
    FAIL=1
  else
    echo "[v38h audit] PASS: ${label}"
  fi
  echo
}

# ──────────────────────────────────────────────────────────────────────
# Phases v38 unifiée (préservées)
# ──────────────────────────────────────────────────────────────────────

check_forbidden "phase 1: RHClaimed := true (forbidden)"            'RHClaimed[[:space:]]*:=[[:space:]]*true'
check_forbidden "phase 2: TraceFormulaOK := closed (forbidden)"      'TraceFormulaOK[[:space:]]*:.*\.closed|TraceFormulaOK[[:space:]]*:=[[:space:]]*BridgeStatus\.closed'
check_forbidden "phase 3: Det2XiBridgeOK := closed (forbidden)"      'Det2XiBridgeOK[[:space:]]*:.*\.closed|Det2XiBridgeOK[[:space:]]*:=[[:space:]]*BridgeStatus\.closed'
check_forbidden "phase 4: ZeroMatchingOK := closed (forbidden)"      'ZeroMatchingOK[[:space:]]*:.*\.closed|ZeroMatchingOK[[:space:]]*:=[[:space:]]*BridgeStatus\.closed'
check_forbidden "phase 5: CarlemanAtomicityOK := closed (forbidden)" 'CarlemanAtomicityOK[[:space:]]*:.*\.closed|CarlemanAtomicityOK[[:space:]]*:=[[:space:]]*BridgeStatus\.closed'
check_forbidden "phase 6: ResidualZeroOK := closed (forbidden)"      'ResidualZeroOK[[:space:]]*:.*\.closed|ResidualZeroOK[[:space:]]*:=[[:space:]]*BridgeStatus\.closed'
check_forbidden "phase 7: theorem ⊢ RHClaimed = true (forbidden)"    'theorem[[:space:]]+[^:]*:[[:space:]]*RHClaimed[[:space:]]*=[[:space:]]*true'

# ──────────────────────────────────────────────────────────────────────
# Phases additionnelles v38 harmonisée
# ──────────────────────────────────────────────────────────────────────

check_forbidden "phase 8: DefectOperator30Status := closed (forbidden)"   'DefectOperator30Status[[:space:]]*:.*\.closed|DefectOperator30Status[[:space:]]*:=[[:space:]]*BridgeStatus\.closed'
check_forbidden "phase 9: ProtectedMinusTraceOK := closed (forbidden)"    'ProtectedMinusTraceOK[[:space:]]*:.*\.closed|ProtectedMinusTraceOK[[:space:]]*:=[[:space:]]*BridgeStatus\.closed'

# Phase 10 : aucune redefinition de MeanBelow / SlopeBelow / EnergyBelow / GridNoiseVanishes
# en dehors de LocalDebiasing.lean (la vacuité explicite doit y rester centralisée tant
# qu'elle n'est pas levée).
echo "[v38h audit] phase 10: Lock3 predicates not redefined outside LocalDebiasing.lean"
LEAK=$(grep -rEln 'def[[:space:]]+(MeanBelow|SlopeBelow|EnergyBelow|GridNoiseVanishes)[[:space:]]' "${LEAN_DIR}" 2>/dev/null \
  | grep -v 'LocalDebiasing\.lean' || true)
if [[ -n "${LEAK}" ]]; then
  echo "${LEAK}"
  echo "[v38h audit] FAIL: Lock3 predicate leakage outside LocalDebiasing.lean"
  FAIL=1
else
  echo "[v38h audit] PASS: Lock3 predicates centralised"
fi
echo

# Phase 11 : aucun théorème dont la conclusion est PhantomMass19 → RHClaimed = true
check_forbidden "phase 11: PhantomMass19 → RHClaimed = true (forbidden)" 'PhantomMass19[^→]*→[^:]*RHClaimed[[:space:]]*=[[:space:]]*true'

# Phase 12 : aucun axiome introduit dans Logic/Lock3/ ni dans FCI/
echo "[v38h audit] phase 12: no 'axiom' declarations in Lock3/ or FCI/"
AXIOMS=$(grep -rEln '^[[:space:]]*axiom[[:space:]]' \
  "${LEAN_DIR}/Logic/Lock3" "${LEAN_DIR}/FCI" 2>/dev/null || true)
if [[ -n "${AXIOMS}" ]]; then
  echo "${AXIOMS}"
  echo "[v38h audit] FAIL: axiom declarations found"
  FAIL=1
else
  echo "[v38h audit] PASS: no axiom declarations"
fi
echo

# Phase 13 : Lock3Certified vacuity witness must remain present
echo "[v38h audit] phase 13: Lock3Certified_is_currently_vacuous must be present"
if grep -rEn 'Lock3Certified_is_currently_vacuous' "${LEAN_DIR}/Logic/Lock3" >/dev/null 2>&1; then
  echo "[v38h audit] PASS: vacuity witness present"
else
  echo "[v38h audit] FAIL: vacuity witness absent — vacuity must remain explicit"
  FAIL=1
fi
echo

# ──────────────────────────────────────────────────────────────────────
# Bilan
# ──────────────────────────────────────────────────────────────────────

if [[ ${FAIL} -eq 0 ]]; then
  echo "[v38h audit] PASS: anti-slippage doctrine preserved"
  exit 0
else
  echo "[v38h audit] FAIL: at least one phase reported a violation"
  exit 1
fi
