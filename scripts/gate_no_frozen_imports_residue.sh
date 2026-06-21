#!/usr/bin/env bash
#
# scripts/gate_no_frozen_imports_residue.sh
#
# Vérifie que la couche Residue/ n'est jamais importée par :
#   - le Frozen Core hérité de v36 (Logic/ExplicitFormula/*),
#   - la couche AnalyticHorizon/* (sauf bridge contract explicite via
#     Residue/Bridge/*),
#   - la couche Release/* (ne doit pas conditionner les drapeaux
#     doctrinaux sur des résultats Active).
#
# Application du principe central v37 :
#   Residue/* contient des résultats [P] locaux qui ne sont PAS
#   nécessaires à la juridiction globale. Aucune dépendance ascendante
#   n'est autorisée sans contrat explicite.
#
# Usage : bash scripts/gate_no_frozen_imports_residue.sh
# Exit 0 si la séparation est respectée, exit 1 sinon.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[gate residue] checking forbidden imports"
echo "[gate residue] doctrine: truth status != architectural position"
echo "[gate residue] doctrine: local [P] does not imply Frozen Core"
echo "[gate residue] doctrine: Residue remains Active unless bridged"

failures=0

# Préfixe de scan : on regarde dans lean/CouretUnification/
SCAN_ROOT="lean/CouretUnification"

check_forbidden_imports() {
  local scope="$1"
  local pattern="$2"
  local allow_bridge="$3"

  if [ ! -d "$scope" ]; then
    echo "[gate residue] skip missing scope: $scope"
    return 0
  fi

  while IFS= read -r file; do
    if grep -Eq "$pattern" "$file"; then
      if [ "$allow_bridge" = "yes" ] && \
         grep -Eq '^import .*Residue\.Bridge\.' "$file"; then
        continue
      fi

      echo "[gate residue] forbidden import in $file"
      echo "[gate residue] matched pattern: $pattern"
      failures=$((failures + 1))
    fi
  done < <(find "$scope" -type f -name "*.lean" | sort)
}

# ── Garde 1 : Frozen Core ne doit jamais importer Residue ────────────
check_forbidden_imports \
  "$SCAN_ROOT/Logic/ExplicitFormula" \
  '^import .*Residue\.' \
  "no"

# ── Garde 2 : AnalyticHorizon ne doit pas importer Residue ───────────
# Exception : modules explicitement nommés Residue/Bridge/*
check_forbidden_imports \
  "$SCAN_ROOT/AnalyticHorizon" \
  '^import .*Residue\.' \
  "yes"

# ── Garde 3 : Release ne doit pas dépendre de Residue ────────────────
check_forbidden_imports \
  "$SCAN_ROOT/Release" \
  '^import .*Residue\.' \
  "no"

# ── Bilan ────────────────────────────────────────────────────────────
if [ "$failures" -eq 0 ]; then
  echo "[gate residue] PASS"
  echo "[gate residue] Frozen Core, AnalyticHorizon, and Release remain"
  echo "[gate residue] architecturally independent from the Residue layer"
  exit 0
else
  echo "[gate residue] FAIL: $failures forbidden import(s)"
  echo "[gate residue] doctrine reminder: [P] local does not imply Frozen Core"
  echo "[gate residue] doctrine reminder: use Residue/Bridge/<Contract>.lean"
  echo "[gate residue] for explicit future promotion"
  exit 1
fi
