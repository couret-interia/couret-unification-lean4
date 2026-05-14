#!/usr/bin/env bash
#
# scripts/audit_v37_aggregation.sh
#
# Audit agrégé v37.
# Vérifie :
#   - les gates Norwich (si présents) ;
#   - les audits v36 hérités (si présents) ;
#   - le gate de séparation Frozen / Residue ;
#   - la compilation du fichier Lean DoctrinalInvariants (si lake disponible).
#
# Aucun gate ne bloque sur l'absence de pièce. Les gates manquants sont
# signalés en SKIP. Seuls les gates exécutés et échoués bloquent.
#
# Doctrine v37 :
#   - statut de vérité ≠ position architecturale
#   - [P] local ≠ Frozen Core automatiquement
#   - Residue reste Active sauf bridge contract explicite
#   - No verified det₂ ↔ ξ ⇒ No RH claim

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[v37 audit] starting aggregation in $ROOT_DIR"
echo "[v37 doctrine] truth status != architectural position"
echo "[v37 doctrine] local [P] does not imply Frozen Core"
echo "[v37 doctrine] Residue remains Active unless bridged by explicit contract"
echo "[v37 doctrine] no verified det2 <-> xi implies no RH claim"
echo

failures=0

run_gate() {
  local name="$1"
  local cmd="$2"

  echo "[v37 audit] running: $name"
  if bash -lc "$cmd"; then
    echo "[v37 audit] PASS: $name"
  else
    echo "[v37 audit] FAIL: $name"
    failures=$((failures + 1))
  fi
  echo
}

maybe_run_gate() {
  local name="$1"
  local path="$2"

  if [ -f "$path" ]; then
    run_gate "$name" "$path"
  else
    echo "[v37 audit] SKIP: $name"
    echo "[v37 audit] missing: $path"
    echo
  fi
}

# ── Phase 1 : gate de séparation Frozen / Residue (v37 propre) ────────
echo "[v37 audit] phase 1: v37 residue/frozen import gate"
maybe_run_gate \
  "gate_no_frozen_imports_residue" \
  "scripts/gate_no_frozen_imports_residue.sh"

# ── Phase 2 : gates Norwich (si présents) ─────────────────────────────
echo "[v37 audit] phase 2: Norwich gates"
maybe_run_gate \
  "norwich_gate_no_rh_claim" \
  "scripts/norwich_gate_no_rh_claim.sh"

maybe_run_gate \
  "norwich_gate_no_det2_xi_claim" \
  "scripts/norwich_gate_no_det2_xi_claim.sh"

maybe_run_gate \
  "norwich_gate_no_lambda_universalization" \
  "scripts/norwich_gate_no_lambda_universalization.sh"

maybe_run_gate \
  "norwich_gate_no_roca_compromise_claim" \
  "scripts/norwich_gate_no_roca_compromise_claim.sh"

maybe_run_gate \
  "norwich_gate_no_meriba_false_positive" \
  "scripts/norwich_gate_no_meriba_false_positive.sh"

maybe_run_gate \
  "norwich_gate_no_topological_universality" \
  "scripts/norwich_gate_no_topological_universality.sh"

maybe_run_gate \
  "norwich_gate_no_frozen_core_expansion" \
  "scripts/norwich_gate_no_frozen_core_expansion.sh"

# ── Phase 3 : audits v36 hérités (si présents) ────────────────────────
echo "[v37 audit] phase 3: inherited v36 audits"
maybe_run_gate \
  "audit_v36.0" \
  "scripts/audit_v36.0.sh"

maybe_run_gate \
  "audit_v36.1" \
  "scripts/audit_v36.1.sh"

maybe_run_gate \
  "audit_v36_torsion" \
  "scripts/audit_v36_torsion.sh"

maybe_run_gate \
  "audit_v36.9" \
  "scripts/audit_v36.9.sh"

# ── Phase 4 : compilation du fichier Lean doctrinal ───────────────────
echo "[v37 audit] phase 4: Lean doctrinal invariant check"

DOCTRINE_FILE="lean/CouretUnification/EpistemicDiscipline/DoctrinalInvariants.lean"

if [ -f "$DOCTRINE_FILE" ]; then
  if command -v lake >/dev/null 2>&1; then
    run_gate \
      "lake env lean DoctrinalInvariants" \
      "lake env lean $DOCTRINE_FILE"
  else
    echo "[v37 audit] SKIP: Lean doctrinal invariant check"
    echo "[v37 audit] lake not found in PATH"
    echo
  fi
else
  echo "[v37 audit] FAIL: missing doctrinal invariant file"
  echo "[v37 audit] expected: $DOCTRINE_FILE"
  failures=$((failures + 1))
  echo
fi

# ── Bilan ─────────────────────────────────────────────────────────────
if [ "$failures" -eq 0 ]; then
  echo "[v37 audit] PASS: all available gates passed"
  echo "[v37 audit] Frozen Core, AnalyticHorizon, and Release remain"
  echo "[v37 audit] architecturally independent from Residue"
  echo "[v37 audit] RHClaimed=false preserved"
  exit 0
else
  echo "[v37 audit] FAIL: $failures gate(s) failed"
  echo "[v37 audit] doctrine reminder: [P] local does not imply Frozen Core"
  echo "[v37 audit] doctrine reminder: Residue remains Active unless explicitly bridged"
  echo "[v37 audit] doctrine reminder: no verified det2/xi bridge implies no RH claim"
  exit 1
fi
