#!/usr/bin/env bash
#
# audit_v36_torsion.sh
# Torsion-specific audit for the v36 jurisdiction.
#
# Verifies:
#   - no `sorry`, no `axiom`, no `admit` in AnalyticHorizon/
#   - all torsion-related structures and obligations are present
#   - no torsion claim flag is flipped to `true`
#
# Usage : bash scripts/audit_v36_torsion.sh

set -euo pipefail

ROOT="lean/CouretUnification/AnalyticHorizon"

fail_if_found () {
  local pattern="$1"
  local label="$2"
  if grep -R "$pattern" "$ROOT" >/dev/null 2>&1; then
    echo "ERROR: found forbidden pattern: $label"
    grep -RnE "$pattern" "$ROOT" | head -3 | sed 's/^/      /'
    exit 1
  fi
}

require_found () {
  local pattern="$1"
  local label="$2"
  if ! grep -R "$pattern" "$ROOT" >/dev/null 2>&1; then
    echo "ERROR: missing required pattern: $label"
    exit 1
  fi
}

# ── Hygiene ────────────────────────────────────────────────────
fail_if_found "sorry" "sorry"
fail_if_found "axiom" "axiom"
fail_if_found "admit" "admit"

# ── v36.7 ArchimedeanTorsionCertificate ─────────────────────────
require_found "ArchimedeanTorsionCertificate"  "archimedean torsion certificate"
require_found "ArchimedeanTorsionData"          "torsion data"
require_found "nonlinear_gap"                   "nonlinear gap"
require_found "ArchimedeanTorsionMap"           "torsion map"
require_found "phi_growth"                      "polynomial growth obligation"
require_found "amp_bounded"                     "amplitude boundedness obligation"
require_found "boundary_log_growth"             "boundary logarithmic growth obligation"

# ── v36.8 TorsionAnalyticObligation ─────────────────────────────
require_found "TorsionAnalyticObligation"       "torsion analytic obligation"
require_found "StrictMono"                      "monotonicity obligation"
require_found "bi_lipschitz_lower"              "lower bi-Lipschitz obligation"
require_found "bi_lipschitz_upper"              "upper bi-Lipschitz obligation"
require_found "polynomial_growth"               "polynomial growth obligation (T.4)"

# ── No torsion claim flipped to true ────────────────────────────
fail_if_found "ArchimedeanTorsionClaimedClosed : Bool := true"   "torsion claimed closed"
fail_if_found "ExplicitFormulaClosedFromTorsion : Bool := true"  "explicit formula claimed from torsion"
fail_if_found "HilbertPolyaFromTorsion : Bool := true"           "Hilbert-Polya claimed from torsion"
fail_if_found "RHFromTorsion : Bool := true"                     "RH claimed from torsion"
fail_if_found "TorsionClassifiedAsNoise : Bool := true"          "torsion classified as noise"
fail_if_found "TorsionMovesZeros : Bool := true"                 "torsion moves zeros"
fail_if_found "TorsionChangesClockOnly : Bool := false"          "torsion clock-only doctrine broken"

# ── Pullback claims forbidden ────────────────────────────────────
fail_if_found "ZeroCountingPulledBackClaimedClosed : Bool := true"   "pullback counting claimed closed"
fail_if_found "RiemannVonMangoldtFromTorsionTransfer : Bool := true" "Riemann-von Mangoldt from transfer"
fail_if_found "ZeroSideClosedFromTorsionTransfer : Bool := true"     "ZeroSide closed from transfer"
fail_if_found "ExplicitFormulaClosedFromTorsionTransfer : Bool := true" "explicit formula closed from transfer"
fail_if_found "HilbertPolyaFromTorsionTransfer : Bool := true"       "Hilbert-Polya from transfer"
fail_if_found "RHFromTorsionTransfer : Bool := true"                 "RH from transfer"

echo "v36 torsion audit passed"
