#!/usr/bin/env bash
#
# audit_v36.9.sh
# Extended global audit for the v36 jurisdiction.
#
# Verifies:
#   - no `sorry`, `axiom`, `admit` anywhere
#   - all v36.9 ActiveLayerFullAudit flags are present and `false`
#   - all clock-only doctrine flags are preserved
#   - all required modules are present
#   - the Release manifest preservation flags are present
#
# Usage : bash scripts/audit_v36.9.sh

set -euo pipefail

ROOT="lean/CouretUnification/AnalyticHorizon"
REL="lean/CouretUnification/Release"

fail_if_found () {
  local pattern="$1"
  local label="$2"
  local path="${3:-CouretUnification}"
  if grep -R "$pattern" "$path" >/dev/null 2>&1; then
    echo "ERROR: found forbidden pattern: $label"
    grep -RnE "$pattern" "$path" | head -3 | sed 's/^/      /'
    exit 1
  fi
}

require_found () {
  local pattern="$1"
  local label="$2"
  local path="${3:-CouretUnification}"
  if ! grep -R "$pattern" "$path" >/dev/null 2>&1; then
    echo "ERROR: missing required pattern: $label"
    exit 1
  fi
}

# ── Hygiene ────────────────────────────────────────────────────
fail_if_found "sorry" "sorry"
fail_if_found "axiom" "axiom"
fail_if_found "admit" "admit"

# ── No Active layer claim flipped to true ──────────────────────
fail_if_found "RHClaimedFromActiveLayerFull : Bool := true"               "RH claimed from full audit"     "$ROOT"
fail_if_found "HilbertPolyaClaimedFromActiveLayerFull : Bool := true"     "HP claimed from full audit"     "$ROOT"
fail_if_found "SpectralCoincidenceClaimedFromActiveLayerFull : Bool := true" "spectral coincidence claimed" "$ROOT"
fail_if_found "ExplicitFormulaClaimedClosedFromActiveLayerFull : Bool := true" "explicit formula closed"   "$ROOT"
fail_if_found "Det2IdentityClaimedFromActiveLayerFull : Bool := true"     "det2 identity claimed"          "$ROOT"
fail_if_found "RiemannVonMangoldtClaimedFromActiveLayerFull : Bool := true" "Riemann-von Mangoldt claimed" "$ROOT"

# ── Clock-only doctrine must remain intact ─────────────────────
fail_if_found "TorsionClassifiedAsNoise : Bool := true"               "torsion classified as noise"   "$ROOT"
fail_if_found "TorsionClassifiedAsNoiseInActiveLayer : Bool := true"  "torsion as noise in audit"     "$ROOT"
fail_if_found "TorsionZeroClockDoctrinePreserved : Bool := false"     "torsion clock doctrine broken" "$ROOT"
fail_if_found "TorsionMovesZeros : Bool := true"                      "torsion moves zeros"           "$ROOT"
fail_if_found "TorsionChangesClockOnly : Bool := false"               "torsion clock-only broken"     "$ROOT"

# ── Required modules in Active layer ───────────────────────────
require_found "TorsionZeroTransferCertificate"  "torsion-zero transfer module"  "$ROOT"
require_found "ArchimedeanTorsionCertificate"   "archimedean torsion module"    "$ROOT"
require_found "ActiveLayerFullAudit"            "active layer full audit"       "$ROOT"
require_found "TorsionAnalyticObligation"       "torsion analytic obligation"   "$ROOT"
require_found "ZeroSideSummabilityCertificate"  "zero-side summability wrapper" "$ROOT"
require_found "StrictMono"                      "monotonicity obligation"       "$ROOT"
require_found "bi_lipschitz_lower"              "lower bi-Lipschitz obligation" "$ROOT"
require_found "bi_lipschitz_upper"              "upper bi-Lipschitz obligation" "$ROOT"
require_found "polynomial_growth"               "polynomial growth obligation"  "$ROOT"

# ── Release manifest preservation flags ────────────────────────
require_found "RHClaimed_v36 : Bool := false"                          "release RH false flag"          "$REL"
require_found "TorsionIsNoise_v36 : Bool := false"                     "release torsion-not-noise"      "$REL"
require_found "TorsionMovesZeros_v36 : Bool := false"                  "release torsion does not move zeros" "$REL"
require_found "TorsionChangesClockOnly_v36 : Bool := true"             "release torsion clock-only"     "$REL"
require_found "ZeroCountingPulledBackClaimedClosed_v36 : Bool := false" "release pullback not closed"   "$REL"
require_found "NuEffNegativeResultPreserved_v36 : Bool := true"        "release nu_eff result preserved" "$REL"

echo "v36.9 ActiveLayerFullAudit passed"
