#!/usr/bin/env bash
#
# audit_v36.0.sh
# Base hygiene audit for the v36 jurisdiction.
#
# Verifies:
#   - no `sorry`, no `axiom`, no `admit` anywhere in CouretUnification/
#   - all v36 doctrinal flags (RHClaimed_v36 etc.) are present and `false`
#
# Usage : bash scripts/audit_v36.0.sh

set -euo pipefail

ROOT="lean/CouretUnification"

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

# ── Required doctrinal flags (Release manifest) ─────────────────
require_found "RHClaimed_v36 : Bool := false"                "RH false flag"
require_found "HilbertPolyaClaimed_v36 : Bool := false"      "Hilbert-Polya false flag"
require_found "SpectralCoincidenceClaimed_v36 : Bool := false" "spectral coincidence false flag"
require_found "ExplicitFormulaClosed_v36 : Bool := false"    "explicit formula false flag"
require_found "Det2IdentityClaimed_v36 : Bool := false"      "det2 false flag"
require_found "RiemannVonMangoldtClaimed_v36 : Bool := false" "Riemann-von Mangoldt false flag"
require_found "CandidateCClaimed_v36 : Bool := false"        "Candidate C false flag"
require_found "MotherTheoremClaimed_v36 : Bool := false"     "Mother theorem false flag"

# ── Required preservation flags ─────────────────────────────────
require_found "v36_is_proof_jurisdiction : Bool := true"     "proof jurisdiction true flag"
require_found "FrozenActiveSeparation_v36 : Bool := true"    "Frozen-Active separation flag"
require_found "PrimeSideClosureAvailable_v36 : Bool := true" "PrimeSide closure flag"
require_found "AnalyticDebtsRemain_v36 : Bool := true"       "analytic debts remain flag"

echo "v36.0 base audit passed"
