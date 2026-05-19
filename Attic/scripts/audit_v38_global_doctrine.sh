#!/usr/bin/env bash
#
# scripts/audit_v38_global_doctrine.sh
#
# Audit anti-glissement v38.
# Vérifie qu'aucune étiquette doctrinale critique n'a été promue
# vers un statut fermé sans démonstration explicite.
#
# Doctrine v38 (anti-glissement) :
#   - RHClaimed doit rester à `false`
#   - TraceFormulaOK doit rester `theoremTarget` (jamais `closed`)
#   - Det2XiBridgeOK doit rester `theoremTarget`
#   - ZeroMatchingOK doit rester `theoremTarget`
#   - CarlemanAtomicityOK doit rester `theoremTarget`
#   - ResidualZeroOK doit rester `theoremTarget`
#
# Tant que le pont analytique n'est pas démontré, ces statuts ne
# doivent JAMAIS être promus à `closed`.
#
# Ce script échoue si une promotion abusive est détectée.
# Il transforme la prudence en invariant de dépôt.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[v38 audit] starting global doctrine check in $ROOT_DIR"
echo "[v38 audit] anti-slippage: no abusive promotion to 'closed'"
echo "[v38 audit] doctrine: RHClaimed = false (invariant)"
echo

failures=0

# ── Périmètre de scan : tout sauf Frozen Core hérité ─────────────
SCAN_ROOT="lean/CouretUnification"

if [ ! -d "$SCAN_ROOT" ]; then
  echo "[v38 audit] SKIP: $SCAN_ROOT not found"
  echo "[v38 audit] expected lean/ structure absent"
  exit 0
fi

# ── Garde 1 : RHClaimed := true ──────────────────────────────────
echo "[v38 audit] phase 1: RHClaimed := true (forbidden)"
RH_HITS=$(grep -rEn 'def RHClaimed\s*:\s*Bool\s*:=\s*true' "$SCAN_ROOT" 2>/dev/null || true)
if [ -n "$RH_HITS" ]; then
  echo "[v38 audit] FAIL: RHClaimed promoted to true"
  echo "$RH_HITS"
  failures=$((failures + 1))
else
  echo "[v38 audit] PASS: no RHClaimed := true"
fi
echo

# ── Garde 2 : TraceFormulaOK := closed ───────────────────────────
echo "[v38 audit] phase 2: TraceFormulaOK := closed (forbidden)"
TF_HITS=$(grep -rEn 'def TraceFormulaOK\s*:\s*BridgeStatus\s*:=\s*BridgeStatus\.closed' "$SCAN_ROOT" 2>/dev/null || true)
if [ -n "$TF_HITS" ]; then
  echo "[v38 audit] FAIL: TraceFormulaOK promoted to closed"
  echo "$TF_HITS"
  failures=$((failures + 1))
else
  echo "[v38 audit] PASS: TraceFormulaOK not closed"
fi
echo

# ── Garde 3 : Det2XiBridgeOK := closed ───────────────────────────
echo "[v38 audit] phase 3: Det2XiBridgeOK := closed (forbidden)"
D2_HITS=$(grep -rEn 'def Det2XiBridgeOK\s*:\s*BridgeStatus\s*:=\s*BridgeStatus\.closed' "$SCAN_ROOT" 2>/dev/null || true)
if [ -n "$D2_HITS" ]; then
  echo "[v38 audit] FAIL: Det2XiBridgeOK promoted to closed"
  echo "$D2_HITS"
  failures=$((failures + 1))
else
  echo "[v38 audit] PASS: Det2XiBridgeOK not closed"
fi
echo

# ── Garde 4 : ZeroMatchingOK := closed ───────────────────────────
echo "[v38 audit] phase 4: ZeroMatchingOK := closed (forbidden)"
ZM_HITS=$(grep -rEn 'def ZeroMatchingOK\s*:\s*BridgeStatus\s*:=\s*BridgeStatus\.closed' "$SCAN_ROOT" 2>/dev/null || true)
if [ -n "$ZM_HITS" ]; then
  echo "[v38 audit] FAIL: ZeroMatchingOK promoted to closed"
  echo "$ZM_HITS"
  failures=$((failures + 1))
else
  echo "[v38 audit] PASS: ZeroMatchingOK not closed"
fi
echo

# ── Garde 5 : CarlemanAtomicityOK := closed ──────────────────────
echo "[v38 audit] phase 5: CarlemanAtomicityOK := closed (forbidden)"
CA_HITS=$(grep -rEn 'def CarlemanAtomicityOK\s*:\s*BridgeStatus\s*:=\s*BridgeStatus\.closed' "$SCAN_ROOT" 2>/dev/null || true)
if [ -n "$CA_HITS" ]; then
  echo "[v38 audit] FAIL: CarlemanAtomicityOK promoted to closed"
  echo "$CA_HITS"
  failures=$((failures + 1))
else
  echo "[v38 audit] PASS: CarlemanAtomicityOK not closed"
fi
echo

# ── Garde 6 : ResidualZeroOK := closed ───────────────────────────
echo "[v38 audit] phase 6: ResidualZeroOK := closed (forbidden)"
RZ_HITS=$(grep -rEn 'def ResidualZeroOK\s*:\s*BridgeStatus\s*:=\s*BridgeStatus\.closed' "$SCAN_ROOT" 2>/dev/null || true)
if [ -n "$RZ_HITS" ]; then
  echo "[v38 audit] FAIL: ResidualZeroOK promoted to closed"
  echo "$RZ_HITS"
  failures=$((failures + 1))
else
  echo "[v38 audit] PASS: ResidualZeroOK not closed"
fi
echo

# ── Garde 7 : aucune `RHClaimed = true` n'apparaît dans des assertions ──
echo "[v38 audit] phase 7: RHClaimed = true (in theorem statements, forbidden)"
RHE_HITS=$(grep -rEn 'RHClaimed\s*=\s*true' "$SCAN_ROOT" 2>/dev/null || true)
if [ -n "$RHE_HITS" ]; then
  echo "[v38 audit] FAIL: RHClaimed = true asserted in theorem statement"
  echo "$RHE_HITS"
  failures=$((failures + 1))
else
  echo "[v38 audit] PASS: no theorem asserts RHClaimed = true"
fi
echo

# ── Bilan ────────────────────────────────────────────────────────
if [ "$failures" -eq 0 ]; then
  echo "[v38 audit] PASS: anti-slippage doctrine preserved"
  echo "[v38 audit] RHClaimed remains false"
  echo "[v38 audit] No critical bridge promoted to closed"
  exit 0
else
  echo "[v38 audit] FAIL: $failures slippage(s) detected"
  echo "[v38 audit] doctrine reminder: no closed status without explicit proof"
  echo "[v38 audit] doctrine reminder: RHClaimed = false is invariant"
  exit 1
fi
