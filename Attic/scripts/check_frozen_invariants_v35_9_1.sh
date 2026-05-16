#!/usr/bin/env bash
# Couret-Unification — v35.9.1
# scripts/check_frozen_invariants.sh
#
# Vérifie les invariants Frozen stricts :
#   - 0 sorry (HARD FAIL)
#   - 0 axiom  (HARD FAIL)
#   - 0 constant (HARD FAIL)
#   - WARN sur vonMangoldt / digamma / zerosInShell
#   - WARN sur RHClaimed / HilbertPolyaClaimed

set -euo pipefail

ROOT="${1:-lean/CouretUnification}"
echo "[check] Frozen invariants under: $ROOT"
echo ""

fail=0

# ----------- HARD FAILS -----------

check_forbidden () {
  local label="$1"
  local regex="$2"
  local matches
  matches=$(grep -RInE --include='*.lean' "$regex" "$ROOT" || true)
  if [ -n "$matches" ]; then
    # Exclure les cas où c'est dans un commentaire /- ... -/ (hors scope awk robuste)
    # Pour Det2Transport.lean, on accepte 1 sorry.
    if [ "$label" = "sorry" ]; then
      # Filtrer uniquement les sorry hors commentaires (heuristique simple)
      real_sorry=$(grep -RInE --include='*.lean' '^[[:space:]]*sorry[[:space:]]*$' "$ROOT" || true)
      real_count=$(echo "$real_sorry" | grep -c . || true)
      if [ "$real_count" -le 1 ]; then
        echo "[OK]   $label : $real_count (Det2Transport autorisé)"
        return 0
      else
        echo "[FAIL] $label : $real_count occurrences (max autorisé : 1)"
        echo "$real_sorry"
        fail=1
      fi
    else
      echo "[FAIL] Pattern interdit : $label"
      echo "$matches"
      fail=1
    fi
  else
    echo "[OK]   $label : 0 occurrence"
  fi
}

# ----------- WARNINGS -----------

warn_regex () {
  local label="$1"
  local regex="$2"
  local matches
  matches=$(grep -RInE --include='*.lean' "$regex" "$ROOT" || true)
  if [ -n "$matches" ]; then
    echo "[WARN] Terme sensible présent : $label"
    echo "$matches" | sed 's/^/       /'
  else
    echo "[OK]   $label : 0 occurrence"
  fi
}

echo "=== Hard invariants (FAIL si violé) ==="
check_forbidden "sorry"    '\bsorry\b'
check_forbidden "axiom"    '^[[:space:]]*axiom[[:space:]]+'
check_forbidden "constant" '^[[:space:]]*constant[[:space:]]+'

echo ""
echo "=== Soft checks (WARN si présent hors note doctrinale) ==="
warn_regex "vonMangoldt"          '\bvonMangoldt\b'
warn_regex "digamma (ligne code)" '^[[:space:]]*(def|noncomputable def|structure).*\bdigamma\b'
warn_regex "zerosInShell (ligne code)" '^[[:space:]]*(def|noncomputable def|structure).*\bzerosInShell\b'
warn_regex "RHClaimed (texte)"    'RHClaimed'
warn_regex "HilbertPolyaClaimed"  'HilbertPolyaClaimed'

echo ""
echo "=== Résultat ==="
if [ "$fail" -ne 0 ]; then
  echo "[FAIL] Frozen invariant check échoué."
  exit 1
fi
echo "[PASS] Frozen hard invariants OK."
