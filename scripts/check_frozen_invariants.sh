#!/usr/bin/env bash
# Couret-Unification — v38.4.11
# scripts/check_frozen_invariants.sh
#
# Vérifie les invariants Frozen STRICTS sur la couche FROZEN UNIQUEMENT.
# Cf. DOCTRINE_FINITECORE_VS_CORE_v38.5.md pour la liste canonique.
#
# Couche FROZEN = Core/ + sous-modules qualifiés FROZEN + fichiers de garde.
# Couche ACTIVE = Logic/, AnalyticHorizon/, ResGold/, etc. — exclue du check.
#
# Hard invariants (FAIL si violé) sur FROZEN :
#   - 0 sorry effectif
#   - 0 axiom déclaré
#   - 0 constant
#
# Soft checks sur le dépôt entier (WARN, informatif) :
#   - signal RHClaimed / HilbertPolyaClaimed (références hors commentaires)
#   - terme vonMangoldt / digamma dans le code

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_AWK="$SCRIPT_DIR/lib/lean_strip_comments.awk"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
LEAN_ROOT="${1:-$REPO_ROOT/lean/CouretUnification}"

# ============================================================
# DÉFINITION CANONIQUE DE LA COUCHE FROZEN
# ============================================================
# Doctrine v38.5 — DOCTRINE_FINITECORE_VS_CORE_v38.5.md §2.1, §2.2
# Tout fichier listé ici DOIT respecter les invariants hard.
# Tout fichier non listé est considéré ACTIVE et n'est pas audité.

FROZEN_PATHS=(
  # Sous-dossier Core/ entier — couche machine-certifiée
  "Core/"
  # Couches doctrinales et de garde
  "EpistemicDiscipline/"
  "FCI/"
  # Fichiers de garde explicites
  "Frozen.lean"
  "Release/ReleaseManifest.lean"
)

# ============================================================
# Construction de la liste FROZEN effective
# ============================================================
build_frozen_filelist() {
  local frozen_files=()
  for path in "${FROZEN_PATHS[@]}"; do
    local full="$LEAN_ROOT/$path"
    if [ -d "$full" ]; then
      while IFS= read -r -d '' f; do
        frozen_files+=("$f")
      done < <(find "$full" -type f -name "*.lean" -print0)
    elif [ -f "$full" ]; then
      frozen_files+=("$full")
    fi
  done
  printf '%s\n' "${frozen_files[@]}"
}

FROZEN_FILES=$(build_frozen_filelist)
FROZEN_COUNT=$(printf '%s\n' "$FROZEN_FILES" | sed '/^$/d' | wc -l | tr -d ' ')

echo "╔════════════════════════════════════════════════════════════╗"
echo "║  FROZEN INVARIANTS CHECK — Couret-Unification              ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""
echo "[check] LEAN_ROOT = $LEAN_ROOT"
echo "[check] FROZEN files (à auditer strictement) : $FROZEN_COUNT"
echo "[check] Doctrine : DOCTRINE_FINITECORE_VS_CORE_v38.5.md"
echo ""

# ============================================================
# Helper : récupérer le code FROZEN nettoyé via la lib
# ============================================================
FROZEN_CLEAN=$(
  printf '%s\n' "$FROZEN_FILES" \
    | sed '/^$/d' \
    | tr '\n' '\0' \
    | xargs -0 awk -f "$LIB_AWK"
)

fail=0

# ============================================================
# HARD INVARIANTS sur FROZEN
# ============================================================
echo "=== Hard invariants FROZEN (FAIL si violé) ==="

# --- sorry ---
SORRY_LINES=$(printf '%s\n' "$FROZEN_CLEAN" \
  | grep -E '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' || true)
SORRY_COUNT=$(printf '%s\n' "$SORRY_LINES" | sed '/^$/d' | wc -l | tr -d ' ')

if [ "$SORRY_COUNT" -eq 0 ]; then
  echo "[OK]   sorry : 0 occurrence dans la couche FROZEN"
else
  echo "[FAIL] sorry : $SORRY_COUNT occurrence(s) dans FROZEN"
  printf '%s\n' "$SORRY_LINES" | sed 's/^/       /'
  fail=1
fi

# --- axiom ---
AXIOM_LINES=$(printf '%s\n' "$FROZEN_CLEAN" \
  | grep -E '(^|:)[[:space:]]*axiom[[:space:]]+' || true)
AXIOM_COUNT=$(printf '%s\n' "$AXIOM_LINES" | sed '/^$/d' | wc -l | tr -d ' ')

if [ "$AXIOM_COUNT" -eq 0 ]; then
  echo "[OK]   axiom : 0 occurrence dans la couche FROZEN"
else
  echo "[FAIL] axiom : $AXIOM_COUNT déclaration(s) dans FROZEN"
  printf '%s\n' "$AXIOM_LINES" | sed 's/^/       /'
  fail=1
fi

# --- constant ---
CONSTANT_LINES=$(printf '%s\n' "$FROZEN_CLEAN" \
  | grep -E '(^|:)[[:space:]]*constant[[:space:]]+' || true)
CONSTANT_COUNT=$(printf '%s\n' "$CONSTANT_LINES" | sed '/^$/d' | wc -l | tr -d ' ')

if [ "$CONSTANT_COUNT" -eq 0 ]; then
  echo "[OK]   constant : 0 occurrence dans la couche FROZEN"
else
  echo "[FAIL] constant : $CONSTANT_COUNT déclaration(s) dans FROZEN"
  printf '%s\n' "$CONSTANT_LINES" | sed 's/^/       /'
  fail=1
fi

echo ""

# ============================================================
# SOFT WARNINGS — sur l'ensemble du dépôt, hors commentaires
# ============================================================
echo "=== Soft warnings (informatifs, dépôt entier) ==="

ALL_CLEAN=$(
  find "$LEAN_ROOT" -type f -name "*.lean" -print0 \
    | xargs -0 awk -f "$LIB_AWK"
)

# Helper warn_regex — affiche les correspondances hors commentaires
# Filtre automatiquement les lignes d'import Mathlib (fausses positives)
warn_regex () {
  local label="$1"
  local regex="$2"
  local matches
  matches=$(printf '%s\n' "$ALL_CLEAN" \
    | grep -E "$regex" \
    | grep -vE "(^|[^[:alnum:]_])(Mathlib|import)([^[:alnum:]_]|$)" || true)
  if [ -z "$matches" ]; then
    echo "[OK]   $label : aucune référence hors commentaires"
  else
    echo "[WARN] $label référencé dans le code :"
    printf '%s\n' "$matches" | sed 's/^/       /'
  fi
}

# Termes sensibles à surveiller :
# (signal d'une dépendance analytique stricte et potentiellement contaminante du noyau)
# warn_regex "vonMangoldt"                "(^|[^[:alnum:]_])vonMangoldt([^[:alnum:]_]|$)"
# warn_regex "digamma (ligne code)"       "^[[:space:]]*(def|noncomputable def|structure).*[^[:alnum:]_]digamma([^[:alnum:]_]|$)"
# warn_regex "zerosInShell (ligne code)"  "^[[:space:]]*(def|noncomputable def|structure).*[^[:alnum:]_]zerosInShell([^[:alnum:]_]|$)"
# warn_regex "RHClaimed (texte)"          "(^|[^[:alnum:]_])RHClaimed([^[:alnum:]_]|$)"
# warn_regex "HilbertPolyaClaimed"        "(^|[^[:alnum:]_])HilbertPolyaClaimed([^[:alnum:]_]|$)"

# Termes sensibles : pattern avec bordure AVANT uniquement
# (on accepte les suffixes _xxx, Value, Custom, etc. comme dérivés
# qui portent probablement la même dépendance analytique)
warn_regex "vonMangoldt"   "(^|[^[:alnum:]_])vonMangoldt"
warn_regex "digamma"       "(def|noncomputable def|structure).*[^[:alnum:]_]digamma"
warn_regex "zerosInShell"  "(def|noncomputable def|structure).*[^[:alnum:]_]zerosInShell"

# Note : RHClaimed et HilbertPolyaClaimed sont surveillés par sorry_audit.sh
# (cf. v38.4.9), pas dupliqué ici. Leur présence est attendue par la
# doctrine, ce n'est pas un signal de problème.

echo ""

# ============================================================
# RÉSULTAT
# ============================================================
echo "=== Résultat ==="
if [ "$fail" -ne 0 ]; then
  echo "[FAIL] Frozen invariant check échoué — voir détails ci-dessus."
  exit 1
fi
echo "[PASS] Frozen hard invariants OK ($FROZEN_COUNT fichiers audités)."
