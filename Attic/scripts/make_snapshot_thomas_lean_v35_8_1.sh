#!/usr/bin/env bash
# scripts/make_snapshot_thomas.sh
#
# Génère un monolithe CI dérivé pour Thomas à partir de l'arborescence
# stratifiée canonique. Le monolithe contient les **vraies preuves**
# (pas d'axiomes "shim CI") et préserve l'invariant RHClaimed = false.
#
# Usage : ./scripts/make_snapshot_thomas.sh [output_path]
# Default output : ./CouretUnification_Snapshot_Thomas.lean
#
# Doctrine :
#   - Source canonique : arborescence CouretUnification/
#   - Artefact dérivé : un fichier monolithique pour build CI rapide
#   - Aucun axiome "snapshot" introduit. Si le snapshot Mathlib casse
#     une preuve, on corrige la preuve dans la source canonique, on ne
#     l'axiomatise pas dans le monolithe.

set -euo pipefail

OUTPUT="${1:-./CouretUnification_Snapshot_Thomas.lean}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SRC="$ROOT/lean/CouretUnification"

if [ ! -d "$SRC" ]; then
  echo "Erreur : répertoire source introuvable : $SRC" >&2
  exit 1
fi

# Ordre topologique de fusion (respecte le DAG Meta → Logic → ...)
FILES=(
  "Meta/Layer.lean"
  "Logic/Doctrine.lean"
  "Logic/LocalFactor.lean"
  "Logic/SquarefreeSupport.lean"
  "Logic/LocalSquarefreeBridge.lean"
  "Logic/SophieGermainMatrix.lean"
  "Logic/C3Weak.lean"
  "Logic/FEnrichedSpec.lean"
  "Logic/FEnriched30.lean"
  "Logic/EulerBridgeInfiniteCompat.lean"
  "Logic/EulerBridgeInfinite.lean"
  "Logic/EulerBridgeInfiniteReal.lean"
  "Logic/CriticalLineTransferSpec.lean"
  "Logic/L10NoGoTheorem.lean"
  "Logic/L6Bridge.lean"
  "Logic/OpenLocks.lean"
  "Meta/AuditHints.lean"
  "Empirical/SophieGermainTransitions.lean"
  "Empirical/SophieGermainExpected.lean"
  "Speculative/AnalogyMTF.lean"
  "Speculative/Ontology.lean"
)

# Génération
{
  cat <<'EOF'
/-
# CouretUnification_Snapshot_Thomas.lean — Artefact CI dérivé (v35.8.1-bis)

**ATTENTION : fichier généré automatiquement.**

Source canonique : arborescence stratifiée CouretUnification/.
Ne PAS éditer ce fichier directement. Pour modifier le contenu :
  1. Éditer la source canonique CouretUnification/<sous-dossier>/<fichier>.lean
  2. Régénérer : ./scripts/make_snapshot_thomas.sh

## Doctrine de cet artefact

  - RHClaimed = false (préservé)
  - Aucun axiome "snapshot CI" — les preuves sont identiques à la source
  - Sorries identifiables par grep (catégorisation préservée par commentaires)
  - Pour audit : voir Meta/AuditHints.lean dans la source canonique
-/

EOF

  # Extraire et fusionner tous les imports Mathlib uniques
  echo "-- ============================================================"
  echo "-- IMPORTS MATHLIB FUSIONNÉS"
  echo "-- ============================================================"
  for f in "${FILES[@]}"; do
    if [ -f "$SRC/$f" ]; then
      grep -E "^import Mathlib" "$SRC/$f" || true
    fi
  done | sort -u

  echo ""
  echo "-- ============================================================"
  echo "-- CONTENU FUSIONNÉ (imports internes supprimés)"
  echo "-- ============================================================"
  echo ""

  for f in "${FILES[@]}"; do
    if [ ! -f "$SRC/$f" ]; then
      echo "-- [SKIP] $f introuvable" >&2
      continue
    fi
    echo ""
    echo "-- ─────────────────────────────────────────────────────────────"
    echo "-- SOURCE : CouretUnification/$f"
    echo "-- ─────────────────────────────────────────────────────────────"
    echo ""
    # Strip imports (Mathlib already merged above; internal imports
    # become unnecessary in monolithe)
    grep -vE "^import (Mathlib|CouretUnification)" "$SRC/$f"
  done
} > "$OUTPUT"

echo "Monolithe Snapshot-Thomas généré : $OUTPUT" >&2
echo "Lignes : $(wc -l < "$OUTPUT")" >&2
echo "Sorries : $(grep -cE '^[[:space:]]*sorry[[:space:]]*$' "$OUTPUT")" >&2
echo "Axiomes locaux : $(grep -cE '^axiom |^[[:space:]]+axiom ' "$OUTPUT" || true)" >&2
