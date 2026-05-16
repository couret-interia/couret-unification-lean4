#!/usr/bin/env bash
# Couret-Unification — v38.4.13
# scripts/audit_structure_collisions.sh
#
# Note doctrinale
# ───────────────
# Le script v38.0+ prétendait détecter des "collisions de structures
# dans un même namespace". Cette tâche est inutile pour deux raisons :
#
#   1. Lean 4 lui-même refuse au compile de définir deux fois la même
#      `structure X` dans le même namespace. Si `make build-all` passe,
#      par construction il n'y a pas de telle collision.
#
#   2. Le script v38.0+ contenait un bug awk (séparateur ':' mal
#      configuré) qui rendait son détecteur tautologique : il
#      comptait le total de structures et affichait toujours FAIL.
#
# Refonte v38.4.13 : audit informatif des identifiants répliqués
# à travers les namespaces (sans considérer cela comme un échec).
#
# Cas typique : RHClaimed est défini dans ~35 modules différents
# (un par module FROZEN, pour porter la garde doctrinale localement).
# Ce n'est pas une collision : c'est une réplication explicite voulue.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_AWK="$SCRIPT_DIR/lib/lean_strip_comments.awk"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
LEAN_ROOT="${1:-$REPO_ROOT/lean/CouretUnification}"

echo "╔════════════════════════════════════════════════════════════╗"
echo "║  AUDIT IDENTIFIANTS RÉPLIQUÉS — Couret-Unification         ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""
echo "[audit] LEAN_ROOT = $LEAN_ROOT"
echo "[audit] Recherche : def / structure / inductive / abbrev / theorem"
echo "        identifiants répliqués à travers les modules"
echo ""

# ============================================================
# Code à analyser (parsé via la lib v38.4.10)
# ============================================================
ALL_CLEAN=$(
  find "$LEAN_ROOT" -type f -name "*.lean" -print0 \
    | xargs -0 awk -f "$LIB_AWK"
)

# ============================================================
# Extraction des définitions : "(def|structure|...) NAME"
# ============================================================
# Format : "fichier:ligne:keyword name"
DEFINITIONS=$(printf '%s\n' "$ALL_CLEAN" \
  | grep -E ":[0-9]+:[[:space:]]*(def|noncomputable[[:space:]]+def|structure|inductive|abbrev|theorem|lemma)[[:space:]]+[A-Za-z_]" \
  || true)

# ============================================================
# Extraction du nom d'identifiant (3e champ par espace)
# ============================================================
# Du format "fichier:ligne: def X ..." extraire X
IDENT_LIST=$(printf '%s\n' "$DEFINITIONS" \
  | sed -E 's/^[^:]+:[0-9]+:[[:space:]]*//' \
  | awk '{
      # Skip "noncomputable" si présent au début
      i = 1
      if ($i == "noncomputable") i = 2
      # Le mot-clé est en $i, le nom en $(i+1)
      name = $(i+1)
      # Nettoyer : retirer ":" final, "(", parenthèses
      gsub(/[\(\):,].*/, "", name)
      if (name != "") print name
    }')

# ============================================================
# Comptage et classification
# ============================================================
echo "=== Identifiants répliqués (≥ 2 occurrences) ==="
echo ""

REPLICATED=$(printf '%s\n' "$IDENT_LIST" \
  | sort | uniq -c | awk '$1 >= 2 {print $0}' | sort -rn)

if [ -z "$REPLICATED" ]; then
  echo "[OK]  Aucun identifiant répliqué dans le dépôt."
  exit 0
fi

# Whitelist : identifiants doctrinaux dont la réplication est attendue
WHITELIST=(
  # Convention RHClaimed (v38.4.8)
  "RHClaimed" "HilbertPolyaClaimed" "Det2IdentityClaimed" "CandidateCClaimed"
  # Théorèmes de garde
  "rh_not_claimed" "rh_claimed_false" "rhClaimed_eq_false"
  "hp_not_claimed" "candidateC_not_claimed"
  # Identité doctrinale par module
  "fileIdentity" "FileIdentity"
  # Métriques d'audit par fichier
  "sorryCount" "axiomCount" "loaded"
  # Status / Layer doctrinaux
  "status" "Layer" "EpistemicStatus" "BridgeStatus"
)

# Classifier
EXPECTED=""
UNEXPECTED=""

while IFS= read -r line; do
  count=$(echo "$line" | awk '{print $1}')
  name=$(echo "$line" | awk '{print $2}')

  is_whitelisted=0
  for w in "${WHITELIST[@]}"; do
    if [ "$name" = "$w" ]; then
      is_whitelisted=1
      break
    fi
  done

  if [ "$is_whitelisted" -eq 1 ]; then
    EXPECTED="$EXPECTED$line"$'\n'
  else
    UNEXPECTED="$UNEXPECTED$line"$'\n'
  fi
done <<< "$REPLICATED"

# Affichage
if [ -n "$EXPECTED" ]; then
  echo "── Catégorie 1 — Réplications doctrinales attendues (whitelist) ──"
  echo "(gardes RH/HP, fileIdentity, statuts, métriques d'audit par module)"

  printf '%s' "$EXPECTED"
  echo ""
fi

if [ -n "$UNEXPECTED" ]; then
  echo "── Catégorie 2 — Réplications hors whitelist (à examiner) ──"
  printf '%s' "$UNEXPECTED"
  echo ""
  echo "[INFO] Ces identifiants apparaissent dans plusieurs modules."
  echo "       Ce n'est pas forcément un problème (chaque namespace"
  echo "       protège sa propre version), mais une revue manuelle"
  echo "       peut révéler des duplications non-intentionnelles."
else
  echo "[OK]  Aucune réplication hors whitelist doctrinale."
fi

echo ""
echo "=== Synthèse ==="
TOTAL_EXPECTED=$(printf '%s' "$EXPECTED" | wc -l | tr -d ' ')
TOTAL_UNEXPECTED=$(printf '%s' "$UNEXPECTED" | wc -l | tr -d ' ')
echo "Identifiants doctrinaux répliqués (whitelist) : $TOTAL_EXPECTED"
echo "Identifiants répliqués hors whitelist         : $TOTAL_UNEXPECTED"
echo ""
echo "[INFO] Cet audit est informatif, non bloquant."
echo "       (Les vraies collisions intra-namespace sont refusées par Lean.)"
