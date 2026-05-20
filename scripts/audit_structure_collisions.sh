#!/usr/bin/env bash
# Couret-Unification — v38.4.14
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
# Refonte v38.4.19 : Ajout d'un rapport texte afin d'enregistrer les
# évolutions dans l'historique git (suivi) pour facilité la détection
# de possible dérive ou amélioration par le biais des fichiers modifiés
#
# Refonte v38.4.14 : audit des identifiants Catégorie 2 augmenté (options)
#   --basic
#     affiche un simple audit informatif compact (v38.4.13)
#   --full (par défaut) :
#     affiche les definitions dupliquées (fichier:ligne:def...) (hors whitelist)
#     liste des imports et des fichiers en relation
#     génère './build_reports/collisions_review.md'.
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
CU_FOLDER="CouretUnification"
VERSION="38.4.19"
# date courrante avec yyyy-mm-dd HH:MM:SS dans $DATE_TIME
printf -v DATE_TIME '%(%Y-%m-%d à %H:%M:%S)T' -1

# Parse arguments
MODE="full"  # défaut
LEAN_ROOT_ARG=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --basic)
      MODE="basic"
      shift
      ;;
    --full)
      MODE="full"
      shift
      ;;
    --help|-h)
      echo "Usage: $0 [--basic|--full] [LEAN_ROOT]"
      echo ""
      echo "  --basic   Affichage compact (juste le compteur par identifiant)"
      echo "  --full    Affichage complet (lignes, imports, fichiers & rapport MD) — DÉFAUT"
      echo ""
      echo "  LEAN_ROOT défaut : \$REPO_ROOT/lean/$CU_FOLDER"
      exit 0
      ;;
    *)
      LEAN_ROOT_ARG="$1"
      shift
      ;;
  esac
done

FULL_LIST="" # "1" = audit complet, "" = audit basique
if [ "$MODE" = "full" ]; then
  FULL_LIST="1"
fi

FULL_LIST_LABEL=" Basique"
if [ -n "$FULL_LIST" ]; then
  FULL_LIST_LABEL=" Complet"
fi

LEAN_ROOT="${LEAN_ROOT_ARG:-$REPO_ROOT/lean/$CU_FOLDER}"


TITLE=$(
echo "╔═══════════════════════════════════════════════════════════╗"
echo "║     AUDIT IDENTIFIANTS RÉPLIQUÉS — Couret-Unification     ║"
echo "╚═══════════════════════════════════════════════════════════╝"
)
MODE_TXT=$(echo "[Audit$FULL_LIST_LABEL]")
MODE=$(echo "[Audit$FULL_LIST_LABEL du $DATE_TIME]")

HEADING=$(
echo "VERSION   = $0 v$VERSION"
echo "Recherche : def / structure / inductive / abbrev / theorem"
echo "            identifiants répliqués à travers les modules"
echo ""
echo "═══ Identifiants répliqués (≥ 2 occurrences) ═══"
echo ""
)

HEADER_TXT=$(
echo "$TITLE"
echo ""
echo "$MODE_TXT"
echo ""
echo "$HEADING"
)

HEADER=$(
echo "$TITLE"
echo ""
echo "$MODE"
echo ""
echo "LEAN_ROOT = $LEAN_ROOT"
echo "$HEADING"
)
BODYTXT="$HEADER_TXT"$'\n'

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
  | grep -E ":[0-9]+:[[:space:]]*(def|noncomputable[[:space:]]+def|structure|inductive|abbrev|theorem|lemma)[[:space:]]+" \
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

# Liste complete des identifiants du programe
# echo "============ Identifiants computables =================="
# echo "$IDENT_LIST"
# echo ""

# ============================================================
# Comptage et classification
# ============================================================

# Identifiants répliqués (≥ 2 occurrences)
REPLICATED=$(printf '%s\n' "$IDENT_LIST" \
  | sort | uniq -c | awk '$1 >= 2 {print $0}' | sort -rn)

if [ -z "$REPLICATED" ]; then
  echo "[OK]  Aucun identifiant répliqué dans le dépôt."
  exit 0
fi

# Liste complete des identifiants du programe répliqués
# echo "============ Identifiants computables répliqués (≥ 2 occurrences) =================="
# echo "$REPLICATED"
# echo ""

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

# Helper warn_filter_by_name — affiche les correspondances hors commentaires
# Utilise DEFINITIONS pour filtrer par nom au lieu de re-grep le code complet
warn_filter_by_name() {
  local name="$1"
  printf '%s\n' "$DEFINITIONS" \
    | grep -E ":[0-9]+:[[:space:]]*(def|noncomputable[[:space:]]+def|structure|inductive|abbrev|theorem|lemma)[[:space:]]+$name([^[:alnum:]_]|$)" \
    | sed 's|[ \t]*$||' \
    | sed 's/^/       /'
}

# Classifier
EXPECTXT=""
EXPECTED=""
UNEXPECTED=""
UNEXPECTXT=""
UNEXPECTMD=""
UNEXPECT_F=""
UNEXPECT_L=""
I=0

while IFS= read -r line; do
  let I=I+1
  count=$(echo "$line" | awk '{print $1}')
  name=$(echo "$line" | awk '{print $2}')

  is_whitelisted=0
  for w in "${WHITELIST[@]}"; do
    if [ "$name" = "$w" ]; then
      is_whitelisted=1
      break
    fi
  done

  LN_MATCHES=""
  HAS_CORE_TXT="       "
  HAS_CORE=""
  if [ -n "$FULL_LIST" ] && [ "$is_whitelisted" -eq 0 ]; then
    LN_MATCHES=$'\n'$(warn_filter_by_name "$name")
    # Minimise les chemins (en relatif)
    LN_MATCHES=$(echo "$LN_MATCHES" | sed "s|$LEAN_ROOT|.|g")
    # Vérifier si Core/ apparaît dans les chemins matchés
    if printf '%s' "$LN_MATCHES" | grep -q "/Core/"; then
      HAS_CORE=" ⚠ Core"  # Alerte visuelle
      HAS_CORE_TXT="$HAS_CORE"
    fi
  fi

  LN_TXT=$(echo "$HAS_CORE_TXT ── $line") # STR_PAD_RIGHT. %5s (LEFT)
  LN=$(printf "#%-5s ── $line$HAS_CORE" $I) # STR_PAD_RIGHT. %5s (LEFT)

  if [ "$is_whitelisted" -eq 1 ]; then
    EXPECTXT="$EXPECTXT$LN_TXT"$'\n'
    EXPECTED="$EXPECTED$LN"$'\n'
  else
    UNEXPECT_F="$UNEXPECT_F$LN_MATCHES"$'\n'
    UNEXPECT_L="$UNEXPECT_L$LN"$'\n'
    UNEXPECTMD="$UNEXPECTMD"'### `'"$LN"'`'$(echo "$LN_MATCHES" | sed "s|       ./|- ./|g")$'\n'
    UNEXPECTXT="$UNEXPECTXT$LN_TXT$LN_MATCHES"$'\n'
    UNEXPECTED="$UNEXPECTED$LN$LN_MATCHES"$'\n'
  fi
done <<< "$REPLICATED"

HEADCAT_1=$(
  echo "── Catégorie 1 — Réplications doctrinales attendues (whitelist) ──"
  echo "(gardes RH/HP, fileIdentity, statuts, métriques d'audit par module)"
)
HEADCAT_2_1=$(echo "── Catégorie 2.1 — Réplications hors whitelist (à examiner) ──")
HEADCAT_2_2=$(echo "── Catégorie 2.2 — Relevé des imports à examiner ──")
HEADCAT_2_3=$(echo "── Catégorie 2.3 — Liste des imports à examiner ──")
HEADCAT_2_4=$(echo "── Catégorie 2.4 — Liste des fichiers (unique) à examiner ──")

INFOCAT_2=$(
  echo "[INFO] Ces identifiants apparaissent dans plusieurs modules."
  echo "       Ce n'est pas forcément un problème (chaque namespace"
  echo "       protège sa propre version), mais une revue manuelle"
  echo "       peut révéler des duplications non-intentionnelles."
)
OK_CAT_1=$(echo "[OK]  Aucune réplication doctrinale.")
OK_CAT_2=$(echo "[OK]  Aucune réplication hors whitelist doctrinale.")

BODYTXT="$BODYTXT$HEADCAT_1"$'\n' # txt

# Affichage
echo "$HEADER"$'\n'
echo "$HEADCAT_1"$'\n'
if [ -n "$EXPECTED" ]; then
  BODYTXT="$BODYTXT$EXPECTXT"$'\n' # txt
  printf '%s' "$EXPECTED"
else
  BODYTXT="$BODYTXT$OK_CAT_1"$'\n' # txt
  echo "$OK_CAT_1"$'\n'
fi
echo ""

BODYTXT="$BODYTXT$HEADCAT_2_1"$'\n' # txt
echo "$HEADCAT_2_1"$'\n'
if [ -n "$UNEXPECTED" ]; then
  BODYTXT="$BODYTXT$UNEXPECTXT"$'\n'"$INFOCAT_2"$'\n' # txt
  printf '%s' "$UNEXPECTED"
  echo ""
  echo "$INFOCAT_2"
  if [ -n "$FULL_LIST" ]; then

    # ============================================================
    # Extraction des importations : "(import ...)" pre-calcul
    # ============================================================
    # Format : "fichier:ligne:keyword import "
    IMPORTATIONS=$(printf '%s\n' "$ALL_CLEAN" \
      | grep -E ":[0-9]+:[[:space:]]*(import[[:space:]]+[A-Za-z_])" \
      || true)

    # Fichiers uniques
    old="$IFS"
    UNEXPECT_U=""
    while IFS= read -r line; do
      if [ -n "$line" ]; then
        IFS=':' read -ra ITEM <<< "$line"
        UNEXPECT_U="$UNEXPECT_U"$(echo "$ITEM")$'\n'
      fi
    done <<< "$UNEXPECT_F"

    UNEXPECT_I=$(echo "$UNEXPECT_U" | uniq)
    UNEXPECT_W=$(echo "$UNEXPECT_U" | sort | uniq)
    UNEXPECT_U=$(echo "$UNEXPECT_U" | awk '!a[$0]++')

    # Recherche les `import ` (crée la liste)
    IMPORTS=$(echo "$UNEXPECT_U" | sed "s|\./|import $CU_FOLDER\.|g")
    IMPORTS=$(echo "$IMPORTS" | sed "s|\.lean||g")
    IMPORTS=$(echo "$IMPORTS" | sed "s|/|.|g")
    IMP_FULL_TXT=""
    IMP_FULL=""
    IMP_LIST=""
    IMP_FULLMD=""
    IMP_LISTMD=""
    # I=0 # Restart ?
    FIMP=""
    while IFS= read -r line; do
      if [ -n "$line" ]; then
        let I=I+1
        LN_TXT=$(printf "        ── $line")
        LN=$(printf "#%-5s ── $line" $I) # STR_PAD_RIGHT. %5s (LEFT)
        # Enleve l'indentation
        IMP=$(printf '%s' "$line" | sed -E "s|^[[:space:]]+||g")
        FIMP=$(printf '%s\n' "$IMPORTATIONS" | grep "$IMP" | sed 's/^/       /' || true)
        # Minimise les chemins (en relatif) + espaces en fin de lignes
        FIMP=$(echo "$FIMP" | sed "s|$LEAN_ROOT|.|g" | sed 's|[ \t]*$||')
        IMP_FULL_TXT="$IMP_FULL_TXT"$(echo "$LN_TXT"$'\n'"$FIMP")$'\n'
        IMP_FULL="$IMP_FULL"$(echo "$LN"$'\n'"$FIMP")$'\n'
        IMP_LIST="$IMP_LIST$line"$'\n'
        GREP_IMPMD='`grep -rnE "'"$IMP"'([^[:alnum:]_]|$)" "lean/'"$CU_FOLDER"'/" --include="*.lean"`'
        IMP_FULLMD="$IMP_FULLMD"'### `'"$LN"'`'$'\n'"$GREP_IMPMD"$'\n'$(echo "$FIMP" | sed -E 's/^[[:space:]]+/- /g')$'\n'
        IMP_LISTMD="$IMP_LISTMD"'- `'$(echo "$line" | sed "s| ||g")'`'$'\n'
      fi
    done <<< "$IMPORTS"

    BODYTXT="$BODYTXT"$'\n'"$HEADCAT_2_2"$'\n'"$IMP_FULL_TXT"$'\n' # txt
    BODYTXT="$BODYTXT$HEADCAT_2_3"$'\n'"$IMP_LIST"$'\n' # txt
    BODYTXT="$BODYTXT$HEADCAT_2_4"$'\n'$(echo "$UNEXPECT_U")$'\n' # | sed -E 's/[[:space:]]+/  /g')$'\n' # txt +Indentation modérée (2 espaces)

    echo ""
    echo "$HEADCAT_2_2"$'\n'
    echo "$IMP_FULL"
    echo ""
    echo "$HEADCAT_2_3"$'\n'
    echo "$IMP_LIST"

    echo ""
    echo "$HEADCAT_2_4"$'\n'
    echo "$UNEXPECT_U" | sed -E 's/[[:space:]]+/  /g'  # Indentation modérée (2 espaces)
    # Restauration de la valeur du IFS
    IFS="$old"
  fi
else
  # [OK]  Aucune réplication hors whitelist doctrinale.
  BODYTXT="$BODYTXT$OK_CAT_2"$'\n' # txt
  echo "$OK_CAT_2"
fi

SYNT=""
TOTAL_EXPECTED=$(printf '%s' "$EXPECTED" | wc -l | tr -d ' ')
TOTAL_UNEXPECTED=$(printf '%s' "$UNEXPECT_L" | wc -l | tr -d ' ')
SYNT="$SYNT""Identifiants doctrinaux répliqués     (whitelist) : $TOTAL_EXPECTED"$'\n'
SYNT="$SYNT""Identifiants répliqués             hors whitelist : $TOTAL_UNEXPECTED"$'\n'
if [ -n "$FULL_LIST" ]; then
  TOTAL_UNEXPECT_I=$(printf '%s' "$UNEXPECT_I" | wc -l | tr -d ' ')
  TOTAL_UNEXPECT_W=$(printf '%s' "$UNEXPECT_W" | wc -l | tr -d ' ')
  SYNT="$SYNT""Identifiants répliqués     (total) hors whitelist : $TOTAL_UNEXPECT_I"$'\n'
  SYNT="$SYNT""Fichiers identifiés hors whitelist avec répliques : $TOTAL_UNEXPECT_W fichiers"$'\n'
fi
FOOT=$(
echo ""
echo "═══ Synthèse ═══"
echo "$SYNT"
echo "[INFO] Cet audit est informatif, non bloquant."
echo "       (Les vraies collisions intra-namespace sont refusées par Lean.)"
)

echo "$FOOT"

# Générer build_reports/audit_structure_collisions.txt (complet)
if [ -n "$FULL_LIST" ]; then
  BODYTXT="$BODYTXT$FOOT"$'\n' # txt
  REPORT_TXT="$REPO_ROOT/build_reports/audit_structure_collisions.txt"
  printf "$BODYTXT" > "$REPORT_TXT"
  echo ""
  echo "[INFO] Rapport texte détaillé :"
  echo "       $REPORT_TXT"
fi


# Idea: Si même def (et dans Core ?), générer les commandes (sh, sed, ...)
#       pour ajouter un `-- IDENTIFIANTS_RÉPLIQUÉS` (commentaires)
#       en fin de ligne (aide a repérer avec git)

# Générer build_reports/collisions_review.md
if [ -n "$UNEXPECTED" ] && [ -n "$FULL_LIST" ]; then
  REPORT_MD="$REPO_ROOT/build_reports/collisions_review.md"
  {
    echo "# Audit identifiants répliqués hors whitelist — $(date +%Y-%m-%d)"
    echo "- *Dossier : $LEAN_ROOT*"
    echo "- *Catégorie : 2 (hors whitelist/Frozen)*"
    echo ""
    echo "> ## Synthèse"
    echo "$SYNT" | awk '!a[$0]++' | sed 's/^/> - /'
    echo "---"
    # Identifiants Catégorie 2
    echo "## 1) Identifiants à examiner (réplications)"
    echo ""
    printf '%s' "$UNEXPECTMD"
    echo ""
    echo "---"

    echo ""
    # Imports Catégorie 2
    echo "## 2) Relevé complet des imports à examiner"
    echo ""
    printf '%s' "$IMP_FULLMD"
    echo "---"
    echo "## 3) Liste des imports (unique) à examiner"
    echo ""
    printf '%s' "$IMP_LISTMD"

    echo "---"
    # Fichies Catégorie 2
    echo "## 4) Liste des fichiers (unique) à examiner"
    echo ""
    echo "$UNEXPECT_U" | sed -E 's/^[[:space:]]*/- /'  # Indentation modérée (2 espaces)
    echo "---"$'\n\n'"> Audit généré par $0 (v$VERSION) le $DATE_TIME"
  } > "$REPORT_MD"
  echo ""
  echo "[INFO] Rapport markdown détaillé :"
  echo "       $REPORT_MD"
fi
