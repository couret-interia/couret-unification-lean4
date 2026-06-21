#!/usr/bin/env bash
# =============================================================================
# audit_reachability.sh — Modules non atteints depuis racines vivantes
#
# Usage :
#   bash audit_reachability.sh [--root <module>]... [--racine-dépôt <chemin>]
#
# Par défaut, racines = CouretUnification.All
# Tu peux en passer plusieurs : --root Foo --root Bar
#
# Calcule la fermeture transitive AVANT (= ce qui est importé récursivement)
# depuis l'ensemble des racines, puis liste les modules JAMAIS atteints.
# Ces modules sont les candidats à l'archivage / suppression.
#
# Le script ne modifie aucun fichier source.
# =============================================================================

set -euo pipefail

ROOT_DIR="lean/CouretUnification"
NS_PREFIX="CouretUnification"
ROOTS=()
OUT="build_reports/audit_reachability_report.md"

while [ $# -gt 0 ]; do
  case "$1" in
    --root)         ROOTS+=("$2"); shift 2 ;;
    --racine-dépôt) ROOT_DIR="$2"; shift 2 ;;
    --output)       OUT="$2";      shift 2 ;;
    *) echo "Argument inconnu : $1" >&2; exit 1 ;;
  esac
done

if [ ${#ROOTS[@]} -eq 0 ]; then
  ROOTS=("${NS_PREFIX}.All")
fi

if [ ! -d "$ROOT_DIR" ]; then
  echo "[ERREUR] Répertoire introuvable : $ROOT_DIR" >&2
  exit 1
fi

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# 1. Modules + arêtes (même logique que audit_orphans.sh)
echo "→ Énumération des modules…" >&2
find "$ROOT_DIR" -name '*.lean' -type f | sort > "$TMP/files.txt"
> "$TMP/modules.txt"
while IFS= read -r f; do
  rel="${f#lean/}"; mod="${rel%.lean}"; mod="${mod//\//.}"
  printf '%s\t%s\n' "$f" "$mod" >> "$TMP/modules.txt"
done < "$TMP/files.txt"
TOTAL=$(wc -l < "$TMP/modules.txt")

echo "→ Extraction des imports internes…" >&2
> "$TMP/edges.txt"
while IFS=$'\t' read -r f mod; do
  if grep -qE "^import ${NS_PREFIX}\." "$f" 2>/dev/null; then
    grep -E "^import ${NS_PREFIX}\." "$f" \
      | sed -E 's/^import +//' \
      | awk -v src="$mod" '{print src "\t" $1}' \
      >> "$TMP/edges.txt"
  fi
done < "$TMP/modules.txt"

cut -f2 "$TMP/modules.txt" | sort -u > "$TMP/all_modules.txt"
sort -k1,1 -t$'\t' "$TMP/edges.txt" > "$TMP/edges_sorted.txt"

# 2. Fermeture transitive AVANT depuis ROOTS
#    reached = ensemble des modules atteignables par chemin d'imports.
echo "→ Fermeture transitive depuis racines : ${ROOTS[*]}" >&2
printf '%s\n' "${ROOTS[@]}" | sort -u > "$TMP/reached.txt"

# Itère jusqu'à point fixe
while true; do
  prev=$(wc -l < "$TMP/reached.txt")
  # join : pour chaque src dans reached, lister les dst
  join -t$'\t' -1 1 -2 1 \
    "$TMP/edges_sorted.txt" \
    "$TMP/reached.txt" \
    2>/dev/null \
    | cut -f2 \
    | sort -u > "$TMP/new.txt"
  cat "$TMP/reached.txt" "$TMP/new.txt" | sort -u > "$TMP/reached.next"
  mv "$TMP/reached.next" "$TMP/reached.txt"
  curr=$(wc -l < "$TMP/reached.txt")
  [ "$curr" -eq "$prev" ] && break
done
REACHED=$(wc -l < "$TMP/reached.txt")

# 3. Non atteints
comm -23 "$TMP/all_modules.txt" "$TMP/reached.txt" > "$TMP/unreached.txt"
UNREACHED=$(wc -l < "$TMP/unreached.txt")

# 4. Lignes par fichier (pour chiffrer le poids des non-atteints)
> "$TMP/lines_by_mod.tsv"
while IFS=$'\t' read -r f mod; do
  l=$(wc -l < "$f")
  printf '%s\t%s\n' "$mod" "$l" >> "$TMP/lines_by_mod.tsv"
done < "$TMP/modules.txt"

# Total lignes non atteintes
TOTAL_LINES=$(awk -F'\t' '{s+=$2} END{print s+0}' "$TMP/lines_by_mod.tsv")
UNREACHED_LINES=$(join -t$'\t' -1 1 -2 1 \
  <(sort -k1,1 -t$'\t' "$TMP/lines_by_mod.tsv") \
  "$TMP/unreached.txt" 2>/dev/null \
  | awk -F'\t' '{s+=$2} END{print s+0}')

# 5. Rapport
{
  printf '# Audit d'\''atteignabilité — %s\n\n' "$(date '+%Y-%m-%d %H:%M')"
  printf 'Racine : `%s`\n\n' "$ROOT_DIR"

  printf '## Racines utilisées\n\n'
  for r in "${ROOTS[@]}"; do
    printf -- '- `%s`\n' "$r"
  done
  printf '\n'

  printf '## Résumé\n\n'
  printf -- '- Modules totaux : **%s** (%s lignes)\n' "$TOTAL" "$TOTAL_LINES"
  printf -- '- Modules **atteints** depuis les racines : **%s**\n' "$REACHED"
  printf -- '- Modules **NON atteints** : **%s** (%s lignes)\n' "$UNREACHED" "$UNREACHED_LINES"
  if [ "$TOTAL" -gt 0 ]; then
    PCT_MOD=$(awk -v u="$UNREACHED" -v t="$TOTAL" 'BEGIN{printf "%.1f", 100*u/t}')
    printf -- '- Pourcentage de modules non atteints : **%s%%**\n' "$PCT_MOD"
  fi
  if [ "$TOTAL_LINES" -gt 0 ]; then
    PCT_LINES=$(awk -v u="$UNREACHED_LINES" -v t="$TOTAL_LINES" 'BEGIN{printf "%.1f", 100*u/t}')
    printf -- '- Pourcentage de lignes non atteintes : **%s%%**\n' "$PCT_LINES"
  fi
  printf '\n'
  printf 'Un module **non atteint** est un module qu'\''aucun chemin d'\''imports depuis\n'
  printf 'les racines ne traverse. C'\''est un candidat fort à l'\''archivage si les racines\n'
  printf 'capturent bien la "zone vivante" du projet.\n\n'

  printf '## Modules non atteints\n\n'
  if [ -s "$TMP/unreached.txt" ]; then
    awk -F. '{
      key=""; n=NF-1
      if (n>1) for (i=1;i<=n;i++) key=(i==1?$i:key "." $i)
      else key="(racine)"
      print key
    }' "$TMP/unreached.txt" | sort | uniq -c | sort -rn > "$TMP/cluster_counts.txt"

    printf '### Vue par cluster (tri par taille)\n\n'
    printf '| Modules | Préfixe |\n|---:|---|\n'
    while read -r count prefix; do
      printf '| %s | `%s` |\n' "$count" "$prefix"
    done < "$TMP/cluster_counts.txt"
    printf '\n'

    printf '### Liste détaillée par cluster\n\n'
    awk -F. '{
      key=""; n=NF-1
      if (n>1) for (i=1;i<=n;i++) key=(i==1?$i:key "." $i)
      else key="(racine)"
      printf "%s\t%s\n", key, $0
    }' "$TMP/unreached.txt" | sort | awk -F'\t' '
    {
      if ($1!=prev) { if (prev!="") print ""; print "**" $1 "**\n"; prev=$1 }
      print "- `" $2 "`"
    }'
  else
    printf 'Aucun. Toutes les sources sont atteintes depuis les racines.\n'
  fi
  printf '\n'

  printf '## Suite recommandée\n\n'
  printf '1. Examiner les clusters non atteints les plus gros — souvent purgeables en bloc.\n'
  printf '2. Vérifier que ta liste de racines est correcte. Si tu utilises uniquement\n'
  printf '   `CouretUnification.All`, alors les non-atteints sont des modules qui ne\n'
  printf '   sont pas dans l'\''umbrella ; c'\''est un signal fort mais pas définitif.\n'
  printf '3. Pour un test plus exigeant, passer comme racines uniquement les modules\n'
  printf '   "vivants" (par exemple `Logic.H3.AlgebraTC`, `Logic.H3.RouteC`,\n'
  printf '   `Core.CayleyG30`). Tout ce qui n'\''est pas atteint alors est mort par rapport\n'
  printf '   à la frontière mathématique réelle.\n'
  printf '4. Archiver dans `Attic/` (hors arbre de build) plutôt que supprimer en premier passage.\n'
  printf '5. `lake build` après archivage. Si le build casse, le module n'\''était pas mort.\n'
} > "$OUT"

echo ""
echo "✓ Rapport : $OUT"
echo "  Total atteint : $REACHED / $TOTAL"
echo "  Non atteint   : $UNREACHED ($UNREACHED_LINES lignes)"
