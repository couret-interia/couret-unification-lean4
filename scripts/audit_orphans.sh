#!/usr/bin/env bash
# =============================================================================
# audit_orphans.sh — Audit d'imports orphelins, dépôt CouretUnification
#
# Usage :
#   bash audit_orphans.sh [racine]
#
# Par défaut, racine = lean/CouretUnification (à lancer depuis la racine du
# dépôt). Produit un rapport Markdown : audit_orphans_report.md
#
# Ce script ne modifie AUCUN fichier source. Il écrit uniquement le rapport.
# =============================================================================

set -euo pipefail

ROOT="${1:-lean/CouretUnification}"
NS_PREFIX="CouretUnification"
OUT="build_reports/audit_orphans_report.md"

if [ ! -d "$ROOT" ]; then
  echo "[ERREUR] Répertoire introuvable : $ROOT" >&2
  echo "Lancez ce script depuis la racine du dépôt." >&2
  exit 1
fi

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# ---------------------------------------------------------------------------
# 1. Énumérer tous les fichiers .lean et leur nom de module
#    Ex : lean/CouretUnification/Logic/H3/AlgebraTC.lean
#         → CouretUnification.Logic.H3.AlgebraTC
# ---------------------------------------------------------------------------
echo "→ Énumération des modules…" >&2
find "$ROOT" -name '*.lean' -type f | sort > "$TMP/files.txt"
TOTAL=$(wc -l < "$TMP/files.txt")
echo "  $TOTAL fichiers .lean trouvés" >&2

> "$TMP/modules.txt"
while IFS= read -r f; do
  rel="${f#lean/}"
  mod="${rel%.lean}"
  mod="${mod//\//.}"
  printf '%s\t%s\n' "$f" "$mod" >> "$TMP/modules.txt"
done < "$TMP/files.txt"

# ---------------------------------------------------------------------------
# 2. Extraire les arêtes d'import internes (CouretUnification.X → CouretUnification.Y)
# ---------------------------------------------------------------------------
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

EDGES=$(wc -l < "$TMP/edges.txt")
echo "  $EDGES arêtes" >&2

# ---------------------------------------------------------------------------
# 3. Modules orphelins = présents dans modules.txt, absents des cibles d'imports
# ---------------------------------------------------------------------------
cut -f2 "$TMP/modules.txt" | sort -u  > "$TMP/all_modules.txt"
cut -f2 "$TMP/edges.txt"   | sort -u  > "$TMP/imported.txt"
comm -23 "$TMP/all_modules.txt" "$TMP/imported.txt" > "$TMP/orphans.txt"
ORPHANS=$(wc -l < "$TMP/orphans.txt")

# ---------------------------------------------------------------------------
# 4. Métriques par fichier : lignes, sorry, axiom, opaque, théorèmes triviaux
# ---------------------------------------------------------------------------
echo "→ Comptage métriques par fichier…" >&2
printf 'module\tlines\tsorry\taxiom\topaque\ttrivial\tfile\n' > "$TMP/metrics.tsv"
while IFS=$'\t' read -r f mod; do
  lines=$(wc -l < "$f")
  sorries=$(grep -cE '\bsorry\b' "$f" 2>/dev/null || true)
  axioms=$(grep -cE '^[[:space:]]*axiom\b' "$f" 2>/dev/null || true)
  opaques=$(grep -cE '^[[:space:]]*opaque\b' "$f" 2>/dev/null || true)
  trivials=$(grep -cE ':[[:space:]]*True[[:space:]]*:=[[:space:]]*(trivial|by[[:space:]]+trivial)' "$f" 2>/dev/null || true)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$mod" "${lines:-0}" "${sorries:-0}" "${axioms:-0}" "${opaques:-0}" "${trivials:-0}" "$f" \
    >> "$TMP/metrics.tsv"
done < "$TMP/modules.txt"

# ---------------------------------------------------------------------------
# 5. Rapport Markdown
# ---------------------------------------------------------------------------
{
  printf '# Audit d'\''imports orphelins — %s\n\n' "$(date '+%Y-%m-%d %H:%M')"
  printf 'Racine : `%s`\n\n' "$ROOT"

  printf '## Résumé\n\n'
  printf -- '- Modules totaux : **%s**\n'   "$TOTAL"
  printf -- '- Arêtes internes : **%s**\n'  "$EDGES"
  printf -- '- **Modules orphelins** : **%s**\n\n' "$ORPHANS"
  printf 'Un module orphelin n'\''est pas forcément à supprimer — il peut être un point d'\''entrée\n'
  printf 'légitime (`All.lean`, façade publique, exécutable). Mais c'\''est le candidat n°1 à examiner.\n\n'

  printf '## Modules orphelins, regroupés par préfixe\n\n'
  if [ -s "$TMP/orphans.txt" ]; then
    awk -F. '
    {
      key = ""
      n = NF - 1
      if (n > 1) for (i=1; i<=n; i++) key = (i==1 ? $i : key "." $i)
      else key = "(racine)"
      printf "%s\t%s\n", key, $0
    }' "$TMP/orphans.txt" | sort | awk -F'\t' '
    {
      if ($1 != prev) {
        if (prev != "") print ""
        print "### " $1
        prev = $1
      }
      print "- `" $2 "`"
    }'
  else
    printf 'Aucun.\n'
  fi
  printf '\n'

  printf '## Top 30 — fichiers les plus courts (probables stubs)\n\n'
  printf '| Lignes | Sorry | Axiom | Opaque | Trivial | Module |\n'
  printf '|---:|---:|---:|---:|---:|---|\n'
  tail -n +2 "$TMP/metrics.tsv" | sort -t$'\t' -k2,2n | head -30 | \
    awk -F'\t' '{printf "| %s | %s | %s | %s | %s | `%s` |\n", $2,$3,$4,$5,$6,$1}'
  printf '\n'

  printf '## Fichiers contenant des théorèmes triviaux (`: True := trivial`)\n\n'
  HITS=$(tail -n +2 "$TMP/metrics.tsv" | awk -F'\t' '$6 > 0' | wc -l)
  if [ "$HITS" -gt 0 ]; then
    printf '| Trivial | Lignes | Module |\n'
    printf '|---:|---:|---|\n'
    tail -n +2 "$TMP/metrics.tsv" | awk -F'\t' '$6 > 0 {printf "| %s | %s | `%s` |\n", $6, $2, $1}' | sort -t'|' -k2,2nr
  else
    printf 'Aucun.\n'
  fi
  printf '\n'

  printf '## Sorries par fichier (non nuls)\n\n'
  HITS=$(tail -n +2 "$TMP/metrics.tsv" | awk -F'\t' '$3 > 0' | wc -l)
  if [ "$HITS" -gt 0 ]; then
    printf '| Sorries | Module |\n|---:|---|\n'
    tail -n +2 "$TMP/metrics.tsv" | awk -F'\t' '$3 > 0 {printf "| %s | `%s` |\n", $3, $1}'
  else
    printf 'Aucun.\n'
  fi
  printf '\n'

  printf '## Axiomes / opaques par fichier (non nuls)\n\n'
  HITS=$(tail -n +2 "$TMP/metrics.tsv" | awk -F'\t' '$4 > 0 || $5 > 0' | wc -l)
  if [ "$HITS" -gt 0 ]; then
    printf '| Axiom | Opaque | Module |\n|---:|---:|---|\n'
    tail -n +2 "$TMP/metrics.tsv" | awk -F'\t' '$4 > 0 || $5 > 0 {printf "| %s | %s | `%s` |\n", $4, $5, $1}'
  else
    printf 'Aucun.\n'
  fi
  printf '\n'

  printf '## Suite recommandée\n\n'
  printf '1. Pour chaque cluster orphelin de la section 2, décider en bloc : **garder**, **archiver** (`git mv` vers `Attic/` hors arbre de build), **supprimer**.\n'
  printf '2. Les fichiers de la section "théorèmes triviaux" sont prioritaires à supprimer s'\''ils sont aussi orphelins.\n'
  printf '3. Re-lancer `lake build` après chaque purge significative.\n'
  printf '4. Recommencer le script jusqu'\''à un point fixe.\n'
} > "$OUT"

echo ""
echo "✓ Rapport : $OUT"
echo ""
echo "Vérifs rapides utiles :"
echo "  wc -l \"$OUT\""
echo "  head -60 \"$OUT\""
