#!/usr/bin/env sh
set -eu

# scripts/audit_proved.sh
#
# Audit documentaire des candidats [D].
#
# Ce script ne decide pas automatiquement du statut scientifique [D].
# Il produit des listes relisibles :
#   - marqueurs documentaires [D] / D-formal / D-computational / proved
#   - theorem/lemma Lean dans tout le depot
#   - theorem/lemma Lean dans les modules importes par Frozen.lean
#
# Usage :
#   scripts/audit_proved.sh
#   scripts/audit_proved.sh .
#   scripts/audit_proved.sh /chemin/vers/repo
#
# Sorties :
#   build_reports/proved_markers.txt
#   build_reports/proved_theorems_all.txt
#   build_reports/proved_theorems_frozen.txt
#   build_reports/proved_summary.txt

ROOT="${1:-.}"

LEAN_ROOT="$ROOT/lean/CouretUnification"
DOCS_ROOT="$ROOT/docs"
BUILD_ROOT="$ROOT/build_reports"
FROZEN_FILE="$LEAN_ROOT/Frozen.lean"

OUT_DIR="$BUILD_ROOT"
MARKERS_OUT="$OUT_DIR/proved_markers.txt"
ALL_THEOREMS_OUT="$OUT_DIR/proved_theorems_all.txt"
FROZEN_IMPORTS_OUT="$OUT_DIR/proved_frozen_imports.txt"
FROZEN_THEOREMS_OUT="$OUT_DIR/proved_theorems_frozen.txt"
SUMMARY_OUT="$OUT_DIR/proved_summary.txt"

mkdir -p "$OUT_DIR"

if [ ! -d "$LEAN_ROOT" ]; then
  echo "Erreur : dossier Lean introuvable : $LEAN_ROOT" >&2
  exit 1
fi

if [ ! -f "$FROZEN_FILE" ]; then
  echo "Erreur : Frozen.lean introuvable : $FROZEN_FILE" >&2
  exit 1
fi

D_PATTERN='\[D\]|D-formal|D-computational|proved \[D\]|Status[[:space:]]*:[[:space:]]*proved|status[[:space:]]*:=[[:space:]]*.*Status\.proved|status[[:space:]]*:=[[:space:]]*.*\.proved'
THEOREM_PATTERN='(theorem|lemma)[[:space:]]+'

echo "== Audit marqueurs [D] / proved =="
{
  if [ -d "$DOCS_ROOT" ]; then
    #~ find "$LEAN_ROOT" "$DOCS_ROOT" "$BUILD_ROOT" \
    find "$LEAN_ROOT" "$DOCS_ROOT" \
      -type f \( -name '*.lean' -o -name '*.md' -o -name '*.txt' \) \
      -print
  else
    #~ find "$LEAN_ROOT" "$BUILD_ROOT" \
    find "$LEAN_ROOT" \
      -type f \( -name '*.lean' -o -name '*.md' -o -name '*.txt' \) \
      -print
  fi
} | sort | while IFS= read -r file; do
  grep -nE "$D_PATTERN" "$file" 2>/dev/null | sed "s|^|$file:|"
done > "$MARKERS_OUT"

echo "== Audit theorem/lemma global =="
find "$LEAN_ROOT" -type f -name '*.lean' -print | sort | while IFS= read -r file; do
  grep -nE "$THEOREM_PATTERN" "$file" 2>/dev/null | sed "s|^|$file:|"
done > "$ALL_THEOREMS_OUT"

echo "== Extraction imports Frozen =="
awk '
  /^import CouretUnification\./ {
    print $2
  }
' "$FROZEN_FILE" | sort -u > "$FROZEN_IMPORTS_OUT"

echo "== Audit theorem/lemma Frozen =="
: > "$FROZEN_THEOREMS_OUT"

while IFS= read -r module; do
  path="$ROOT/lean/$(printf '%s' "$module" | sed 's|\.|/|g').lean"

  if [ -f "$path" ]; then
    grep -nE "$THEOREM_PATTERN" "$path" 2>/dev/null | sed "s|^|$path:|" >> "$FROZEN_THEOREMS_OUT"
  else
    echo "WARN missing import path: $module -> $path" >> "$FROZEN_THEOREMS_OUT"
  fi
done < "$FROZEN_IMPORTS_OUT"

MARKERS_COUNT="$(wc -l < "$MARKERS_OUT" | tr -d ' ')"
ALL_THEOREMS_COUNT="$(wc -l < "$ALL_THEOREMS_OUT" | tr -d ' ')"
FROZEN_IMPORTS_COUNT="$(wc -l < "$FROZEN_IMPORTS_OUT" | tr -d ' ')"
FROZEN_THEOREMS_COUNT="$(grep -cE "$THEOREM_PATTERN" "$FROZEN_THEOREMS_OUT" 2>/dev/null || true)"

{
  echo "# Audit candidats [D]"
  echo
  echo "Racine : $ROOT"
  echo
  echo "## Comptages bruts"
  echo
  echo "- Marqueurs documentaires [D]/proved : $MARKERS_COUNT"
  echo "- Theorem/lemma Lean globaux         : $ALL_THEOREMS_COUNT"
  echo "- Imports Frozen                     : $FROZEN_IMPORTS_COUNT"
  echo "- Theorem/lemma dans Frozen          : $FROZEN_THEOREMS_COUNT"
  echo
  echo "## Fichiers produits"
  echo
  echo "- $MARKERS_OUT"
  echo "- $ALL_THEOREMS_OUT"
  echo "- $FROZEN_IMPORTS_OUT"
  echo "- $FROZEN_THEOREMS_OUT"
  echo
  echo "## Note doctrinale"
  echo
  echo "Ces nombres sont des indicateurs d'audit, pas un registre scientifique."
  echo "Un theorem Lean technique ne vaut pas automatiquement claim [D]."
  echo "Un claim [D] doit etre inscrit manuellement dans un registre relu."
} > "$SUMMARY_OUT"

cat "$SUMMARY_OUT"
