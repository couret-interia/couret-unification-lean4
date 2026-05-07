#!/bin/bash
# scripts/audit_structure_collisions.sh
# v38.0+ : détecte les collisions de noms de structures dans un même namespace
set -e
ROOT="lean/CouretUnification"
echo "[audit] détection collisions de structures dans $ROOT"
collisions=$(grep -rn "^structure " "$ROOT" --include="*.lean" 2>/dev/null | \
  awk -F': *' '{print $2}' | awk '{print $1, $2}' | sort | uniq -c -f1 | \
  awk '$1 > 1 {print $0}')
if [ -n "$collisions" ]; then
  echo "[audit] ✗ collisions détectées :"
  echo "$collisions"
  exit 1
fi
echo "[audit] ✓ aucune collision"
