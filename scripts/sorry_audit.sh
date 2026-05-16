#!/bin/bash
# sorry_audit.sh — Audit des sorry et axiomes dans le pack Lean
# Usage: cd lean/ && bash ../scripts/sorry_audit.sh

# Note v38.4.10 : le parseur "strip Lean comments and strings" pour
# SORRY, Prop := True, RHClaimed est centralisé dans :
# scripts/lib/lean_strip_comments.awk.
# Pour ajouter une nouvelle section : une ligne grep sur $CLEAN_CODE.

LEAN_DIR="${1:-.}"

# Lancement depuis lean/ (voir Usage ci-dessus). D'où ceci
# Chemin absolu de la lib basé sur l'emplacement du script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_AWK="$SCRIPT_DIR/lib/lean_strip_comments.awk"

# Helper interne — un seul find + un seul awk pour toutes les sections
get_clean_code() {
  find "$LEAN_DIR" -type f -name "*.lean" -print0 \
    | xargs -0 awk -f "$LIB_AWK"
}

# Cache une seule fois pour les 3 sections (gain de perfs)
CLEAN_CODE=$(get_clean_code)

echo "╔═══════════════════════════════════════════════════════════════════╗"
echo "║  AUDIT SORRY / AXIOME / RHCLAIMED — Pack Lean Couret-Unification  ║"
echo "╚═══════════════════════════════════════════════════════════════════╝"
echo ""

echo "━━━ SORRY (hors sorryCount/commentaires) ━━━"
SORRY_LINES=$(printf '%s\n' "$CLEAN_CODE" | grep -E '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' || true)
printf '%s\n' "$SORRY_LINES"
SORRY_COUNT=$(printf '%s\n' "$SORRY_LINES" | sed '/^$/d' | wc -l | tr -d ' ')
echo "  Total sorry: $SORRY_COUNT"
echo ""

echo "━━━ AXIOM ━━━"
# Note : axiom n'a pas besoin du parseur (regex simple sur début de ligne)
AXIOM_COUNT=$(grep -rn "^axiom " "$LEAN_DIR" --include="*.lean" | wc -l)
grep -rn "^axiom " "$LEAN_DIR" --include="*.lean" || true
echo "  Total axiom: $AXIOM_COUNT"
echo ""

echo "━━━ RHCLAIMED GUARD (hors commentaires) ━━━"
RHCLAIMED_LINES=$(printf '%s\n' "$CLEAN_CODE" | grep -E '(^|[^[:alnum:]_])RHClaimed([^[:alnum:]_]|$)' || true)
printf '%s\n' "$RHCLAIMED_LINES"
RHCLAIMED_COUNT=$(printf '%s\n' "$RHCLAIMED_LINES" | sed '/^$/d' | wc -l | tr -d ' ')
echo "  Total RHClaimed: $RHCLAIMED_COUNT"
echo ""

echo "━━━ Prop := True (potentiellement suspect) ━━━"
TRUE_LINES=$(printf '%s\n' "$CLEAN_CODE" | grep "Prop := True" || true)
printf '%s\n' "$TRUE_LINES"
TRUE_COUNT=$(printf '%s\n' "$TRUE_LINES" | sed '/^$/d' | wc -l | tr -d ' ')
echo "  Total Prop := True: $TRUE_COUNT"
echo ""

echo "━━━ VERDICT ━━━"
if [ "$SORRY_COUNT" -le 1 ] && [ "$AXIOM_COUNT" -le 1 ]; then
    echo "  ✓ Conforme: ≤1 sorry, ≤1 axiom"
else
    echo "  ✗ Non conforme: $SORRY_COUNT sorry, $AXIOM_COUNT axiom"
fi
