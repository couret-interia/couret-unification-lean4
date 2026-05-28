#!/bin/bash
# sorry_audit.sh — Audit global informatif des sorry, axiomes et gardes RHClaimed
# du dépôt avec un parseur local qui exclut les commentaires Lean des résultats
# Usage: cd lean/ && bash ../scripts/sorry_audit.sh

# Note v38.4.30 : ajout de *_MAX
# budgets des sorry et axiomes du dépôt à une version donnée.
# Une différence de comptage est possible avec "make build-all" :
# Lean peut regrouper plusieurs occurrences de `sorry` dans une seule déclaration,
# tandis que cet audit compte les occurrences sources après nettoyage.

# Note v38.4.10 : le parseur "strip Lean comments and strings" pour
# SORRY, Prop := True, RHClaimed est centralisé dans :
# scripts/lib/lean_strip_comments.awk.
# Pour ajouter une nouvelle section : une ligne grep sur $CLEAN_CODE.

SORRY_COUNT_MAX=19
AXIOM_COUNT_MAX=10

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

echo "━━━ SORRY (hors commentaires) ━━━"
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
if [ "$SORRY_COUNT" -le $SORRY_COUNT_MAX ] && [ "$AXIOM_COUNT" -le $AXIOM_COUNT_MAX ]; then
    echo "  ✓ Dans le budget global d'audit : sorry $SORRY_COUNT/$SORRY_COUNT_MAX, axiom $AXIOM_COUNT/$AXIOM_COUNT_MAX"
else
    echo "  ✗ Hors budget global d'audit : sorry $SORRY_COUNT/$SORRY_COUNT_MAX, axiom $AXIOM_COUNT/$AXIOM_COUNT_MAX"
fi
