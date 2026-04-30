#!/usr/bin/env bash
#
# audit_v36.1.sh
# Audit automatique du paquet v36.1 : Frozen Core + Active Extensions.
#
# Vérifie séparément :
#   · Frozen Core (CouretUnification/Logic/, CouretUnification/AnalyticHorizon/)
#     — exige 0 sorry, 0 axiome, flags à false
#   · Active Extensions (CouretUnification/Active/)
#     — exige 0 sorry, 0 axiome (cible Frozen-eligible),
#       mais importations Mathlib autorisées
#
# Usage : cd v36.1/ && bash audit_v36.1.sh

set -u
cd "$(dirname "$0")"

errors=0

echo "═══════════════════════════════════════════════════════════════════"
echo " Audit v36.1 = v36.0 Frozen Core + v36.1 Active Extensions"
echo "═══════════════════════════════════════════════════════════════════"

check_layer() {
  local label="$1"
  local path="$2"
  local section_errors=0

  echo
  echo "── $label : $path ──"

  if [ ! -d "$path" ]; then
    echo "  ✗ Répertoire manquant"
    errors=$((errors+1))
    return
  fi

  # Strip Lean comments before grep :
  #   · /- ... -/   (blocs, peuvent être multi-lignes)
  #   · -- ...      (fin-de-ligne)
  # On utilise awk pour marquer et supprimer les lignes de commentaire.
  local stripped
  stripped=$(find "$path" -name "*.lean" -exec cat {} + | awk '
    BEGIN { in_block = 0 }
    {
      line = $0
      # Gérer fin de bloc /- ... -/
      if (in_block) {
        idx = index(line, "-/")
        if (idx > 0) {
          line = substr(line, idx + 2)
          in_block = 0
        } else {
          next
        }
      }
      # Gérer début de bloc /- (possible plusieurs sur une ligne)
      while ((idx = index(line, "/-")) > 0) {
        pre = substr(line, 1, idx - 1)
        rest = substr(line, idx + 2)
        close_idx = index(rest, "-/")
        if (close_idx > 0) {
          line = pre substr(rest, close_idx + 2)
        } else {
          line = pre
          in_block = 1
          break
        }
      }
      # Retirer commentaires de fin de ligne
      cidx = index(line, "--")
      if (cidx > 0) line = substr(line, 1, cidx - 1)
      print line
    }
  ')

  local sorry_c axiom_c admit_c
  sorry_c=$(echo "$stripped" | grep -cE '\bsorry\b' || true)
  axiom_c=$(echo "$stripped" | grep -cE '^\s*axiom\s' || true)
  admit_c=$(echo "$stripped" | grep -cE '\badmit\b' || true)

  echo "  sorry (hors commentaires) : $sorry_c  (requis : 0)"
  echo "  axiom                     : $axiom_c  (requis : 0)"
  echo "  admit                     : $admit_c  (requis : 0)"

  if [ "$sorry_c" -ne 0 ] || [ "$axiom_c" -ne 0 ] || [ "$admit_c" -ne 0 ]; then
    echo "  ✗ Anomalies détectées dans $label"
    section_errors=$((section_errors+1))
  else
    echo "  ✓ $label propre (cible Frozen-éligible)"
  fi

  local file_count
  file_count=$(find "$path" -name "*.lean" | wc -l)
  local line_count
  line_count=$(find "$path" -name "*.lean" -exec cat {} \; | wc -l)
  echo "  Fichiers : $file_count   Lignes totales : $line_count"

  errors=$((errors + section_errors))
}

# ── 1. Frozen Core (v36.0) ──
check_layer "Frozen Core Logic"         "CouretUnification/Logic"
check_layer "Frozen AnalyticHorizon"    "CouretUnification/AnalyticHorizon"

# ── 2. Active Extensions (v36.1) ──
check_layer "Active Extensions"         "CouretUnification/Active"

# ── 3. Flags doctrinaux (tous les namespaces) ──
echo
echo "── Flags doctrinaux (tous ClaimedXxx doivent être à false) ──"
for flag in RHClaimed HilbertPolyaClaimed CandidateCClaimed ExplicitFormulaClaimedAsClosed; do
  line=$(grep -rhE "def ${flag}\s*:\s*Bool" CouretUnification --include="*.lean" 2>/dev/null | head -1)
  if [ -z "$line" ]; then
    echo "  ✗ MANQUANT : $flag"
    errors=$((errors+1))
  else
    if echo "$line" | grep -q ":= false"; then
      echo "  ✓ $flag := false"
    else
      echo "  ✗ ANOMALIE : $flag n'est pas à false"
      errors=$((errors+1))
    fi
  fi
done

# ── 4. Théorèmes attendus ──
echo
echo "── Théorèmes attendus ──"
expected_theorems=(
  # Frozen (v36.0)
  "primeTerm_eventually_zero:Frozen"
  "no_RH_from_explicit_formula_bridge:Frozen"
  "reflectionEdges_card_eq_6:Frozen"
  "R_A8_eq_6:Frozen"
  # Active (v36.1)
  "primeSide_vanishes_past_cutoff:Active"
  "enriched_does_not_prove_riemann_weil:Active"
  "enriched_does_not_prove_hilbert_polya:Active"
)

for entry in "${expected_theorems[@]}"; do
  th="${entry%:*}"
  layer="${entry#*:}"
  if grep -rnqE "^theorem $th" CouretUnification --include="*.lean" 2>/dev/null; then
    echo "  ✓ [$layer] $th"
  else
    echo "  ✗ MANQUANT [$layer] : $th"
    errors=$((errors+1))
  fi
done

# ── 5. Règle d'importation : Frozen n'importe JAMAIS Active ──
echo
echo "── Règle de sécurité : Frozen n'importe pas Active ──"
illegal_imports=$(grep -rn "^import CouretUnification.Active" \
  CouretUnification/Logic CouretUnification/AnalyticHorizon \
  --include="*.lean" 2>/dev/null)
if [ -n "$illegal_imports" ]; then
  echo "  ✗ VIOLATION : importations illégales détectées"
  echo "$illegal_imports"
  errors=$((errors+1))
else
  echo "  ✓ Frozen ne dépend pas d'Active (doctrine respectée)"
fi

# ── Verdict final ──
echo
echo "═══════════════════════════════════════════════════════════════════"
if [ "$errors" -eq 0 ]; then
  echo " VERDICT : ✓ Audit passé (0 anomalie)"
  echo " Frozen Core v36.0 + Active Extensions v36.1 conformes à la doctrine."
  echo " Pour Bernard."
  echo "═══════════════════════════════════════════════════════════════════"
  exit 0
else
  echo " VERDICT : ✗ $errors anomalie(s) détectée(s)"
  echo "═══════════════════════════════════════════════════════════════════"
  exit 1
fi
