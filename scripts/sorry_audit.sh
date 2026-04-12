#!/bin/bash
# sorry_audit.sh — Audit des sorry et axiomes dans le pack Lean
# Usage: cd lean/ && bash ../scripts/sorry_audit.sh

LEAN_DIR="${1:-.}"

echo "╔════════════════════════════════════════════════════════════╗"
echo "║  AUDIT SORRY / AXIOME — Pack Lean Couret-Unification       ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""

echo "━━━ SORRY (hors sorryCount/commentaires) ━━━"

SORRY_LINES=$(
  find "$LEAN_DIR" -type f -name "*.lean" -print0 |
  while IFS= read -r -d '' file; do
    awk -v file="$file" '
      function has_sorry_token(text) {
        return text ~ /(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)/
      }

      function emit_if_match(text, line_no) {
        if (has_sorry_token(text)) {
          print file ":" line_no ":" text
        }
      }

      BEGIN {
        block = 0
        in_string = 0
        escape = 0
      }

      {
        line = $0
        out = ""
        i = 1
        n = length(line)

        while (i <= n) {
          two = substr(line, i, 2)
          ch  = substr(line, i, 1)

          if (block > 0) {
            if (!in_string && two == "/-") {
              block++
              i += 2
            } else if (!in_string && two == "-/") {
              block--
              i += 2
            } else if (ch == "\"" && !escape) {
              in_string = !in_string
              i++
            } else {
              escape = (in_string && ch == "\\" && !escape)
              if (!(in_string && ch == "\\" && !escape)) escape = 0
              i++
            }
          } else {
            if (!in_string && two == "--") {
              break
            } else if (!in_string && two == "/-") {
              block++
              i += 2
            } else if (ch == "\"" && !escape) {
              in_string = !in_string
              i++
            } else {
              if (!in_string) out = out ch
              escape = (in_string && ch == "\\" && !escape)
              if (!(in_string && ch == "\\" && !escape)) escape = 0
              i++
            }
          }
        }

        emit_if_match(out, FNR)
      }
    ' "$file"
  done
)

printf '%s\n' "$SORRY_LINES"
SORRY_COUNT=$(printf '%s\n' "$SORRY_LINES" | sed '/^$/d' | wc -l | tr -d ' ')
echo "  Total sorry: $SORRY_COUNT"
echo ""

echo "━━━ AXIOM ━━━"
AXIOM_COUNT=$(grep -rn "^axiom " "$LEAN_DIR" --include="*.lean" \
    | grep -c "axiom" 2>/dev/null || echo 0)
grep -rn "^axiom " "$LEAN_DIR" --include="*.lean" || true
echo "  Total axiom: $AXIOM_COUNT"
echo ""

echo "━━━ RHClaimed GUARD ━━━"
grep -rn "RHClaimed" "$LEAN_DIR" --include="*.lean" || true
echo ""

echo "━━━ Prop := True (potentiellement suspect) ━━━"
grep -rn "Prop := True" "$LEAN_DIR" --include="*.lean" | head -20 || true
PROP_TRUE=$(grep -rc "Prop := True" "$LEAN_DIR" --include="*.lean" 2>/dev/null \
    | awk -F: '{s+=$2}END{print s}' || echo 0)
echo "  Total Prop := True: $PROP_TRUE"
echo ""

echo "━━━ VERDICT ━━━"
if [ "$SORRY_COUNT" -le 1 ] && [ "$AXIOM_COUNT" -le 1 ]; then
    echo "  ✓ Conforme: ≤1 sorry, ≤1 axiom"
else
    echo "  ✗ Non conforme: $SORRY_COUNT sorry, $AXIOM_COUNT axiom"
fi
