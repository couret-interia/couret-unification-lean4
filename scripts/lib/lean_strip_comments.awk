# scripts/lib/lean_strip_comments.awk
#
# Bibliothèque awk : strip Lean comments and string literals.
#
# Entrée : fichiers .lean, lus via awk -f ... fichier1 fichier2 ...
# Sortie : pour chaque ligne contenant du code non-commenté,
#          imprime "FILENAME:LINENO:CODE_ONLY".
#          Les lignes entièrement vides après filtrage sont omises.
#
# Gestion :
#   - "..." chaînes : ignorées (le contenu n'apparaît pas dans CODE_ONLY)
#   - -- commentaire jusqu'en fin de ligne : ignoré
#   - /- ... -/ commentaires blocs (imbriqués) : ignorés
#   - \\ escape dans les strings : géré
#
# Usage typique :
#   find lean -type f -name "*.lean" -print0 \
#     | xargs -0 awk -f scripts/lib/lean_strip_comments.awk \
#     | grep -E "(^|[^[:alnum:]_])RHClaimed([^[:alnum:]_]|$)"
#
# Since CouretUnification v38.4.10

BEGIN {
  block = 0
  in_string = 0
  escape = 0
}

# Reset l'état à chaque nouveau fichier
FNR == 1 {
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
      if (!in_string && two == "/-") { block++; i += 2 }
      else if (!in_string && two == "-/") { block--; i += 2 }
      else if (ch == "\"" && !escape) { in_string = !in_string; i++ }
      else {
        escape = (in_string && ch == "\\" && !escape)
        if (!(in_string && ch == "\\" && !escape)) escape = 0
        i++
      }
    } else {
      if (!in_string && two == "--") { break }
      else if (!in_string && two == "/-") { block++; i += 2 }
      else if (ch == "\"" && !escape) { in_string = !in_string; i++ }
      else {
        if (!in_string) out = out ch
        escape = (in_string && ch == "\\" && !escape)
        if (!(in_string && ch == "\\" && !escape)) escape = 0
        i++
      }
    }
  }

  # Émettre seulement si la ligne nettoyée a du contenu non-blanc
  if (out !~ /^[[:space:]]*$/) {
    print FILENAME ":" FNR ":" out
  }
}
