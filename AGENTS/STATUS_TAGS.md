# Grammaire des statuts — Couret-Unification

Ces tags empêchent de mélanger preuve formelle, calcul fini, conjecture et lecture philosophique.

| Tag | Sens | Preuve attendue |
|---|---|---|
| `[L-verified]` | Module ou paquet compilé par Lean. | Commande `lake build ...` ou CI verte. |
| `[D-computational, finite]` | Résultat fini, exhaustif, calculatoire. | `native_decide`, énumération Lean, ou script reproductible. |
| `[T-theorem]` | Théorème prouvé formellement dans Lean. | Pas de `sorry`, pas d'`axiom`, pas d'hypothèse cachée. |
| `[S-speculative]` | Heuristique, analogie, conjecture, lecture philosophique. | Texte marqué comme non certifié. |
| `[X-blocked]` | Blocage de compilation, preuve ouverte, dépendance manquante. | Erreur ou trou identifié. |

## Règle de promotion

Un énoncé ne monte jamais de statut sans artefact correspondant : build, log, preuve Lean, script reproductible ou audit.

## Garde-fou central

Un calcul fini modulo 30 peut être `[D-computational, finite]`. Il ne devient pas une preuve globale de l'infinité des nombres premiers jumeaux, de l'infinité Sophie Germain, de RH, ni d'une loi asymptotique de distribution des nombres premiers.
