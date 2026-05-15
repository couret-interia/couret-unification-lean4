/-
  CouretUnification.Logic.ExplicitFormula.TraceObject
  ════════════════════════════════════════════════════════════════════
  Réceptacle typé pour les côtés formels de la future formule explicite.

  Ce fichier ne prouve aucune identité analytique. Il fournit seulement
  deux objets d'interface :

    • `FormulaSide`  : un côté formel évalué sur une fonction test canonique ;
    • `TraceObject`  : une cible neutre pour une future identité de trace
                       de type Riemann–Weil.

  Refactor v35.9.0 → v38 :
    Anciennement, ce fichier déclarait en doublon :

      structure TestPair { g, ghat, admissible }

    alors que `TestPair.lean` contient déjà la version canonique v35.9.1,
    avec `compactSupport_g`. Ce doublon provoquait le conflit :

      TestPair.ctorIdx

    Désormais, ce fichier importe la version canonique de `TestPair`.

  Choix v38 :
    Les champs `ghat` et `admissible` ne sont pas réintroduits ici, car ils
    n'ont aucun consommateur dans la couche Frozen.

    S'ils deviennent nécessaires plus tard, créer une extension séparée :

      TestPairFourier extends TestPair

    plutôt que de modifier ou dupliquer `TestPair`.

  Garde-fous :
    • aucune formule explicite globale n'est prouvée ici ;
    • aucune égalité PrimeSide = ZeroSide n'est affirmée ;
    • aucune identification Det2/ξ n'est exportée ;
    • aucune conséquence RH n'est revendiquée.

  Statut :
    interface logique / Frozen-safe ;
    point d'ancrage typé pour PrimeSide, ZeroSide, ArchimedeanSide
    et Det2Side.
-/

import CouretUnification.Logic.ExplicitFormula.StatusFlags
import CouretUnification.Logic.ExplicitFormula.TestPair

namespace CouretUnification.Logic.ExplicitFormula

/-- Un côté formel d'une identité de formule explicite. -/
structure FormulaSide where
  value : TestPair → ℂ

/--
Réceptacle typé neutre pour la future identité de trace de Riemann–Weil.

Aucune égalité analytique n'est prouvée ici.
Cet objet est seulement la cible formelle vers laquelle `PrimeSide`,
`ZeroSide`, `ArchimedeanSide` et `Det2Side` pourront se projeter plus tard.
-/
structure TraceObject where
  value : TestPair → ℂ

end CouretUnification.Logic.ExplicitFormula
