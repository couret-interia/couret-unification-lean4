/-
  Couret-Unification — v38

  TraceObject.lean

  v35.9.0 → v38 :
    Anciennement, ce fichier déclarait `structure TestPair { g, ghat,
    admissible }` en doublon de `TestPair.lean` (v35.9.1, version
    canonique avec `compactSupport_g`). Conflit `TestPair.ctorIdx`.

    Désormais, on importe la version canonique. Les champs `ghat` et
    `admissible` ne sont pas réintroduits : ils n'ont aucun
    consommateur dans la couche Frozen. S'ils deviennent nécessaires
    plus tard, créer une extension `TestPairFourier extends TestPair`.
-/

import CouretUnification.Logic.ExplicitFormula.StatusFlags
import CouretUnification.Logic.ExplicitFormula.TestPair

namespace CouretUnification.Logic.ExplicitFormula

/-- A formal side of an explicit-formula identity. -/
structure FormulaSide where
  value : TestPair → ℂ

/--
Neutral typed receptacle for the future Riemann-Weil trace identity.

No analytic equality is proved here.
This object is only the formal target into which PrimeSide,
ZeroSide, ArchimedeanSide and Det2Side may later map.
-/
structure TraceObject where
  value : TestPair → ℂ

end CouretUnification.Logic.ExplicitFormula
