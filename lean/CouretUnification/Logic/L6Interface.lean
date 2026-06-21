/-
# CouretUnification/Logic/L6Interface.lean

## Rôle
Interface MINIMALE du pont L6. Contient uniquement les types opaques
fondamentaux (PrimitiveCharacter et sa parité). Les grandeurs analytiques
Aarch et Ztot sont définies dans L6Bridge comme aliases sur les
définitions effectives de L6Analytic.

## Architecture v35.8.6
Refactoring B : séparation L6Interface / L6Analytic / L6Bridge.

```
L6Interface (types seulement)
    ↑
    ├── L6Analytic   (Aarch_effective, Ztot_effective + lemmes)
    │       ↑
    └── L6Bridge     (Aarch := Aarch_effective, bridges par rfl)
            ↑
            L6RatioEstimateDerived
```

Cette architecture rend `Aarch_bridge` et `Ztot_bridge` **provables
par rfl**, sans aucun axiome ni sorry de type DEFINITIONAL.

## Statut
- Layer    : Logic (interface)
- Status   : proved (pures déclarations de types)
- Sorry    : 0
- RHClaimed : false
-/

import Mathlib.Data.Real.Basic

namespace CouretUnification
namespace Logic
namespace L6Interface

/-! ## Section 1 — Type opaque fondamental -/

/-- Caractère de Dirichlet primitif (placeholder opaque).

    La structure concrète sera fournie par
    `Mathlib.NumberTheory.DirichletCharacter` au moment du raccord
    effectif (v36). Pour l'instant, on n'expose que les invariants
    nécessaires aux calculs archimédiens. -/
opaque PrimitiveCharacter : Type

/-- Parité du caractère.

    Convention : vaut 0 pour un caractère pair (χ(-1) = +1), vaut 1
    pour un caractère impair (χ(-1) = -1). C'est le paramètre `a` de
    la fonction complétée ξ(s,χ) = π^(-(s+a)/2) Γ((s+a)/2) L(s,χ). -/
opaque PrimitiveCharacter.a (χ : PrimitiveCharacter) : ℝ

/-- Prédicat de parité : `χ` est pair ssi `χ.a = 0`. -/
def PrimitiveCharacter.IsEven (χ : PrimitiveCharacter) : Prop :=
  χ.a = 0

end L6Interface
end Logic
end CouretUnification
