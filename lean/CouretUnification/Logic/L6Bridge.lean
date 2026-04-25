/-
# CouretUnification/Logic/L6Bridge.lean

## Rôle (refactoré v35.8.6)
Pont définitionnel entre les types opaques de `L6Interface` et les
définitions effectives de `L6Analytic`. Expose les grandeurs
asymptotiques `Aarch`, `Ztot`, `eps` ainsi que les contrats de
décroissance `L6RatioEstimate` et `ZtotPositiveEventually`.

## Architecture v35.8.6 (changement majeur)

AVANT v35.8.6 :
```lean
opaque Aarch (χ : PrimitiveCharacter) (T : ℝ) : ℝ
```
Conséquence : `Aarch_bridge : Aarch χ T = Aarch_effective χ T`
était structurellement INCLOSABLE (un opaque sans corps n'a aucun
contenu auquel le réduire). Cette dette était cachée derrière un
sorry tagué [BRIDGE / DEFINITIONAL].

APRÈS v35.8.6 :
```lean
noncomputable def Aarch := L6Analytic.Aarch_effective
```
Conséquence : `Aarch_bridge` se prouve par `rfl`. Plus aucun sorry
de type BRIDGE dans le projet.

## Statut (v35.8.6)
- Layer    : Logic
- Status   : proved
- Sorry    : 0
- RHClaimed : false

## Remarque doctrinale
Cette refactoration ne change rien au contenu mathématique. Elle
réalise simplement, au niveau du système de types, le lien que la
v35.8.5 ne pouvait que documenter en commentaires. L'invariant
`RHClaimed = false` est strictement préservé.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CouretUnification.Logic.L6Interface
import CouretUnification.Logic.L6Analytic
import CouretUnification.Meta.Doctrine

namespace CouretUnification
namespace Logic
namespace L6Bridge

open CouretUnification.Logic.L6Interface
open Real

/-! ## Section 1 — Re-export des types opaques

    On re-expose `PrimitiveCharacter`, `χ.a` et `χ.IsEven` sous le
    namespace `L6Bridge` pour préserver la compatibilité avec les
    fichiers consommateurs (`L6RatioEstimateDerived`, etc.) qui
    importaient historiquement depuis `L6Bridge`. -/

/-- Re-export du type opaque de caractère. -/
abbrev PrimitiveCharacter := L6Interface.PrimitiveCharacter

/-! ## Section 2 — Grandeurs asymptotiques (alias définitionnels)

    Les grandeurs `Aarch` et `Ztot` sont définies comme aliases
    DIRECTS des définitions effectives de `L6Analytic`. C'est le
    cœur du refactoring v35.8.6 : ce qui était auparavant une
    `opaque` non réductible devient un `def` réductible par `rfl`. -/

/-- Contribution archimédienne le long de la droite critique `σ = 1/2`.

    Définition v35.8.6 : alias direct de `L6Analytic.Aarch_effective`.
    Cette définition n'a aucun contenu autre que celui de
    `Aarch_effective`. -/
noncomputable def Aarch (χ : PrimitiveCharacter) (T : ℝ) : ℝ :=
  L6Analytic.Aarch_effective χ T

/-- Comptage total des ordonnées spectrales jusqu'à la hauteur `T`.

    Définition v35.8.6 : alias direct de `L6Analytic.Ztot_effective`. -/
noncomputable def Ztot (χ : PrimitiveCharacter) (T : ℝ) : ℝ :=
  L6Analytic.Ztot_effective χ T

/-- Erreur asymptotique résiduelle du ratio archimédien.

    Définie par `Aarch(χ,T) = (1/2 + eps(χ,T)) * Ztot(χ,T)`.

    Le branchement `if Ztot = 0 then 0 else ...` traite proprement
    le cas dégénéré (avant le premier zéro non trivial). Pour
    `T ≥ T₀` avec `T₀ ≥ 18`, on a `Ztot > 0` (cf. `Ztot_effective_eventually_positive`)
    et la branche utile est sélectionnée. -/
noncomputable def eps (χ : PrimitiveCharacter) (T : ℝ) : ℝ :=
  if Ztot χ T = 0 then 0
  else Aarch χ T / Ztot χ T - 1 / 2

/-! ## Section 3 — Théorèmes de raccord (par rfl)

    Ces deux théorèmes établissent l'égalité formelle entre les
    grandeurs `Aarch` / `Ztot` exposées par `L6Bridge` et leurs
    définitions effectives dans `L6Analytic`.

    En v35.8.6, ces théorèmes sont prouvables par `rfl` car
    `Aarch` et `Ztot` sont DÉFINIS comme aliases directs. AUCUN sorry,
    AUCUN axiome. -/

/-- Raccord définitionnel : `Aarch` coïncide avec `Aarch_effective`.

    Preuve par `rfl` rendue possible par le refactoring v35.8.6. -/
theorem Aarch_bridge :
    ∀ χ : PrimitiveCharacter, ∀ T : ℝ,
      Aarch χ T = L6Analytic.Aarch_effective χ T := by
  intro χ T
  rfl

/-- Raccord définitionnel : `Ztot` coïncide avec `Ztot_effective`.

    Preuve par `rfl` rendue possible par le refactoring v35.8.6. -/
theorem Ztot_bridge :
    ∀ χ : PrimitiveCharacter, ∀ T : ℝ,
      Ztot χ T = L6Analytic.Ztot_effective χ T := by
  intro χ T
  rfl

/-! ## Section 4 — Contrats asymptotiques

    Ces deux prédicats expriment les propriétés que
    `L6RatioEstimateDerived` doit prouver, en consommant les
    théorèmes analytiques de `L6Analytic` et les bridges ci-dessus. -/

/-- Contrat de décroissance asymptotique du ratio archimédien.

    `|eps χ T| ≤ C / log T` pour `T` assez grand. -/
def L6RatioEstimate (χ : PrimitiveCharacter) : Prop :=
  ∃ T₀ : ℝ, ∃ C : ℝ, 0 < C ∧ 1 < T₀ ∧
    ∀ T : ℝ, T₀ ≤ T → |eps χ T| ≤ C / Real.log T

/-- Contrat de positivité éventuelle : il existe une hauteur `T₀`
    au-delà de laquelle le comptage `Ztot` est strictement positif. -/
def ZtotPositiveEventually (χ : PrimitiveCharacter) : Prop :=
  ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → 0 < Ztot χ T

/-! ## Section 5 — Identité doctrinale -/

open CouretUnification.Meta

/-- Identité du fichier L6Bridge (v35.8.6, refactoré).

    Aucun sorry. Les théorèmes `Aarch_bridge` et `Ztot_bridge` sont
    désormais prouvés par `rfl`. -/
def fileIdentity : FileIdentity where
  filename   := "CouretUnification/Logic/L6Bridge.lean"
  layer      := Layer.B
  status     := Status.proved
  sorryCount := 0
  rhClaimed  := false

end L6Bridge
end Logic
end CouretUnification
