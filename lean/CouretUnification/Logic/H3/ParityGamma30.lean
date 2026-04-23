/- CouretUnification/Logic/H3/ParityGamma30.lean
   Couche C1-minimale branchée sur u29 (V35.1 stricte)
   0 sorry. RHClaimed = false. -/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import CouretUnification.Logic.H3.FiniteSpectralAPI

namespace CouretUnification.Logic.H3

open CouretUnification.Core

/-- Parité lue via le bit C₂ de `charCoord`. -/
def parityBit (χ : CharIdx) : Fin 2 := (charCoord χ).1

def charIsEven (χ : CharIdx) : Prop := parityBit χ = 0
def charIsOdd (χ : CharIdx) : Prop := parityBit χ = 1

theorem parity_split (χ : CharIdx) : charIsEven χ ∨ charIsOdd χ := by
  unfold charIsEven charIsOdd parityBit
  rcases charCoord χ with ⟨m, n⟩
  fin_cases m
  · left
    rfl
  · right
    rfl

/-- Exposant de parité : 0 pour les caractères pairs, 1 pour les impairs. -/
noncomputable def parityExponent (χ : CharIdx) : ℂ :=
  if parityBit χ = 0 then 0 else 1

/-- Facteur gamma local attaché à un caractère modulo 30. -/
noncomputable def GammaFactor30 (χ : CharIdx) (s : ℂ) : ℂ :=
  (Complex.ofReal Real.pi) ^ (-(s / 2)) *
    Complex.Gamma ((s + parityExponent χ) / 2)

/-- Version locale minimale du facteur complété sur un ensemble fini de caractères. -/
noncomputable def LambdaLocal
    (D : ℂ → ℂ) (L : CharIdx → ℂ → ℂ)
    (chars : Finset CharIdx) (s : ℂ) : ℂ :=
  D s * chars.prod (fun χ => GammaFactor30 χ s * L χ s)

end CouretUnification.Logic.H3