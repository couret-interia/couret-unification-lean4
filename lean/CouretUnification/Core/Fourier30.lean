import CouretUnification.Core.Characters30
import CouretUnification.Core.FiniteOperator
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open BigOperators

namespace CouretUnification.Core

noncomputable section

abbrev Signal30 := Vec

/-- Coefficient de Fourier fini associé au caractère `χ`. -/
def fourierCoeff (f : Signal30) (χ : CharIdx) : ℂ :=
  ∑ g : Idx, f g * star (character χ g)

/-- Transformée de Fourier finie, dans l'ordre documentaire gelé. -/
def finiteFourier (f : Signal30) : List ℂ :=
  documentaryCharacters.map (fun χ => fourierCoeff f χ)

lemma finiteFourier_length (f : Signal30) :
    (finiteFourier f).length = 8 := by
  simp [finiteFourier, documentaryCharacters_length]

/-- Le coefficient trivial du vecteur constant `1` vaut `8`. -/
lemma fourierCoeff_trivial_oneVec :
    fourierCoeff oneVec 0 = 8 := by
  norm_num [fourierCoeff, oneVec, character, characterEval,
            charCoord, residueCoord, c2Phase, c4Phase]

end

end CouretUnification.Core