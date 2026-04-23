/- CouretUnification/Logic/H3/FiniteSpectralAPI.lean
   API minimale au-dessus du noyau exact (V35.1 stricte)
   0 sorry. RHClaimed = false. -/
import CouretUnification.Core.CenteredSpace30
import CouretUnification.Core.Characters30Bridge
import CouretUnification.Core.CayleyG30

open scoped BigOperators

namespace CouretUnification.Logic.H3

open CouretUnification.Core

abbrev KernelFn := FunG30
abbrev negOneG30 : G30 := u29

theorem negOne_sq : negOneG30 * negOneG30 = 1 := by
  simpa [negOneG30] using u29_sq

def charFn (χ : CharIdx) : FunG30 := fun g => charOnG30 χ g

structure FiniteSpectralAPI where
  kernel : KernelFn
  chars  : Finset CharIdx := Finset.univ

namespace FiniteSpectralAPI

def TCset (_api : FiniteSpectralAPI) : Finset G30 := TC_G30
def negOne (_api : FiniteSpectralAPI) : G30 := negOneG30
noncomputable def centeredSpace (_api : FiniteSpectralAPI) : Submodule ℂ FunG30 := H_centered
noncomputable def constantLine (_api : FiniteSpectralAPI) : Submodule ℂ FunG30 := trivialLine
def evalChar (_api : FiniteSpectralAPI) (χ : CharIdx) : FunG30 := charFn χ

end FiniteSpectralAPI

def canonicalAPI (K : FunG30) : FiniteSpectralAPI := { kernel := K }

end CouretUnification.Logic.H3
