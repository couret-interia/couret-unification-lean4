import Mathlib
import CouretUnification.Logic.ExplicitFormula.TraceObject

namespace CouretUnification.Logic.ExplicitFormula

/--
Abstract zero data.

This does not assert that the zeros are the true zeros of ζ.
It only packages a discrete spectral set with ordinates γ.
-/
structure ZeroShellData where
  Zero : Type
  gamma : Zero → ℝ
  zerosInShell : ℕ → Finset Zero
  shellBound : Prop

/--
Typed obligation for Riemann-von Mangoldt style shell control.

This remains an obligation, not a closed theorem in Frozen.
-/
structure ZeroCountingObligation where
  data : ZeroShellData
  boundWitness : data.shellBound

/-- Abstract ZeroSide contribution. -/
structure ZeroSide where
  side : FormulaSide
  counting : ZeroCountingObligation

end CouretUnification.Logic.ExplicitFormula
