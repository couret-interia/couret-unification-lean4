import Mathlib
import CouretUnification.Logic.ExplicitFormula.StatusFlags

namespace CouretUnification.Logic.ExplicitFormula

/-- Abstract test pair for the Riemann-Weil architecture. -/
structure TestPair where
  g : ℝ → ℂ
  ghat : ℝ → ℂ
  admissible : Prop

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
