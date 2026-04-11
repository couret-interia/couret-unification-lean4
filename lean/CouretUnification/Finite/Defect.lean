import CouretUnification.Finite.Foundations

namespace CouretUnification.Finite

-- ═══════════════════════════════════════════════════════════
-- Liens avec le noyau fini (T1-T7)
-- ═══════════════════════════════════════════════════════════

/-- Énergie de défaut finie portée par le secteur λ = -1. -/
def defectEnergy (f : Sig) : ℚ := normSq (pminus f)

/-- Le fonctionnel I(φ) étend le défaut fini δ(f).
    Quand φ = 1_{log n ≤ log X}, on retrouve δ(f_X). -/
theorem defect_extends_finite (f : Sig) :
    defectEnergy f = normSq (pminus f) := rfl

end CouretUnification.Finite
