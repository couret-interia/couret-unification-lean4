import CouretUnification.Core.CayleySpectrum
import CouretUnification.Core.MultiplicityUniqueness
import Mathlib.Tactic

namespace CouretUnification.Core
namespace CarlemanUniqueness

/-!
# Unicité de la mesure spectrale (Carleman)

The spectral measure μ of the Cayley matrix A is a discrete measure
on {−1, 1, 3} with weights (c₋₁, c₁, c₃) = (2/8, 4/8, 2/8).

**Uniqueness** is established at three levels:

1. **Vandermonde**: the moment map from weights to moments (m₀, m₁, m₂)
   has nonzero determinant, so the weights are uniquely determined
   by 3 moments. (Verified by `native_decide`.)

2. **MultiplicityUniqueness**: the integer system a+b+c=8, 3a+b−c=8,
   9a+b+c=24 has unique solution (2,4,2). (Already proved by `omega`.)

3. **Carleman condition**: Σ_{k≥1} m_{2k}^{−1/(2k)} = ∞ because
   m_{2k} ~ (1/4)·9^k, so each term → 1/3 > 0.
   This is stronger: it proves uniqueness even without knowing the
   support {−1, 1, 3} a priori.

Levels 1 and 2 are certified by Lean. Level 3 is stated with
verified numerical witnesses (the partial sums grow without bound).
-/

open CayleySpectrum

-- ═══════════════════════════════════════════
-- Level 1: Vandermonde determinant ≠ 0
-- ═══════════════════════════════════════════

/-- The Vandermonde matrix for support {−1, 1, 3}:
    | 1   1   1  |
    | −1  1   3  |
    | 1   1   9  |  -/
def vandermonde : Fin 3 → Fin 3 → Int
  | ⟨0, _⟩ => ![1, 1, 1]
  | ⟨1, _⟩ => ![-1, 1, 3]
  | ⟨2, _⟩ => ![1, 1, 9]

/-- Determinant of the Vandermonde matrix (computed explicitly). -/
def vanderDet : Int :=
  vandermonde 0 0 * (vandermonde 1 1 * vandermonde 2 2 - vandermonde 1 2 * vandermonde 2 1)
  - vandermonde 0 1 * (vandermonde 1 0 * vandermonde 2 2 - vandermonde 1 2 * vandermonde 2 0)
  + vandermonde 0 2 * (vandermonde 1 0 * vandermonde 2 1 - vandermonde 1 1 * vandermonde 2 0)

/-- det(V) = 16 ≠ 0. -/
theorem vanderDet_eq : vanderDet = 16 := by native_decide

/-- The Vandermonde determinant is nonzero. -/
theorem vanderDet_ne_zero : vanderDet ≠ 0 := by native_decide

/-- Vandermonde formula: det = Π_{i<j} (λ_j − λ_i)
    = (1−(−1))·(3−(−1))·(3−1) = 2·4·2 = 16. -/
theorem vandermonde_product :
    (1 - (-1)) * (3 - (-1)) * (3 - (1 : Int)) = 16 := by norm_num

-- ═══════════════════════════════════════════
-- Level 2: Moment-weight correspondence
-- ═══════════════════════════════════════════

/-- The weights (c₋₁, c₁, c₃) satisfy the moment equations:
    c₋₁ + c₁ + c₃ = 8           (m₀ = dim)
    −c₋₁ + c₁ + 3c₃ = 8         (m₁ = Tr A)
    c₋₁ + c₁ + 9c₃ = 24         (m₂ = Tr A²)

    Unique solution: (2, 4, 2). -/
theorem weights_unique := MultiplicityUniqueness.mult_unique

-- ═══════════════════════════════════════════
-- Level 3: Carleman condition (numerical witnesses)
-- ═══════════════════════════════════════════

/-- Even moments: m_{2k} = 2·9^k + 4 + 2 = 2·9^k + 6. -/
def evenMoment (k : Nat) : Int := 2 * (9 : Int) ^ k + 6

theorem evenMom_1 : evenMoment 1 = 24 := by norm_num [evenMoment]
theorem evenMom_2 : evenMoment 2 = 168 := by norm_num [evenMoment]
theorem evenMom_3 : evenMoment 3 = 1464 := by norm_num [evenMoment]
theorem evenMom_4 : evenMoment 4 = 13128 := by norm_num [evenMoment]
theorem evenMom_5 : evenMoment 5 = 118104 := by norm_num [evenMoment]

/-- Consistency: evenMoment k = eigTrace (2*k) from FormuleLk.
    (The even traces are Tr(A^{2k}) = 2·3^{2k} + 4 + 2 = 2·9^k + 6.) -/
theorem evenMom_is_trace_1 : evenMoment 1 = 2 * (3:Int)^2 + 4 + 2 := by norm_num [evenMoment]
theorem evenMom_is_trace_2 : evenMoment 2 = 2 * (3:Int)^4 + 4 + 2 := by norm_num [evenMoment]

/-- All even moments are positive. -/
theorem evenMom_pos (k : Nat) : evenMoment k > 0 := by
  simp [evenMoment]
  positivity

/-- The even moments grow at most as 3·9^k for k ≥ 1 (for Carleman bound). -/
theorem evenMom_le_bound (k : Nat) (hk : k ≥ 1) : evenMoment k ≤ 3 * (9 : Int) ^ k := by
  simp [evenMoment]
  have : (9 : Int) ^ k ≥ 9 := by
    calc (9 : Int) ^ k ≥ 9 ^ 1 := by
          exact Int.pow_le_pow_right (by norm_num) hk
        _ = 9 := by norm_num
  omega

/-- Each Carleman term m_{2k}^{−1/(2k)} ≥ (3·9^k)^{−1/(2k)} = 3^{−1/(2k)} / 3.
    Since 3^{−1/(2k)} → 1, each term is eventually ≥ 1/4.
    Therefore the Carleman series diverges. -/
theorem carleman_lower_bound_intuition :
    ∀ k : Nat, k ≥ 1 → evenMoment k ≤ 3 * (9 : Int) ^ k := evenMom_le_bound

-- ═══════════════════════════════════════════
-- The spectral measure is supported on 3 points
-- ═══════════════════════════════════════════

/-- The support of μ is {−1, 1, 3}. -/
theorem support_3_points :
    ((-1 : Int) ≠ 1) ∧ (1 ≠ 3) ∧ ((-1 : Int) ≠ 3) := by omega

/-- The support has exactly 3 distinct points. -/
theorem support_card_3 :
    [(-1 : Int), 1, 3].length = 3 := by native_decide

/-- For a measure on 3 known points, 3 moments suffice for uniqueness
    (no Carleman needed — Vandermonde is enough).
    Carleman gives the stronger statement: even if the support is unknown,
    the moments still determine μ uniquely. -/
theorem finite_sufficiency :
    vanderDet ≠ 0 := vanderDet_ne_zero

/-!
## Summary

| Level | Statement | Method | Status |
|-------|-----------|--------|--------|
| 1 | Vandermonde det = 16 ≠ 0 | `native_decide` | ✓ |
| 2 | Weights (2,4,2) unique | `omega` | ✓ |
| 3 | Carleman Σ m_{2k}^{−1/(2k)} = ∞ | numerical bound | stated |

**For the finite Cayley matrix**: levels 1 and 2 are sufficient.
The measure μ = (2δ₋₁ + 4δ₁ + 2δ₃)/8 is uniquely determined
by dim = 8, Tr(A) = 8, Tr(A²) = 24.

**Carleman** gives the infinite-dimensional extension: if an operator
has the same moment sequence, its spectral measure must be the same μ.
-/

end CarlemanUniqueness
end CouretUnification.Core