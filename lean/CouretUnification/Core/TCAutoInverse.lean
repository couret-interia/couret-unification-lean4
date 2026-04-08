import Mathlib.Tactic

namespace CouretUnification.Core
namespace TCAutoInverse

/-!
# TC auto-inverse : ∀ x ∈ {1, 11, 29}, x² ≡ 1 (mod 30)

Each element of the Couret triplet is its own inverse in (ℤ/30ℤ)×.
All proofs by `native_decide`.
-/

/-- 1² ≡ 1 (mod 30). -/
theorem sq_1_mod30 : 1 * 1 % 30 = 1 := by native_decide

/-- 11² ≡ 1 (mod 30). -/
theorem sq_11_mod30 : 11 * 11 % 30 = 1 := by native_decide

/-- 29² ≡ 1 (mod 30). -/
theorem sq_29_mod30 : 29 * 29 % 30 = 1 := by native_decide

/-- TC is not a subgroup: 11 · 29 ≡ 19 (mod 30), and 19 ∉ TC. -/
theorem prod_11_29_mod30 : 11 * 29 % 30 = 19 := by native_decide
theorem nineteen_not_in_TC : 19 ≠ 1 ∧ 19 ≠ 11 ∧ 19 ≠ 29 := by omega

/-- Full multiplication table mod 30 for TC elements. -/
theorem mul_1_11 : 1 * 11 % 30 = 11 := by native_decide
theorem mul_1_29 : 1 * 29 % 30 = 29 := by native_decide
theorem mul_11_29 : 11 * 29 % 30 = 19 := by native_decide

/-- All TC elements are units mod 30 (gcd = 1). -/
theorem unit_1 : Nat.gcd 1 30 = 1 := by native_decide
theorem unit_11 : Nat.gcd 11 30 = 1 := by native_decide
theorem unit_29 : Nat.gcd 29 30 = 1 := by native_decide

/-- TC is closed under inversion (each element is its own inverse). -/
theorem inv_1_mod30 : ∃ k, 1 * k % 30 = 1 ∧ k = 1 := ⟨1, by native_decide, rfl⟩
theorem inv_11_mod30 : ∃ k, 11 * k % 30 = 1 ∧ k = 11 := ⟨11, by native_decide, rfl⟩
theorem inv_29_mod30 : ∃ k, 29 * k % 30 = 1 ∧ k = 29 := ⟨29, by native_decide, rfl⟩

/-!
## Summary

| x ∈ TC | x² mod 30 | x⁻¹ mod 30 | x · y mod 30 (y ∈ TC) |
|--------|-----------|-------------|------------------------|
| 1 | 1 | 1 | 1·11=11, 1·29=29 |
| 11 | 1 | 11 | 11·29=19 ∉ TC |
| 29 | 1 | 29 | — |

TC is auto-inverse (closed under inversion) but NOT a subgroup
(not closed under multiplication: 11·29 ≡ 19 ∉ TC).
-/

end TCAutoInverse
end CouretUnification.Core