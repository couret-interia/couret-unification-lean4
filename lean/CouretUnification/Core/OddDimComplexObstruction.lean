import Mathlib.Tactic

namespace CouretUnification.Core
namespace OddDimComplexObstruction

/-!
# Obstruction en dimension impaire : J² = −I impossible sur ℤ (ou ℝ)

Pour qu'un espace réel (ou entier) de dimension n admette une structure
complexe linéaire J avec J² = −I, il faut n pair.

**Argument déterminantal** :
  det(J²) = det(J)² ≥ 0
  det(−I) = (−1)ⁿ
  Si n impair : (−1)ⁿ = −1 < 0, contradiction.

Ce fichier formalise le **noyau scalaire** de cet argument :
  ¬ ∃ d : ℤ, d² = (−1)ⁿ  pour n impair.

Le passage complet J² = −I ⟹ det(J)² = (−1)ⁿ nécessiterait
`Matrix.det_mul` et `Matrix.det_neg` de Mathlib, non invoqués ici.

**Validité** : sur tout anneau ordonné (ℤ, ℝ, corps réel clos).
Contre-exemple sur F₂ : en dim 1, J = [1] donne J² = I = −I.

Appliqué aux sous-ensembles impairs de (ℤ/30ℤ)× :
  |TC| = 3, |V₅| = 5 ⟹ pas de structure complexe réelle.
-/

-- ═══════════════════════════════════════════
-- Core scalar obstruction
-- ═══════════════════════════════════════════

/-- (−1)^(2k+1) = −1. -/
theorem neg_one_pow_odd (k : Nat) : (-1 : Int) ^ (2 * k + 1) = -1 := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 from by ring]
    rw [pow_add, ih]
    norm_num

/-- A perfect square in ℤ is non-negative. -/
theorem sq_nonneg_int (a : Int) : a * a ≥ 0 := by
  nlinarith [mul_self_nonneg a]

/--
**Determinant core**: for n = 2k+1 (odd), there is no d ∈ ℤ
with d² = (−1)ⁿ, because d² ≥ 0 but (−1)ⁿ = −1 < 0.

This is the scalar obstruction underlying the matrix statement:
  J² = −I ⟹ det(J)² = det(−I) = (−1)ⁿ.
The full matrix version requires additionally that det(J²) = det(J)²
and det(−I) = (−1)ⁿ (available via Matrix.det_mul, Matrix.det_neg).
-/
theorem no_square_root_neg_one_odd (k : Nat) :
    ¬ ∃ d : Int, d * d = (-1) ^ (2 * k + 1) := by
  rw [neg_one_pow_odd]
  intro ⟨d, hd⟩
  have := sq_nonneg_int d
  omega

/-- General form: any odd n obstructs. -/
theorem odd_dim_obstructs (n : Nat) (hn : ∃ k, n = 2 * k + 1) :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ n := by
  obtain ⟨k, rfl⟩ := hn
  exact no_square_root_neg_one_odd k

-- ═══════════════════════════════════════════
-- Application: subsets of (ℤ/30ℤ)×
-- ═══════════════════════════════════════════

/-- V₅ = {1, 7, 11, 23, 29}, the quintuplet from the synthesis. -/
def V5 : List Nat := [1, 7, 11, 23, 29]

theorem V5_card : V5.length = 5 := by decide

/-- All elements of V₅ are units mod 30. -/
theorem V5_coprime : V5.Forall (fun a => Nat.gcd a 30 = 1) := by native_decide

/-- V₅ contains TC. -/
theorem V5_contains_TC : [1, 11, 29].Forall (fun a => a ∈ V5) := by decide

/-- Determinant obstruction for dim 5 (V₅). -/
theorem obstruction_dim5 :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ 5 := by
  rw [show (5 : Nat) = 2 * 2 + 1 from by norm_num]
  exact no_square_root_neg_one_odd 2

/-- Determinant obstruction for dim 3 (TC). -/
theorem obstruction_dim3 :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ 3 := by
  rw [show (3 : Nat) = 2 * 1 + 1 from by norm_num]
  exact no_square_root_neg_one_odd 1

/-- Determinant obstruction for dim 1. -/
theorem obstruction_dim1 :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ 1 := by
  rw [show (1 : Nat) = 2 * 0 + 1 from by norm_num]
  exact no_square_root_neg_one_odd 0

/-- The full group G₃₀ has cardinal 8 (even): obstruction does NOT apply. -/
theorem G30_card_even : 2 ∣ 8 := by decide

/-!
## Summary

**What this file proves (scalar core):**
  ¬ ∃ d : ℤ, d² = (−1)ⁿ  for every odd n.

**What this implies (informally, via det(J²) = det(J)² and det(−I) = (−1)ⁿ):**
  No real or integer matrix J of odd size satisfies J² = −I.

**What this does NOT formalize:**
  The matrix-level passage det(J²) = det(J)², which would require
  Matrix.det_mul from Mathlib.

**Scope:** Valid over ℤ, ℝ, and any ordered ring where squares are ≥ 0.
Not valid over F₂ or ℂ.

**Application:** Odd-cardinality subsets of (ℤ/30ℤ)× — including TC (|TC|=3)
and V₅ (|V₅|=5) — cannot carry a real complex structure J² = −I.
-/

end OddDimComplexObstruction
end CouretUnification.Core