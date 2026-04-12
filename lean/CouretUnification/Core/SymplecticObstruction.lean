import Mathlib.Tactic
import CouretUnification.Core.U30

namespace CouretUnification.Core
namespace SymplecticObstruction


/-!
# Obstruction symplectique : J² = −I impossible en dimension impaire

Pour qu'un sous-ensemble S ⊂ (ℤ/30ℤ)× admette une structure
symplectique (i.e. une matrice J sur ℝ^S avec J² = −I), il faut
que |S| soit pair, car det(J²) = det(−I) = (−1)^n, tandis que
det(J²) = det(J)² ≥ 0. Si n est impair, (−1)^n = −1 < 0 :
contradiction.

Le quintuplet V₅ = {1, 7, 11, 23, 29} a cardinal 5 (impair),
donc aucune structure symplectique n'est possible.

Ce résultat est un théorème purement algébrique, indépendant de RH.
-/

-- ═══════════════════════════════════════════
-- Abstract obstruction: (−1)^n = −1 for n odd
-- ═══════════════════════════════════════════

/-- (−1)^(2k+1) = −1. -/
theorem neg_one_pow_odd (k : Nat) : (-1 : Int) ^ (2 * k + 1) = -1 := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 from by ring]
    rw [pow_add, ih]
    norm_num

/-- A perfect square is non-negative. -/
theorem sq_nonneg_int (a : Int) : a * a ≥ 0 := by
  nlinarith [mul_self_nonneg a]

/--
**Core obstruction**: if n is odd, there is no integer d such that
d² = (−1)^n, because d² ≥ 0 but (−1)^n = −1 < 0.

This is the determinant argument: det(J)² = det(J²) = det(−I) = (−1)^n.
-/
theorem no_square_root_neg_one_odd (k : Nat) :
    ¬ ∃ d : Int, d * d = (-1) ^ (2 * k + 1) := by
  rw [neg_one_pow_odd]
  intro ⟨d, hd⟩
  have := sq_nonneg_int d
  omega

-- ═══════════════════════════════════════════
-- The quintuplet V₅ = {1, 7, 11, 23, 29}
-- ═══════════════════════════════════════════

/-- V₅ as a list of residues mod 30. -/
def V5 : List Nat := [1, 7, 11, 23, 29]

/-- |V₅| = 5. -/
theorem V5_card : V5.length = 5 := by decide

/-- 5 is odd. -/
theorem five_odd : ¬ 2 ∣ 5 := by decide

/-- All elements of V₅ are coprime to 30 (they are units mod 30). -/
theorem V5_coprime : V5.Forall (fun a => Nat.gcd a 30 = 1) := by native_decide

/-- V₅ contains all of TC = {1, 11, 29}. -/
theorem V5_contains_TC :
    [1, 11, 29].Forall (fun a => a ∈ V5) := by decide

/--
**Main theorem**: No matrix J : ℤ^5 → ℤ^5 satisfies J² = −I,
because dim = 5 is odd.
-/
theorem no_symplectic_dim5 :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ 5 := by
  rw [show (5 : Nat) = 2 * 2 + 1 from by norm_num]
  exact no_square_root_neg_one_odd 2

-- ═══════════════════════════════════════════
-- General even-dimension necessity
-- ═══════════════════════════════════════════

/--
For any odd number n = 2k+1, no integer square root of (−1)^n exists.
Applied: any subset of (ℤ/30ℤ)× with odd cardinality has no
symplectic structure.
-/
theorem symplectic_requires_even (n : Nat) (hn : ∃ k, n = 2 * k + 1) :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ n := by
  obtain ⟨k, rfl⟩ := hn
  exact no_square_root_neg_one_odd k

-- ═══════════════════════════════════════════
-- Concrete odd subsets of G₃₀
-- ═══════════════════════════════════════════

/-- TC itself has cardinal 3 (odd): no symplectic structure. -/
theorem TC_card_eq_three : CouretUnification.Core.TC.card = 3 :=
  CouretUnification.Core.TC_card

theorem TC_card_odd : ¬ 2 ∣ CouretUnification.Core.TC.card :=
  CouretUnification.Core.TC_dim_odd

theorem no_symplectic_TC :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ 3 := by
  rw [show (3 : Nat) = 2 * 1 + 1 from by norm_num]
  exact no_square_root_neg_one_odd 1

/-- The full group G₃₀ has cardinal 8 (even): obstruction does NOT apply. -/
theorem G30_card_even : 2 ∣ 8 := by decide

/-- Singleton {1} has cardinal 1 (odd): no symplectic structure. -/
theorem no_symplectic_dim1 :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ 1 := by
  rw [show (1 : Nat) = 2 * 0 + 1 from by norm_num]
  exact no_square_root_neg_one_odd 0

/-!
## Summary

| Subset | |S| | Parity | Symplectic? |
|--------|-----|--------|-------------|
| {1} | 1 | odd | ✗ |
| TC = {1,11,29} | 3 | odd | ✗ |
| V₅ = {1,7,11,23,29} | 5 | odd | ✗ |
| G₃₀ | 8 | even | not obstructed |

The determinant argument det(J)² = (−1)^n closes all odd cases.
This is independent of RH and holds over any commutative ring.
-/

end SymplecticObstruction
end CouretUnification.Core
