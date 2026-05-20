import Mathlib.Tactic
-- import CouretUnification.Core.U30
import CouretUnification.Core.SymplecticObstruction

open CouretUnification.Core.SymplecticObstruction

namespace CouretUnification.Core.OddDimComplexObstruction

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

/-- General form: any odd n obstructs. -/
theorem odd_dim_obstructs (n : Nat) (hn : ∃ k, n = 2 * k + 1) :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ n := by
  obtain ⟨k, rfl⟩ := hn
  exact no_square_root_neg_one_odd k

-- ═══════════════════════════════════════════
-- Application: subsets of (ℤ/30ℤ)× (Aliases)
-- ═══════════════════════════════════════════

/-- Determinant obstruction for dim 5 (V₅). Alias of `no_symplectic_dim5`. -/
theorem obstruction_dim5 :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ 5 := no_symplectic_dim5

/-- Determinant obstruction for dim 3 (TC). Alias of `no_symplectic_TC`. -/
theorem obstruction_dim3 :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ 3 := no_symplectic_TC

/-- Determinant obstruction for dim 1. Alias of `no_symplectic_dim1`. -/
theorem obstruction_dim1 :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ 1 := no_symplectic_dim1

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

end CouretUnification.Core.OddDimComplexObstruction
