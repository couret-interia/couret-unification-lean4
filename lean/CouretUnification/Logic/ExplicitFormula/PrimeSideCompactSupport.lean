import Mathlib
import CouretUnification.Logic.ExplicitFormula.TraceObject
import CouretUnification.Logic.ExplicitFormula.ArithmeticWeight

namespace CouretUnification.Logic.ExplicitFormula

-- ArithmeticWeight vit désormais dans ArithmeticWeight.lean (canonique).
-- v38 : déduplication post-Frozen v36.0.

-- (lignes supprimées ; ArithmeticWeight vient maintenant de
--  l'import ligne 3 — version canonique avec weight : ℕ → ℝ)

/--
A log-compact test function.

This is the Frozen-safe version of compact support:
after some integer cutoff, both g(log n) and g(-log n) vanish.
-/
structure LogCompactTest where
  g : ℝ → ℂ
  cutoff : ℕ
  vanishes_after_cutoff :
    ∀ n : ℕ, cutoff < n →
      g (Real.log n) = 0 ∧ g (-Real.log n) = 0

/-- Abstract prime-side summand. -/
noncomputable def primeTermLogCompact
    (Λ : ArithmeticWeight) (φ : LogCompactTest) (n : ℕ) : ℂ :=
  (Λ.weight n : ℂ) * (φ.g (Real.log n) + φ.g (-Real.log n))

/--
Frozen closure of the PrimeSide:
after the cutoff, every prime-side term is zero.
-/
theorem primeTermLogCompact_eventually_zero
    (Λ : ArithmeticWeight)
    (φ : LogCompactTest) :
    ∀ n : ℕ, φ.cutoff < n → primeTermLogCompact Λ φ n = 0 := by
  intro n hn
  unfold primeTermLogCompact
  have hvanish := φ.vanishes_after_cutoff n hn
  rw [hvanish.1, hvanish.2]
  simp

end CouretUnification.Logic.ExplicitFormula
