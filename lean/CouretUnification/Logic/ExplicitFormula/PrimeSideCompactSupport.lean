import Mathlib
import CouretUnification.Logic.ExplicitFormula.TraceObject

namespace CouretUnification.Logic.ExplicitFormula

/-- Abstract arithmetic weight. In Frozen, this is not yet von Mangoldt. -/
structure ArithmeticWeight where
  weight : ℕ → ℂ

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
noncomputable def primeTerm (Λ : ArithmeticWeight) (φ : LogCompactTest) (n : ℕ) : ℂ :=
  Λ.weight n * (φ.g (Real.log n) + φ.g (-Real.log n))

/--
Frozen closure of the PrimeSide:
after the cutoff, every prime-side term is zero.
-/
theorem primeTerm_eventually_zero
    (Λ : ArithmeticWeight)
    (φ : LogCompactTest) :
    ∀ n : ℕ, φ.cutoff < n → primeTerm Λ φ n = 0 := by
  intro n hn
  unfold primeTerm
  have hvanish := φ.vanishes_after_cutoff n hn
  rw [hvanish.1, hvanish.2]
  simp

end CouretUnification.Logic.ExplicitFormula
