import Mathlib.Tactic

namespace CouretUnification.Core
namespace MultiplicityUniqueness

/-!
# Unicité des multiplicités spectrales

The system:
  a + b + c = 8      (dimension)
  3a + b − c = 8     (Tr A)
  9a + b + c = 24    (Tr A²)

has the unique solution a = 2, b = 4, c = 2.

This is the algebraic backbone of the spectral determination:
given eigenvalues ⊆ {3, 1, −1}, the traces Tr(A) and Tr(A²)
uniquely fix all multiplicities.
-/

/--
**Existence**: (2, 4, 2) is a solution.
-/
theorem mult_solution :
    2 + 4 + 2 = 8 ∧
    3 * 2 + 4 - 2 = 8 ∧
    9 * 2 + 4 + 2 = 24 := by omega

/--
**Uniqueness**: any solution equals (2, 4, 2).
-/
theorem mult_unique (a b c : Int)
    (h1 : a + b + c = 8)
    (h2 : 3 * a + b - c = 8)
    (h3 : 9 * a + b + c = 24) :
    a = 2 ∧ b = 4 ∧ c = 2 := by omega

/--
**Packaged**: the multiplicities of Spec(A) = {3ᵃ, 1ᵇ, (−1)ᶜ}
are uniquely determined by dim = 8, Tr(A) = 8, Tr(A²) = 24.
-/
theorem mult_unique_nat (a b c : Nat)
    (h1 : a + b + c = 8)
    (h2 : 3 * a + b + 8 = 8 + c + 8)  -- rewritten to avoid subtraction on Nat
    (h3 : 9 * a + b + c = 24) :
    a = 2 ∧ b = 4 ∧ c = 2 := by omega

end MultiplicityUniqueness
end CouretUnification.Core