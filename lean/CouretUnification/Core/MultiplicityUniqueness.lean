import Mathlib.Tactic

namespace CouretUnification.Core.MultiplicityUniqueness

/-!
# Unicité des multiplicités spectrales

Le système :
  a + b + c = 8      (dimension)
  3a + b − c = 8     (Tr A)
  9a + b + c = 24    (Tr A²)

possède pour unique solution a = 2, b = 4, c = 2.

C’est l’ossature algébrique de la détermination spectrale :
étant donné des valeurs propres incluses dans {3, 1, −1}, les traces
Tr(A) et Tr(A²) fixent de manière unique toutes les multiplicités.
-/

/--
**Existence** : (2, 4, 2) est une solution.
-/
theorem mult_solution :
    2 + 4 + 2 = 8 ∧
    3 * 2 + 4 - 2 = 8 ∧
    9 * 2 + 4 + 2 = 24 := by omega

/--
**Unicité** : toute solution est égale à (2, 4, 2).
-/
theorem mult_unique (a b c : Int)
    (h1 : a + b + c = 8)
    (h2 : 3 * a + b - c = 8)
    (h3 : 9 * a + b + c = 24) :
    a = 2 ∧ b = 4 ∧ c = 2 := by omega

/--
**Version empaquetée** : les multiplicités de Spec(A) = {3ᵃ, 1ᵇ, (−1)ᶜ}
sont déterminées de manière unique par dim = 8, Tr(A) = 8, Tr(A²) = 24.
-/
theorem mult_unique_nat (a b c : Nat)
    (h1 : a + b + c = 8)
    (h2 : 3 * a + b + 8 = 8 + c + 8)  -- réécrit pour éviter la soustraction sur Nat
    (h3 : 9 * a + b + c = 24) :
    a = 2 ∧ b = 4 ∧ c = 2 := by omega

end CouretUnification.Core.MultiplicityUniqueness
