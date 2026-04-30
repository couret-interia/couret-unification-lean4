/-
  Couret-Unification — v35.9.1
  Logic/ExplicitFormula/ArithmeticWeight.lean

  Objet : poids arithmétique abstrait. Frozen ne connaît PAS vonMangoldt.

  Statut     : Frozen-eligible
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0
  axiomCount             : 0

  Pour Bernard.
-/

import Mathlib.Data.Complex.Basic

namespace CouretUnification.Logic.ExplicitFormula

/-- Poids arithmétique abstrait. Instanciation concrète (via la
    fonction de von Mangoldt de Mathlib ou autre) réservée à Active. -/
structure ArithmeticWeight where
  weight : ℕ → ℝ

/-- Poids trivial (zéro partout). Utile comme instance de test. -/
def ArithmeticWeight.zero : ArithmeticWeight :=
  { weight := fun _ => 0 }

/-- Poids constant. Utile comme instance de test. -/
def ArithmeticWeight.const (c : ℝ) : ArithmeticWeight :=
  { weight := fun _ => c }

/-- Le poids évalué en n comme nombre complexe. -/
noncomputable def ArithmeticWeight.cweight
    (Λ : ArithmeticWeight) (n : ℕ) : ℂ :=
  (Λ.weight n : ℂ)

end CouretUnification.Logic.ExplicitFormula
