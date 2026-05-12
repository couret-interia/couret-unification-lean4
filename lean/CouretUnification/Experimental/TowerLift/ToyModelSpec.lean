-- =========================================================================
-- Couret-Unification / TowerLift v18
-- Module : Examples/ToyModelSpec.lean
--
-- Spécification Lean propre — pas de #eval sur Real
-- =========================================================================

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace CouretUnification.ToyModelSpec

structure TowerLift where
  numChars : Nat
  level : Nat
  name : String := "unnamed"

def toyLift : TowerLift :=
  { numChars := 4, level := 1, name := "toy" }

noncomputable def lambdaDelta7 : Real := 1 / Real.sqrt 7

def dirichletMod30Coeff (p : Nat) : Real :=
  match p % 30 with
  | 1 => 1 | 7 => 1 | 11 => -1 | 13 => 1
  | 17 => -1 | 19 => 1 | 23 => -1 | 29 => 1
  | _ => 0

def SGPrimes : Finset Nat := {11, 23, 29}

noncomputable def toyPrimePow (p : Nat) (s : Real) : Real :=
  Real.exp (-s * Real.log p)

noncomputable def toyLocalLog (p : Nat) (s : Real) : Real :=
  -Real.log (1 - toyPrimePow p s)

noncomputable def toyFibre (p : Nat) : Real :=
  if p = 2 ∨ p = 3 ∨ p = 5 then 1
  else 1 / (Real.log p + 1)

noncomputable def toySpectralWeight (p : Nat) : Real :=
  dirichletMod30Coeff p * toyFibre p

noncomputable def toySGEuler (s : Real) : Real :=
  ∑ p : SGPrimes, toySpectralWeight p * toyLocalLog p s

noncomputable def toySpectralObservable : Real :=
  0.37517  -- δ̃₂ from scan

noncomputable def toyCouplingRatio (s : Real) : Real :=
  toySGEuler s / toySpectralObservable

def ToyWeakCouplingAt (s : Real) : Prop :=
  ∃ μ : Real, toySGEuler s = μ * toySpectralObservable

theorem ToyWeakCoupling_tautological (s : Real)
    (h : toySpectralObservable ≠ 0) :
    ToyWeakCouplingAt s := by
  refine ⟨toyCouplingRatio s, ?_⟩
  unfold toyCouplingRatio
  field_simp [h]

-- NOTE: l'existence de μ(s) est tautologique.
-- Le vrai signal est la STABILITÉ de μ(s),
-- mesurée par le CV dans le scan Python.

end CouretUnification.ToyModelSpec
