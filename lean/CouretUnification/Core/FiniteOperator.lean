import CouretUnification.Core.Mod30
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open BigOperators

namespace CouretUnification.Core

noncomputable section

abbrev Vec := Idx → ℂ
abbrev Kernel := Idx → Idx → ℂ

/--
Ordre de base des unités modulo 30 :
0 ↦ 1, 1 ↦ 7, 2 ↦ 11, 3 ↦ 13, 4 ↦ 17, 5 ↦ 19, 6 ↦ 23, 7 ↦ 29.

Le triplet distingué est T_C = {1,11,29}, donc les indices {0,2,7}.
-/
def TCBaseSupportVals : List Nat := [0, 2, 7]

/--
Supports de ligne de l'opérateur de convolution par 1_{T_C}.
La ligne de i est supportée sur g_i * T_C.
-/
def TCRowSupportVals : Idx → List Nat
  | ⟨0, _⟩ => [0, 2, 7]  -- 1  * T_C = {1,11,29}
  | ⟨1, _⟩ => [1, 4, 6]  -- 7  * T_C = {7,17,23}
  | ⟨2, _⟩ => [0, 2, 5]  -- 11 * T_C = {1,11,19}
  | ⟨3, _⟩ => [3, 4, 6]  -- 13 * T_C = {13,17,23}
  | ⟨4, _⟩ => [1, 3, 4]  -- 17 * T_C = {7,13,17}
  | ⟨5, _⟩ => [2, 5, 7]  -- 19 * T_C = {11,19,29}
  | ⟨6, _⟩ => [1, 3, 6]  -- 23 * T_C = {7,13,23}
  | ⟨7, _⟩ => [0, 5, 7]  -- 29 * T_C = {1,19,29}

/-- Indicatrice du triplet T_C dans la base active. -/
def tcIndicator : Vec :=
  fun i => if i.1 ∈ TCBaseSupportVals then 1 else 0

def TCNat : Idx → Idx → Nat :=
  fun i j => if j.1 ∈ TCRowSupportVals i then 1 else 0

/-- Opérateur fini exact associé à T_C. -/
def TC : Kernel :=
  fun i j => (TCNat i j : ℂ)

/-- Application d'un noyau fini à un vecteur. -/
def applyKernel (K : Kernel) (v : Vec) : Vec :=
  fun i => ∑ j : Idx, K i j * v j

/-- Vecteur constant 1. -/
def oneVec : Vec := fun _ => 1

/--
Symétrie de la matrice de convolution finie associée à T_C.
-/
lemma TC_symm (i j : Idx) : TC i j = TC j i := by
  fin_cases i <;> fin_cases j <;> norm_num [TC, TCNat, TCRowSupportVals]

lemma TCNat_row_sum (i : Idx) : ∑ j : Idx, TCNat i j = 3 := by
  fin_cases i <;> native_decide

/--
Chaque ligne de TC contient exactement trois coefficients égaux à 1.
-/
lemma TC_row_sum (i : Idx) : ∑ j : Idx, TC i j = (3 : ℂ) := by
  simp only [TC]
  exact_mod_cast TCNat_row_sum i

/--
Le vecteur constant 1 est vecteur propre de TC pour la valeur propre 3.
-/
lemma TC_on_oneVec : applyKernel TC oneVec = fun _ => (3 : ℂ) := by
  funext i
  simp [applyKernel, oneVec, TC_row_sum]

end

end CouretUnification.Core