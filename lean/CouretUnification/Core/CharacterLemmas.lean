/- CouretUnification/Core/CharacterLemmas.lean
   Helpers génériques finis pour les caractères (v35/A)
   0 sorry. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.GroupAction.Defs

open scoped BigOperators

namespace CouretUnification.Core

universe u
variable {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]

abbrev Char (G : Type u) [CommGroup G] := G →* ℂ

omit [Fintype G] [DecidableEq G] in
@[simp] lemma char_mul (χ : Char G) (a b : G) :
    χ (a * b) = χ a * χ b := map_mul χ a b

omit [Fintype G] [DecidableEq G] in
@[simp] lemma char_one (χ : Char G) : χ 1 = 1 := map_one χ

omit [Fintype G] [DecidableEq G] in
@[simp] lemma char_inv (χ : Char G) (a : G) :
    χ a⁻¹ = (χ a)⁻¹ := map_inv χ a

omit [Fintype G] [DecidableEq G] in
lemma char_eq_one_of_forall_eq_one (χ : Char G)
    (h : ∀ g : G, χ g = 1) : χ = 1 := by
  ext g; exact h g

lemma sum_left_mul_eq_sum (f : G → ℂ) (a : G) :
    (∑ g : G, f (a * g)) = ∑ g : G, f g := by
  apply Fintype.sum_equiv (Equiv.mulLeft a)
  intro g
  simp [Equiv.mulLeft]

lemma sum_char_eq_zero_of_ne_one (χ : Char G) (hχ : χ ≠ 1) :
    ∑ g : G, χ g = 0 := by
  by_cases htriv : ∀ g : G, χ g = 1
  · exfalso; apply hχ; exact char_eq_one_of_forall_eq_one χ htriv
  · obtain ⟨a, ha⟩ := not_forall.mp htriv
    let S : ℂ := ∑ g : G, χ g
    have hshift : χ a * S = S := by
      calc χ a * S = χ a * ∑ g : G, χ g := rfl
        _ = ∑ g : G, χ a * χ g := by
            congr 1; ext g; rfl
        _ = ∑ g : G, χ (a * g) := by
            refine Finset.sum_congr rfl ?_; intro g _; rw [char_mul]
        _ = ∑ g : G, χ g := by
            simp [S, sum_left_mul_eq_sum]
    have hfactor : (χ a - 1) * S = 0 := by
      calc (χ a - 1) * S = χ a * S - S := by ring
        _ = S - S := by rw [hshift]
        _ = 0 := by ring
    have hne : χ a - 1 ≠ 0 := by intro hz; apply ha; exact sub_eq_zero.mp hz
    exact (mul_eq_zero.mp hfactor).resolve_left hne

end CouretUnification.Core
