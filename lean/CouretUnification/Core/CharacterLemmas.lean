/- CouretUnification/Core/CharacterLemmas.lean
   Helpers génériques finis pour les caractères (v35/A)
   0 sorry.

   NOTE: On évite Finset.mul_sum (absent de certaines configs Mathlib).
   On passe par smul_eq_mul + Finset.smul_sum à la place.
-/
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

omit [DecidableEq G] in
lemma sum_left_mul_eq_sum (f : G → ℂ) (a : G) :
    (∑ g : G, f (a * g)) = ∑ g : G, f g := by
  apply Fintype.sum_equiv (Equiv.mulLeft a)
  intro g; simp [Equiv.mulLeft]

/-- c * ∑ f = ∑ c * f.  Contourne l'absence de Finset.mul_sum
    en passant par smul_eq_mul + Finset.smul_sum. -/
private lemma mul_fintype_sum (c : ℂ) (f : G → ℂ) :
    c * (∑ g : G, f g) = ∑ g : G, c * f g := by
  simp only [← smul_eq_mul, Finset.smul_sum]

lemma sum_char_eq_zero_of_ne_one (χ : Char G) (hχ : χ ≠ 1) :
    ∑ g : G, χ g = 0 := by
  by_cases htriv : ∀ g : G, χ g = 1
  · exfalso; apply hχ; exact char_eq_one_of_forall_eq_one χ htriv
  · push_neg at htriv
    obtain ⟨a, ha⟩ := htriv
    -- χ(a) * ∑ χ(g) = ∑ χ(g)  par réindexation
    have hshift : χ a * (∑ g : G, χ g) = ∑ g : G, χ g := by
      rw [mul_fintype_sum]
      simp_rw [← char_mul]
      exact sum_left_mul_eq_sum (fun g => χ g) a
    -- (χ(a) - 1) * ∑ χ(g) = 0
    have hfactor : (χ a - 1) * (∑ g : G, χ g) = 0 := by
      have : (χ a - 1) * (∑ g : G, χ g) =
             χ a * (∑ g : G, χ g) - (∑ g : G, χ g) := by ring
      rw [this, hshift, sub_self]
    -- χ(a) ≠ 1, donc ∑ χ(g) = 0
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr ha)

end CouretUnification.Core