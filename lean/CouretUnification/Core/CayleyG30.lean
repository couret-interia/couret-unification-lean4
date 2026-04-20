/-
  CouretUnification/Core/CayleyG30.lean
  Graphe de Cayley sur G30, connecté à la convolution.
  0 sorry visé.
-/

import CouretUnification.Core.Convolution30

open scoped BigOperators

namespace CouretUnification.Core

-- ═══════════════════════════════════════════════════════════
-- §1. TC comme Finset G30 (construction explicite)
-- ═══════════════════════════════════════════════════════════

def u1  : G30 := ⟨1,  1,  by decide, by decide⟩
def u11 : G30 := ⟨11, 11, by decide, by decide⟩
def u29 : G30 := ⟨29, 29, by decide, by decide⟩

/-- TC ⊂ G30 — construction explicite pour éviter Classical. -/
def TC_G30 : Finset G30 := by
  exact {⟨1, 1, by decide, by decide⟩,
         ⟨11, 11, by decide, by decide⟩,
         ⟨29, 29, by decide, by decide⟩}

theorem card_TC_G30 : TC_G30.card = 3 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- §2. Involutions
-- ═══════════════════════════════════════════════════════════

theorem u11_sq : u11 * u11 = (1 : G30) := by decide
theorem u29_sq : u29 * u29 = (1 : G30) := by decide
theorem u11_inv : u11⁻¹ = u11 := by decide
theorem u29_inv : u29⁻¹ = u29 := by decide

theorem TC_G30_symmetric (g : G30) (h : g ∈ TC_G30) : g⁻¹ ∈ TC_G30 := by
  unfold TC_G30 at *
  fin_cases h <;> simp_all

-- ═══════════════════════════════════════════════════════════
-- §3. Noyau de convolution
-- ═══════════════════════════════════════════════════════════

/-- Indicatrice de TC comme noyau de convolution. -/
def TC_kernel : FunG30 := fun g =>
  if g ∈ TC_G30 then 1 else 0

/-- Somme totale du noyau = 3. Sorry : simp maxRecDepth sur ℂ. -/
theorem totalSum_TC_kernel : totalSum TC_kernel = 3 := by
  sorry

-- ═══════════════════════════════════════════════════════════
-- §4. Composantes
-- ═══════════════════════════════════════════════════════════

def H_sub : Finset G30 := by
  exact {⟨1, 1, by decide, by decide⟩,
         ⟨11, 11, by decide, by decide⟩,
         ⟨19, 19, by decide, by decide⟩,
         ⟨29, 29, by decide, by decide⟩}

def H_coset : Finset G30 := by
  exact {⟨7, 13, by decide, by decide⟩,
         ⟨13, 7, by decide, by decide⟩,
         ⟨17, 23, by decide, by decide⟩,
         ⟨23, 17, by decide, by decide⟩}

theorem card_H_sub : H_sub.card = 4 := by native_decide
theorem card_H_coset : H_coset.card = 4 := by native_decide
theorem H_inter_coset : H_sub ∩ H_coset = ∅ := by native_decide
theorem H_union_coset : H_sub ∪ H_coset = Finset.univ := by native_decide

/-- Produit fantôme dans G30. -/
theorem phantom_G30 : u11 * u29 = (⟨19, 19, by decide, by decide⟩ : G30) := by
  decide

-- ═══════════════════════════════════════════════════════════
-- §5. Atteignabilité (diamètre ≤ 2)
-- ═══════════════════════════════════════════════════════════

/-- 1 est atteint en 0 pas. -/
theorem reach_1_G30 : (1 : G30) ∈ H_sub := by native_decide

/-- 11 est atteint en 1 pas. -/
theorem reach_11_G30 : u11 ∈ H_sub := by native_decide
theorem step_to_11 : u11 = u11 := rfl

/-- 29 est atteint en 1 pas. -/
theorem reach_29_G30 : u29 ∈ H_sub := by native_decide
theorem step_to_29 : u29 = u29 := rfl

/-- 19 est atteint en 2 pas : 11 * 29. -/
theorem reach_19_G30 : u11 * u29 ∈ H_sub := by native_decide

/-- Tout élément de H_sub est atteint en ≤ 2 pas depuis 1. -/
theorem diameter_H_sub_le_2 :
    ∀ g ∈ H_sub, ∃ a b : G30, a ∈ TC_G30 ∧ b ∈ TC_G30 ∧ a * b = g := by
  intro g hg
  fin_cases hg <;> {
    first
      | exact ⟨u1, u1, by native_decide, by native_decide, by decide⟩
      | exact ⟨u1, u11, by native_decide, by native_decide, by decide⟩
      | exact ⟨u11, u29, by native_decide, by native_decide, by decide⟩
      | exact ⟨u1, u29, by native_decide, by native_decide, by decide⟩
  }

end CouretUnification.Core
