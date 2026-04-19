/-
  CouretUnification/Core/CayleyG30.lean
  Graphe de Cayley sur G30 (type Units), connecté à la convolution.
  
  Le TC existant (FiniteCore.lean) travaille sur ZMod 30.
  Ce fichier le transporte sur G30 = (ZMod 30)ˣ et le relie
  à convolutionOp pour fermer le lien Cayley ↔ spectre.
  
  0 sorry visé.
-/

import CouretUnification.Core.Convolution30

open scoped BigOperators

namespace CouretUnification.Core

-- ═══════════════════════════════════════════════════════════
-- §1. TC comme Finset G30
-- ═══════════════════════════════════════════════════════════

/-- Les 3 éléments du triplet de Couret comme unités. -/
def u1  : G30 := ⟨1,  1,  by decide, by decide⟩
def u11 : G30 := ⟨11, 11, by decide, by decide⟩
def u29 : G30 := ⟨29, 29, by decide, by decide⟩

/-- TC ⊂ G30. -/
def TC_G30 : Finset G30 := {u1, u11, u29}

theorem card_TC_G30 : TC_G30.card = 3 := by decide

-- ═══════════════════════════════════════════════════════════
-- §2. Involutions
-- ═══════════════════════════════════════════════════════════

theorem u11_sq : u11 * u11 = (1 : G30) := by decide
theorem u29_sq : u29 * u29 = (1 : G30) := by decide
theorem u11_inv : u11⁻¹ = u11 := by decide
theorem u29_inv : u29⁻¹ = u29 := by decide

theorem TC_G30_symmetric (g : G30) (h : g ∈ TC_G30) : g⁻¹ ∈ TC_G30 := by
  simp only [TC_G30, Finset.mem_insert, Finset.mem_singleton] at h ⊢
  rcases h with rfl | rfl | rfl <;> simp [u11_inv, u29_inv]

-- ═══════════════════════════════════════════════════════════
-- §3. Noyau de convolution associé à TC
-- ═══════════════════════════════════════════════════════════

/-- Indicatrice de TC comme fonction G30 → ℂ.
    C'est le noyau de convolution du graphe de Cayley. -/
def TC_kernel : FunG30 := fun g =>
  if g ∈ TC_G30 then 1 else 0

/-- Somme totale du noyau TC = |TC| = 3. -/
theorem totalSum_TC_kernel : totalSum TC_kernel = 3 := by
  simp [totalSum, TC_kernel, TC_G30, Finset.sum_ite,
        Finset.filter_congr_decidable, LinearMap.coe_mk, AddHom.coe_mk]
  decide

/-- L'opérateur de convolution par TC_kernel est exactement
    la matrice d'adjacence du graphe de Cayley Cay(G₃₀, TC). -/
theorem convolutionOp_TC_is_adjacency (f : FunG30) (x : G30) :
    convolutionOp TC_kernel f x = ∑ t ∈ TC_G30, f (t⁻¹ * x) := by
  simp only [convolutionOp, LinearMap.coe_mk, AddHom.coe_mk, TC_kernel]
  rw [Finset.sum_comm_of_eq (s := Finset.univ) (t := Finset.univ)]
  sorry -- structure correcte mais nécessite réindexation fine
  -- Alternative : prouver par calcul fini sur les 8 éléments

-- ═══════════════════════════════════════════════════════════
-- §4. Composantes : H et 7H
-- ═══════════════════════════════════════════════════════════

/-- Sous-groupe H = {1, 11, 19, 29}. -/
def H_sub : Finset G30 := by
  exact {⟨1,  1,  by decide, by decide⟩,
         ⟨11, 11, by decide, by decide⟩,
         ⟨19, 19, by decide, by decide⟩,
         ⟨29, 29, by decide, by decide⟩}

/-- Coset 7H = {7, 13, 17, 23}. -/
def H_coset : Finset G30 := by
  exact {⟨7,  13, by decide, by decide⟩,
         ⟨13, 7,  by decide, by decide⟩,
         ⟨17, 23, by decide, by decide⟩,
         ⟨23, 17, by decide, by decide⟩}

theorem card_H_sub : H_sub.card = 4 := by decide
theorem card_H_coset : H_coset.card = 4 := by decide
theorem H_inter_coset : H_sub ∩ H_coset = ∅ := by decide
theorem H_union_coset : H_sub ∪ H_coset = Finset.univ := by decide

/-- Produit fantôme dans G30. -/
theorem phantom_G30 : u11 * u29 = (⟨19, 19, by decide, by decide⟩ : G30) := by
  decide

-- ═══════════════════════════════════════════════════════════
-- §5. Diamètre
-- ═══════════════════════════════════════════════════════════

/-- Chaque composante a diamètre 2 (chaque élément atteint
    en au plus 2 pas dans sa composante). -/
theorem diameter_H_le_2 :
    ∀ g ∈ H_sub, ∃ (s : List G30),
      s.length ≤ 2 ∧ (∀ t ∈ s, t ∈ TC_G30) ∧ s.foldl (· * ·) 1 = g := by
  intro g hg
  simp only [H_sub, Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · -- g = 1 : chemin vide
    exact ⟨[], by omega, fun _ h => absurd h (List.not_mem_nil _), by simp⟩
  · -- g = 11 : un pas [11]
    exact ⟨[u11], by omega, by simp [TC_G30], by decide⟩
  · -- g = 19 : deux pas [11, 29]
    exact ⟨[u11, u29], by omega, by simp [TC_G30], by decide⟩
  · -- g = 29 : un pas [29]
    exact ⟨[u29], by omega, by simp [TC_G30], by decide⟩

end CouretUnification.Core
