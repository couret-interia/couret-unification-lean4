/-
  CouretUnification/Core/Convolution30.lean
  Convolution sur G₃₀ : branche A (masse) + branche B (équivariance).
  Adapté Mathlib v4.29.
-/

import CouretUnification.Core.CenteredSpace30

open scoped BigOperators

namespace CouretUnification.Core

-- ═══════════════════════════════════════════════════════════
-- §1. Translation gauche
-- ═══════════════════════════════════════════════════════════

noncomputable def leftTranslation (u : G30) : FunG30 →ₗ[ℂ] FunG30 where
  toFun f := fun x => f (u⁻¹ * x)
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp

-- ═══════════════════════════════════════════════════════════
-- §2. Réindexation de sommes finies
-- ═══════════════════════════════════════════════════════════

/-- Réindexation par y ↦ u * y. -/
private lemma sum_reindex_mul_left (u : G30) (F : G30 → ℂ) :
    (∑ y : G30, F (u * y)) = ∑ g : G30, F g := by
  apply Finset.sum_nbij (fun y => u * y)
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => mul_left_cancel h)
    (fun g _ => ⟨u⁻¹ * g, Finset.mem_univ _, by group⟩)
    (fun _ _ => rfl)

/-- Réindexation par y ↦ x * y⁻¹. -/
private lemma sum_reindex_mul_inv (x : G30) (F : G30 → ℂ) :
    (∑ y : G30, F (x * y⁻¹)) = ∑ g : G30, F g := by
  apply Finset.sum_nbij (fun y => x * y⁻¹)
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => by
      have := mul_left_cancel h
      exact inv_injective this)
    (fun g _ => ⟨g⁻¹ * x, Finset.mem_univ _, by group⟩)
    (fun _ _ => rfl)

-- ═══════════════════════════════════════════════════════════
-- §3. Opérateur de convolution
-- ═══════════════════════════════════════════════════════════

/-- T_K(f)(x) = ∑_y K(x y⁻¹) f(y). -/
noncomputable def convolutionOp (K : FunG30) : FunG30 →ₗ[ℂ] FunG30 where
  toFun f := fun x => ∑ y : G30, K (x * y⁻¹) * f y
  map_add' f h := by
    ext x; simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro y _; ring
  map_smul' c f := by
    ext x; simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro y _; ring

-- ═══════════════════════════════════════════════════════════
-- §4. Branche A : conservation de la masse
-- ═══════════════════════════════════════════════════════════

/-- totalSum(K * f) = totalSum(K) · totalSum(f). -/
lemma totalSum_convolution (K f : FunG30) :
    totalSum (convolutionOp K f) = (totalSum K) * (totalSum f) := by
  simp only [totalSum, convolutionOp, LinearMap.coe_mk, AddHom.coe_mk]
  calc ∑ x : G30, ∑ y : G30, K (x * y⁻¹) * f y
      = ∑ y : G30, ∑ x : G30, K (x * y⁻¹) * f y := by
          rw [Finset.sum_comm]
    _ = ∑ y : G30, (∑ x : G30, K (x * y⁻¹)) * f y := by
          apply Finset.sum_congr rfl; intro y _
          rw [← Finset.sum_mul]
    _ = ∑ y : G30, (∑ g : G30, K g) * f y := by
          apply Finset.sum_congr rfl; intro y _
          congr 1
          -- ∑ x, K(x * y⁻¹) = ∑ g, K g par commutativité + réindexation
          simp_rw [mul_comm _ y⁻¹]
          exact sum_reindex_mul_left y⁻¹ K
    _ = (∑ g : G30, K g) * ∑ y : G30, f y := by
          rw [Finset.mul_sum]

/-- H_centered est stable par convolution. -/
theorem centered_invariant (K : FunG30) {f : FunG30}
    (hf : f ∈ H_centered) : convolutionOp K f ∈ H_centered := by
  rw [mem_H_centered_iff] at hf ⊢
  simp only [totalSum_convolution, hf, mul_zero]

-- ═══════════════════════════════════════════════════════════
-- §5. Branche B : commutation avec les translations
-- ═══════════════════════════════════════════════════════════

/-- T_K ∘ L_u = L_u ∘ T_K. -/
theorem convolution_commutes_translation (K : FunG30) (u : G30) :
    (convolutionOp K).comp (leftTranslation u) =
    (leftTranslation u).comp (convolutionOp K) := by
  -- ext à deux niveaux : φ : FunG30, puis x : G30
  ext φ
  simp only [convolutionOp, leftTranslation,
    LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
  -- LHS : ∑ y, K(x y⁻¹) φ(u⁻¹ y)
  -- Changement y = u * g, puis algèbre de groupe
  calc ∑ y : G30, K (x * y⁻¹) * φ (u⁻¹ * y)
      = ∑ g : G30, K (x * (u * g)⁻¹) * φ (u⁻¹ * (u * g)) := by
          rw [← sum_reindex_mul_left u]
    _ = ∑ g : G30, K (u⁻¹ * x * g⁻¹) * φ g := by
          apply Finset.sum_congr rfl; intro g _
          have h1 : x * (u * g)⁻¹ = u⁻¹ * x * g⁻¹ := by group
          have h2 : u⁻¹ * (u * g) = g := by group
          rw [h1, h2]
    _ = ∑ y : G30, K (u⁻¹ * x * y⁻¹) * φ y := rfl

end CouretUnification.Core
