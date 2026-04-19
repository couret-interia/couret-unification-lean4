/-
  CouretUnification/Core/CenteredSpace30.lean
  Décomposition FunG30 = trivialLine ⊕ H_centered (dim 1 + dim 7).
  
  Dépend de : UnitsBridge (G30, card_G30)
  Statut : 0 sorry visé
-/

import CouretUnification.Core.UnitsBridge
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic

open scoped BigOperators

namespace CouretUnification.Core

-- ═══════════════════════════════════════════════════════════
-- §1. Espace des fonctions sur G₃₀
-- ═══════════════════════════════════════════════════════════

/-- Espace des fonctions G₃₀ → ℂ. -/
abbrev FunG30 : Type := G30 → ℂ

noncomputable instance : Module ℂ FunG30 := inferInstance
noncomputable instance : FiniteDimensional ℂ FunG30 := inferInstance

@[simp]
theorem finrank_FunG30 : Module.finrank ℂ FunG30 = 8 := by
  rw [show FunG30 = (G30 → ℂ) from rfl]
  rw [Module.finrank_pi ℂ]
  simp [Module.finrank_self, card_G30]

-- ═══════════════════════════════════════════════════════════
-- §2. Somme totale et mode trivial
-- ═══════════════════════════════════════════════════════════

/-- Somme totale : forme linéaire ∑_{g ∈ G₃₀} f(g). -/
noncomputable def totalSum : FunG30 →ₗ[ℂ] ℂ where
  toFun f := ∑ g : G30, f g
  map_add' f h := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]; rfl

/-- Mode trivial : fonction constante 1 sur G₃₀. -/
def trivialMode : FunG30 := fun _ => 1

@[simp]
theorem totalSum_trivialMode : totalSum trivialMode = 8 := by
  unfold totalSum trivialMode
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_const, Finset.card_univ, card_G30]
  norm_num

theorem totalSum_ne_zero : totalSum ≠ 0 := by
  intro h
  have h' : totalSum trivialMode = 0 := by rw [h]; rfl
  rw [totalSum_trivialMode] at h'
  norm_num at h'

-- ═══════════════════════════════════════════════════════════
-- §3. Sous-espace centré H_ℂ = ker(totalSum)
-- ═══════════════════════════════════════════════════════════

/-- Sous-espace centré : les fonctions de somme nulle. -/
def H_centered : Submodule ℂ FunG30 := LinearMap.ker totalSum

theorem mem_H_centered_iff (f : FunG30) :
    f ∈ H_centered ↔ ∑ g : G30, f g = 0 := by
  unfold H_centered totalSum
  simp [LinearMap.mem_ker]

-- ═══════════════════════════════════════════════════════════
-- §4. Dimensions
-- ═══════════════════════════════════════════════════════════

theorem range_totalSum_top : LinearMap.range totalSum = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro c
  refine ⟨(c / 8) • trivialMode, ?_⟩
  rw [LinearMap.map_smul, totalSum_trivialMode]
  field_simp

theorem finrank_range_totalSum : Module.finrank ℂ (LinearMap.range totalSum) = 1 := by
  rw [range_totalSum_top]
  simp [Submodule.finrank_top, Module.finrank_self]

/-- dim H_ℂ = 7. -/
theorem dim_H_centered : Module.finrank ℂ H_centered = 7 := by
  have rank_thm := LinearMap.finrank_range_add_finrank_ker totalSum
  rw [finrank_FunG30] at rank_thm
  rw [finrank_range_totalSum] at rank_thm
  show Module.finrank ℂ (LinearMap.ker totalSum) = 7
  omega

-- ═══════════════════════════════════════════════════════════
-- §5. Direction triviale
-- ═══════════════════════════════════════════════════════════

/-- Droite engendrée par le mode trivial. -/
def trivialLine : Submodule ℂ FunG30 := Submodule.span ℂ {trivialMode}

theorem finrank_trivialLine : Module.finrank ℂ trivialLine = 1 := by
  rw [Submodule.finrank_span_singleton]
  intro h
  have : (trivialMode (1 : G30)) = 0 := by rw [h]; rfl
  unfold trivialMode at this
  norm_num at this

-- ═══════════════════════════════════════════════════════════
-- §6. Décomposition ⊔ = ⊤, ⊓ = ⊥
-- ═══════════════════════════════════════════════════════════

/-- Décomposition directe : FunG30 = trivialLine ⊕ H_centered. -/
theorem decomposition :
    trivialLine ⊔ H_centered = ⊤ ∧ trivialLine ⊓ H_centered = ⊥ := by
  -- 1. Intersection = ⊥
  have h_inf : trivialLine ⊓ H_centered = ⊥ := by
    refine Submodule.eq_bot_iff.mpr ?_
    intro f hf
    -- f ∈ trivialLine : f = c • trivialMode
    have hf_triv : f ∈ trivialLine := hf.1
    rw [trivialLine, Submodule.mem_span_singleton] at hf_triv
    obtain ⟨c, rfl⟩ := hf_triv
    -- f ∈ H_centered : totalSum f = 0
    have hf_cent : c • trivialMode ∈ H_centered := hf.2
    rw [mem_H_centered_iff] at hf_cent
    -- Calcul : totalSum(c • 1) = 8c
    have hcalc : totalSum (c • trivialMode) = (8 : ℂ) * c := by
      simp [totalSum, trivialMode, card_G30, mul_comm]
    -- Donc 8c = 0, donc c = 0
    have hc : c = 0 := by
      have hmul : (8 : ℂ) * c = 0 := by rw [hcalc] at hf_cent; exact hf_cent
      exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
    simp [hc]
  -- 2. Sup = ⊤ par dimension
  have h_sup_fin :
      Module.finrank ℂ (trivialLine ⊔ H_centered) = Module.finrank ℂ FunG30 := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq trivialLine H_centered
    rw [h_inf, Submodule.finrank_bot, finrank_trivialLine, dim_H_centered] at hdim
    have : Module.finrank ℂ (trivialLine ⊔ H_centered) = 8 := by omega
    simpa [finrank_FunG30] using this
  -- 3. Conclusion
  exact ⟨Submodule.eq_top_of_finrank_eq h_sup_fin, h_inf⟩
  -- Repli 1 : (Submodule.eq_top_iff_finrank_eq).2 h_sup_fin
  -- Repli 2 : Submodule.eq_of_le_of_finrank_eq le_top h_sup_fin

end CouretUnification.Core
