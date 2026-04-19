/-
  CouretUnification/Core/CenteredSpace30.lean
  Adapté Mathlib v4.29.
-/

import CouretUnification.Core.UnitsBridge
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Pi

open scoped BigOperators

namespace CouretUnification.Core

-- ═══════════════════════════════════════════════════════════
-- §0. Lemme technique : Nat.totient 30 = 8
-- Fintype.card G30 se déplie en Nat.totient 30 dans v4.29.
-- Ce simp lemma résout tous les goals résiduels.
-- ═══════════════════════════════════════════════════════════

@[simp] theorem nat_totient_30 : Nat.totient 30 = 8 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- §1. Espace des fonctions
-- ═══════════════════════════════════════════════════════════

abbrev FunG30 : Type := G30 → ℂ

noncomputable instance : Module ℂ FunG30 := inferInstance
noncomputable instance : FiniteDimensional ℂ FunG30 := inferInstance

@[simp]
theorem finrank_FunG30 : Module.finrank ℂ FunG30 = 8 := by
  change Module.finrank ℂ (G30 → ℂ) = 8
  simp

-- ═══════════════════════════════════════════════════════════
-- §2. Somme totale
-- ═══════════════════════════════════════════════════════════

noncomputable def totalSum : FunG30 →ₗ[ℂ] ℂ where
  toFun f := ∑ g : G30, f g
  map_add' f h := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

def trivialMode : FunG30 := fun _ => 1

@[simp]
theorem totalSum_trivialMode : totalSum trivialMode = 8 := by
  simp [totalSum, trivialMode, Finset.sum_const, Finset.card_univ]
  -- Nat.totient 30 est simplifié en 8 par nat_totient_30

-- ═══════════════════════════════════════════════════════════
-- §3. H_centered
-- ═══════════════════════════════════════════════════════════

noncomputable def H_centered : Submodule ℂ FunG30 := LinearMap.ker totalSum

theorem mem_H_centered_iff (f : FunG30) :
    f ∈ H_centered ↔ totalSum f = 0 := by
  simp [H_centered, LinearMap.mem_ker]

-- ═══════════════════════════════════════════════════════════
-- §4. Dimensions
-- ═══════════════════════════════════════════════════════════

noncomputable def range_totalSum_top : LinearMap.range totalSum = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro c
  refine ⟨(c / 8) • trivialMode, ?_⟩
  simp [totalSum, trivialMode, Finset.sum_const, Finset.card_univ]
  -- Goal : c * (↑(Nat.totient 30) * (1/8)) = c  ou similaire
  -- nat_totient_30 simplifie, puis ring_nf ferme
  ring_nf

theorem dim_H_centered : Module.finrank ℂ H_centered = 7 := by
  have rank_thm := LinearMap.finrank_range_add_finrank_ker totalSum
  rw [finrank_FunG30] at rank_thm
  have h_range : Module.finrank ℂ (LinearMap.range totalSum) = 1 := by
    rw [range_totalSum_top]; simp
  rw [h_range] at rank_thm
  show Module.finrank ℂ (LinearMap.ker totalSum) = 7
  omega

-- ═══════════════════════════════════════════════════════════
-- §5. Droite triviale
-- ═══════════════════════════════════════════════════════════

noncomputable def trivialLine : Submodule ℂ FunG30 :=
  Submodule.span ℂ {trivialMode}

-- dim(trivialLine) = 1
-- Thomas : si le nom ne passe pas, essayer `exact?` sur ce goal
-- Candidats v4.29 : finrank_span_singleton, Submodule.finrank_span_singleton,
--   Set.finrank_span_singleton, FiniteDimensional.finrank_span_singleton
theorem finrank_trivialLine : Module.finrank ℂ trivialLine = 1 := by
  have h_ne : trivialMode ≠ 0 := by
    intro h
    have : (trivialMode (1 : G30)) = 0 := by rw [h]; rfl
    simp [trivialMode] at this
  exact finrank_span_singleton h_ne

-- ═══════════════════════════════════════════════════════════
-- §6. Décomposition
-- ═══════════════════════════════════════════════════════════

theorem decomposition :
    trivialLine ⊔ H_centered = ⊤ ∧ trivialLine ⊓ H_centered = ⊥ := by
  -- 1. Intersection = ⊥
  have h_inf : trivialLine ⊓ H_centered = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    have hf_triv : f ∈ trivialLine := hf.1
    simp only [trivialLine, Submodule.mem_span_singleton] at hf_triv
    obtain ⟨c, rfl⟩ := hf_triv
    have hf_cent : c • trivialMode ∈ H_centered := hf.2
    rw [mem_H_centered_iff] at hf_cent
    -- totalSum(c • trivialMode) = 8c
    have hcalc : totalSum (c • trivialMode) = 8 * c := by
      simp [totalSum, trivialMode, Finset.sum_const, Finset.card_univ]
      ring
    -- 8c = 0 donc c = 0
    have hc : c = 0 := by
      have h8c : (8 : ℂ) * c = 0 := by
        rw [← hcalc]; exact hf_cent
      exact (mul_eq_zero.mp h8c).resolve_left (by norm_num)
    simp [hc]
  -- 2. Sup = ⊤ par dimension
  have h_sup_fin :
      Module.finrank ℂ (trivialLine ⊔ H_centered) =
      Module.finrank ℂ FunG30 := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      trivialLine H_centered
    rw [h_inf, finrank_trivialLine, dim_H_centered] at hdim
    simp at hdim
    simpa [finrank_FunG30] using hdim
  exact ⟨Submodule.eq_top_of_finrank_eq h_sup_fin, h_inf⟩

end CouretUnification.Core
