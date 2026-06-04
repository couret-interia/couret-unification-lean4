import CouretUnification.Core.CharacterSubgroupSums
import Mathlib.Tactic

/-!
# Lemme du défaut ponctuel (abstrait)

Couret–Unification — couche abstraite, étage C.
∀ G abélien fini, χ ordre 2, A = ker χ, a₀ ∈ A, T = A \ {a₀} :
  E_χ = (|A|−1)², E_ψ = 1 pour ψ ∉ {1, χ}.

SENS DIRECT uniquement (mécanisme général). La réciproque (dominance ⟹ structure
de fibre) est spécifique à chaque groupe, hors de ce fichier.

Statut visé : [D-formal, abstract] après lake build. Dépend de
`CharacterSubgroupSums.sum_over_ker_eq_zero` (déjà [D-formal]).

`RHClaimed = false. ScopeExpansionClaimed = false.`
-/

namespace CouretUnification.Core.PointDefectLemma

open scoped BigOperators
open CouretUnification.Core.CharacterSubgroupSums

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- Le Finset du noyau de χ (convention `univ.filter`, alignée sur CharacterSubgroupSums). -/
noncomputable def kerFinset (χ : G →* ℂˣ) : Finset G :=
  Finset.univ.filter (· ∈ χ.ker)

/-- Le défaut ponctuel T = ker χ \ {a₀}. -/
noncomputable def defectFinset (χ : G →* ℂˣ) (a₀ : G) : Finset G :=
  (kerFinset χ).erase a₀

/-- Énergie du défaut ponctuel sur ψ ∉ {1, χ} : vaut 1.
    Σ_T ψ = Σ_{ker} ψ − ψ a₀ = 0 − ψ a₀ ; |−ψ a₀|² = 1. -/
theorem energy_secondary_eq_one
    (χ : G →* ℂˣ) (hχ2 : ∀ x, (χ x : ℂ) ^ 2 = 1) (hχ1 : χ ≠ 1)
    (a₀ : G) (ha₀ : a₀ ∈ χ.ker)
    (ψ : G →* ℂˣ) (hψ1 : ψ ≠ 1) (hψχ : ψ ≠ χ) :
    Complex.normSq (∑ x ∈ defectFinset χ a₀, (ψ x : ℂ)) = 1 := by
  classical
  have ha₀mem : a₀ ∈ kerFinset χ := by
    rw [kerFinset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha₀⟩
  -- Σ_{ker} ψ = Σ_T ψ + ψ a₀
  have hsplit : ∑ x ∈ kerFinset χ, (ψ x : ℂ)
      = (∑ x ∈ defectFinset χ a₀, (ψ x : ℂ)) + (ψ a₀ : ℂ) := by
    rw [defectFinset, Finset.sum_erase_add _ _ ha₀mem]
  -- Σ_{ker} ψ = 0
  have hzero : ∑ x ∈ kerFinset χ, (ψ x : ℂ) = 0 := by
    rw [kerFinset]; exact sum_over_ker_eq_zero χ hχ2 hχ1 ψ hψ1 hψχ
  -- d'où Σ_T ψ = −ψ a₀
  have hT : ∑ x ∈ defectFinset χ a₀, (ψ x : ℂ) = -(ψ a₀ : ℂ) := by
    have h := hsplit; rw [hzero] at h
    -- h : 0 = Σ_T ψ + ψ a₀  ⟹  Σ_T ψ = −ψ a₀
    linear_combination -h
  rw [hT, Complex.normSq_neg]
  -- |ψ a₀|² = 1 : ψ a₀ unité de ℂ donc normSq = 1
  sorry  -- normSq d'une racine de l'unité = 1 ; voir piste ci-dessous

/-- Énergie du défaut ponctuel sur χ : vaut (|ker χ| − 1)². -/
theorem energy_dominant
    (χ : G →* ℂˣ) (hχ2 : ∀ x, (χ x : ℂ) ^ 2 = 1) (hχ1 : χ ≠ 1)
    (a₀ : G) (ha₀ : a₀ ∈ χ.ker) :
    Complex.normSq (∑ x ∈ defectFinset χ a₀, (χ x : ℂ))
      = (((kerFinset χ).card : ℝ) - 1) ^ 2 := by
  classical
  have ha₀mem : a₀ ∈ kerFinset χ := by
    rw [kerFinset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha₀⟩
  -- χ x = 1 pour x ∈ ker
  have hone : ∀ x ∈ kerFinset χ, (χ x : ℂ) = 1 := by
    intro x hx
    rw [kerFinset, Finset.mem_filter, MonoidHom.mem_ker] at hx
    have := hx.2
    rw [this, Units.val_one]
  -- Σ_{ker} χ = |ker|
  have hsumK : ∑ x ∈ kerFinset χ, (χ x : ℂ) = (kerFinset χ).card := by
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  have ha₀one : (χ a₀ : ℂ) = 1 := hone a₀ ha₀mem
  -- Σ_T χ = |ker| − 1
  have hsumT : ∑ x ∈ defectFinset χ a₀, (χ x : ℂ) = (kerFinset χ).card - 1 := by
    have hsplit : ∑ x ∈ kerFinset χ, (χ x : ℂ)
        = (∑ x ∈ defectFinset χ a₀, (χ x : ℂ)) + (χ a₀ : ℂ) := by
      rw [defectFinset, Finset.sum_erase_add _ _ ha₀mem]
    rw [hsumK, ha₀one] at hsplit
    -- hsplit : ↑card = Σ_T χ + 1  ⟹  Σ_T χ = ↑card − 1
    linear_combination -hsplit
  rw [hsumT]
  -- normSq d'un réel (card − 1) = (card − 1)²
  sorry  -- normSq (↑(card) − 1 : ℂ) = (card − 1)² ; voir piste ci-dessous

end CouretUnification.Core.PointDefectLemma
