import CouretUnification.Core.CharacterSubgroupSums
import Mathlib.Tactic

/-!
# Lemme du défaut ponctuel (abstrait) — [P-scaffold NON VÉRIFIÉ]

∀ G abélien fini ordre pair, χ ordre 2, A = ker χ, a₀ ∈ A, T = A \ {a₀} :
  E_χ = (n/2−1)², E_ψ = 1 pour ψ ∉ {1, χ}.

Vérifié numériquement sur 10 groupes (brief §1.2). SENS DIRECT uniquement.
-/

namespace CouretUnification.Core.PointDefectLemma

open scoped BigOperators
open CouretUnification.Core.CharacterSubgroupSums

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

def kerFinset (χ : G →* ℂˣ) : Finset G :=
  Finset.univ.filter (· ∈ χ.ker)

/-- Énergie du défaut ponctuel sur un caractère ψ ∉ {1, χ} : vaut 1. -/
theorem energy_secondary_eq_one
    (χ : G →* ℂˣ) (hχ : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    (a₀ : G) (ha₀ : a₀ ∈ χ.ker)
    (ψ : G →* ℂˣ) (hψ1 : ψ ≠ 1) (hψχ : ψ ≠ χ) :
    let T := (χ.ker.carrier.toFinset.erase a₀)
    Complex.normSq (∑ x ∈ T, (ψ x : ℂ)) = 1 := by
  sorry  -- Σ_T ψ = Σ_A ψ − ψ a₀ = 0 − ψ a₀ ;  |−ψ a₀|² = 1
         -- utilise sum_over_subgroup_eq_zero + trivial_on_ker_iff

/-- Énergie du défaut ponctuel sur χ lui-même : vaut (n/2 − 1)². -/
theorem energy_dominant
    (χ : G →* ℂˣ) (hχ : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    (a₀ : G) (ha₀ : a₀ ∈ χ.ker) :
    let T := (χ.ker.carrier.toFinset.erase a₀)
    let halfn := Fintype.card G / 2
    Complex.normSq (∑ x ∈ T, (χ x : ℂ)) = ((halfn : ℝ) - 1) ^ 2 := by
  sorry  -- χ = 1 sur A = ker χ ; Σ_T χ = |A| − 1 = n/2 − 1
