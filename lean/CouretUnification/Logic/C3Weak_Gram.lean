/-
# CouretUnification/Logic/C3Weak_Gram.lean

## Rôle
Certification ALGÉBRIQUE INCONDITIONNELLE de la positivité de la matrice
de Gram associée à un opérateur `S` possédant une factorisation
`S = A* ∘ A` sur un espace de Hilbert complexe complet.

## Statut (v35.8.6, inchangé depuis stabilisation antérieure)
- Layer   : Logic (brique Platinum)
- Status  : proved
- Sorry   : 0
- RHClaimed : false

## Principe
La forme quadratique `∑ᵢⱼ conj(cᵢ)·cⱼ·⟨S vᵢ, vⱼ⟩` se réduit à
`‖∑ᵢ cᵢ · A vᵢ‖²` via adjonction + linéarité, donc sa partie réelle
est automatiquement ≥ 0.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Basic
import CouretUnification.Meta.Doctrine

open scoped BigOperators
open Finset

namespace CouretUnification
namespace Logic
namespace C3Weak_Gram

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Section 1 — Structure de factorisation -/

/-- Un opérateur `S : H →L[ℂ] H` est "rigide au sens de Gram" s'il
    se factorise en `S = A* ∘ A` pour un certain opérateur `A`. -/
structure HasGramFactorization (S : H →L[ℂ] H) : Prop where
  /-- L'opérateur "racine" `A`. -/
  A : H →L[ℂ] H
  /-- Équation de factorisation : `S = adjoint A ∘ A`. -/
  factorization : S = (ContinuousLinearMap.adjoint A).comp A

/-! ## Section 2 — Positivité semi-définie -/

/-- Théorème principal : la forme quadratique d'un opérateur rigide au
    sens de Gram est universellement semi-définie positive.

    Stratégie : on réécrit `⟨S vᵢ, vⱼ⟩ = ⟨A vᵢ, A vⱼ⟩` via adjonction,
    puis on factorise la double somme en `⟨u, u⟩` où
    `u = ∑ k, c k • A (v k)`. Par l'identité Hilbert-Schmidt,
    `(⟨u, u⟩).re = ‖u‖²`, donc positif. -/
theorem gram_semidef_of_rigid
    (S : H →L[ℂ] H) (h : HasGramFactorization S)
    (v : ℕ → H) (n : ℕ) (c : ℕ → ℂ) :
    0 ≤ (∑ i ∈ range n, ∑ j ∈ range n,
          (starRingEnd ℂ) (c i) * c j * inner ℂ (S (v i)) (v j)).re := by
  -- 1. Extraire A.
  set A := h.A with hA_def
  -- 2. Réécrire via la factorisation et l'adjonction.
  have h_entry : ∀ i j, inner ℂ (S (v i)) (v j) = inner ℂ (A (v i)) (A (v j)) := by
    intro i j
    rw [h.factorization]
    simp [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply]
  -- 3. Substituer dans la double somme.
  simp_rw [h_entry]
  -- 4. Introduire le vecteur combiné u = ∑ k, c k • A (v k).
  set u : H := ∑ k ∈ range n, c k • A (v k) with hu_def
  -- 5. Montrer que la double somme = ⟨u, u⟩.
  have h_sum_inner : (∑ i ∈ range n, ∑ j ∈ range n,
        (starRingEnd ℂ) (c i) * c j * inner ℂ (A (v i)) (A (v j)))
      = inner ℂ u u := by
    rw [hu_def]
    rw [sum_inner]
    congr 1; ext i
    rw [inner_sum]
    congr 1; ext j
    rw [inner_smul_left, inner_smul_right]
    ring
  rw [h_sum_inner]
  -- 6. ⟨u, u⟩.re = ‖u‖² ≥ 0.
  rw [inner_self_eq_norm_sq_to_K]
  simp
  exact sq_nonneg _

/-! ## Section 3 — Identité doctrinale -/

open CouretUnification.Meta

/-- Identité du fichier C3Weak_Gram (★ fermé, excellence algébrique). -/
def fileIdentity : FileIdentity where
  filename   := "CouretUnification/Logic/C3Weak_Gram.lean"
  layer      := Layer.B
  status     := Status.proved
  sorryCount := 0
  rhClaimed  := false

end C3Weak_Gram
end Logic
end CouretUnification
