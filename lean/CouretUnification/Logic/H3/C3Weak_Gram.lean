/-
# CouretUnification/Logic/H3/C3Weak_Gram.lean (v35.8.3)

## Statut
  - Couche : Logic / H3 (auxiliaire structurel pour C3Weak)
  - Sorry : 0 ✅
  - Axiome local : 0
  - RHClaimed = false

## Changelog v35.8.2 → v35.8.3

- Aucun changement structurel. Fichier déjà sans sorry depuis v35.8.2.
- Ajout de : `gram_semidef_of_rigid_real_part` alias explicite pour
  l'inégalité sur la partie réelle.
- Ajout de : instance `IsRigid_of_HasGramFactorization` pour faciliter
  l'interopérabilité entre les deux présentations.

## Doctrine

Rigidité structurelle : S = A* ∘ A ⟹ ⟨S v_i, v_j⟩ forme PSD.
Preuve purement algébrique, insensible aux turbulences Mathlib.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.BigOperators.Basic
import CouretUnification.Meta.Doctrine

open scoped BigOperators
open Finset

namespace CouretUnification
namespace Logic
namespace H3
namespace C3Weak_Gram

/-! ## Section 1 — Structure et classe -/

structure HasGramFactorization
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : H →L[ℂ] H) : Prop where
  A : H →L[ℂ] H
  factorization : S = (ContinuousLinearMap.adjoint A).comp A

class IsRigid
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : H →L[ℂ] H) : Prop where
  A : H →L[ℂ] H
  factorization : S = (ContinuousLinearMap.adjoint A).comp A

/-- Interop IsRigid → HasGramFactorization. -/
def IsRigid.toHasGramFactorization
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H} [hR : IsRigid S] :
    HasGramFactorization S :=
  ⟨hR.A, hR.factorization⟩

/-- Interop HasGramFactorization → IsRigid (instance explicite). -/
def HasGramFactorization.toIsRigid
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H} (h : HasGramFactorization S) :
    IsRigid S :=
  ⟨h.A, h.factorization⟩

/-! ## Section 2 — Passage entrée de Gram -/

/-- ⟨S x, y⟩ = ⟨A x, A y⟩. -/
lemma gram_entry_eq_inner_Av
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H}
    (h : HasGramFactorization S)
    (x y : H) :
    (inner (S x) y : ℂ) = inner (h.A x) (h.A y) := by
  rw [h.factorization]
  simp only [ContinuousLinearMap.comp_apply]
  exact ContinuousLinearMap.adjoint_inner_left h.A (h.A x) y

/-! ## Section 3 — Positivité vectorielle -/

/-- Pour tout x, Re ⟨S x, x⟩ ≥ 0. -/
lemma semidef_of_gram_factor
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H}
    (h : HasGramFactorization S)
    (x : H) :
    0 ≤ (inner (S x) x : ℂ).re := by
  rw [gram_entry_eq_inner_Av h x x]
  rw [inner_self_eq_norm_sq_to_K]
  simp only [Complex.ofReal_re]
  exact sq_nonneg _

/-! ## Section 4 — Lifting bilinéaire -/

lemma gram_quadratic_eq_inner_sum
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H}
    (h : HasGramFactorization S)
    (v : ℕ → H) (n : ℕ) (c : ℕ → ℂ) :
    (∑ i in range n, ∑ j in range n,
        (starRingEnd ℂ) (c i) * c j * inner (S (v i)) (v j))
    =
    (inner
      (∑ i in range n, c i • (h.A (v i)))
      (∑ j in range n, c j • (h.A (v j))) : ℂ) := by
  -- Étape A : remplacer ⟨S vᵢ, vⱼ⟩ par ⟨A vᵢ, A vⱼ⟩
  have step_A :
      (∑ i in range n, ∑ j in range n,
          (starRingEnd ℂ) (c i) * c j * inner (S (v i)) (v j))
      =
      (∑ i in range n, ∑ j in range n,
          (starRingEnd ℂ) (c i) * c j * inner (h.A (v i)) (h.A (v j))) := by
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _
    rw [gram_entry_eq_inner_Av h (v i) (v j)]
  rw [step_A]
  -- Étape B : absorber les scalaires
  have step_B :
      (∑ i in range n, ∑ j in range n,
          (starRingEnd ℂ) (c i) * c j * inner (h.A (v i)) (h.A (v j)))
      =
      (∑ i in range n, ∑ j in range n,
          inner (c i • (h.A (v i))) (c j • (h.A (v j))) : ℂ) := by
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _
    rw [inner_smul_left, inner_smul_right]
    ring
  rw [step_B]
  -- Étape C : factoriser
  rw [← sum_inner]
  apply sum_congr rfl; intro i _
  rw [← inner_sum]

lemma gram_quadratic_re_eq_norm_sq
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H}
    (h : HasGramFactorization S)
    (v : ℕ → H) (n : ℕ) (c : ℕ → ℂ) :
    ((∑ i in range n, ∑ j in range n,
        (starRingEnd ℂ) (c i) * c j * inner (S (v i)) (v j)) : ℂ).re
    =
    ‖∑ i in range n, c i • (h.A (v i))‖ ^ 2 := by
  rw [gram_quadratic_eq_inner_sum h v n c]
  rw [inner_self_eq_norm_sq_to_K]
  simp

/-! ## Section 5 — Théorème principal -/

/-- **gram_semidef_of_rigid** : positivité de la matrice de Gram associée.
    Preuve en une phrase : la forme quadratique est ‖Σ cᵢ A(vᵢ)‖². -/
theorem gram_semidef_of_rigid
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H}
    (h : HasGramFactorization S)
    (v : ℕ → H) (n : ℕ) (c : ℕ → ℂ) :
    0 ≤
      ((∑ i in range n, ∑ j in range n,
          (starRingEnd ℂ) (c i) * c j * inner (S (v i)) (v j)) : ℂ).re := by
  rw [gram_quadratic_re_eq_norm_sq h v n c]
  exact sq_nonneg _

/-- Alias explicite pour la partie réelle. -/
theorem gram_semidef_of_rigid_real_part
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H}
    (h : HasGramFactorization S)
    (v : ℕ → H) (n : ℕ) (c : ℕ → ℂ) :
    0 ≤
      Complex.re (∑ i in range n, ∑ j in range n,
          (starRingEnd ℂ) (c i) * c j * inner (S (v i)) (v j)) :=
  gram_semidef_of_rigid h v n c

/-- Version IsRigid. -/
theorem gram_semidef_of_isRigid
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : H →L[ℂ] H) [IsRigid S]
    (v : ℕ → H) (n : ℕ) (c : ℕ → ℂ) :
    0 ≤
      ((∑ i in range n, ∑ j in range n,
          (starRingEnd ℂ) (c i) * c j * inner (S (v i)) (v j)) : ℂ).re :=
  gram_semidef_of_rigid IsRigid.toHasGramFactorization v n c

/-! ## Section 6 — Instances standard -/

/-- Projecteur orthogonal idempotent + auto-adjoint ⟹ rigide. -/
def HasGramFactorization.ofProjector
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : H →L[ℂ] H)
    (hidem : P.comp P = P)
    (hsa : ContinuousLinearMap.adjoint P = P) :
    HasGramFactorization P where
  A := P
  factorization := by rw [hsa, hidem]

end C3Weak_Gram
end H3
end Logic
end CouretUnification

namespace CouretUnification.Logic.H3.C3Weak_Gram

open CouretUnification.Meta

def fileIdentity : FileIdentity where
  filename   := "CouretUnification/Logic/H3/C3Weak_Gram.lean"
  layer      := Layer.B
  status     := Status.certified
  sorryCount := 0
  rhClaimed  := false

example : fileIdentity.rhClaimed = false := rfl
example : fileIdentity.sorryCount = 0 := rfl
example : fileIdentity.isClean = true := rfl

end CouretUnification.Logic.H3.C3Weak_Gram
