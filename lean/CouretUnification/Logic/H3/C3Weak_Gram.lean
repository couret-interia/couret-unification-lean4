/-
# CouretUnification/Logic/H3/C3Weak_Gram.lean (v35.8.8.1)

## Statut
  - Couche : Logic / H3 (auxiliaire structurel pour C3Weak)
  - Sorry : 0 ✅
  - Axiome local : 0
  - RHClaimed = false

## Changelog v35.8.3 → v35.8.8.1

- **Corrections Mathlib 4.29.1** :
  * `structure ... : Prop where` retiré de `HasGramFactorization` et `IsRigid` :
    le champ `A : H →L[ℂ] H` ne pouvait pas vivre dans une `Prop`.
  * Désormais ce sont des `structure` régulières (Type-valued).
  * `IsRigid` reste utilisable comme classe via `instance` à la demande.
- **Syntaxe Lean 4** :
  * Tous les `let ... in` Lean 3 résiduels remplacés par leur équivalent Lean 4.

## Doctrine

Rigidité structurelle : S = A* ∘ A ⟹ ⟨S v_i, v_j⟩ forme PSD.
Preuve purement algébrique, insensible aux turbulences Mathlib.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CouretUnification.Meta.Doctrine

open scoped BigOperators
open Finset

namespace CouretUnification.Logic.H3.C3Weak_Gram

/-! ## Section 1 — Structure et classe -/

/-- Témoin d'une factorisation de Gram : `S = A* ∘ A`.
    NB : ce n'est PAS une `Prop` car le champ `A` est porteur de données
    (un opérateur, pas une preuve). Pour la version proposable, voir
    `IsRigid` ci-dessous. -/
structure HasGramFactorization
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : H →L[ℂ] H) : Type _ where
  A : H →L[ℂ] H
  factorization : S = (ContinuousLinearMap.adjoint A).comp A

/-- Existence d'une factorisation de Gram : version `Prop` propre. -/
def IsRigid
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : H →L[ℂ] H) : Prop :=
  Nonempty (HasGramFactorization S)

/-- Interop IsRigid → HasGramFactorization (via choix non constructif).
    NB : utilise `Classical.choice`, donc `noncomputable`. -/
noncomputable def IsRigid.toHasGramFactorization
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H} (hR : IsRigid S) :
    HasGramFactorization S :=
  hR.some

/-- Interop HasGramFactorization → IsRigid. -/
theorem HasGramFactorization.toIsRigid
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H} (h : HasGramFactorization S) :
    IsRigid S :=
  ⟨h⟩

/-! ## Section 2 — Passage entrée de Gram -/

/-- ⟨S x, y⟩ = ⟨A x, A y⟩. -/
lemma gram_entry_eq_inner_Av
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H}
    (h : HasGramFactorization S)
    (x y : H) :
    (inner ℂ (S x) y : ℂ) = inner ℂ (h.A x) (h.A y) := by
  have h₁ :
      inner ℂ (S x) y =
        inner ℂ (((ContinuousLinearMap.adjoint h.A).comp h.A) x) y := by
    exact congrArg (fun T : H →L[ℂ] H => inner ℂ (T x) y) h.factorization
  calc
    inner ℂ (S x) y
        = inner ℂ (((ContinuousLinearMap.adjoint h.A).comp h.A) x) y := h₁
    _ = inner ℂ ((ContinuousLinearMap.adjoint h.A) (h.A x)) y := by
          simp [ContinuousLinearMap.comp_apply]
    _ = inner ℂ (h.A x) (h.A y) := by
          simpa using
            (ContinuousLinearMap.adjoint_inner_left (A := h.A) (x := y) (y := h.A x))

/-! ## Section 3 — Positivité vectorielle -/

/-- Pour tout x, Re ⟨S x, x⟩ ≥ 0. -/
lemma semidef_of_gram_factor
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H}
    (h : HasGramFactorization S)
    (x : H) :
    0 ≤ (inner ℂ (S x) x : ℂ).re := by
  rw [gram_entry_eq_inner_Av h x x]
  rw [inner_self_eq_norm_sq_to_K]
  simpa [pow_two] using (sq_nonneg ‖h.A x‖)

/-! ## Section 4 — Lifting bilinéaire -/

lemma gram_quadratic_eq_inner_sum
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H}
    (h : HasGramFactorization S)
    (v : ℕ → H) (n : ℕ) (c : ℕ → ℂ) :
    (∑ i ∈ range n, ∑ j ∈ range n,
        (starRingEnd ℂ) (c i) * c j * inner ℂ (S (v i)) (v j))
    =
    (inner ℂ
      (∑ i ∈ range n, c i • (h.A (v i)))
      (∑ j ∈ range n, c j • (h.A (v j))) : ℂ) := by
  -- Étape A : remplacer ⟨S vᵢ, vⱼ⟩ par ⟨A vᵢ, A vⱼ⟩
  have step_A :
      (∑ i ∈ range n, ∑ j ∈ range n,
          (starRingEnd ℂ) (c i) * c j * inner ℂ (S (v i)) (v j))
      =
      (∑ i ∈ range n, ∑ j ∈ range n,
          (starRingEnd ℂ) (c i) * c j * inner ℂ (h.A (v i)) (h.A (v j))) := by
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [gram_entry_eq_inner_Av h (v i) (v j)]
  rw [step_A]
  -- Étape B : absorber les scalaires
  have step_B :
      (∑ i ∈ range n, ∑ j ∈ range n,
          (starRingEnd ℂ) (c i) * c j * inner ℂ (h.A (v i)) (h.A (v j)))
      =
      (∑ i ∈ range n, ∑ j ∈ range n,
          inner ℂ (c i • (h.A (v i))) (c j • (h.A (v j))) : ℂ) := by
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [inner_smul_left, inner_smul_right]
    ring_nf
  rw [step_B]
  -- Étape C : factoriser
  rw [sum_inner]
  apply sum_congr rfl
  intro i _
  rw [inner_sum]

lemma gram_quadratic_re_eq_norm_sq
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H}
    (h : HasGramFactorization S)
    (v : ℕ → H) (n : ℕ) (c : ℕ → ℂ) :
    ((∑ i ∈ range n, ∑ j ∈ range n,
        (starRingEnd ℂ) (c i) * c j * inner ℂ (S (v i)) (v j)) : ℂ).re
    =
    ‖∑ i ∈ range n, c i • (h.A (v i))‖ ^ 2 := by
  rw [gram_quadratic_eq_inner_sum h v n c]
  rw [inner_self_eq_norm_sq_to_K]
  simp [pow_two]

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
      ((∑ i ∈ range n, ∑ j ∈ range n,
          (starRingEnd ℂ) (c i) * c j * inner ℂ (S (v i)) (v j)) : ℂ).re := by
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
      Complex.re (∑ i ∈ range n, ∑ j ∈ range n,
          (starRingEnd ℂ) (c i) * c j * inner ℂ (S (v i)) (v j)) :=
  gram_semidef_of_rigid h v n c

/-- Version IsRigid (consomme le témoin existentiel). -/
theorem gram_semidef_of_isRigid
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H} (hR : IsRigid S)
    (v : ℕ → H) (n : ℕ) (c : ℕ → ℂ) :
    0 ≤
      ((∑ i ∈ range n, ∑ j ∈ range n,
          (starRingEnd ℂ) (c i) * c j * inner ℂ (S (v i)) (v j)) : ℂ).re :=
  gram_semidef_of_rigid hR.toHasGramFactorization v n c

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
  status     := Status.proved
  sorryCount := 0
  rhClaimed  := false

end CouretUnification.Logic.H3.C3Weak_Gram
