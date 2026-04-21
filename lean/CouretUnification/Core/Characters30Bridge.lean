/-
  CouretUnification/Core/Characters30Bridge.lean
  Version v35.1 — Fermeture complète du bridge caractères.
  Sorry visés : 0.  RHClaimed = false.
  NOTE : ne doit PAS importer CRTEquiv (cycle).
-/

import CouretUnification.Core.Convolution30
import CouretUnification.Core.Characters30
import CouretUnification.Core.CharacterLemmas

open scoped BigOperators

namespace CouretUnification.Core

-- §1. Pont G30 → Idx (conservé de v32)

def g30ToIdx (u : G30) : Idx :=
  if (u : ZMod 30) = 1  then ⟨0, by omega⟩
  else if (u : ZMod 30) = 7  then ⟨1, by omega⟩
  else if (u : ZMod 30) = 11 then ⟨2, by omega⟩
  else if (u : ZMod 30) = 13 then ⟨3, by omega⟩
  else if (u : ZMod 30) = 17 then ⟨4, by omega⟩
  else if (u : ZMod 30) = 19 then ⟨5, by omega⟩
  else if (u : ZMod 30) = 23 then ⟨6, by omega⟩
  else ⟨7, by omega⟩

-- §2. Caractère concret sur G30

def charOnG30 (χ : CharIdx) : FunG30 :=
  fun g => characterEval χ (g30ToIdx g)

noncomputable def eigenvalue (K : FunG30) (χ : CharIdx) : ℂ :=
  ∑ g : G30, K g * charOnG30 χ g⁻¹

-- §3. Coordonnées CRT (locales)

def g30Coord (g : G30) : Fin 2 × Fin 4 :=
  residueCoord (g30ToIdx g)

def addCoord (p q : Fin 2 × Fin 4) : Fin 2 × Fin 4 :=
  (p.1 + q.1, p.2 + q.2)

-- §4. g30Coord morphisme

set_option maxHeartbeats 800000 in
theorem g30Coord_mul (a b : G30) :
    g30Coord (a * b) = addCoord (g30Coord a) (g30Coord b) := by
  fin_cases a <;> fin_cases b <;>
    simp [g30Coord, g30ToIdx, residueCoord, addCoord] <;> decide

-- §5. Dépliage tautologique

theorem charOnG30_factor (χ : CharIdx) (g : G30) :
    charOnG30 χ g =
      let (e, k) := g30Coord g
      let (m, n) := charCoord χ
      c2Phase m e * c4Phase n k := by
  simp only [charOnG30, g30Coord, characterEval]

-- §6. Multiplicativité des phases

theorem c2Phase_mul_right (m : Fin 2) (e₁ e₂ : Fin 2) :
    c2Phase m (e₁ + e₂) = c2Phase m e₁ * c2Phase m e₂ := by
  fin_cases m <;> fin_cases e₁ <;> fin_cases e₂ <;>
    simp [c2Phase] <;> ring

set_option maxHeartbeats 1600000 in
theorem c4Phase_mul_right (n : Fin 4) (k₁ k₂ : Fin 4) :
    c4Phase n (k₁ + k₂) = c4Phase n k₁ * c4Phase n k₂ := by
  fin_cases n <;> fin_cases k₁ <;> fin_cases k₂ <;>
    simp only [c4Phase] <;>
    norm_num [Complex.I_sq]

-- §7. Multiplicativité du caractère

theorem charOnG30_mul (χ : CharIdx) (a b : G30) :
    charOnG30 χ (a * b) = charOnG30 χ a * charOnG30 χ b := by
  simp only [charOnG30_factor]
  rw [g30Coord_mul]
  simp only [addCoord]
  rw [c2Phase_mul_right, c4Phase_mul_right]

-- §8. MonoidHom

def charOnG30AsHom (χ : CharIdx) : G30 →* ℂ where
  toFun := charOnG30 χ
  map_one' := by
    fin_cases χ <;>
      simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord,
            c2Phase, c4Phase]
  map_mul' := charOnG30_mul χ

-- §9. Orthogonalité

set_option maxHeartbeats 800000 in
theorem charOnG30AsHom_ne_one (χ : CharIdx) (hχ : χ ≠ ⟨0, by omega⟩) :
    charOnG30AsHom χ ≠ 1 := by
  fin_cases χ
  · exact absurd rfl hχ
  all_goals (
    intro h
    have h7 : charOnG30 _ ⟨7, 13, by decide, by decide⟩ = 1 := by
      have := congr_fun (MonoidHom.ext_iff.mp h) ⟨7, 13, by decide, by decide⟩
      simpa [charOnG30AsHom]
    simp only [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord,
               c2Phase, c4Phase] at h7
    norm_num [Complex.I_sq, Complex.ext_iff, Complex.I_re, Complex.I_im,
             Complex.one_re, Complex.one_im,
             Complex.mul_re, Complex.mul_im,
             Complex.neg_re, Complex.neg_im] at h7
  )

theorem sum_charOnG30_ne_trivial (χ : CharIdx) (hχ : χ ≠ ⟨0, by omega⟩) :
    ∑ g : G30, charOnG30 χ g = 0 := by
  have hne : charOnG30AsHom χ ≠ 1 := charOnG30AsHom_ne_one χ hχ
  have key := sum_char_eq_zero_of_ne_one (charOnG30AsHom χ) hne
  convert key using 1
  apply Finset.sum_congr rfl
  intro g _; rfl

-- §10. Export (compatibilité v32)

theorem charOnG30_trivial (g : G30) :
    charOnG30 ⟨0, by omega⟩ g = 1 := by
  simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord,
        c2Phase, c4Phase]

theorem charOnG30_ne_zero (χ : CharIdx) :
    charOnG30 χ ≠ 0 := by
  intro h
  have h1 : charOnG30 χ (1 : G30) = 0 := congr_fun h _
  fin_cases χ <;>
    simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord,
          c2Phase, c4Phase] at h1

-- §11. Réindexation

private lemma sum_reindex_mul_inv' (x : G30) (F : G30 → ℂ) :
    (∑ y : G30, F (x * y⁻¹)) = ∑ g : G30, F g := by
  apply Finset.sum_nbij (fun y => x * y⁻¹)
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => by
      have := mul_left_cancel h
      exact inv_injective this)
    (fun g _ => ⟨g⁻¹ * x, Finset.mem_univ _, by group⟩)
    (fun _ _ => rfl)

-- §12. Diagonalisation

theorem convolution_diag_pointwise (K : FunG30) (χ : CharIdx) (x : G30) :
    convolutionOp K (charOnG30 χ) x = eigenvalue K χ * charOnG30 χ x := by
  simp only [convolutionOp, LinearMap.coe_mk, AddHom.coe_mk, eigenvalue]
  calc ∑ y : G30, K (x * y⁻¹) * charOnG30 χ y
      = ∑ g : G30, K g * charOnG30 χ (g⁻¹ * x) := by
          rw [← sum_reindex_mul_inv' x (fun g => K g * charOnG30 χ (g⁻¹ * x))]
          apply Finset.sum_congr rfl; intro y _
          congr 1; congr 1; group
    _ = ∑ g : G30, K g * (charOnG30 χ g⁻¹ * charOnG30 χ x) := by
          apply Finset.sum_congr rfl; intro g _
          congr 1; exact charOnG30_mul χ g⁻¹ x
    _ = (∑ g : G30, K g * charOnG30 χ g⁻¹) * charOnG30 χ x := by
          simp_rw [← mul_assoc]; rw [← Finset.sum_mul]

theorem convolution_diagonalizes_character (K : FunG30) (χ : CharIdx) :
    convolutionOp K (charOnG30 χ) = eigenvalue K χ • charOnG30 χ := by
  funext x
  exact convolution_diag_pointwise K χ x

end CouretUnification.Core